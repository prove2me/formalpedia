-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3588
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:05:49.742998+00:00
-- url     : https://prove2.me/submissions/f79c6350-a679-42c6-b7f5-1b15eeb77146

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 645143884 ≤ n < 645323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 645145134 1250 645143884 645143887
    0x9090706022a0f04090f1b0608073914100207031b0c052701091a09090a080309030a0801061e03150b0a11060907050d020d0c0914040201180803 63
    0x302c0505010070018402ea5004e0404107080c28a600d03140300c1c90a0f00041198a46103003802c00c082c550404d49868050981d42c580041c803401c10308001422001d00c2c800c0e0034171f0301210002400740c071000c558501c2e424000d00501e890f40c0e500e4034140450304261074a074640c058026a001e02c6143c04d002c1c42100c00b0903034162680c6181170b544001000c0e4640c160300c0100e8580c40ea511000c1015a101110194103100d403004418465000e09a5055010360603031000c1c00d90b41c01c2c8152521180e032002e400803008501a6815106552030607480ca03d0410240c0b80900b88030000403d000b10060b001c130083c0000c0c140c0b03466019040c0d9840f40c007203550444000c240c10390840007220f00c2c3d040e603110790004a50507007540e81440c115901d038030400516520031314010340420803825140300e030200240b00090344106000c02500c401e5107000e020a01e0381048140080c40740e14030400345001c01001c010048040c1c00210f178108110200584050506042034406a0200d071126024200000b185511007058a60b0300003c0d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 645146384 1250 645145134 645145213
    0x602030706051b030c0c01110711130903090b0a09051504060f0c020306070503061306150320030103022e08060f0405091f090203030d060509010b0301120b070e0909070602 75
    0x40c81e5003001503d403016542395011191811100c90142c60800d0040d00d0741c4032019501c40400600aa01d620b185c400181003074600008250010a5082102c900011065817559603070b00c110745008254008a03408880b4452000703180140708090720641d1aa071316009404021010192005662844001e5040d0302c49400202c0c002d116401a50f0400406008503540c200124446420388446400202c050940400c4204032164140074501c8412258884180c07043c50000104001e44414000a030048501c0c8100e00d49443c500e826114092038800881340a500c05402c0040461000740d81c898030a40304002a45400c1c501440f900d0302600e0350400610456001c1c09106052600039480312240654510903c40561806e1000307200071030707070000001415800c10081110f040e030180c210408103038061005110204440240c0c107581500070a4050095842044c2100d40b003080c10150b070780201403030080c03110000d800100c2c00c080d01d40b950252544050b00b802460b102c0c000d000003024480c840c80520 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 645147634 1250 645146384 645146401
    0x91508070b030415060509180d0302070c03020405090c06070507051f051207050f12270a06020310050402191706030a02090603100c02030409060b1801120906060602030706051b03 78
    0x1a881002d244c3c0082070540d070310400280304640032120001200c44541c0c5101201c441400084810081c0d404d045040036115101d4609402c0c960100900030b6035500c2c04503241c210100041d505248000b042181d0328540d0340790943e150a0340d4814030780900c54440450413a41d001401d10101e40c003c1d907807001c0c00c000940145840026010300040f041c004100000c25401110320700038254401c0c01101d5031454109440a80070360000801c62401c6d090f1040c501d150340d0000443d02014540c0c1104000d03849840324000c40c0c2000b00e540c0d02080d030051000542a004205910a4002a440c01c1d110b0020b001e2003c07410150f00c64088580580c180c00c246402c1005140c8410f03819003004003c3c04441c0312100d08140881200c0b00f149020000d40d001003001c0101c568540200800f0f8a0995011410940720743e010070602255919064140081c0c24100c07406010103603c010989034000340d05001042d034900c8003030349a0340048400d5a08034141000207640c1c0401810410032028480c5d0711501c1c46c0d581800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 645148884 1250 645147634 645147653
    0x5030c03060d0204051e010f0303020304181514010e01030e03030112030507020d0309031205040f05060703050c0d050d1d0303060d02061318052413060b0301091508070b0304 76
    0x580d642c01000c0c00030081c09a00c403841450b202e010001400060a42900311800292605901c050501d410301e210500010f42c0c0401034408945010040a622079075071152000985103c2081f1008039260100016100747e00c004412082c20081e00c07038030203100e440740044040d00c40045034060f42c2e91007040100308101b2400c0700006a94040d00e0b040d801c101c0594009503e000c40c040041d4001021610140144481c41d555080c4080e202c5c1001c0d8a030030301c0e280310f01c9031411340d6214040c402e107408250030003410301400450b000480780005803000a441c010014103c0e400c820101d44215107041d001090042600c9010301d800c0d101600254110355510040211324450a17204a0b000a0309104c0000c80d600c0c01c604d028054a0b070380740444c0c3d8003e40c1e035018204541e4010002c040351200c0804500d031031221303074000403000c02c420350310810150340c0c1007207000151082d030344030040340360000000040c20b084562116100b00300910038020066a5aa48983e580b4618015588a07000c10008a0f0004aa08a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 645150134 1250 645148884 645148891
    0x60a090b0307050d061404060e0708150a0302031014060a14042d05092803080622020702040e0a0312050613141801060612051807030822030305030c03 66
    0x141040c50801000713965026544260b00440d02c01c030030140300280d149031500528016101c8280080040e02e42a00700600300100034000038030f41c03080c41a0141e19529900c90713902c003454010f011201c1102042001800030440d000e03581d15456607801c04907101d40f814062110445103002e080000c509962410080208103441d000f00341092004907035900500741c2921402e28040b1202d0004543c03a140350000d080c0b55075181e03040f000c9030742008407001c000020038101e0340e480d806141c920b1442e680c1d0f00c08078080541c210440751070900030001862046132a50001c110152080d50240405002015916030781c41c14608001e020505859504045a4061b03002d664802e0307000385a0b40c100a154030b9001e04a582804403125056800c03010800c0a520031006100c07030406903002042100d02e0810010520401d0740c0384c941003a40c40d04081441d0030a00601d41466800c0d03030040e901216620700d4002e2581e4030a0b002c2d1003c050007070105060700c95580c1d8140c011640c00d9181c9500e59a203541da807240a03130004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 645151384 1250 645150134 645150137
    0x120f070b090a080f07080610120f0501140921040e07050f0d050712140c04150306030b07090608150d0f060906060b09040e01091703040201140c06070e060a090b0307 72
    0x54000200351001300045400110000d019001d1030b81032542007810714100402d030b80401a0300307580402012403003802481419411810416144c0c00a141c124090f25a249400c600c0440c140240302d00840003141c00b0300101d01000c0f03220b80000740880c85034001d010f2403048529811704080003c1205018600806400459080003450038501c012000c0c11983c040c1c46401c00204500c00340c40c40507165114035404080074a5000c40a854444c180c2d000510540c00364142010312901844d6106009030094009140d0000d0441d61078600301d00020000c110b5445050002544040424102c2e070503c5017000c1c00e20b001404141d00c644581d1262150300710b1010040350080e5540c22001c01054143c81501d0161105240b002d6540b4055410032003030303134002c81c1121103a0745400c000340006601c038182442c4080d604506d0b44e46903aa64001a29007100c2402d184410440005800b00c1c801c00c0482d103103125610301d48600d42e4294140d01402124021040c80da03003c1510000c0c280040503045010b554491400e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 645152634 1250 645151384 645151399
    0x61309020d06020c03091e10141201080114130317040c030515070f0905030a060b12060702030d140906060d0618110307080d08152409120f070b09 64
    0x1e6035030070b000c84e031040484403a00c0d000801d80402c10300d0403800d0b0360381140107404003c0031420a0b03000940b8075014690242c01b8040500042c81c050380f100e1042e150303a82e000e058402140d6942d2219180600615030b05400c0501510001038111240d0000180344160503a5407404100102540100700c5031020344241e501c85001100080040d5080005a60250445058900d6414019400f03400b030440b03203a062003440884d080600c0640c40016003415030580200300030440450401c04120a400540402c3d2018041c0e141000640c64001004090101102130100711101038038603c0c0110380c4c1d0564401c540e50300120301140b0b99203412a041060300340100ca0001c0d8111600c1d4080c0802d82c1d8011040b0b031050071242a50485203001d0280e07400410400c0c002d08800c0c1801800201035800040c500c0c01140c00f40e001103072483c2c031403544044540a541004010102c00000d45a81c55008441d91602c20004400092110800400c407001501e055000420104c0d0420b40302a4154200100280c0c00c00f42 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 645153884 1250 645152634 645152659
    0x105121b011205040f0201020c09150609060c01050c1201120308011e0816081002030f01060c03051e09030d090315022d070b072606010203070c03060c02070602010506130902 76
    0xe940f00d050b0240d44980604401c100aa200280c00c0c102c4001413544a0007a00d42005a90100e41034812112003084500540c0e81000d0400501c8600510121f081990b1070041000300001c0098010f10652141500305011607030b840001c85410303003103104001c00040000004200103010601030001d0000c13041c1801c04510f0b00c8444444c9420680c00e013081e80c041c1c86e604c08110b1840c0500c48000c1a25001c1415891480e002800810b00e0ba41803040c0d0041151320320a010516128000b82c1c1d400100d4a10b061440c0c3c282c1d45c40e0700019070421185640b107401066040071280c1d004040440440381e11141500c101c0c0b0000310400700940000059080081001908100803100c0341c0940c107890003035011440c1c980758a41016642d20000501c44000e00120f250400c050040940090719424459240c40010340d544400407400e6015600740100400030080010007084a1074010600d0b8150366404c9030704a683e030320803c07820303a503041e90345a4011802021b0780ca0305070000d401c02903040340090712101c000350307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 645155134 1250 645153884 645153917
    0x30601030e0f030a11070f05010e0a0e07080106120b030706030e010e122a072601020a11010507030c091206091407050102121c0b040b03010204030c0e0105121b01 71
    0x2a03180b400d00b16000043c03698a4281c0064a821812442c18000e01e031060801c2c81c00c446440c03050042070b051018050820303074595a4070b68194042c000d0f06407011203a090200c009802001c0a0003080302050b100d100510400c010b0784500720715107800800421100345000000e03070041010142101541d529524404516031040000d44c100f41100d51449031340b06049185c0c844086802600ea4440881501080081c05000034000059951106d1040c0d1106d1501101c140e40351080c40103010f09500110303009012036001205008090a01c500038000d56492450803012900c02180305404a4032007102448030510806004034010711070a4001401c1403c3c7e102c1203210800d0803a15002030f8805074080c002542d05100c84d5240c510800c0c00207007070200405520540f551a090004400c0d581c0300090b8041c0c1d611504100078540700034008643e1750340c0700c1c10007116030040d0303024101e12001010000a031a0030000e21740500064524003900700311500050160007400c1410485040002920031044101c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 645156384 1250 645155134 645155143
    0x71a0c1f1b0203070c0f06090b36190f0b0f070218090f0d1b0f0b13050606091e1b03010b09120a03021c120606080106021903050f030601030e 62
    0x80d0342d0000c60316010710f8500890b50784107640012407602d440000420440740c0164011090700c5104009030b444001070707084244204040803e0f080c0420200714007103003918030342e210603a540c0000d44903a440b201030200e0711200e502144c070a075220800d64540400c02032a20401074200708100e401201d25142c49900001c07407820406100300200f445200900c907081c20708000c03800c0e103131980d40c019082c3e200c0b040300050400007050008284e0810410065000c0001c09820048030551100c1107175000c0c201441494140302071100d003203816110703490203e44940b4041e1245441482c4140807506c1e00e8640c222080b03401031002d00445400c0c00c1d5400b403224190000c10146000e0708164414a803079089030004c004501c0d12041800e91a90442e00011020a41c0861003000124081555080400000d48122000d070b01001d001c4404610380200800c11903444881c00e41222602d5003181c1486105030b0800c200c001c0c1c540c2c801000718900308000300414209102941d4414014100055104190440d06040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 645157634 1250 645156384 645156431
    0xe061201090302072c0f1909030f080604020c01050103081b1c031d030f07110d0b1b09030118020306011e150e1c0201020d03020702030a0b1512071a0c1f 67
    0x10040c0706c0308000d01e1250a03507551005e440100002d00846282c1d450140075000340c803108808101038400024115265501180d00c6010014000c0000390703501d05101102da0040003c54031800014901100100390004000051401080b44108500b840c010300382e009225280c01114450b01180032440010414400382c0064080d03414600c2d40e8003030030b1030028407000c040140e40d072103581e040300d200c030205a00e02501580701980d000c255201c442c1c81c1041240724003c5080081d415820400018403d518030384408500078800d030b00b00e40c69039884001e49840c3c815069010380d00790300030080804c844080c400804a10319000c0c285204c2030389910010a03100b14041c1410500101851061411941c2c100000b00101c0400d1a0840c1002039950010792529000304c005407805481e04049400005480e00c80008450002e0120038036858024845860301d1040c898000f102040c0c4105d03000081e40c000c126003444002c1800361025038040981254000b89032a48134003129039610300c1c800d2013400044c21004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 645158884 1250 645157634 645157651
    0xc03021e03010c03020c03030420040f0f05061804060c1403010b0309070f08030912100e06010906091802011b020613080c0609010903080708070c0e061201090302072c 73
    0x20003a0329400d1600791225418050b00301071040000b000c07400c2011040e80d40241e4492514490f60142c82d001c40e107894010385c041540b240c60722a03020741080c010761101c104129841c0051103560b031400c3c104205a0b0690100d1026403ca4900250005106600c03520482c59982031a941c0240c04006040d865042600000600340b4004244901040c040042d03400500d01202c104640a0400a6a603104d021b0920840d0092046c0240c0b4200c7c1c100c1400490b10b24507a2a40070014100100102a501c0d0401c2c412180c040b0728100c00843c65013000d000395109890341616400301e94907250300460300d44034000106281102c5400341c4200595402004000c01440c2c80424040c190424011905140070700031240d00c189010480c4007100e0f600a180c010840341c210406540301c81c6542000e1425100e1440c00812840300c040c2c000c0360502c200052240036031003c1d44d540d4495601e50214900301c8802000160140e07008580402c00314495820702240d612480409241400040307172100d401c1d80c0d0a072004076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 645160134 1250 645158884 645158929
    0x3060e010506030a020f010f120c21140f040201020c12030c1207051b130c050316030504020d0210030f05151005070b061516052506050d090c0302 64
    0x69000090198a030032480841c0640040d0b8403603400902101c2e031840b1503038140082d10003000c1a1601540a902c4004048101440b43d01c90040c0c00410ba0800c048408801c3c13000c01c0e07801001408244200c0082006050f107030440e945074159070030510903000704228114415250607420070b0b00e40700c003002007411080740190307215040f0101050410140c401c604000c02c800b4400e06010420003d1400c4019a860507018540c0380c000d408254580d680448941d039040c20305407401511a4407000840c0b24000c6000902c15800071242d046003940ca094801a50200e280d050450262420500300e600c9c00e5080d00f400502c5d402160402c10544600303c412803604803052548455500b01008104e40c0c0c0682840d02d90301e41012130790f4412441c0c102620321402440d41034429411a1080c900b204d240285402ca2880500c8040c40c02c0c80c6d903884046050081d060300110010074507e0a058048181c5031542c44807401c0202c4207020000501102c0c00569080c440e2110020140e1103507500305500740500c00448 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 645161384 1250 645160134 645160151
    0xf1413050d0f1e0308040f0203070806040b01060305060a230319060b1521040812010305011a06090f010c020609060412120203031e060d05010c120f0c050403030521010306 75
    0x28010300e0681ca0f1254000251070741060000395000450560013039000151020b442e0f49400407916014698201500c00d00c41c60301884184500000218100c1d0210b5805224070b44d100403c0c040310b031405200350308500c0200d1020300d85440e01a0030840c9500c40150448460012040c4041c0da5090301d0071017900d0050303580540c002c560900100c0c10070754414a80070385152514103e04540d20007550169140f8003c41d090214041003400300031a4070750340203054482d0185d41c50f0300f07003a4002d1442d00c40d18014a0080542c00c1c40d2341c1007480a42d120800000c1460310f10790580c10040d601c14650300300032680244c0c100720640c0c040d5188c070068400fa180e850502201c804080c500b003e4010103458600d070555006004101126003040c101c004054045c43c21a000782d00c0710404104400c1041500404550800c2c0c2a403000503800b1051810482e885281407101c7d00390b0046440813900c00c0320a60f030024508000600220380150010b00c1940c01d04d402d40202e400e421000b40303200b42000c5e0403c41e03041d512030411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 645162634 1250 645161384 645161393
    0xc0e03100905070e1e18010207080c012d0b01030209040e0619140c07030e03250506030c040e09070e070c0b0f1005010f022109100f1413050d0f 63
    0x20740301a22410a40080508164042c501040708900c98020b001c840b01c4001040341591b0500d604010f940ba0000795181e01e0246405030082d000380f000149590301c0e12000c05820200800d00c0050b01c91a400a00c11074450022403102421503a9115814960204581c1c00c56131260710400d180841d030040980085c0c2003441c00c1071034401e8120803d03250306091090f03d0f1051441d03200015089900d60011603501d40702c619056400c1224640b01a9141c0550b01c0507400b903804101500c030039000c004d202d0342e503240d85820421a8500096480030160700c0f00707001c140803c440c6442450f8121000b1011104010f0756201180f400c08021070780400014038415000b000c01c00103000386a0030480e1064900d1241c44d0104500020304204e106042c1041074658031490034070f00074484010030111400380f030400418200c1e01c01105a2005c02464082c4a041810300c42c020700c2807200a49814140da0341c0b080300c058009503401a5000705031030310440c40c6180c00024441d541e40901d56085840f070302c10381500d841903090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 645163884 1250 645162634 645162643
    0x70302031c03290603191d3c190c05030616050d05060114181503010e0705130e0108100c0f090b030405070504020a021c020712060c0e03100905 63
    0x168145404211050180c18501e0411681c2454401c0c1d4415071a503882d100400c803540b43c15121126014031f00030881818060034424000e164403050b04030b444c074000c4c03074181c400a8481d6807030040b840d886020920040005c40310203540440041c40032500c00103c002e0120f2554446901c0446140940ba0f2003080b942c1014000c030740d8015880d1000408004035104040d20510a4007107202e011a5144005500e5a0040c40c4004400081c22082c64807441c505000d801040442d1401902ca10b10403a210034420401c1c10460381610007003412190207487d02c880c1a1000d401070444c0380080c461355080400c2c006080b120319402001d03590300905803149018603840445502c42c40c1d5400300701111100f0761400d81c01620711400c44956040c9258ac2c0d581c1c40c20310700d0a02c2c0554101e980d00a00000390718408590002ea98a22100310415040b03410030344090a91342c0f0a5103215650324000a2005170b004681c81d030b4041074200348079007072440c46964404002410513030010400c00283c2d0744d610303110081c82010032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 645165134 1250 645163884 645163901
    0x312020304051305130507080c0406050607020a03120e040f050105120a112106011202120f071502030c01060810060f0e0a0c02120a05120a1406040509070302031c03 72
    0x5189403900b800c1c04198209000c8192110041d2604040781ca952a03546001607417a80180c20303240040d845400468544984241ca80e03c1142007007400b1420780303004011100d8496008000002707040c07840d40d075010385441c10704550b818850300d180f2807081c1e5221801642c001000035200007410b507051000f00810140240b405090b5980003154400008558007240d5804038011507000b845032140b00004108140f0503400300c00c55001c0d20000296203ca100e002c11491031003120301600f850095024a0b540f0035090100e0b00031540000010001c04c0703040c040ac20581c45080c81aa4138000c44202000e0070340c0c8032781e07001c501194041d0a014004581e944901809810400500c2420328900307441c0821200c4050140d414040c1c0c0c444a402d0080d000700111f142a0340703d0044181c6a018803c07001d082c9400c02010782084082e014001181c244892180c004001800c2c05e035103000792104400e00c8014500144104540d108640e40880542c0c1c3c20000b00030304142d81c64180c12a1000004001d0070b940444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 645166384 1250 645165134 645165137
    0x100e0a030f0b040c06170a0b0a17060108010e0a030905090a0e031614030a1707170a020324030316051006270908030403030504030e040e01090201170112140c0411040312 74
    0x3000c6c0e00c804120481001a0001c0828002091a941240004201d02140da0241d00010041c8184542859010910740c0c100d44020008012400c41a6601d81d250200100018000b0f541c05505005a1401c182ca0b250807044c03a200010350007900340805440c540c040081100149001c0c41410204035945032013121000190028501f001d0705260007814081014a6035840d052090b0001028540f0400100500404d009454600c0d400c126460344000c1d03000f070f20082401040b64044820007070f103441080c0301544010b4005c500d011841e90407980202c55503101240c2074080c984031400910218020403024118005e610454030003154445404050300c0e03101c00c41083d0a220000000c160114260380c2d2040d054200416103a985280450358843c0720384026504c00d24040d0800c83c550070541c0212a202c1c400e8861000080c58900c3d050f000c03030001d105048080a02c0c030004400111120303c03444002210404540401400b40c0025065510010218102c1c00d0045420002e0142c0c9903400c0242c880113 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 645167634 1250 645166384 645166397
    0x60e091e0a020607210801080613110f1f09170109020105030117070e01060c0308070825121404021e011b1e050708010f0b100e0a030f0b040c06 63
    0x9285100c0c0e2906285440640b184002150003802e01035446001c0881282c0c0302c10122100348018400782503580b00b030003000028030400c4001030150980c1c2300c03031310f2401d034000d8914039000100d0402c10143d40c07402d110458018004007400800c80c6044881804604016190203c0303085c148600040c000b140d00d121104243e0422901e800540d8020048a042d51840600e1401440d000c0c51594600b800f6603104811490781040001041640031464400e03551195071241043c0d240e00c403045401c01d02c181c0d44101d01c90045600d810b10000d58800d0780d24013412909054a21000502e025812105c001000248131143d000c1013008500d410f0312450400c000c00b4843e881540301d41c2000800c0005a00c0011800c03c80c0c204c8501c05000244c0c0e0120a0311141130001910148285001d50310340d0a0751144510a60030300c042822441d480b03005044c650003001d440b80c500458103800c211000d0a13030500060300f1412246000c000b1034981e08805600c14060a101c040600302840c11071800403281d400401006034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 645168884 1250 645167634 645167683
    0x501240e040303200301030c1502030a021e0f0f0a02041b0203030417070f1208011205030904091707060603020f010503040f0204110d0f0608070f06120c12060e09 71
    0xc0040c0d250300940c041ca00064a4030104103444070f070502020f003221400402200000030010381503640f00030b95010541042c82c415102c08142d0741c070b0044011103030150304402c03000101d0360321a0f1488080c03222000112440c2400100c0b425003054584141c418103a0000413418055051500401c1c201490898044210480440f0029168080903000070810302e11001412212443c0205841c5403941105048186c42000d2900440302300081921802041000d070000500c01c3c0150740b81480690444080c52600f480702c81080004d12103410708035a201215580207007055006005420124468000014003038214010850000300b401c0c542410000e01300304120000f40c0c4200290585641a5030110340182d00e60940361180c051b200d0030301c94152528003480036070351880d004101103450314020b841c0e8094588100c3e110004a6018210124200310304007803a14009074030415803855645418148400081d1a0310290b0300c0b83d500c00d40142c0021000c1c80f0800c3c43c280011144171242c1d6490041c004e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 645170134 1250 645168884 645168899
    0xb09010f08120a120f09110a0b0403230a15060816091e1509140405030304030f0c080d0203241c0507050a08060712090305040509130f050124 62
    0x4070408070703a0300680750202d02d00780d07980e00075207483c90100725140381401a540c807840e945004180c6c400d000c1d41c01c812041c0502440741840030301c54042d030714070f0000d10b40380034119201c01452150081100c0e01211508200c843d420506012080070148907070404041c800f203c84c14403055404a0700030042075081511050104240d42c490507046900b50203001c109034052080841111150300c006c4850107003803a1a400c001e01c3c2c034200b9042aa0010407082041c0b00b42d0300480056002d0880e402000c660040011401080c003a0595840944032482d00c400140e100e5076552200c0d800034003041c1036054000c0180041c0400c0720355403d41450200191740c000e4242e60001030b10103440300c0f1649130350102c80741401007848024040b010103000e01420310040704c0d40e2070340c01c80c0e51003c084aa08000400c00c005050741408180250142150180d45040c140750902c070800000000150520b5600c10005d03071100009403085031518040c0c0d024400001c3d84c4030b40d9000d40b02c4030551015805400e9480d040c4140300a6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 645171384 1250 645170134 645170143
    0x1509150310030201111e060a0f02030910020304020a080a060c0e010c0203060103080310050d0c03030e060f04150c050f060108160609090b0303070822060e060702220f0b09010f08 78
    0x302d40900e0100d16005071740900909005d100300081c070307102c82468550444034a002400c1401034440500401c0001480c2c1003003000c81c0000d403280d003416000301c0c22682c03510a640d00910341043c002040d0800155448080b545401100c81c811500542c440303901e103003010f030030080f280601042800e01995420043c0d0000391070740300500006086c0c25001c404a0313090445100f40502130031000d1305541040c0010306000141c1caa041c40110001051200490801e0600c08241d81c0d00541f181038040c00c0608061608544428100c442010404901d070420041582009100140f4051030302600c05941050106400c06100007003003008584640700c100a12688240d8100445034030010001d2501c480c00d00190840c422108082e00c000808030b090030440301d080c0c1e11840070100d1b0728a62580e050307464000390f82464001035a40d6005405005440141c10308820090381100358182c4001580040e0f60000100c400c480319415486507110740d000e010f03060215225000d00b2102c104560300b24a48208203546 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 645172634 1250 645171384 645171389
    0x6061602010305220809030714031e01090804030f0c08071d100522050702010b1008040201032403060608010b03211303140d180506090f1509150310 65
    0x4240da03d0700080e203113246400a10410f01318201001380610114108040c5a41040150034813034007401c1400a1400d9030b5032024a981c00c00a00030307107007081c2c040c803a00e40c903504041c80a01055484401c10f030700054121009002840c41448003a0be21106407e000445c0000c0741c000d40f6035980061014002e06860001d010302c1c5410100c40840d0301c1e5244210a00c09101c0d07176010070340107030004000112005c4407a035442200115218104003039604c0f201d00f01d007600c240008981e00003178031441208400f4410810164494018140480e0046540091a03580b6400c1038a40010b03a6030400c0500401c5114001d1f0401401c4402c024040416071a002a0b2a6200d070100b94860b031010303141000080004c182551210300d41c840f03090031402d80d6824003c00c410118441c4440038000e00302069107a5015410403000105000001c058960401e4244889503106042c0242d2106884681007595511151440c01d0913000e0304803140c03203e41d044103214007400c2d0030440c000d50100038420802c84102d084445401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 645173884 1250 645172634 645172637
    0xb1206132103020901080f01152708031902011103060f0a03080c0a1205121f170304080d090b120c07052506050a120b0315010602150606160201 63
    0x11500d824034040c00c9860040c001015089060360018000035056400f900480d942030701c85024035540d184000310480400d00403582028620500f816103a88200d16140b0648000d0401ca0810404442e0311000400103900c1810182d100103043e062102c142880f07004039400c00c1c0024060401040349001c0c01d07000c001c18240c06060b0034255142c00340d455031a070500440d0031251b10740d52180c16a21980e1204184030003030360340f4800ea5446020079882041140c0001d41e103980c1c0e046641d200c40d8845a69880030386224010655481000329200c03401d1240b100c0102e0505008655481c640040182032640f000061018000303c9201044056202e0701241d001c880040d840d0f00080d034030881d2000306400f9604001c0d0052181a10451485152119100302c003070f4003010051099580300e200301c0d541c0c4600300180f0006264071100381e40b51000b0343c102c843c0ca070070000d0544613600c01118010000600036030004c001a0300481c40c7c4107034100707181c41c01600510b05844141c81d00782445050b0303c0180308900000d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 645175134 1250 645173884 645173911
    0x18080a11010203070b0a060e060603041a0907260f0106060512040507030f050312060609030316080409090503030709060e01080f070908010f061d0108061f0306020a080103060b1206 79
    0x660310030701c110f0b540713294030480240040c10881d074100001d12050103078621030444000814418981002660310803039101140c000d0013020821034800e13160024002502901c6104000f04d921440809110060088041086500c0310902101c51500007081c10b092031903403402005014080d4800b0840d0b003041d1400c41c1c00440d5803a10300d006480e210301e40d40060114107048480e44100a4048018542115841c59074000c585071031040104503c00d01080d20f40c503600400c4081901c10018641da50268004d136402400c01c0c2d5540c51803000d541c00402e040301c054000004101e401500241e5504c05070001c1d02d0038bc1000c01c90003001900c105000f03032030707000390b0008000000d419901c80c1140301302410f0b441c1d00902260140e41040c4000d03100c603004804640b0208021840782405000c4c280c0d040781c0d42d0500130245921001e03c2e820540e140a8a24070740e60511443c04000b140c824002895030700b119660300c0f034a66145040c440101e4000e004814410200204032001844001800e2900100040c0c0e00a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 645176384 1250 645175134 645175163
    0x20a0b0d1521110301111908010605030a15050909060402090c0903030301091e0c09091a09181e061501020f120a0909140402041440050d18080a 63
    0x3c0345075036540461142d044d82444000c04600c40101c02403c00041c4071403525a6240c00c080c0300381d0310030f4002d0140d50001507040c000100d00c0c0209410038074015200400c00001162143c01084884000300c8940744158880c8052004508180180355488034104417076501342030042000a88030700c018030480219584a80c6003141d0700280720045805014126400c100e00d405101d40900680028887c03a400f10b0701e00000d40c3c00c0d0542185019111160042c00d0300c41580c0c60992015590596083c040d006114200000c5040c840780b00d03504c40c50140e003000a0045160141581285064600342c5c181150410040150768110024902d0641c401542145446041807a01142d140d0b610381e00905801c2d007000e44080c590000c0444913030040f4000e89050051813a000c8881c0e40e040c0c4141c038079400c1d083c1c400302c8480305a0303804142084803c51091041b0529032100d901d80122070207101064a25801000385030743c0e5260800c0001440d840711450141c07010b4500302845445904456020b051441e896104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 645177634 1250 645176384 645176393
    0x31603060b070501060801060915051e0901030507050a06030908270d08130b07030504140f130203070315140607060219081806011404020d09020a0b0d1521 68
    0x404007411201c0c00058480c90305050141c0a802c0500c0703240815481d00002003656400c50050aa43d041c0460010140c0c51500052204c0c0b01f030344c0c020300c001640d500e030b40500081c2da9640801c0d000310301031401804001e00380401c002c101000c641c00302060616003490b1303100041200041d506600c0622108604049844d122010040c20340c180543e40300307a0302c4c00c83e6020003010801804606514070a03403860b07951114001c01a51080d090040c012030414803003000510441c42d081550301a000c1c9c41480da111003000800c50100030680f03000015074010080000140c0d261050109080c0c0b04410118014541100700102d0301c42840304901680000903801c003481001d804407900928080c000c0002c0a0b11082c1c01411450b080d1a0714030381e60546500704070103140018446060720081c103151000d51b046942040025484170021070b60740d80e180c05000025030b5584594000800060f1016591103054040a804441080011039840d07400140c00f4407514000544000d1001e05891030500d29500300d080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 645178884 1250 645177634 645177641
    0x31e02120a030c0216050306161211040504050a0b22091a0115020303100b090d0609060501050f1c1b030605010b04091a03060403180b0d021b12031603 66
    0x40208103000254166505038076620a01155585030700380c40b0007408540c14081c13580c8140c414540d0641c041c0300414070301c442c8a6841c00c61002507003468402c1500e10703224601661071280041407451000f02d01000942454051158402a00581040302000c0b4400003844c298041d45400501040340234007a9410038142d0015240b01d800c080d142c1d07418010300107000b6105000f4007901031020707290064094650300010a0301d0180d0500f22180a50500f000c48040154102c8030003164003001207451b03500401c150344944141b40d4010400401d0941c10315040c008000220000c1601030560302c2d41ca0345c0740040100300404600e600001c02d0f0040808843c2c1c04101600640001c0c149034504000020311441040c005e000312418a5000e0001100800307000901c661703440c6043d50103070802070024000034400e100010303110385984000100151030320441c15154200e91300040c801507000640d4017200c4d085c9e030180344034144254010400200301c0190f21606001c064408504454445100588a40682c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 645180134 1250 645178884 645178903
    0x16230105210a06030c03060b0f03060c031b0d0f0c030b12030d0c091a0d0510210c08030a0905150f0a08100509040f06050601080c09130f060b0705010b0d031e02 70
    0x96050b0705c03075078503420603100404981031410300c43d598601c07899050b420302082580c03050b42a204140e08644c1e4540390004420008802ca0800080800402c60070001a100d40040c00700d00081c005014002c950014046032082a080f0f03204004a611440e03031a4000400c58219802226011038038400c82c50781941c1050480e00580900b118004901e8a03550b400009001c0d240500c80c0240100d803035034032079205241c005000d5034002048150044900d2004401d80b9060320b441815880d004907031383d0f00742600719041030300b4540c0040d0a0344400c00841c5800c1c08280788018142249500d01203684d06011031511909111400780415200001c108204d544100f10040002501400261400380303085112000d481c0401c5481c01c1c40c3c5000310300503500c60080b05200d2500c00c100c061030030440b02c08101c0f0410303c5c8200204071648610341518041024003903103008002802425485206603d4600e0a43e01d507085c580f801205c040b12040080ba61010303c825581403089003410043c40c0c00a01207042840c3c12 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 645181384 1250 645180134 645180143
    0x20d060f06020607021005130b190204080c0a091a011b0510051909030906121803210c0804060b06070219150302040308120916230105210a0603 63
    0x2a4400141d20b9004036003103204008a6080e030700ba4003032603852003040b94001d031098981000090306c07050000d03036a00040c81d002802800c1c0c3c4d400041c03c2091038020780c0d215800c603c031103810007491030702641488400c4801a014035002407024075081d4004036502104030030207038100849080c081c042e03549001110756407a0f801000ba40c0c81c81c40311b01340900c0504010359540340c00003582e541005284589209408a242c0d06540b00340006291030300c21180000401d01070540d5581d202006214511030a0480760f182c1c1c483d8581c00f0f11a050881c40200e0310400d019031890413070405c1020007403164410056503000740e0100c8000780c0f1350080400708616000e2107000a40043c01003a8604500030418149002c0314182c01c080954818102822001e03801180b00080200805005120f090042481c40c580e00000c040e088541c1d9003520014136071011549d80c450010404804210041c0380c0f00035100b06060002030178042c2c40d02d10804010f0030050f510048100752280d25031301190156005070844801150032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 645182634 1250 645181384 645181409
    0x616200916032f030f0a0c0c08250c03050f070332011517010903140f07050a0b0403120608101104050a060207050405060301060b0d0b0303040e040f20060d020d06 71
    0x40c03c003880d5106684440341030b10980001003200c03510b4024000f4000700d0b07564401c1c0040320b41d560b2100540008030100801100d00b0095488003039040c1034014042c0c000e10702e0360b03085840e504040341440001459001d05401c1041c06002003031390005504c04540241d011102415442171071002d00d89110544070045500303204520120382082d10484060340c1034560700140d12210034414608030741042d0030007030200d11110466000e064070b410260181403554103185280c0846640c800341401c0f1140021510341200300103100c185075204888803640068030740c0812007981050281599003d090310790954141c0c40b10222640003039100b043e5002404081c0814100c117440b44030194030b07900c4602845000e03600d44800113000b40790501480c01155051a240c40c90642c0070305254000c1d244419625030144810040001ca01d5904070000348500d00405d003900389040c0610340200420041500b0040103d41400941001ea544a040320203020038800010b0740c8542203103100000e403181c0d03440b01c10480078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 645183884 1250 645182634 645182711
    0xe0703090b1816061b08040902131d0408160c09060824061011010612060902101409060a0309020306010602030408060f010b07030c02061620091603 65
    0x1601101c0b640c903094150203950503060051424000c290007441410001038816040b1045c0c0342081300d030714608a005081d02c529054031a0304402c20380c1d01c6002d030030b841884d00210820140d4200d80c600401d403a98141d01d4100b60602d5220004503020b02c488100c19100f103500c0c1c130001c20a1380b0081000510a0034000d01c00c103507880c545642c0740d560421801440c12655144501614520070700c8500c00d2000600c2c1e0021580d560004860004ca000c2e2400c03125960350784045081805201c0800c807141c4030316004242c4098510621501030140154807040c0b0100407a4808140d00f070342c0c15582032650642c0d440c1d8507410402d20031005040300280294042c0210800071503041e5010008209072003c1c4421103e0a480302c1c000c45103d01402d20070f82d040c2890034403c80300000c2c4a00a10580c1c503000402c95030401880000000d00d10175074160403680180001c0510710011544500c01069a0b411075108400c0d103440c1407500d07101095030381c040c0201960f40e4408030700502c0c412541654080c8401080542d41c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 645185134 1250 645183884 645183901
    0xb01050d1806062621160506010905060109120f02091b0c0a0b160207030204050a060e071e0513050907020a2009153d030510120c0e0703090b 62
    0x10350701240c1035582140c20b0130000c86a40001d91440f101c864841d40002d250846000340d06150000401065458551490380c400700300300700300c694040c01072050009403c0c08c0050000d40340001076807099925000101607070002c031311404401c0e00401d406a600c3c65040c2c4da010000d80390381400c100c1c2480008408905528000000210540c40510030315a4088075100c3d0580d0035040843d00b2144030040c1c0c0460030a0005041ca600660780000c040840880c8840d2a4218081140c000f21808000180101c19140d4042c040b600f0005140c0810300300360b80b42000c04205500707004014010503001d0700745540030030315543c8208102c000194024440101c8500384032403500d002115108050b00c501b0b8183d020481d640d00010388440740c1a8001c10a60342c0758600c8240700e000010095441555820a54699221940101c0b8400b20701495a400042e5403609048205100842c0d4020351400c0d49414030000c002440301d0301c00f4090340e260070030101d078559821500b03c003c1c2010050051640c9019401e200d8080d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 645186384 1250 645185134 645185159
    0xa030903020901090e120705014701020a020f06040b070305030a050c2502031204060207060206010806130201110c0604151106242808100b01050d180606 67
    0x164400c40c0d08810340d0340c0e135000c41401d4031800b90059905410407200000761080403001480b00500c0b41c40086946200101ca8400c2c07038481c0421a030010b4607024003222484420038141c00034105107104110303004c0e54480000d42e40c0030b16100c001e014000c01c030701c0301145903540b605403001440911460b903900c42286c540106982c2003601c05111043c20000401d5503568000e050b6002d48442c1c40460240100b481d403000420340740302100741e8260203442c24900405603031600607c040d04c2c4a400901c0c06515100d4002c0ca050700c16400052107810038014005806c004180e03903003040e0740903e0010703442a1140700c2107050008000c45954044000100099174500a12140d0107041c0c00340c0321269131903c03200032591610822903041c400c240d00e1111141c0c010030b00c0c80c0c103d6010440504180d2441180404203031a5400d410503100802100b01c03000c0040c0d400812510b4880780702c0800c00d01c00b0304803440001e041070082e6050800c1503030300c0e459003500400c40e01031802089a0010420b000c041d5585500c80d03641d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 645187634 1250 645186384 645186389
    0x21b01170a1509050103080322050d020c1008010302030d050307050409021305090a02030f040602181201050423030304150b061204050d03020915070321060503060a0c05031807080a0309 81
    0x2d03041c01100010b0b4284041c414a0f04807a0059043c91030b6030f8034010111050b034440c0b8000650741c03c000b404a00881c100300090034a801041d0000d09000c14004200488003843c0d884003030400c1a40d00c018401a200460440882e04036406c119407070740c41d080400e50312806550440002c061000c0340106604044012850442e0020b0303509503619116a071405060b44821503150310605049000300c4c00044069000340b0001255409442d0820301100009902c08807480c9050f58a039120300074801032000d0707402031903400205250b0004a600741c1c03080d55900c9000017071015115040c0619004840100381d040700840481c01055266102800000c10028403015102980e445c030481c079110109901034800c0300c00c418030050442151000a851030301869004440440401c484031000300003410100c040324a8502050401245650030001403502e441c0004200742500c0c0c0c1000030041059402000310783c2c010600d000c0c102032546140b038a05180c44a141e100c1080e41c800c04555005041d40050309909 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 645188884 1250 645187634 645187661
    0x9050c031f0c08010e13020f10030e0d0201060302090f0901150303020f0f0111160503120c031b0a05070f170a0f1209082506050f091903021b01170a 65
    0x2d00c055002040310704103401d004103840d02d03945502140501504080000c82640b0040024400414120208007074010702c506010110343ca0b5244010151424403885c0208140d0b40f000300419842e40e0009101c42c032014200704e0307883c0350420204034001001e4110402000d1540018000c09a591030000d65030151101c210003180180101848000d4047c0180c0040c0440040c15500306120401c2c00c000b42c1a9080301110184020450f001f24520030f0041544650000d40c40541c81c1d1800400d460f801d43c0c00c3c000442944082040040941a00304068581c4140c2010b030070002c00c442d52503e401401e03400c02181041e4034000c01e040d003203d90300c200d0920b00c918092f90380000e0030803001550800d03074500900c02440e4a030705000f90b1814a4040e40039154030480c0003003541c3d0384003841d11144110b0b50700b0742d40540070211100c1042051042000441041c5c0421111600b035000503031002501d074070910302a00300c1400c001c000b0706002da1040f60860300703110101c400b910481c02c280c00c010f0020018a4120107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 645190134 1250 645188884 645188891
    0x301060605090909070e01170f07060c03020d020303040803160210050f07031a21071802130e040203060103170903100c180b090105090109170703020a08120d09050c031f 74
    0x4183d40342c0031070383c4c200306ca4010401c40e000b44d0a1541050314400001e007451070500c00e04064154288080054400070b102a0300c030800701c2c20480c100241032819407504101035500070814000003504100840703900c00e41011407841d0011b0555004ca003440203064502090b00c1c20031040c0207404003051841d90141c041910104802c514042090f01d0112a24285a030702061440100002220740080b01440d62014402e6034201c41c1c0b528894202c0300c02186400341e0269000c240c0f100101403c4843d0400b0f011102c81a0012b45032581c0001d968040500008050000030b400c00c030705c0300203440d054070903110008042d500d03d00303480c8200000034580301c0c4407100091215001d80c520b0005003040340054501b101400c2d41b4007460440192071640c0b02c113040c281003221a1000040080c00007000980c215100ca0244c0449455070042025680d01d0390809111500030701c0b084002d078440b040486e001e202c000c003004280101c0741e0502c40d0802080707c00700d54050160883d005003a1900881166100200481c1003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 645191384 1250 645190134 645190141
    0x13051f060c03360f14120c01030908041703031012021008090c0d1515080d3c120204120b0a06031707050f0f030f0c01090203010606050909 61
    0x220341c407100003034020b00810b40749045400200452a40304644070300c010300501440600d4034255804107215404429981403244084c0b06000340341180b032200c0d02d800c8440e400d11050300c582d426120321103002c20701c5c14143e451038514104080e200544e80180342c07000ca4046100802402c064403a4000c4070300b07107414224194041a82c007080e6140070328040d0058141041c5d078081000c00d440490002d01410000c0c40356008400e02603446050b0580e2041c4207443c4422001c0c8112100d5081e18900303411208410740611040c00319100000740d502c80301c0e00b5450842041c80054201c40e404c1001401c0701c603690165519034030812001c81314112595002035490000c99018689084100d0140e802096042c100c4041880007141103640342a802003c140c10001c0c6150742c951343c3c144030350900071a03402c015201040d21810f00005109011a8032590005406d080000020302600c3c0d1140d80c0c01d600c0410808070308051242c80951044034119800b900801c21640c5070b100c05049500800186072180c0041c0000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 645192634 1250 645191384 645191387
    0xb0a17010f03170319091a06010c0803150402210403080705040f0510171513090c0b0c1213091a090a0b06090a0b041505040b04031113051f06 62
    0x1030302100d8100d03141e00c480c140f4024002d0040c0d80050069081c19016002001440c0c0f014882c1854041c0302d441c4284c4641c8103205040d00c01c1200910303071070602c640782c4e10780d002240c0c0380c1003180d60010b084801800c1c005c0103d400240280a0f80e20340c2d010031820440d101054002044c170840c040c0b406070720b6081d020380c0c4042c001c688900c01c0303010b49002611803c00401090411244010305e1849508010f14212001010340c02d40180403243c2c0044d0307480500021026080003600381140c0002e00d0b1052065106035103440f148e500c40307489280c80352840010305801108003845a0344400c1180c0104c1a6030f624208580b403480040390142c0b1030310b54a880942100c02000d0002e603071103408007400002a0b0f0752002070500081c101e015605402410030400d000c0c090341e440c10700d90041c20b000c7c40059240e80c10301d80d084006c1081042c2170400d2100070041880050b0349802541c0440707034804512100144108040761158400044014099042078103201c050080460040d21080450100402c00c82d41c2e001c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 645193884 1250 645192634 645192659
    0x1401080303041208070504120c14100813050309060310051518010e010509060a12110903071505040f08010b040b012309061207270b09060a090b0a1701 66
    0x400030110850b8803019010240240c4e070031036200c185410400d080940c0c5070314036a544900304004071521908a03000388031000e20403650707000d44034042d0b80d41012101d50440c06070929001501840e00c1c141e0f0341c0a201c040087c10400c6569078013000c2c00c41502ca0800241203106180203024903849000544a0083d48076200002c0da15801c1501e00250240004440103480c2e0040c20100309040020410088400d13884a2008046c0e8600313907920495482c0e0030340e4041044560045100000b0310040041e010150360000e102c1d0245c854885240d400c000e62070070107469074480c079441201c6845a000c40010030807410360189801c0d00b001d64042c49040201c000449920701d040f84515140c00400308068074110407480130305101c0c40003800d2685003079031071074000103600001c80c1c000e40096040f802d804006001c82c1c51078588200400755051156051000b0000d2a009000748503024000216498089501c41d20b20040242500305a242d41d40303411107001848003541c0508440714400c41000000c0c811038070f86 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 645195134 1250 645193884 645193891
    0x40e190e061e06010f0f0210060b180d050c1c02041b0e040c0206072006150a090b0112020702030a060501080c0a17070302100903050709150503030909180a0b0a1401080303 75
    0x5d540b101417140c1d411042d641c0081002c402002c501c40e20b001c4c4d0381d00d041180724000150034813401040d1203411000c0c904010000241115004131100a003e0b800218000707010105400100c940b0070003400c6074100040741420080c40658041d040410040c41042d1070b01408400641030b680e407400003114042404140d64901c0440c030010307070041000035a818494805c1d0b9a00715480c0c200d015841140d45003c03803404400ba5514150a0340500310713640035207000c40d40000140400e0009004200601002034840c14030310301008500354000440c0c004540d414441481c2d4182c1c0850100003c0d611000079a1350743c00c000c0500350040c004800e021494034847e81c0e440c03d020390b810b8000c240340340c03c41c0d0070b12089443e512000d0091001c480340200000d241400302501401700c0202c0001c80d20038800e4846d051084981c0454040c1d0010021040b094450300340040d802690030003034148207522480c1c460324103014050003074080f514a40504c110500d051f089101510302010241c82c059803580062500c0344002e9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 645196384 1250 645195134 645195137
    0x60c110109210c06060e01050a051206040b040821090d030614130213090219141b120d140703050f0103030f050f0f09040507030c05040e190e061e0601 66
    0x2d90401c84519074641c6841c001440d03e14003c40c00a010780d4882c002c0d1012a00140b150300e07440c2d0014031042c1003c07041c0e100100f80032503000201c80007841c034031a115900508054180c68a0400040900881e40101c0312508a001d0b07601c0a40021441c601d212408159170346900c5004910581807500c2c4207004900594050500061041d002d15003003045042202c038807121055005d001040d1800c032403505100050a084d02d002d41e8030304419146051406484405900b800030a240d07120920704048140e5008520130501c40e410f01004100340e92a00341d6480c90301040000000d240c80405841d9002084614400c0d4a81074241c1c036080c00c1601510003c40d00701c4525050040104040b030310800c00700ca506025400c260b0315062114950040640c82402035481d820710000d1900103d050621610f64802030500c1c040155488803080144148034074070440150307040e1b40c00032400c00c0d048110908044800c202042004d142118800c50700c0d100211001000c0d508401070b4510811001c58006100341e405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 645197634 1250 645196384 645196403
    0x90b0a0204050f12101b08011d061c0203010e01020901031406010507030f090f240f020606010c0303180f0c0b0403112107090204151e080606070c03060c110109 70
    0x2580c00c3c40340304102d00c1206131642c1301d80b16aa00511038107225a210700031034650b100e14560580b95019024910681c000c507403203141e6019059046800d5920f194002100701d030550400c0903480c020181107264401e01941c5035180c4070007408038440550092141400a0700c0a00542e031154080303042003801101c0c0a4040b4100300304a40000384580044103040042d8106040720030786608400030301403040d1b0041492164110321090341c1410800707022064031198500014070017800c44000352a40741c0940703418144941c1903801d00405020b43c004c1a21962850303a003020580d02400d0940d0603402e040d80a8401c407a10200c042440c4001c44211003e480c0c100403290305c240c90050074050545d000c5028040e10000d1b0107039201c80d2190034001c81e0010050860007603121800c0c8035480140b420865825003c1c003040c40324603400000c100c0701242d5000602c0c200881203070342c0d080c00720300d00b8440c9050080c0344500c40c034004010003055034081100c0b50314a5554003284100001c07503600325801d004000e0300c000031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 645198884 1250 645197634 645197659
    0x1d030406030513060204030501061d070c0206030910020d15050d050304140a09050708070207090b0109120c3b0112060902040b130501030b0603060c0a03150b0a0201090b0a020405 78
    0x1c0d400041e00306444103000ea20b041da003521444100c2e04a42c0080f81c0381d0b511448100300180c030170780d1107165141d407c00c51205c02d03040035000a0654903600320000d005001c003200241000c038080c040320014030086002555a5070f101e40c003040081c10b9101350500b1030115064041807500b025800c0c024910360020046207818100b501215624100801c1141d10858003240803d65012a002e807902415954645142c18144440301034280903480d0480d40d0303018548501028036a13407210191003260440c0c107030150b40d1151400c0c0781c0020119600400416003940440d05c400d18004090080a0001c0c0c18101b0342c135000041c44a910790340284106520f00680420603c045031680c0c1c070a00e80c00d440140006190b051010200300d103402c10085140e9826070742c00040091100c040724059106000701c003d00110310b01100b0340e000f2801690450303001c05a4600c0c01514524001c1c100c03001a042d03c1c03a9558941014200c001d0280014600c121403034030303079040465120341c01c50013901c1c262400103100c14004103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 645200134 1250 645198884 645198887
    0x20114070f020a08030a0207060813020607080306180c0901080627090706021b060a02100f0915090f1e0831050307090c0521090f0609060403030c170c0d1d030406 71
    0xa000e080105821210042f44e070042ea07441005214051090040c00c1d16443c00a040100c0441c08600721101c001c103501c00c100c0110060012183c540509090180701611a180407031000c0c0c0c1c02c0c1c0c9600c0d00e074105002025260364218421700c2c4c421900c02088401c0c0503201d400c2283c039001c0c4940c00c4100048107000030107880c9003000281c416400c0742d1044428403501408101c0c10344c0c3c00000c82c50341c40d60b43c0e414054203210540e0205882c03401d50500038410b01080b90758550802d8100d450182041051564030320b203110b04629100485504010030036101e000803007900c080f04841c3ca103104440c07504030000609003062024a802200c000402030704410b0310703041c0e54502405c01e0301282c104111007008594010606c4e03181d600000c0d003a8925180d854a000c0f0314a1389010f01c1c403403010301a0750051041000b803480005945600960515001c504540001419500501c0d000c540300300c01030003801004450074900001d0308078908014002e0001c0005003030003d402158903030035900b554004110505c07201c2e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 645201384 1250 645200134 645200147
    0xa0806101809022113110312120a0f09170a030b0a08010b01020606031612060e0327060c0307083a050a020421020114070f020a08030a020706 62
    0x8489a00301418000001d00715821807900c15080841055404030740200700485201c007034452251100d550900170700b4501440c280c0400c00420040503140350419580454030300344480004050059403164903110400c802c0c21a651080381e0380c503a8145070102820380c8204500442c0030098001e800c80040c4122071041c2081d5034454000c000505840780e904d00b1882e11000a03c100600c80e10000050880c0d080000a0a182c0c0107494184254802d00904111441044c004402c4039411702e8101c140344241d2401c0e40c05410b1003940040180000324030b0807400c1c04d4102c00d40301d51103506454008003402c21010803155014003e025081a801880882e00107090308008107045010500c00c075140f00407101894425010700120400e0380b0304000207114180d5100d0103003a800281c2031900f0350034107051070f91000c800070006801620510386480d6200559008460341704003a000220304c903550b0540340c00c00707000b96404100701302e000c0c1e10046000500310764044141c40d0505034607409018036501d400c13800c6504 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 645202634 1250 645201384 645201409
    0x1814090601111203040b010b0c060a0c0210050c120a11071115040602030a120204030f060b180c070c090b180702030c0703140c0a0305060601050a050433050a0806 71
    0x140542e0a10003601c000040103c015010b141c1c1c031800b5135030b29207440e03c00c10010060f809817001110600100800300004034003660b0100300230310000b590134601070040303140c000300c00501d04d0740d03d180c481071001031151007004021a6040c1003031440c96440d1595444c04070340090170750b1050388000f440304800046080d062070400c103d00408241c5070005509038400b190f8425805030015034800111031031059000b11048290f8514980d0841c2014030b03680b030308480c600340e582c0c0080c141603840d18884916a0b41e80f070711410041c4150300c5d41001d45881c2d18030000640c8235a42c00e84d1003400340304000074900c0070342c021020b41d06c402034a040c20100c1a10781044e000480540503d0030b500081c8004058000700308511401103001c0c034205014240d8007880c03c0c1c101900905c0c810300400481c40e003480413030700024800750811020b10300b8550b90040c0e01700c101c0ba140986d41040e42d100107003c20506a1044580300241c41009695600d00f44003620207090711075101b103080703a40200d4880b0300007400c0f5242c03418441c0352 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 645203884 1250 645202634 645202637
    0x60333161b0512210a0c09080604030c0201080a0219020c010908071d06060c0a0302030304060501120f11010c0615060f0507050d120b0603100602061b030604050603010204150801061814090601 84
    0x701c13401d035003400c00040008441d208050390380e4000c03200095620a884a00070008070001d0320442c202610f004240d0184200064140724001c0f0208034000701590454080c0400c05a00410100407103a000351140060305001e4005800600007240c0388502049070340444060104400204040c400304030064000180840d620050500c25100c52941c02d02070502d66501c60ba001d107030749140034940b100c100e40060b00f24210b0207a849125000259441e0034031b00c1c40581142c84412982d000c000100c2d104815194020022400c04c0c1800c0b402041c4900d0a0342651040d440711006c020150304101da15004108000d08107500190780d100702a4019003440701000b0380d410000c500b13a40a40003080702584107443c8855902000481000215030500070f40350001029031036480c2a0341000e41108603400003400040c400d82d42c8001140240d41d00354101c2e40181100c0fa1003411000368010080c140140c01d00c602c1d40441e030000d4501e03151940603503404056421402e4243c83c12640d90b81804070180c0011309190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 645205134 1250 645203884 645203917
    0x307090605030c1c022e0f020c010e040e0d080a0c0302090d0b10030602070b0402010906031a190f030c0801050702070f090f0b0307080106030201030f05060333161b0512 74
    0x140c6c030782e10030248045500d04a50b01034102c01c1c16202c0c0c040f0782602151020007800160715405194007040038101d00300246040c01c4071640c0307540001c0091074103410300d081390300c505601c60703c841d60044c0e400c51040180c00f800b000b10607164031056081c0e100d01c6031020350250480d00d00e080056100c81c2d620b50040c41c0c65000d0b042135a00c80d951142268086401070740ca280c0000100b1086680c401403002c003401642c43c052003000c0144462504a4081c400f81610841c0d81d191030401f9501d5840030f0f036000341521800045501e40e02d0030310050f13000740790140e001c0e0b95080000081d0000d00010b0104200c0e060442e007650b003107140602c901d00400140c0c028160f03894580035080000e5404014040203080e4110001540d05d14500c0090215903081001d150114140070802400703507004a10504070401c244c0e80f00c001c007007800040c9455015a94276010034070b4811402c1c0301080320110b45078006c80301d054803509081044c5445200010103521300040c0503134004102c0c1d0390304000c1c0f200a4150102003100c00e0717 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 645206384 1250 645205134 645205189
    0x5181507090e010b09090a060b1b01020705030f0415050304030f0806040902041b12050c0403030c14070303031d0102280e040501080c0109051504120c031a060307090605030c 76
    0x400d9030b01400e9020288400c004241507815240c22a003103501f10316582010054070340341401e026580c0c0210001c841c1a03030514449849040b5007034045501c9682d201d42039070b6540050382034200142c2c010340110120503500348a1030303a196001e002200d02840c2c0540b200340800305490340072540c103000208501d070881d0302d84180d10b00680303c07400341024110048103c0c201000181c0e034000d05014943c0c8586c05000d081c01d0078000041c3c11042203500b03894040ca0000301041050a2280b000e0b0400c0c0c0501456114205001041c164140e02608150200907a100a00100103954500340e00801031032484400b0298040014002d188a030503410a049044c03049041000d04002401c88400341d0041446401400e000ca076150b84c400141c070003400084034200710720242941841424007032801240c0f48140f000698a0512403c5601c103030040d9440b0211102c030354441e61194140f15416541a4040e21500d003001c220418980600c6007a200094000d1624a031f001042142d010f0105407500108491310600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 645207634 1250 645206384 645206399
    0x904020a1509030525031b1206091703091b01180303080604051b030a09020103110a0c05010c0801080c221506020c040c091715070c0203010518150709 66
    0x1c28480703020a48403a88900d146007000d41c00c2402e0600d13000da021074900c03030542503000038a24140c241c98225030801c901c0a60001052800c00aa0b0800500c03008518210010040a0380101c1c1c0002d00c183d4104203d25a86102d401c01c41c00182d400c4115a04801c5130b5500c2c03041c0039a0700540d030000502d01421004401d43d6509464201c07a007062700026002e078100449800e05014141d0454520481c07803100e5901104e01c0d50041c00094010f500c640e49a5018009580c4642c1040c00c2103006164811740d01c209111000c3c1072502003c07001ca4803942001d01c00c5c01050301561000f0b042380d402c4006081c10b40710910030001450f030000e011a81201c13003140a50801e0b1180e100764040844080d0210006604004001e403400c640a15614810303402c2c817110840403580020140f0031502008500480c8185e82e017017981c20480402051010b411040381041740580d44020182c14160080d40200000d499040c80811b0b20308080341c1d40c4035954402c52840c0c0c440b0304401303841f0368092181d00d0100d801a484195 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 645208884 1250 645207634 645207659
    0x40507030b0c1206030d0503180a1b0510090503030a030b0d0602040906060909050705120702030706051f051504060516330e0d1112120f01051507020904020a 69
    0xc02c19000040400d83e44401c0540e1030b50240c010000b10700508040407000303801003ca00c03005102d00140b1b019040c1c1d688040004100b008180d03984000150328212400d910f0301d445030454490f103031248200c100b0b4005101d001d2500d90701901d0025026520341400c03c002a40a00300d02e06d580780d0010103a0440c900401d204c0d10242000d0280c07040082840e030724100006000c2c0d03031203400c00010249007100388002141c20030120313100c5100c01407800b681965603503000d03400c5026840d00600a039040c40c1c2000038000701c3c1d91100a042e540030031035000441e00d4000740a4442109041c0164020b4100301c14003006001d44080c0a23400c1c0f140c0c4100307818400c1036840b08008142c141d801381480fa19103064480e542c010a0441da11003a001c0b6040240720301c580324040d643d4031705164041c140000e8001c10020440140803120011141c4106155218258405021445022961208403a00b80d01c000309051500b0060030b0200c84583d00b4190034204c943e020441c05840141c422a4005d000400002e24210f4414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 645210134 1250 645208884 645208891
    0x60b0f010c200a08030d050121122129010206040605220803040b15030d0e030f030a080907080a0c03150b0d06020a09080d1205150405090703050d0e09010e040507030b 73
    0x700a144c65443c460b0a0000f501c2c810b8000002040b44441214048410941c45449c80c54101880a0032130801010548003800e081111230000c81181c94816004c10b01500501c241a810313920700b28503044000c1344000004080c03818640181c000d000450041000d91704540d80140c445400f00e4601c000d92a580540d880d0010f104882c03000010003000103201e40010307166441341c1c4540c240b0180c0002d9400085e21808030b9000141801a0042081c44644080261b4059910081d040b83c3d07850249010240401b502111a9130310f07031040117004178104401117902c9035803c0c0c1c0081191015400c0d0364400012403030300c0120813421503880c03101b014240d442c0c800300c07900c13640921001680e8a025400042031128280c01200269006045151096500c11800d00c00301c0010800042c103505c803403081070700400e180c10802d030303101c0d0408080c041e00c120302080c1c00040364070481c1103a414080e00001a245c0104443e495944040030f4401002502102114160300034411400d1b102d0440d180d6075074603091482034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 645211384 1250 645210134 645210149
    0x5180a0608010e0c0306150a0c06052701061a07050312190524010f0c051b240906070203010f11040906090e030d090f050a050a060b0f010c200a 63
    0x40780100002e110f03091103640c10a0356041e00901e945041008079032280881c60918520f41c02c00a05228a40d00c520708020030725511010502141c00c2c100585414142c8113001440080200401c1e0b4118240511882c01214003c8401b03420020300c8e00800ca0240d00301003002d0701c0304d0008000040e00d0249044a051284880350042d907906070f4120017100c210355000703014400780e80d0099400b80d5503945582d030900450f035003441c1200f600c00705038100b100c6203140c44800403d20b1041e008594503a54000d4102d102c8001d0503903410740204419038950b100b404000740780740744000c81000b00c45a20300b849802000d9140c005000417500c0e281200305001140d144088460190002003000e100c860300324000c1c2401000810000d222402e0201036030354407441201055590140c1c1c2d18549400c0044003a0701d9000381e40c12a0545884034602e08100d500c51a04031000c882e441d00e0a24054103520b8200030160340d048040c0c1d528508142c50342e4684a80e605a0f010014407803450b800c42000340e65603640300c8000380c80300c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 645212634 1250 645211384 645211397
    0xb0a090f1a0301020711131104030f02041b1b0f05030d050a0f06030c18060e0c0c160b0703110c03010e07180603210c0209040609050f160605180a06 65
    0x4507001c500d190307071002450750701c6640108240d0011500060902074620003c0b2594440c452039070f00054000c00f0444001400f8450114001003030003020001303000614000c2d039080c40400511a265000030011210020105240981d110880107941010686d00344c0320f005c1243c10811191103542c0f071a000590900000c9446100700300c00ca0882d4058091200480e0006100e11400c560f07584600380490b00a05442d40d03140c400d45840b000d6950460070040c02004c58162150610002815580d400300d01c0e203001601c1042c4003150080028a001e20848404003212401e1001694089440c034040003841c8089108407900391015070780c20710900c04910b107005c00600007945807424071102c951150754001082ea213482c0003040821010541400c090b4943e00c1d40202c0c01c195000c00b9030315400d4400000c2d401200480420003040b00b2540000c1c2901d00074002c42c3c0c3c866000d007800603030304d0781900c484c0e665000d245102000154061005011075103210340010b403140400d03501141000c0000c0e8400c200040c038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 645213884 1250 645212634 645212651
    0x903181203020c061e070f08070b1f030b0402013902031c080c0d06090204171005011503020d090b100e0c040f15021f0c1209020a03060b0a090f 63
    0x804011040000f0303030640340c450401c0700180c2c42c140c01c81c0340134100b00c0ea0300b0320021318030082144a940d065002a0700503603080d12151a0309048004000860307840d460103801e100201d0b5800c541d0354059003200d40c0f080c004a01c1e035079254011500424447c01101c80d02a01c401d0207525205211410b8821b0720f40c0700d512400b01300a50041603d040100c840c244150484030039203014169200c000b031680b004100f42040da40b980b0072041000100101e5022010080c4042400b04e181c102c40814041d071000110708607640030000c00a0321080f910284240f002801d5140318550440303000740c019146005115100084140f52a221201c80540481c0c007068485140401070018a200d00d110540001c01d404042e810f00b81000c64403003540645000702a034003c0c402d8881c4003140c0c070070840035050641141015101200c0c582d404005401c9603000d0300086407921400ca540010107108900304140c0041c40c425605165880316030007461440c1145801c01c00711200030401c21414083c0b0011341c04900c01c001061030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 645215134 1250 645213884 645213887
    0xc1a0c0f100f05060306130c030b0a0606030c0e0904060b13050c0c0d1b02040213080109150c05070317040f050d020601030201140f0d0507031d01060e0c030103050604060903181203 79
    0x10030041c01125042e00d80f10a010321510002500c56000100304e225080000301e40c10700115501c91030744000c29104401c010004104030310340000040b82c403651000c1c010001c407810255003003458038a82e690407001c00c5000401181c101d81150800744170140040c058465148101c2090b114112803104c0c0030030f00011003140080742000250880c1c0b10034600801c041c0d554200400070f0501c038034800703071046401040620040000c0420702e0000d044003002003184034010300c2c1100a512010f0b01001c000340c078011040703841e2402001140c1101d58565070304076100d90070b00d0a04c032285c00c001d0002e4a41200c00c0e60b100000505c20401807190700d0294000b08aa5031440c4001071040e07c0310040e034900000c090042c000310340544000c5e213140184071400414550b403140000c60080c40f4141541102241d0b5036145031b1000e906601c42400d03141651041b022a030b965a0900041d07210070303c00108650300c41320000300880c01c1a409402d0307692081c0340407036500c0c0801e070441d800710845811084140c16441030000405 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 645216384 1250 645215134 645215141
    0x607030e1905010215060609090106080402010f02120405010c060b0603012301030603021005070212060a060e060d05030a05070c180c120c050a0e01020c030a0809030f0304030c1a0c0f10 81
    0x151540342507004403428100000d4480a0038901d000941c406107021a43c01d68410056484034080501610300c550380d581300091081340151f40580c00b0640c002481c0d0042480880c9628090b1040640c03035141500c0c0800440f40300c00c030318806072521581c1d0300072900d1603035411005600070032200c8039004078110000d041d07000c0003041490306410300d481c1680400c016180d540001180c0151414020f4803082c00e400400c3c2c5028a040b044109401101c0401c292034101d030b8401e0080d034003169031005075941d650040c400007c4040b00c0c040c0c1540e205201e000100c034480c030002e02009103d07900041d0741c3c507a0307844035407500b6480c840c09640076a11002e09034a001e030300001c00508104504d50074010101c2d144401307492072151120b00170400c102604401c44a034000c024a10400c1005003c40701422554103029003190803061030544240a2090001c0510000200b81c82c1620341150801d51103600d4000002c40c0015042407941c40303030000b800441000e0b1018080e4041c4c2501d142c4c00381900591a10720700c801c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 645217634 1250 645216384 645216409
    0x4020a0b0a2c0a080312040201210f05090c030a08040b070c09020f0901030c0f140d020f070c170d1e110a110907031103010b0904020f130807060f0e1306050607030e 72
    0x4551040c007011010881691b40550003a40a0074074036190200e01102c0c13148003070080b40c070b6a0558288001c0c0c106089980c2c1c0828440e5642c00c0c252034110034203408258564402030b401130710814092009101d0180d09100130601d0520a0784051334041d9515858416a0442e141407041f064000c2510303e0303196014058108a4040d501c3d180c128461000009884005010303a0704800010115182c40144030550442d90032184d00a03010340c81d20042e2503e0641c45034540102d5040400c8001405001180090031280600c660f07241c0c1045d07d03842c0d528101004030761255001c1001050440002540c20a0010160307090148442c0b0180c00f40343c10511000c407201174140e408045c940811a00001810425a81552454109180da9015074400500a805640e03007819000c034001034020b0710340303030414100802c03101c00005541000d50b48070003d86c0d00c001c04445810200c1cdc0d01c00708807a21880d03c0d044403080b2a00d440e00c00a04541c03258080380c11600b0500b0120041521403842c140680350400e010481c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 645218884 1250 645217634 645217649
    0x5101109030319091a04050a0f05100f09031a150907020a03180f18060902070c030b0712020a030b0103060b09150318100506120604020a0b0a2c0a 64
    0x180034000c101090380d92056024030710010200b08880b8900320301c14107084005041c0462042c0201840d02d0101d4400d034001d10446200e0b2a0300300c0005400d003c00c24601c41200c100601c040c1384010000000e41d02c4102440440d010440b02c154080300085412a120310b80c421601e8207400d043c603044147c440398514200000748642d8000d001c20260a50000313921607072a5051809400c8280d43c540325000d05a0a80c00007031413601101d6002c103c2e92949000c0031001c02010b403060003059683c008170744c224492608040d044050300c59080c00401e225007882604189945071914205240640b0380c1c4c100d0300f00d485898001394403108208115079050003130300f003d03048004040380b138500c0f0f40c40020b19408018581c0782d081d040100010301c0c07004d40c0d07507800054181e50009551030220346403803071001800c080344e090f445200c25202190501300005400c07486268064259048581440300040503900301601880400c1610a80c000d281c00504024003c1d00c80c000c003100d60000c071000100100c0968036008000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 645220134 1250 645218884 645218887
    0x40f06030203070b0d060b030405010b0102060c070213020307200304080c370f060f03050f090d0813140c0a1e050411120702101802010903110f0d051011 67
    0x1da80c003c100c2d1400c540c40d09581598a200684540b0301410b6140c0c4105a019400f004101c140302c010b404c10344c184802603003075545503922201080303214010424069004894040080b40700401c3e5802190011014100407551884122030318200d2014640c020700260008142049007450400451142ca0402c440c030f03101e0007101c60070050740c40241401000c1950090032402c0322029607a40c0c03000107002c90002010f1001d442d03d0001d88000000500344000a1400380018046902e40c6800d0b8014103020f40a084030180f01481100e9944d0041d000c0d9030010007100505000030400c40c41075100e50003842c05003200e0f0200d40204141482d0039406075016002140940e000000d1003203104040e14411180001c010100500c242000d000706540618003040c1c50060066581d0002000840080c80100034080820b190071211402603404070024041070081d00d042c400284100d031104031400018103502300020701c0c44001112070202d0101035855030010220f001c00201c890098500d200f1081d29060f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 645221384 1250 645220134 645220139
    0x1e0318010e0c130b120a03020619092316170d14030718030605150a05060a0c030302250c083706060b040b090f0f06071401150306020306040f06 63
    0x1c1600d1040f2410405440d40c038802104070307940340e000c0410000d00c24800c4030384800003840c020b0341c1d800043c2c1d20802e01110b10040c00d0310303240160003040f04066010000ba0440804682120320080b4070381c07100c036103601802c0c0107450809140c00c1080d005060082010300100b940c603840d581801800c4000c1d00411028a8108041c04464011a900b1102e5860540001200d0408031b84c08070b155500010500d0303080c101400107841c00c258451039901000c94a031000b41e99520200010340c42003940078408a9401991440440d00a5018200f52459544130f58202c850424a40303808064403041200c0045e14602c0501c5000300400541214480701c0300c02550b80c05200410358401200c1100d00c213408058180400d007004100e800c0080201010652142c0300c40d03c078622002d16401c07000ca5503024000c1d6520400061034101d0420260314005800149804116110218036031070318943e130700c1250b40750403110412005220126000318003e075401a2641055001c202c141e80f000c0c8401035801d401c0000c00d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 645222634 1250 645221384 645221389
    0x901050405131b030608011409071502030408011127090a0f0b0d111305160c0203150a050a0506030c012007080f2103070c081e0318010e0c 61
    0x100c0e030540340300b240e40745100040d51495101500e003c40b10100b0f100d000084031801d850b0550850004e841400009106403c011185038054110864498005a0000100300a03417120105490640c0c40e0500c10f403860192541101350035100c000c41c642500c4040010f1640300154001040140c18003048040d281e40910040040c0c454800540500c00c41d60769038150b10300301c02c881d510040d03d000c00600082d15020700347c02e00d852045500004980110b41080740550f1a2041c0d20819200348814004903c100b80310032400c640c4c0034102041242c26104503c0c02c2c40c0082c1c0c1184200744500e04250b400f02e058074040c40d418003034030f8010384084e00075400024400c15503a0800006903c0d12070792400003469403a030110881c68031031268011001030243c005081c101000108a85031a56209203250100e0504105510010710003182c60400154640e811803000504030740040c0305030328103151814941c1620903480800c96006646d20140c4200003c1e0303841406a0a000320780c00c500041e0040c00b42600c62001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 645223884 1250 645222634 645222637
    0x1f0815250503100504150920030414070506070b09011104080c19050616060b0a061707051b0a05010f0509250801090f03110d05040531020717090105 65
    0xc981003442804400529480f000180e09801004014424003d461405103802c49850407070040c4d15016090603030900d85014841c01c40040343d600200340328559502e54450b0402c3c2d2643c0b6070030320714901503004002035a5444401400c11070303000303120594440c103080543c98211040c0e24150581040107010804c610900800c0c040580300c0c05407400b2013100c3e0807030303141036600311140c002c04e41c003104c080303203103590010544038060720544900f0040002e80380b0039041100700c02c460320640d80014080302c01041148111150316400442904244c2d007000740200d01c642199a42d16080714080d8410400c0b41e09112007401400400c000c50501000982480340e204d40d181d4040c1c2c00c00c400e01400341c0c03050880314545500c8001c0181142402000030100e1f91600040002c8050b07820b0f4001204d400710242d02d450085083c1e00210300310340b01c030b81ca41440c20041c00f0f100604580001c0c8101d1540102c0b078080c40e415404541e4a03142800016036414051030701d0044440111b5420110345003c0c04900c0ca01c2e6041310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 645225134 1250 645223884 645223951
    0x22401060f030b0d0c080a051b0a1a0c07030b090d0309030f032c07030212030309100e0102070b040c180209030a11031207080711041a04051f0815 64
    0x6008240d40301c110003c0352512940c4c0b10010050710340c41e1000105040302180d010f00c03007446401503460b00340b540c0d50080c0a07401e816105941c06065048200a110820500caa40d00d1112070242d9060a56809142d0709000e1141e2040d150400301c4800c000e58008103001000410b038036803c00300203028094070002d144d0b1540a69000034141e031380c440c24050240c1c428210311031407601d43d80b07107081045945040c0c0e00c400151108074066200300c01c60b840c1154000c401d8a200350468030081c0740c201c02c05000030300a8030300300004440f595802c2100d44041a59024014820703030150710007003001c920704102100b420341260104510a8414002644143e5001c12440076280c0c11a9810340d113142000d0004c4c8c10903510540c145c0090100103041c03010080d42501602d90180907030b41c244004000e840074401a0b845000d00d070409200fa01c4040980382ca019800340d0741001c0014682201e1038030f0590100305280032a004200c5560101d2218085040720100b00340d408000801c540c004042c000540c1040240d040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 645226384 1250 645225134 645225137
    0x60c03090303030b060c061006081b0921011505130605091306022b06140d0303090c0f030f060506030c03060c0d02131701050c0a090504111207022401060f 68
    0x10030600300c0031780c0e400013982c00c000c00e80416a1520706051024082e030103913500caa40e0216081d03100080d0685000e16051f51007414110300c40b86803041d4401040200b001c0041210203076601560700c02c841130424450381e130007103410400000b403041c01c10040000401c84e20181c0680181040c10034090781d128a205103070800c03a00c4840749020341c8107142c5203005e070040c20103180c0050782c0c84480540c80d00c6280607032601e03018403403c00c12450380c03a0074125251008900c04142c007c4140341540c1c4c0000c0c071950024144038018080801e880f501d9400302113105c0c00710f03441582c0c43c002c030036101d009102c0540324aa40200c41100144422180c18001c00d8580400415031440184c0100300102c107245250103c0d0680304602d170b2030f8603941e81c4400f003035078502c104130160644d90761810002402041500044a07020806a00c40e4007249107032008207c0500311180c50009070040a00002c8080700700f50740d5850140035260090800360f00903a100c8010b01c403082c0d00e42e840c2d5002180040000c540c0250382c9900c400300030b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 645227634 1250 645226384 645226391
    0x140a0b0a1a0409080d050403020a1506061e11011e110406020a0b090c100f03230a0b06070204020703030516020304030305090607062a020d031e090317040b060a060c0309030303 77
    0xf404d105586000d0216482c0030179042100700302c205640031850503141c078402ea8244030160440c1c000e601c110b9940d80076290208141c0c2440c142d0f401c94a9080c9030004540346001d580d49000340c500d9900f0744032600d600e040e521032030351402071546451f402011300b0046201522800c061800c40000d43e100c111030005082d02c61082c022880303510b810b01030700100340405044450000b80420000300950403903841c03100024a4045032035601e0280e149040401e001c2c0c2640000f550329410f1000d0010311542c10310756440706040042100607200c500148c84628000c0e01c0000c0d880c50201c455204450101080300110f400411040c000242c00c03000b0f640117490190b4055484c2c80041c908074000700880c4140513035160501003e98003050302080c941c54902c10b04d5080c2e5454042542081c2c00703079012008a11041d81d003032041d92081c1e11f066848100d2045c020302d03089802d00b030f40b4001c5165400d02610203407a850b400c84200a01801e0500440c0c0062510345400541c0024584004000c1c0d103160000070700301902c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 645228884 1250 645227634 645227651
    0x10b030307082a070e061e0a03110301021b0717060c04030305030402130e0c01030e0106031104091a0106090608070507030813050102091305010311061c05090703140a0b0a1a04 77
    0x406071140c103c030082c601c0c11502c900c0e4a406035100642012130341e06100d40701d5000880044210701c120100268400340000c4c4040742980d403480c0325a1803140b00d06030150360074032500d481640707400c501e4520520ba1301d020740035103410501d401d500c541d038500e08480143d11502c14484510000c100322001c40b5054609a52283c48610010f22000c4001441403e894249842e00e400154003090b41e803150780d02600c08200302d0301c200702c01a007650076a11024040503c0040c0080700d038103103600201d40c5c0f10705c12391645005400304486035081d84004e03000301340000c81880c4107000346900301640940200544c104181485130a54000f0015007008100301d420100484008003003203025015a40e000200800c080c0050400e07100c8000240380c2403200b501c1071405201c407038001c0d040100c201d070190008604d00000400788980b0781c2015140103446681c0500ca41a00080481e85541d1a410b04020384405000020b00a081104904001400c1462081e01c0d000000030301d0f91501104403030080059501044107003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 645230134 1250 645228884 645228937
    0xf04171623031b011104090b0901050f1011010906180c0614070f03111b09100806161b030c030e221503150e0d0c030906030506030a1502030702010b03030708 69
    0x103005c038001000100080340204d0128810b0b080f01014a0003942d00c41c4160f070380d0302c0c204814140c84041d070300c1d0002606205000d2507841580700c500d02030141c800104417041a6a1014200e0348042c8141003508281c0340441e082041418201d4010900f0380b50942c10000900121143c034843d08030004c08041c3d00005000815004d40100c035200d913007200a448064414404034900400342580440c0718038088800111840e01c4500e0500031358403244000c01c82c59440c1d102e01d08540001c0c640c82010301c00d2400b50981c01190911002a1180c400d6480c40100b800e10700c3c0c0905401e00d0f402241e81310344c640400d200c40701c0506407252441021040c0c4081400030b0400c58a03440080c13160000361a61800b440000741540241e0040c4640c2401003045544004107440c04542c0300c40358050050010320b10b98001c011491080c0c11442e00144006d0030b403910b805856490794448084000000c0c29550040104103a136a020321aa801c0302000354003035880c00040d643d5280640c89101c541515000f00050030b07c030f10740e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 645231384 1250 645230134 645230141
    0x1d070306270f061e0801060323030d0501030303090605070305071215050d0503040608010b072f04020307020c0a05100c08031b070506060f180f04171623031b01 70
    0xa16a42804001c499200c0d180d070118094440c02c4c103541d541406100140042051140c0300449800a5098800801d02c41c070024800807002c0040116120602c1801c68072452807241500035031107903d000525070780c00d1900c0000d6400003000c450034545413604100f240c1740c201c0c0c0741040c089190701c800140c801d0f103007103140403900058014a411a02e4407144904004002004000799900e0303844e0020140c3e81c4601510283c0308040c0300924010002d0349a0741c2030810701802c001c158050801814413000d0a20124049030011603d060050b409440056541e04003003c030350f0050101070f00c241d0030b40d8503505070140c140c8850700402400460000000361a0381c0c111010300d0170300700003210a1507580c0300303c3c1410b6070390390b40944080d0321034a120700515080b4500f203211800b421741c40000c840d0b103a5035a070314400e8000b0801001590344400301048a0446c540706802440c0f074054440d071003944e81845003020444035000010303c000381010000030194908000040d0741d0850001581c00310342d803800c0403545015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 645232634 1250 645231384 645231401
    0x105061807120e071a0c06150a120206040b0f0909010e13150b0303040303090e010b09010903060c18080304080f1605090403020a0c062a020105160218011d07030627 72
    0x10907240310185c14200b44e01c1c2d002800d8403000e144c01c855175611914503001c01024000c5105034040115a02001510440082110840c0c0014800c81c1000d130384950a18160780500b00180000388001400100d03868004e4180b4094060907800880c1c62038068415040c11a041401620ba003c00c524a204c603134a442e041a070182e1005016292034036940c5c5005030500300980148a00070380e0600022420543c00b070195141d4680523502c484003e803030341d1101401080342102800810100310410560450030038094401050507000035a42c0d10318184e280703402d19402015405140c0c10810180101801c108101000e884003103c08410503242c43c80c00f03034079100d40b00800501c6010004000660325402c42d44a991101811040f2402d92455031040601c943c4800382c007e011070028400384880300398030310307130300740300c284081c040800e441c41f2101d0340c41201c1c01c240d2288140c03c8965005400c1c01c0441000607401150700d050030710695040000e10381800300c0865028100c4620b007602c0245d50840c42d0000740780d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 645233884 1250 645232634 645232649
    0x4020f0415110d02010b0102030d02180301051f080105040f12090914041a100e07140706020a030c090b0d0b01032c070b0a02030f130f06020105061807120e07 69
    0x54892048034082d2100c40c800d4080380490164401d1209001e0040c043ca1010760016809945000200310a000003500082c1e483d082040260400c0006c54409104190040c8041c12031509074007010713000c114000c0c1d0a600030070226414001031000150714040401c4c51280d004a00308603805030310301c0850b10045603502c107010b4241030a0284850040f85141240a01c0c0601c031106010781c0500350003280c00030141e0f03480e04c03080302d030100801c062603c1e05041d1f0303000072591800e8607030200419640c0310547c003d10019a00541d00080041c11a5054840d01d950340e9040c0c10480c0e81f90707190a100340d000c0d024480d659501d050b12402d403038000c0d078070a5100a0080ca14000c104204030703940b64410b2443c0c1d4003a40100a58420702002045040c00301c4117440801c141c0343d005528021048180a41070b40108550380000c070042500850700340d4800484c0e90140c401a40001994a00724041028034980486114181802c950034000e0403079001c8002c43c40c1450281c000f059003480302e18460701d4241325900004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 645235134 1250 645233884 645233909
    0x62104030903050d0c0b1602120705060f100501050f0904020702120a0515060604060e030f010509100507030b0a030807031806120b090601020c090a09060f02031906030201020c04020f04 81
    0x10550081004819070f4083d070215114840700c1807060f1031054079850040c04103c0c14000260001d854040c01004a02d128810784500d00f13000e1450421981007503400f00c0d99a0401380070004184040011903034000100f41c45110f140b8035041c0003800601c05c20032000d080400003e1020b220b5101d5404803048154054044c00101700034840043d118100240115268040c40c0142040011802e1405010303110007809545841c2c0750400643d015102844025010301070881520004c1400b84502c2e0712940c0b1600180010b8a00004130104480c401014081818030b00903482c02903455130040b0105880c8e0046c23070240c0c4c84241d03003401c3d181d405241c0200544012020004140158020106e440303820241e40180114440da404010141d1011210f00f03005070300c500d024082c1c5103000202c981e000302d041c01d00055074442c1c5407105000d558070060904159a000024072201d8421800352810000041400700502425903000135141d242c5030000c640302c0d0380c003c103d41442940301011100182a90700440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 645236384 1250 645235134 645235141
    0x4060804051f0b241801030b090a060509010f44010218010c0209070309030c080c0a110d0b16020705060c0105040b011205060601051303061505041a0f0621 68
    0x10806403c190040c240201e00c1421030f15444010003051302071482601c1a03490410060800c210005400e48040e241019140d410f82c4000b0b841e0b190342d03070340144070851011501d0750030a02800b0071080c4c180d2268194007d0380c07104100600031500810501c465080c80982c02080b0f0055040c0607103114010a840c82d102c0040d59540600705500030040220b072041d01b07001d40100380d00150b9280070700c00e101039041030500b000103c1141c0b190348810189071080c00d00401c90186034840c8415038000400520307095002c0724046003400443d409988540030219200c466031003071551066551000609088198a9891140440c180c0240981e40181c44041e0140792074071081c0705454064901900d003a5903202d8013000200344620760060b051280c54110300213100c40d072110302c0111104d41c41aa039804000001000100010b4124040e0008014107900721040f01c504080c00c0100311030700811144030001320340030341100030740320321750b03010b084030b10440b0305986461000342c0807419074800052940d0421301e1101003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 645237634 1250 645236384 645236443
    0x30f011a06040b0f0c1e0312221113020c070e1e070c0f0c12060b010207060905191508180307020d080904110c0102121006050406080405 60
    0x103180c003a21864060a003030038203401840030078411405000c004032010012a102072400304003d105045c0028121030281d00201217450a499824460007442c2c5c000040d1240d41c000301c0d0136103e8000d00d01840740707040c10310200300c0183c0d6000402d40041c00d000100040492581e140e1800a903110300c528000d5644142000d4842d4440049006038041c1000180200f450303001d8240803046000311811031085030f500e403200c0556655400b4141155500440041318001424400d4050001c01400300820b0703c0d559985400020340b5100d8009a04562003480c2c01c010362580140b44200f11407054602002c9000c416007440070030314091700802044421002c2c01210503902c507521034031684071403a03140d0303062004511158581c0b1907030f0006503001105507031510100c7d5611008102d04a40240b001030084c100b0b07003d0390740c0e035081603103c3d1760f199501051400103122900300d00c3da482071108411034003407820032402510788d000b43d0203403e00300490200010200310301007000d088112140d1801c0c0c2e0b00000100c11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 645238884 1250 645237634 645237641
    0x41419090e0a06110a02030406110304090207080a0e22020901021221010e0103030801050108090102120f100e01081c051b060106140a080118093804050a06020a0e030f01 74
    0xf00c0c0c81918100e01d0040b0707940c0610a9070703002d60179a0301a41c546840c0400032140300c000b503006800540002c001c0003031060054030041558a204000050b12070303ca0303507409045010705034180c2c0e0041c2e881004110b44194448041a40c01c0300c401c0b001601c1e1140a40100d1801c45031031006039a101c8001081710301400709200380303240002d607998202003a80c0c980d10f028500d902e00b8800140481c22640052000358050f0003119401b0907500001400c0101c84440002500b00688003010007444410030701003441d803103c0f03101e006040303402d15404142d40341c946121b58507100c10021041c0031780c00c0303410756160620401c200d401864401004901d00180e0094803515801c0a1160602107031480c010040201c90703c5e01603039642c007020703212a09940e1030030500c1440b11008169803400c40f95101948170005134040c0c02040e00e010202d0b541000762481d619040004051450b0000608000c8000c000c00214001200f0340d402d5840b84000d0317103c3c0700300e840a0b118541d11018103030385809103001e006100b050550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 645240134 1250 645238884 645238903
    0x2121906020405040e150f0c070f0303150902070506040213091a0609070e0319031e080108011d060714120702030c010b10120203090304080304080d02010f02041419090e 74
    0x1c90401c280f0301705842e016a07071940728a81a40c40301100d800203118580c0141815030007145211004d1503d000d60b950740703540c88100744045010941e1072480600c4900c0004600010746841802117117002e1141d180c496132100000d10092180c0300c5460051384201144e040300354440d030300c15840745a40c0c01c244079013001d003041190054001c2d8803030000a0b40d01882013881d030710070410190103807000d040701308500002c000498006509105002d450001c0344211501c2c0403046040540d240c0c0700f40d5050001c020b00356100d100c3c0e20309941180e2049100581d00200b40f00e42c00205d14201000f4401c00000d0210490080300075400c40c02c8940000c01c2061500800140003082c0440004c020510501c000c014010300c44140785400260b041740c80b1001034403594000d43e0405001c0048074100fa648020b0a0b26603031194125800c00c0d0003180e80d940701c00760240145411607400c218203604041c280308461885031000c8003028400c0020107411940c0101401c82d00000c0c200c01c0d2000e000b00b07a0b00140d040d54910400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 645241384 1250 645240134 645240139
    0x1905010b0409020609040209120d0309152309010906110306121506100513030807300f111203010f0e0f040b04021f09030b0609060d02121906020405 65
    0x1091421041c501807049681441d8010441d5041020b94000d21009401a407000c4d0307004a2030b0070b084020309004100c0d00d1003020845d030b80480d41106c0c600d4401e001180083c075042d107050905401c000000340755800f410800d4256042c1502960741c0101103809040d03113510283c0664030341502d4011441a0b1001140300711004c3e03602c46402080c0121841da901a00d520100790300101c800411041d14080100034280720307403480c01e00e082c4080a140c254068446500443e98003000141c008100030b907120040a900186036410ba00b007d25541c1c55818140b9042c2a1508108007420100b5040740603c0a010724410001e088820440124002a1840e4001e020304501088103000c0002c110001c0011300788036502502e50320120f0b031240e54802c264500c0c0500220703131180301890a280300c1c3c2551100c0400c8401c0315981c0d18006491801c25116010700906658011440340c2d042010503110030b0b0720408450f070706480f01d60011980c0a64241094007054071440003000c00c41c9143c0601803143c01400684604 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 645242634 1250 645241384 645241391
    0xc240f02160902090d0605130203010b06070f030804020d0b0f0402031e03040e0604060b1207080601090e06010f02100204181815020901021903020f01061401050f0912190501 76
    0x4140d0303407014403500c424015582100c0500c80c40b445900034040c07805001c0c00301020700300d40703560345000e90ba401c030352441e07102d600000f0b1102589001d0041f00076041c3c0076210030780f4040845d00c5030140c200c00d0100103820f001e05940428219280c0d40c0c2c4540d1400d40002e0b0544107424413035819000c401003610306920030311810301d0070400c240d62011040b075003103140310040d40ba0030300d4100312907016440100700c1c030781c010358030300300096a0030700003005050181d881c1840c1219844c140340b01508050780903051034108402441c081c44104560000e903034000c202401e08581510390060120702c0d14042c40d0b014080b103400480c00280e0b0201d14103a40c0140c4810300d0061000c4c03480c0c00d100e01c3e0824203010000d48020084104400b07000d0055000706824203062066071910145254101c111220142044005a0282c3c800c2000c1403000c2c441c031409008860416103120740060002410303070184809014084400186001a03640c0e44041c5903404824441566021410f0400ba060a0f01a44e1000c2e9010f508 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 645243884 1250 645242634 645242657
    0xc130507141c09060e030307020a15050f07030906151e0e07091205030720190503330717090a03090603020307050d0906020c0f030702060a08040c24 65
    0x1e051056a145565201030551030380c00c00081407016000c0000d00707903000e0340e480748a8000640c00380019071045c2d00c13a400405c070004030b916003d0600ca8484c00001c0c60340346440700f8004054100200180c22000c54074000c611003800d030600b00f0042c41e103081c0c01c00203032980a000252584080009800201d220300485500c107558810103c40e0030f100b1519080040d44410090100c218007502d2039070401d000c3d81c11641055401c0d9540040f4003e106c041e10050140741445001c0d40c9000c1c50f0320000c00f50003407580c0514074501400301c0d41c0d40c4248451400e00d10003490352024004c845080400d000c0d00c0d4100d10241034244904050005200079000c1d40c0600781c05000184a0540010542c000c21740c90b03542e160340d991034084100c009400c050500403c128082006200c013501c10702501c058540a90b200695450700743c1117403450f180803485004200c1d0000d105140242ea10709085e0b501002c120304104006075154a402507010384103805c001c101c80c0d80000ca80c003403414250358101c00d240b900e0f15211104070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 645245134 1250 645243884 645243917
    0xd1d0d03111203040203061f080f01021801021609050606210919080a050a0e04090c0e0907030317090c130f0b0a0b0711010315060315050402030907170c130507 70
    0x120885000c1d416921000110b2140c23000c02c0e07100011414504462282c1d5501c030841d880c1000500c5038402144d07034001c6008846030301090620240d015090004001c1081005449810505680b080c1d1081503034904c0058480c0d00da170000c440b070350b080060812110821004009842c800c09523501000341c4a54028400449080000c0305030180c4c0280c1403e0809000100840d07a0b40e11000b091020403803800050030b0300c0c0c0c0b40ca005410305584228020b65240d41081c81502c4880001003501038154000701041020a03003091101d881004a00080c1c0b4040d550040e05900d40b183c0800d42030342015144d00c8207071741910350b079211007107411656030207004543c4614100300080038240580c01c0c1e0000104200000030b200c111740501c1c004e0060401190540180b00c03040000700d1164452b001194482c0300441c100031b81e0510280250004a41c11421420415030080d541e800c0d9010b85182c880c003401034203079840c804225404010303000401032591602562004405041c041c0c03000c4005c00c08413110040980e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 645246384 1250 645245134 645245137
    0x504031506050d060222080f06090303012306091008010806060603040201122a090e0105060723100513150c08072102040f150f020d1d0d031112 63
    0x11480203041d50810f0850744c507010b000794842c8403000014040b41c3c001408151943c10707940b00070a0f01d10040c0010505810b13032941000d100400307940b4141c100b04018080805001c045012448140074101e45800f007130004281c0921491900540c8108149050007240c1e41c415503140c140c80100b019903c1d561074600900c021404150740090100e0501c81070f2801048a5500c944900080e120340d1040d0700c0507020904c000150b401b0100e0001480c01c0300103008803e0260026401400c0540b0500c0c80c0076042e4440700c20100c1421442d1068545540d040b00c1c03107080800805080b40790b40b0308204454104641044250740010b00c0403105a4150300c0710120054440c0301d10020114292656221682d8080088449011402841032030390003142a581e01c280243c40078101400c10107a02e09900c80c107107003010403140d003a10490410004480400e12185a021880d0780c246005d9003010a140c03100302400000c1c6a002091203a0040f01280c544400d141d448010106504c460740c045d61100c0c0c10300945040075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 645247634 1250 645246384 645246389
    0x170a120605030d0c0206120412020c150313050f060a0f050121080a0225090b06030c0f0a050d0c0801090506011d0d0203030f0c0607090e01080d030903030b0d030504031506 75
    0x1640001c00707440fa0b00b90098805166442c80244040d142000416524601c010b050303806444501143e156400c83c2c94040105202040c400c580030f04816401e41121b0744584001000e414110b1a021242001c00108226004e460341c44403050720b20314602641440e0040400c02c010b03000e0326052000004416a004030080d504580a40440f1200c206981300e644c601d038007950700c2c03a045208aa9005928440083c0611070b00c1c000800a0582c071860700d40c1000036980a0056a07115400820500000d0300400c0d080f03610703101900c800b40d61981110b040035641c4c2d010303502080e1107207402e1a1500744c04503801002141651410f4000b00066201c600c01100d40410000d4490466030020964031064980703055003841241c402000c49140c00c0203000a015217401203801601198441810300c034407560003180740c10243c40051260b05441d0301d002007060380c8441c0550014180340d9078002d49414544260400004a00050222000b0392994030b0b0003400c0340c0c001c0c481664002504143c21070300b4046409403804 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 645248884 1250 645247634 645247639
    0x50a020a02031b070801090303020903010501080c061803010b09040302060412090807030b10030204290303070b1815011e051206070f0302040e0a0b040c03090506070c0c03170a120605 80
    0x5050909000c0070801056401110ba2441389039400103030798100b405240e95640c440c0e640540c80c0d011a20a00d8295601a0004c0b644d9400c2001102090b44516050b81e90305000b075810145051801c6011034010201802c542c1c1c3c004420030204410b00d0740000310180074500c02e55260b4036000d02007a04030342c1400d003030140500b01e4000c02c1d0104045809030b03505641180c0d50240301340d5010750301e074002000c5501445d901010007070041c0890b10482103441c64414140e5058010b10f1400c44103596284c002d520091400d454032164030b90164003c2d074100220440d48070440e944070f4041d40c58030082c00003250003c0c00c0d07003a11940a8000304460400400e1003902200710001400c1c0ba2301c1d1100c003a20032982c20351f044002c01d0340c240000541e0804800403d1f0189000043c00111341480c6410702080e03032100c18201c000c1c1420021500009840000c013141d101341303980f500d01580b000303900e40300c1c0e0b041c2c040380c0c000307010b100c950303016460013421901c02068109215210394440d42c802000403402d45000c1d11a003613 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 645250134 1250 645248884 645248887
    0x140d0e010c0c141b04092315130201210207060f02030105101e0e061e2104050a03121401030515010618050112021606050403110a02090606090d0b1801050a020a0203 72
    0x40301c500740780c0c2148841504c602800013441030006048400c82042013100d900c01c8d4080c50a68600c6001c0c01c10300d940045100095260690094001a20031a10b0300b4070540c5040e04038404414180c0a0b9060301c484036401901481040118060100650420302500f0b1107003c02c001c0d030323804090242c1703450340c4608a01500320b030004981810540d001c002040103190442c10403c400301d24103900c40c81803805143d912460503101d56004012034120001c500c520b040c0030806030305010100d140003c1c807100312030345450030000c446425800c0d5001f500c0841500b80444800d0000402044400b040f2244024003d404684450b0b98030701c01101c07041007500000c10740d000012403d0019510940440003452202c3c040545414004001002070a040302c1040e01c0742c1c0c0d9904140001c16501c1040e0203041b0224600810507030700715070001050740d50082e105070310889000544103038a40300c9017445480303e07810408003049890110101d440380350b500036841500b5464000050b00d460303250700c265100301c02e25500030f6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 645251384 1250 645250134 645250183
    0x1401020703230f10020c0111040b071101031d100509030906070b040c0e0403270b0a03181a040312021e0a1101020a0f0210020307140d0e010c0c14 64
    0x104041d0b101c074412009024041e07031540c80482c20001001d0041c3d01d034000603a030300520030401c2d0850b800c10400940c0184100002c1200a0011003521030b459080891310780352004150050b40104151988100304056260503414134590221304556210103484086c46140d5903110200d44902c07403080510791000080c015907010548520f40d540d440b9210340080030000340c49080f10204424115811800212942c103604400c0d2a03829050b444d0f84440001428220305080580419004a2130070350101a41c1c0c1650307000c101c0ca21444c1000098025074405010400201c0f003c040c2401280d056010036403c4102e100444100c0c42280c6110205995401702080030450300c102c240d01c0280300c07604010002c207545100345428401019a13440365102c019050307010701c2c40642059014012100e10034818800c0188141e0850307000d441a02d0742801c41c59460500186440040c020a00010000c1d86406040005990450f140301080c40c09075010340d425030705503a210f540d210740d1803144000160b0400c80c0c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 645252634 1250 645251384 645251423
    0x50a1e180816020d060b18060303030a1e0c0216170601050d050a05010f0c261b040806010608010302121c050a0306270c080c03070509060403060f061401020703 70
    0xd80703685008074040b0000055142c0009801100a6400f902c13802da640171600706a04d080d481c03210100e1003414052001c0d00d8901c000a45074080101042007081c0c4554001807082400c0e904202e001000c050108440b2203041c900070350304d5106107040c002c400303010358000c41c00804540b050140c0b26a070070001c00e00c42c0e0a06041c0701d0342215940c1c00700c886110701d142d0a00001c800380140003004040310700001da00012400000c0151051044402e013144c0700f810780400d200c1d56a210540c4c040c610034440c50840150a1a010305132080d5403152030580540c00000c11220ba0000ca114106ca008407401c5140380041002581c036110800d200b01e10b41c980040040d0b10003401000903110300503181c200002c070340c0d41e40d030a40d058070340e0302d000403e40c17a0108510113141820322703100f4100662010318010316146007071000c100e140d20002e0609014440d000c2045219a594503046502541d404001170143c120051000d4002c1e2015008410200101c0d032103030743c0c065100080e200200d0350044501a00c0354184d018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 645253884 1250 645252634 645252637
    0x19052805160503190902010e090f040507060c150507020f0607030e100c0806010f050d020f0403020310020a301407020f0c0f040207050106091137120f050a1e1808 71
    0x49042c2300c486502031203139540d5007007198890900f40049000c580340501c2c02905152280e00050f0078017084c0d0f080400801c0560083c004d5651112a00050940320620168600906410b1000c41c0307108140030800c5007581500224510300000040f134030004801c000000a03903800015040002c1e0754a800240203602c220080c20041c0c0b42d5092061600030704080d40c8080e6071060f441075000c440000340c200114103080024081041e4800c40c11800c0100441c030081c16280104850303100c804001494661140c0350b107070503014284c43c0004c104500e0404814690b06c00c0400c0f0b50010160140d44540403c4250102d4040b9000d54010100c1101224040c108802500003038002e861a40d6600400304039100d0303074460807022484400307605850f4801010951001060032070484005c10400d941c8481d58140110b90550801150516616060b455010300006208540d105082107040c0340902078500304c503070301105140016103c00c0c4601440b100103030302580c1045096078210451f00e009100441c02040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 645255134 1250 645253884 645253901
    0x4030b13150f091506031e02060301151101060e010617010f090906090f0308010f090e03030a0207020f030d0e041508030304140a0c0f1d1905280516050319 68
    0x4002450548079140c0204e0802ca0100b0a4526030751244140140504001558100d039203216031070b1418a0954003141860006200d00b034041c40c9400d4502801c1405000540d000c10b42610082059a0383e5504446c1080420300ca150080b50302c010340f00203071038101307030003107050700d40e00c0303542543e9a80340500d408010202010292491a51400181d0006026200d4100c60074081e03503401c17026504049041e808903107582d022000c160303d44004240001d0001c42580d0340001d05d0000103868502500201d0312162820802035854003038816080910380d0421049825180203546c20020142046607104641f6914082c80296500038030000d40028615010040c034221002c0c2610768a819aa0342c4201c00a502c6e00030098480007924144100c0d101c2000c2100070100d02c1c1480b41550410803140d0100e0a2401000600030751500001107400e08005142c0460450104803007000500e2410450010720040c0c0300075918400714031000312014802d005590044049840340d06c8a103044084000c010300d07400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 645256384 1250 645255134 645255161
    0x7030903020114040807080c1f020a061a03150f070c02031929160323040c0803180a050d0215030417030403120605010306260a020d03020304030b1315 66
    0x422011981c08805d00401e070040000030014223084102178100419402000001d10029074490600791540341d0000700d880426030042070001d0200d031015100070105004003091a0548170b82c02101816000e203681643c480c0000c2c840346101603c03084806c582c40798144e040650305501c010050342c0301d00080183c189001d881414a4465680000c0070b011350305410081ca041c1181c416010001500900110340607111114a4208156a944120222820004030192445080750000a8100122a0340880103005031404a0303865070112000300f490300c24101d2070380e4010084540001041d04154961150347c540c001c00c500212940080940342640000304159200e12900340040b20880d03855006500031800b03941c80415a80503107885000356030181d48018101440c0c03000401220801003400c1902107822400c1c1c52103241224080c500e04030089034080e5003c01030300da800041640000092013200d1103001d08000b260b950f100e1500082c2d07880c1070082c0001c0e200703401207988441c0d81c0e80a80723801540d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 645257634 1250 645256384 645256387
    0x60b07110a090209060d051f030b15040606120c09090f0914030306010c030c030c0b07110f15190b04181704030b3123060105060417120d0501060806040207030903020114 74
    0x23403211841085581c0d03881503a441510340705210740701c0d01c010300c210764000e4240c809222203807602c0740041041c07180e40f48001c0d46d03d55480103081d007140300d02020301c010f0050761801d0000707000340048503000700b201810032501421104004a0680c00200c240c0c1c0c41150161034030101d02805880640c0c00d40320a110450400c04807201001c0002c1306541c403103014000559a6207951035101e00b4192400740e69561248103a84040314a40440c08092640307940524180004d6185895403000364014081c000d44103030340070f0b0070001000c43d030100e400c00138a0000c0c020610341c28109101c00c0d00185520603404003800d015121000903a0903d0205da6a414501d5040d480241106043d441841e4100140d142240c3d1694840081900361201c91512100c01140704090100c81d45044000b5400d0304c580d100341103101003007143c4000068001d00001c07160890422015a0395410740c0c1c203200003048240650b0303011840500104405041c80c1c4299400340d60b05840c0d0003069030640d001980c800541d92508a080c040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 645258884 1250 645257634 645257671
    0x1309020f150c01050709031a090c0111070b03090c040c090602250815040302060601090f0504091e03020703030305010e0c16080f0c030d061e0612060b07110a090209060d05 75
    0x2d0034882c0b148030320740d030350749008100f4154500510001241c0445902e080b074082c4c00d00c00c01090110b1401003d141c24208024502c41d01e00c580c0e424100c41d40e110700000c440220410040c03480c0850f050640440c11101041103414140003030702e001c0c40340e00800740181d000b5010306c01d2070308088020b1105040c1402246141540e5036140b1840e100700300e01f078109001ca00c04140300c01c05804210060308a442420880484c600f0000c66a92003800ea108a91040d80c8840102c0d05101c07010284441201194164064004541c20060340e1081284000c03400030b490701000007418040050300c1405250f2202201b840c03c2c003003480c24100b0005020003030300c04000c104801c0503000041d1b4014090143d00401440d100c0c00c503004c20b1003c84e1102d9001c603000b1391040c44001d2441d0700360200542616480d091002180041c0c1000318000c0627560450f0001a40001d0001c082c044d80058188201c202114400e0180340c9601c2c6120990244e009890b400c40024481c200c2c1e219420b40000d03034010301da0b525403100c131503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 645260134 1250 645258884 645258907
    0xf040e06071d060a120f02090102150a0225050f010b06030103110307080105130218011a030403180b0c2a130f02070b04150e1b0112090b01051309020f15 67
    0x1404130034a840031400348a008000c10b802400f520003d0400c1803030860400c8880c40010b5101d08a0341215199000403800089600c0c6181e8165164a01048101c107020085910709006610414034151007034490f541c011851604140a40882108041d100b00d0030f50b4a565281d0b071517140011711090f0715018100c03001c02c00540902c50b0a10480b0304200010901100b40184007a4002c9074880700301d074100110045c0000402002038506803081c94150681c0c95443e400d003164408110b040c4420180c52294001440003403407805040401c9001054038100f0400da07a40780d08a4403c904150f00c10124990f082c0c82c1440c1c05501103844020700040072030441001000b01d001c9078450b4070201c0d03000102c1c0d800d210612503102c8200809451501042200c0540c0d0107203c0d60310f04100035900c6a1403e00b0501940a92250200b01440144100b040c020841207203000b01c80b400d400d00643e409000a440c84094200c928003806c088690003401c6120202c101030240943c0148001440415840800415101c41c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 645261384 1250 645260134 645260137
    0x30e37031e030605040e0a02030c060f0c0106090c030f09020a171501150201112701030f1d0f031c020a0c02030313080607170f0916030309050f040e06071d06 69
    0x3100c6a82c0026541c0c100b02c00c00045880b0650004802d50049010200680740000e00d00b1007400101c0301c041d11201c1d0300305460b20a2162a200c00015400d10300006403440d015089081001c07020784050000900001700c66003100c05d00c41c8065800100300404000140140741c104035500322240a5980880c03d412022540e050203070b0051100540d111f05500e17403683d080c0b050817948101e2b03d815501e00200c1c0002d8140c1c44542804030700c4941d0503c449407040e03a004e54440e071602e800c403280c24071241408900703013201c0c0c2805544021a03801010000c69050307401201302c0e4504940301506024032012500610000d4210814150600203480b00c4480580e90801c00b0384004403090b800114041d0a00707000c6030800b5405001c940c1440394010402051580c4003400661050162a40c01d40b00d41c0c640703200a10f0803107548581c4200092104010052561001d824025101c00742c0e1142e80c11482c035001e003c12a9111010400030340c2140000c02c1e0030501ca08210f0100150f0b03422a02d120340340020018406 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 645262634 1250 645261384 645261437
    0xb180303041b1509050a090501082a0d1103010b040b131503140706030b0328030207030204020d020409050108281103060c0a0e0a051c03110d030e3703 66
    0x104180e04010805e92609280d84000382480d420700b44419403400c0b00d1183e0310f01543c0c6120f1100540340f03501000903004131110300107130000140303d00c034805441c2c10703c01032075500f81211500075400c00100320224100342c092a5402000901a1107091075540c001c80000c1c070b5451203891402100b150000f0201e20900b10115034801d05a01401a007454800c000d01141d045215841c0260400b41d18138074100150a1444100c07008065043ca0803d1a8035040b4103100381c54000a600510104401410b0f69207a8043c01c25510700034420015641c96040503944c400c2c4441c031661880f41201c1484404400030300c100c50040317100300820b034030340300c00103001a08003d0100c0790310002e40c0b40071800c1006654801d0010601e2002a02c0c070031a800e0514001c594404800841e00901d40170300c4504c1e40800d032280d680e5031005101d00c003e4071118510002d0050140c011064601618418450704c80d0403400304500204c0d040c0c20010103428042e07101002c010320903001c10b9042e000d03c001600a01000000c11031496030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 645263884 1250 645262634 645262637
    0x604090807122f0706080901141810091709060d09030e090711120310050d0503070c051e0f0607060f051801060308041403070b07050303040b180303041b15 68
    0x1d040f009008508020300d054041180c664040600306050000104043c42030300d81c03a00c1c002e44555904403107503014210840302e00c24000c190004100040f004486150b410070100000d0f990719098122101003580c170103000161281c4044024511448000c50080c0b02c3c0c403001074030987c04c04011401c0c40c0c0840d80c036140c0540100303190760203202084c034164071000d920403124180128550034000d601507542000c0070300c8a444440003c0401e41a414800400c0002d00700144406180760702890702644a4008a40468400895400201e66071400c0400703e002c1c42a600c079224251841c0340300f0090019440e14046801c00790030007801022410902130015a045540700108007405c0011030800d800484007a0700e091070349090303014000141000221402c840340c040b044683c0c1e00c2d00400181c01c00400e81c2c881c0e07014403000a0303414100040030000d984914054007052200f43da5100c01020b429206084032901c0d50010000203001980d81003050744008000041d1000040d12207901314030411b1501e17003040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 645265134 1250 645263884 645263897
    0x181e0306010f1505040b220f031a06040b011b0204061206090c05060a050702040e030c03040e0f060a0302090118450c050d140114042108060409080712 66
    0x8041103616030510483c3d003440e1a514061400c11014014021400e00103c0840ca40004504010749941c60340044d001d542e486c0c901850b0b40386056081c0007482c0c0601c0c41c503500e422000070b03490f151a114200150106844003132041e808003215954044401074200d03800381d6503204c0441c0a01e200601800741e00c1c4034003000181e00c841c41c101980c1145c040d41c4410f1145130100300e40c6e103d00d607000c0280c5120580c141c8001c5541915010101d046002c1d4000c0314866100204001a404804807081030040307840e0140000c0d591240418059100c10301d010203904030110301e00400840703040d6514009504e1500800086080318030b9500020030a41812104135224034440d00710030020b4502152001140445800703182580c20365500d800000103100d1b80f03204528842820090000c03483c80701c1840785090000300641b00e49a80d0542030100150780645600b90300402011706941320860461448241e81c40b241441e07911b400400c00600020502142d850340c06105c4040010040c50f0540c00c3c40c06642c5695 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 645266384 1250 645265134 645265139
    0x3361502160302062815170601170303070801210606030521090d020108090f0a0c06090b0304210c020303030c0301060e0603010303120b0616030801060201050c181e0306010f 76
    0x340f82400107004054400b5194135410044c1e4071280c1701402c00c000e4603a000c603000411210940062069078854240e88000c81450322100e1000324001d4142c8005460881003024504200340d580d0204403003000114002100603c041e0025005030049504100100083c01465030f9440e000e494a960040300c9540c000c050320002544050502030143c40d44001d84d0341815101c4001442207012010040e05100c0e200c00495180030043c400480c3c1082403a0850321030140034500304c444003035144101c03400940d00000205180c03041904490240b0380080340c0107602035500c1101c0c081007002c8003c5400703010b40e07286034000503102840654880c10382400010f86940c50801e0162110b19003081103403142100300010301c0083c1d00f00e2045804a42c0305180001d0030b10914001c540e2510075001c0c90600f02c55410420400c046d4000b105c50f0688200c2d500a21907902e0782c0e1100c000600642021003480314180312851141d0a01c0c0d1419055110002481e85000003403c02081c00c10000780c002402c103940b4154107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 645267634 1250 645266384 645266387
    0x203151b07062d1d0a17040f03211e36050f03010603051b060d0204090b13050112030507080706050702030706061203050306040b0301090209070f033615021603 70
    0x2010081440e07440140e070340d0b2004c4d0701c4540d1140401600103000c0c502c00c1300c8106c41070100c0c0058901a007443d00041419941301d05254540310b1580011049804400d41031103c05441068002114040c11491980e22140b11609950340100c0c0c2c1c0d034403541c42d00d048a4524203481100c101121118200280094403030510b818001303119001c070080d60290381403281c204000ba10018440184400d80c600a408101e41200019584d10642c40400b143d1380c0040f80118000e9442c0e444245605800c44d00e1019149202c02031105486092080c600d40301181c02c0d000f00442d0142004040c82072040010b40d2401c400d9a03107031000c64005507030100040e0300228904040080c2403045101070003000603413030b0b102061a81c000308284002005140207980b40c110200050f102500241c0801c2d6006003001541d02d40b9400040888144ca20320308000b80c20b04d10b0664141c500e5003a44030490001c061a0100c0c000008204900429040340440c0c8960785030100780c550000910103443c00520424403c2052015400c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 645268884 1250 645267634 645267641
    0x606050d09051005130b0907030206041a0412030f17160e1c03020105070801060512010b090d0b010b090f0603010b04050f1810090c051306120e120301030203151b07062d 74
    0x51f415a005000078800760340c842c0191011944100d1202c0e00503911500180c1c0280140e80c81a420100114066030030150421412000640e0742d6940d01c4a581c5d1404400c0c034005d800f50707901040701e454051102e070880c0c400c081c09c1c14090340141c00507d000254154540e40c8054011040d40140d554006000c2d103586c0c41030109006145911b40281004501c081c6110007090620800400c840001824605500c800512a0a4035005aa41a203035a920b20107801540d0015101d5445011404644445840d103403054905030b40381346c0714007420a41080c042c003881484100c52241c2c8501c0a10b25041c003074611682d00c40c840c2403400559102130b071803c01c01d1020b450000000381c050040900c0b4404c0d440d50300b08501412502c082c07402420369001d10002c88024154a10340c00540d01030301c11182d0441d1840302c01581240e00c08d07000c584514078000084003c1e044169808900409032071030071030207403414101800809009410002c0d07082140041740d4a100702191000e04c1154805c0700c02d181a085521 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 645270134 1250 645268884 645268891
    0x90608030a021506130c02100c030c0801030b180604032a0b1f0803160212030a05070f02190e04030e01030c05090d11060c1e010606050d09051005130b 66
    0x10000d50400000c40700107034440c40c1c00585600d0408001c0b000540d1940c0b0312440c0074101c001c00c0e01c10010315070780c180001e444821854001d401141040f903c3c0005034468402c0e0410b400b0340ba03548001c4c590846e520342d0010b0402031700d400c010348410720500301c10030030078803000340031b1403007034403103203142184550340200302199410980a030751040b0041d4000f2607080203850364088080c0706102100500102d848004140e01d8200b58003510000c10b00351101d5001c0800ba1500c9802201d0311680c84403035045a95480c4a40c0082000107441800681c00040c075140f0b0081406100500d0881c507140c44c5070f070a181c0c4003116484548d01d03910764021710091641020b4000c041d11401e10302444102980c2d64050301612910710300501500402c01650f007408843d02c4803180a0400405d4240c1d106600c10030656100100070700d0700401e54001006580302d9105103d010304a0304107072142070824007600e00d80002000d010394213a826000e103650050500c0d59620071030f842141d09144c0f48a48641ca420032914181700107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 645271384 1250 645270134 645270149
    0x20105011a04170109050d0306080f120405060315040906140a0c050a1b0b09030301030b070e091504020d060b0c0d020c033a02010f0b0f010c0210200303010906 70
    0xc1541c0d0646501c04100d0b0192898408404082003295100d00d00620003104d004d0060301803510f901e81c81642c103821202c11200c41104a41e000b03490030100710b849900281204021400c108020401c6041550286501c40b441002c03402d844d20b00c00c4082000d0310304651040f29400d179101003a581c900d80121a480c0c1001c4410f604012271019104054204e00ca04400d0005110181001c1041c40050040502c1281d03030009410340ca0381844104280d990b002800b04881c3e03403010b1000220b000c0c0c80b40c10f13a0305001000a068a8580c1c507907402403241441f12a0000e43c00c02e03001c05c040303403410a4a0295400600000e0425a07803082040c0b0b1a60801410703064040454100d00c0756400070741c0d400591200c15000198000a40c03000c196181180314628514a112800d030507020318212035010751040b1003400c00301c4028000181e4801c100048140c0b012141804074588041520250904e002e44030011605030800d15080d80b410030f211580b800039901200c107103600002c0103110200d440c5c054a00141101d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 645272634 1250 645271384 645271409
    0xc0901150507060e0d0813020a05010813060e1b060c0d200303090714040c091a070f050d0e040c020a060c11160f0902070c0e0415020307080609330324040302010501 72
    0x1035000900c00c075214800c02f03040048480102e0043c12015a00d280d8141c0c2c450001c210100c184414540c0320f5480c10b1103000c100e034003040500700c0c03400e1400407102c601c1d120401800ca000060741054500c819100f95545111035802894162400204011030045000000a045503842c050a081910f19160a0103000d641044070f80c5490ba5007102d6a8000c0d120709003003550b081d01344402440450f006020000d03221a6a41b019101407101c00320707540d8501744581c6d59410003054030708240003c0d01d081d03d43c500c0040e4400c081042c0421400c0d88684a41c0302c41d4500502800c2c0e0500299140c40c12450ce4031002c44031000c01003046031b8118908400402207810709605007940c680b200103c8491603c81c00c481c140a070302c001400c00000c401000030038028280215268113220b078005041d480210781040c01210402e02007041504882ca1414184a015a19180311341314040321b0a080507980904a400d48600c429249505004403409102e030f40051950018915290034001d007501c6041e402a07002540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 645273884 1250 645272634 645272671
    0xe060c041409060d12170a0912050a0c061a010305160c0807080c0111030114040504080a05071415090706031109011428110c0901150507060e0d08 64
    0x1c0e5414840340400045941d01040d5454001068002641500090081300341c4210104007681140c4411a00c01540c001440c241d95180d2086088880b06100582207201290b415400103204038010314400c2d00c54038180001e21075540c3c0d40c50651300c4c0610907207420f00c242d07011311203256494072440c0d45c007d40e4142e85070300d40000030350007410300318036180094040080042c03030406000500c000c903110140008003c011041100300206841c1d0400e0003154614414038403081c80d42e00d01800344a0041d504080241d10380071904e001507806600103502254114002c00305030a8002003405020620700f4a246c200c0554540a80003d080205e0303074000e001030500d0111140032580d406015101440002c1c28100009102450720400c42d0040c1d1503580107a1740704000c002401c003040c50203101014600d443d10041000011401074a40040880803030f04041103400400200500da45521010021401d20920b401076a840f500c1c240c40c400c40c00002958000000030780f43c9a8003541c12a131000691414540c0083d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 645275134 1250 645273884 645273899
    0x2090a0608060315063609010b01030e03090901061101060b0d0f0c0804080313080c0a061d03090904020603130b0a0501050a0609050d060506270103020f0a0b07120203070804090e060c04 81
    0x70f10100806c1d04070302c055081d0341504102d082d94904e200d110010000a860800040303406400c0010705540041e040c0f000c460a900c0303001054440b8140001c203d44110382c240707407045030314000c44c800b000c1a564852100080c240c400f0401007034a502185008035858072020013103003d072081c003403145c020011060100004100c1000c103681e001041c8421490180e041800c00c0c1001d409030030400c14450003540380c402e0070890f44c3d40c061460505140c3c8003486607000c1e90200ca072a40183c14500c1d800501c0b000c0050018544070340110380c0883c0d040c0024030801c04949603944020000c903031070b02d41305948400520062800014440c000e100300e107412150a800d0202048000441c207000034079807511000441c84c95900c0016004070030507002200c000841c0f50006403000144288000d9014450759008031446091603c3e140094030814031700649001110b0f51010b141d00c564940402c11030006000180000310000020402480012000b15000d400240100e0078020041c0a619a01108110070407521 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 645276384 1250 645275134 645275149
    0x204140a0b0a14070510060815070f0e040b03010f180b0a0b061603140a020a030809010506030d0807050f0d064e08030c04060206010603060f030b04020402090a060806031506 76
    0x10003600d007016114030407071901d103107080e001b520500005070614001280500c000104580c00c0c0816010f25950f40d01c8141054071980c420f00c02403c00152074600c045d0035400c050b000711040e542c6c05000018110403034020502111203070381c0c102c0442601c1c904001c0c28040d071a158290440300140081100c040c04100080091083c1c00019044d100031500c000c06050203401c0c182c1d02c680d4080790300340e0785014072003009441d0900420210046800c0030f01191140e01d0520a40c1e04c01c05000c0d0040c1100c0560030405d403880d0380001c0ca08002c118003080000100c14842c009056800940710740030400b1400c00e4031080009420100c040005400c040801100d103030450150b031214204464002403802c8050811101c00400a0000d8804a0000305111110007524020002c4480321340c01e40d100b50341c03034071000c60a070b4013a4807407481d90088854080c0301040101101542080c40108014509a0308801240714a50140d00000104590388200546801e043c400c030103070a45610302403034482c940100004c005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 645277634 1250 645276384 645276407
    0x50109020c0d1412041e080310090e0712230106050405090c010e0f011b08070201030e0f030322021306051302090321070b010806090d0504060e090c0d0204140a0b0a 72
    0x902c01302101040502c071401002e071030030b0b071440c100268040b6000c0c1419080d0740e1054031541207044405e0340014220701c05200302d01202c105000600101e40c600041280c00206000c419240720003003c0d8580241080c00d0b00801f1042c0c1203200210303482e40740c0030400007103580007000381c07210b60448424625280e070f00c10b0085010303641c110b66500c0815a01c500485000d0340302039000d207458540c0300c600c405000080340600041807013607800384041040b2404058075130b1030a0302542082d07032080c4046003045a11840280000408101410b10020365800145200d61000c03044400160746410900007400e0a03505510306810101066140030000400300703980b6080c00302d0b8403419550b56480104d14180c038604948803290018201451961140a0319460340f40980f01c0b02802c0c0310300b100003030615000c3c10a4400f181d80544070313a4007d000400c280543da02c4000d04288503000204807400e003096107407018202420325844d080c2d0b04050403c080c00001310540c2c00090b0300c65410302401404c244d020010000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 645278884 1250 645277634 645277657
    0x12040b070311010608030703080f1608070c02150d09030e0306010b0904050405010612051005070c0b060d0c08010c021f060302091f0b0f0309010507030c090b0f0d050109020c0d14 78
    0x11644032a144a0f0b00402aa400070070b080c1c00000b8041c030506030700500203401013945104260003034484003181054108100c8101d0302240b030210004400382d01900b0384030000c500240442c2410000e480c5000c078107a00c5080803034602c0396170b80320310000c7c903901860700100c40500340d000703111039410624101c0c450300489108504c5642c41c0e500040411100303400000040c2200c2e2165840c50440b40303003030341d2180041000403000d00d29100005403200e202c0e4980011640d040001c030305e4a600c0c3d030020300000d0b00000105969403246a1400603240320b0034861016000308030b41c040d246103101c2c2c5c0000c61a00410303103d42e8060506201c0d090000d40d90304a0b006411071000c1d00d00100f09200340f80024804a02d99002064007034011511050088503031004521820140c002008a40d551000940854040704441d90000c0c181181c1031108416410040c1031000344540920b09003004040c8130405d85001343c100d41d035404e4012400307501e00ca40070011130000d0303561800c0000c410206950020141d02900a04c01c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 645280134 1250 645278884 645278897
    0x110d08070815060f0d0c08270114010f05101b0210050712031a01080903040e09100e010c1b05060c03060f04050a0605090105122505190e13020102070e090304050d120212040b0703 78
    0x48a00401d600031191003000112b012560361b520b12221080312400e10642d030064250109402c1014442c0074559690f02048c8000c8020402030303028840e06007a559000c50921200308150390100751640148400850180e6021130b04041006040b441c0451209406040c01000c800380302080202005036800d5a0f1485a906100d42d10400c1c5545803005000001c0d18442c43c1c818165404081034202e8240c2c0d00c40758803030301c4415408050b80c2640b1082c400000d08243c0010300072400d0804401d00842d0400801020040e00110180024040715000c2c1c0740c4080035540d8540800040c10521030750340c01007134201d401211030165202c4075a100c00342010244031071000c00b07864180c014182100d40c0c002d0b04028150a404d03900c82c01440c40c0c003082c14014003c406c91881d00051030348961030f800101c1189d041e4003400c045468500040d036650000307407440800340000d1002240b181c450010704001c550245140740c03408800741c1006030074100e803645411030201c0104405d002459003030080f181013580c58600384c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 645281384 1250 645280134 645280201
    0x212070e1617010e0106020d081509100f09060f0b03090a060c09090906020306091b0a080a09170a140405010e06030a1515110d08070815060f0d0c08 65
    0x31580c0b04150440801c22089210001c40c100b4189615a410303902582c08803909450070790300c2600e03010380849204003000100881d00742d0505001d80703155004003082d0043c081c5203407506500c0b41e440c06141c00214409036252410012400182071040c005c0100d44c0a461a60a201c069541c80d012280d2001d0022034840d20710004103440b84000b0b1008100440e000c022440e00c42c0b030400080d6009030340040c82041e6440200d0303460104980c480c1c03018901521a43e15120003442c0980e02c10350300400901095a8030201280402c0c500d1907082c004101542010f6030f1102c1c0d558002d0010715443d0f200e0852454148401c0c403c998006805c40101c1004641040d12030703030380c03404080241011440c0e4152000d2000800110b4038210f1081c501d600c0c686442d80031002000490310ba644a2080c08440e00050301c1300003040040b8064084590091900c41a42200d0070318040441c445c1d6218503040e0000610003e005101c0340100d21601340c0071303061031800d40464109004466a10881d00a0304501c0c1804007001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 645282634 1250 645281384 645281387
    0xa0506031e24010f02031c0f0c08041b0e010902091903110a0b250c0305070b040905090f0a080a0c0c0b0702090906090a0611070206030406090212070e16 67
    0xc9070340000a0201c2014286007516400101e9420480c20100203000608001955802070500b07054500c0b1940c01141008104590f004000c030400702c003021030a680b00310b0700811004a0049045025468423001e225007042c1c80d00500340a0600d00c008500c00d01a03100380010050301c0d071003a0441d91881e03c0907031240081d6002400c0711348101d032450388515a050b0000700b0412004421912950f048455600345541d40200301400d10540a100030f075010000549212240e0b03007044454118003403e150403c00e91290f6070b4510340312031070b040750f02003080100c2c003009000707090b00995070b00c01c0c885c1000d00075004205030311a44ea03801d0214001c100b40004180140c4841c801c215410100d500068880d00140d603421165a55610a0303100760b004030352000c00070b2925400000ea050203074002d000108100790305030f20340500809048035808490b8100b00500c1d405652144083c43c0550b003ea00c00244210305071040280a4a160481040700e0f004084200240c114441074294000d401415091550182040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 645283884 1250 645282634 645282661
    0x9070b0307091d04051009050604020405072303010509061c0201030b0105090406091a030304030f03080403050f0a02030c07090b03031e04081c170f010b073305060603060a050603 78
    0x4000802845411443d041100e4400e80e50b00990094068900d074800c0341c01038005032560003002a000d03134002d401040050600754416640070308a0302e080c0705500c0c0c0c102d805004104803181c203002d042c10044014407183c940041c0c1c4c60f8000204507001c0080701001c40010302d160340f5034000a414560781e150401350a03400346c0200c40702d882e0010006c0124549850300480288024a451200030b5000c0c0d4440190382000011202920341294251207902584d5404840c0340000500440c108030080c8032089122aa007409000e01c02c109802840e107620303107119082d140c01d41c10381c0400212400c10495108a450210849119134a21403070015413260f01581b5041e648a140d2280e03040e4460180c030f0740b29034001000040d03144285d9944030f0409c108412516000030300155a04075800002e0001000281c01e0300c030051500510034402180854074060045c0c0c2803240c100c003000c0e0b00940c40b503180c1c49040d4480c415203905c2601203803e14110300702440404c0030352984d405003500404000011072100e90b405074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 645285134 1250 645283884 645283889
    0xf0307120315051903170c070312020f0a06090b0907030b070e031f0203040b010e15120a0209040b0106090603020309030f1308070603020d0c020a02012a0804080615030609070b030709 80
    0xd02000e13000d148202041d4200b100341c4001d944514884449260414122003202c0741072441da00200034407415603c900201c035002515503c203501c10865441d01e4020203005d40c0300309501500c00001c0750f0a17541040282028010200c0031903422130071050000841090005800c114140f03048138100c06920003103443c00030451051080410a0b1610300000b8020307070025403142e0310460b201784880c0d03a41c0144030840401650300d032400d0325405201440307a08010250000c01480d03001220340c00400d90700400d40c0c0784010748041c0c0b4109407001c0140047e0b600046500000c04061500f14610300d04490016260b0207256800740d81c46500145c14209040c46902c2c84000e00031380c0065400d86540ca4001900a5001c903040052407818868003014aa00101d420700e425038042e15a5941c48bc4090b405a4800a040000d80860f0641c02c2846011a00120140c40903016140c0141640e003041e10000031324900b00700340301c1d00c642d0241c001c11605c0400800c0800440b0083c014080d01e98403107040c0ae403090f60158 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 645286384 1250 645285134 645285139
    0x907230a1e0e04060506030d0c080316030204350309150703050c0f0129100c020303130306050f1f0e0c1902010b0109050301050714070c0e0403020304080f030712031505 74
    0x8003480706101c840c0d804540a211b045044078000500da11094440b80c021031400350220105000117185c521020080c0305d4000c0303292500510745a106d403c0510110340145944c041000c565001c100c2040c0182801c0c003104004500440c2400c00d000b000403078500b001200300102c280d001c0303482420140140d090b980a81c0c03100040e1200d180070040410300074400d00c3e02d0010f0400180c0030ba60040e200d00011030550358805404a00d10100080c03081d56a05100602240c05100400c03503103559118220700711020710311803503002c0384034200204040480c0e14080c00f001c47c80c481c080299810104400441000c48400d9100c04020795208002c500490042c00e2100025070786204510180d19419132100c22028000d8032408640f0362500149800c83d8011503d107001700d005181250b0303615280328054414076206010200300140c40c0c00c0140c4040c03006440031005a84040340510815205109180c15825000011414581035444010b4682201000c040c107040d511000381c100c800004e2800001751a02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 645287634 1250 645286384 645286409
    0x90b160609060501380901030905070e160809030f0a0819140609090727020903071d070806090403030f330501020f100c02150907230a1e 60
    0x507410540c1e5107403d00350042842c62074120311240801245020f104070041205c4e50315092140000040d001070400c0380d0203071003500c2040c4000800b6900703070140c24420403034180020700c007510001c000f402e841d002908030740454100b4003145058801400aa5140d00c0319458901c182d51101460210b00c074000551084905040a1821501c00040380701d42c1d01407001581c002440d0791300c8414064681e0b00901403440d0f41c886484038006090344a14501044110501d0018601003001000918012a56004c5c00e86956400c0c2464000c0801000c41c0d50301c5112400e000200c1e14100f80040c0040d0300040000f02410750b1800d10703828000c0c96901050803080c068900543c04440102e24005007802400c03440004000000040741f20f51010485420300800d540050070390050064514000d009070a507a1070840c854a164046402503100209018000300e201400402c1d04000c0040a00c032090825031951015401007104c0e0f03601e80d15041e40843d003002125444008500000c510511400d90001103038000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 645288884 1250 645287634 645287639
    0x6040812030106110102120c090a090e0105061c0b01050114040305060a05090d0908060a0518070b0c060a1415010e040c0201050a0513020a030803130206041202040c090b160609060501 80
    0x200c0001d50503940300c0d440741d1a1540042450034240d20a4003130041c2050600c0000c19aa42106409014902c0c0d000340741242c12a203842c004030440d07020038102c10781d42e0b45807024800c080c01c2c462107903944499404a45401c040d0281c85100c200300040c4242d81c100100c00510078500d58030102610041d5070b0009c2916000d06080b444c1001400c802d071201481409074813107000c3e405004540300d604850340c01d800b0704103d42d40c4140c484002c24008154130075451a04848034030070f0100b0711010000c1d11124204070f0301c5641c5114901c0c540074004040c0c0c0d10813864800e1501c1d11203100d28005500242c00224031051000c0100101c0750341003403c030560340103814076a0b080d01c1c0d1760701034104030300c11a006e82c820040c980d0760a22140c5111a1240040c3d00203a984000748045110180103552003007140812042401d0146d01291041d845588565003084060071198114030f0140651001c100c6070b4035220b50100e0078a40d10030314a2050460b11048000e03212000b0b002c110b00c503041800490f4000b04100095a03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 645290134 1250 645288884 645288913
    0x3060604121b0f080721051c090803090a030602071506090207150b010c030f020f060412080f010f050409171801090915060f1b03031e180201030b060408 67
    0x5603030344101c0300602d002400820079100c42d180981c01c48240c00d0083c03c203549046201200c03014903040f01c0b00c102e45c400d401000800c108110400004222040810f2403c0c10f00c1801010300020360421101500108103010540d52065039801c01c1e01d40015005070313a28094a4404114801e8101c02c040c1141404000282500d569016002d0f5a0241001d059a07008801215040340c2032895101d0100e41544008400302c1e100c1e0171151086000d9004403900c2103401c45d40e4a00d04602240c0848480204013078521031940c2c40b40400d80c2114007401c240840f0350401082004c0884240105801265604450b4041c45a500d01130b4108440015200790f94410a190004500c01d03d420a80e0200d250400001110040ca03c00c940024800004da03840082c1004011a00311050348030040030420301844011500006482d0480c00c07520a4034002003504000b60100c41142c00b0020055200b4a00405150210940010420040d50910780090358102c0c0200081c0c3c0c0740200c0d0409400d0348140c4200040c0c0e031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 645291384 1250 645290134 645290153
    0x7021507030e0d2c0d1a10050f031e25030b07052506060b0c01090308090c2202040305070801020703020c09130201031d0f16060302040e07050306060412 67
    0x154402c2c240c40d800c545a038010398030354411030b903548064200860132000111015500202449004209050044098130b0b40300e40048180c9064240c14020424405683c21800c80d40d070040078269015880034960000107038640300c074001c003104001182807120040364014090b540c0018042d00c0d0a00b9880c11420300800307807a0f198002250030810440c00302e40300b40d02403c00e441c03602c0c401c81200f56032000c1c0f1400d29000c0d11101c6004a801c40c0d101c0a0120b80c002905018100744914900006100c40e0345042c0100b6924010b054052641c10070200c0100c1600e030051400c1c041c0c000d00b9640401d1700d4450208030700074450b80d403000e0300710b0160003404201c07550190004c203c070a000f5821201c070200340340b00b007003081002515481a00c03c08a4040b500650080d00040d1070a2090344540d240c0c04148040305080800c582d0f071100c119040103941d60301d004c13040d20411002d88468602142030030708110303910024030340c003905600903c08040001021790f90340130110307405401c042550140c2c128092910741c1e0700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 645292634 1250 645291384 645291401
    0x806210f240406090f1703041506060e010507111f030f02040b0403020103051314070e09010c05070b130c060905101d01050703050405030616110607080408030702150703 74
    0x8074058049008440640e00c1501c2000c800071880c1944281c45a554200060080d00c0c42100d0b01048074401c500412560319600b981d82e406415100d80d81d25182c5460320300c1016203040399800620b0034001b4001950310103900c0c0f502d68070a081603a5251451b05202c004101d040911580c401c6100c581c000590b10038400700c03480030481d07480c1801300b00190480d24082e406140544800b40350305120402c05503129801c02a04881840c0c0c14003114a16074648144810901c00240380c107601c684010802900f03554040b82e407103507014008010030344080b0801403640c41540f0010f4284200100441c9942800c179031454200383c1e00c04c2e0062000e03582c4290240c1000c0306482034910400040e41d4401c6214040c14003079106190300b080e020321050309100151a1070f0070489040e000c00801b8003003c941c1c1d890800116000e100300030044075914042e039000400e13600183c4188806c6421140c180030082d904a0070a607005644102d0280e00c1e541c420f1403c03407401c0c0e40304800348110001c4d0403d00408941607440806c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 645293884 1250 645292634 645292663
    0x10b0d1211061312030e0a110109050103060b1e0c15060f0f22060801020d06150c15050612010219020607050a090b03070e0310020a0315030210080621 66
    0x149840d02224254031510201c0d00190441560a01a00090800040c0118a84d080e0400003001001030000c00c0c0340c250602c40489502c5050885000340d9030b0040748002c000c0400f441c003400000d0400c0c00179072040c000d1032070b0040c6158205030580c0d0700c0105802a5051645050300b1516000c5c44801031152003030302078903454001c0c20200c604502506004020424003100503001a0100592211030750101e0010140340003880d5955201080381902800280610042d11b107021a0344c0d0300700540c980403034920440040034003090141c80700000300d58501e1210501c19030700c8002002e41c2e8a00204040c0480034405070a02e52002502c0b0701c4500780c80700b00301d803d40c461358200d908668424009072558400c4a0301040032031560b01d01085400d84541c0196400700883c40c1c00c08404000d03c010900ccc010b40842c01c50150b68000c502c4038001030345482220010208039100d4810f04d0b1541d0041100b42405c50400c1d0100032980c4d0004a942e241c08008074100e5001c51410f0001440900300c2c5511a8440da0242c030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 645295134 1250 645293884 645293897
    0x220f09020901170907050d061a0a081c0e06030f100501051c1104080102030405030a0e0f0f011206051906030f09050c01050c01110a050a2304090e010b0d12 68
    0x128158148241c03001e040e41a111003000c098039500700715602e50020b211280c18407a01001013455203814650307640192180d40c01164082e0390120f60307400015448805405200c80310020418400700040042d1251124410809080d03400d080840e604629124240c2d000f15002080c04a501a154841c0c0c0c03081d858400e40710b03034032a210001140c882c0301c1c41013000724001c580500380000928682c450050340fa65400d034186402d07078600d211800d9070400c41d001d840c141c0004c69040c0c203041d0080169a4611012184031203240744880000b0120b15803100ca070740c1004198020301e8501e0020340c3c480c030064140106100034103200368448150b01c1c1814060322002906002c1401d4031030019000781141070b61305c60080c0c10f03100c0b014801104c086d044420a0411992524401c0034421600c00c02480c1e00006941e5083d13880443c0300005d0020103546034009a100030000c4c41da1030240000f000d590981340f0402021848012942069024103005040f20760702201d418144e000300481400003809414a070388900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 645296384 1250 645295134 645295139
    0xc03011a0f030d0e1201020705010e010c0f08010806180f1c030c0504050a050402031e1515190534020906030604050d030c050d140a1d0318010203220f 66
    0x1540b0f910034140c0e01e0b8089586405403443c1031034559000c12506510704001820070055485590a5606080044e09a079660307003541001030354025081c500d201142c3c00c00716041d5140800301681c42c44021310260f4500251180b603000c2c880c0605c402d800d00c12419080300c44180d60030441c50140d01c65031600002192401603c00041802001690111a8000d0104501c2ca1030030301408065800100b512000ba40c20304a80a102c80d492501707180125070050300e0891035913259007408078000759044080c0d003c00e000d00c44107224030b24024021941090f20f151043c1c94500f9440042c0040062031800040d2002c10200910207002849000c404c8a00071500212551111010f042d110141980d01810030b40104640e0280740d806900260000b20312450003c0ca0701c8001c64840c8226160740f283c0680c224124014021120580e0060401e01d410f03001e0704401012040401075900c0c8601d40304011031004e2847c1b01c1100343c1c000e100b602c404002c1031048100d040c00c4c642860420803040e01400612078101c2001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 645297634 1250 645296384 645296389
    0x90c0d020a180c030501170304030b070507021201050105210309010f02070b0d0f0b010302132c04030c060e0102180d15060f080f0106140409060e120706061d180c03011a0f 75
    0x950401f105400554903190541d01c0300f5604502c020420814044204020300040e1940501072800303110590000486504000400c44903101c000d007400c07680320364045600b0f00708001008550039403070309080c64600b071000307031300c2c1a420005942d00c8000110382c0402c40c2101c5506503002101e994007505410808154000010f400f07c1c064041e03d503070213030b101500500c600340d01e00c0c1002c1246002403011940003001c040d061403070381208860480010310601244810040c080c090359008000c643c0080d400d1400c4c10701002400a09c1150341407062180d8164003003800302120028450429400041c07060f0364a4004440c021720340c5108000070b45c464041d0303040500d8410f1040800786c0300d45451803100082c51504110240018490030340741c05546c0c00c017280041400b0020010724506801c1d10a4562206081110880d80035510404042030842090303080803000301d04c0c141e0b0040340c50300b40002d0014041034503490885003c0d902901986411a94185405551031780d00c0c2e0300c00c00300c0b4030186051401c0b05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 645298884 1250 645297634 645297659
    0x103030509061b102c030f130503070306020a080f011a0702011803032006010b040e07110d120b0a0503060a1e0c05090406060e090406020f161b0608090c0d020a180c030501 75
    0x40320181c0d0824460b114145103203400030007440201090101208d034485000908050865208603403032940080c0d01c0484d560489803180d40034a04000940c4598542600c454a000301c02c903d80c000281c00158040c216030017218848894294112141032060322450098100581a5030268441c101001c1c801c08060000a681d13040c0e8281c00c40c4a41400d280100c04603500001401160034004101802c040a510805c910380780c50611f0354440d482c1c41c09200001e42100d911811a40c000c1c00424800c4c03007240c07400100690009581200015204601c440c001045103032040f00301d01c0c4138186040205000d500002800c0c0d54a4200d904010701d555801007680c03454070040c2c0c0c09820007411000a07020074030aa01a22214482c1c0c2200d529010408410030000b01d450b020446540c11405103090704183c9240561024000c1e900301040309090200c0a02e5450300781d440003e20071600b0004400440d207074608050020401d641e1b107030604030690032880d0051714030100074000007440e0000006106c03a1252 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 645300134 1250 645298884 645298961
    0xc10050a0c0207120c1436161b0c240e04021908090f010e0f0d080408031513060902070312060f0b030c220315050103030509061b10 58
    0x8151700c901ca80350450080c01402421541a030115501a10303200d26140c06441c50f11220360040c0c9003c0d020302c084810180c1c9030f00542100b10390300340d890b0101540c41e0000d2048000002d0780311900f52014051402d0b600252180e0800c0c0c0c04190042040c0c0724840e40200c515800c80080d4540e10a0007580205100480c0205170043c99120310340358075074601d640544072482c1c10142d094142c0b22011400500e8078251003990035040a0f0380e110b5468204002014001504018114545a00f00d410551135407040c900000d000983ea031001c181c00e0a0403652180c08444200d5011582805240e503550402002500040d005802060030305807410507034181da1103050151029000000f08aa0410212100c0c2d900f00522804020008000003180350b01001c21a1415500031041880b1686c250f24080c0864154411262050340c101340061002076082030a40d00900010303981992282c01d404824030107102402110405809522400e80c20198580c114491101c1c5440d5070442c8040d18548070708480c0ea045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 645301384 1250 645300134 645300143
    0x80109090c09091a090a1731121505090f060109020c01090204060807031202030a080109020f130e18030306130504020a0e07050a1e090303050c10050a0c020712 70
    0x51006002c909a507601844446018040d80031140340794040e851a503c405940d4031032503500009015080001e0041000311000d0040d00407818080079401050141242c100c4001588040100b8850040e00000c00100100311540d00502540c1490a00e00c2541c11480d03d11001c0314107143c000351080e5000120812601400300003001103030700e170011070750094210f00c5c20a03038995254245500580d90f940200c60207070a49001a0030f8203840c52401401d051266620101950002d02c0340c41883d98018415504551040d0000340e03070b54101e4000307901e07035106000b054107030300d105808007290610b602607903d0f20860949102c01082800325600319a40c0c00101d0b0dc103a800280e100c2010a01d004d141c0001e0b401600c0501081039040c0c80c0d9030744400e14841228541c001590100c0c090381199840042c065500311800304a056260809000a200001c94000a014441c00090580d00440c04001140b00250940e03010001030900301110406041c10b0345030040144900707513020819510000c100e880040c1d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 645302634 1250 645301384 645301403
    0x20712080601020f120a170a0e1c1e0306150e0a06090b0708090d0b0103030c030e0a030503032a0a050c0c0603061f0e06031501020d020303091509030906040b0a08010909 74
    0x118042c0846590051b80b02404114015003891050480c885c5664007031511002c010880074261141c1c0c81c0340c00c4960440221021004148405458101c0d5a5800311094004184503480c1e21500940191100303231b11160064000d4079100c5040d643c491805813507410112807100c0b58654400086500003400e010b001c150050801664000800080082148010241c25684003c034651145103c5040036441500401d10394072440080590040701c000001c9d00842e080c17142c0e1381c20345c0c881680e030740002440400704070400c0380b84c180d14034548004d45082c50307800c411455845452400003466900650340c086040d21954402d001c5510706078098902c00c0c44041d00300d03c02e00c0360084c090007120030300c0c0c1070090030711401c2444d00c0010b88544009521a005c100e100403190302c1440e000a241491044503501190418400c0c0520b0880202d00044035850810b4038a8113a03d480c0403060139489045410341d800240000c000032071a010707101404503040f9903190401d00381c0ea00c240c0e14054070303144503004000020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 645303884 1250 645302634 645302653
    0xa08030406270b0a14190305071e0f110c062b020a0305010302100206150f21061803070305121e0405060a0b01020a020d06050702030c01020712080601020f 68
    0x314448103281d10a448040034400c80d450310290300e40b14020341050302040c80000700c01c0c60007a080303070311510b100c1580324503e4600f00743d00440340d00400c0d0300c024032010580c840000c225107030305c070b40703080841f41d60700c0c00d00d0f140e070301c501d91401030035071124154480081030400500791892103001c00c8014460b20080c01551070001d00000712045030007001c01c02c42d03803003110114080da1071846101034042048141c90016495046004102c015007100e40b000301150f200170100410b400d0304000b84810311205440140f52a059440040d03481454414070b041c1a2070203100d110403000000030300600840c1040060510510548071150b12803144881c00b9000c160704211541c5140042c0d2841540040d42842b500c00c80902c054800b5081c070030030344d0292065070000062055084132481072003c1410700f40000e015500c1603501064991030054000352000c0d03510400905000d00900450394502c2401000310f54908262400c035801c4481c0f2107080d0300040b000400100d03503500000c0d4154a0010640003840e0181 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 645305134 1250 645303884 645303887
    0x904060609080118050c0108070c06020f03010f120210110a02121b0d080a141209010b091f03061a060c0f060c03010b120916030303091203140103170909070c0309050a08030406 77
    0xc401501d03d00c00c10030ac6c035170b18a011a245101030024120440341d0f985c1d607540341170305400001c8a1a005101c048035043c40306001a503400303005400204035420401c0f00306c035544a01904060340500080e40000d503202071040800d002144059580144c0010707508940342c41821300081d030b100c0c1e1600800182c400c2080c0008180601c11554001c82202041d6190215040c010049800255a0707100642e456044181c1c0703901d0003c8a071640207800e88030012034200c86032000d5030104002d10016240b00c1d0740300446c00c1c50487d14044856401030113040c1c07076034038600f100b80c4650304c3c500c8800c542072900404000c41e0050700c11408a82c104d5201d00c541500b0700462800d4030000890290526229110b9440c2d482c81500b00322609000442c02900c0000700003100e03042c440100c8801c400c6013401c01d480c0c203201150801148010320306407030300841c0c0ca00a0010018910381240f10b030144c4182e100502c0c0c000c11040550201c03030505410300c40e82d24103d11980d12010300140000e140245046c54109000c10f01c0650f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 645306384 1250 645305134 645305147
    0xa0b1c0216060e2a100e03030f040b03090106060c031409190b040e0f16320c0d0c1e020f0405181605010e0409080904060609080118050c01 61
    0x5910350a072034032031603032a0b6568200300c6074210030459950300b204c0c3c028440d804035a403119400c4080c440c01c1070748000d42c44c4001101140010510b9040c8170b8040c5450049407410019200b00c4010b08501c0d99543e51180c5006c030494004030b8004d1540d40c20300070040b03074081c81040004906a4142c6580895014844680825070031a55040307800000300c56078100a5442c00035100002c01c0c81d9040345030740300e0501c403001006c6503006001030345d8485c202d001c5c040511040280b00808113050318106441031554190810720040007200c649044044404403120440301c1c030001d21000c2568401c4442c603401c01c45d010f803581c11509034042d000e4202504121204510075440d1940c8038801043c08990702003e2000900315441998100c40f01032141c0002ca4a03002e040000d0b01702c05200c140e61240903483d02000800050f11254524011625110402308011590f8240d03050304400070030500080340c850302e0040c45604c26100e00d403480c0d030074410706c07503040c1111030032076172441d030300324000c0c3c01c10342500401582c88 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 645307634 1250 645306384 645306397
    0x180309100309111e01030605031b0d1a01180b09040c0b0309030903030c0708070506033304020d1a0d0807020d020f10080f1e0f040503090a030803060a0b1c02 69
    0x810080750302c280310f50707490250041001d4040d50250f84c102ca0444001030031558103401a0380a80d00c0f1080c14044460900d21401420400310340585400701c1070700e81000c80c11010007440f1120b80d400c1c0300200300c00c1d110342200c070414082144200400c040080400121160554001e0040c08030200240328041e1890003e5502c00c80c20403ca038504030920000c40e2856002150055194016000500070100103214640c028002198190b05500b0114100c030000300c6c5190301059050038525000c440e2107208032980402483c014011034403120021721007405004080c1e83c144000714550141403041c54040f000c400074039046168142003480ca41d0038810729105001f016a44410081083c07073b842c0d41c035054101c110300c02640d15071140d4104840119091302004e0076021504a480c00c0d180340c6190300030b4203d6484245003e0100701a151420194198403d50540341e80221104001005200d842001103000703c406550b01802a6912a460142401001e40c00100308020800c800c5d81455244c014081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 645308884 1250 645307634 645307643
    0x60f1e010305330a0f0e1203010e0702070602030d0e07050d12030507030c0e04110409020c0304080606060a0c0b04020a03051006060905040608070312030e1903031406030d050c070e0906180309100309 87
    0x11090a1506e80354a0000460488801e012000005002280c16412100e82000190000b061010704241001c0d4980c05005180c907011695a84112800e08040020b00020240035000004070034160a209100115a0190b00086800c000c04160058403034840d0b105200420b0b5601c0d01072014000404c005807544c12481110300704180030116400d0345070310041032582104401540e95510b090b80755410010000d2459100b90018001025910307040849070440302e41c05001a20150b9403840001c1da01d00035070300003801c03074810b2074100d45020f040c1d0b911030410b0b1160707030300e07000600340da03420400040c0c80c641d000da4505500056001c0000868918600303a0918042c280801c00324140100b540c40d1812080b041e240502211f45a841403681500c0761208a062010500c8800d03d00000429503413404021114100f080010340240c01c1502403041c40d019280040313503001142000307954950307503440994880380704c2d11550218035040d0100004079000b000e8050004920316440c45010340080c508100e0989 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 645310134 1250 645308884 645308891
    0x306070e010f0302070503190f18030c0b030a02070f050106140a030c030308070c05030a090911030f1614030f0702071212050d14090a110d020102060f1e010305330a0f 73
    0xd50035104594480003419903451070b404200b027500600e04222005001e501d1712070164280b010420402060064500545000350782e9110620190000d12031b407000500440408a651000c0020642009040301d40c0e14624030034a041c4c1e50100070010595200040c0048041d182c02c01c0004d000740031a0340d0050301424280030103c41a2551410b590091064800181e00c2e05824890200b284c81545185101100100d0071840c0c52440510520741c040c0060703048150400606900500c1420103003081498400455101e0406003943c11400c8015285d040242c040c50038007081d60030aa007828500302d600704c17401075409100b402043c1c0303065011104a00103583c582003500d03000b405e2019442c0c0210073b62401407860541a090203620744102d0046140718903583c100660241c0e90010f042900002c5103003440b8829190729041e45802c5d944122160401c00100380004103100c004030b00c001d03080c02400c5041103c8040030040e2406441a01480c90f81120100c0104079904131950007592410800c08001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 645311384 1250 645310134 645310147
    0x10051002070509161e0f17040f11030102042c01150203041e0b03010e061216030b13050d05120c0a08010b031008010204140301060b03070f1119060b0306070e010f0302070503 76
    0x11043d50025013822170214401c038050410140e0302a1030344680d03031704641d505401410155107103034404100640141884c9810205c0344503a0342d0030360481d401030145072001840c02e0181b00306d41c0c460440e02c6003103080342c8407100b00000e179010140003a0000c0040a81c080c2d45080e0425050b20208184166911410320700d0302804920145900011030290960f00231000592910750104285100380071880062500410781c03982c1e054500058007030036642d001d00b076000c2070b56580e41000d80d030101000300030b80540b107892450040c4603000801891590f0a4011928080e52464040017240c401c02140c140041d84540c010008451241e020396000303602550304080c034554a41c082030998000e074120740c0c80a50a44034480711450300340304d10001411104003c1303046182c198000361031380380c0004581c010b101c0400c081000c09042403102d807200c002d20241958004400d400e080004010388402d86019104030000304442500441140c050041c0c16555400a0704145070202c000c0c0d041950708590071722091024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 645312634 1250 645311384 645311417
    0x30e060406090b130e330a27141006090b0703050c01021611010905030601080d141b011a040e0a03031817030402180f04030e06121005100207050916 65
    0x101070042c003407104a8040900400d140081c6c1805000304020141d2800d9286032051301c80d6001c000c2203070740c449032035804000340c0c0b0708011000601c0400c11030407600d07081040c1801b945a00700710f4040c5e410662540304403912414140d42c6000765000d01c82c8900030034040000080d1049005017550310009001605110300c402000c01c0384594174400312020742041c0400c91107075034840c503040000c5c40c085005003584c1d40340c1100c0740e0320340030081c0c407040c10440c04c0403230f4a040803012350490b440c14414190b03a40416000484690082804200c401003800d00743c01201900e2425001c1c01d88005044000fa20800722255016401401d2209000161005040c10305000c1500640300000116242503803035071b245420310400241c02000f441d45070703020394860f0511004160015102d0742c020381c5030030005018582d84001a8032030090130b17000c20156807480e00304401030b5040105001224015255400442d000985c10b0380c60705420b0103500e40080448001801c0c0d00e034808005007080b52076040048070080710740803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 645313884 1250 645312634 645312659
    0x1406090604051201060608061e091005060a0503160c050d0e0121050103110d050618011e020712030c0e130207060219020601090c08161101050a09030e060406090b13 72
    0x2070000304d075500c0004100315504401e0b1940d01440803a66000d4000101499401c003c0b00c40380d402d8094403000b00010b060388801c6074281c0182000078000c80d12214258001400740d40103c030380111030340c0402c800281031801609e01c80c41c4a50310001400b000108100100c510070000002e1904014032003641282c100444819914120009540805d00d5810f504001d0320003100b0301ca500c1d029400640030640442c1c40860b069800c502103040d1850700e13405ca540445d0240c10304a0203d5903007070300890940c1424a15500500c89284200e0b85040203680707030801501111941040d500100d044040d0720303403c03403404a080f0020b039520080014185807140d01c80808076000310041d800c010386150200340d0780903010800f09004066100c414000c5000204004010a9020b07114010642c0e02d540d0313000449000d18040940b143e00071000f04400d103054035085010f00700558081d000310303030405000c5003103041c80011202035071000d803070342c2035200c1c43d1103440303141588500d02c0c400000c40000b1003c11070034066503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 645315134 1250 645313884 645313909
    0x6010201060f171e0a120216060c150c0503010b0708040905010b0a18030804060c0302030d0e2a0a060507141515040207020906090703090c120c0609140609060405 71
    0x481944800a010840b0313403400914800c2d41420001e0b0030900c00c511100081c0000b100b5501c440242c0701d20450700c10592503d01c003044450702c400c2c0244c40106078075502550f03d05030399000e4003c040c900c4180024100440b06044410310004d0310420040c0143d08500c402001e100e4455100c0e00c0ca001c1d6100c4940045880a0300b00340d07001980000c10140c40d0740d0005a0300c800c007000a03c419070341807640d6510004e600c15880303080d0030700c25034003a02e1051600a0041e50021130100b6030510139468104116038a0302c00360b100d140c4510910b00004604880300b000003c0310340307070040c00b103040031814141d0549591f00565000c4404941d10840220f440780709002210901131104444140e03420304141c0400300d00a0404254066441800404d0159888045840d0010803d8600c41265100c145044000e840c0c04003021304070b405020740014607440c007600340040250144054102c4d03070386c0305c220840351418030b80f2603102d03c05400c00c44002140307041c1e4000c10006400034861481c2c2503032503011900b5112084c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 645316384 1250 645315134 645315149
    0x30103081803030a0c020d06020c010504030c021302070b06150f0406080a11070542060a0501080105100f09091b180521030424170408040e06010201060f 67
    0x32844414086074168850103041d0100e010b903080c02c54844000702480d11416010388104c1c1c020300d030786051241c158120790b441000c0700c000b4001c0d403a00b820007503c0f074003070820101c0c092507410800c1905c2d440726109895189030302407604045030311100c0811075218503410501c0c89090f410450145280e4450000708018a070f16202d051503460058103100c21502c0000107040d0480e000c00c088000124045211a03440a0702903d2564540c0b16003682422603040c02000a05180325410099204504040d4a0f100340802c596000c182a02c5100445200400713104250304040010f0080d01541e006540420450b98280307010854150381d0341048094034144141c0104200a2451003018036a003c4203500b44981180204c600252801012a40c0603581e800c2e4886509882c0300100030514050080f80c000349040210b07081c8011583c40c807070112207000c0130700e200490242c000d2202496400701e0394910a80d044210542054031f4070039502c1c00303204003c01550443d5030b1403401180e071031103905001024040c0d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 645317634 1250 645316384 645316387
    0x1020c01090c06090b030115050304050c040501080a1118060d0602190e03011a010504060f21060e01060f050a030b010e0904062c250f1508160f0807120203010308 71
    0x401d1030180c0000201d4102403005c0c01c040005100c0310103040b403080c910000342e150465403a078070b50070a14100075528600729031050900c8000035030444002030030003955000c2c02400c2e079000c00c04020003000100001780c170002d03420b0b25000541c4c43d2800b40045403006d40118805441c1280704501801c04602119012000c40d8020b41c400b00b903804c00740320f0170600110400d80a0740402d51080043c020b801248981c4042203480300c400c07402c1c00d205010b042e10303200b4001c95844603001002c4210001d008280201034000c00342400015041d40314100010700c1500701d4594924001c8054030840c007070f01206a99034188400d040c290065603c5414031203200e2400b0f9900010b04001e01700b4116a5802ca1504424103099441c1101050100c0407548052984400a83c11020f0000d420703a510f402a080e8070039400c80396040e80019103001000c102c0b10141e100f664030408030ba07a80759610042150405840360025290f03000c1c18886034083c0840c03a800006900304840034812500f11042607a009070822a9000130 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 645318884 1250 645317634 645317639
    0xd1a040b0f0405070e060102070305010204080d030b01260408040806190b010e06090625031211040b07060c0203160807051902090a05071b0809010206310501020c01090c 74
    0x41419266400c003a08540380c01d96410203072100d0f9600c01d1140034912034400c040f804202541c0c000c001050046500100135511141e85040303841c3c4402080b06600c4c0881c1c1800c4003d2525803095800c500c07603020807482c1800b541d6411345e8005254100030030840d00d09004020200c2c41003001c0002900ca0071000d51401940307034110110034152055007180a0502c02c0d20401c8080076a80c000079602560742c10b0322840d8640180070051800c2c13070021011032140000d003170750729070915502480602d641680d0100500040ca04d0010805280c400c61251a940720000c3c440c030400078845420084460035107104580c200050152171048881e4070140440d115600007800d6000c006040c402186048000f00c11401d6507136030307030300403980b0b0b40d01c01001126025a901c00041400d4010a40103800300f2204122085810b21460088070b036504c25502c075805841580b00150400000305c0c0c412540c3d0007a41c1c003d11000030342c01001880f20103040001c17503555409102c0c1d169030300824030899066502656854050070b2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 645320134 1250 645318884 645318893
    0x1e080d0519060f0f05010822030c1214041e18060305010e0a0203340b0307320906040e10030308010b073306080f25090b0d1a04 56
    0x195075510418107000c40441c100013030f4014100c800d04880c001c1c281450700343d85419000c1c8002144600e42c0c0041c2103040141018160b01c0090481d009210341c0e18403c030418841c80c25640b03690880d1035509584070412083c04090ba044103445020010510882c0002d0749500401d40900b1130900c1401e96665540c104005025003402903070100c100683c0903203124211600820348581a80d201c80c800c031319107038560120070702c51520100382c01072820329442800e644614240041d41d006942520006400c400f07050146010a036220026462401c90040401f260034079241050300310b8106664010b00c144800030784221507941d203500c5a0764482034804124251b1034050310030310040e080707001d03910b80c1400300a00050540d407956050140b9118084000c1d0650360200038441117280381c0003502402d00a0001d0707842c400003140c0c1070444200c4140c407103644d182e01c1080c030600025071a0700d0308104c40d48810845541c9550204001c020064014440b05082c1d442d000141c3d1010032180030141261401c110034031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 645321384 1250 645320134 645320141
    0x10606020d14030402060306010507170c0c01200703121b0602070b0903120408070204061d060109120302070b03090f0f06090d140a03110c1915091e080d0519 69
    0x4031100340810f046003440d030080b410303501004040c14141300b00081c0c2c404c00d10103070f1303000d0060003003440344d4241d52407103c1040d20741c5602c50f04d1600c0340401d04550342e100d401e4110b02080400c00e45c03207800518003145991030b400445184400d80000b0711803804910a000906205800300c02c038050704016030b40303a10918003010290402000c41004d9041445103525801980d0141a0400e411103200303a15134084d070000030010842544184007200031804909005001c0c3d0806e00e00c645000d8032801d0b000e9998036402c03c407038540044020b0050700302a0060200c0848103000d55005444102241c21a021903042546402a00c0c1d000c80c0c80d9500003c01c015400f0b0f405c000c850048519860134141c86920302c60b08003018013071685c505081c16142c145032840356500e0010b40302c0f12480c400842d41300d40e9021800e0741b8145400182901c03280940c0e560f11003044400c6c00b820b440d140c1d20804860500007042101d0071440041103044940503420010901411014010180100b01c40d890f20780c2d800b1841403c0700200c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 645322634 1250 645321384 645321407
    0x7060f23091b01050a1d041d1002090f01110a0516090516210920120607021c0c0218060118140f04140a050601110708120a020a05010606020d 62
    0xb034150100c0c818a0390380202a607985090b60700b000c204074109105800d55016500110a41003454a00c3c00c0c11001d5204241c0c0203248218015200c130794050550174010b9100b004aa07030340003864002c8030100c03544504840d02c50542e610060328207080143d524581810310700e01003e10011824002444108518400e1a030030001c80000e00794030a5001c040541070742d40d101140402d0500d1003072000409200c942150751019404048554203500380e00c10301102d840881c03561402120800560003000304000342c01c1d4001c00d07442c0c0081143e130041c401502e80c01c242c0030b0f10203000c0154220600006884954075401159049011525140b4050000508840c01c8030701c0000000c2e1003100400030f4101050042098140560f40c1b219842d000002140160208030a486003079500941000311058460b40b00340e0050000741e035841d20750100540d0140d80d03000c9501407038003103810101900b07840e07400c1d01e401001141e4190060b43e400e00510740f141e50031102c03158001005604609542142c095000701074900303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 645323741 1107 645322634 645322663
    0xa090f022b05101512020603060112050f0402041b120c1803050a0c0e0f010e0a09060203040f120f0512063115080307060f2309 56
    0x3942d001c0800e2202807991400d4642c0420001404c407202c11180b02c0030740c1101040c169020000242d101800c1241441a06030b0440000c144d14003540d80704006a2410725040c2c5010300600080e03898400311342075124802c510301c030341403504945004003c1403042e40005040100c040b06540913000703801e00721a401054903001082180000342c24050b58410609041440e9941100780c4405805561150440501c0001400074021303030000b6076031141c048200071842070ac0c107444660072684252001d90342c4120550401d024040c02c400d4880c10344d0118a490305001805020003007060141107090340301025100c01055440d0303201e0500c1c082c007003a1072030002051204400c90342200184510030300c058905000d05014065000c00d003503000c80311004040c6140c40702d10ba40d00c400502e03034214403241c0207541c3d030240c81c01c4c0d1034854080d10760300c901040580e2a509090104a29061041000c80b8 = true := by decide +kernel

theorem cover : BRFrame.Cov 645143884 645323741 := by
  have h0 := BRFrame.cov_init 645143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 645143884 ≤ n) (h2 : n < 645323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
