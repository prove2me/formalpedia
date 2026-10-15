-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3961
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:10:40.008782+00:00
-- url     : https://prove2.me/submissions/449c8bbc-2728-4d04-b0f9-8ea0b0e8b7d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 712230215 ≤ n < 712410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 712231465 1250 712230215 712230223
    0x1e072c091902010c0c090c120f02040f06081503030d1a040506030601030b040512030a1b080601080a0908040504020d0504021002010c050901030903110a0305180a030b0103060c17040809040b30 84
    0x6101b110f2040000b40d040b114040c1c0103500c520108240c452501c030703008941b00d407a4802c0e54250340240402140060525030700740c50100b07018100b6541d13245840c113054040c2c0d0342000109030303548a00f2004280910511441041540c10700e010078441d030b0030b1030308100e0b45450000b0602e044a420403d40c0a00b501c450030711030309101281d044815260b40010412680781140e0300402c040b1080c10030490300e2000f403200101e030364480030340d80a400119107001023070300c00e4243d0700211100c502a155652500b0764a50007d0100e03880f6900800b00306856200708402d601d001034010902d44a640000d010035400c00500030803a114000300b00c2e0505688400b032000b8903215046402500d5060700440c3e80e100c8a904028140350024107804440c1c0e2001c60586e40c941c107200d14084110ba0b170010008200e43d003150344035005803048400813420000d441a40903200c0e4450042c4502407030046080f942d8881e060814481500c5030909183c0c00f80e0000100c132600180c00e200c610300da01010105419952105d00001410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 712232715 1250 712231465 712231469
    0x2090f1b040e011805090d080a0605031c110a03080417120411040c1d1309021806040b01050705030702040e070b0409060905090106081e072c091902010c0c 68
    0x9404100400c1090001000e41d0584030407600304c414000c4444000c4064501c2200d1026064002103003070150070740500d03c41900041d01c524003160f02d545800209160004a001032008441c000c20740c88074003600084011200d1107043c014011118281e1800752250030040d000030300002c1d210032a055200100c40070340c0c06285680320342030600d00b000c0c1070090641002062151082e03260110400c1000d00425035803200002d42c1244a420034403400400c50300101c41d03210088855110f00b10200140e603801586250742c8007219007404035041420900003120f0000a40f641032003030410106000c42d10000580d480c03035904860210f002154007600078101000e5038440508418003041c0400c0c0740500740c10420a0700c07400d0340708100c0366848004190907a002480344a455802c00311407203040200291100140590007402c0380c220582e907030500c0d00d000c900d1070300003c0000c0444040c0d0b80d91841d0f40c030301f0300d400000110003801d40c40910b290b04040c0309034180000b814012001fa011007003041d00700075040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 712233965 1250 712232715 712232761
    0x1909030c06050a120504140c19170304090c21020a080606070c090c030e06060d03080705031b0301030c0326250b0a1401170601150c020d080d060b040302090f 69
    0x851b0819190560341500500d104401c68001d40c1c0461a031400c100b01201c030961396038010a01007a14044001541e0003c0700c00d41000c1c1e00041201003000090340c040c92803001d00c2650750204a203403460500007004504e9062105d280c0c010084034422a5202c044c90b034000004840560f40e0704850b1615500c0001a5485121010b04164a00542c50341542c8042d110001117415102c460762498204514554142402004581100e002c00c00c400d03c02c2c3d02841d849240314250480740d00d641035a17040690000da0048540d4034100406104001c41c2410741d074100c0120003884502c0d020712224140c2c40e4090f203c50b1915010250301d280e00c03101e07825a60100441d070007200000036820901c8000d0050204c4007298013424070450000a150f509601c0c101e61007000d80c8018000a908007000d049081d1800241c0380100141491904050b07a11201c04100c500d07c00c841990340c584503c0c09003016107501e43d0019541c043c4c203010810142c3c44d05c5007101e501c1420316201e01a15985c80607401031120340c808020b5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 712235215 1250 712233965 712233971
    0x15020f060108060a0e0606060d0b181f060e0f1c0602030c0c1203010605030a09020423010602071e03110402160b1902030903090f0a080109081909030c06050a12 70
    0xd82c448003242060282403010f100303001080300906425a505401ea4143c0c0c0c10a0f02005103e085100c9503000d15400d940003000c1500d0840a0400d0110403038042e0762015800000020045040c549156100018506c60030001005090b00700020b03d4001c40905450244c92203000084050145445c1005801d522810464407801c099515400c20b4014000c40d0b2200e00c01d40303451004000150301030b06e040f64065a50146140d40f00a003040180c00c1e4503208a8110391a520503c0c500314130500c0305a82c05201c1a5110855898141e000b40350084e6540a00042d582e0182c020700f55601e020340c81400d6070703042441c49240d4045100410006e00c681140a0450b640c2010903504002d4120032050180c1110070701075008545030103c000c103c1c4000c0d106024207a004005040071411b207034a40c4540c0c490020404011180d031165030f542502c518003403c0360201000110300c07510307501c0c50b0340020b03500b0704034503180e07400ea81181c6d030b4400b69000390301482003806000f0440e82042842074034841e140d02c4000e5024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 712236465 1250 712235215 712235219
    0x12091227060c2310110708040603150e0610110c150a08060108061f090b030703240e0f1b12070206072a0609020604080721080415020f0601 61
    0x3820016200403c0720401c20b01140200500001080700e041102402c000d05515201032541d14000c20306882e000d2005c0d14207000300404510000d0107840105025100841c14850311095200080c22542000b40c1c020440c100b03002d084d864400404059007603a0418801042d10721000074648045400640da01c0581404100d50749880030020300a1f00034141c0750381c050743d11a200156800002129180e400040b032038143c245002507407800b211811141d0801c201229150b400400e4035500449410b4042900c407031003404070001540000c1300981c0115101e011407070400b5040d04803105d0207003000316015030741c802040840365140d0b0301d0000186602c00307403a0f0b01c4907160221120103408a848401500a0307800203071115000700a0090b41d035a440d030341d0860a9450040000600c0c00d1b0b01c0c015030740b85641e00070311801a15550010700280c41d0246c020200b041ca0b00400c070411030140483e02d031742c0d0b800700710b0711000240c00a400d95060f210a070b01e0300e00268a00503001c81c544030ac199143c03a414482d80f000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 712237715 1250 712236465 712236467
    0x21903022a01080a0b0f0d0606050a0504050c0a03022203060501060318030e0625050109050c1e2205041101030e07050d0204240b0a1209122706 63
    0x102410303107034040580904034401d455140e08118600101d242c08a62403c001525401d4140d02c8001070780c03030062244500d4103002c0041401d01c0e407806011a14113580d41d005015a280c20070a5000030942110103200b64600564054124009c00e9290418160041190405100c0b0300345103c03500c085054020880a96a0404201401c1c080c852000400e1801c03080c511503440c070340d0741001116007645801220164a1061000f1540081d201c04810f010f07041040c1800301c8510100040c0078010170010400c041a03090060500c034401c030385140b0525840700c600f00050341d0900343c2c040440c07080354030701ca1080c080110500701d00003651b569403055141c0380070002000b4101c01403040c41e000a030f0302001513034451400e40d6034800460007042d90000c20144000c005282507000301c114001c03a082c500f1007030a40b410f007808108a01c1e800006401030045411199281d120ba00c0f00500d407a490800d00505001c0d40b10720f9040f042d40c5114500304480c0260300c03107210b817108088171040c1040744070783e0010030342d2000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 712238965 1250 712237715 712237723
    0x2030c07050a1b05090105010c1506080f012016110d0f06020705010b0603090718060306020a09030510050f01030807231b03060405070b030709050d0605250207060f02190302 76
    0x4030b860110344480d0800709003800e1403200c1c00e060314010707114030705140000e455510b03841c810083c000e8111601c2cbc1c14082003400091200550b0142c02c03900100d0302c000080a0240340c0004180f0613030b40142c042c84101061603510f0b803041c08664011a903860085c0091b000301e0b24459111078080c00303031010b280c0c0310010004141e000b80000c0780110000c001049214080204034031040d202c500d02940603180920110740400743c0804d2040d8065800a00b0b00d5076a07452005a8121865190202e00018010800d1000c284a8020314540c0000100014504030800c140c61580602010700130400119aa0003080040d00b0070501d070325205910f40090b601f001c0215540d440d07500708501024003c2a8415180c1d007000205e07140611790000140807003074100300c903081841d00300400030302c2000404680002d0301d4494000090700d5500500000c105031601c0c901c3d4048603030850070903440d10007419252b80d04c3d480e40030550304250350440c505848110b40001c001c92a024102da45a03121440c1c1045038000c240d000a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 712240215 1250 712238965 712238993
    0x111906110d051e1303080403020f090403050307112104030b2d04020612250c0f031b060606021005010512070e180f0c0f0a03050c060f04171b040c020a0602030c07050a 73
    0x4407a1221030700c0010500c460303122f040d140100418824070200f000309000307204046070401c88008949403510003c0c10b5801d010311050f10b601e02c07044000b4051091000440c102c55019a0701208011103260b00741d0f50081040c400404400c14502d840042421599044c080b01c4030008903078148400c0d400c140071400c1e40b0525041844031080e09040c01d001400d4000c5107502c100c076411944407a02e2081649007540c035074915140f01c901c04d1180d2015180081c505200b80c0014000d164000c2070b0300c02c0422202c204503041a00b0a81c46200c0043c500715159100181d40c405841034142c0c0100c803071700c480c42c00c0320341c20104600305581c1d809040000c0861010000c1c18500445045500c41198820301c41400b10500b82400080d10640019581c80014104078000b03100c001c14810300c003407070301d50741e030710700714690400a05000041d400c10004400e103400c400d111300c107500304115810030070814032403000b030343e154807445000701000e80101c0000c5292801c2c1095038141d5401c030080c1c80800c0e5040c40e20280e042c0442c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 712241465 1250 712240215 712240219
    0xb0d170a11011e0605010f05120a020c030a030e0706090e0a11161109060607020603070809030d240f0f1202030a0f05030a080f1909111906110d051e130308040302 71
    0x10000c0029a90b03c103d001a28800782d940f500e9140c0300c2c002e102040180b2740148000390082e000c00c101c1c0084d150420080c0000a05581e000400c461581c001c01d0802d0300c0c40c1e001001300700ca1003205100f503403c0d20141342e402c098610000120072190501581490151080035200c403000035105805001044019003a002e0341100e2109580d5680701c10481e582c0112040a5040300c410300010b00b04900400440390018084001c8034204001c1d22080425100854070702c044009014040e0641e800ca00013140002d03000703c41170000329500f020801c4071303810017501c00c1c0e54411400507929015500d040c400c202104d40c000c0c0303000302054824180b195880d44602c1c8007000041c4481c000a507070f0f59001c410703140911020045031040c010341440700e0014240fa1903080c1d800c41c04140b10b80c00d280d5100c4560000303498040c00300302c44061a00c0070290036600d6042c2000300c039403c0382203d40030b07044e03101049a443c203955043c1035805018107542c004050240c0c0b111804000700200022081c44081070292080b02d1003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 712242715 1250 712241465 712241471
    0x1518030303070f23190215101d040506060103090c03080c060f010909020f040b06210702010c0206060d030c0f0510150503030a08150d0b190b0d170a11011e 68
    0x1d91005031313032001081d2401d040455001e110008820640901202902a1a104030f42c0204940d41c07203032540301e4041e1000c166803006500700b000380660900e0900504606200046a240380c80c0e01c0302501c4090040440d410584d454004000700402c0712040009507400035002900d07144440c4041d5035440003a50381000380c0800d44e0000841c2030305805095619031f0f0140000300c010815000b400080c01150410560004080c00040300480c55880d0b25070a541603426401031500b03080d0720107400c4031900080c200840d00100100001d6444511071214515418074250059800500b07102020080d4818020124080c1c5070034445c3c4203285401c038a00e4030f021060501d500c00d07507403810140c0e00d10070048480e0204410000061081b9046084c040305c00b0806000c00d1886405e942d54100403010444800b07400c03a0045003500c50798401071140e0007a503401503c803070981010507240d021840b1b0060607220141140040e50814003803103000c0c0240056100c0c0000c0c88242e1910813212880c000155042190b946 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 712243965 1250 712242715 712242737
    0x120c060207080f03120703230610090e0411180108060402030d051809060f04020703120f060303091502010f06150201141005190b04030c080d020c1518030303070f 71
    0x1022501c0b080002d0440025031512145c056151803004000f0001418141c0e642d240e244c0e021410140c006041709141012181441d007502040007480309486418100903080c14140090344054003215080b0b0b40004136802030808200001d61140443d4500d02c540342104800010f00d01d0b000149580558400c41c1a1400001403040440b070901449001c03924520302000d06010b9818409001500510013918081041d03d012700803c050380c0c4085011800941e80d0200760381800194070030032a40084118091140740c1c80c42c0c074001c068483ea8040c83c07a02440c0601c952155074003d40c403d00c54910168014050355544818441079000403242100c00b41d401d001c0c0c10320b00012a42d109034070501e1802c0180550300c4c02c04050080c01c4000c500041c1b0101011200400e41e02080005400107600c41d0006d60082c9080000c900c1c1810b090200e00e50940d0b01aa02820b000c1c2c0d11050044000301d0192020380e107440b011f003403503081c0d960341d40d09658140c0400401e20005591080c2c650070b0740165901c6141c00b0756 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 712245215 1250 712243965 712243979
    0x60405010501090b0618012c0316080312073510061e0c08031f0b0703080c030405100603050115060c0b16122901020303130204020f04120c060207 64
    0x911004d40780c0d944107004224070741001e0300c800080850458103140c0042c15070990070640314101c803e800c1c0074040c1001f650320740c4003501c2c0c00c221420b003002c1c0035592805020f1400949640e00d003d00344c0c5125455074148001544107103e494198000150500407222305d003e6503a841c10a0301c0c04e000f002450600f4a400160000c142d40400012181160348482c0c0c82d941c1c0240f011021080c1203c42d404000d0880040c00111b45004081c501600392030100c186502031006144250008a9210300207c50040c030204001c81e400443e26a0b12454080100750780b5030317440c41c1c0103040c50300b50501980003514102000c018090158046820b0065034850301c01407546411042e80d2540c0072050041c40e0302e4070500080c06800da110380c280318070b80c40b03401c1120a01007804041002d48a03070791054201d2018021143c0d5429480d180e484915800a00165265040c070304210303903092421400207030065400003100c55100440c0005c8a00071301070080c90742c9100000780382c0030658440318442c01c80103100c0c07080081000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 712246465 1250 712245215 712245221
    0x4232b0213021e0c03130e15180c03100512010f0506031506100c12080a110c0a060e10140114030606030d1d0a0303050a0f020c0607061a0a030506040501050109 70
    0x9070481c0f61641c0b040f85280107580005610510303603d41c0034041803000c100440b030b1420001014200422034440c0714606101d101032281c407100681442a1b10040181c039113404110700440e0010482c042c13040c0d0300d90b10b41d48220021045a0301c0150071511380660013070710410650001d50700644504090003281c80c3c210405a0f288414000303040b070658048042105803500c00200d000c05c45a508040e008000ca50f10b03030590030100942070b5008100d5000410000030403a11031075420407900e1a400d82045038102a65035260848032000f00b030640d64908508118008102c0400441038118003840340700c2e1390407101c0c02109000c1c420481035207074030003407400c080c90040360381840f4031130140040402080505085403082c008032a4040c00e40d20741c0c060300080d038403601c580c031010b036009481d040c1e03441045003401400ac0111003012811904010b905018558904040784c0100350000ba01252064920040d10750365030481c03800c0b60340007107251000810080d0100d0043e21842c01080200001d84c1d84141c51029 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 712247715 1250 712246465 712246477
    0x100b040e030f031504020c0a050111191b1401021309060605070209190204170c040506011b0c081e06100609170118150e0304232b021302 60
    0xc980041c0700c0c2d040c1403582840610352040049142c0489841d115000c00c080340e0001c0301c00202600034030302c001c2c24400700340160203c86107180c90180c5448407101e450200b8106003c2141c0c200207801d85495106400d01e005010000d4018082c0f006070301074001d285000b54000702200a10f00100d80c00000d000145210f0b00084458035125149402070603420880200e00c010b000e0840303820246005516800188085c002a10400c2440c0c0c42c14044a05505c2c50000b20000702442a03042a0403c2200c1c3d90040d65540e6a1035019840440e0b0700403480c1031400c0c1e2003540c2102c8050710580980c40b40000c00e5049900c00b110204060b02c499464402d9a54030300e44041c0242804100a201c0c1040000f2800618038039a030b0305c0780300004a107050b9981800504420b55400d45031070801d21150303101804940716015011107008021031030036260060189a04d4941100c0da1001146480c50f26602d0711050000307c6101d4a0054000c110145d000301c0c1d155444440800707138080c2000c000c0c21034401c100c520850700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 712248965 1250 712247715 712247741
    0x2a040b120403020304120f02011205060f0603070c05120406080106110a0312061e08120703080a05180a0b04112209060b0a121205210408040302090702100b04 69
    0x8503214045809000c041000792045046100812000030000d80482c000121544a28100d8043c18003a00004103000c1e888080c0d010070038a071000384541540c50300b1242510142c1500c02c00e8a03903807410b50a0303481c1000d01402a101d4020010400c1050417108001c1c41642d48944445280740d0f00c8200c01c8558000b50146003919502c120240e41c007003801450385194401c07100401003001a140d0400d6006003000050300715482c000440c0900200405009604103815000d44060500315075880003002c020f006400d900c6816965000304443c4d05c0e664001e08a00c3d0b60f104100c0340c0d0f4214610b041c0e45081c3e811a000c0d580302e070383c0301031001052134178822540e040c0100300068074460220803103020080240140c00c890166440c46090388544400061100405084014140300862400c018000900d402418400c1020800001c001c0c858000601c0ca00c421001440c0010f03959945044501d500c6580c1019620880c04010014407503400504110011b269031010311440c8100824041900c0924850342 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 712250215 1250 712248965 712248967
    0x6090218040e0708070e102301020714010f08040807020409030c0302010b0f01080a151a040f05040207031b031101021216020a021f1e080105030d09050a2102092a040b 73
    0x34506e4400c2e158001c035100a0507016180c2d902058007041031a6000101d400e81d248a150380343e981c060000e0001007040652104001e0704000000b040282690148814800c00e48049800d0003021300030b0f00c000300d40c0504200544203642c100601a88ca007110110011b40c02c000341c001150038814003140f209001a141c4002030b84031060b20030098113002020140c11200d40c0350000d8240311a0782c8074550b2460019640d40c1da1030824000107a0030f003050300400d0203180100901d200190b032204042c408419111040e00030904149001c860000c1c441c40c10202e29800822441c0001003241e071124012401c0b1381405000b03500100c0c003682c46126498010754003e0300d0f42c0300000d01c032042131781a1a81c3d0200c0c0c41c0141220544590f09141000b13103100c504d0014201100520050408222990010042d07013000d1b02840e203081c0009414110f02d008010820000b00020040340d418070b907120304826401440b088907460b1491382e10360407030407103034118040c504026800800040030200b2074054034482d18980b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 712251465 1250 712250215 712250219
    0x100605040e1801050403050309010e031c11040b070309170c0d08030919050d08060114040b070f02130902040f0b0108040b04020d0206070c060201061706040f0606090218040e070807 79
    0x25501c02001030103148404210340d40d1424200c800e1013039030321545c42512400d890f420107118290844024003c0039132079030f000304194440d50b04051160005d0702d2030048041111030032416002030902079580410641c1e02d01040002c10960401c50715410b0f1910154000316141850011641e10180c1c3d540d200d40110b010a0700c0c0707022859000085a101004c0000c5418518208400c0b882040314590140d5154020003a50800d107688802c150b0b41000c001d207001079003074201600040062240744142800c00400141319420803c98610303901e50150010a4588400d03207028040024180b0403404903c5145484926a108180741c4596400504180d56441960359142d4551821f84006041a60302c01c1400c10b102c1c0040c2d94050040141501c50b40c001c8801074030309540030b400d50b00a50030070046141d0f800c804001d0544000781e00ca80c00758004800c0000c180b0281420002003409801071266a400010318120f41ca0380010500c070010802d9604002001181105540300c00307141c01015101d4121080c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 712252715 1250 712251465 712251479
    0x17030c0702130213140a080142030302010b0102060906070e09040501090b070c0b0601090614030a150602030414063a0f060314210a020c100e0910060504 67
    0x202051458545034014074200004c9001d6a4094190344888041000801405100d080003c503280080402c10300a101008140001e01043e180b48901c812280341c40c450018a65030409060000140c400d05c840e080b0107850303080080c041e21241d00d5030fa0162080c02c0c08640c0c0d103200000c10354810701079075980800c000c034007100b040000100584150f907a50b40fa420340e00c022460f29128035000d40000e44440c1502200381c034055514400051526041c1302a42c2000c00200742c00011000e2240704140b4480e94998540301040d0041180e6074064182071892a001301d81c1035000001001510080c80c0040a004042030401449100e803110b004030140f108210482000e58054461001d60b0b030036800040084012204441102d4500014103120390f2280303c10414070500307014a1042d00d0400d4043d12544c0c25130740c4104d01d041c4184d42e15042d04840004c0c98000316100744010105414001e21400500d00a00402441800780c1c90701c83d40304030007034004602041c0c180d050b910708450103902c034903051914100c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 712253965 1250 712252715 712252729
    0x2060105060703090e1510050403030507230d02061906290d1815050624040b0f0d0e0f07140a030510050405060c0a171018050417030c0702 61
    0x82c00c0f014040350400200e04041074980756032003204814200303030f4525040c204020300025001c1a01341801020003040c000b12b03501004480c165904134120584240c003540c000c2c0744401c0c82d1205003e4600600788804081640841d03154002d620780f04203080342034030300c0d2890b10031294188182c03010300e010400351040069801d0181a07090701c0000d0661704042001c10481c2c1074030402100384050b500310030030030001c0190701c40c528110f600007100200070714a00381000c10810705503000c0084540ca481c150840c0b032100400b0807103015110700c46640b40c4800104d00e104c1d2090704098001c030300542c140840205920b40008183c81161241c10050403003500c2d01c20503101000440045c80c1d0441030b1200007002003007040041007541100088001203a01d42070074828102003000d04080d441c048104020304400d80e02c0b2149010342d8408292800700d039110904850000d0071244e0041000010481c01c900c030704906640494421402980c9485000300c03940340108241c8000c0b180c0300c0c07907071406114541c05420920 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 712255215 1250 712253965 712253977
    0x1207052101020c030408010b010f0807051b0c0d05060f0f0609010b03091608101514010e1f0207180c050d0209240403020a170c060f070204060308120906070206010506 73
    0x4000500d004910140e50b130a641c007582140281d6911844100c041c2c1d64000282002c41080e86003038560780c140030300c0050540c440d5444101c6020184590141109030901804030304840003018800019030354079000d921004204d0740030540f88144000110320313112030184a8400d460040a02000b81c1c00c0c044103000c1a080a80817001610407940c40c80c2a100c0c2d600c4009028000d8000100340c040000795580e4251405a68010b8130003d40300c408004020941d42a444044424240441c000e203800006c1035120510528403d01203100b81422441c0a802144000968a11401d000151081c3c1d2404405440c004416100003600030004650000c8689e800f40c8910800100f07044820500d1002c450250014228011034240000030200118035100d1908001824210246844000108030745c98951031620803060043c100001c4000842074000205e0f203005500134800c20646480741040715440d0403003031103052403191510204415440001d141840360340c6a500070041a0b003420244800e507000301c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 712256465 1250 712255215 712255279
    0x110a1d0d030f08041e030504030506070914270c1b030306030601210f050d0f02150a020310030803160f1b020f010215010e0912130b07150515120705 65
    0x2503109104040c90544441e840c550103a51108c3c1c5850a6081083c10014091310380c009005145200b0800d130513080e00341500024003140d8441c0c030f103000c000c16500391566111084040c1c2107042c0c10880405c03540750161808104600300059100400c01e04959030b88400c1d103a469051380100b004121504280481121210300a03880c0714808080340d441c0c000606009108440c503400c0841d61056059202802200a04e1184000d080d84082112440607820f80909995402d035000800503c0c06a07a00c0680b500550f402240c856503442d0001040000001402c01100020400c20329007910a22030008803c9454440c0b0a144d1a40790b41e90800440400d1040003e055020b504404680a040041c0f41d074001c1002c002c10501303900c0e10441090625596244510354480240a0a0103403403405942c0c1064603941d003101681c6080c0c0c0d04005000d000503281420410f070621081207180c84822000e4a03070350b403007540c0c81100c3d03000c500c007540d49605041c010b0a412001c407400ca5511381454504000d550295 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 712257715 1250 712256465 712256483
    0x605040807062f0702063f0a0b060903030d0518150613020301030804060f0e0a031212020901020c04020319110703090e0105150904110a1d0d030f0804 66
    0x450b69801c401d40340346000b401e26071400550b0403100c044200d00200600d12041e2803061920144d9400100d5501540740c50030507004048440140040c1d00010500f282044100c1c0b00031030070a8080f112282c80000c540054809061000b0842682030a0007640c25111005010f141411004000c0100405008148081d052014085907816078024400385000d0380251001c0c1e005c6242040c1400840038000d1400001a841000104049514001654207580d00d500d43700c15000b240301003c854a10041d640315900035600b03c0e0000800850b03940021000703c2c10f4031890304803000078140008038090600e03424090780096015540a2400c1d0b40219405110150501c0c142000e00d070f040002c60341c2584501181480c0004d0b01800e140d000741a003801400841e44001240d0f0400c0040341c81546030417a00305007501d001c680d150840c0d0b103503046410201c06620809480d010070340c8009200f00040022000b64161144c404c41060501c800c28900743c0390143c9900c040601d04c8001281c0d4480e0040c030680302140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 712258965 1250 712257715 712257727
    0x30709141305011514190809030f1c0c020d141308010914100c17040f2001030b010504050a0e06060c01020f12241003060503240709030f06050408 64
    0x25030b4440c4501070304c1e5284512206a0344042c0140204074528104441d5402c18400d45040d11441810051803007824a880581919140e0344c05146008000b1615010400841c0882c5068261a582c020f406c174012014018403c1561041e40c90303a414220500000f0f4203100b08201000e4075100a0101c100380844018400b43c1c4c500116007180d07100034089400780041c002045010704204000290304480403c100044000303100c0c0036000c0c9510000c62801680003c00280520203100c0e00d0000c45904142210b004800b0038008011090110355580d0200e8070700700c0740b41a954860303401c4d101502e402a00d100d20443c1480050740000000414265000758104800051303d00c081c005001d0301101c001c1d24039161043c001e000540c2d001d00926901b500d00c40d003c25807580b2050f850003042110425281c80644c00c0320944110302034902c540100360907200e0350804081c2030751400c42079103243c2c508030340d880c03100c1d00c4003001203660401030301c009820107801a01a90109110740d2000b50428072440e96949000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 712260215 1250 712258965 712258999
    0x1e1512070f0905060a0e01050d0f080a0f080709080618030c0f0d120c020a0b062704060c0f0f0e010207030c091b020601120b09010605120703120503070914 68
    0x11045401010100e03006441c10400c1e0310b000d00070703150840c1c030131101450140d080080b8a2540c5c101407041754840d00c45c2e20900d005000c02003005c20710b4680c03c542c01a1741c541003000090040ca40d6607400303000140e844400501d00381d108410a80684011401404171619103101d20900440070b50498180d501007007000003502a010880d03994008a50703c0039025203820310740e0243c0802140b0340c004c00e20b2410900050391f4640c0c0030841002d071a522108100c9546c8807600030900310405062041440c1c00e241e0b20031000e60702d21200140c45031740f1440d0300380051301d40d0002c121807210199504102281007064050601c0d4082c608443d03240c41d062040345c41440e901d0700ca10b011003070b49a00031404207582e024080010000d0300105004010b01c1d0000b04040e500d0300804020800b542030001d030804e02d8034004651440d80a40120004010040c140c20355061102072050311000c0d035110031202c089000104d40d2640f070048003568030400c425210b0304440c91604000304050660301120942c000e41080301c0e85004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 712261465 1250 712260215 712260223
    0x6010503010b0618190f0e01050402090109030308040f0c080f060a060305070302010c050111030c0a021618090f0c0b270603060105071104050403021b0405060f04090203150a0c081e1512 81
    0x81189540c0310854621f420080344c049a8180c00c45401140100407054650340c10030a2402200c0d0305260140050740c2303508100800032031154004140c0b110030200060403000005a070420050101c060300d01c2c40d21031301d240c0c40c00c8a02510000341140c118403000c0015600030150206182c0c051800440c0740c80c0c41c0050041c0369030040f0748508040501185880085034100071191010407061400305600d0f007409141210b412400c0c01e0243c40a80300c400c00810001c40c42000591954461254884c0d40e880ba0642e000d86c1c0c0020080003125030765580c408451000c0002d440391203d80107402645035480c4c4600441d69544403e03400e46105101d1010380010307890318403034075111f1070107907001c0e01c012441c10040e042a00306419855104508000510415940d405071200c02c850044a00085d640c4107840071a081041840400000a8408040041981d06a005141061410340e01d0041607a2490b41c040b03207454041c400720801001000009006c500319011500440301d00601c0c0101d90b030901c110042c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 712262715 1250 712261465 712261469
    0x140304051e03030708060f0f120304031a040b19020403050d0e0a170c040b0307081002180109030b0403120b1c050c060703021005130c0e070206010503010b061819 71
    0x10781c031100d100000840380c1504001d1500120026614500b0b040030001c00220000d00680d2048000e5028540c1e9980c40850040403200b000d00707841802000c812001d1b8598105200a40d01507042c68a5549505001615688100d50261842c401925440400c07007009426144105900742c2c04c05c00840440c0b020410000311040315592428840840c0080c03022703c203100c0d4080080721944e03402d84944c1160109840030108001d6900264451140c80041d1030030880d84e00101c02070060014400a140003a001840005521405c60400039001700c0111103003610f80c130020700a103103600007007070000744684401111360040b46400b2802d03009031030019074010400b05061030300602d603025075810020103121102c02e8150480c0c045003040c03050348002c0d40300c60301a14444506542e43c00068006056811400c0e5084e4019a034072a10544481c03200300650010380c1d00c04003500c60071000051038501401482d0140300080e1200341429454500005083c0b01600700d954400c4500600320320491a100300500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 712263965 1250 712262715 712262723
    0xb07030504030323240d030c05010f380f010806211b0d0503191103130302180c18040b061809090a02090f0a020702031006061428140304 60
    0x80c82d810020324081d4000138400c840f04c540c807905c0b403000900e07036900c0b06102481d03505400c1450225034289001801000d0740b4046000b85880c0c11740d2000700c0c403140780b907140c031509850060ba5542c60200400803a05012154090b0b0310181a4210000303a51095003c0e9800c5003010b407400b05080d03008542134244030f0841045050036400031440000c200c10754001c10201607030640344200c14400b1038507025100e1140c4208002a2080b0a4444036254403441f0b00745403100303440d01501d4a8000100b02a61102c1030307440181d01c0742045507454441c88400d81c40c0b85016004501441d89803801202038001303402514100981e2156550081c00b0080c1c803030400404041100da1030300307510514541c08002502d1000740044255602250864005031140c1100c1030300220b41c5e2003240034980e540c404840292090310303c025010700030040c540d60f400d402900a0415209651100c000d03d8801c105100c4450162080e540741d0100300c2c4000740e010780b489000c110040521071804844803802848050582e84c011b4034200c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 712265215 1250 712263965 712264031
    0x30b19060810120c0608040804030506040503030417090f01031d100506030d0518090a0e030a03051005012c0f1c05070b0c0c043810020a0b070305040303 67
    0x10000c0d42d101d805026002c8641004843d21054441c444200200c0c003507041482a0580820140190f40e4241c0c1e00840c0c2c0901250300c2840d003450000c0e100c0d002960112900c100034102109020607250079100d0f042405003041ca42c0400d800700445c09054002d40c0c0c480c4480a100002c505101c00748102008440d0031040403c80d8100403042c140f9280c3e03009500c01c104002403010b20318800c140800801c801c0390440c0c40d180d02d501d960040100500400d0400b5940740b000084d01d401c1e241c1c0580042d4420030001001d4007040390f1701c00054410b0f4000441c88040880002c20310949171000000c550301c5020050710081441c1203520200c0c0e400400268500240035940a05c007041001c02c00065020300b1200811a0818071300340349403a9100080414184101d40350001140741054442040000ca100c14544410041004602c1d00c00789014030304d11409038210102c9101658000910310181e1540006400d10076560070300c04a00900300904214101a20344030328514901503202e0f11503189441030400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 712266465 1250 712265215 712265221
    0x61e04110f09100c05030d0908160302100e070609090207060b0607080c06060406050f0d022206080601051c1b0f030c0e0f0910091722060c080a030b190608 68
    0x100c0d020f03200450400c1381d85401880000c001000b5694414140500030a81011514051140d4000c5245c40385100d580c800c0310406060740007400c021001b040820402541c5807030f07041c0940b0b80030b0328090032000c01c0006500b001034840c668010040640202000070b0304541000029000380d12884c1c041e14070040c04280140007001c180130319034002e10308503820030007180750a02040a9000c0000141d00c141c0242d044102551540c1800b10300e800a0300003411640ba141e014407400a1116001c1e10306c091141c1e000114140c1009804608582903503041109610740d40d40e60f6070803084111105441c0ca400c001c100142c3d0081e08240070001d14801d40000c0c003201d080000e04081c90383d00401002c5172154400920610b90008100303c0c1c003c42c0070500c0482d619956060410101030014003586c610f403c0000c0049082c1201010340740710414043e0b01040320b55550703908940784825442c0207880301c80100281d0300c07414041c1d8003034001590054480c4031501400062107120550551001021440d00020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 712267715 1250 712266465 712266469
    0x1c080711010c020c0d0302011e1505041406060c07030c0801020301090c0315030209060607080313020117090c040506010e1f08060a230d02060d0b01030b09061e04110f09 74
    0x20200000400d20000c1046076035514000356034150038580c00b400781c02c4050b20f880500d4801c1d0030240c940d0110544001c00d0603a040140d8005080354282d0b480240b00321440032402c0e11b001d009a0031031410f0141084842d484800800c421544003900b1109e8038440e2000c004000760142c140e100040c9484000181c4a624000c42d007015100ca0f45404020545851001c0c0003200f40314841c00c040c0e030340559641c2034640c1c80e0303404512980702e841d4000c0c00c0441d0200801c20403103a40d05000c4403c52003a0f030b4030180c01c0d005007000340c2c10383c400f0340307a2210343c1d00042281207142c00d0030703400250310410503d05070b9003007004d000100c3d598148070700c07550284400340e0804815081d0080c03010ba8100f542920301642191400041d9a0004071030a104807040c0410001e02c0307600c5d030b20150b1b0030702450340080075150b6419076555018001c000c82d540e8680801d0034a04041540d162075881d0521400018105004040c40780c8043c04d249505045034503449542d8161282e59110349070050721102c1c2121203010743d02c1b682101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 712268965 1250 712267715 712267727
    0x90115090b03030307140409181406010609030b1302040905370311030c03040b12010902091c050109060501060314010b04061e05040b03040605240f0607051c0807 71
    0x103120164141055080c66480000849601211514041c030f860700d43c41226615901c1140d004210a6060045000740110080120011107121308a01004100c06100c0180c941d81d003440ba04000c51100302080000c40e090164643d13004001e0b400d50000c41500c0d900080456540c007105603801e40c00312000c0c200030a011400c80b0120030140a05025400d440c10b800e40b02c4440000b001030410a00c1e0070880b4082c4402c0040e02c0700c40700711109a80e00c60742c0380c0d048080240c016442c0d443c9501101b00000400c208688221740e202c2001030101c1d259503442041141000720040b6080b500da40d80c0c0c0d0b1602000c140d5905c01d031400b9060542e008114542c01076842000b4000603045420381e450200300170004540c20441c2ca0120001e0308444240d20a4a0035003907400d030089910000f04841e00004100c104181503002c580314000781400e007080d071440c44440700300790300b0250076281d040080c0c040f00d41198a40700380584601b61040084500c0d1003034220503201c1801900e5051004140110144500700340c00c86 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 712270215 1250 712268965 712268969
    0x31803090e0a09150e010608151b0c0c2715010f0203090307031124120c090a0320150301052b1b0305010507080702010c0f051b070509090115 62
    0x20801d00c081c5820b51580c503400c00c81c0e115544c5400d0359641c10001d60780c4003900880700034411001510303843c0c40b00300030718103150300c007115805024a503100032180342c4021a01954101c00104d80103005030801001801080c0e4400e4084015820015114102c400500740220b84520300b2010000c0306003140f0000500309141400c201030643d007050107640401d07200000e4810489810100d41440304d00c0c00d41c00f082c040300e261013209207003c20000381c0c180388030384c00e0004004000e01041200e0385030741c0e42090480d49000d00100c641c1e0111030740400300040b510345141140108c102585100720310400a0002d003441d003543c2045410070703401000400861401e540d07110282d804180030611150260500f03d8005d0700101c1e4001c1001000704100c401d151241700300720000d5984070f0000c002500308120f02404004048919000641c00d01040101c0740740309202914200146440b5a400d21142022440d9404000c0303817030f120140300f4001c00107215901c0d03244182c01080b1100c00020b608260b1140c0c06240f160a0b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 712271465 1250 712270215 712270231
    0xa09092c030403210507020d0812070509010512090c0604030506010e0a0605060715020f042411031c09060908030106031103151201060302031606021c0804080a031803090e 75
    0xb4442000071501e5600040b11500c0422071568280c070100380203403828016500043c1d004088124441d040103e0000145100ba504004685490781c07107490031107061007001b01c8180044c006205440d4045507140b4115002081d020a0f10445042100440c3c001e8105034402d030b5880c0e000100420058004c9101c01b6000a114030f0140304260421012070200c0c4940d0707100034415070188a00581d0030304158141c4556064150406035601d50b105200e15500c00b9560b43e543c0c1c0141e28080480d0500d005039410300d5000c45403005141000c00e54985074504401c024001c0400320b80359201a0001055886803c401d0362180a059440f035040c90401401c40e25240d2804181c4070b020003d1042004114041d10802e0504503654003480e075140c18494050030099000a42521611080660b8480007016043c107903040c55084a000c1c000706000e0103460503081e4070050110b24480d0208012a5002e002031900030018100440c3d8000707082e0b88bda40d0160040320980000b800e02c041072007401ba003203080c1c642080311 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 712272715 1250 712271465 712271467
    0x20315070201093507080909040804080d1d1c050115081b01090509130b1527070f090308030106020304182013030501020d0e0d0206090309060a09092c03 67
    0x1903192510180401d41e20841444e220201e01c0d00c04001c00c020440380309010141070100d4508151503c200c20790010f01450740680154480235960303500c98641411040702c040c0240000c0940c4001340a1a20001c40114408600021332900400c8003400b13202200d018810049032040e01d010000e900f800001604010f40c405603c1c29030041e42c0c2d0191001094070801c54031854980c030740d400c10224140140c103000b4040c0495008100022030607800b034142851041d00c034861480d600350381e009804000700351018214202c05000c2140540b0a07418445420074600b48960900d40300d8944204a8000340d00910060307100080c24400390b18415110418041048400e000b040e0b07620401c424491005620b140035204041000d444005c45a00150015504100219640c1e01034079940409001003503482c2805114405c0c0c4008540e1000441a110b1124000176500340906002040b00c00c0d0301c40c4224204116882c40007081c0d42d6124810b80c4060b2240e85141c0f0101180e5400c5000c0c61102244908801e0704 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 712273965 1250 712272715 712272773
    0x503030309061b19090f060311120c0c0304120c0e160f050912060103110303160b150a06170a06150c050109171206060a0f0302030402031507020109 65
    0x1200281190b0003142c80c001e02d0002204155020031503018400042c54001c910000e141c070200d401001c450180d80f45108240d000c151034850135420340e907110709c00c1601d40004000c09900109190102c54001c504502d44078541204065020b156409c41d801c85140d120701c80515404001100e902000108140100e80c002c51609802c010030000c4c046030244280000301411141141c80750b0100c5643e414010301400380e650b003201c4219174900c8240400c07510302c500890041c00ba80350000503102e001745c904010447c80c114a031303151024043c0244c05040b8034078030354113800401d50305c09585c030028005543c0c4556402d2a807841046225002808030180d262a09006010548811030028022070160130804401c110700e28000d801840b0f4800c000e480703410b6403111189000f47d5a00148400721501110110540321603040101303510924220001040300b003001d441d02c42e4003c0d00a150300900050541d0708540941d90a80c01c8130000300d80c600c005135940c1001c0c40070811241000328400510044400501c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 712275215 1250 712273965 712273981
    0xe0303130803220b090d0f050711010c200102120405031c05040308040e0906063a0c09090320030703110a12050c070e16030519020a051b16090e010b04111305030303 72
    0x101c102781025140d03240403104900d1590083c0996003400b03138051000c0d60081030032a5641000c030f00320521980103002e41e40c214806043c0c12030035a002d582005019056640a884403048506d42c24081e603018404d051200001195000740500000d20100d52044010b1408001d120309150703000705000d21603c041d14002044400b1040360f80d00c00f5061003c0d40302c9051001042c46090a0000401400384040000100350403140b03401003040d1500c47e48908800e64481451520702c6c138852044205190b10522208001c41d22810a144614041105840f001583d54440002c440307401000080418800102d400482c0810043c4000804040c00e5440c4541070110591144d03080d0301040104250301ca1002c5200d041d150001c08500c0302d4041811980c90700544000391040d00b003481c40c1d040b404aa00c09042c0c0b032a0001c60b0603102d0b40690b0645005003814055050010030b030045400c4003d642c0c2d00340d03e0700301d915a4803501c04103000d11601c20b42c07164085078420020f101550007042c001e130814070520142c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 712276465 1250 712275215 712275217
    0x219050c0d03021b010f0621080a0e0d1515050d0b040602030a1d0a0309090e0613051c090305010b010c05030307030c03230a0e0303130803220b090d0f05 67
    0x109a8503016960340d0301c8048031001003101c140383c50101c0d441c0c003001c601030703811660154040342c1242c0d110840d91090b40d40d040b400740c8c0030303503901402c0454200130200149204080c0d0007125480240341d507511906a41301d00c205801203260b4410340d60b0b070765182c010b00b40b03903415018001028111a8603440e0392140d0390341481582c01510080449401001040b424003198003c1240c44007504002101d481070b00c1d4080d80c3d6412400015004111043e8012035907500c94000c04034551004002821b040c1c9074a05803000b118a0301000b643c8a0050345020a0484000d1044001205056607807403015800c504049084440d07480c107039414000110300350320001d5008800d403980f081c414280024007c1d43d41c0c20640140604c454900c82003a1018032098000300240c1c10710380654800407040042c10410718902c0d03642d11066812403410b41c81a400e402c0003a111310029a440640c600c403c0d80e54001380b44280c1403d120503802254010412010451149010405d04447c90950714046000e002003d0018180d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 712277715 1250 712276465 712276483
    0x9181e0f072010200c030a080c040501080403180b0d09020a080a0c0b1b010204030b18010b0319110d050d08070c0b010905040519060203091912031515030219050c 71
    0xb4107840b41040540070400c021111801354200040daa42c50b9802c45031652039a05c03070301c80749021800d80d0740400d90070003042013960262081a101c012040d2140e44003901d149280c011002c40e104040c05005c606404000b028003100740140402040c0038030107104200d81c40320113400075074a96000038920303008140e0003c0e51400302d5904207411941c58440442444044050036645e4180b580005000001c10207608a40780c8102001075094029004007080c1b54284c46800801035410743c00070344c124031270409921300c0b5241c0c1445582c0b000482d82040d404200100c5050700d055902d9004030342c091a08075041901e4940c092024036001e5070008107030b03580074540b80301030041d50b071000c4d910000101000310400210b02c0034080340c0315070408d6201034034041c00a903100712941d94450061443c601080d0001c900b01e00c40c60343d0321060011710040314110450080c0203002c64590001e884400002c0c5210aa142d06078000009650140c3c0d190782140c2c2848600c0b0282c0700b84002c00404000e0002c94810109460b06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 712278965 1250 712277715 712277743
    0x303060501200c0d0f08030103082703060f0c0405041b0201061512150803070b010302040605040917070303090f08040306060e0633040803120c09181e0f0720 69
    0x30540980c245517080a1003000001d001010000004c020b002040001e400e9400000c000081c0c04180100e103012007000300001d8581581c090404107803403003800d40040350300c41c00d80c4845a0815648034000b500f034850900c00608080b0300c4003d0300b00069420700550300030741030803d01da010000014200901d907c0e03030b8000c0d032242c89a031000a0401400c11042400c0200440011642c64003081e0a0080ca806000c0c40128402c2c1d140850004250426015581c2c0c3c01c2d4010124040e1002c0906c9800d600380d03c200c00880030155111089000110102c0a403440707540100d010721307115819464640100c81c01c070307080740d920320400c40d00b00700c41903603441d240b0814020000115940104054102c510406864a192400d400081004a403c1d0800005898a141100d161014a03150b410280e0f10910a60301ca040d0000c4003a00400080400035102640000c500c0744103544041741038101861666054881101c0d240149007404a11584080c050f0004e00303104a080303880b00100081140c1d10396007043c5000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 712280215 1250 712278965 712278979
    0x204061b0f150c0314070e011b0209010b120a05040809040f06170307020301060518061903060213080606090c0a0f030b0319020a170304180b0307030303060501200c 72
    0x103041280c40601141665440310280b405422900a81e0002c0c0c0049110b4100081c40c000b05a206400760012080c040e9402c1d4558403d0900080d0045502d030700c2039921b40100420448d01f040068480d251450b00030126030030741c3d0f0307203409085408000200d006040144428101814400850850310858206480840340046c1620545141e00c02a04903907000400e02c0420078000d6841700c1001c401080e003248210020400552a01c017007200c4d10922540300e041c990306600000320241000c8400141e894503915581101558a1707a039042a40c1c020b0101000307581403d0310412084c04c04000d016040b106c119030720000f072700d40075489100038007400100c01c00b0044107004103070300640290312000202d5405820360b039170840054401800001510401c034014515081d001800e000d4415540844c031040fa4080d43ca014500104980d4400b19581c81180c2d040c2c0e181c03085006503400700514070080d4444d84012401e1071a220005d070010840c041c00448400c0c046409400100c0c0100303480d5800042101e9170 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 712281465 1250 712280215 712280267
    0x30b01060c0614071e0305090a020f0622150206060108070e010905030304030b330f13051302030714061b070806090304051c02031b06250501050a020406 67
    0x82c01c0608031030a80201e80c1c1c29808280500c071680400301d050040c1c00301c000c0740240c50784028100c044810480d80304e540354128a90300c1005140603d9000c00d00007000740101d0501c40809000123400e400e03c80d4007001240820310800501da65010406030b507a641d40040d04544c501070001078400c10780148a98200b040421070003035541c0c021b80c039003405401c000e000c507601d5540f05c0c0f41044141ca0300303803803814581b100b5075003070300e4502210381c06220182d42c1162040c420384e103500288948140c5561000e03600608955503a14052030170b108280c42440042c51544044805006050501e11580c00001194540c40e4410f40e06444150488840c501c103c030158400c850308800040c00e12140b40c0214815000343d0080c0103901800001800c1540c000700e6141c0d0740d20341c010880003074a003e40d0000a4061300705012003840002c02c00e180030030044002c1d101c113140c130801703c1d1a42a910b80b0204440010012441c900c8180102442044e030710034819403003140381c6814908040c203054291018202581154080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 712282715 1250 712281465 712281473
    0x6010c170d050619060906050a09090203070c0209061c0206070804090212091531020a081b0d0f140f100603030810030b07050703051309020a1404030b01060c 69
    0x416128031110108592102011001c0700042c1200356181841110b01610500b600001c0c4152001241c0d000d442c0c00094519100003a01c0d541c2101801b60300348698a400000c810086000561150702295202d00c038140f801c0c4100254001e0180002c0e00070851818001d0303251300e00a14189002d6011110b545d00c840d410b15158540d4810f1303400c0300a600d400810661521266040740c940200c8414003620641e0a84400042075540304850035284a888410b4812801d8000300045000f00c03660846108074003030a40104d0072000180d8000729199100c4514260b40d902d403030748822150b50342200d20902130441512813164040c0740840180c51825203094a10600008004131542c0b00400026200304600021103140100100e1100740c0100d600789001502400000c03d0316001c1d01da020502c2032640d110354604803460b8100c08812000c0c000e08209011290b10402c45c02030007080804c10159544032401c00060a601f110003080f11031400030300040c4001100c89801c14152000f602e4a5800500300c1c0c24 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 712283965 1250 712282715 712282733
    0x10060228080f0702090f04080f09032e060906120201211b121404030806030c0409210203041401030f020d02070303050114030d020c09040c030510061a07080306010c 72
    0x10081684000140c0100e0034000070014220f028000c488445c000d5540d02d051007004801100c00402c044020800c20405100c08005419000d00150480d0b00f00048240407a0a101c007880c5c015181c62102101743d890496180200e00191130090f03c107004407417510400703030007851820100a040c4040241d000400030142c40c0210952800c00100340714900d410040c0e505440c64916060000848603584041e8014450280508004203046082c14541d1251400c40f406100948070707641c180035204003070040d5665401045c0c0c0207030064030b1410f41036a41d500c80b80700b0705261810810075508141b004001101401d1244034042c582070801182001c100e0800d08006e1054185000b5240c3c40450309200703242e41039001906a51080c5450001d4400340c50402da50344024068540040e406401c140c202400d01d02d104542052280c9910040031351a035a406051020b803114902c5819501c64003003061052200c3d2007407036034810550081c0380200a40350700c411444024a401d041c0020100d05000f0054844 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 712285215 1250 712283965 712284043
    0x3080426030a02190e21070b1c051803040b090d06090620090a031502070c060206150607030806241801031a01020304060c06020d06120b100602 63
    0x40e826681d20724048018200940050075072481401c10419006401800317a1185032940100030318803006503a1501808044e1204003002036103602604000145014150380509081002c0481100d4140000a0f40310211742c0001c28458241c81c00a40c5940d0100000c07049a060300e00e0707208890358542618001c0f071090110540010325682c90300c09004184a080d44c0029010a03409007421441c045d0400303042000d01442c580356500c0b51101c0000c100040c852903043c042c0403c10940581051080c1c3c503403c220003a5580302402680084017003150031640c030018101c011004031500c0b81440800e8400170300550004040758010041c5600d03190540410380d0226002001000c0e1469546d00d411160621071701c041c0d0f003000c2c04241000c59420b1400502a0550203901040e0300447c00c261400d0412a1580381964056600c903031308101251204800e4000d11014220406460107002e5052900c0c5006510003000004e6044044d80244520b56000c50240096052048141119010411600454580c2ea = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 712286465 1250 712285215 712285283
    0xe100207030803240406182004030809090a02030903090d02010c020d060b0a0807030f170c070303030516030507140309030f042306030c16060f09051c0c030804 70
    0x11040000c21307064030580852000c015039821815250080912081da585400f400116100c90342c54117000781102d501c01002c1e00030000c40980c03140745142c100c2c0507a5015400a449241001031888102d080a410250304009031004c118990701d0714072075140e00ca000e0712540f18451001e0144e101e0541e03200b07001c006406500100641c0603070b00386142c6200100441034801d40146051600029050808100c2104898010440c510307490050340e6410303074211036034085400b0f101040c061218115410080702c40a1482034400203000d042230701150b0413006005061f0b0080505000810450302d80c8030aa80c2416441c03031100035243d455824006085010b10001040c0285c0082000244028000c800c10b44503400d03401c810110541c40c80903c12284400c5603034440081041018600c1100e648484030301450040d00001071110a0b00f0048082c1d404480d000c0d0340540c03002808840c010040000200d0003916401c0000140b00307255005810108000c01c064a42c032510540e1110340ca45d1580036858805074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 712287715 1250 712286465 712286467
    0x7021003060b13060e030a0b041218080c01090902030103111012090606031a160509030c041802041103160c050a0c0b030f07050405060f0d0608030a0e19060e1002070308 74
    0x2c1694222010802c612408000030308104010003942001f02c2c101d1030241c1c000e449144690303500c0d00c80c03490751002000414100300c01548030b0b241080e2581d07140c00c09460442c0240c01d042c40710000040582820350003070801c0c18810001000041c41040721460266010741e1045c11500140200380e8501c640c441c08242c83c5824040100f0030000580d0090050724403402090390b80b04400700021424a10071150b04030b15a004c42c00301407480b40243d026000c880c00080c00c0b5400c00b034603000481c00b9140d603010003e03881c5140b011902d04601e024000d01d070701c901c2d00140316402c2d40781042d15142604050f10000d0180a0184203540078007105202c6002010307084124035541d0740d80c64409007415402280c00d240f420300e541000c5065203106204071000c44000504c580c1c140b4440041e030f00c100d43c1c0038510401d40f4982d1070342e0004104200b4000752140b000e50f526101c0c03208904105100302030b500c1e02c07007000d401c80090340140b011a80125001c0320000054074030144d0b016900000340e140c05055000a0801c00c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 712288965 1250 712287715 712287727
    0xc0201180b07020a080c0306130c26010c1404140409050d090e09060f010b0f0d06090c0207050919051e0115090617010303110304051c02090702070b07021003060b 71
    0x544a00201602c501c2680c04c4c80341030759103000031521303008409000359042e0408804075000c1d480c450129100c46000b12249d001c107503030b10720915018042e03002c503080c02c503268424410030740c850030301c90140c0001d490b04058070000306c0c0c00ca0f034413150304c100d0103000f24a41e24182041401d80320341e4003841925501c5011a0000219400041e0103000644141c0c82e0b9030070031000141c070f44240460350038010301624441c02c1e460b909040c0d03001400c0d01b11490540028106100403005410340b40a400010703e4006030008015510038402420f0452507001240180a04428440c82d0000294000d41c0014120800034070340e00c50b11201d070a0091544900207103114540000b003060030b01d034650441d10300312a84400e5034442d5a000700b65030760700342103000c25181c0305400700402c0031034001c0365190f07009082481541d141035216000103000242d100c0e0418010b1032000d50f00c00031803d1442c9590703000080341c0010481d1301e1a0502c501691300c100c1d41c000b4090000794258141d802d000c0c0e00141c1c040d281c2540410345a070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 712290215 1250 712288965 712288979
    0xc050601150210090c21050604060b12030a11061006140904180c0603150b0723121c0525050f04122303161406070f09060f0f0c020118 59
    0x1038003401140c1820704801940c00c084038861390741040540c1e000f00500801d590780c2d00c614004005200280c0ccd00040b030890a05030481c41400100b060b62495214104050798106040b8900800117002d544c0b022803070f0806001141c0c1050400c0b051a8004022960702e401250104e009410a02c0856001040c8500d40d03600300094220f4000075a403491750300300305100303c0c07081c080c612a0851280c07039282d8004003e400f01040f1141c5541292010b4800c2408000d00000c42c210725001c03120034000420900441c0030405101400d12035a079100050b1014421400c000400741880c16560803401c100e0241540d1142210307005005454010070122002c41e2240d654240d281d4100725411011110011a039000140c4070016001800b01d90340c0110007581170900e0781100e441884180c04017641c0700c4003003528007183c074602000400d2140c402c2c1c0c1c2d11800300030303100b580c042d00c5081a41c01900a000c0b409a05c4d0f540c0380c0e80416012640c14075450084580c039610300068900790384c02507034403070054040306010a1075 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 712291465 1250 712290215 712290233
    0x4120309090c031b050924072a0509131a0132010e031e03070c080a110409080d110a020d0e0d020402280e100c05060115021009 56
    0x200c40c00035081c45202e00c5070038128111001984803c0c020496440b094071224410301c00b92010030070207440d095070280d40303208841141c6490840b0a400c031400140e00e80400404400c1c90300c40d42940c0c40300f001c4152094190712000480c070300030980282a0440003a50141d40f10802c0c4000c55008248024031082c1160740860b981ca09000752804000e580c400c40080326141401e040800d4008503980200040d90801100c001110100150f4148031345919079500b201c036400c80c0410b6111540c0115540c581b0b624200c01a40201d6100e10115005907851802003407450038408400c0c6002c4500150f031882510b840f080034026802140e454038900640072100007008070062600b100513408440901201c02001c41c0c013001c03089901c40d04401e0a000040050030290007410b0b866501c20f44989a11200401e042801030030180d90000041540c110041141031138058072400b01c25174903088280b10b03400d4803959625030040c482c4070f80600300f141c884908113109000034640600c0360030060202ca2010305001c019 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 712292715 1250 712291465 712291469
    0xf12020d0915082a12070801051801030807020a09051609090227030c06030705030105151206091f08030c070503010e070603090512031e0a05071b0804120309 69
    0x460301c0ea060200b00c07840d500c00740003209482c60b91096100e0ba07030480034250403030541d00d200300180442e0341d14082003001100031300741980403940210311525061400500c030446c1a4816030048079040340049017440740000e020306403600414590388d111580c0c8042850b110195000300c80e81da25000a009400c070304284002d4034100c1680c2c602c00441d486000150886c40b41ca03420420780340c082c403a0032640c15124002e00c40c24580050584601401003000f082e5158800c8503140009500080144100d1402d0544c05a800b000e500d112400c0c00c0c0a51011042d401c0090859446042640c0006250307881d000c0ba859410311200c594074805a94450b400c50703882c1c0003e03400c2209400340780000714081c20148036580c0c0d00b2540000030103110307150102c203400400003403038141c0b1180508d20700c021a00c5440c1e40158010051802c00c442035402510440b448108041c01d0411014104410b101959510001d054500c2e40903e01a4000800b2494900c03140d01c1075504c40c0c0c02100b1b2006040f000c0c1500902c600c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 712293965 1250 712292715 712292717
    0x2d09030d050a0903110607062c01050708070e0307080d020c0f040b0105030402150f03040c150201360f050c0a140603240d0501020903100e12070f12020d 67
    0x4040000390015503880c02268600e000040001c801000070410300c190101070382c0070141c8000e1802d4469107402d016075660311145a070b44403a0700d10800001411101c802d642d070790901c000308824102100d00030040000503003110b0802c0781401c86802ca42c1d41c14001c0030700a003400011540b4a042e1100081d4581d0041e0504501c2071700841c035566014103043c0243c08012005035a02c0746181e44070307800c011482d44195a44481e80700c062100340c01c40c0c0340341401507018500600002c4031075841c204106018210b1030707100d48216414908500c01c034a4200d400600301030b001c1c180d2074100b03030150362820014041000c0d002d070400f0703500c00f910020b002000c02c8690090303505079000780f0443d4551030340704541480000f02c2d40c0c000d403042000036110007407207101d16501d80003000c514040c88601000552001074080084d40c081c0d50018415126140c01c0001c803246c01c11010052109103481e442164031600044c0e00000f5010001400b034080040d210840383c0c00356072141005090180c1c00310029550f00e8a103501c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 712295215 1250 712293965 712293973
    0x25030e101d030313061404030507032102010b100f021603080c010506060301080607030207140a0303061e0b040311040b120105070201050105060c0d0309031107060215060105040501142d0903 83
    0x440340d401c010040762101c542c10051904c1e49441d0060440d501107220110180400f4144030100c0080c0040c042c1900850240e5101d0449034a1005a00b4a00e039000c0f0740081560307d40301d683c4070603403030f2400700170703020f4041342002d40d6884039050069040184d401345034141e0361389885010081004000242c06c27600c0e01c540081000e640d6240900c91284030030301a001c152741c01680062100c43c40b9030001c04800f48203401d840c0b5012081c50206240192111089003c00d0301c420341809403800001d4440e60040c00001e60b403105c249041c2549940e41706078003001d025449101210401c0ea119600003000f440780c040d0104e03d0b204126140d0741d000b050250f13512401035003048000512464610b0594884403d02005411460860001507004050580c412001e010800f400692000c405009901c020611a00a08140450855150590b0b400144524103001080c841400540d07031240c84c490032a01da5189595650540c40d0f2112840040200c104464020b01801d4103400d154210181c00701c1c0000368116 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 712296465 1250 712295215 712295267
    0x403031d0f070b04180e010b15070b0901112a160e06010201110d15080f01090605090a1a1003120e010206070c151a060304140d030225030e10 62
    0x503003c180b069200e001c03c60241180d1060001003035070700551125483c00000031b070003000c1c074001c54807980f00b0140103040c8410100c0c48405000031070042a83c0a00070700000c00c48401000d540910038040c0030b0f950084800700000c0f9208100e0308150451100780b510707007207136000e0602528581c01240240640410f203030030314000c01c1455005004008480c0b003803500240c10042030784940c4000f08607019410a011185040000d1a2003050003c1d0400d005034400200740c1d84a1030805030203450005d00704020b99807049203244081506143d10034500e0b40070b80c00042c5203840305903020305000403980001d0000d02c1161150000c681c2c1105144241280a07002e0750656611004140c0d0b03c1e6124402c050661021012915003007481984418201e800f0200c0c08140100c489010607000d8108032000c803103011155500210001702003100c600701c22030030b25080d8070308130035202c91403a05030910280c4003004070401144c0003014041c882c900e9000c00090b00100941d000034400030200c02401d5020194031240c801d074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 712297715 1250 712296465 712296479
    0xc0708120418021306320d0b030a081b0f06090a0b07020604050d03020f0f040f0504050f25050c060a0617030c0303130f20010e0915090403031d0f07 65
    0xe0740c04a03030010854841191901700c3c01c0c0d0794291035503844810801448942c250a14414201a10003c001d176046900c9521400c00e0b1001c50303c2e07003c0b60a1007075000c00d207a070001411380d0049601c2000c00c2e042003042c9110f005107040c40c0080c2c0100c900c0080c020841040300340d04002840310301483c003800082c191070b15103a40503600e884085da0301a182e60444c40038800918003940051105045800d001490b1298046602100c0d1b003058100820795500702c9400c200515050040c1500800e031841b400c8003d00f0141800a40a50500000b2002c08150300d201c4460ba0f0144064554090300002916814a00b8003900c40040003c0c0c0544031381c0c4401c0010f840403182c030002c10340c3c480340c0080c2d00462954650030048142d4003001c2e0b40c00c5580388240b02c20303180020003481c80c102d84100810440050020a1000501014807950f80c3d079014032600c500b0845826038007907005406040a0b665400141c03181d00302240906100c4c0d035040c1d00050000e01600b0381d0540014294075400c03c03c01640c1e2500d0b101c1013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 712298965 1250 712297715 712297717
    0xb0a1e0e03070b04031b0f0c0e0c07200d03030506100f051209010f15081207020a0506092d01020c040504030509060d1e060509060306070f03020c070812041802 70
    0x140100360344144800301c00182036400464216003c0e0401001c3c114035a0008440141068000c6440044d200c5c540d504100c04024150064078080d08031480c3c52074184015080c0e80980d1074064901c50b103403076016606000d81480c80101c0c60300076000d03c00028083c100900580000c1d6400e5010300b2801d103e000b01030f80b25aa40a4511140740e03102440e06c8030300241c024540c0b902030020142550b8a244100c108462446101589840c003140c54281525240385517040c00b0f0404c0030000d544004010900040c0d680007141da0076501c0c00c441181d21a070660000c20034008480000d940d034841c3d1560100040311f00010313142d040201c01d03422606007428410500060300c00940c2d00030045802403110548610b041001b9054100c803030380002803440d10301c40710951711610300d81d2034030300300c642c1d400c42440a0304180c0911584840103400414050400e0700008061044090a034410551301040380c0450300e60030321031301c001003003950b08480041c2c00760a001035090b8080c1c42660240c40c5160000300410410340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 712300215 1250 712298965 712298981
    0x60207031e0228020f03071e06020c010f03050c1b0714040221090f030f0405121902010e040605130e0c09090a0b060d1407080705010e2103070b0a1e 65
    0x81a103001004404440343c5501074008101d038000985075540d042c42c0c41c00c100d1040108082845d00710303055482042c60100361190f030000006c6400c004507000840e40c01107400440740340306103000115903071400c40c946034a0058404512244a0608450f0004200041c03100144c1b420315034002001341e00b050030001207100c2d140d00070300800680003a9000740a826490568010f402d28107940046a0f81490603096500075100e0701c000d640040746c1070145050022903094140725010050004502040c954400c485032400300038100040494040100d841c0c40c2c001340001c082c0540910850440e5007613603c041d00741070311028402d00c5440390082c3d4501d0300000c0c460144003000c0140003215020f80302c1ca52605c5000f019580c115a00200890004100f0304400d01084600ea018100701414410603c4c104803003075210a040045403444c0800315540c0c2c114101c40d40e15801542c40460103048003c40c02d5001341d000190040412104000040301140c12445d20020300a815140e59160100c2c0001141c0d010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 712301465 1250 712300215 712300243
    0x22050a09170703021c03060e0f040f0b150d0f02130b180703140f16180605090f03010519050c0708030117010f110a11030a0806011b060207031e02 64
    0x28403440070319000d4050040012500030300c1a100b01950020070101e0f0614a0308031000000e646003010804090200701264005442c2d01986103541000d4441401a1502420291101c1d82d0700313022601030b40c1e018500803046c010160822005203070506002c01d07025041107040e40255420b40c003241454000d0b204d0b42c080b101000b41030aa03100d18902d000c00018200030001d00500da510190410f6030b00c000310004d4032501d41c20984c0407840c904035448100c0e400c0b1007000c40040c1f1550701c0c280545003601c0030100d400d84141d0b190282d11101303400d0000750f9504542918980652905003400703500b40744d07441182c2d0110f0104c0b1040c0001d86507101811100e02c40e19101130203042c070900042c00803560208440c908110343d0b10000c51103401c0719280a086460280a000c1c00c504005112540d003500401ca03c8501c1204201550405050010140204078010329040c100060030800301c1003a1425201c220b0a20f8004204640f2208079150140c50740f2900c0c0300521b000b41d40d01c005072041c50b20014400041c9804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 712302715 1250 712301465 712301483
    0x14010f1116030f05070204020f09031b060a11070b03090d02061807030201050a170114030111040317070203030d0c02070f1707051201020c0303040b0f010503060417030c0922050a09 79
    0x1070b1401ca0392003e180920328200202001810050784d10b5001401e81c148045846594902d0104100361030125802d00c0c02001e1111221105819076035076041d02d15002060600845041d60400068205401c13a040b4081c1c8800c007100780310300340c100020b0710800e80380f8540841f0350300c1e01c2d1500214150010f280c4c20752115802400144010b511440c0500010b60b0349041080c0901090811010031500c241c1040a000c01c080c0c018080301e284c2401644110b00701c0b007a046160504607215001e007040509509800d04600055140454508008441301d244100070108004904038100179160001482403052100241c4404900040c09603407801542c076020009140c2146000103004c0a090380365120900340d5401e04c0161a030010606c021031281e0700c16110694689020307582c0c6804204181c200c14000d40c4140300304400508540c48140c81d001f41d07104040e0b205e9485d00321018091003036884043e0001043c038694503c016804030002c01c0100004424003e955a261642c8212000004042d1031910 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 712303965 1250 712302715 712302757
    0x1112010f0f080703031b080a11010c03020f040e15090106111c171005100504031a010e040f1104061d0a0b03031804020906030709031e0209060f01020a14010f11 70
    0x101070004482c05401001c06c451120580762a40f5165400c80312000380428140386070f1080700a07007807083c03080c0720790b890800b1400d00c42c040d505021140110301404a41144400100c0d0064601d00640240050b004108003030390340c0c5950380140a62400300d0071800782e2181009200f01c141d1303441c400281a40059032100c0e410190b45240c0c0c0c0032014060300c4008114140e482c007150079125044403030250f0b24103403a0640e0b241d10358903040c40c0103031060144421210303000006004a807a40600907401507000342203080070780c030181440b480f030119220b00240d0051418a000406060301c001c4200c40d2010b5180101255a038a4941010b64804451281e89500704018015140710284001100d009000d440142003070714500128a8a920680c2c0b000007080460404000300400b1800c0000469480c440d2151811032560120350f05400140215114010040b1581200c2e4030130080030b6540f03908401c82030742c1c0e00c100d181094003c00c49407911540301c1f824200403000312180300044034020070a0b074130001c4030b220b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 712305215 1250 712303965 712303967
    0x723060408071b170c090a140106051305090f0105030d1107050d150c0302190c03080a0b130c18080f0604080708040f0315050a0c0c151112010f0f08070303 68
    0x81c280a0481001243d50b2102041c2d1150221850781c201c4180d000803c40364001d001007108280b40182001902ca0030b0a42c80d0242070904018641111a60305160f40c441081d440b0400034010b0b10303000702d60440c50350800c00a1502c0078184080c1220300540aa403004403405001300c0d496103050030781038259031061100300030300c0c28112103003480d09025081c50742c090001d07409a5016102200e420100098012800003142300c0240c2102455800c5401d004c4407184882d98046c216140040c01143d03881e0759489500c03039503102e00020308141490400308000490b880b00019024400c00326500180d101204000b050626001403c041d034031140b18028040c6554a59032454103609c2103200305c03484441800006070000e424032000c00614480c20b0701ca8084106221361200700c4030010501440c26040c4155000c0c190b030003c0c40c1e402c0356a00014240303c0c0c240300000c110302400c542c0192300070603c03000424249030b11504000718140d035220012688590b50742d000e02e81e00406d4901a8002075001b4810800000f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 712306465 1250 712305215 712305233
    0x16230607081306020d0c02070b031e07090e2a0a02031909030c030c081b010804031d0d030509040b060316030e0c0909031803030a0e010302070501020d02072306040807 73
    0x10502c40c00341c000c0c0c9202551039030b042e078101020f0b01d803c240e00c400b191440c40344c051240c2c01c0901141c0c04014190b241c929800080006d0075410180c0d02805030300441e00d89486040307144041c2004540301c00142c18000fa20241c000320120f20303c0b240048040300304c0c00d01c491000c2110899900355000314203180c0c2610301140070304404450101401025000040006c1a180c2403400441c0074449040300c0f14540000b440c1040c0500850b11f03103001c0061800825031b03804c0920326030043c0d0503144c801044040383c90390710b2016034000c0e0010ba22000d850300310710030140d000000300910303903040e1002e1115903030303d00c21b0204602003900c484e0300c0d181c512810b01c0307095407180e40700c101c04501e89000c44001c0841c440100b0200c0e00c041d1071080440c0c000141e07803001101c0107000b0319030150f002c0e0003d5191030008440104054240c03d0028109600084c0030300603c00d007501510304040d0803d000b1983c5078801e1414004c002000d5000301c0c1001da0a1800b80b07400750001c15080d203d150080c00603880c28035030b5903c5103a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 712307715 1250 712306465 712306471
    0x501050f0403020405010e01060201050709030f030e13020f0a0905030a0503040e040c0b040608090c0f0114130b0a021c0206060915030a0b0f0114121e030706021623060708 75
    0xc41005000000250b034482c010036000b4003820310060030b1541003010090a40740300810030014001d0020741000001d9008001145446d0140303040e0307000c2c038503480005511980c2159420300300360003c1010311180041000505000c800342c5c485410a65680080c503464862400001d060382d0800d02c01080802010320103550301900c20700241b100c1caa2259158005070f00990407050018800008200d034030001040000d05420084030722002108400c030008003039072103c1c1901c52485402080070049501c0c040343c964040d00d088210340d0b0322102030b80e0000b50345103024418a0b040480c05842505400e00100742c0d24003d080c00740c100c140681c0c40d1614040400490080260188078060f2804041251051206e008150107030040300194540400002c002c0b50004000e0312403100c1003d8103c18100024940c050300c00c0216000700101c20f000e02c000c0c1140190400904070030700014a0070054515001803040c031a12510514856041c140303404400703d803e065992011740d01007800f2030343c03290150b140564 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 712308965 1250 712307715 712307737
    0x20705030c060a0203070305010b19030b0a120f120f0807030230040b0903090904260309030c0d05070201052b090605180c0612070c020a06110c0a0f050105 68
    0x100d4691000390040c82e100040b201c00c0086076021007840403056140c01114010107a02d010581131102414140060800c024114420700d99610800c0e0b5040d200c4072108070003400c41d40d4089000d0445414111000e100400c0e089038002c4044c1c000c0700d0320a0007103125072501c400642d1202202c7c2c0c2d4048040d402580400501640b41c070480907001c49000e0240462207111108114101003030900c2c1c50504040f4078050b103c000203400920081800d6202c250f101a80550420328030b03100601e1002c04194403054861503a240c82100100300508480004020070401000c10b00300e40c0c1403041000c0c101c940b40501040240041c0c1e08015004503104040707101c402e00d0350111030802000b020400d802d0200c486003002107903016150001c000100481036003410701c112070030010302010524a000600b02d03201c3e121013140300070808000704035158031441c00c1030141507000c0c180c81e00c0311391200805010303200f800ca140b00b402e115501072444503050080640e000c641c0e41d0710742c1d0032031503040000546046c1c0210700348032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 712310215 1250 712308965 712308967
    0x6140d020d0606050703020f1b090c070f0b070f0e0f091005100306060306080c060301030b100803070606050906100f03110903030a030504030815030c010f1205091e0604050c010302070503 82
    0x11084030309219410043c80b4a40b10199155814500031b41040102d40302c07004260451a00c0c800c40442d1085914140241121142107556814012003d1401981000341c038a100b850408170400c002220141c1c080e00c1907486624000342c8403041210440c000750001a000240c4010b5041c00d070900c800780b60b030040e000d030200d0b995903500c0d000840e12000c542a185000291079880400c040750301849a28058141c003409031a07500c4903900804c140c1d1106200003045240c3c01c90004000034175228410000e00964000d89698200d181005405071004d4003aa030b11a04411000c0361035881c00030011400c84459450f6000217900d407130303020782c001e1070b841c42ea41802d11802c102c030100d90b64040c40103191685942e100041e190070a81401441c03440010035019074910081003050342d0341c1e0b002416803d055024a4420100b21035102c04845140105070a81c2d440d60514080c0301c4103400c040b51042d950307602c07400321039070007214800403507500c0e1b0054030702030080d030896680d852955110f9001400c505009208603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 712311465 1250 712310215 712310227
    0x6020d0804020105071b260601030215040b03010f09050c09030a02010f020a0b01090905060601051e0706021213140a210c02030f03040801060605041d0411180f0601050406140d02 78
    0x3138400e0000950803c1c031641c1e204009200305c1c034484a0003030448013803455440302c001554201f20b90768681804040e00c5904801140d00c0c81d00d00c0101290b010385042d082198595a40390301c1400490300b140160703000241001c0005001c020080309852000300c0050007424000401d070010344441c5d08034110417007140a0010070f440860141e0314928028810440c00003072481440c28031604000d1f000c5c103402d041010401043c048000744460b0410350800102e00660348007414540750303000303200301702585406100704000c03c054194946050103180740141c102a200324684c1d24020b807116a82c080013060100340c83c0d06d9820724840c130f00d5119007600c5982840342c2c140c055500000d01d080c0d00c51540140d00c0d4000a420b005082080c0903900090032241061030916080c000032600500703503c00102c40303205400c0c0002e000c0c04403003c0e202c1c1003508040e01145055004204103070b85000c0c200c0714040261758400200760154807610455045488958403000c1e200c2142c1180070b4141e10410101905980078400c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 712312715 1250 712311465 712311473
    0x2b0209100210051e0406050c0d0e01020702030c1504090207021c0f1205040b0304112d180609010b0c0c0a0603051611060121060c0f170106020d080402010507 69
    0x40c00106416940041074030454031220002580e8004010000f10700000710300c404034044803500150010ba111202164580c2c50018260150007541054000c403410724000d4040080c3c194020320a241c000d0b829a0410907249040c40000709954144112801c81040f04004214443c0d002e881302500c01415504048864440442d00740075281c015141004408141301c10041890503a00a02d44181806403c1601d8017820b200d142c000100050410103950349000d1240e5200c11640d103010759800100700041c00450800d1204440d450107540c020344180e42d0049020f6408240507215280c000c01104103070303080c1100100f054000f040c2d007201a2140b10f064849607940c4030341c0f010180c80e06690005552800b95107500946010058600502c1003c802900f16000c0116040381034442c038902241c0310300c900a400000c6515110703c09803c82d45400d2008a0250344240c1014400070b244e0741c2d1400180c010a24101000030030710590707004d03078445501201500d0180007499413060050400318101141074507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 712313965 1250 712312715 712312729
    0x3030a0e0c15130905010e04030c02032401080f1204090e071a0a030623120c03010609020a020105090d050406030c110d08010302011119080c0a080417122b0209 70
    0x6881c03802e40020880203110500041c00b0300003844c0c415001e00c80da525080440901030f502a1000c0d041042200c00d090545d2001c0003045425181030701124040389850051025441c000e004015950007400c0340d00304204400200d943c41c684281445500e060700d00300711280144203c840c43c90b030f60b005001c2c00007007040071640140d13844003c030031085590302d00144004044a60740c2c3c1184105140d0b0302d0800340000498800d0910303d1409a88104103104980803061608240e52446a410340c24001c000c100004181c02510740400c041c2c0080c401ca850b06080c882e201c0d801c1c07008640000c0e805100800c10584250812003041645081003080e16581291050500220080b0320004c508008010000c55901c4111074440301c035110302420070400e80c2d20111030002c1403074002610702400882c3c010080d20003440f0010360260f02c2000d8980d10360386c03051244402c0350304001440362809201c0c1032a140e010000c0846002d803a00d010001114200c0e00000e440d4205c0303411705107080320707400e2022000c0c0b0f890b50300c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 712315215 1250 712313965 712313989
    0x10f0c030e191a09130504200301020d020d090516060804120903020d2a05060a05071e0b100602061915080613021e090c031909121e0203030a0e0c 64
    0x103007515138078445001440654103138114040401e038030708070403c004980940c001d803085142501407401c03185044000070b4007a02070070544c40031181c40040d80f074440800302da01c820203880c85401582d0350880140243c3e03003860454850080880c80d8840013070001121000240503104442c24a00201c0e40c903600450408880003408075225076241d441c0400001d4403482e2070300074004004003419620708040200f01c09009600e4000300f844008a0618100009850041c40040030003a94030440452810b09a24025003907071003080c00d80c050100420302d1840880c0191181200290f60360801c0f0b042038000d4002c007003810500280c0c900c40707003010881400501c20030b402000013211801c01035840b0300400610303090101c5806141c5000c0e101c95040c035151301c00026400420103034455200d0740c4d0900c1401c89021481200402c0c6441e0140220170410502c1400940002642e113080c1c4000e14065900781c42c0c2208a03860700943d0081c4001341018045401159480803e0ac2c26a0400e1032240041200c0c64a49 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 712316465 1250 712315215 712315259
    0x915040605040b0f01030302070902072a1505031003020121050108010b040f061503180c06030518060906010302190f080c010f081b0d020f07050c010f0c030e19 70
    0xc1c024041402500d0302200e0300f01d43c5901c844007242d403540d90003030342e14550740c81020180340e00428080148403a81c8500f6a007024505100c030103a03010306664044040c914002ca00711a0003103944200060300c64400d803071040601c0f0106135501411a001500d0b0207415a00040549018800e0701303403468564080c85000300300741d00c00407840704402c10401041d14a2010381400b03291604604021060850100c419403100a0400240c0c0c10303420007018040035640c5101401c01001c0f403200164166244e0f12a03841205030054140d1031401845a568545000307540540c2c2c2503000c03100500c00741c0303000c400e4820030b05810601d2400c0650b0b14900709042c909a84e1007041c59412032400f082095800c03031030203c1342d0b030000d141984062504000c10010660080d010626054001c41e20841b0f071200c5a044520610b00444c00035102c0509260050781d81c02c070001800d00280c02c0015100031940203001400c00d5503807517191308203191041024001c400405451402070074100e40b00c0001c0020070401180f00c05254 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 712317715 1250 712316465 712316471
    0x3030a0e040606050f031501020304030c030f020108010504020f0a0e03030d0f060e0c03040506011802070b0906061201050114010c0203101b020706020d09090b01020f10140109050c1209150406 84
    0x1000c0c2000308580640d031000c0d0a00100f000090740040d0214102d0380d111226890805007000d0781c00c0100d1460103141c00007421082c8074403012081c07040e4544060440c41c402d07607407080c140c0e0301d48090000360300550006000e008001c1c0aa0000c0318080c1c44040205500502103905010801030b103101074890300007440c00304542d28401888a0841ca540ca20b510880008500789141029515603030388010505c01c1900300f600c88801f0008035440c0d134040380c2209820114401c02400d0202d0000e4580c80180c5182d449103a5012080300c0a41040c0141c070b0403101240b20b0881d410014900540364243c00c0101244d050048503000c0d041a202071164030518400b010070007242c00950a80079203010500c0c0c00c94030540d48a03810711000705034420b90704802ea591810340460702e1b407410300060340381c6164450800794602601c10580c1c1600d04030b40c0154042e503d05601c544050b40e9448903802100e1003500d1402403d002045059082c0b035003c946e540d000303400d46046566500d851a00064200010b071000c89403551 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 712318965 1250 712317715 712317737
    0x30604110d091110020a020108090a050102030f01080f0d0806130b04050c09180115051b250e04080702010503040f0f081216090e0a0605040f2021130203030a 69
    0xf01c04265008907040a41c0d000e03000e03001000019607200401c0e440241044504000104401c0c8180403a01d03d8507131001c004d49d100d0505d00c072030ba483c90000b4000c58045208000b000c0c0d500e46000078080d460740c0e14075112000c964a4013814403089043d0110428032017506c442d80c41708561214815244075600560090b910f0312440810402c9400000341c1c410346d003111345401800140e00440903404100d085040040c0d89116006403d04c4001150040781d00350b008400d0f01c1c441d6a00e822180e50f1030b216142108030041c0341c0364481c2c98811103055602400b464018420040107501540044d42c01501819841f2542d00d529130760385005201150342141d00311008103810b1103880c126582541c01c20141e266005001d01113001c01031280070706100e07600e0948100004200110b07055400300e4040d240183c01441429125101200500030382c1107074030034403203c80d0301a00c1e00012070310a440f444200e55050a45d0800070908180c42800050b082111540c8036924400041c4d40c20801400c41041d0360700e07a441125 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 712320215 1250 712318965 712318973
    0x903042103030c050c060112150c0807181a1b03030a0b0a141815210708060f070507030909060e040209060301020301080c0105072306040b060a050d020402030604110d09 74
    0x10340e10801203c1480340c1840040e81c40c01000c584203040da8600c2c481d0440801c0c10b0f00b4a40d450081c688440c507106850003054011840c0d0020305a84102103986a00350078035480c014031481c2c000c1d14401c0400401420301c1e400c0c0100c035410700a01c03404025994030340856410050f101d0271644240c6024103c141d4402c40350146080002072034005221440250304940170003404904e021f40e4410000d641502200d000812400a250301607880403006400c140c0420f05106414510006144500c00180304203070700080c415000080d6944200140010351046888681050b9865084001c042301440312171a00441c409200d4442c480050402c0d41c81e202090815005020220001500303083c0642d00400c0184401103000504c141401028a003507551002181820844083d4440c800c403104510903245002400c1c1c0058920301039130040426072140d440313100c10066a00054411a9007200e07045030914003600d03181d800385a1003440074001160514440b61180503551210f0001003070b1640e5840e00d04240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 712321465 1250 712320215 712320221
    0xb0a05030f0f010b0a15030c0915050d0e01091e0305040305100203041202010b15090415170d11190618121d0603010306020313080307020307020f06160b090304210303 73
    0x40300b03440c0c12211782d007801c00e4800c10b03940610360030086c56221181d440809100ba5000741c000e04510b00300000b05000761000034482d5128040c4c00034032504103154440c0c112018440c6124a6a01c01001c0001710009486043c00907a1840c090342441030602002010460622456074505110200107a881c0340602e085d00c4100d01d0540e41c0b05c02c581c5002c0c0b60120300c1d116681106944201556000d407280300580000700031348105100d00c4100c40081030000b0351114465050100c88d240030080e14075081c3c007a8811103501422104014140d44002c0c0070302e0380d0150344180c01c1c420b680511404145066102035003035000d581c0300030845421340d40610b40d182455008070b0350b8030030104841504000d01450030004035240011300014003880c2c0c2c0000410b0300b026501441c100d0469104003070030707102d00d0003c001070344035002403809a00489403182107200f80d180000413030300d484e101812a0802c020003600c5d179010210b4000c20080c9103210400011880f040d4507000b00100c0518000000c01121182c0360003016 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 712322715 1250 712321465 712321481
    0x2150403021e1c032403121412040b061219020102061602060a020d090b040c14040209010c06090606080f0105091005073204030b101e090b0a05030f0f01 67
    0x9542207181a0f01022003102041002d42c00c180c500801c000c0510010b28208005001c8038590b04100c025000081002c000065040d00140c1d848440c510a0a44241510740c45031224202d1140c000d080001c00007583c1c0e0714002d4102c0405090010301c0c00e1100031643c54181b9500090300d40c43e034251703c00c904540e0304000e915482403050030406aa0210010040c0d41c40720050103030102d06030041030342503940106500c0703040003680180b0002d182d03040070700f0403512801d0b20380191101c05440f2040d0340314900b00780c0201c82e0b030b03d44180e40c2c1031a43e11241d00c03503000600344040c3c11580f1507115000080c041c00d0402c20b11980000f8034000080c1810440c03605ca28102c0d07078a85000c181c508201c104183c0755004a070f50304001401c00044900c0089035028064403110342a485c0440743c50104021080c42002e01c0d2031845107259080f4030380f9041d103800420f50f802c451000070512600c100c00061003508200d41140c1d850080280039a0000c0c1c2e220340c0001d081caa0100c1c006043c41d4403d8403240d005400034020100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 712323965 1250 712322715 712322773
    0xe030909060a0f0b07061b09140405130618050618011508030a0f05040506030a02211b0f300f010302150c0309211e03070f030215040302 60
    0xc42c8910340400d40c20481203502c01c0e906168000300e088024481690424081140b00c00c007030031900c1c0e840610140c40d69a0501983d91601e4082500744400d061034030406000d4180b800c59010001440d030b035103c024024a11507010882c000071440390010342c08202e03490241c1d480c0c0d8040c808a64008015508440c00c00b18140ca00b0f4244031001c201000010080712207642d40c03443e04221030401303140180c803d03108035848503804c00b50000c200601181d4a0340600803001c204a840c0e01c01d4040760500d01801101070b070324100e00160b480020715503401c07404c0003080b4200180840d2404d10300c04400c00c541c0e4070b12000b0302040428600350341c01c0e03141c01c034241c069902804a1900c030300c0750350454020981d0441a50100b001c0031800203030f080c03d0350800300181c4030504c60081803040355006283c040e080c54503805902403494840c20810902410900442110f040c4000300258142030b00c0b601c0b50482003040a00c1542503001300c0100003a440958140140700301d0094004203080b055000404000027200c0312185 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 712325215 1250 712323965 712323979
    0x11130f0e12030112020a0314060103120518040c02010f060e01030212420a1a0402040506090f01171f0e0403080708060f030f1b031606030c03020d0e03090906 69
    0x5072103111007640d041d1014060481d545240d0b503c04104030070040c1c1c101401280e038251a8581000d80080c102d41a00c0c8070711140717003101c8960207050302c49020b40b41c1d130380401c0503804270450524100f50f40031820105e0f41d8400031031064035000c10b1108450854020164401e9000c0052040d404d01001191b40051464020400c6501c40301ca561988000c01c5510003045090340e010b03060300d11113860042c500551003000090641070144e040c4000382242c141c14030a4002c80700c40210789140910a803000c0360720191015140c03040d0141086440070076514001d05004030742130728103c0c070f071903412086100d400c0f10204074104d0340c04c00304907684030901d13588040080c031291000c1000003640040610741001b4242088620307601d0701d5001501301d11178503039140d401d40300e180c028014498000a0711001408800c080b280384002c2c1034249901d0f001405c40b0a40030007946142000214869842508448000e1800509058a0345c031a5000d0f00c00084160303005510106415000340f500550750303500035000b101e01d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 712326465 1250 712325215 712325233
    0x2040314031215030721030810050307090f021308030a140702010c0210030e03130e01080601050a0612020c07030807021903200102030702040c03050121050c0d11130f0e 74
    0x41c0d034600d400410f549904000031400240c6500d0030040d0002501c803000000e411a114214001c03811030210070168002020040072498030f015085001060741c80140c0a8081c3c01e080c10003003c00381200d42104034555508210780311003005802242406045082e001e1035540381d54804c000c00005000c0180010604100428030043c2e0300691026542030f419205d03012170041c034810a80c0100071200741844103000c0010204c11803c100104070f001d4424845450034a45d0701e03003c103656129001d0140035088284650306010341801100d0301408060200f00c0549812400d580c950f0030140141d1045402200104501c1c00710f1502413920045101d000b80e54200092840d142c004010300c0704d00c11000b11010b80032080d070f03840c1d10034800c0703551003034000d00f040c003540c140e032900200207050034881c503800550140200b01c80c041c060000b81c0380c4a50050000c201116032441049040381e00d1480807101e09505070718414058030707000b0080f03981014001002661800e076100384410750780d28025001040d00701e0b4a030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 712327715 1250 712326465 712326487
    0xc080a0503040317030105060306040b06070605010611010608010e060f04051603030305041e030c030513030c0f170a03020c0f0a080a051c0f1e050708120106020c100c0b0603011506030204031403 85
    0x270707207a0084049a000c920550001d01203101481281409000c1c2400e100c0049400c03604081084a42038103d4000c0080c42e0744d80c440b0314200d030b0292442103042e820003000310300142e500b02d10968200f8026000d035007018585120b041d003001c800d68400c40119484e041040240454442c0300d007608130750044000b1030b5108907980102803400c036010007001d1200204507080c548070513400480c0610740c04002d04102c1d6403940811007100e4400d21030140007030a0005502c11342003001c95071620040e410380052200c00d914000b08020403007020390441c0c002444117800201907408105c2c012032940100e014105c01c07250555454002c0341020044070a0041940d500740c50f15074000d04011070705800d045a0844020064000c0b6458851824058100b0074041070b100748443d0001e106034101e420503000c46101300800c0e802e00100b52a40e600c000080cc00c10005013020520f5241443d60000c0c000b000080e1b50341224048405118094024100096000c03800b4030401c214208040d51100c1414021743c1400b91b8445 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 712328965 1250 712327715 712327717
    0x3030f1b020603130516032103060302060f0906072f01020607141c0204080304150e0d080d091e03081f2903010605030a0f0905060604090c080a050304031703010506 72
    0x204d9000c60180301c0c080f9201344881801160100490311122800e416500e091815106c81c0c007030302082900340c01400d91054140203108400490341e016000c01c0c2094800203c030356140d00002c4040e500120200030010000300031250382240621404151901c0c058030384d9580c0807060710103480070f0541d842141441155604002e059043d5214200000d42d51a881c2910045c0c90445400bc0200e5600104000c1103091000c0050303c1543c1081085561001042c0c0e0100c5801c203014101c070750030140150650010440c048010888000124004078141c1c84655a07420180081403441405864000c540700c105540503e0381504100070414500350400c11411940e44860310f07200790304030328550b1206030070218040c00100510884001e14591690fa5407000601554811260341034810b1400040f80e07036075880c611860b130807150031000030080c0d07541d680c060200410908100307544d0200110340c00501d0b0001041384505062084000e580c13200d05c0c2d860082020603074102c000c00440028001030150780c507110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 712330215 1250 712328965 712328971
    0x20703031e0c0834050c060718170c1f0f030b2110090b01050a0902070308150a0b0304050a1b140d031101020c0a02130b0d1104060f03030f1b020603 65
    0x1c0914030004c8030060181048260b088514056429000c00a013450340c104005d0481c0c40224001d0312802c5e80d9401c803c032a1401c514400001511185130180031559601c000d458810b54000c0454402d248580b0010310b61a0860307034180300d012003c058000006500c03080b08958800c2504050000f0b0440304002102011014a0b411440c0101c0040040c90710040012965998020f001005200054248058003407400d00599000f00c010180009032400340c2c3c400c83c0c0c007203501036440c00310548490341d194030183c0445000750b5000042460114285201c003000750302841c0b06000030035141800e80303842490b078440b840b4220080b1039604c80c1040000300862150300a2003080316900350007035091505880c00e42102880c000385610120303151480420000b448200b0134000c0b80c01206003201c8003403910a42d001c00c04160303000695202a000080c6481c2c000138004080208041001e94451040d00350425041e8001e4000482e0000f815480542050700c0391105228540e5080100d4410340110b40c07d88005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 712331465 1250 712330215 712330231
    0x2105070501030b18040c120602040905010b040e0f0c190203041508130b0a090b011202030c040203070f050d020c01092f180402030708120403140c030c0d0303090501020703031e0c08 79
    0x4c3e00043d041100301030803500500b5200b601034840d205a0304150009400c5402140c820900e418004140841940191011105604440040c03642d40040034100c0e4030020f4a510350b028824040c0e00b0002072501c182c18001d000c2c6a00454885284c44034100d5403114501a00c018000d44205000c003400b19644202c0c0780c3d0b504070300391210302d840745195440281904c5102a02c40460140040b4034409610504400c40380200d0840301c50100003403c00080b44801c1e0307a5040030a1b0300c0f141c9401c144d030042d8090100200178900060415130b1a01c80c0b6820350b21360040444120341c0c0101b0000010081c15000480703510414502c031507064651000c80d010b228003807440120008035100107011940c04000f40d10182044000340d0b10b0a041d00c1c030300420b46401a00040307842120b6070400a0510300006002131071003000800610950407800184a84c1958200d016410141c0701c44c14100844c8007400106055440b030303a000503803a441d0700300c13403803011444100c2034801504058070080242e5009240c84c1d080041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 712332715 1250 712331465 712331509
    0x8030a05030903040f2c15010e130204080102190212070f020f2d0402030f07140d181a13140f061f0e010f03060c092105070501030b 58
    0xa0300c484507146000d183d001070481c00300340e01c0201e80070354544c44214041c44100200000760400c8010000346c45000c40341c0c51140441c00201c0c030801e620420008006000181c1803e07502c10240c2c1904c800d9a10076084800385030740000c1d0b0002001011800c0d401d6000091001c3c020407410014040074030701c180d00014100c40303840c900010940d56034140001d452400207040c820368400c41400541030782c0801080481c03a58011211142c0c506081c0201c0b4031800340551250440c0c1d071022410b0303030b58804030500c01c1c45948c0c080c050300c4140b9025100301e07000e0b0058ac0c1c0002d9100d427203601d131101400c2421482407244840e000d0a100c441c2c410101e0020340d0b10b03408203400020211003103a4500e401d02141041a031841100c0901c503c01200e5601030340342075240505500881c1d21042340949804080c0324204460740118820404240720744e1020482615070305d041e09500d40c0d1100602420b03592050700c245d10350002c103054010040200f207410002d0100b824140141c0ea0004005003001078035400020262070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 712333965 1250 712332715 712332721
    0xf200403050d111203180a151121040503190305040506070c03050a0f110a0f060b030a03080711010204090c050a09060e0109090f0e03070f151407031a0a090905011508030a0503 77
    0x100c0340c142c06111030040840f050b907002c0d03041231054555900081c1ca50349142c100301c4604114101e04442c4103c0d207044408081c005107808401c3c016070020801c0ea440d00052000c48107216003803094820450b101e03036010810b4141410010304124015150f0014825600c151000007034110081c0c0d4030152030381c100200420a20102614090074a2a0321034650040b01d003107404010f01d0340030903460103001d80c1c020405030042e903040c1952466500c0018007c5140400081e070391600c160020703404442190300150805595666500c140e030403c1c01d150707001c07520224071180e01650165188000b08480c7c6000c91b01d03c010900040c02041540c021200580e80303072444155404059000194904880030460340e0350005420041c0904815400484a5483d8480c01858042840c06080b005410103680702200341c80cac42000758000c29400400c408084d084410080c0075544519094000b80090031000c92081c28505e011800c64020085810018071030381401e00c074003c07001080c0e500f04681340c00c145030759807 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 712335215 1250 712333965 712333981
    0xe1c0f0c060c03290609090a0e010504060504021c0209010605070201050712030903112a1c141e070b0a02330a0b130f200403050d111203 60
    0x220803000190415040040007205164181c0c0881c1c010700d0a03000c2011001903488508824001200803158000018081e40905c1e1810310045a003003041c81d500007610800102c030044c2035410868041d516a80c2c1c5000f004194107088004159104070070711a0403e000b11a400220110811b00403c4100040403510300b003164010011110001e4010f071440340d070500005c0c0014064954910304030001080401802d030749580000340301484c0220b145c00c00070030100244140f820724509404d25580842543c81e0f0f0120840e41143c03441c5c1180c06113161112403c1001c0c006881c00c40302d8901091100400c16036150301c0030b00820b200d0306440498504135036920410804130b25000c8042045c494600700f41101a041c1d001d4031813168100c0d45d807089541080e55410035020100c4a42e48051038210002082d50369a500c1294420008440c0c400800114040400310b032145404008410607000c2c0b100103000d109102e4108003042002056217000e00c4001c1c0c104040c0c0d0384030541007034640300c083c0c0c0c0840462106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 712336465 1250 712335215 712335227
    0xb01050904060801150f0b0406030203040f0b0717012120121c1d04090c0f0f050f040605060a051e0a12050a05060f0603100302220e1c0f 60
    0x100401c1441401c0d00d404800d03000303240b0a04104443e4102003000912849038080d480100ca8164150702e041915154003134001c0d50004004031920381807000c3d01c0707000400c4e0034503080c014050f40d40d541b11144141001d51419000603089190305000210310400122911140c440d1b1031948402070103040b13a0100d13040c0c6100e0f80101703c41d40c0d0124a0f8980c2039090000001d21a401c05243c000040719004c00074420b0300e05024075113403007400d02c03c00120140c450504d500252262446029030100c1141d40341c036010540341c0c03550041042c503403842004200a1034107804400046900711002c2150a1400d03001808034401c41134240e040c8240403603900a858140d5911110782144075962035079841d06680010010b080c55100c03000c505141402081d4190010712800c4e110b030b0400343c600140328481c41c08001c4650001024222490a0024040016120f80c81d802c4d8181070b4500b41c00292080e90403901068a805100b600ea1580c005401441c044144050a60488082d401e01c0031265021240888403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 712337715 1250 712336465 712336477
    0xf0141040908030406050c09181e0a020406091505160c0b0d02071202120406031a03070906030521040e0a090b0408090307060c120e0a090603030804030e010804020a090b0105 76
    0x442807500320307000c0600085400843c842c030300c104010002680c8448810783c0740d004500100781c02c00d003404190103014400204041e08401440550401795a40301543c036032604007200c02d03200d03198000c241000000e411240c90000b810400b04d008031010440c0c81d0040c400c2c007c10b40300010110340700d040f0005201510041e1005000c1ca0f14072581ea030440e0000400c0694450801207850741c6444190340da4192000c2400c0358295005001149403602c0c1c854210b0103041c040342403111114406101100942d410070982380142408180400e6480c81c5041041c2009454074880e000c688640b5000c1c0030f603900c0c510496080e1003000c42400101c0e01e03076103d44c400818070688010042c0300d50034103010a00c0348100c00b82040380801c90032070b00c00b0303503c0340360848011000c0f402c01400e001100c002144154021403a000f00e0000240a424807503540d0300e00795080e29819802600441d1240303060000303040c0d0010440d02c0c0b0001c00e0034005603606095011902c0080144121564960389100fa0003290b032040c022204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 712338965 1250 712337715 712337719
    0xd05060d0c1d0a020a0207060e03010b12071e06050a03090825020307090204140d0204140703060806070f0c06200730050d05190c080f0141 61
    0x54031916074030002440b0200000c5588041c01c82800182ca94809000301c4840c3c080aa01030701c00903140440c150380030001c41040582c15501c60791420341c50b8880c07484ca84996600ca4000b40700c920b10f40b04c4a207064030f0b030700c0c01c1089049040510038031905030420b0460f11080c901d07250005e159003607030414150f507000381d4881590130540c2e60351120042004000090205000314180c071456907032441000b040348a40c5c8242c4004004550300c41c6258070700003014041030b5001400c081403040c09400d20381c150040807102c1c600441e640300400c0c0321404007006820750040b03060a2a1004002e10400035008041070b284c02482e481c1c65607400790f042142603881c5010540030140d003079100c01052408145a0321041c3d108a2002841004440c12509203100740071040e000d40c50301450324900c1c60021024000c01042d031490802c0c5181c01003a01c03003642c445d039074103a0101e0f5100c46880c142140c051a9015044c0d1140a03489038085d800d90103c4004001005047c00f8a800a0b10206c60030f1984501300b0b807180c000075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 712340215 1250 712338965 712338983
    0x309011506020d09062604140d0c0b07080705040b0c011103071106090102040308041205070b120702060603060c22030f0f032c12010906151d0c0d05060d 67
    0x41c09940014000f00700d07480d036840700c07000a0b07100d41d01280e20390500c2243c1c1c002c000d05841c3c84024100c40141c8030f60020302940013850440d10b01640c0b14989403074640c02c0000036a144171142c083c041080001600000180b0341140340342030a80300280340e40924010781400c503030002150703e433131902540246000d84924240070344900c1c1c09800901030085038000c180b05809035100080d50000f06108940940c0d034000312076400c141c02e240203501c459401074000c4070f061240a6000c2075040d451000b405041e01b40070f07255035061030701d820b0003810104041e20345030103a1320003824840810b018105071014401c07100000300c005d04a081e8041e0034003419510103016030004602c6241070060301d403403582e41745000340c642a13014610300c1d01d500744140119102c2c1c180400c1044880c1c0351481d01e40044034024411400104003862992141c408403205c10301c1c2e8100d0300380b0940c81049510300c0400013090111113190080d10300c0c502400d89141c0c1c0d02c12a5144400740d82d458000414a90f00c0c000780c002d405400c01100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 712341465 1250 712340215 712340219
    0x1202030a080a27050310061a0c070e0a0506040b03030c060c0a140f030723160c0320041803090909080c0601060f020c041a090c190815060a0207060503090115 69
    0x3e141070140f5014603402405140420041031016010b10801c81d400c1413103d908000b01e0501842c02904190118600c82c0501c03030002481d00c401c5d04245001d80c40f09000058242040010041100c5215600c50f0094200384800c4624541c045002c0d540454a40b00c1155264030b19202102c01415080c810003080c080402c90002ca0100d183c00345214500d42c5c2c0390140e4800308940d00b2200814140c1142c0440a000c1121200c0039000f1104014164071900b00c0e880401c3e2241d56003400300e001840c08951883c004050034510b0704d854002d81c0a21000c2000f49103410310a901d00500d0040c0034051402d400e51604211010803400c03004a03a0a04d50040a4600ba07585400c0300a01601c3c1d854104070042c8a1400e0351000352615208001500c81080d40700c0c5d1240000c2d0f014003071601001000c03d104900180902c0d04072600c1408001040d44413a51000894030b4403100400500811040302c60150006100c03050400360000f51800c140e03115400c0c02c1c0d4590b9503218031580034200b10700d52449021044240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 712342715 1250 712341465 712341527
    0x60e010e060a0606090503370516090c050403062c030a0f2d02010938040203030913320a14070507060b0a0f0608011202030a080a 57
    0x1010300540b120071040c00416561181201c5008250040a9154010381e0140b041030440c1c0b48040c564075440808403120035280402294150200c00d41511141c019a540e04103442e0821150005040203800c100042107a00b03200901c3c50243c0d000040c0750558900040d0380300ca01d48285240c9150f07080008000080c2600c965070349035041074001c240400c4100640203201d5028001480c003c059102509d0140200325040940d4050a00001000d40d56280b200c6808521900241c404e0b20900310704c8507034800f035092040001d140e003140941d002c9010b050180001642c0c0442161001e240498020b0038410302881a84010300e060312860a5032a004001c1d00d10700808440b43c609140c0c54180c2407005656085031140665004c0c494050a070b40003403000900399402000030304903c500904000076901c0310355010500d41116904410907881074040104081c2c1d6020012601525141180981c0003c00da40441d583d0000c2107070003400301c000494a4401c0780d210b800c1e65012540d8180208041b00b1400103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 712343965 1250 712342715 712342723
    0x2106161215120503130915090b0607150e10020406020f0c0a030311100f060f050d0f0b1b04080303010504050106050f030105100c060c080402040c020c0a0311010309120908210a0804060e010e 83
    0x1071140341f070b411a240300094a115a10454411403000b4014502d440c0c210381c1c40e031100450300c54410a605580300c240c402107620410403074100003503401005903200d080160180c907015155448170310b10380c41148198400d481c0c201c9048212981824001e00c0d41081c2000d031806c3c010028003560b140c520f0040700a46200180c1c1003002100d44000c0030003200c070b8481c0b00b80441d8007036a60002d0003d0007040340340700001e00e03040041d070b078007003030f054a81c0820840703540711105030b98450341c40004c89500c080010301081c90241f06050040005042441c0307000030340f0000360b41c03a0105109282c880e2410f4035100f181c4502604c0c0801c1d5995000301e0800142c0040140606039041c10b54090340600c1c6081d110081c501c2c0000ac0c00102a64002c2240b09624511340ea5442003030065030416041585600324107001034404d9889040301da0407a1502c0700e0751410603044500d84010318001e41d0740b01e00103080d01400c0c000200100c46039030340031745401040b41d5100e08054000c0d10401640500d83d620745095002d2402001c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 712345215 1250 712343965 712343981
    0x3040e04030f17070813321501050312030603070504021204060c0e2d0909150c070804050d03090b160c1a0921061612151205031309 58
    0xa222102c201c2450902e00901c07902c2244c0c42c00110f4004400704104500c00c090050707005201c1c8100f08014040032401580d071070b8401400719400a9103148408040314180180351107180b411140d4000d5626180019903925000c064041a0b1000000400c10f517440c144005000783c04080c20556580416004d04034001c10b04580550303450b80780c0104510818801c001c52a250040100a402888440301104954040b001c100c00380c510010007481040780c640c148500d204c3d0441501500342d007941010149c0c000b000003040d100e20740701e040007881c0014000e64251800d407607003070303620104015a0745019a40125660407541c803402d80440c40d4441034001e0105c2e0609130340318960040711682d6440c9103c900035101045800d140000307103c0e40340c0b81e05024111038000f88040c042c005c2c0c440c504954250a1050a13500e00c910142c0841c00291255004081c44203100d0400f582004800d01807401845c0051880c0100001e562980308824140074080003550300d000d110840e0b0304d1110740d44a40d001c0c0209041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 712346465 1250 712345215 712345217
    0x80403240b0307060318060e07050123070b0603030714070501030b01050f0405042c1005090c180709091109030c120604081c0203130303152603040e04030f 68
    0x20422400c49801a0066a1810724050000c1242c541081d209901a0610810070850081844140c9010680074040d060820044c00068114241001c0004082c0302030422017640b03040410200191216640d01203456040c0c00031900e590645030100028158414950040d0031001000c00044c0d2507080882e40800700c032004d8a0811090851400640e200c0c000c00081e0940710809100c100000c0c1099006000c0810140100701e10510043c0d424143c0d814039070706011000e45c801e4070314480703941c050b110340d90b00f0215640051000e080400300044600d040c810395070418620000204006034081c0544102500702c020301400b031548904c007101380030340201e10a41e2203413040709442107881c1840714a150600000201400240e0740e1074845001035888802c01c202100d85806002409541c20310207103000f92418107041800d034046080c0182038440035000c20100c04030a1004000e46c2c5082203801c0103007541c012001c05000101303c0d0107411343c0102c3d4002c0c0c103000f0101c01080201603100380d00d407241d9506 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 712347715 1250 712346465 712346513
    0x50904300201150305070e0c0417030c010501051f030e030d09050115050a0305120a0c080c06041b0b090f032b030e0610031b090c0c140f061303030603080403 69
    0x1510f50f10140301d10240c8409483c0703401040080c006407880302c2076580c0c451540d020706864a80d03181d0109150103409910041c550f080843d04200908081c090540103010484001c0400441544104036400700c24401c0824941e44250340001d441d8144259845840300b81c01c204401407203800c16030302a0250520303640c0c1e2000b86041c00308075858124000c0c419260040010040607255800880f8241e01940411042c00303a10044180000c600074010000514842e001d041642440e1030900c6001d1f03840e100340000c43c0b440d2003060203107030300980035078230f03104821600102d143c3c5800c4003082c01d01e2425001c030718074540c400001205550312a47c1c17500d0f400030540da0801010003003c520310340b0754409990a2440448414041011400c500c900030782c10000d081c1c0060030581d9581c0341e002181c1a9420010200b41541c205a007484406d0500b103c0050804010700f038961108041c2c3c0740c81d40300060564080100300001e00091501c01d0788000041c3d6817042400e075032140c0301d0a1020451401140917403001d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 712348965 1250 712347715 712347731
    0x1410050a08061015050c07030606210b1906030510090506100609030b06031c020c01110615060309030705100209040b0f210115030c060311070804050904300201 70
    0x2800919240f09101c9405000000b0341840d8840f4004072500c0b86004c2086014440080f50000600c1070700010362094030001409840d1010b200b48410a02e44094800d410b144203e8002c61b84e00d54105030b001c80b10740c42490080810221000007407045070409440c038456007004103d04007644c0d00c00d202d01c601030b0040310113540d941c3e080070500c849540103200019126800410006a015426a4102c02c0082c240e03801150030f4054120040107022079040143d010005011003543c114030349411501c200300240801d8505003c0380034028184110f014007405002000070126072050003550015130740714003500d500403961056207020f5040f83c642035110703034a0086801424541038071360b44400c80002d0b00c0c6001030440a50950071340240302d0f000c02a155281c06542100300f501c1008000503502c14000210020308011005003104c403900c20441420307004018000c0414802e10a40382100c2045402e0012036603640307000880c01205c0034818121500080b100d52000b20ba21003041100c6203107a00800c4401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 712350215 1250 712348965 712348979
    0x6030a063204050703060b131503021504240201200d050109050411011215260622030507152003070507031220040311040218060307031410050a 63
    0x1200545000348613501000040001411503017215400200052824419032000000d00d02610510080100706103a9450f040c011451f011a18009641c3c4000180e8200cd080441e1410030680c41301ca2551043c066252110300603100350011201031012001c0c0c115800441c810503070071070b04a400f00c44046403c060012034006000c1c41811301c01c0d034004600f0422800140e00640b01e01111040841c0d84136200c07503801c0041012030200500802c24010041a13a44892440c40c404882d401c003200c610b81c0240c0d0900c5459141d02802990100111a20f821803810710718083e9012b05c40c44900801c1205ca460083c80c0030115580303c02151041501048400d0301c48050703100b40380c03100b120000e010480038005280400c0c800c90140d40b5580c4000000600d0120003175101c058070584064040c1c03081070010f400e108101c80d00f605811149003d4400f942000000c69004034180001500c240c0110130202c0001c0c0f43c0da02c2600111514002d000800384035080980c4c0305240360001c1c2c01958026440000002288 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 712351465 1250 712350215 712350311
    0x303280206070c0f060c12060602031804060305120d02070605131401060305030a052b09020111070e06010309051005040302011b0801121202030d050c0306100f080f06030a06 76
    0x5154419101c2070f00011a60705c0900502134041282c00b0401d100032a003950000c40d00c901c401070101c83e0001d540b10801c121492032034a10030b542c010701407400c203402080029000500d490700580c806207440d4803a550031454400134010344030090540ca080c54148070a502d00d030400348079a10701034002a421140c070400c106007071740c40c90300c8020816881080b081c222144168081c00b0341f041c8862420341c6811900700044101000f41c0012800b081d03640010f01e003190380141d139100070322003000060300c641071800b080882c1c0350b080141024140b6846110090070071406110750340d00c00520160800c560700701420001d00902000206c2000001c02c0350703100310614040d894003412140c030144d81c50008107003651401d0300c0f400000d090800354441403005544900c080c1c011240300e1110303818216180e150074410448896a8004810b080c0403a40107003510b01580102c0c4158001686910300c4080e455040c0802e03c5d098031840003514044c81d048046060000780440c2c148280040032113090308044941031500741c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 712352715 1250 712351465 712351487
    0x9032b030207080412170d1b1e03050601031404150e07150f0c2306150603010306110405030604110f0901030f030c0512040803070b060f030706110a0812060103060e160e030328020607 80
    0x2898070909c400304143e11030b401c0300e030748004180b4010941040c43d08000d6242c0005039003c84129104440d51050041c00384034081c032081640b0001c1c45454944060a01042d51104451040090b410343c14503015004d502c1002c4102e50102c0440d11050140300403012280700009081018028500400c107000d407050b20344059418000d2065146900c0c1d0794502001340b0117611044034144090100040c586d50900880c1d01c118000c91196541110340b008008074803801c006260701c83c400c0d10700144041041000e8800c419039042c01c0a0304006481e050031403424010b09104410580e0016001c40d41d920701001500d4240d100740c041e4000380c1c645a040084090f0380400c0541c042e481850100900740c4181030314800c1c40d000a007901c401542a440c0c43c08180d0241c0e0368161201170110511105591501c143c10007030188046416203401d18580c0b10b000c41d004214041d04200c120503d18510359014422508000e829090b0020850901e10712404c8000344e9125101c0980079410006051601230008030031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 712353965 1250 712352715 712352747
    0x80a020f120a170402040617250f051903050601090f0e06011a0a14160308090d0806060715140121030c120509032b030207080412170d1b 60
    0x40000c05100c580b520f00d00c02002641d11541742c010010f0b01c1c1816815024442800d171024090090303100403040301c0e0803400c4034510703030b000d00d102c0042100c4a000303040c40d002d549044a0641c400301b85d81602030390b41d529075007024015000c1e64000281c0f00005030f0040c54100c840360801d00c208a045102c09484040912488200b00980403108038103c07440001080310f00900e0429903e8605022050980c5400c5984a100100034101d40602450b41000000b5800181c2c5401132504240041000701003010180242c0c0c0038034404103081e010007000d4004002070b500b004208005c8802c58110f110035441080c4500c2c40d040003000d40c0b441211080d0300c00f5010054241d103505c044000380e03543d521415800745808108001040c4411000b65800740a120088034400b0000c22003508007100300062041b241d0516403d052040080e10000b88424040c0c40480e03248800e080c0600ca4207041075a4025641e801001d2602e60000308183c80d44540da115540c030308180b01012840c1c00c0000310a45441c4c4030014032107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 712355215 1250 712353965 712353977
    0x10e0a1202100c1e0204142a0702042a053103020d030801060908030418110f030405010203070207090e03030f04031e020609010b060a09090f09080a020f120a 69
    0x20025080041e101d070715002c0715240102c00140284c48000001d401009118060455440201c0030b5151030700441c90140021244001681402c0c05180c81418030001520114100c4022103001c180580003030341d0120342c01034810b015008040100d262003e042c507000c080c8003540311045245982c421800d4940210491f400e201951000242500c06611052013400304c3c4905210040b005844082c07200300d605100c0e4a54401c6541800009800e50030035070400992a0b000707000c100072401c006940c2200a0984030f2000411042c840a40443d6219400050341203400010600040140c150f000354880c2520741e084d5030089803200190801c0c0c4050001403112588140301203141b00510200b200c0c1c2003880b07801c0145500c038520611f0121448181150809a0890320030414021800e005404510034115003491522404040140035000140900c0c0303000c80d0349900038841506d1540c0407082040c1c0003441d8680312030040d00001d640c0d20400c03036071b02014003400341541c400d0b01d10a1b0a80b40d03010200d0f1110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 712356465 1250 712355215 712355249
    0x4030801030f02030a060f1b021f02071b030302030403050d0f050403060e0f490f030b1809010c0804080a050c0c0a090b09010f1a0c150c0306010e0a 65
    0x400704032003441d9041c4e034940507590101c0005a1588104e40000f1020200404c60007040c055041000054414140954000132000744030303107000c81202403948600880043e20f83c0031604004401c400602107900d00d50500e406c01105042d000000b9000f140e01c58006c44010048080301102d54400d013002500120703134203010500004804c4d07003045682c158803c0403503840e04520018180742040070700030220508082d254034075003001c201050084070700c0c0046541200e10141c086000c01d082e0a048c540040115915100062074425044a006490003c101d18240602a0140c5000c00c1b030036100003045d0342c0307486298903255019203020707885640c000303010a0400b988000f0580d6264800e0705410402e014058008131195620140c41c03000e070070030a03800103c01c0a00000c5c400e034400107030041c024110007007104010006032400e10000051900c40d015413900c0031a00150f1030030303150019000200c80114104000c02600c0c0d8003441c41007e00b680c41d114280700c110b050019050f4640100c81036001d010312a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 712357715 1250 712356465 712356473
    0x7050c06060d0203030705010f02090307090506090403050306181905061c060b060904021c0612050303011a07060516140f121803030c0a080a020901080612070f1e0e0403080103 77
    0x100b001250010701aa840c091842e42c60b00e08440150410b0401560b002ca10048a41801c10040c00030300300080e401c02442c2003180015154580042009042000c004002845134454915101140711480c1c500003c40c10902400e0001180c031000c40d220300c514210000d009494a5040580e001040f10750144100000d5207448014240d4082001d4000c8010400b0a1068a8601c01040040c801e8041c1d00c2d40c02c0c610001402c180c4030242e11107058524100780c5030012601c08004c41c1d044480307004141d94029a0b28200650600501d440502094548010071141c4007408403140102c400d1623640990a10304008140fa05000e440c0200101e51000c1c0030348102e404c04251100d4200710030f5400e5952090340307901d0883c515402198940d400711000b0455900700f5402000094000c841d202040d810040c030140000c05640d40182098840c48207c940754a18817010b104c1040030b4682c001c250b1501b95117441c80c034641d04040c0c241240d0a04038251f400030301d1040748030b0001c2c0030320351560b50703004640d1860719 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 712358965 1250 712357715 712357729
    0x30f0209071404031103060a06211509030c05010b01050c03120c0403050a0f050d080112030c0204110307090501080a0e06072604030c02190302150a030605031506030607050c0606 78
    0x324040c0241c20b40e00302801d010180141000790700c00e21a24220401c40d01c14141050000380c0b010080c03030f0400e90140003000c0c0380d5849400c00510400908403600450400c080e420705615055a0b003180b41c40452001e043c0c0c0319a1002e5101d0081d402401415104401154544150011702c8141d030810f0011001c42501c140e1142e4002c09540d40030350410340c581d15000c0c00c0c0350701220101d0300c20390659040800c10800713119000c08103859040c461125071400b50044038203403500380001c00308216500264215565980309803145001d601c401030f02c92606039009400c0016030b009041c0490408800a19181702d90301800520f500c00c000034066a8035030f0401074800380c040921080082038a81d42011300d00d950314002c240b140d03010765901c40b840d816600512609140803c264140300030b00841c00e02c00340c0c40c1e507504500c196660110444d0f44c0c910047c02280208820f400442c0d040c00359500c000660180c0110903401000300b107040e035499441e140402d4955205a80301d4945e5608140001862450002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 712360215 1250 712358965 712358971
    0x1d040203030f0c0109080a230301030804050909150a050121080403060e0307050a2003011b2006150306070c1a1009140907080f1b06040e0f0a0b010801030f0209 70
    0x300200d091a56075071b0300289a04840c50000005410080340b96600540c0302c8850000d40c10442802c2c55541036856074900c41c4030f60301946000380605c80105503460810040e00e490800400b425244d6420485c04050180c00280301d8014165507e10900004042c0040c0b00541c155124032410f141c9495a6103190103010340c100700c0b07002404117004001c04150140304000c2524490a82000d020500020348205511103000190081c1e250000070000140b20b010448100c82c1d00d410b05101241d0440590240011a042e1413a0310b40039280c141b01500b002051411035000d801c130280c03609039441020840d940c980c03107180500041d8018071150408103070700e282035401119004400201c562074080441c190f40000c00e4a85c10511503604025800030181316003c06411940064102564100c01031540c80d81c00441000d500c0c2d000203000350302e43e511042200c00400c4c0d11040d00e400380c034044481c0d50311314004960b207808860a044009800750702c503441c05030507a039020324142c50200c80b030703024407030408002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 712361465 1250 712360215 712360237
    0x81b13153905030d230601020a03030f180501020408010c03020702100807030906060305061905090c15070b240409021c0309030506190f0c050f0c01060e0c03011d040203030f 76
    0x3514403030040b03002400240003034140840c01217010f6075149215210405800c10074510300300b00724284030050382d010515a51103034140c900032400c4102c041d060303030062074100d00482d400703191a03400d03004110042d00504101c1c0d01c501d008100040200703c00b174050b44980c21000350b202c1001401d960605001d00882da8001080745400a103003e4550340302401c844098005560a074812002c00c6100c1c05405d0350700101141400080c002c80c18490301d1650b903074003a0303c40c80d44181c6c4844502c540400035007044d1540941c019a52000904144800214480359010b1924524407d0070301c200c0903013010301601c80410385c050013070858102c10b2103d8103052240040d0072000c100c071074000040802c804004180c05109400c1c800490b070300e14514410100d030040c01d10440014245808022010b400ca025502982d07040440c0301e45da40115001c280c0101141e811104414411100703009108503d07401542c182c6100e4803981340e02c0c581220f00e404030524102c800030350542c0304202c1454210030b0100a802c4400344 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 712362715 1250 712361465 712361567
    0x90f03080403090527090d0801060309021309080408070f05010c02060d2405270609070504091e0c1b1e060204080d0801150906081b1315 60
    0x2c2d0000504c141c40548290388013601c08005d054119074094a0a5403c402c8550052545c00d140d00c10140003130030705102d40700038541d0fa80180c0c0191344600100d180080c00c0603500300302500943c43c203410945c12502a80d082803045c0c0c800400c07040340070118201034840503110b12401003656800c022103030b4002036182040c00d4a80e01c180c00c1c1c0020650a2050041007041043c1c002030601051044011800480c3d00b8a030b07805440c8000210f0544511743d800203c281c0f51a800d40d0741d49482650284103560219101a2520201640d8415000105c0c00300100d00f003000d100c050036a10b4202d454485001410310400714440c65070001414511071740d28025041541081000f00c0da44559049800a0703000da0040c3c0c0050b414002c03e81d92043e03401707024201385104d0144400d80110300920743d0a2a001d000107022104010402159000b00c0c0403411008854106a03541c0b2001c0c49541380ac0701503c190403104400700e11017850f8a008001c1c80722500420151b110990142500241c2580d2421f684042e417042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 712363965 1250 712362715 712362719
    0xd050a0e010e010c03050703020f071416170601050a0e071101060503010c051213050303150409020d080a03050108030a1413050306040f1707030e010f021f1e090f0308040309 76
    0x100c00e001c2c0340d2403074030081c00002d00004010405402e880008040404161040103145080c02189043e41c20054010880c2c84000c850311035001d28240c1d0320760701c03188a01146000040c2903104005000b519545a07403d40b1056642c400602c082003d16008842854280c1000102d40911950f242614511103c0011585554443c007084c21520101901c030000b070301c0065111300003a10044003a401903075a5a10200f42c040c2922041d07180e00000d0041d40160a5580e800003080c0c2d200d420060f04507400803d400d541054620f440320701544185422070200741000000200c024011041d21100700c1d55403070302c80b503000701844c84140c1d591001c0e4080100d0805640049580c0d20100026442a40f02d80b49402c054042820034600c0c01c2113000781d600302c801d01007109000180d88601d1010030b1507420f0a02c1c0c040c454400768141c0c00d001d02c8101d142805541e48012015410b0160050100c0d02405c0504040c40008074842d441078902903c00601003e1084402c1400240708100c580e43c810b009241c20040c182e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 712365215 1250 712363965 712363991
    0x10b0a05042d0e1b0d0209130803070314070327020a093909051201090b09061005030a0b0c031f27022a0304080a0c080c060a050d050a 59
    0x2d5540c40c41e141c00781e6030743c1404000844003000460300d4526007240141007040c4a0000a00c044440c0b0300003809103050a000c03e4005a0051240e4040c0e80d00000d004e07100c2c907044000400400c0211508548001004040388070385001e441100c2400c039070b246007280310780314a2040080401d40c11404907002907104200207002e0110784546001c48c1c580c01a10045041620000300c4c0c00842c092a86403076943c0140b04a2589410212100455070306072100c03840380c1c08125109004112030308010b017a0b40106000c105030074401240144c440c210380a801a10281c07500705156464684400042044071103030046032019825802955129000440321514221f40480444000b0455072261882d26408082208090f82c028100c15421045d50030441c01c24424120140800d00200074040800101015454001006108440c087c083d00c0c4211020440e580c82d1414201c1d41621410038540641407924000d0310301201101c805801030313501c03d42081000020403005000103071080d0102c1d80d031041c500ba000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 712366465 1250 712365215 712365281
    0xb0d02030312100f061706040b030a1109180a0206030603031902030d110306060d0e0c1806100504030f0803060d0b0f1506040b0d0203100b04030c03030e03010b0a0504 73
    0x40380100c00e090b011403c24038940441404940c124019000700079506014042d44040f000d80356140d0304108609a1f1100c00c0840e0040c06405103454241c01600c03585000d10540d2010708074402e41c261414489591040203600000c0481c0310341e070540c1c0d0045020304016140040295400520040950385408408081007000f1030b0b0110700040940c201288111003c0c01c0e03480307443c004102c0140306502e5031621800180349403007002d9018030003e5032203601c6260500204180c0c184c840300900508a034940b8941c0c4000c01040445409106001c070108003403c441c820801e5500300c0e613205002c080088142d030382d108101d0304010322282d080200030700f006020806224900d4061922190849500c2c201400c021400d041d90180182c01000200010030070b500e6900129a41c4a52114006071292545110010101000d40c00002ca20038082400300600c148203540c0301c1182d110740c441d000d004044c0c0040c942617400c0300d40c2e2954820080c010810071400c103500003442a030b05010450400342c107a240c0c50340f02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 712367715 1250 712366465 712366477
    0x608100b0301180c0801120f14030301090f0b040c050733020a11010501060f0f020304050909010b1002070b04091e052d06100e2106070e1e040b0d020303 67
    0x12101040140c044100380f244241d1304446007900c3c05209960500368140340c1107020200060058503010f055905020043d40c814504010800542c1d644c3d584d00d40d40c4002400d03041480103d00b6151060203490703454148030321900c031101921254140103554031820700c2d910199205500c0d0011106200e07280c045040c04e110015060f403540182c0341c003d60503009144104040d0f0210349685080f00521407686c01a50a1509140c14541000115402481242580103079805150040c2c3c2c1142401034421040d0041040c0c10f1003a66030f52603401c10b150301283c0c1d40907284203000212608110500111141c1c0e04030300c12090b50032000c507000c03007080b00441e000c84030700726001e00e498614510141c42400c1c02001140c11000046600100c0e0300348080040c1010440e101c0d440d040c40383d01042501191181c0c0e803030f010180d013111191100542148940b41e11135004442e9035001a0b0302d0440707410076180c02180012141c0090103465000d40750343c2c042c00000d10740e11412507030110003100c00e400180d50810081c00c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 712368965 1250 712367715 712367729
    0x40c031203060905011401020c0f280e1b1801051c051009060e0c090102150903190f05070321020c0c0a081504060c0e040c020d2003040608100b0301 65
    0x60010301c3c00740380c041224030607004040c10180700c404031052681e0000340e1007404081220072007403070140b01d00003560040c00c8000c0da0309c21020145020b040b4041c1d010881044078440c085c6860315559030115503d803911140160801040140f00c41600c0040d00c41c0070b40090328040c109940341031500203962070124104000c4800c03250f181c030100203c4800d410a01d40040c244101c0c14001da904240010740000c0c0003c085100e01d46002c1001c41c0203038802c001c20031004030100104c041504140101035100d5200c05080c415006400401a85c1e5600c99000c140c03041850317a944604062090b034003140c804444060751b40213030041c0c08202c0e850309010b10003485190307600030081110340c0c02d000c01c0c05800740d030643c4455016003004181715145080300c181c20b94040c2e4040000078610680c04026140e8080c80b60b8542e4009103000303407412030765400085140102c0c40b2600c4000c1444c51510780074255109003c0d010032127820500081100c0d50007500d00381e4001c0996031a070f40405840d4030011760f45d41c000340d11100c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 712370215 1250 712368965 712368971
    0x90803090606040c0509030c0f04180308041e030c08180a080304050328080307020f0a03090305012427020a0c0b0a02040305060c1b0f060601020c060309060609040c031203 75
    0x802d880c6072500c543c042c41c0e100390500764100404280066180d1440040d01401408000b01c00401c80c3c0d25a8092040380708220501850120030f800c0040031504115400c46007400d0b4003444103031070010305a10302072444c0c2c0b5644800440c0103940e25980d6a4000e8030740c510310030450300c80b4411599100d84a19010740411801980c86a00c4c4c001018540409031084080d24045c038041407084041c1a50301c0301c4501d0300310444556030f845410080349030130919494030444d03000d14070310f02c01007581c896116070440b401074000b4040111160410440c0c0392000c000100444500300c42004401b031407100c5c50541c00144200c0c001d07100304001e00035041c0e9010040ea07200050690f00f03403404101c4000142504901981c00450070304d42583c2c0c8055940c1005884494016004642c00c070410000200003c3c0305e00e41c5000f0f50740c40505540f0429650343c0280d4007035016000302c84841030a03040600c01e0724170440006005000310b0702c1d003e00348a402200a40203441291050744003201082c54640078151221983d40c2c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 712371465 1250 712370215 712370221
    0x9010e03060114040c1e111216020906030d0e1009031401060e0106020706021b0a1805010303030c02120403120509030307140105180c15040f06020714040e07060c02040908030906 78
    0x204032034512054805000e9140c600e00702c4c8074007600c0049404116414180b1147c03440c40f01d918900410380368504040c3d02c0c002250182c3c140780706140644a8401c5d03a524130750703880362000c05440d070791403600d401d0008070705203c440e03007510304000c41c444003442c5810000c450540f170b9220001e19034402031904d84c0d180e45542c3c2c20401d5a840c0780516005005a2000d8101c060509400a4903a640381280d550a00c1d100a2002d00f1980c400b22144000c241301020003000480340c05008000d004244410340100c1e283c089210071036800031584c03544103091080844d10789819030303441c141040c005500b40e60030800e09004044941d1030800041036124055130b004e0000441610340d06081d94401440c1e00c191070f82c074020b0a2460300000540207002c440455407840160303110030501c00c65016540c007003841c500c03000300c0029000390042040f0003501c1d82c44100c030b0100030000041c8010b641c0d281d01114115408684108041c900c07510f91110803e02c01400407488040d107803511402900181c43c03028060b0408024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 712372715 1250 712371465 712371469
    0x12120e1329040908030f040501020d38060d0e010f050f010f06140403030813020a090e10090803010e090f0a032703030e01050c07030209040f1b030b0c09010e03060114 73
    0x15070054401c084800f401005603e030f840c42c01c9030202a098604c214980000b00e420864290140c40c03042c491180b0810500203014203012a0701403c201e541912001c0c0d5100e5100c810745e0607502e0007043c001a00c114503100f03540110070001d1024900c40101c2d55680d0183c0191402c0d68040e040c010411003002c00b04a50401d0000c10f425421544620107103c4a0702950205c6c0304042d09075001c89805040403003860341d50041811004003100300c006c0d8029482c01e4042044e003a96030040354800d91041c12150580c1045900500300d40c1702c010064015141440100440c600781e1114a902040c44001d88490910030030180740b4000d09403030110301003207890340c2034a1144403400103290b14025084a00500c00d00d1074070040c1c030010014000740d0402c000054041800881080290015980034144d03212034a4641044a600001c40504a0b86016058100518800c100c224074082d6038101c0e82d00700d00e0740c90307072404280150b01c010603180c1400545107a1210680e000d0203481c0c000c1055901c420160345500301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 712373965 1250 712372715 712372781
    0x1202030f03030603060a0506030a0f0507080d030e150403120f0b09060409023f03040e010f06020c01030902040e06042024030c040b0d0b030712120e13 66
    0xc034225140d8000d00400ca0140d03000076055070800201000004e8940751100401d0601d99a010050310300c41c41d00c0c629604000001030580300302e07100c440030750302010040d40044055688400c09040c1c2039201080e504100038a081c00c01740c206220307050802d58800141d10540503100700048881901c0d542c4c40f41491242450712041c0c0c0e00c940203c5040101c0b0450f94002840c0d0203012059040c958525940c2281e200f00d010794a01c0d030420f40d201260030200c041c1100d182d03664007078050100b01131400e80c00001e880094080003419981c3d00c0e0050f203085900f160046008050301d00080c2d903c1a00da18440d10b00d000c0600c1001d00179400b8007255660041c44240c05080c5d50044049240560344111016500301c140b50b0f03841c6801e804540440340d40e0b4503507580400b050f00660708a00c003103050020b418a0300c109198041c3e440c2e20010b4081e104003a42c5c0d1011082d11590201016054000200a50900c030340304004448124200402030710560300e40e01046c404890445180c09485415161003408440c0350301 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 712375215 1250 712373965 712373983
    0xf0b1513090b01150518120f0a021206040206120c070204181a060d0b13062406050f1606060b0f07060e0304081f0609090b0601080709080304210c120203 67
    0x140729188140504c000070410711601c1240d02c074180c4c204102c1503a90391070814000d410801501210204100070707100c41d49800000e50304910500d8003188100c03d4005c0443c0d014821034006040504017010902c0c46204003000520030110000d00f004000c0041c1d40343d209007070442c103d2039001c05240f41245000e00d1901d041070395800f140c42d10030301040b09a665912580c44901d601500b031600715100c0880c94441c520080f84001c10190800e10743d0340740058a4842180c03204a00182c8681c503da9400c01510207108035014800c10301000c01807004008030b4200b660030414410b02e070015030702c2d0b610520142c590300441c1a0345012400040c603102449003d000b5040301c4070a14010f50310f01454800981c1d40c507282d640c03120407400d20600440b03c0c6003006903c104014020740f02c7c02d01201e0b00e145802881c8407000c8032118007042c41440814901842240c1200a40e481ea1000314901414015103800b020b000302200781c0c0712070303440f41c580001510b075107841c0d001494141d0109540f10964810541000162 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 712376465 1250 712375215 712375229
    0x809010504080d020903030d09050a051002070c0504090f0f060e010e1203011a1207020303011809020a05090c0714030d060e040b0a0515030f15130f0b1513090b01 71
    0x1109000c00b08040a0403035500c25200200141d80da88000042030460162540c0001c02d00e14049070710041c0203002c00e0541d08c880c03140e8280e6480689503480c0d00308901880e50040e000105410050046003020744c48a421240214601140d41a040d616500350b40c0900204940280d1980740443d0848404d00400c0f0b2011f014101030801c400580705043c855010500c52026170044049480305d55941d8281110f0020b480100b81070300d1840c0000e0003030341c2c1e6882880385100d0801100c507658025000743c400d4603c030b07960003080c40c0b04507850f00703040040f2400301814000c44404208910300c0040d42c21503082e02c142c4d4466002c1c0d5200c900c485a000c04841070b40c0e2107800421381c4481000b00103104031600707540c00310350001c0004154582c0b0300d081d420340d900943c0c000e41503c210481c415031084000bd0a81c008405c00d04e141c8429518000886032800803524001c044014441e068400030744d0080c2c800f5800f0071314003d148510070544002884084500e40220381442c1e0b2108907209118620130303000d02400d09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 712377715 1250 712376465 712376471
    0xf0705030a02092e0303090501020d0311072604030b0103020306010905071202070309090f1508010213230d030c0629010c020f06030a060806010f0506031906050d03050a080901 77
    0x41e58002c40c14445000300100c140075001410740352000b0949941826403c80e80303e14100c101e0316883c0180c00c06c03d0500034940988907000e0a14000c038464000c000759041d00050751418001c0039600c101140c6071600f64980101c3c1c01c0d00b010703501441002c000d03200650003a000c080c0c0c00d501d50300516043c098180c010307010b030301d04240412112075000721882c8001980711100603595a818281101c40c0d94650308201082402e00006120b4000079030001503000303a02c0c070300d032074030715591809101d08278030442882d20341c0d44400e01c1c000c20a4002c458504885c10002c0b1801411800003040002d551922081003180491121315045041c0441441441a081d95500e20705007182880e82222007010401c105840c104400314284030115110084036114901000d41156140e041c004103c0000d418240111a024880c60000240d107220114029040f16005051a4951b03110403900420811000610380d0700305854540004a47c6c131020340c4075005500981d1741c1504c43e1b1b0f040900800203107019040f42e0140c0c1c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 712378965 1250 712377715 712377733
    0x60c150a02070f0311120d050601110703170a030902031023010f05151201141002011a010c0c030b04060c0e040b030d050a0201060b220b0f0d051306020c0f070503 71
    0x103c40c01c0c289100c60705420a42d860038000c1174028644584044540d40103c0042503d40040c815604a140541c0b000d895940342c1d10080b01500f5590200c034480904642440d204000c61002000010303c0005d50519000c10400351640100b031501e1500d10585403001d507034001c0c0d454804e04e580400410340780da01001a4055140008001c050001c41c010f9a22a2462060309200c1c104028115025465030351a5048190396440902c1c418a40e14070206004071407000315021040d1040c4501d60000710109401541d14103160011241c0440d0703c9022030f08401c500c2c8000c0041421140c61901c80c0d03204890102d606111140002d007158043c00201e4010f90900142a619030380200d070341026080c2d54a007083c0c0f101d100000403405010305600c006105840004c0705010841c0240b441842c0c81200140650300d69900d154052081c42240e1010780c20400c24007031a045446140c100c0d94015002d003240b019150f1241e10386200b26400350340e000c0440c0d4810207160101304020722101004240071006480145 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 712380215 1250 712378965 712378973
    0x1e01260732030a0f0e070f06050a1704020f0a030803041505011d0907050a081006060e031f02070602030106031506140708030a1805150c04060c110a05060c150a0207 72
    0x40100103014a820080300191880f1540d6008002074a030140c820b100031a0240c0c0c81c0c0f61105140d000f01903107980d17010000324045000700100d0b09504501e43d038201000d40100003101d000207015004a03488000f29001a005582c1c003003481000d58080c0c02010f54905082c40c1c0545d12540746010140301c1401c0c5001041304103106140c3e9548803407141054000e41e40c46200e02410305000e42c10440d80f001e1044008a1a40c0e400103112407100a5a0340401040f40c4030741054a1560071408403607410b5000d40f07410b48203050300e800c1401e2101510a00035040050958030740c3c0c20390300240c00880c0000c2d513034001c1b112002407248240e0028150340c14505401048200510801e10400340b0162224400101042c14029039610400301d49400c44800b041010340e45c54400c0d21542408012607a11503810301081440170380c10122411224151121000f60146d50f0303490300141d04806209a0085502400040580ba0b40340108403e10229002e050311500c0f8024400c504a806464003005c607106010210000b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 712381465 1250 712380215 712380287
    0x801090605010503010905280204050114120402060a0201020c0625080c0406031802060706090210031509110d1a0a060201060f0e090f0f0610060c021e012607 69
    0x592012031b80400c03e80d5410400210509483c14080e17240c0d48a6800ea203c29000e55029106480090340c070b2440c0300c0070300c015149060060048109800b00140c0119005140c40d100400741c0d602140009414080c001110303508010040341e43e546294000ca000d03100381e207030000d400c441888140c20003000314140380e6007280803070107180502014103a488032101d440203000100c41140325030040800f66070383c181e4a8680e018046402c0d04a001e112a030b610080110701a0040502202e2500c141c2c1d08001d2410b5031080241000101e0007411410410541c01c0212050080302e480348a04103a413a0001404000d00481c140305038405811a45090000d1094250221544040300c80b8828007034803e8a4000d0128281644c90160b8240f0b4455480c103c81c0740300c0c000c16600c3c80788240401c41c0305210354500040c1d4000002d4600258031103840014203a6100c4403910601074608181741800941e401814007260300c05100407041e0221001c4002c00201d154131910703045070208042050b05070008180c10040300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 712382715 1250 712381465 712381469
    0xc030b0703090b0c03090a0510020a080f01060203070f210c05100b06030109090c0b1204020a151e140703080f07030603021e0f060f03060a1410030e030f03070807080109060501050301 80
    0x2140400000310700c3d0f61001f00a250340d01c1e0781001c181c0c0c0029840c0600c92001b50300800300311003c100104009038002c0e07200d0035082c2c102da66580245182c5000b070754600d03034103030b04261048031015641c0c2d0080c80170b604000d6014148000544400030075103c0c0341801ea161000007101070807014100f000341401c81e261035003a40e044801d503040c041502889441c00c4503141640350003030520401d011582c006090b243c43c044030f00550095a20702401034032020005804040445c0c80d001003400c01840c400c0040500741103646000301c500e0103003460613492100501c20303170040f1003c2d000141002c0c03c2c0074111076004003440c3c1002d220f040401001d803560b80030503c4400800060240e40310a1440824a5107036141020721000c0c000b02042d5403030044034042d4280f0303007081d20b61078048c0b83e1031500461f513543d0041d925030008000510307010071200015011409840c802c11115014001401031181000807100903501a00d5039868102481c541040001c02c0940140e10020f4141d042000400569030080c0451781 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 712383965 1250 712382715 712382731
    0x303091809010908030708041709010c0219080d0201020c060a060e1f0e0a060312020a03050306040b030a0f060905160b030403050d020c15011805010305071401020a0506040c030b0703090b 82
    0x8410703619100150300400840b0f5024000701d50000c2001715896120601c2da12551040e80005080004031040d0940740c0a00c03074030140420740301c00d442c20140c07521920100c022240300724480219912074150340c6c106244040e4090150390040350005005400b4400c055005203c4882048240e02e4102c1e014828100541448417000040509407110440100c2c1c1c200038110402c40c400003070800110305c01c02408503103c1596004141c1d00e000840500c0454011459a010f41c2c9280c25070721000e0801005011000c183e50303251050b5800580002c0011102e00e86950003110001100e1003103060450a001c42030107450240d031340740070051003411581c80680c2e4000b90945401ca03140d407442882c400003882040141d820a10404141c1c02d480a442c200080c1a2080c3c0e958002c0c802141c1c60b0b460054400030300004113550810b1606110542a40d00ca452646e401481154000c0d542901c81e1410640b0554047d14020108a003d100340442219240d82003c000e10302000310001c641c46e0324102c088064207482c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 712385215 1250 712383965 712384009
    0xb1507020a06033207030e150417070b0c040509010608191508101508070506160501020405090a1a0105180f063603010207080a03051b0a020a020f030309 67
    0x20b0f5940b020f01c0c030724092800214200030049a80344e0941e0101c01c1c040b200c000010741000410b0807080008180c1410020f284440710300d15454540c0c1e2841c04101205600d10040700510104001c81c0590501c0327405207841c409039070f584909140602c040442c05030059814404003400b40801070071004c59140100111400014070321560480c01e400e0030066910003030491141030f54448420900d40d1041480da0503090030b6a9a071550360b00059107031036003485842c3e44038109001c000c40c0031f081c01100001091046c00014502034403540001d203407500907144540000c1e42c851002c4494103c9010680e9000c4090a046003452860000c4040d0680005100b80c02441e180041c5081d43d21803405641c070101c80141414030080001c0c0822034600300d018a5824a44102080050941010f00c201e690310360b04070000c0b614040034103400b41c01401d005815142d8a0841d1100840200281005491011355171b6003d0258000140100440c14290f10f038107a109402c1001710500903511540d0424003641c23001018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 712386465 1250 712385215 712385231
    0x20a0807060b0303041502030324131e110406030501060e0a051309060c050706062c100807170d0905030705041e0204061e02070312031e06090b1507020a0603 69
    0x401c1c04c41c0070301e5001018040d402c8194401090f008409984100900484001c3e108030303c410b0914040c0040c2e00e85900003600851207400070015030072004404034010454402510314000800460307091034650480b010010406000c0c0b1949405001d004081038a46000d003000703810001000e020701c600c1017a00c14602102c8843c9a45065046104031f250841820400041102c0001c1c001c1e0b40502001c4803094900000820903502d40242d070154540a039003007a429601425100b08084409020400807400c280000941d502c1c08000d9200601040d1a62001c5058440620352620020451120074094100b0080c041528001490300c12210304607004285242a000c0c1041124001c40f1210030743ca0000034041080ca07007090a0700c0c0403a1004101d403140c8642d08801301d0f120b40d03041c0030060404024004a1a031184250840710f40080c1c0f0030718071800c0c00d000c10340d0442103503d1a4828202c854460715592507628080c0c50140d820500340d03481d030303151859a40c0024410107242c0070b61418181d4480003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 712387715 1250 712386465 712386469
    0x2010f031116050118060509010b0105030f34030903030506030109030f1b0f060608060105010804050304030b0c160b0f09070f05090c1c0902131b141309020415020a0807060b 76
    0x4c05841780c1741d01c6400205804545c00e041001c0c08084865031180c0d82001e0034502035501c50411244140c0e440541d504040d00c51840802003161114042240441079681403000d4190080b610b01034410b560310005000d00c0540b502505688004104070f20a9151a04440100340c2001c0c1094a01c14203180c0f10108405100d4181003600f84000c0140055450042c50702c204882c5600040945030b49070110350480c2e0340c6100440e0000030882c4d00a2094000f80410000540c0044080d5000b4803a680e034a400c00b0004040d00300007080c004025900309888000303001501c503903540a583c02c240328074046d20b021402c001403402d4508140c030895009612060015100f0a280c90556a4140201d50b260101d04401c40c1c00c2400f900e9000d0060344542e4210070511080610b501c03c41c180c20030305240044a4003c00f14007510040c018000d0541c600c07004202c460000000c400d114005000003810044e02c46060140c0b0801022200c2034020666011119000201d495002680c840c2580030502180c8840b643c40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 712388965 1250 712387715 712387721
    0x3050c07030c08160c1e0b07060209041103160f0f0203040e09030c0a050f070e1612090212070e16051b010e061e0a14061e090c0702010f0311160501 65
    0x10340603900441d0180444100300c04c1e0701105d4200c8840f01c2550104124109040c0b81d00103d902c9204100a420444e140000b0081c0d0040c02410038020300010388140d54140300340c9503600c100c0c0c0100d1a5080c400c08110244d400421418002c4010700d020000c070f6070300726006560f038800c40c0290750b0240f030309600050342d2003401c000301c0707018074264426101261114030308180c0c0c1d81035410b1700c44244c0c0100340011808540c01c0c0919845084100710003804c0d0b1150306c03000c0da1280e01a03880d02c04e1560706c1d5030411002d6243d003001d13075001059802c01050381c0c52800aa0980748135001c0c00182004800140e22511a5800070a46040303108243c030a69220100380c0c1c84900501d4201c0c0c1380c04d500e008100410140c0300c008010840c0c00b00c1000480549503440d003404d0f008640100c05e110a0803440341d4049585410030354a1050882e059100c1c1c1c084400e1442e00050007440116024031582100046480c21543d11410084103030005003421b010352812140300035458010345005607642c0442c0700240e010311800b50 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 712390215 1250 712388965 712388977
    0x1b030618071802031e150d0602130308090310110409050c0403050a030f08180616110601090902030d09060207030b190515031e060c0c011d0a050d03050c07030c08 71
    0x30080041000284100034080d410417940510168000c569a01e0a1030381808660721034201c0b041140c2c2c095aa46042202200c43c02c07609950b820780c00d0040002166400ca11500510b00401000d610380c00c11408240c5041c0072081c041020700e0803e50310100d00c0612805031401d032854a40c001c6110b584400020045010301c2d403010b801d51080480342c0c000e06030400c03281c0d00d18006959410420b80c2d25201c2c008441601e020310300e14641d2012002170301551400450002c200810b141004410f032031501840c3c6004402c1e00032000d050342e00c0c440c131001c600e0308212010b10792140c7e04080c0852441d200f00a910b42d0b000d80b00180c01440c0c0400020175140c1030f10b400301c403000f940d00c4003001182807041c00c4e841043d40784025580a4412640b10b050203a850f62112039035407045000034407440d80c89410303504854000d4840060b0035904e614070303004040743c0e0004644040c030403407004040c10961800d01c9840c020107001c0120906d842c0c1030500541c2c46960044034420b036018100000741202c0ba02d400c15551080c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 712391465 1250 712390215 712390229
    0x10c020315070207170d23040305071d0421020a0b01140909120d0216143406030c0c020a17061006050a1107030c03030e031b03061807 59
    0x41c20036007400c007400c0090240556500b2224040d449040401013110042d00141c6640d010400001e101d030b101d1400390f800481c0f5810f86131421100c0a500e000c240c0c001d50001c80300c0c2c0e008810148031a807043c411500c0e030248a95040c800e01e040c80c2d155001055810a00602245001c12003049054020040c00c68180d07440381c0300310201e60751200c1260400380050b000a100e0500c120115004131f000040b041840e806103480f0311700e050f540c00c03040e000030360241c0b10b241c000c00101400b01002c100003600302c1281d050384001429607004070b81164084416100010710014100801e04000780c0d9055601d501503c140382000030b0102d503400c505030361028507140c0095000d000990701203044252600000c9860040700210345181c0c407802148aa00b090f1030282c031001520601c900940d6500c141c200c44009081c44c4150b443c0c2c0c948035100d6129803031490b0010380220318807111200281c201003101880300d8100044807200c0d59030180c0029150940600500e0512046040d01000b141c01444520020654 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 712392715 1250 712391465 712391473
    0xd05070f0308071103151302030f0109110a061e0e2e020c090105030c210609031b0303040f030e030c04020c0d11070f030605040320010902030f031c0902010c0203 71
    0x81d074034242d80140e203c0381085a208092450201050030300142640020712040c541300f400d96644040d503101c03002401d1060343e061060f1810002254000c1c421004400c6c094000b131000c01d0414000e00000b000c507944a82d042203180109807008000c42c01c0300d1001e01041c0e02d0302d0700b4202d0000740041c0c02e41c00d01d8130782c44841c0f0017100031520800442042c0c0c0000c1540d075070203617010604650108800c1da00b091040a416030000c10b050003d62070b2220401035814061a42c08880d0001c680b09140751110031202d0301e00c05d41c030000f103154406440d03e45102100200400551552030560781d050400180e40d00010148000d6a5a9180b40c0c0e80030312000380044c0c0302501c03c6454200c0d40c40d529955440840905010600704605065007040c0412540c0603a801c2c11016408107255943e00001407800400a90820149401d0600d44421245400c0304030840a00086071100083c01018101300c200c918010041d8420040041a0300052040b014074281e65400040c1e0340c1e1180c00141d845241c1020020b5140c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 712393965 1250 712392715 712392719
    0x121d0601230a030210031509150504050106020d0305190f06140f01021207050c120d0908060105010c111903140f0c01080609040224040303030f02070309050d05070f 72
    0x100029a1604a9030664105005400c9096441e50040036101038541c10a84815003030000d4180440b0801d00241c07540740000341d1714401450316505e81030030b40041124039120035083d15102d0407024442d000d808111005c100075454424080c1d03680c124841ca42041c9034071140041c5100079074120b5081034450141042c8904e04100e18280d000b41100e000d001200003540003850341c13134104261071414050043e00289040800180c54003002d41100c007045816115070500004551034401d150154040c4d00d000411506640d010003418038044c58200001d19444000100003a030783c014428070025401940052108804501203505c158500303071825a002c2d50720303500004000f0303134580d4200449071a5055580a05001c40c99076141c620074154be500180c1804080790300d5241610300d182c0c100c1c2c40249509104504d08a0f212a103509038451820321020121b010414990180941200c40103000c204500e8546140d40151184011f030041c107019112400c06042081070402c0844007805624040144d01c0d5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 712395215 1250 712393965 712394021
    0x220209071709030c032b02070b0603010b03012a0201020c070f1a1204060509030903010501030b09160521030c10090606081902120a1a0103111206010612 67
    0x40d1484650a0401810700005030949a0100035140c0000c0c11034051450b103143c6407280001d9a049030070804185008891854600b840c910040501138811142c000703440c5031075420142198031811403a8020703418207860b035001c00b03200c4e20003060b048111a0701e504207620b0040700302c0c024020000400050302c0782410110346040b6035030801d8215101c072409001d640c132040c0d5114080c0d0154a9120034450802404100003602c2c0d5000b4640c000c0e8564110380c14100c040340000d0035a9401c3c2d1003940c8220f103030b40601007544c00a02c101d5800100100b0f400002d00d152402160103403003065042c00494040c0742c03034403220075414001c07280340d240c00804881d2003941c0e4100d450010011044d080351583d161500c00034107468041141c41d41c2c5194000c611310740d01034580a04c8a828207014052034180201080c140000c1c0c81c0d60608085103140204d500703070035811072806000e600e00443d100b0b4491880306420f1040107100003000c0381582e40a2500e0311900017140464005001880382d032012100c12401c55030051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 712396465 1250 712395215 712395227
    0x406090b0a05010c0b010b160206031e1509040b0402040209122a0d11012313050d0803160c020d0303140105010306080a080702030313270b0922020907 66
    0x203000896010740c4203642c400c0192981060b010005210404040c01085044201c501401340c011400001c0c09410300154009043c0381d004036212050038103c00201c01c0914481141c1c2a40308160100b902c40740090305c00002ea11990041000b0054444200040c1c00c5494640680d8110507020b03004506800031118402e4030b40c02c10700d40ca02a1618528010310006082180701c1856080151101c1c0283c289034a869040c5201d90407000e0500658180b40068041028884841400050050764607401504400d62411151703a101e1132203000c1e007900003004110202d080b2504a09411910030701c2d03600c0581d05554100c0c107114043d50100c0c41010714828550190401960b10038030048804030b41e81c031030340190b0441d101401180c01c5607201d0088800041d41c03420040c079a4500050889007040800c40140348c0d10b0400b42c1001003040d29003d00300381c03002d4444102806401e803010080c020550b00f8404501d000b00000c02e00603a04d040c01c90102c84160045450502c85034016203461703c903140541004e088 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 712397715 1250 712396465 712396481
    0xb0c0721020c041808031015050c0708160b1303050111030405060a05010305030d090303021c0e060708071205060f041103160503010b0f0a0219050d03060501050c06061509040609 78
    0x540102040b10845140a10400c86600307442c1810610b90741540e12144020707040113003003403d0342c42844c5000c28440d12020540d075010021350390f1542e590000042503814100e4a90180c58141c2c0a480c0f2030b0107601100141c0c80c117030f030700b0440704588070703400600d810308052595800600b01c1d5280c03038003004a840b81070008500c030b14001d20443e0810b4541c0c884190849801744009060b80d0003d000c1100407484a80086082c0c41c02460003608140e1071aa801d0b0301100051000e640c015580c6010f14491a0140b000f250f000314641030084080c81c0880000d881340d08200080c00006594100103410b640d10112410351880003d8400c012138000140b5402447d44142c940c141040b800d00c42c1171407054400d00459043c1d44255090a05001004a202d40507404c5100520158022600000c883e4034148649148040c01040104110030204030003030100d890541101d03040110401c148a000c070000a03016030440c41c1554801900b0044a10001c020b01a240c191984541007050004070b400e51074201000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 712398965 1250 712397715 712397717
    0x260c0702041a030a1101200604050d050313020d061e0e06240f0102010b1023211b0c0a05010b04140412050403060c020f010e0106060c0b0c0721 63
    0x2c01c00c800b070080c407000403148a52180d8181c1c04100e424000a0041d0521101000d060600c00200140600b10101c822a40c440b1200a41c0c051420081400001c00129070203485e036003405840e44c10543e6221020620309440a8040c40880c181c100401c5520703407221200b580610400041c20001c902c40d00042c0600200500c9036104800c0411001c42c03260155134490694881c012031000e403d00c05002d102049001a141035540e100c0c03c2c0880c43c0c0b2664140a060390603a5505400404d19450381010f203e40c00c12146034182060014140400c1d501e000103104469841402526548081104040588401c010f04100d17030b01207802c81d189c003000541c0514a5100c0c100a00041c041c6030184800c80d0100403e404c00b00748a140801c0c0400e0801004941525552034030a10701500c03074550405603015801941c0040e440070203103441400f000e00c61481040240e400038010301c0d2070f100b001032100710b1540029003550b520101080180e0501c1c1c0c04c40b507c0c04c0d8031401d440d0b00488e038602113031001600f400c8650 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 712400215 1250 712398965 712398971
    0x30803070e0f030105090a2a081f06030b060103051506040f0317030601080412030603020612040201030c0e1516060e010203090601060e100c020301091401050106020c1807260c070204 80
    0xc11624040c01172900c525256001071030748420507100c084007014410505294040a40291406050403666040140c6258002055004400c244160b605520500d1080c0581d2400d01c091002460340c0c041503030820024a80400c603031312201350441c40380100c1202c0561200000900046017410303014414100ea021300486080007202040a403da4442129080d0000b040c1200080011b00a207101090038185807400081c825141c2d80400c015900c01214018142500c008000441da89409040c217041d58601d0705483c2d00b0201000b080b921104c0071043c000c01d080200c1e01c0d0903c0619040720f04c0c4403540008080c05004204000309000b90720640e40503c0e64041d000002c20281e01402d201d5031b003100090310412007510101001c883c28589017030f040b0b03419525091700c200030800030542040105044000004d15514046c1d001e0b28000000800c64003c440e1307503400e05a140b5241c10919405907050801c012002025592000681100442e5410740c825803000d110182440401034000a0b100b92010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 712401465 1250 712400215 712400239
    0x2101a0103203004060204050f060a0c03030e151f061107051003020715052502030904091e06060e06040204080309011404180b030105070531030803070e 67
    0xc01c10041484401540c2000300141c1c07928104000200442184410342010f0208034002c0c0140200b40a5500350341310340d0040f80602580c9003603116032029020480340390f4504643d0300005401d0142202c00075061550340c8403840c101e08001d119039082d104a2542072403442c0350469007010844041c4800310304001c4c03406400320b102d82c042ca400030b440424040052808074901800c0065420311952402c04258003441080001120511001c80c101d440c0c050200f41440c00e0b01000030102e200041d0040c3d09003144040200c10354021040310304201c803e032000704a0307140c1303400c081120812100c9104403104024030050700303100f550340c89401650800003005032251180005c00059001c2d6025442c45a0010420119150f00904007910b86025404c0700500300742d9a9189803151003190b40d40414002c1c0c42c0c0106000e0b515082c81804c0e80300c030150030074030706200f600610300c2c0ba12072501d8200a9050800080000360000600c422001964400612952450003007001014404899480c03400741c2844a20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 712402715 1250 712401465 712401491
    0x16020f040b031f180b0103080c070504060303020a11030c36040c0602070806070906050a020a1203090203011104032102030d09112d0d0213060b130b03100e040302101a0103 75
    0x1040c520b0940017203584010307900303548403a5030355848100144043e2082c082c0009458855000c0c0c00d00440c0260003404050383c0a0901c0d04400c0f05c02c10031144207401c046c0c103200c45a5240007109145585100082c01c105940c6d00c200c100461000011102402a59040004103d40301c84c001d0146c440c1a420344074600d40e03420529030303516020740f41c150200b00c405006000ca18803d00181030150070501c110b0b4441c030b02c0d80d20f0701c0050613540021503000a45480c000c2d419814240a42c00c0b10000110302c0c80d15061660b100e503081006a2040003000b4400d200452560038820010b442c1000315071201004030003240d203015840d6090090b2441e00035403650854200130181c806446004d100020166154602071104001c00400d9801c0c041360b0001c41c96800781c00010042c4600f5016081c40c801c4240d441205824401020078584d0200100303003410002c21410006074503004c03003220301d1202d80d89a2610382c3d2600743d00741103000c04059081072610110114002100d0048212100b081e2410007000c504500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 712403965 1250 712402715 712402751
    0xa08010204050616110a0329010b0906070f0c0f0303120509070620060f07032f070201030902091501030f150b070c15051306030216020f040b031f 64
    0x11800b43c0c00071060081080c00c0a80400c80a0001e114800104400700e600300018801d40031500241d5540c6050305c01c3d00381d03005008080455000e02ca11000e030760f80d807519441c0c03c1648200c002071400b0b1140400c025017000301040038080700c41c0d031158200541e951100f20701140322a11784403d03400268a1118468000c04601c1900d0261200c4400741caaa1403e01e0001e0340c40b05100f0b4041c010f0040001050302a4000074000d890040d114081c000740c16040c45200101070b81e02d803d030070001c0310b01000901610107242c500000700104941d000301d03031a0741c40c03400140c004004420b4041d402103000c10802290381d00480300c0b0361000c0800d0704c08204115039800e95130103d5010700d0b40000283d0901d80d06009014440c40075000442c0704402441c806a1100c2c80c0325110b0301214407100100701e0228a41028141807189107000c0c000a240071800c200002c00c40c01c400010041d80030f80940641c82c2d00308116200c0c0d40241142910140880d800031200c2c4d66071030002e04040d607840260502c0c00c000b2025101440b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 712405215 1250 712403965 712403969
    0x212010f050904170d0e060901050108030309071401051905030a1103090a030302030a150e07091a03060415090c0203070c140d080a030e011406101e050c010f060b090a08010204 77
    0x10b404048166607a41e00c071805454040181582c4500902030082010b039035008040304104150050282c070b06003503201d507080d51410b802401180d0024020003202e110b002500604441c141c100e8000001544001070f500c40c41505840035100091590705038949411000645c05200c1c1958200f0030b54840c04102011404256a4114240c00031000000402d10903000b464108002c0240021580701e030802e600c5110003168040c0c028060b1000030030484940100b91a0000d01d842c817855010310301126800c0d00980b2001384100d22450341e9a19150100c10300040400c0a0088443d041062520441c80070b0f5494120075821941010b6846010070780350041c00182c1c0710f50138040e1a04d501e00c400343c0d176240500e401540490041507a50000307400c444200b4001c0240c0701c041c40b070b5824039a04004050000740c1c200b5181140034030980598035002c0359001c1d28034500402c018902141c840d040020b500b809000d85061001c8600d04120011a51920400050052090403181030396603a40d1684801d090303000724 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 712406465 1250 712405215 712405219
    0x30708090a020a090f0b13050108070801150510110105042004020906030705071703070f0e060703021b01051e0a1106040512070c050616030306120203101d07090212010f05 75
    0x3d03103410401040c044e00b0401966840d4a40419080c800c5004074890280700c1c05030b01c1486440310010048418103010f0017014100c00b40003401403008070014643ca0404a2003a58055602c075642c4152040c0300d81c040302c0319011040000d02860802d030614190000710703010000c201d90800c954440c101c0ca0284201c40300010040c02490031503480720011b0310340d0b401402054550300c2201ca000d00441908100461203a0002d44424125140c0094020128000002d004e80110402c110240100f81c000421030045104040c1c600781c000ea8010040b66140510310480714050040e0000d40d400b13074901e0001e409201c80b103503a40c105072092151001d65808055802609a81281040b40100788928000303004607402600c03861903050762040442d0140d8820f001221507c903e108401042592602881e4001d10020f40310021580c03a6800080c0c41c2c2041085880d03c51365168003210fa107200c00c040e840c040108200c151203003d40c1e40c80e00b45000e548017000134802004017000200340706117203c00701e106407000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 712407715 1250 712406465 712406479
    0x7110f06211f08010212070518090403030e0304062d1202070f02090a0c110715080901060807030c0e0901063204020319050a020f0a05070c08060c030708090a02 70
    0x1410541019001a010740c82d4001d0010000c0011045059400014070210000581da611101450401c04a000d4899010441c0802c103005100da414180c01246450032100a5101c0c0c49515050b4010400700b16084803902001c01c0025016400c17002c824168000034458000000700990780d03e8401152048502c0401c1d015001c520003008d4640c0070b0012184200060b00001d9002c1d000214008000c81f951002151507410402c18181c1c8501c0d012414403404000f0070749103050100351030800d41d02e00025030411158200040f0482d4094000c403006095010548083e680c0380d0508000c0c01303c3c01d00800c0000c00b6140d010500f212814481c800803100c01c0c80240a580000420405030b05420030b1240801705140c101811843d551880210b004000040b4130042c00001d0305000819220300a0070101410300c140000351003101c1071011a40c48404901c0c1c469a518030502d8010716076081d5030441c0456128002c2004100b038001c00085001f14026100d01c201aa140d0a080c1c0e950940440000c2d00210 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 712408965 1250 712407715 712407757
    0x605061303120e060316021c0806010507020109050607050c09090318010f020a060e0c12070f12151410090b010e01031d060a1d280f050307110f06 64
    0x301042d0544007840051030040183c2c504440015a5908280d44240c29103080021503c8102c0c0c0400420328207450040700e01d4040401c1070000f0300810300042c44a8180480001e0204c00c5a20400c4550040d200040800341c44200c903040082c4d075203031007507400b9010f045005c002c98900b40000007611840b96800d039544000c501031400440e41000c05030484025441480c1820001481c1c40c00341503000d60b0300c80020107290b2924801c0084451a15007580d07915006101e061040b421012281e2003514019050540384c0000c078034101c40c40065504107046802d24090009402c010102e451034065075161156040d05525000340c90211103100d8901408203103034a800c3d00319035009400042c904601d0b518440d4010942c0480c890811600312600c00409a690085c40004649032000b070205105001c000c11004000864603941924509600d0b114200c00c80d88070420454541d283c440e00a600c202500d84038421031a0014a440052100318400d07030380d50501d0344090500ca025501052144020030500c84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 712410071 1106 712408965 712408973
    0x3031a1206090705120601141c030203040e0c09061801230405030d02010c0c0f020604050a14030609010203090d05030405071e180603020a060e030c041a040605061303 73
    0x11711701c40c2104010600003e64075041d140400c54601e100d4941d480003511464036091030351100c00e150004401051741c0032025000b02e071219a5850300b103844900e0051802d00400d200d0079003042040c813450302a80501c421461042006040c810b51102565241e851a010a025120b0075a0400a0f042049007010400100d0703220562000300030b141c480c0540203100e00c84401015141a40070314001e41550741c0c1030111001408014030542000d69110a84030180c1e4036140401d200c0d000706000100140018021030b441401108060616002e0301101520660005002520079102d17840b030205070040000e45401d80143c405140001251600250901e081c0a000000a00ca0b061a03030410040e2184680300c02500c401e8200b640388808450086880d24113800d0303c00e68010b060990070494105803c15144480606507418001141c0b264140851403080c000d0030260b2410340b042c10000b00d = true := by decide +kernel

theorem cover : BRFrame.Cov 712230215 712410071 := by
  have h0 := BRFrame.cov_init 712230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 712230215 ≤ n) (h2 : n < 712410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
