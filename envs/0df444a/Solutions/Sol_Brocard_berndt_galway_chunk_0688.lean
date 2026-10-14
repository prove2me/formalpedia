-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0688
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:09:25.913985+00:00
-- url     : https://prove2.me/submissions/1bec5006-aa46-47f1-b0c6-f9518710e4ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 123561151 ≤ n < 123741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 123562401 1250 123561151 123561157
    0x9060d0201030f0509030a030e190312090c06050c010e07060e040b0f030607050301080d0c020a05040225050d030b03012a020703051501180b0102060c0a0e0406290406020706080c 78
    0x2c510f0309103050144244030002100808000f8020348060000c4d0841ca40c1280d84c440880400203c3c030710000d408040068030900c02d03081c1c80801142c008c81c0300c80e240e444415aa9149511010200e180022051543e000070700400000c424203001038444103140000103001c1e1221089101c1c4200d40d280800d01c50f5940383c160380c1982c19005000c9038518607081d072014085510a00601d80705104035248186014400d0120800507030f40039100c00203451900c1c0501c03029412828811302e0145012040e458140c0c0c0c110b542d8800f2074090402080c82d404840300280031a039003406040e009904062100d0745c0f00040d8003c0c032620200361880c02080c80c0c0c07002412401c18040350030081840c041e008007450040c2148112505070b03941c1003070307000c100e080507141601190001c1c1328582c09a0801c1000480c0c0c50f181d04058201c1c402e403410310325040540580040d04565503500440c80910030300c00c070900452041850610200c1c2000f03005440d041c10032074065a42c0c0c4081c0700b8441080b0321100081c070315010340019 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 123563651 1250 123562401 123562421
    0x1030b09190e0f010c08060a0b070f14100b0907091d060a030506070302191b110f13060306060b2104020301020d051816140111030903031c0b0f09060d020103 69
    0x50301d502000c141c3c2c45a01030040341015a0015014074040360003443d0560300d1008441c3c401d82d54606c3e015041c0e5800c60b132540c108400355a256107003601e401001d0b40074011558500354075103001170039161700020440145030250003e000c01940c181d040c4030001000e400d041c00404180e1441380c0300d030345603070019038841c42c1600014010302460041c8560560540c002c0c0c1603019000000c210752124a0404545101080402002c0d210b0356840b04c40105c1c18045030701d944d00c000640109030070a07180b0003286040c6d00301c40c144006917503a02003c0050103128030940002e80001d04555243c036070192a0140100462030910303c1c0141d40201260031580c007541141d10305444501c0034009480c140006840d4021258800e001a0190f001c000711580d11507404e46040d02e010028103080742000c5001190022122180351440c0d100400c0361074000d65041002c2c002600b0503803903003058554007040801c19030302200f4905000e41002c1c1e200500d41e0f640c81c1f6045900c070009a90b5502c07907000ba400121b0241071400340c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 123564901 1250 123563651 123563653
    0x504050f03190c090c08060d0303051b19020609060103030509010f12060909050c0102010902031c0903020d061d0106030308061509120c010e06030402030a11061e0a090501030b09190e 80
    0x124001086800c1000310300715803200303008100355045c1ca2400d0f138850b41c0440c0c0d459840741201e075056000900940c022604025200910201c00305150490002c5a2000c80d141b2940d1810f8101143d009504001c0664007810340d1024003081d52465502070040e00a082030030781030107818200c40200500c03580080581810664040c0089592030b140d07540100b00189054942d0b0241041b000419401401841030035980030300241040c924603029041c4039003040740e01d07200308040c2020000251b9182c030b4aa0180030b02a0100003034084c00b040b2200850101001c030081c0a03414254100007080d04450340590000055811a18022010324080b40754840e0342030b01135002405440f507007130310003001605000c059020f8a45d10200d0103502c041003032078002114001d50540c0090402000a222201c0710119050301925980c100500030184800681da41720303050040c0c8a020400c40702080d4800f820170010502800c0800408580c100440e48901c8001d169101e52220040c801e042c0204c0c5500003010088584 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 123566151 1250 123564901 123564943
    0x3040302030c0a0f03030b0609090105060903010e0f03030a0b15030403030203070507050d08072316031b03031b030c1205041104021204060f0c020a0615030b010608060108090d0504050f03 82
    0x126013840c41c400b800c03000340c0010b803400b8210310f1207040c5441102d410982c000d04207240f50303181504000c0140d2000c680c154141d502d6901d0840d16040410000c0104400c11000d1500c1e8074003032000201300c400c490081482480d600c102e509110325800100e0760003036058a0003607542c0e43c0d10700c1c09640d01c0c80f4028000303246100e540ca0300c0c0c1d071881c1c6c054030340b60180f202d541e1139401c81d07030841340b854429400031000d000f12a02d0822045034418050314400d100588a400e00e1070050028610024007814040b5040d0003094a407a18401d1030b42c0303444000004d684882c00c04101074070250070024110b00c000020444420b90b1440804d00740b02c0126124111210001c105541e901003150b1101188501034804030381c03150500c5c2c1c03508103071033441c080c0b02d091040c268000c01003c044c4c0e84400018040c0d490311030401003101c280c00b00102d032040c46440d000c3c0847c3e88865459090030400100814002020b03a090754203c01003000c10198404c04640840c2d0007210318013100146240000e042408801035030314034020399 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 123567401 1250 123566151 123566153
    0x70309030c031b0812161a10061e0f0804050c04050702100e0f0a030503100305010603030306050f040c021b0105040b03070c0212011104050607062c0c03120d0203040302030c0a 77
    0x75a048036018101040c2c40c80386640ea0b812076660350045c0503c491030070014810700d900c0500c00302151200a000e4114448040c20100414031520701c107840640071840c0708081401555044042d03020421032042000c0540c0403c0c031b01c01809040d40014900410000c100401c09020042040380030101006000300601d0421443c060356903a150358041419509040d200c09481d038002c50455045018540030740580001550111802e0740000d00145464584000c04808214240f01e8040958840e48000541d1410f00041010b11410107000c140304030b0804220303400856000c5614094404081d03a0300c00c2d07545400c001030358940074640080e440c0e0305012003008102c90b4042c02d0381d240d01d4003c0d182c001444203801c00f00c40c00d132040c0d4801500c000400704401c00c01414500300070810640503150018550115648441d0115503c0b101c54805900b030f8542c100182c2c1c2c060144c110388100072002000c0c61200c44140400c02e025202c50205001d03808400102414028001c440c440c240a405942da60041e17 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 123568651 1250 123567401 123567413
    0x9050703020c010f0501050a081912021006030609110d050c01050f0903060f1030030c0501050703050411180402040f090c17010614091308090a0b03041202030a0c0602070309030c03 79
    0x344921f42c800e82d4070a0000a0803107000c14040516403a0388102c0c0b8a4441030740b615042002c2d1101e0201c11072041c00c1003080081c600d44a9400030b1403081c1c202050030050b0b8100402003114925800d40700d5070740075070024006603000510160419003801d00315216403001e460301065002e03140600d5058011401008403044034507400d18441c00c810310001c802141c4403451808502d003070318142c1450501001d55001d110b1060b48052400520a10307000f0081c0d40700380e4030ac0b406e5800550350718020a440d60144801c00960f8101208480c50540d982a410039803201c0c0c2c0d4110b46005800680a15a500403101048105420640056030042030b089407032075441a048624850114800c4515440c16001103052182c0340c0301e890350313090000c5c014409511407094000d004200c044007140d40c0c1c401000448104c1e10b84103103210040c00b0307035100c107600c0703103410304000d00b0070f1820310300380030454104001d040b00c9603811011011010360400e00c01610740082d8541500c0984160b00050b1585500060020070810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 123569901 1250 123568651 123568661
    0x1104180b0106030b0105120603070902040605030702060711120928061103030601090302010f09031b1a0301030305031b070204050411190510030e0c120a02011103120109050703020c010f 81
    0x2200e045106280e030380e1500102c0c21030390341250180c00503904020000d100f0210440280d00030800038266648140d68258000480c0e00a038400404034a022007002117060f018032800341c1c001510b0802d003a83c0c1b03103000b90890703d9801143c10301e444c0d000040307200d00b0030781c40e281d245508210250001020245039900f121803c0405441014005075607044003002591b00030050341c2c000d90f01a16501c001605540c015524440c3c00402c000801c4001600000422142c0c03000700b218800e09014100000d00300340603104000700000911181d81d20800040000072340c0402140e43c009c620386030106031515007029903ca00d114540029512604210612080c090402181403014204440700d00580382001c50002006602d4400d00e07a119170007100d0f004150380070350802c1c4229a00c490a4440b0791550000040031520010101c9a40b43d2184440d80c0855802071503400141d404031004500b80749a401c068002410140204004162518081000103000c0d03016a044002c000d80240701c4031007607542e80300c0100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 123571151 1250 123569901 123569903
    0x603020c0109020a08151003020303030f091f0c0f0207080601060c0804090519180c090f06170706020105070221070f0b241002060a021602061b010f0b06090d110418 72
    0x710b046c502144c40890059044070403070303a0203409941150f807400343c90040c21b44010100d034100e00405038541024444c951910f04400b49100000034520403500f030050091290b0b21b01803040d0f501050092091600c001003240c116407075480c3c004200d240310f1070004518003442d801202001d0600c4c062009a14841100c0b400300c42ea000010040191543d2040d00f19100700070010700701030b0001d01c0c00d0008070100d130000b03441c00c12103540118003196500518001c0808280345600316803c1151300380075490b030a0203a1a00203920b0300c02051a00b110000141c2445910160541c480b100050880208041c00881e03200f1b45070801483ca102c1c0c94960f00d941d03100f0418186011919205883c0041c0d24900100e101c104164517034007c029540c0d410314144020344c00301442c1902c03585540c214900582d139590040c00c1e80110200d03c03218050482e40c4c400c0c00d42c1c0d40310b200c00c0c94442c242410005030391244070503126240d504450380070070120f0904190006c04000412107800c1400c01d145540b95254044030042c1107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 123572401 1250 123571151 123571183
    0x50702060d232802041401080601031808120603070f18110324090903121306061805010801050103020117180102041203080a0204120b0a0608100b01030e06100603020c0109020a08 78
    0x44860160f03844201e100343d005680f0f10625034106500294807034440c05078820010304000800f03503401035000340c0d503507101c1c48101c5007648006402c2c0710f581c2c881c06402c4d401c41002c1e00203201940c18811000c40f80400c038010100c640351030403281440c44555030805040710385510502942ca040690341071088440301e8404070fa503c2d034074516591460502d00c50700d88c0f16203466006103042c18040030444801480c050320078070403100c0003802c103404a081031203100024250007002c00060801440b014054850590007508a40d250000410141c1d800080c5020780c084007040c400351079036841c0003807000f02c2c1c400020300b40150700c081408610060407840301d000c0c450190b100c4076101c0d40c4032006041079200d140181d4803a0f00b450301c2c07d00e000901981c2c0107a08024030301c1d004a4002d44803848107160503c10144800044d4640c003004919507090f00c1104007aa51200280c8000d14080f003140441e010f1512500c420075a00280c04c07081d6800a502079690a0750003840c08140395a91640c0a65401110f071740c805107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 123573651 1250 123572401 123572461
    0x70903030e030a05120901090f060e0a0906120b040203010e331017030c0303070e1c03141e0d06081203070915050d150312050702060d23 60
    0x46403030001182d00450b80e10500030001a007000c040c1d003291b60030006a172810b0003a88140400e40c80d07541519003001e0000350752143d4001d00c040c0104210b098469001c650a1407402c00188414525020f018000315000b200000e007640705c5102290044c400450703070a10a010740b01c01e03003804010084540764180080d40412900340447c03180412881820740c0e00800759010301380c04004948040f09804051580081560b0070f009030031710303070600b15401203403200d001500311a0b11300078500d402e800740401c425080002180e5043c0c66600600b0180c2c1c0c2010041d04101c02050107101a12509400c14000e04541d03201c6803580e03403070b90040000c0d10050041c11107901900b1108943c2e03000d800b041da8811140c50795110781e1503162a4071000801111b4a0b20010031008200d003a006031124006c08000c01032802c440160340d45036041014040c1c41c0000c2d40401c0000c20855080540e07904411382c1e0907012403800000e0700400d8107000c50103000d400c605604001d43ca0b102000040c045140d0000260404d241c40c00e52 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 123574901 1250 123573651 123573677
    0x20f0d0c05030f010e0705090c0f040e1b0901020307021210090605040b0915040f031205091501050604060c060b0604051009140906100302030702010e190501060509010f1203051207090303 82
    0x200b030726803440d0b117901140c0c0040b20401c0395207018031400e41c1000d5180e454078988011000b11401c2c5501c241c000c04d1050020324180f04000140c0c0e03944440b0051048a078900308070008000030f4403803240d0b11010b0b21544172100d04a0702c42c3c4040c08040301908603640f0400c40e400d214948000600812202500e241034240c000030650310003c9405107000044400c00c1d00c6541e941c2d81c0701b8103401d8000109900300490a8041c09891109100b01c03401608050f004080101c480300d40320500c032005030051401910f007070104005858014500900307a59100002090701203104022030614001e50303008a5001c82000341d14909660046044001c1c1e94004441809290b1082c00f80404c40000307851190300700c0b0103200c80a10240c0f299000c0c54025a442c0700100300c2500105405207001d4840b14111409002c1070514001c1220034071880006100548100005624008000708030345141e104609102e01d06482e28020144600120781c0e00b051400d000041a08045030001c03c802d1440c00201c000c203009021002c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 123576151 1250 123574901 123574903
    0x1020708010e0a1a160c080403291803030601030209180a0b120c010509010e01170f0a1505030a02090408130f0501080703051014010c06110309070609030b0c07020f0d0c05030f 77
    0xa10460020345c0342c618141118070b003103d9007061040b00b614542d809000200015110706101001014a030020b100d07480174900458108000182407076100c042050164106c0000c0801a00ea019409080058803180303000c0114203010f8440d224101c552003107004018051500341c2c001e481c9240295980c4080700780308900361f41d4400c90310a000340810b1090100310825031094521500d01c2d02d0601d07040010903200307940e4003500b14040d1076028101c0f102c141007240b07481c218494400514130310006031100394500804a5100c03028139074080e001d4403c0c00001414803a2a200300d51660f01c5900000d030165a4698003a8103410184c06004e00094403a408201c20900c03038003510740141b8150200455051418441d0481840c25032007032818070904c50481000724090344108584681512040c6039640780c40f003001414040c2c00d400900900040710303418804070310700030750b1194005d1724081c2d640e0340d52005000281100d8041e420055100c6184d011050401103902280003c481044c0c0c100c80000014030046 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 123577401 1250 123576151 123576203
    0x90f0c0819050612030706050609060315011e0506030c0a0806060f09040b210708010b0303131802070c03030201020a032a030b0d0804080d090807060f03020901020708010e0a 76
    0xa4071040ca4078000c5207020000707030342c04590001c00040644100ca444e03c501d1504540119405941003540d6008000341400e141d5903042e07108000301c0c00340100d002c6002c500c6030143c0c0306002d20442009140e501d01c5442203400314040190070000c00454aa103010505841142d018030f400d4000208d0010110b09903042a0f81034170300d404080c9101c9030a020b070b650140070003050590005980038030002c01040481c1d0040007810200d082c19030180403a00d080c01d40080c2501c8444552a0090344104810600d2402019059090b0b441c00c03400094800c0c030001e445006801150405051600c2d819000410150158018406030b0410345040c046100c800b1000100d0701420040034041e000d000c44075020329442603014203808500201000440700d16503d0ba80001d0700039400c0001980c3c00059000103890f004114640104911801002202d00302500241018801250718007499000b15803c4480d82c020311249010300a40402001a403000d14080d50f40c50f5644001030300c4800710b050034100f40c2d005c48162 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 123578651 1250 123577401 123577411
    0x60801020315041505100c06110a02030901050309010905071d090a050309061303080409020417010e0307020f01020c100306231807090b07031d01020f0a0b0a0e0304090f0c08 76
    0x310003008020035083c8006803645421001c3d0469400c080030900c0d69401744035041806040e920a04140c1591506408403244d2100301988040c0a010103800243d000084030f11045007864220303102d40300c0c044801d0140c54040402020340c09102e5010403101c40c1d541041c40e0500307030084c9032030250325041c08807501c900c001c1c80f000e4425002000034000c2c031300b13000c0020003003a8402a14001e80d05d81c1da44584d070090b0025003201501a4000070100318101c903001c0c04807800311081c4001c1056861560b09240c1d0392181c03a4000740641c0741d125064081d81e00074003401d0800b41c00603218007051244500028002c015038012000300008150b4040001083c00247c4003d141000c0c000a03488400e0b40c07440c03245210000d04100400215540206a010029018008862003038540c1038601080c03010703480489c01007440c0c407030440d400a6010f500030640000c0d01c00700b4581280030b10b001d50319080c444501500103003d1140d242d1000050000b520001644142510040d034181008061910141143e82700c5094030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 123579901 1250 123578651 123578671
    0x1090320121803010f0b0405100b090d21030605240d05100308040803040e06012a15020a08150a08060a180c090f20220905090f010608010203 62
    0x2803941041c80391000038102e03500c003a800301d0380c401d02c8500000e0030b464452031000c00c100c0e162549058181410300a9a030480d003c4c410040000e42010510720351405120200d500c1011140b00000c1400418961501003040081c0381104140840303001601509140c80f44601035503950640401100072225039120000e150500e01d450b04c00f08a000102601d40907040c0044c0c403406580020001d501540244002c046543c040c584076441c2003408084007500078541410f0220500c0180c0e40700c007075115140c01c004c02601104030b0109030303400c00c0c4603034942c00c40007805641d200252a02010340c00c502414865580180b40c00a80941002030110442c924890b1000039031100e00481c4510029030000c4045038013444404086880ca5220121004040c0e0b02c99040e0303554502d815400203540d0300072045101c1da01840c2c4090760001e03110310603403481414406418003591001910801c1a200d1100c1d001703203081c1d6806d00140c1080340c00741d61500d05c00ea0f906102d96103004000070703027101c040c0250392003078050700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 123581151 1250 123579901 123579913
    0xb0c0a0b0907050901080f070f0b04030609110a1806080c01080402101404030b25020d03091406040501022206090501210f020310050a0b1602060c0106030501090320 72
    0x3a94904900e00003400340c11840c000c2072408107030b135211000420300030491034004103107005000c8212420020503410403259030f4100b04084c0880c407007131000c4030101c0303500040014840c1006e04000c800d20500ca40d440d07034404d20105c4c0000300c141e940001c0c0001161503203020041140e071118816540e0b6549080c02d40880c1058000901500d8166640841040e450806410040300c1403035480d0251300541017180c04491244c180305400d1500200c3c5c00e211030b07505120745465004881c0c040d6a6031400c1401d0000c00da02e90910f00f0400030800e120800703800c8000110350207400c1a01c2c01c98041d402040003d409400100c810b10301c030303001c241d10440403100740d52501154a420580110b45a0102c2003039007200b081c0e1001c030f0b06036030160742c071076941d9211502c00c0c0142c4a041540d040e909141e21640213501c00c00c40144140005c0c00351108480e40a070f490215010000401e2001c6000c5001e41541c080039540b800c8000030034000103400500b0000d02c82d40c0d512807000c98180e403640d91049070b2502d40310982c0c010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 123582401 1250 123581151 123581153
    0x1021204031a090a060e0a0b0c090d060b04090206040314010c05041413091407050f150f03070c1a070905180a0b0a05040e150a05010501080a0b010909180c0b0c0a 71
    0x80b01c4030541100d100d01c25100100083d4441318251151402c0c0c03425140c0c450b440034414019400c0801d9048108004001c0c50076400e4000107007416450b40001c6c0182d90342e61090005507856600c484941039010b811103486075541c1c107081d0186e070003481310240c265007010003c07082d43c2e00c18011102030794040304170410340f28020001c5c01032030b1418020303d48580d540e4074078145c0460208010050b45100410050245509183c14440c1c1d03100e0007544140662030703130358100303410303c001c2c1060b42c2600d074a210000c1e0b1251b4502404681c0e10f055210007038491294024203503020304020300c0c014441ca01c00c0d245c2a4002c0c4d5541c2c28040040c58031140319400b42e100707030301185600e0115003161141c0ca100034081400b15803203800042c2155001e8040340c165a0042d103241030300281510762305610407110032081000d0340c9803000180800800400140c065643c03000d1840c3c26070b004c0d60565024180240c0200614a10303a0030181c01d0010300300069910f801c0034400081c03800c1104044401c03001a40e40582915082 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 123583651 1250 123582401 123582443
    0x100b0604060f2c040f050702030405040e07050d080a1b0c030b040f0209010b040519080606011b06060b03061903032c040504030503041e050706111015050102120403 72
    0x2119000d0104140c20041840f00440d01e50681024100410801c1005024408101c211003688501406141c2440204a0b03160f40210a5508694042d82c0105194015105250400d0410340180e80c0c010a4000148144225080039003400041c6494101c01c81010895020a030100c2d51030092654051a5051001900a5960303a42281c4504913498440d14158006111560300760042240c0b8280450200224a04020605440d800d420440c41140c0e04026055481d10402401c00341440001c04200b1084120400c24224054002c87e0820505031101c007002441d0f8000c1d41e4840c030410340c4402c64a18a07184902c24012240c0c1900c5081c03111011102102501c004c5a5000f400050b00c00d01614294445000b118421482591101d03a68034043c0703018075482070360944600403015061076020008500040010a0310b2090500c20003034620051702e103240c03285840000418508200410f445600d6101800c81591002d0f000d0f1008203c1e12466a00c023402207102c06805500b05001210358918 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 123584901 1250 123583651 123583667
    0x180f07080d0f36050607050303070516080403030306170102120a05090102040b04090c091203020303060108220b040204050916031101020705060a0c110d0201120e1f020408100b060406 80
    0x500d03081c103203c0b106426407070100c0040340e5a0741c0d80207050900441c0c0c440312030010030140a001c044644074106000c90b26690750340d010040195040c000009080201140740102e1004159808914a030791140c0f64074005015013200c0c4070b8112401030b211010300009c203040c02543c58043c49081d10b030f049035031002c90503400351001a2261081cbd550810022510241120042010704407048000c5061011000003c00201c1c40e940100e0070400341c1d504002c0041d40c040200c0c2d03000982441c200e9190340b2440703080c1130660316010003190090041c00301c03401008066110f00744a075000f00c904002d10364400702c3c500c0c2c407103188018a101d0100320120a0000900702072040e1600003042c4120365555803140c010505c80d42c088103100c804241e42c007209000300a00e01c1c081c00456007081d200c2000100440e400030f404111400e0740d410000b07864103901c0000c82e608100e003280a906890036040141c01c0365800300e009500c213000f00803040c0561011141d030700f0145e00640c4004074010f000c040c035007490540100c54400b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 123586151 1250 123584901 123584927
    0xa12050d05070305160305090607050c030706090e0f060a0e07111507090302060310030b07090807050411030a021b032106040c080c03040c0909080405100903080412020a0305010203180f07080d 84
    0x1000600c140d00d00317032700c5820141001c030307208500070100b07050f50700300b05032604005030301c070504000800f001881440c2c8850100c5402810135007845100d0703150030001812a0400d034010389610b244060800c5801940a420320045c1e0007580141c1c4d84400c06038100e14291902100c0510206400036030400040c00d0180055610500b0001c1d80c07100c07907407079aa03241c0c00786000b03517480c000080c0c1c0c01c00c0034030814006009281c0100000c0345c3c200031151655041840e2808001c001d00052940460182d40b62441282c0500c1140c8100303096030b0762240101c009048281e02d11102c03590040d0190002602410188101d660f100c1868880c104141e4131400c0110603540b000b00100c1e042039400b44005403058150145422052003012801e868508103401c0c0310115600c501c441c0208100c055040020410203011182515002c1d40c640380c10071164004115092040d0f4002002c545c030000820008001481d1a1010365101c001540c034440411408280d1310b0545001e002c4103a0441034030600d00c0c60203528804100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 123587401 1250 123586151 123586157
    0x51201140906010812040e0703020703050910051309060e130c09090b061002010219050d18080304060507050403030e190e04030804050c0415050603040606050a12050d050703051603 79
    0x5049010004400d0460a4405440e02da00510060003460024003207800c0c0c00c40f866804500b01850001e2100103000050081018154001600000c1c98441c00c22220348104c080d02d03d0b54411403150008116034013000d600f02c01003040300c0300450350307940a008440c1110100d0403c0042515051004030001400d600f04688a00501c0e0f00019240400c0c058443c83e02c0c0200143c001d503207803400521102947ca0410708045910401080700203c1224013081d04840c1149080744d1038a041d40c503e40010721081c9101c0c7c2941403075102450412100c0e20056102c0c500c1140e00384201d4850756425a05401f91340002808a00070300305148460828103c002d42c0070f004d1001a907042c0341e8480d00b081c1101ea00b59401d500150140d030401040c4041001088106c55003541c08200e0340381050a0074101401c4c5001d0345100d0034000010400340151500801c000d400003c048104095586945001c85501848203c0c1c440c00340c01d103508043da0041c410b8894035034140e12000d18050504030001ca032111522001c8042c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 123588651 1250 123587401 123587411
    0xe0a1502090307060c03080a090218070525050c04060506030106052d07050c1903031103090603090f060609040312020304050a0b0705090a1a1b010f14011419051201 72
    0x80c0d034082083d07100401003500c0c1c1c210281e40e11b0500800196005000c100d400741040c40307203001038950844804800c401000d100e00540c80d26041101c0070f215440b1403080f0544c1048005141c107032095040c0027058454400c495142e400c0e40280010383c1c18070300c1110b9000c081840100041400b8200522002814032001070081008400c114040c801d111241c0c3c0309075001007100000c12100300440341d80d4160856607404040140007041c260a0319034003004080000d0740c8500149a1800c009441c0e926400410441c0c50389854030b0070039034a540d5218410756510642020403804d0510300880e5026507016560301460003c41c0065402030340c40500111410710038940c021001c562441d844078043c605668940340e98003036074409c1000f201c0c00703034100c680c0780407044190b50540101c0000302d4541042d0800042112044550900d00500e0840740d581d041909024510003004a02d0100300c0c1a110360810500414800c1402d1181005074250f10080f00c04a5000601c032916200a1580800785800c1c00850 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 123589901 1250 123588651 123588667
    0x6152c130302070b0706060e0a0506150919060825050f0a020a021806040c02060f0a05041a0c0307140928051504030501110a120b0604080604050601050a090e0a1502 72
    0x10685c1c4010750545403542c1e1054180b00801c01c0c81540d50304076520b441c0a000f0b90802000282003401030050b1000402c0c3e0010341181d0340e491703c3c004105203c0d02603009400f1541d0b00d0720080c159010450700b655588251503040580012801111401da1005036661801c004800010f004e450740040d070b0300c0003584a030b9440f4800503078580421100140d152034081e1040d040c94000c0c0015105034480d50301c10764105004010310250181002c0c1e034041c0b0301120100e860f803a58208000040090807071182021038880410056000100040d8000c0304503581d03950260044107a0a849400781c0c03042c103640281e042c808140c110130701010548602d21048a805801640c03400000c5000c11100c4445d03005000100e4104140002886103030b800000200f00246000e0542900509261010746d844c1c40d8650f880700301d08425100c11381500c01902104c41121020309207420880e030345010034440c0c0b0340f00e142054404104030301e017402103964002c1204010301414101d5910480f030f0300c01c001c80501129500f80207845c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 123591151 1250 123589901 123589919
    0x11101020d09030237060b120115050d08090909070503030a020c10080c0d051005041404020f01020c0a18091a010603050c040f090c0c06152c13030207 66
    0x355004080000007801080c2d031074080e05040b035135503581c01c00c240301501021280c0c40511600c20200c0300300340c01640341c284030315000c4003e203d40004250800085001c0c0c1d01c20410552003920140348240c0820300059840341040312601c18500000c0114a050044d80d103d41071850402d5000007110090b903002544070f90129117160008000354006034460b807401441d6080005030000740140b1071420300d40303502d400910b08840d44912004603009580d1400000c0c103178204010b02001401008109000e40844240850300c4131f04180d406a210b40320f54100d00b0701540c00022501d5011a0162142000d1464460000c105440c00034005510788c2c0c4420030400040d401440c1c42c8942c1c0a6400d100324603504140000b0111140209901f1a0b040700f00410700060007045121422541c80f01c3c0c01141100035450116100e03218010010009410400c100c040480034041c0403050b1403030b500e0b854841c0c0c1030200c4422030401100c1000341c40c403054040814040d50107010f4006c0c1d824000c0c01151499581c9460360 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 123592401 1250 123591151 123591157
    0xa170403120e010905030f0a020901090b0109180b03070b0d0f05070f0f110d02010207050601090204030c0509190e0304080c030303060603010905090a080721030209030d08070c020603040c030314131401110102 91
    0x2400c407504078423051000c52a113169800e01421505000f041079480d0a03001070300f91009401001080032900e460565181120303044001180e40c00f030281c410503035407000c0c2e850503500413031a003082c06820b25055070f03144034562003518400c0300c0660b120401c14a030201d0a5424040f007515030350811203141200d1003240da00304003c0403046d64a03400140d0790781c0035003040790400d003041e005560105c4c01084100082031458000d50f06035402107a07070f10103948420a01c040041401e00d60f40c04440e0421403035030328921012015004031010700341600c610042c07030002c240d102d10048136a80c0d8801414801400440302640c01194071001d503200300c0300e41c00d13025110b40d50907030031401040390014001d000c0404070f480890014001045141400d40c05c1c2510400029201c2400007900d03420005c685001442040c82546008501e94024046a0b0307641481e0524000728070803030006501050390419001807200e2820704451581702c41940d4040350906109130f0889007200365600034100420b00d120341011180a00c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 123593651 1250 123592401 123592423
    0x703020f03010212010b030603060f0f010302040f0f0e070e10120f0203070b0304080a02070f05091527060f0a030503030c07061d0606031213061b0c03050a170403120e01090503 77
    0x2106c0d0712481c00c41d0415103024401414100308212200030302030642c05000c021070643c0c2c1e04490110f80303c2d40c4d07403000b10004d0071100700c4d00c01c25a080c4000c014000e100400e180090300c1168000324010f41d038805140420b250244036649d2205444200030340803030100034200404904c000c0a941c50556620401090b81d04203032010340701c250001401030701c1c00d501001040300405020400782200e910f840c000444018005150815009400c50b00e0803407030340c941d01e0301e146a50345d181c00950f6000760501c0004d80c940c0b048401601941d60300c203a940d01c520f0721001c01400c6030342c0030008619660341c0407070404103078000f10703c101c2d4025102d645c2030312100d00795180ca0060442c1c04009090074607201d006c0500e007818031311100c0401c0c0010407218850500403070540702912982e007000301500407024002c000c000091075000e0031655010001104000e004600b0200d49409003403e244d00850b18641c4c1045071045102c01844400350220a13014a8000c55120070448414103111401030b07074401c040380c04e081c0f540355 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 123594901 1250 123593651 123593669
    0x51b070504020301182703120b10050c010b030304050f1c0804030b0a1a060306040e0f0a03020f07170303070f0e04050a050106020d02151f03080a0503060f120703020f0301021201 78
    0x21002030020030a104004c0d41c0408080303000400180f00c06c00d248092510607018040114401c40409144400e4010f00b803601006400071700a0100440018000c5c1c010517080d0b1815420801c1c8007804c0e14001007503406a480080029040c481140200300c043c08a002c489000142004c810780e020031034a0002c5e00056000d40c024880501c0c0001017001140c01c0c6550040703500d000f42415841036110141901c0d401501540c0004480d200700c0710251618124580740c000c0b030320480d0b0b910b03820142d000c01c5072000c0790003100446800a0300c0300c0e6000f40f8502008030b42134090340240f0006041600ca411403c2c0100e440b03050a510300d034465408503064950031242070302c000b074840004001160b4100702e000141d151a101410809500e0041010760310800b41003d07101c02c04990300d0740c2c1c5a806040d4010b00560780a12010303914280b55401601d940c004403159485110075403640310b0329052108141c1403000704100a000414115400c2040c11840e00003119003640d400c0c05032000001540d01c030301e40600000300c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 123596151 1250 123594901 123594929
    0x51e100908061302090121021903140304060801081203070516120c0302060c04031e06020c03030a1a0a0e0f0403020313060504031b0f140414070f03050702010c051b070504020301 78
    0x1c01031209200c1c060f44032030601c100040d00301081b9122000c208070b41f154100c42070704a1000351814440c1800b05a00080c0c004001914226082c01e4000020403c8075400e45841c003043c0e030780d4040740b13469490b90844021007520401c0040c40440c4224010f0000070300103103048060901070348070f0000301c80e245403508000c40c122602c0082456010080b03203506c0901801c6461803e811565046019054540414840441440400b0400502e41c068900031100701c2c044170380340d03d4412000800390030083c0b20130b840c41d03440103544111420b0603110341c1c3c251203a00301c090840340c03034501d4a0600b47d4802002a02140020300c600fa6050812140302001040f0b6907442548807400d41c1015800109450111504129100e800b003110a1078543c000d801c640c0c001000d82071001d60382c00030070f0180a1481c255035490400380100200c050f080030b04184e603000190b03000c222030f5417100c0c0107078201c92403d4900c50104000303000340c1c0500041100d00e290300303c00c02e1013600d00550b0782d803000c10160f810a8000c1c1140c415a4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 123597401 1250 123596151 123596153
    0x261b040908121801020a020a0b0901020409090f03081e0106110a0206041409130b0402010c0602120414010c030506030619060e131203090c05041a03060108030901020106051e1009080613 81
    0x50407140c0c1a07210703d800840c40e01000d040c01075030701e140410380207040c050030a001500b881000e43c140d43c02407400e20414003020509107850b07a01050b180c0c2c02140800c0400c0045041c200c00d000044d901420008514680c0ea42043c034155200c68901c00c003800743e48a2101c41c0c03801600c03030201500042c219140d02011480300d01040190b00d520060150383d0101d041d04107440072500d88400160401d4082c01c00754005032141c2040d40113846030303818500240c8400024442089419030000340050f5410000304001d0b1260300048054490980381603034923901800100b949100c40c0082040c5515003c0c00015030140c0e500722180d40100c080f5040e144805241d200c1c0414050300800c43c074800c1580e850100b103040103560f1402410f6500c1c0c080d0b140196680c4001c5181501c14015450090a009046601647e540c0030a965644d01001c0c40c00d0055007400000030300ca04000c0481c401d19002180203007000d001201c1442b4a51086041c40000c00243c1c240c0003030103100c1884017a00036101c1040c4036401c2d840d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 123598651 1250 123597401 123597421
    0x1b060b1801080d020f100203091c08060907030917090105160f0507080a0308010911090904120e030d05041202010318030207081c02030a03110408070f261b04090812 72
    0x80030f210400d40d0030003d03904400034008180003c4a610b40140182c6030b03100c04d9034062401e0014881e4810345526441c01000043e004581944110000c0343c0f08541692041c1044094034520340c1d0040600740075003034808003010443e01825013024189081800d00c041080490780b100b22441c001c4c0e50701480d030410308061200901441c0c1c05000d000d0010082222181c3d4002c182e440144501c075403087d80c6081404000342148101c0d200039800410b0701d9202c0c14941040341d12075411091201c041908203028480c0f5007008070b00b04a10450715142c4904240c5403101c0405000c1003c00d04034101a524903750183d10400710100c1e007218043ea0082403002e09008005240440720f25101500050000c505c2001d550f0001c201c0e050501c3d94540498010032009102c8094052904018000c0c0100b01020450440c0d12455408a130507946d002e9100d000d11034410010b29100d17202010b4142c0092100020055143c0c50710411868050302c001400b1100d6191031000307812801e85500d0071010319044c0250548 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 123599901 1250 123598651 123598663
    0x8040302030705190603090f02041b080901061203030f0e070b030714070b010b0d0e0d1d06040b0306010c050a060c0c05010b1206060103090303060906090903020f0303071b060b180108 80
    0x1056410010411001300f00300100d140600c220420907403556540801c02000019403070700164090024071002003841d44503a81d45840c8216580044c90300b03c0050a004014000c202c11201c041407540880d0110b51400c0b8003401d030390b80c1c00703140b665140c0c2c04200724207800304089801071210801e019124100040014000344d07030944202c100320340521203400440c1c10f8183ca1411900b18042580c7d48009070205500640001e604070700581c014201903c0c0001d420001d00040d83c400701030481170b00c0c0898410407401c0d004a020ba241701c0c40c018000901356500803026004800d0045085038210f46003540c0b08025100250004000a1754134030010b8200203090280c6003d5035000c451129828111485403079882d20010a0725040640304c1c449201458000da00110140140401c144405922504030201822149608030014031039200c1c54201c074040441502c1c050203c1c1d81d248010028040d245032540200508240d07861f40c0e5880a20302c0329035401c0c0c00262410358098440782c4070b614100740e15017425 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 123601151 1250 123599901 123599909
    0x40c0b090a15091e0510110a120216050d050319020709020f04170109020102101503050f030301050a0f0b071203020c030714010f0204050105120718030f050606010509010c061e09080403020307 84
    0x144c0c00c0105000c00e43c0c1700000c090440f0498a0700c01d81e030030f408000180c03820744058405005020ba501e43c2a0000c1d0740425040c0c08040c074401e101060b182c2da0410310007210950080a0440e4000780209440c220381c0101d10a240c4202d441141d0789039480d00c0c080001c03680500101500721500207010401281011482042050300000800030701e42e280c0c0001c0c0d20380e80c00200c811403003591034520320700440b182c1000b00f01860b00b100881d54075001f01403d05581c0e500a014282c41051900700009010340789010b180103450541d002641080c0003030781c0700295031042d602d160341450703001e03c00005809010409061013600810381d00b00c260070108541400c40c0c1e9040400c440242c0100014000369800c01e0031603414503030651039042c003a980c20f042110a51440d400141d00b0602081000051007040301c0e072030506a0250055400540312940156020301c83c041105010841b0380c00e1714030104d5001da002d8400720050f50808840e030810131a03881c040300c01811003210400400b00d024021b609007000240054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 123602401 1250 123601151 123601199
    0x120c010206070e01020d0804080c0a0b04110d0218040201021f090c080610050d050705040e060718030c03060507021608030705010e07030c030b0a09050d05030106030b0108040c0b090a1509 82
    0x3e14103440c0000e4561141c0d15030300062000e150b0100d401c02a05008403070302d400303040c01901d40c0d00c4d49a1502e84441c1c40c043c1e81c00d80e455059481c04010a140588015800590040c10b041c00c2e4003402d100f03c024103030010000e90660048204100e0f44043e4545030b40f0348000d510100181c0e0040e140341404180300140c02072000c1d90b100303c040022080740d55081d041511002c4a2200400e039036460540d203098265040795800a040c0520340c0d22050b80014114082c4585440d8000306c40301402c0d51800c0c0c04801d100203401c4a001e01c50410100f01e544c4c0c4010f4000c030540c4140c0365080745460941400505170341c000c80c50f907400000c0384c2c07003030110a118030a261926071000e4105540707561101e14410665000140c9200002004204c60301030035884040541e030f010054034001c00e10160044d0540d0824810040840e0901c0164911503200d00700e81481340390b100008210040c100041503400da003000400c907420400301940030810f0b111607800c0445c0642e09586a03d4203d003480840d98422480101d64445 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 123603651 1250 123602401 123602417
    0x3060a050103030e041107050109061e05040203030d09030e03070321020606090c0f04030b0a150603140a0e01060e19060b030103030c030f09030206030f0f010b0702060405100e120c01020607 83
    0x264085005003e80c4011170780400c4200c1015075100c50f80c8a02d0f58002e12561810528004000c1c181c0c01030f00295108182e100c202d21b0a02420700c043c1c50b004c584c000d42c1504204448041c151083c0d2008000702d0107450600c80c0c030000322000c41d24024082c0c2041e103c800d00c1600103425092495100000207000340b0140c10581011408208100c00142041348051804107044045200840c00d407001035800104050140c00c2040044000f000c0c00300ea001107519041c40b020410900074000da400c0c010143c00700010075500c119a9000800071070140012075500d50200150a1182200325070140c05910903080b5500d05042c0c0b008203d51a650040425050520040020a030400c0361046255014100700c40c1c02c501042040f1400422034000950024010040c404012203038001c0070320a4400512071001c0d44d803503501a070310a0150360302c02075020300e04100901150802c2c0c41103c030003c04c9810111442d140003800102c101c1c20411162078541c1c802c10000c0394540c0d0400255030403540c50304058070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 123604901 1250 123603651 123603653
    0x603020319031e11070e0103300c060b040e01020c0106060309170c01020d0222080705061c0204050904030809010c080606030c13030804060f140f0304140a05030a030b03060a050103 79
    0x100e42e081c8500b244280f0207116804240d03402551004400307680102a683d40316103030121044100d03c00c0c0016034401038448010100c1c14445110f401e491085100403000007610400211810051300b0400c659417511001d9540054940340074296101c0b071014000758681d6410b500c81407c44903907621041c10541807101d0400030030148640d0a1140707106491082e038568a800f0340501a1284000004142d440013441c020000d50520740b8662000c644480b01e804a0790301c0d945240e50701003601513160701920402034900f000c9180c9005201e0025600c0002d0700700380e42d0348006142d00c1c00440703081d00820b6249040080300f0400384619081005036040c401180c1c10f01d02d0201c4c42d1400010070011104000140d081e0540c01140c4180e4004c5500450542d600d07901e48400412071640c00d280100428040e0306441d8140c00d025098a080000c0c4040042c1155101d444603141e85d8182d01d451555400b640c0881c03400701c1c0051005281c608196100030680020030001c0c14549403000701303202c0c1c01e01c1c0307804c4c0144 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 123606151 1250 123604901 123604907
    0x60909061011060403090815160c02031504060b13050403050f0306030a05070b04060908010603150c1b06060e07020d0e041a0a0f0801050606042d03050f01060302031903 74
    0x54100e03800380c0d620720101181140986518910080c015a14491a8200010503610029220540318048241c80d41040d41e200c4482c2ea80000b9521040e0220041c0100751001d4441c1c04220040c40c00101245c1d12419042c0c20399070b10400560b000d40b00c854807040317141c6003824002d402800c22880c0c224200450b01d002e8500500d10700514441200060001001c24119681040a800900e03040419240000e64512a800aa170310501c40c04010039624080090a100c1c18814002200d410121204003c9150b5010364000c1c1a00e8082c0b031705000c00c1c496541d245100c1000b420040c00e10800d4005615801e1503c102d421900040514046500100005c0c460315070001c80c00c42e06400a68000c640c140c08906d4000800d001c1d6402560800000800010003140c03e8410f0421030740642d0007004a5103520050000f0342c4030781e0103415100340c20104415100c40031208031000007a1800c11440c2c1c510348a540359400c0ca0105220349509a4480b2420300c00e5190600006502d04c079608c030142c18003111a9005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 123607401 1250 123606151 123606169
    0x41404030c02010c210c0c050312030f04080f030709030303060e151905060c0601170a050a26070503120601030203090a02040f090206040e01060e030105010b04090c030b150d05060609 80
    0x80c10051304001d400304003c1e8107000405210382ca0b0102401d81100018000d0000221410944031403922180008050a000c01e440c41c07104c03202000316107165103524501d00e80240141c001c032015181009401088031a80002d103000360b10340c2c0e5031490130380e03d94140217050b2181d9800071421803c1c540180542c4001d902400e501c995829a02003242d882c003007401c07640700c142950295170810000112402031460108415060b2030f07103030050388900e41c002c00c080c6036109043c0304028251380c0440c03207031404645c035000c0c400e02604a20740304070054500c000c4000c0c0e0784d401001c000c5030191f0011900071944030030036041d9940030000f86000c606529201d10706e20798402c0140c8010b0b0107140d9500200d080181141c0041d2843d5401401c01da07646c42c0d5a6140c062101400d01c50380d800a5902d400c0e44042e464103009150486195600d21410103040c07040d640d000b0b180405c4082d00717050791030150300c59548034640d001e0200342d0503e8007540c07641c2e80d14a41c8010344500070000741c4a80c0c4100302880700381e0380c0d10580b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 123608651 1250 123607401 123607403
    0xf02010e0c1c030903060614030f0706050a050304050a050709050406050601020c030c06090d0b1302010f030b0603010501140c0105010b090f0102070b04030305070f0b04060b180403090302090c070b0a0b041404030c 93
    0x50080c03002c0c00c098130058600d1700054951b5081c1030010403012801d160349072000000382c04440d10403e408a2550b140c5407140035180c0060010405884000e00ca24080c0d50080d010780d0031345040e140c00360b882c0c0e132038221a50b02644099403110204018051a8810190720000c00c1c009810b501000000080d1141d4500d4040f51192001041c07400e401e4940c528442000e5600004074090703030070401013218607440300c904202d00148504102d031988610a000305c281951028000d0760543c1d00306401514000d403024480d40316840107000c0301751038030024014070b8001c0075a070403a26aa400b85d0014800f50000c1d000780c86041d5440358034104404101d800843d0200e9405103401c0d41c5804040c81c1102a145501502070038041050f8148414810b45500c884031502d0700f15025000100078010144803003408603400307400310f040c0701d0b020000350601c0110aa0f10000d0648150b103000c0155131004a1810142c40e0180041e0766a085810385003458171036001c4c51214007410858a2400d582c000309121000c0d40c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 123609901 1250 123608651 123608689
    0x19060804060f0c120c0201061710230a11070506100303110d080a0b010201180614070c0f031103090d061401050409082d03010308091509030c01140c010c0f02010e0c 72
    0x2d44420017074400c3d03200202034210319000b200b0f001d00164055990b50b01d20785000d02010b01d09205c41c007004060300c0032841c490b000e8007203490081c2e452050601c010010059001042c2008214460001c5d00070b00081d0b11030a09601c0220000703040d824000c00d0411508440103041d4802d860300803040d0340090368660b105540d041c0200e8a012000d00403405000094111009030005c00710b030200304a032035005041c180ca140c01c03001802c2e9840c1d0004603001c0102c2e040117804c146885a088012074880c0d5010300c0705c02200e02c11240380000220203d01400c80d480003d44006907180b010001e480c0d0607500960060600326800c0c0314041464a543c60300340f02d07400441c00b013240300e440a10f11954450150024100c04501e81940320760b924145900503070f11407500c1502ca80302000303030040c2d111403030015602e10f68005001460408140e10064608094079a145e00b0703c0e0b0001c2c030900400d1b035024010b52140ca4030359904c152403140300c3c400c082d00390380300c10300040415000740100c0c6010361a08102c006003011000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 123611151 1250 123609901 123609911
    0x31a071b02090a0608060106110d080403171509010902120f0411100c02030706030209040e010c0909020f0d0207030207030201110307330609150803030108030406050919060804060f0c12 81
    0x2143e254001c000a0303000c14554000c14000180040c1c00a00d84503c0b9044242911703131050b511902103030b0408048400401041c1600040e2800000780b4006c04d61184106501c0710b000c01100b40028000f207401d0b40602032081d000210801e4007191105031030340040e90a42c101110703060550b62007520080000070f09004181203804c2e8244c040c400e040100d81590054159000c40d616284002c4c0603500540c00180a54105441180c0150f0705102c2c80c102a280c5a45d260a42d03403d1071002c4003c4c1d489480f90301c01c8000d00f0b00c240e1a8400c2d062000340b20340b17071180d001421080d24610001d8414440048646075541090110602150000c406c400380392a41d21410441d401501e4070040181410f803035411801458140007040c1002d01c0e61040102c4086040c102d40c1d17450350740b200d00d5980d00c001d0041098540080c00100610f5010b40041c0c0b0170014001c01c4000d80803000c030315041c0d0345001d50303102400182c410018401800102d02c40d000c410300d07a28409024022224070b02a1102119a003d40c440c142e8070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 123612401 1250 123611151 123611161
    0x120a0c092c0603100e01050109180215030606041a0309060705180108060d0b15090a0c091707030807080909010b0702030c10110106080703020901060f0f0318020a031a071b0209 77
    0x5002d03800703901e01008420040d8a00b0170903498000c2000340a241740340c80c58101c0000b091881d40e00c0c03e0a066500a20502030410781040c00561504083c1409800003018040820450000c9400c80d113513420805036161640383c070b000b240e4544078002d40300100348801040450088040340030440080c480a003807200180c1c0f07a400105485600d000c10191402001d1002c3c0074810b9481800c00c0b904860880b02440940c44009042e011070780740c485c9400202e446920100030024258040e00340c400880c2c001e54495039501e444008031a4070410041b1408040010364449919044108501402c0188809030038408a540800e030307144490b1200358800c0910f01a40c00e1903e1085070000708445040700240a0300c1c1d40c50a405640308014003007244142181000421264490509040388040696901032a00e102c13040580003490b030385503c0b0917600001050100507855210b442c5004600c5540c140b84845141100d030104901e01030400d0081004080d104070000102c40600320006070110f5402d0386035158 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 123613651 1250 123612401 123612403
    0xb31080a0215090d0305060103020f12090f011103070306081c030f0923100c020d0c051606210b01021b04020903060f070801061103071205120a0c092c0603 68
    0x6402e241d0080d20000303810040200ca010452914141c22500d0601c0303e41c407500c00550582c024103550b600c0350401841103072100310381d0644043e042545e600c01d07a100400505141070035035008040d04454050b0020030f1101680d818441e05004040c0b08018184104028250041040c00400902d04040d215000307940e285420b0780c810208542c4c030140c00641500c8000c00705e05885000301481005001d15100b40a83e13a1a6000d100640e401550290180401017034003070325091440402560144909044103003070079001280c0d0301c09004140c07540b48060707540e44207106030000b0829404e0744103800c2010202d0381e40d03000141240031040c0384034030b8600c6120400129000340202c480c07260b410b1064108dc8400b41d82403c4c2400d010365600d0b43c40412aa0701d40350169540b409698034604e4940c0104013800c04100100541c40c010035241c680586049070141800d40c1c1d560050302d00b821082c1c0d80380f0300718001c01d820890301002091503002d0504100031001d900c0c01180301d00402d0300b00d1804c0210004120b694 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 123614901 1250 123613651 123613663
    0x203091903030b0301060603020c0303011505070b0403080610020109030212090d0b011409060d0503040306050a06330e061b070b07080301081b030a0f050f03070b31080a02 75
    0xc00345440055180c032814010060148031001c01e000354600318004c1085440703802220280d0012000035032844e4a4110906581d000c00010a010010180500702c001000788055130b00680c00b0f41d036142850306040042261049403445400c06580c584048180029000b1a8a01650101e0001d45864000090102e0038100800b00b00030508180400041201145d00910b14031006095600304c185682c0d100034002da60003c46005419684180010070001d0310640140744d0000c5c6038800810340d40d6030781107584040c8140880d03200708400c60b4240d071084800d08041c403001d040241c0c640049034030084400300e0050700c1507140003001400d80b0960380c076034141d00f04121001041c0110200d552414141840ea285d90420701560f0185d0084a03194001c031020000784280c1c07800010043c1550314100c2d952070700c0c001e0090508032001c1c010103066045074242800074100103401010030800500c0c050f6400301c1303030a001d0080c01203c0b00c001000841056548062035803242d41c04a0420342d030b0300d0714640580c03400c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 123616151 1250 123614901 123614923
    0x60a0e0108101703030a0506060703140901030b10030c021002130b3108010606020102121311040e011a09010305030405120313030804090b0301090b0a020d02040e0703061509030312020309 82
    0x7040c0303a20b0300f0f404503002004500c03039441c42c0000c01860700c0755000c0102c0d40c440e840303020b00041d02c003442005c0381d210070000420040405040000ea4064000082030340099240010300c0440d9070341e0709540596805102c980c00344401d0f56401c501d401016042142164220b01600c00399510101e00345140d500c591491040550b0742c00002504003002001c1c4800c50706150040c0052542803202c00500107005000f505e842c4090f8070070980c940c1d0b445560350480181680e0066540e410b140700c0030004c030f0300d407403142070358500b41c190002c10540c0040e80800705081c0e2001149001e458841c0040022038804429901034490440f5440701c0e5458a550b0145540142911042c8085800c40000300f00a4644002d100b11050a281800301806c40c41c100350880e00621030140500107044002205500107a000701034152110030b0041c1815119140c82a00300c80494040c404259204000d01c0f00308450070702c60f0f81103006454611449801e41c1d9004200d5400407051410242e0040003280886900780003801100c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 123617401 1250 123616151 123616169
    0x90c1e0c010609060609060306060806100e0a0b1e09090a2319140f0c0d060906120b06060c1504110d030c0b0703020901140306010201090f060605090105060a0e010810 73
    0x495103c101c1d150041895102e4540412180c00300080c08034000d000c0c803030484039181c6903030000c1d07a1140180091017110b12010000c100c1c0342010603255035120007500000e00544101c40c0d49841034018402d40c541069883d4a2181c10180b03c0d07018a42e0f10884c00a81c040c820900c04100200c90700d050120400007415000a01ca202d0410410041005039000c2c0000040c1d4400307100304101d42c0050404004d0598020500b10180f0b00002c0014601000400003081421000640c2980e20755049085032416000301010301d03a00601402408800089107402c071100726412454580c4145485985038030034101d81c010000c00b03100150910141c140d90403da2100640111f44c500e50b2860000c0c40385136a103004460003400718000c261018824400e861005806840310040c1c5501c800440c091600000d2aa50440d9240d0402e42c001a403030202d0241c40a11400000c9012800c00c0300b00950f021050300003a0182e441880303105400e552000400c00300d41e40c20300b488511070300c401c1081004200c140e0000061 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 123618651 1250 123617401 123617411
    0x204030503030c0c0d0305010303020d11030408010e0c100e010507060504020d02060a050a091401020705012a03110f010b130902240405150702100807032304050c090c1e0c01 76
    0x3e080300d03031008103940e18451064a0410031411010f4080b60001c0c040a03005a10000480607003e009641d501c0d80d20903007404032400e241e40c5004050039580c0101030361107280c2000b2000045414100c649450f9420103050074641008042e0000f000c50107480c4c1c02602c015180c1f404074082d9202c0c480352404854020340000e41c1e84116540103009507000d02d400500203140c60800190b0301c0c06a40200c00d24081c1603016101407450308004503000340b600000050700e0421518429036803034916451406c100d00c06d0b281c480300d1112a070360541c00c01048010201281e410405405c490341d94505c40315030300c04d1208800152058a60020920f140c0c0580e0018104a1021200f0300b240ca044e034005c0d00484800320381c0110503041c1c202c6041000c0c0a08080250001041406142103d00035900d032039005400b40740c002050452451248049409010065559a604010302c0b00307025013404281031012040d0ad60300101c1c1001019240540f00b41001c4480c008041d080407114400050201c030520780301c02d4020303c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 123619901 1250 123618651 123618661
    0x190305010c03020406080f0105011b08040f06020c100e010207060323010902030a0e010207150207171c0507020a0c0303051c0f060e0708090d08100b03180d050408070315020403050303 80
    0x4000c1d4094050700300420a1b07040011003541d15102c91905941043c0e42e801c41e007034807a40480d088201303108403c0720640c1c0140004140d00e039070122880300404030b543c020074140d04084140320b9000e074518480b03010007480c1d68410b44c841c0d0b0002400030866800b40340c00903050606810b1240060910002c00008603000d2000080e01d40441e0080d600030103c100c3c08008080406160600301d20901c0c00007442410070742d007940790000140e806001683d008008505511048501e001ca4a03408034020940038600f076403810804580c0c510910380d1201d41d40c0010a41111203403500c0b052400c05101c001c003000360024200001c041c0211040524107070003441400544029010040644024000c03840030010f003030b00090841e80f280e46118040d0f80140090300c2c502c0c3c08240c089804803401411100d0f4001c644400191041c9900c000718814034000d0204050700c00c18003004c82c14103405030207a00801c031050000703004403180407810074126075129050300300c0034540000d40d030007030b010300d520141c03084c040401005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 123621151 1250 123619901 123619907
    0x906011a071e060617060a02070206040b04150318030804140f0102040906031202031204060903090b120708010806100902030a06030807120f091a0306010c140a030e03010515190305010c 81
    0xc2c0220300c200c405000c0b05403101d038071644084071050145055440031000c035a00e0160381c1e0040101c0c6001402d4249880d84406403020301e82d00c164010300804012420341d1495541c148610581240c3e011000f405015190302e0003410944050405000c3c21549840b401c2500c10800c2148021203150009544840d943c030000b034010304040c4425905034500354580100544048210368a054107520000001d44542d201c0e10000d18081c9c000300c0601c80304c504040351602071203000d40340c114180400320145103003800f001014884180d204590b40d42c084424800d00300d130182200d005403513800030010b80384c1e51408034050103404103a0028143d00d10014a03007050003039504a0007128a4680c9420b02003051a4000700c89001040c89030104003a411910125030085007070046800450501d059070300407002d5118a080341e541090110342d241d1080d0019000c140d00f02d91050000d40044000300810316210340010b0012192034510ba12400c54224000d4022205119407805907030840d00800010401da400030f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 123622401 1250 123621151 123621203
    0x108270a0203010509070602070303180b070b01140a0612090309030b090303010f140307050616021201051009090209060d03091d15030d090302090c070204091101170906011a07 77
    0x1c0c1d0003035003444006810350800250f044212001680242034091560f1800c648036075140c000046ca6541c1c1280020f89248100302424480e4000d1180314170652502100c448060348081d855030094000c504200581600040c512691002c1944007080050742494200d8024000c0d410041c41041400c0510801c100e00002440c140d682c085031290106440d4500380e90103d02100f1a15450380c0801da05001c0e9081c204040e041000660070380880404050f40011b02070440c1555254442c0e41d10010020031061801405000749000d120812240ba0a07030003142d074a010091981d4051480e441410b400c16102d548060001c1c4140300902001d4146c0c24041001e10005030381001c00c11030060b40d0850f180c41c0100b0303104541022511240000744c034590900400c154000c003589102601840000007507250f5000391100070b0312032004115840c44410024040e0316401c01c2070341c5000c450804205d00303000000746c05415595076060a4102c0300d6614200f0415100d1142c00030180b5031050055800e030300c02c1000c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 123623651 1250 123622401 123622403
    0x903040b07110a17070323010207060b01080c090f04051b0307020601050306250f030b0a0608010503060a050f0a020309010209062704020a020705272d01140108270a 72
    0x90000811340d20043e80240340034001130000d0b00c2d00714000c10800240c2ca1180c0302e0402044416901c0c140f1800b503111030898000b00e00640c0c00da602c51404036484e680c4860740175400055180064201145000455911000c1800480c0a2542c03600422000ca0404010401c113544205c24990740f85800b2030000d4a54400384901401b9114407004603c501c551801c800030541c0d28134400d407918400680e07080b074142003458008001d140c1c2d0f80d161224942c40785004600a841a5102d4075582c0d40340405151500800a00c190280380c0b409040c01080103240d0125900806040400b603141c0d11080803a900910ad0008080d80c445400210304411121001d04e048402c81001500c07120703c071340541404260b02c210603020005802485050101e0300c1d001c2c03c5c2d1190344e2038004080c05000c1d1004004030302380f001555281480300803480700455583c112400c411a0301c0003142052020352614441400c3c010124040c1814855040d002601c9103101d95842021003000d540c0072503602c482103a072280c0324801c0c0c00b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 123624901 1250 123623651 123623659
    0x21207080c010603083610030b03060c0717030408070209071403011d150f01030c0903020306010e01080610030206030105040c0e040c0806030c042a110304080c010908010e06010e0903040b0711 84
    0x1b030f41a0100d00d41402c021001070340005150b214039071000400200c418080052001d150b40c6180082041e102042440d00c100c4051075011f50f0b90800e428a298075083c8155951101c002c1081040001890003041e2015154150381281c51912200003d80300b207007052032f603c0c40f804404800040d00030054a96803080580c0c0c001d00f03e0351511200c0b507452050354840120351300005100caa28a840d4400d502c9141001454a000c94186450ba400641040e10aa0000340c02c950400010301c280c0c04c050141b5038000c500e122848d82000e04c1c5501040160105105443c41150f4a801c0307aa250b601940380034201c204000e0041010941103000a0f10f0700c1e10940e0b51301d001c0d05c1155040030023814144100c0c0145d048041c441e96001002901a007c0032060014440800840c1403101c10401c1c0100b0281c03028101d444051312a28140743c0004202c04103a61003418240c1c1454030012034407134003042c001d045d6940e405c4001025550007543c2c6180d8800d5070b00425a40c2c4000400c2030a2007082e50340181201c2d000c035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 123626151 1250 123624901 123624937
    0x90c0e160f08070e12210c010b10080703020a030915140a0e060109020702120a0b0921030a0e071706270601140307030f03050304060f050106021207080c01060308 71
    0x4201c03800601240c5003c0403a0001340003000502d0907401d0300222003000c00881d81c1c1d108540d0640c0909041420000946801c0818000c0c500d01080c09045078840041d1440f40400e03906001c0209050405040701040c154000340000586100b90017000e282d03074224121200d45065580b01400804868104c081c98544620100d44501c50742c1c0148860603060741d0042c48540d00300000c1400950182c0d0080fa409030841c5090042a10280301d0101894061121040c1c5890540941b6080491980c0801c20050812070002e1107801c1c2038040d00e8210358000b000140700d40701907544030b04d001e00b950440521841001c1061303402944c0026100d2061650130000c2c1001c4240e0018840d5148482007e0306040e0000801031050852851000e406640c0050454520960326110550301b0412071b10b040d00040d40c0001003100b030000501800e000000d16aa0821207076161120003501e0f40401c0e243c14540240010b2880240300c40c49041d10500a08000200241ca60781e1805134a158442c83c00d07018508101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 123627401 1250 123626151 123626177
    0x120b060a0224010f0314151807090506060403030e030c060d1505030d17040303110f0a020d02062202150a03020306120303061305090a060e06151f03090c0e16 69
    0x6a141412500f00c0c44200c1c0019003075985a001d00c200840c50703000b087c0f08000c0c2906800c04410115805000060307200c902c0c10480020072802d002c0c403500304006c03085c00c04042c050380d6115242100c0032242c04d842c15464841020000030b08000b9a09001c6502103c045408003400b52140e10400c11110707001ca144413501c2c0e0790824192540c0350ba01c95407000c55002c6800b040814210000c09074000c1c440d190010701d001034480b0b04941600303c0800f403030400c07202103114410907030100000140b40c04140003e0680707103000c2c080c0380b54503001002076048001d80180300404640f50013090b8000300242140c455101c60703034500300400a420403501d09219004c1c1c24a0580760315804000c0b28010400505500c1b001c0741c0859508010344030144c40ca00c490b00c1070983d000c01080710351090340c0400501c2f00251050382403180d246007804864004191088038103000041c95100c60306900158420f0901f07000c41d83d4019402d01104a422607400001000e41c03900411154841000400034548801e440cbe40c980d10f82c1c4c2d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 123628651 1250 123627401 123627463
    0x1009110f1206010312050403050703060f060603021c0c0509040203041b0f0305030d02070201110a121103040608040f0503121303140405030a1719030b120102030903030403120b060a02 80
    0x41d64040581c2142006201144800c00c10280b282407038100310340317426926a00c180c07800c07059500c1600e41d80d80e1500300b4144903481b4084e0b10300600300c910b000c1d070030070580b04010151a404ca114440d00c8941c0e40500440450103134003a079440c0d060051007107449262508000308030000250300c40165400010000c9203055003d8804001c1d00e070004c00541c1007242c0f49808100942c000003040e03040c801d40f406482c0c02d0203c200400001c00b84070365800c1c078160643c50310144c4925030801380900d0070f410030b000600100c0c0d400144603074400d0300105080111081800c00d941188a403081c4004884002c030100945c0784211644030741014401e40d21460510711103801444a80100e008241d4160407440d8500e010440313101404050340c604945c2d1900d014050074500e018641d9611000c008680c60711703201034052401c80c1052880c0d04041c3c00944c513514200100319141e00c0020001800c0c0910402074480c050031a07442818600000b8021980c0c03452031040103951280408030100c021907008030446980743d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 123629901 1250 123628651 123628669
    0x301090c03020a0c0b07170411010f03060506070803060a12080307020c04020405010e102c1804020108040201080c070c0924180e250e01080304030c03020d02031009110f 74
    0x40d0f02e5132084903d004c140c0c4e946065100c0540010f0400c00c1c62202100e1030340881000d240220311072143c1040c110440000540030b85a05801d01c81418070748001000640c03034010441d04015485078202c0d50380c3e0f4a0300700103080f140c4650401c240c000c43c4940701c18104009680158000c02c0c16400f1071711400c3c901c608002c1a44114007516001990480c54004141081700c00060042c071035042200c170441a01500d079421300002144a105101c07002401c0d11070341440c1c10822070528642054044502d4190006030a0303030f801510007410014030800090740c040c41076040c0e40d10550b01c41261400c69a07603800e2034020340544182c0c0154400020034007540d80000003412000c44242546650820459100e40c200901d5501c035100400e0155074540b240127201c0c654050810400200003e41550400001c260102416040501581d00410007403001ca41645d1810040b40c0e8101c410240440c4d4500c04a03040800241110452030f04104200e001c2002c50800102580f030103450302d400f007101240030420066 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 123631151 1250 123629901 123629917
    0x19030509100209220f05072721020105040b03040302060f0a020307080708090f01060b04080f0d121d0a0311061513052802131a1606060504110301090c0302 68
    0x1c0031900501890102004540c12254084d82c0c00681080210240340c1038900450f6200006004040e0350480800416048034002800c1da490143c01ca0034130018044c0145031030070035800840c8400000045a20820490340644411000703d03840781018507000e5942c42c03040d5146245000818000b400c203082901c240c030300c0b400803030340c402c0c100b611100819280100041d1180304103004484800e100500240604001019030008a5903101d1500804608161150040050030303046210807410255200300f00103550070021a0014200c401c420381200b070380300307840c00040240c002c0305243d405040d040b010b5040f582c1c1580b0140c601c00d9543c0c44030174004500c040c1002d54484140c00c8d48801c60042d0740c0c05240d010481940d05039000050aa000000c00081c101d80c001d000e4001030402003d070840c08089000b4060268030304811107205a0030111405000f1b0860046810b4280400602040d0b82050000701360282080040994074a02c009155001740100300f9000d08180320a09641d100313100b203c00700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 123632401 1250 123631151 123631159
    0x1060603020f09010f030605030f0319020c1e0117180708061b160c1211090105011b111f140a08180c041b1d01020304150519030509100209 61
    0x83d20040d2900c0080da03200008140d030354030700030070f864078200701d40f2007000c1482008603218141400a80c901e00b840140c5070301150040301d6070b00c0454072450b1185062000742c11001262041a000407150401240c00030340e002c90340201800344a01c0c4091000e2004800340e01034550303542d201d50380030b69142c00c02c0e54082266102015800f100080039800307400c4500200c0781c4240441102e880c1c0b006441802d1b003100f0005940300f4030031702c10000941c0441001100c25100079411398506000600b10225090041d07000b0854000c400d001c03c0040b076000c601503c0020320300d442c214a00161400162221780203a00413840c540d0b1456006070100041d0340c1a0b405640c1d6207070055407550b01c410801e82c1034201140440c4142c4c0100c2c5016612800b0354840d403910580b1042078056400c0c0001c1ca4819003089455018181061a182d640d13400f100301c03400e43e25a04c00700c0c00c0c0100b5048080311648191040c142640c042d0b000203809056054020501400c581c0d03046070310190384021254104d00c01e49a41d5940 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 123633651 1250 123632401 123632407
    0xf0a110406050a0c2901080601030b0109181209051201020319090c030b01090506090606091003151815080609070303031e0228050a0507060b12100605010201060603020f 74
    0x1403a104034010000c40780c140c0b030301c0b800c085166a00d405e00704141c081480c81c500c2c4c5445000301c0b400030002c1100c0c0142506401052207515503150301007404010300500ca031050322140e006614100c0000741d10005580a14100020014041c000b841c04185002c0c852185089a82c4000d2510050003a68040e0b06001403052a003e14407a0340f600914002500303d5200d089440c001001c80d18040d1441d008200200d004216071420781c0801152844c01410300348200000d00c82e4400725293381c819000400c0b0103007000207040741c03601c81680c82d0048552103041005c0444051401c2043c041d00800400001c516000e0103030743c0c40e0700080392180800c41c2c0b80d04030780c0d000520030000710380300380c21150480d59603c0e038402c10703643c03803082030700c02d980c0326024900c40103002052501a2b542840094511503006180c46810508800b00c02441403081c600c0107080b560f22040d010078180d490002d020209901c0201701d83e41407110141100107444188100d6000d54a4440005a014017034021522280149403400340303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 123634901 1250 123633651 123633659
    0xd0c022a0d0221070305010b04050c09011116180506010918050a0b0a06030b0915011202091c0b090105011e180b03160503070506120403050304050a02090403080f0a1104 74
    0x700e91045038820b0307900440c0031907040610000f110400507400310090141c04282e0440c10200e0a407140f16483c00d015900c1d0804000151000d9004d940d03440b8002d00e01640c1c5001030840701d0380340020100f6103195207a80c1120006548a419103a010303440c21041040c00030341d075000015244501148181104807600a4000c0059402e43d0300c1164409442800010100640f40215007070b4491600144046907587c800c10803541b5160491550207a00c4108600b41c0c5907801c40002e000d08206205840010340210300c41c486699415180c8980c2c03003901100000101c07160625110182d0f042c1d9008601d9407910b030000c2141400b042c55800403000e4800d0380a80030385442e0244001644021031894226914000c0001c00da81c10b10400040003030060700b06850605150400d400c0c465242d111074031800d0100100c100201c0c0042c0b03400da01c1505810320300d44030382c0c40b0b0502034100400040e000b9404400c90081100309500301c80c0c580d008a02c01e1810099503910151600111540c0404004500c3c0742404104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 123636151 1250 123634901 123634909
    0x114100b1c150b0a021006060f0c05150a1b0c17071103070807060e010908102003090601090c2d05040b04030606090b0d08090402090111030d0c022a 65
    0x1081030024810000382c0803034031581104400b00c55044040042c40c005950124690b0400188807019070f0400c0c2000020701d0400c0140440080c9031514060283c0000c892040c010300340048090a03409654680080c07500030744c2640240014000940700b0b0741a91900d40c5510322800c0c251548540c0200c20f4200c446030f8140320130b1240c21542c4119907000c41451403101d1074400b80812001407902100030040380c1c4c00c0c014050071064880c1c1d505410403100110400403250f00189540700408406400109503500340c2e02001000c3c1d200c050b600414a0010a20a6101002901c00e04840c4403540c02c03c54011a42000ca598000781c1c0c5100700c0c1c4485240d04816411002101c0201e003044a0612a16103035644000d03640b550082e0b031080c1d850380c4e038486080080b5041c2d40110301c084001200c1086102541c1d984410f181c0c001c08400b180603076070102d01d1034410390042c009d1603528400d5a0440c1c1e00c2d81000101070b0090a80702e1102d50043c05403042103102000540b4400d01e03e041c13141200c0c0c00c130b230796104148 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 123637401 1250 123636151 123636187
    0x114100c032a0525140a050409030e030d0c0b010501080c121504090804031109010f06180f090b031b0d02040b060d06030507030b010608190f0e0304080114100b 70
    0x40701c0c102101030300d0b50000382c00b08504d0322960151803d0601824000042c0f250b54041070340310300c5031075414a0300784046035076400072070054800c1150001400c403031500b412038a000c081c06c40e5607058411017141c412240e402a411284a500c500ba402c04941c0c0c80e8001110707000401e1b41da11000c0d08c0140078090b28202c001d000e10342c0c06011207070718081e00119800040c2c02d80d290390b14152156440040d0030700038001c002c2d0181c84801c0013980c020801c1d515011280310509454802c80c0c04018601c04010ba41000c10248413004024006001c0f080586428100004000b4150306910130310a426032a0000c201d000419503980078000d05001c20110a034007440003900b200c0c47c03115800003042041c07045100c0e02d481013001030350090303005180c103a0039450b100c1001a01a00400b0601c40300b1410002d0b07528202c283c0241030400160f01040c0c1c402019040030151449049907103076400080750200d8002015400350400d2440b07030103941c103240c43d0040d000c180d01c5d145000707803401c0c0b82e81005030030741c2c0314980782d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 123638651 1250 123637401 123637457
    0x30c08070b040b0c1617070906080a0b1810050106021e120705010209060301090c2303070f110d021c1b06151a0304030f0503100501080901020c0102030114100c03 71
    0x142e40070707803203d22810712041c3e005d900040c0640c0300d091030748140c0d0001040310401624015008002c15403d010681e0342c3c4518050340140b125a072600018001d43c81c0716007090190010508a034a002e0800182d00702401d424003802e00144070324500d24036150100400d104100500b0800b8044601c050512001e2a600036007056400390b400700000c0b0b0f040d448a80c025030003005030000001e8100040c1000400400380310380c0021120209401006005071240100d94119480b13052040f1340000d80c280640d070100300440d5460007401240001241d007500810f8801030b03003003202e00703483c0c2c1c0c240110026520301000c10500620340114948800001c1c400c5d40c810b103841d0354440c50a6040c0e9668110840c07845c154130b004814246070101c1030004054001c10006003062803802c1ca02c0c1036242448442c105504113101d030504005a5074041841d964082d030488003402070301c1c0002d540e65038654000c5007542501c0c2c0320321409440d054807030040701e80c8280701d8220300c0717541951503440c041c2242c0e6030110300c400080e1b6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 123639901 1250 123638651 123638653
    0x9031b011a011d03100e0c01050a1704020d06020a0f031d15091c020102072306040f03050f040905040c05011110020d27030e030c0112090503090d0804030c08070b040b0c 74
    0x10312010750b40402c41c9041700f0840e8280440c0406641210506142c0c0040d05e081c188003040c131010002a800006940907101035410301006a40e80d400018040c921032403010385200e00c0060700c40301c201d0340240c810341444c0d01d60f2010311420340c1108045200d0a10050090303035a03080b215100101444650046811400c0d400880304100b035502e48082d18454880300400241c1c0d130000d01c1c8010805030070002d210400c40083c3d85620403500e1600251501700c020802800351503454401d40803d8010710540741581c1030b0074400c80c0c0780c80c1c0782c640340d10081ca17040d9000d407010401c1290000d81c0350303c9209040383c440c0444000d40f201150410002020390004000010410340b510b4940c0c8a1588400946050321000c1030030040d00003241c1009019150180d6400d40a42c001c030040d150304e41d0704000c02c0390804050582c0000c126a081c1400e508600551880a900c020542c028006102c0e1080c06403007038034000c0c07805130719003640d4424450b65034030030340b00d101020502480100705401000c00038089401040d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 123641151 1250 123639901 123639947
    0x8030c0a060f1103010e010e060f0109030602090102210703090b03040201050406110c0d030f0f0215160e0301050106030c080906040b15130f0e0c0103200c07030b09031b011a01 77
    0x8200f40b0150308242c02c8115907400741401040303420400c1c2805904000b05542032446040c084000804060b030502002d407205400290a80080c4d108000c100a048100c070010058070b148150801c007650310044054001034800100400d0540300030341164003503a4144c5803189083e1400b4010703200d0764180c0280340107a000303400714010740761100b0340701d150003522a594402c00148512000741c01c8820141c1c10f030741154810302021080602100009030440700d541000710880ba040d5800716821602d0b144019015400c3c80c0000955a03015049081c0030001034452100701c5e035801c491035594000445004d80310b26100f10110301003911b50400813642074805030659441c03510060180054504411046010701d0362001c00c1000301c1c1d03043c0910300d42c00000f4641806203080e0480704000340b5203004514281c0c240002507503481d1000070040500150b038811155480c41c503119100945a40080d41100c3d1511403501150a0645040c450f40c90b90800584400c1d1042e0003590044501510700541000d000d0150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 123642401 1250 123641151 123641171
    0xb01050d020c01060e070807121805030409051b0c030d091106121834240e10050a0807111e0d050a091208040506041e08030c0a060f 58
    0x90000b080c10401c00000459094908200712100e0350000780b0b01407c02c13a006c000e2003030b09a40041c441d4418180d206010a0600c45d1074582080c0b004c52036002402480300080000340031105801c610300c120a40c641e03161695002e0b110700c000d40e1058212000d8a07400400252030320402c03070750185c01344500410112181c03114100202d0780c41c0c0d0108154210100001080100502c000c20070a40c501171180042c00c1c028070341c6090700c40c251443d403040400903c1c09590030003c0c00d25801110005288003c41483c1c007143c0601d180c04600c01038080407000800760081626141082c0907000120a402d0391841d16041120100700c8561780301414103030402202640c0441c4680003048580c41c1c107080810310125001500034502d140007840032801090140910000d070700b26810403178500c2103801c03040e1000102d541c6442e01c10000e2180b034000e2580120041400b1403004a41e590b400a48c200003948142807540b50803038203550b4050304105c1d4103982d002050380c200041c034a80040114a01c200400700e030407460 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 123643651 1250 123642401 123642427
    0x90602030103050a15111806070b0f0a0605010c0b0109020d0e03030711010f0e0601051002010603120327020906270106080405210a0c050c1504050310020f0702040b0105 74
    0xe0707005489035840616000140005c041c0c1048081c1620b203004c00c0084500c1042c8113850041c44100d1800310035441800c80d064884a08803040c2682c010b204100340c3c07400d4508140e0544060b2260b02031709241c40008a0f59500481a0355002900500d2007802a882c10b55448040d502c0b030745140c01119103802590741e45e60740400107907000d5903880d01c40904a100c2688100e08482c10142e0701c10741d1301c3c24a0010b6a03000723004541981036840c10b54082180004940041e8050700c281d0780700501c0201040c5600940590551022556095040c05440c0c1400d44007542000a803c0401c040d5028040301e01080f01c5140c0b9000e100d41a4201d07d0320b6035224501045081030042c03090307020342c020a085104010801c40c0900840d031407014807034070103041ca01441940c50b034039004440704e110901103c000b030031080c031100f000904402c40c3c005215041402240b0980031b183d8000c0e00c0380500920891004035001005402920803909806841c01d0400129400b00000307010305d0b0030b0030743c14050304109400803c02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 123644901 1250 123643651 123643657
    0x60702030a0803090c0943090302120610050108070c02040221220b040c0305011a01030c140d0207020d0519021003060e0a050402041107030206010e010501050a170901090602 76
    0x1c042c001d200d48928110007114141280c100f9458804c2c581607042000b0a43e404c00c030441051201d6580714400380030311220f08107041058085400c050305080e00d050000340e0000fa010242c078800d40d2030b820354084c91404550380e0078040c0c07901c4010030807003a07061000354851341003180d210b1058546481c9005094000c034040740e014501f05041d0800c03000044c1c480c5000e43c411180c00c01c14006460141003e9a64500c004110310b090090650310b180002c10b00b07010402042c003002e0350304000200407484240d150b44541d0b118100d0751501180c1030440003080680230b00300c8075104d20380c200c111510f8030a45600c3d460080d800840100d82c05a030409004021071000c11510701088038210044841a0040c0100000803542482e860101404c2a40600c03d410780702c5407071030300104080e10105040e00d4910006002e005c5200c9010f11144010a00c031051590010f12641202c4c0e5148003050700340d80711001118988a00b004000100ba610f480c8030f0f182041403a642d0382d220a001d0000140c03c0f40ca13943d207000340c0c0c4c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 123646151 1250 123644901 123644903
    0xb01020c090403140a02031b030a081614030108060402040b040b01020703020613090e0313050a05131d0102030c090a09050c0301030f05010609020a0e040b0f010801120204060b07030f0906050f0711060702030a 91
    0x2c7d2005c14aa4050001003e0b19248403000200031820951100c10041003540d0050003038503510507402001e190705000e8030f0f043d80061080c803400c036244d6031103110303440d6908001c80c2e00340d204a0401e080b00b001c42c1094030076628610030603409420003508507001d10149500c0750003240554003011500188514040c0300d13130541583c1c2040a0350355410385480c89405007915410252103201010010840756031141c401602ca102d00400102d40380d9441081e2581e5080020360061165000108224140c1c40c0340d001044d030b454003200c94646090720380141808803281265a201b80f50030410050021079109a000000c1a00c5a000030440325114121402039820411815010408400c07681d549032415003e1814107044c20359007090f800344a13000003082d8100600c0303180c45034541c0340c114130705546a94211001801c2100b90040d17030340c001490000c081d004000b03044070000d41040300200e1520720407806c86040c29004030702c00d4203224190304c42d0000011440c1c40b142c0d00040030004440180c4081c4101017480d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 123647401 1250 123646151 123646153
    0xc1a07020a09090b0a02040f05130905060a02090a0801051017210910030b030604030f0909090c1a0708030f060a0509040b0a050907030302150c0417060610030b01020c090403140a02 79
    0x3c004a140540002201030680d041481c014001448024405000b0000b1661304031103160341c045003903181130024040e1100140050056070100714686080d90010080c1650584105420765503d41c0300385d00300c810941d4005c03421b045c952003c100030080c170300844540002c158181d07480d0b080c0301440e43e80401403100000c40590740104000d820792400202c113030f60030705103800c050240709e1503000001e0302e800c1f00400c000d01b80050800304d40d100d24421000003001c0c1038500b0f8108526010350800d82d8081d1a24440c3c1200d016241d082020b00415010aa8107102d83c805192419503c408030860800c2030002c2c1016000006540c0000312642c600e1504d0380074074020030b80e030ba449003040b0404005030380700141341c0d00156005034010070009a0004094022400201101c885600c51001c1070006100e503038002442d00350301c0704001540900200c0c010380203200031920384040e0300d00c1000031741c1561210f400c02e034007580100c407040a150420640e9030754001d00c41e24101491f4001a80b0781d40c0e85401c5040b40e4001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 123648651 1250 123647401 123647411
    0x160c0302100c0506040b1f060504030c060504030c030b06151603020d0f020d051b010c0f08010503060c0d0207111504030506060303030c03071b0f060f0c0c0c1a07020a09 74
    0x40d801d01000902140c425450000c08080303168840d0303680c40102a20040002c1002000940303050b01511a0741040c00c00407204a84441c0e64030001083d40d08580030946103094a03460002c0c519006000b1103085980c801b040701440741c91902d0740c01030058018949a00001910341d010207443c0d40e0001803407401d4030f02518104a5805042c000d103000d0884401400f4441030301c0305c56908a0f0009104000c42c00a4a88160741d11100300840c1c0655854409512083d800c2841c00700d45a5004500342c07445c20810b5440300c4a80c0c0e607680425540700d0068072441c410f40001c02001040b0b03141900100050b82c0a10b03100e409040d0341c840850810b086004000811101c04a410300c10040d0038000a600254210001c60035410910f041040520001d8054824820041d081c926490441034116101d2504070b24030711100b460720b0402c000030f8003c5040c00c40110307142c0034512001d940130f00002000150018040391665040a0400d070382903d6460f1040076032a4140000700060340c0d10b084000c0a45900355002c03031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 123649901 1250 123648651 123648653
    0xc052101050708011806050a2309090a0201020d05030c0d0b030102130b1e04050312070c0b040e070e041a09070c15020d05090f0d0e0d020301050a0b031b01020a1205160c03 75
    0x45c2c1001c0710320408620b040001c20404c0359070700800d043c1518040c1881030401a2880203101003282a406195000701d00c820802c21400e0000c00c6442d0001d000b078003503409800e0703014001c90f45880202d403070070002c040a220144040f41240d2004072030030f1014000600c2d204c29a42406a400055400405100e00c0001d007003e8082d41c0e00c28007045d401258000c981020305290009480d46154460301c803590101140c0f050500c052040590f00400441210f10355a81d104c0030a814075140459003100032540f940c80210807030074548250300300038540d00d8100328480c464500300242d902019068500300300381c00c180078002c2181040d03181030382c64200000599561080384040107490b03008025000a0308000c40d1a035968001180d590300c00c180624101903100080740000d602c034002c40c2c40c081c1d010344c601020010201c0e05d540c07151102030380850494183c80c10644240010f080e05aa07080e0058003d455200d00003589000403030741242d49070400750700b400c0c8212240b1080f0b4582650aa0300320034441c003300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 123651151 1250 123649901 123649919
    0x406080f04140f2d0601030605040f0b07110d0c030203091002071701090506060108010609031209150c0506060f0d03052a07150309020a030308040201031d0a0314070c05210105070801 80
    0x100501d904416021300c13000a070182c0310780300c030014030000e4407071038a5400280801001c0411102c1541d44099580d010703003410003005200044641c3c002100b071003907090410546000e0015600c00740c2d419802149010402c2e424821080260b51005c1d0030751191017400700f1400207001d42c1000401e0071200001b1003403032608005142000182c51103040c0310142006200d455446407042e82500d400009840c1d40c210035100485800401e0741c0600e00c0000c801c1c081c43c1c3c0465010520064050240c0b045030720b580c58400403c414040000180781c2c1c003601c80480000001d018201400c0345904c125604034851064043c80d8002003504201d01400303030800300c001d04c40c2c0803003c81e030140107640a290803c10942154046030036007c03213002c06020700c014140003a04682c40313034001c218040d004490740d1101d41035140d015517503800c0c107020442c0841d034101000d1204501c0d8001340c0f0f0040f90000140d40102d85014144500c104012034185014122006071070b4a0003424000c2a024100035a2400410b41c5007a0410b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 123652401 1250 123651151 123651193
    0x907121104080304060507080702130501180c1b0201020109020a03060e0f0c15071509060507170f2e0b0406080105030a12120902040609090210050406080f04140f 71
    0x2142841a0a010600c4140b80c00416241554210304025a43d02c03a91705210030365000d5500d0013588a000700308403501005694120030304841d42000001c014600300f0400000362030301000e407400045e00e9510140300c580b04075003800c00c01e94010300002a010480c1e03004101ca40f45940c00c1a03400c0c3d81c1b0b4210b15900004104005d9441c082c504015003884032080300060500d0758011210341e45208040340f00390a10185480003c2c1e207000823601080094142d14022000c1c11040714804042101020442d5101c02500703103a920480051b42c0b02e15181ea11210741e050390284046c45d0300c49158244681a65a10980f80000040d045d200092903d580c6444401400c03000e05030080d80c000e8020000c03850000b0060292076000044a060003e10002003026a80007020642006540f082c141340340000c64010641c002c201d010b000350f403100182d00d000d10054465220b68480c0400052962000a10201006c1c0449400c584203025000010a4001105140201c04e591075241c1b44c10095003007140c54241d00708 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 123653651 1250 123652401 123652421
    0x203070906080c04050d0303060806090c04112a0c19140a030f030f05090402160b0709240e0a0602060711120901031112160801090b0a0b1305090712 65
    0x4a46844800524035000c1c0781700c3da60198003203c8207142014041c1e00040058240001155040c0c81d02c0380130141d03140740d002403160003189403103191003016a45c00300311b8885007003490b60121014074181c1d20014458a00700b00f00b00f41e0040070b82c03c6d0034540c2d542000303080020102c0c820103030a50400b21600c1a6850b078802d45403051090713950420006421082c40d04120740c0505144103012041d040030b490b103104007200780e5881440090005510065005280100390140419002541e96050117a501c00003a01a81c1d4907244a44203110400640084c81b021300c2c0e4592030107903440c1c41440302140540442d0f0f0005409a0402010000c440d50301004d00d02c03140a414000308803040102600900c0c600c030310400030b03041689030000703901100038100440360140144003c003401c038503103402c801c3e000ca01c01d40b140e0f02c001807845000054ed039040d4000e00806250081081c291149000d0381c0300342c02d42c80440d80440751404580002801d64599415a1082a00792035a0114400b81180c0c1d1003200c009560b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 123654901 1250 123653651 123653657
    0x180519080706030c1b030221120a06080322030804141c03052208030301080114100305060a02030a0e01060306020c0c0105071a060604081b0a080c0f0f120f010203070906 74
    0x841e4426178841079072400409002203103804d203005428200c1c28001350601011b03c0c807403d0426000201040310040422001c3e03c4000c0b50507407908541d07a4299001e52207480e445500a0100301781c94521030003120045905541d110300c24650302d964842042c5c1003680800d104a1a00c0000c20b403038204907101e0508040415040c50254484c0d40e4007900320b0040d0f61a41d406020040b440114401d05495094003600d14441140c2d1a581d48221007070203801441300c0500311900c00c3c0040b4400301c000f00041800d417644071014100540e2045046002504010301001502d92a240300d450325480a00c80e48005c5c0d03009000c003603541c240b8a0820361821a8100304981002800c1000f0b20209002d0340d1080f10a41e0f81084151164442c007000445602850700401500d008100c1e100c41103406501c11400a110309403100000660340700005c6e0b840d01c2074141d21b0350300f001c500c0d50710040c1407901030701d4041e4281000341690382d880405100305180410b101064400380c0e50010500c20510b8000c0d40500090034185 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 123656151 1250 123654901 123654911
    0x90106020102091311040503010e0d14040e07181206090b010614030c0d0b100903020112050411040504020102010e01020a05030109050105190303030c020c180403031a0a050118051908070603 83
    0x640451145407a0a0544c0b0000e591240c100c0381c411508011240200002802805598100c1f01540d03118114502c2c0403001c51903541d1340d5001c09204105403005c4650702604141e0070baa40304d40c15030b501402001040c40400301c1e0400407481c44481100f0b00140c0d40204030001e641035032440c160741812010b8004500348500e02140c00c4122010703600702c0e580036415099007621281d2101d0310001401041110f194003004465060703402651001030070003280e0003640d03a4114002190041000c03200c0540b0094001c040c10000f100c901e040a030080c54001d0b00c10f10002414818406e07407242207800c58450000002ca00000401002c9082d0040b03601408084842c2c00800220741c140c4540220648002070030700d41c903000310f068a24002e1141d07100703503117001c0d142e03804083c0f0440b0440c0ca040c404031404c5011a140501c0d0f0031b01d44400110440350200040e20004915082000544d900f00c40c0341c00ba50544060707140301240d41d4407144103020300a0f554081c04800941020202c9040c1100364201c00c0c2014a40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 123657401 1250 123656151 123656167
    0xe040302100606390606170105010605030f0f060a2312070b160c080307080919080c0d02040e03120105130b0307050d02211c02010b030c0120100902090106020102 71
    0x84d20020344e2010010342030b8052401e00c3d20b010043c1c050180090b10091800c5000104d001040f099500d10510780f00080166a17200e80c030071780e6980002e50340080b404100c00c0018130300c2003103a510150440340040505440c40d590390400c2188203c8082407802d4241e5003241c0c800c0904000300f444030b8480818014112440c140141001d1030300035400741a010880070051803080c0125010000e0151507107405482e40c0d511a401c00e02d41c11350140c00c0150050001021001d0280580300c004015508400302800510a100c4100f05203140b50080c182e80c03155540d140e800a01408200801c02c42008185801596260004001c0040180c2e60007819240c1440062035483e030300810004181c44085034180402e21081c004034048071b00520b000660504810700c40d0500708000900c081044100c051352407030310301004404a00b651405540e05400d40c0c041c2003814029070043c84a00b40c09542101d050032000f4412420515000c4d00b40b51591006a4491030310040d800e240308803902511090000b903242c0020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 123658651 1250 123657401 123657437
    0x150e0d0206070f5709020a020102031e0912090f0904050705010219030203120408120703050103290c030603031306050a0f080606070f060605030a15050604060302030a110a0e040302100606 82
    0x840d200354500851207012200318403004c1041c1e0002d08203280c000c5403070b050412000b0f07000f50710550f581c103040c200c0501d0780105e10140e00c850a11400c41c68019103200104420003e01c10b4100c454800da000780c6892408010740c0341c003000c2900c03440c007c0c1d0084c00d034945800000fa040010b2401280c10100b03c201001300480e4002040380c0703203500303271205070590b13542c481c00c200d0994012082d00700154040e003028001d05c0f43d0705404c078034141d03409910110346140103202e5402c1009170300401d0500d1100504005095030300408040c5500c400040c040c0c0789001c2600f4028a1b0b02d20b800c2d004940411404240280d1580d40304a81d407042602904100c8002e04080c07000880c2c50159800083c00c5403800c01c040701c100001c5410840042030003604813584803407546000d1a0101ca82c4409000c4503140c80c1c0004d006291600505084076006405071002544a0b22402511140544125044400d5a0000039007000e400c010714411400782d030140c032180401600c00c806480f017039480542000700c103082201120003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 123659901 1250 123658651 123658763
    0xf1a040e031c050a060e040b04030e03070b0a030b0907090f060309080c010203180105090d09030f02010c05030301060c1118040807060207050a080a030509010b1c030e090c070507150e0d0206070f 85
    0x18150820030350380bc10000000b4540001500110ba000b800480ca203401d07580c03d0b1300446c0700407504640910043d40d44001c101c4d9291414414940c1d00b6189000c20406540a503210545140c0122000c9180103c03280c4810300360303030041d80d02c1000c0360700701d402c00030740d1250a00c90182c11080d044058036981c100c5003401030520b00319000c0981048501d0389030904580c0616415002140d010041da0307260341e0745000241c011520004103480040c590318070380d50907190003c0d005001030341d2001d072814983c803961141c0009400804045680a03820051007020807020040c1c0641e0303030300c03c80402d580d54200c0c1c440102030b61000390404c20a42c2c140743d00045103540b500301d10069400c3c0c0c0000c2480005080c2412034844d090411082e8201d08010140020200c91400038910741d400758048480c103503940d10240070707024a00600b000004181000181e00c5103490880107010304d000426090401480740c0716502d026092003002c48100305032010340f010006071a0300c20a01c0c071046407500c5501c0f598108203101102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 123661151 1250 123659901 123659903
    0x40503010908250b0703020c010b03060a0b03160305120a11030301081605030a050a020f04060504090b100e070f0c0303060e101701020c06060907170f07030f1a040e031c050a060e040b04 81
    0x141d00410030141008e800d5209030014100101106e80354102845920300030403c03403006a01a000e002180850b440d203410307240702100c1d8050010061066001c4078013085420213540d280c100020b424954405060800241d8040d000759009070403458440440448048515402540260005080780d0b000c60004590016440d4064548044401c40100060000c3c070058000550191401c07801005000352546514400e41c003407000d4200d01501d81e84040e000c064111a000300260581c2052030ba0b10f8401d00006c50082e229003004100b554541c4800341000340c0031100c0c01040842d4070000c2000100c0ca02c0d440010031003901c003c5140481400e081900d0340401060341c0d01644002c4045200c1d503129882504c0d900200e03540c204109c1c10300c01421480e02005851440000c0e041050f04079550026200d0149a041c03074030780549603844000300344000b61604544880f1640428000f024424540441c031042e80c91481400140908e0507100039011620325401500220011200b0080000d0308a51075503042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 123662401 1250 123661151 123661157
    0xa14010e0f0a060e0f030102091c020307090c030207050d1d0603130b010b0d0c02060f060d11060d14010b0406080c0d02070f080909060108060102060109020a0302040503010908250b07 80
    0x841404200d0110080000e1a0007941200c1c000480503400b0342c030403c050b0b13411584e0303040d401190010507080c0e0007540d0744903030301c01400d08090b02d000c0001d00040300c0c42807024007030b07030f880503504d0b4520021101514072500c0401c3e000075820b800c100080c490900005094148181c07002d15094a001d02d001c0d8030300d2f610303000d0600000850700c0c3d203001c040380c80000c690010b01800f00707607107c1c040461035070442c2e01800000c0e811700c01ca0781c030ba050010404602c00c1a015111085d160740b104108015400030160942e0320710740d04c247d02000c0743ca07180b0061030300c0c0c9078211001c01d99000d00b09a40c49400c1c0305034440000e0071f8091000303004a592013620603800480b02c00c416601c0b0503000c01040000c0c4189040102059a9252100704202502c4041d10700f80d9403c582d0540c0795581e00d001540c120f0021a000c3d40140c0180d001440b28004543c081c01200859140c0141841e0705d0304003190841d44940d00a550400021428600c10b4034050050101480f00140c101c01d0b410081d071f590550101c000d0100d80c18 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 123663651 1250 123662401 123662417
    0x402100f1d0a031502120114060a0807171501180e0105210d09030b07020c0310021605150906010501020d0f0f14070f0224070209040201090509010b090405060a1401 72
    0x110b0b600d158110010b9078021204103085041210281c009501071004095130f04001e8000158a5442130703101c03203040f140036080b117240c090704480490f91070a00401c410103121140031018800c160340307001e1b42d12a060b64080c0404040c0c00e140007401c43d615012b8600d00d01030103507009022081c440882d0504560081e52450f038060186e180c540302c0c0d110f5094042c809032050034a200c1c1261f07031042c0b880c0c007141e00034002c0f8502038490070401c13a11580300d503500076016440078070140b40d206131a41c01041c91490760005400b4501d403950710241482000c0e9030801c01e124020b018091166801e21089004203800d000610080c0c0301030742c0107040b116001205030b0030710846007800e20165000314864110701c404c0d0303403c3c65514a013030b180c0180d00d400460003d90156811081c5100180794150161350001c01c0c1d840709030b0401000390700700100003800030002c0741007004042d00002e1949800c054140a05002d40c030050301d5100180920040b510004c014901c44c200d020410024040392003c84100314600f8a00119 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 123664901 1250 123663651 123663707
    0x60219051b010c1407030c0b0712121803030b0a06081324090f1511070803060409080705070812070218090a120507020a05090c03061c08070b0402100f 66
    0x10b8600100b84041c100c07003550700d810098004c0c08144001920301c03882101d071545844d565960f030b81d8011181c0003000d044003c44001e800310f00134000f55402d11108800880c40070070b088640e040c03100b00720804402090700c994203110285041700542000d00ba0f5490300c0c01e80c6290842d02c0c182c0d05940402c020341103080c03900380000721820211007620320040d40141841400428034000c0514130380810107440d0300340e0315640d6601c040114068500103040c2268031178201687c94440b074060f40d00c040c00070345c0d203c0d54039594080000c5101e0301a104050082c00070703118487c50b00c040745003004010a80c1030144c0784200f01c8074005075500039060440c202480780e20f400e642d403001580380c07a02e984400081c080300c84808001407450b52140040006620949141168640d1070b01407000c41042511405405101800029050b09216040d41c5181c0042644207208a50300d07107c418090b03104100070303940070010008001c1035040c4104480450040e038a480098034600b83c1d40140700c1c402480107079000d40880a03880c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 123666151 1250 123664901 123664907
    0x1090f080c0304050d0305120f150f0f030115080f03090d1101021e010f0f02040f1e0905010e0103030e090403090905090a140106060906091202040f091a01060219051b01 74
    0x3e4007812000d0280048108241005001c94100201c0c0702442224140020000e580e804100781c0555120a1148200e120f01c004000101d0b060151198010b2501e103241c0c4560343d001d000c0c03011702c82c244c40c41540e642820007209c4ca003421030301e4807035042552040144030703050703161018444034842e0050740c6201c1f509500d400403400c00420a1003200e1860303103252000e0300c0c0030042d400140c52200d2000208012280d000c078940030f9001c1c901c02d01c128de42c45c881d01001903100d80042202c84000702003181540c540c9038808a030441c1e5003030b0007000300303091640014810035400c105c400380d003046c048506140c1440e007036034018501407540c0540344010380c8800102e03400c038804018ac900d0481d0f00072034824003c041040319034024070b4144502000202510310010f081805075668405540085055800e043c0c425000c2c0301c0608020703144642a203586c1e00b0003c000c070300814003440c1c1c01850012440795651400701c0081c030382903100c0003401400b806c0700c01c40c0b0005880007610b0a020144010030702d4500301040d00603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 123667401 1250 123666151 123666157
    0x40b090103090206120a05150a0b09040c020102090603130501060f0e06130605040f0902040612050a030f02030405060705030a0906090b18060906040e0f0901020712030f0605030106120303050901090f080c03 90
    0x480500b2179920f0610881035000c1d088107104401c8035190201e0403001008101c031817821403151400d01c0d5800c014141d0700303080039000606c44a0403400058a00001e05022507072075841120700200394080c0c00d800f20200301c0300780181402030101c81901c002c0e0380d0070012601c010550142489200d000401403000300c04a80d034000a00a04000307004100595000300400e01900000c40120b114500c4d1000101d0700388000c010f5114080e4000d4010f04003440030b56410784464600000480030740c44188000129640c503030004004081c0710344040c2d80c8945501101030700303541301c03600560207201e40c0c0c440038071440d043c00084d1012039880b01410908010391401291403072080c05002e68201800040109a00c40360030f461a00510b05903280665540c0c07511002e078200c1c06480c0c40107140902d80c14501c1145842500316060f00d030030b01c09002805507a84e000107821607455a10045260099000690905400d0b2007403650100720b18000b84070500f02682c4074102c10541030001410440042094032003000300f0400c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 123668651 1250 123667401 123667417
    0xb0c010e0106060507050c180402010c03030b15251104020d0609050c13060f0e011d0d050c01020c0303120c070804030501020a0306210302060f091005010b040305070605040b090103090206 82
    0x80001d0b686a80d00144144d00400d81070f1424494141c1c0b5021074108000742c8000030080040d90400c03520b440c0d00468003412b5919058041645440302042540e4846005030410182c1c442c42584e200000c500301c908011501e102089c1520850a072103000c1840ca620365048643d00320780040c0d840e200e00391044003d001a0f04040d80c03403031901c41000340300708c91a40140081d8114254401130719030342e8001250340c00081c01c203480004188081e802080d5002d6102e00e4541440322519450b000008404941c0481c0003d00035600b0343c2c45809046400d50f014091902202c00c20b0340610300e1701809241c080308488010b0004126220000351100911264006036000303558040c0081d0743c0c0e42110780c002400703488540a0354940810f1450203400740360007440c912480c01d40c9500a020513950703e09400c5044040101401000d0180e40903000342c3c0c000507c074850103081241d5255484a065091440c0740002a411200034014108014406c0082c40016201c054a00340703070100c1c10120510200d0428082c2c02c1c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 123669901 1250 123668651 123668653
    0x501120e011104080f07060509041a03060f060f06040305150711070e01090f090f0b07020309030d09180c02210d0507030504030809070b04061803021807080c040605040b0c010e 77
    0x800e4801d40590240140f0484150750100c4210401039141c450b1101d903903100703d80c04680c0801400d0094149038200c0500741410307440e9030141400340b1002c00d00708035007100d400c141154018100609407600c0b68030300c03c0b14a400d41310142030505580d251580d410341001601101c030902c20000e90304e28070601c205c2e42404c120409640c110356954038405c0f807041d000e0089506845c242a89070b101c81140c1d1040c0955181c00c84bd4000104080b0307120036128103000b41c0800e0840c042045500c0160f2020016040d840c0340580d602c2d1413603407801041c91802100302c188005140d081280f51100c49900203070111504c0f08141d00140050221604002a4810312000d1051079050104000b86244c05074050b52049000340c4072411155109418243c0310070b224040c18400080a00007031026521510201103d1401140c202082941300d400207001c1d40b07100083c44484079603082c10040026070181060313800420301030316641440d04102d006800c5005a000d51081c1c01d0010230300e0700d01d0503800d401c00c8103103280d100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 123671151 1250 123669901 123669911
    0x406061d0127080f1002031e0402040b04020309030406080f0702061f0e2412060115051204050102190c120807031b0207080111031b0304020d0803070305040605150306010501120e01 79
    0x30b20151150781622100005018a226170b1412000b1070089a10900b035141d620001680c030018030741824100500143d800c036039900150401038035540f00850003090340000643e21240350100090519500410f01444000b03035030306001449400150064104903506130124041d281980030b06100d10065004500c1220a40700b805405081684d2100c0d03403818482450454044150034404070811541600d111644080010803042c032144c01502d20341c2c283c0c1d280440c90080c05000c500012003041d1420317542c80c0d600103940303130442c0e80401d070007800407800b800c00200c009042c1d1580c600d01590030302d5060038010050006514148680e00903140034422152000c8a245038207402951800540106851986410702c8030541081410580348100591594040f81c0d03c1a00040c0030340b5000034000304c3c1c0080501c0151000524078030055841421160f50000b02850300703007440020b80700f014003100c212242c010881401a01c012a5142c1034442c20b0918540c00690b042114004101000c03004032203520f04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 123672401 1250 123671151 123671159
    0x61e0d050f07030c11060703050615130f050a0f0b0d0905010c020105040b0c070803160309020d08030f0c0301030816050c03390109030f0f020603150406061d0127 71
    0x86514107020342e0156400700b040000003081616900200b0710b050800390712040008407083d209410043d0700001c06011803001c12000101e0060039000002004901c01e241901880500c8442207082c0003071208035210340442d0310b890b032140c002100c01e00402030740030700010701e45010b001607401440c80345078824020090f8800d1005c00038001c00c1d0603501121040c0c141c8001c00c0d01441641c4c140c5e00441c4d00242d581c0d00d16114020000d0251165107510000e06031240008809030b5079954501e0045401524440da89290441103884020001441015024024030050010810300020b541074010341820803c0c00d801142811440c1c124403c0b021641440b440c2c05020100d0450300d03100121400c00c20f5801c09044c404e5807400c40c2d05051984050010398444802c00200761003ea45015980c0905480804e00c0980c0d004100c00d540202c0d48804003510310044444941400e1041c01c0c000d040d1440c1c800c5a00c4200200002d480c0d0301d400b04241004200351190324152104040c4201517000390880556150791 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 123673651 1250 123672401 123672421
    0x20c0d0b0f060609010518030a0501060303051206030a03090509070e0a090c02011a1c080f0a0c03021603020109060e121e070806040f12050c0105010b0c1b061e0d05 72
    0x112880c0d107410520340c1c08648941440019540c448505841d6a03040144905506651482e03040750640c0c107100f09140c11000c41c03028841c0c01301850081c1d980d1651034002c020030320300f40680500f1135402680010030010129610004540a0724801c988542541c1ca0b0345000b282d025848001c00c0d40e12400c50300000410610613445924540d000b03400900c0301069921700002002d41580c0c84980160102c0d05440002d508032000c01c00316480742084905005515540e0441c41e000140b196007c10b5034030394a04c1c2455010000f603060604404c03401d55030f207400d590009292841ea4030500d0240f100008581c0c000b95158000d0081c202c3c10001151182c14502e118002c400c008ca0800341003d01070a8000b060076000802c0704e42c8140d070041d5800103208215a03903510318015200400c810028140080c20a006081c010b4a000740500c54103192a5032140440504105010f400044507894005100c14241c4070107081d1160b8001003100a45140c0200d8110300943c0701d04e4200d0781c1050b107002d0400c0380c4200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 123674901 1250 123673651 123673673
    0xd020d08062409030d0e040b040603020f0411070c0e01180e0d08070507020306040503090f09070c110402091009031203020c0709090f0b0c030901050f040503030a0b04060f0303110c0301051006050307020c0d 90
    0x1007203c0a0103402301520900089070424040690890f0300150303880c810b070034290010f121040c040c0c1c04940c5032070b405403a02d0201d07030055001130503041c2140d00104483c00c2da004000241041e44102000001c0c185503074140c1e02c0c00d4282c05a01400b02d11800100100d01540a5840d20741d0050f00b600c025103854905141c696024a4104d07205000301184c594035424070b503071f0381c43c4641519250211850341d42c0e1903038000c02c0c010f1020241c3c40380e003c001e441000c0d00e803400c0f00890b5003000d450342440141075141850f100341454240c101054414000034010701c0740094a00300316041c481002900008908000403040981030001d0044000c000900111045180046100c0da601000812039034079128004545080e09490180003540140007041c0d60751103a41c0f001401400c000c0002400a13501c4009501202d031700c0c3d20039004208220740f0030840050038401e090b00d00d2001c9000700010b107460704495504084034001c1104002e070100003d80d04078001c0140041011004003040c11801082c60503201d030003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 123676151 1250 123674901 123674927
    0xf1b1b0906170109021309060213080105070806010e010c1104110a020307030f23030603210702090114010c0b0403020f0615130b06030117120a020d020d08062409030d 73
    0x2858000074800ba40c10f20460300c01e658000c1c0101c40d15002410f03400090007030f40710b064902903420807124001c580d08030b000c1c50043c40e5820010525250540380901a043c0040c4940d050050010044640342c2e441002c1301b0a160348030b0742c0b0764500307946000400c0090018142070f0000000005059204a400102800541b482682c4800c00b102070510f046032008600c1655804003403000440c011000d051402445d4048170150855402d40200452911425280c910325503081c0800101c00055040c40d0110302d014003031036587d503444490300c4000207200c5542c045015050301801e2020404161090001d4041a806881110f0190400000580f1740d0b5184542492103100c40740c5948071006100d018804418400500705070450b0b117010710342c100080b00340086101500550603a40c010302e1984001d0109408651f004118807501d8031300191820f0ba140c031651052164030340070800e840d550412240704e4040c00c1c035000c41c03070141c110f1900141c038010400c1c0107905004025010209075030003003c80c0190 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 123677401 1250 123676151 123676169
    0x16141e060109061d0403030b100f0e0303090901030f020105071b050406090b010914030309090f01080105060303120403030b15160c140a03060c0e120a020901060f1b1b0906 75
    0x9036a02d080c0741040715031910a4048141840c064940b41e00f41c2c080070240e01c031b40a0306000c9060b1403e000020b208028503210310002c1070a80c074210301c09650207800c0c4200190194000d40c5000a0200050a004070500c802019071018124078401c5920800035643e00542c031040c80d1420a02505101c3c022031070754000d580c0036502c0c0460005092049000e410b8445006071160544182814414241c0040039900f40e50548010054881d4680301d64103154402c80400701202015414190b145c0d0a488003e440355210354020302800d904d0034200c0741040d030001d03403505000504c80c51550108090040f01c055120b6440350200b81c0b5015100321800c00f280d014412000c82c01602d84406407140004c00307444240d5009011007009000150080c0d029680005650070002d256107850320000d9540c64540c104410150024586c034400c5003010760410703000d000c0034100203004215180c00100305241911150749100c0740d41729450b051050700b55220a015102e0041d001141d9114443c07600a000315100d443c01c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 123678651 1250 123677401 123677413
    0x906050c0301060c1106041a090415030309060809070f2d0803071b050a030c033509150f1803030a05040e0a060b0d05010603050709080316141e 63
    0x30050041040780d05882454903550000c5200e070700d69810030f4445160458206004200104001c0c9038428030800c490750005e2804e07520030600301072200791400c2644541d200010840103200103074000003200c050f03581c81e24004030305650718203000d450700316558402802200c105202145c0b007480521440035981b10044003601e070041c030040f900b400ba000380c420048030b9082440841e00003481c9a0885802e0f64900e950380300b03c0c68a4100040c415a080e600486240440344400c00c104498060b0813410046140b03a0320743c0104035041a120703006982958041d0b5284000b49a45075070b078610204449201003140a1a01c0d010900ca0078062548a2800c8e1100c18400341c22081e02c074500002212542c44440c0e503090305140c6004404c540b2050003410300d8040c2900c900d00451450020000380c681d80300000c0b00813820754035002c400f5007268400780c0280d08002c03180006002c60a40081110036040c1000450040d40b24103041845c003070528407000b12403500840301021883d40c49101c4051100d0710724025961 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 123679901 1250 123678651 123678661
    0x3020d050f0f070e01050c060c030610030e0705010309020607061104090605030705031c1106040506040309050306150907051213050606011803110d05060718060c0206090f0a050a09090605 82
    0x428848102c0d16007049400b00c000003683d40e449418032000c8290107050160400000c45d925506001d01103800c1c00220501108001c1c0c0b9203444008558521140e0a0801a03a024201415210507a9028070341c1490307251303c043c13400c40d01d40608881107181c010304c00304907844100f4025074042c0e109110f40311101c1d0400c032003c80c9518001c1415000c40f10300600400c403090b428100842d40c180b0101c0b1410500c820f00b800c0010100c0148041c2d031080b8480e0028000e24a002d10740640003000d02e8100d03901071b50000040001010700726042c030416050440b100c030003d42d51030340211618416400b501521b40e2034034060100e100d424031401c0d200e0600c1481923402035540d04c070044403164200c01c000204042428020000703e00c1c0d04003a0503c4900c003902c0d004074207005840707691804100756004400a810013401450700e0a800399008054250b45c5000407280d1050740005a050050410b001d206007000c0c9242c0c5203603503c591a250042601400c0301d8038895451411400800c030050060365100e00300301c0020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 123681151 1250 123679901 123679921
    0xc260c0d090807051e03010204080604150c0305011206051807080106050a0816090e070b0a080604060510051c0b0301060f080d050304020a0e0402120316050c18011503060906030303020d05 82
    0x141c144ca201a0003103200d40c0001c58a100158041000c071038055600f0840410f01c0041400000c0c480d5001c0d0b44014030424490801400300e411500e2130008042c60200141310050114426400540e008140402c8680301e0550300f900240900303814204030b1041050006201c141074100300d0032a030089444000c00356a0f400306d280c641481c2c2d141007100201d80507080c4101c1c44c265001c80141ca0070712045a8680b038407541041c4060388600841004124100b01700190751801d8069080a40425a110b045000b800c3c4e8002d0090b00030500b83e021030440580d1840d01036080c980c004e13544d8501c01002072182507a42c0900c0207004201e40208100c6005104040080074081c01c1241c0c00365a01500c0c0081c0145040c81c044590388018004030707030007003a03044c09058081040002d846182c078040c0713445c10881d0241c40c0c01c40c5000d0740090464082c4444901040f02c00c0b40303400801e411500842c000d41955041700e20210014141a0004004146132510110600d941039018024800b03400c8000c01554403110380341 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 123682401 1250 123681151 123681163
    0x27030306010c150f06030f021c0203030324060403082104020109090c05210709080f03030a0513080c0c0405180706050a090f1706070507030c260c0d0908 67
    0x600d0202c2c521210340310002d04207a008104081c8800d000244880c00c4035408810343d4000d50040d516603a1003114001945486544285248100000141d40c882c0641c042a140c0c04002c1c483c0e0314519a13070000f1283c60901c03a480040807c40181095a1562240340a0740290030002070b801c506c3e410300e83c0e00a1110084d00d06140a281c05865200d4003528000100c3c0191070032800e03030300c1000014000c494007004400ba02a44000c8000164040d500c0d028030014410f50943e485884541c1c8084045d00004030701000712600864540400704096583c585408090417401600404001c40051891066480410280b0200c0d0017280c1c18450394440b09a1804172170200350024050748c00c0400200308144c050780c0103001d42e00300b038200910380d00d41e41e50304158929015481007400b10314451000b44c0364078051003804d900c01c80c0d40c1005420640345480007456801c0d002e800806d9860351911055841c0741072404030401d41c01107103005540d5000c628106403682141140b160204e01031040c00301c0d8043d804111 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 123683651 1250 123682401 123682411
    0x1060806040504060b04020703030b0f010203070b0f091e010603020117091525020f060612030a0806010c06230603010507021902060904050c070c090501030c0e07030b0405270303 78
    0x954125444640c200001031501801c1207039480e0ba58110a001078031140080e00403180603441c0001e0b1a1590400d00940401080d0414115002006000e0004081220b85038000e292034420812a6550043c501d02d0000300d0740144a01184020420102d03c80c1500710030140c0c4c1c801e99032000d8141c1070626071300007124207a40c1c503042c81d00702c240e090601300401d09010380d2050162010500140e203c80354010007001161003800141c010910111449404024150300b2160581d089103003000300c94040c135103038010001d00500b00000c01004c00c0c02684900390541c031071038000708104402c5000b88903540c4241094030030402d52000000010b1017034901845518401c0d00a1f8028055910201c004140c0410a0030301c1241d00000c00e00c01c26119840303500c107840c400c002c07c40300e080da1000b641c202010309001a5009104079030501e001032002840c01900c107000c940300560107030619207584800381c2c00741203008252504140b500041003800442c07a24440004141c000d0b400e07956103000c0300b006840b0b00c02211 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 123684901 1250 123683651 123683657
    0xe01030b04030e03070b0f04030c080a080f07050c040203190b010201140a320601120c050406080403210c030b030307110f031501060305061008100314012304050705090106 75
    0x540441d003d103100d800780720f0380203040d5520580c841166010725001300140c960981d402140c03e00400200081010282288600403c0100c043da44d51844600c2900352110081074040380001c200841001810b08404000740195180e10b4505880c507260103106420140f080c0c20064102c4940d40184100642170989401d0200b2035500d070791100003d40540546110b03580c02d8540550103c08040e980244000c204402040741424010700040c6194000820200c06600c1d103000a15426000030455003150082d0030305014507621820141c0358503103030300c02c0b9402c1c4074448070710303a1038101c1d840d80316800f40303002d5413400c00c50086040141562401079101c010800864080e0005d1140303040b41005000c0c1100508448510040d241080f86da5442a03104102281d2602c0a004292601528049c1e030f0400504d4891402d15080588540701c1005110140c101810300035402c1c40c0390020341084070040f0101c40c2603842c460b0b1030b807800d0940000469081c0c3d5a80680f590200b9140307841001c541c12104243c0d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 123686151 1250 123684901 123684923
    0x21b0f0a050f01050c011401090608030c1b010c050d0c0302100212012303030d0e0d11060a0e03040b0c10140108030304060506010302090a03080a08180a030c14011104030c0e0103 78
    0x1400e100942c0a00565241448001d000180e00c1400c24000c500c05104a4841c2510303d51409559030b080c0c450039000030b145034006219900480a000800300c078081c81000d84402102526401030790321154080001c5d201d801110180001c4a400220000b4500c0c4030b0382c03c54442c07002c003590510481c01207441146020303c0345801040040380605e50000ba0040d001e0708002d54501010001c5d14540c0187c1440e001d01c0e484000e03a1400f40414000c10500304450301701801020b1201c103007142c0f144401070403003407015550944c2040f0070000304107540140002c009281d65410400480319036030400a81c1401956003000840002100410100350498101e6002981103864555400020307250040039141019030901480300141d8800c40040002c5014082080ea200c1080c3c00092024100400120022040c070480d41c3e001040042c034903054941503d0150140c228500c0d00700703407094503401080110760921680482c082072200040c001c1381e1040e8003519940360b031202000c4000a0901c40505421585 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 123687401 1250 123686151 123686159
    0x3130905040203030d0603120e0f060304060c09080f010204170a05070b1c0606050406120504050c0105070614010902130f030b01032d0b180111090105220303021b0f0a 73
    0x1580116400501c01004d0b64286904024081d08407402d170743c0261490319014441d4030f8455002550200d0342c0909492150441900700c000c40e04511000e04000c0100d0f640c0d0b100328003818841c0d0a1130026204910964140b00740180b0168041d401600803440720a182414000c40c050000824000745030b801400f6105041c5003c80303040480c2c00408225640c68281c00b14280084024844d0001400c403903110180c40300d007003c1004005082241010014502d0070082c00045040000d2013600c4210900e0210b98400e0186090b0b0090290208001d001c07850307020020070038910035006025842c40c903504485e52542c0e00d10a50000070100e11020301844039080050001c90401e280c10140000780c6504c002128000c0b6001611880d00108143c40043c60f50051100c0380c00305002105c0e507210303110021304c8110020100c40d2010303ca45901d81d41405400600842c02c80d60b0802000c00e050340f02d81d003243c48035503a810065243c08030402504035140c94400703030050915010543c441c280b40d01600c581c8209083c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 123688651 1250 123687401 123687419
    0x807050a032a0905010609050117060f01050702063f0106050a0903050f0a0312020903030f1612020f10021204140f120408070602010b37090e0606030313 67
    0x640c502026241c072100c0d80e184080b015440354028a1074001c00951585020030052945146822031410480340c11401e40d0034a13400480325400410403038001c9030140c0c113180169241e11601c17030025081100030407003c2805210070400c8600c18684030b005064024401440d1040c600c1400100154411001c014840281b056003e0500d40b940e034180711144545903100e251410a17204d480000d25404041401d040513400840d01d00034410300d21065040403104400241c6074007038001100c00b00140802c2290244100c0810400c2558001c444c6501e118250030009448860520070922701c2c0c401d00b1022841e00c90684212005100301c001c40d200035442c0c1d42d0301e0110488a8003c0c0203400c2c8500703008819980000c2c4030309440100600e00050362145481d44107803d18801307a02144c107691500805c070300079466101030202100c0c1c0c10308414004140780380c94400c1090304402190402c90f807200700424244480e611441d400c4503440d003215640d6440343c0c200350350307071140c000c1c1c9001c180d000150801881c80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 123689901 1250 123688651 123688673
    0x4030c0b040201020a0602030c1c02090d1e1209080622021306080d0c020406080105060102070515040305010903051b0109020a090903020f0307080406140412140307050a08030a060807050a03 83
    0x320500c16240700b41306031b1302e40c80240d0304180c41a40c4400c400152594a00201c003102c10b0129004078019803c12238600300003a07100130041d00c090000304007101e02d040c070301d02d800f814520030542c803d1078206002d440800081030181c2901503921035101d102d0101b59480c0f05002c9500d00103a88a4049210041d15400c0c000707440100c0001603142900c406000c501201e05203c20b892710503940d81c91000300419401000140c401c07552042c841640340805200c0142d074040b9040d029100241c80c01d00b40b110f01042d4040c4070340f0541c0d002070301651038010040308042d40a0008d040031100c0c11030f00078180c04848012822a20741140095200c80240c00800030184150000800b03035000b4010340c0c10b00801036400e181181d0186030300300c600020004080c0861f81d00302400c098021618050581080d050205038051207880c0c01000d07040001269520b0300c0b9a0040040f90308182d03024081c0c07580304042d454007041c02d400c10f540300f0442c41d0501c0d401103450f0b80001410412600020031580f245442c6445940703002c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 123691151 1250 123689901 123689903
    0x1003080702101107060f09120b060126090102040303030501140f010e040b0409050703020405010e090d140715090209070c08071e080310060f05040303020a060e212104030c0b04 77
    0x100d40c0f001d500418140075103c020071a9032942510400405001409244a60001c8085221418000002c10702000b5a654000d60a081c801402407440a4030210030000c19510840000d84404010000351306401030011640300352428040d69032500e000d65907105981801982000c0d900d1a4400c06600c18007405484040140002500184001c0886c003650300e483d10544030740d80020803c0045051510950b40108501050355080b0b0a05a42554540da10b0350004420401e00d956058901c0c0300325070860700e0140c0e00c051240c0ca01c0300c0c1d1202d82170140550547c00e91044250000052003203015103600103800354010846490300b001ea6480142d144055010800d2a8050004400c0020f4020000754060050710030310011852510800412084070700e208801000342c28031003000043c0e00010000c1c00c1c203510031408140e00700343c1e5040510300300c04001c2410114070241e039200c81078a200c0000740070319000d580c1602d4002c103105260380314180007910000c001483c182f82e8040030401c8446a29041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 123692401 1250 123691151 123691157
    0x2030615010e12010501051503070c030f090b0d05090d032d0209150d0605150702061c0203011d0a020307140c010b03100e0c10080a0b0321040608100308070210 70
    0xc2d071214070210740e445210b810a5540343e036440e030051121786062440c4000014002e200c1a00c4d41c9403c0100a15180d5042c100400303103d400390744a01d859001d84620400b801180040703544600240e160000a040c0954464005010303143c19507407100e200c1d01039203a00413186240c2d01359141170f006810340c03105464841c5107c0568241300850440c1e661085d20311000b4003036a500c40c0c0781c00820349003004941050b48072500c41c40300f89000060700c00740c40065403030b9250110742a64176290050b41041e01600d40d520ba000700640b0020002c100310411340780081c0c841c02e000f00f004807150340d8182c464040b8841a10904003103800030300300c1c0054031070000051242d08442000480e40c8480c04000c40d1030711800c04903000d40192909150801700108014001002004031105103050b180440003030880c0c0c901402400d101500c1c4c400f010748a031410020402d10960050740b84a058010080b42c50040d0020b001e218009034948002c0707044064440c032204192600958254030b0040b007582040302c40c0c420302003140c080c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 123693651 1250 123692401 123692417
    0x2340803030406060e010905040b0c03040219060908070603111b03040b180907020307240605030703080c0708061b0a0e0d0506040618050601090e07240206060d0203061501 75
    0x5108180061405a40304840128010b0300308100f07000380100580002141901d071508010100c0c002a14840c1c2100303a91382e01582d26211030003c20b140308203813298124038a000c101e0000e400342e440341c00305040765030040a489909466080443c1034034910059020301c50300500000c1e0a0048145414044440c900e046030b140540e01c00340720034540c02880c04071704c04003152025008941480000d01da484001d610144d441d02c0c0241d035a400700e03006541071002c0d103003481042544c001404d80d40940040e00c0c004003111845036683c901503419500541901c1c2c400e0056100020354504001101c40c003d81c0044c0c014028055200540c00003600130280710810000b600c0040c80060700e54525594481e4018400b910702454503051150542d1224005038882281e454100004038401051480c1510040315012403041c200340b18203854080680c202006003131180300310600c08415003c030301040e40328a80035281c05603544000c100159182d03250103034150300010009006142e814200b00c0c2072803414146054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 123694901 1250 123693651 123693659
    0x190b090417190903061b1b08090a03211e050c01021201060203130f18020d0204170601030506060312040b0309071a0c060c0403050c01050c01020f03070c02100234 71
    0x1c0d026180d02c0082c04211110001d0040c000036005016400203010548040b80c400f001c401004e07001c52407440c00001c10001c3c810420081c40718115203c81d1800ac082040050326400c0940c8010400d180000810400310142d140d214003800100d007003541110400701c20b0449074081030714140c1c090004820746540c2001500901311a19101501070300c078075401540c851407420082080501c09420000d44c2030b0b5070181c200b00107401841e0f4040c0e07071400403101580356000d141c002006401140c20245000c8081c1c85814102200010481c0c102c070302410450300e040c0c43c4c940a02d0f844409041e0701030401c0b48200f20612140034042d00543d00800035108880c0140d81e14401e408000484840d020a8400001960750555104020301600800f200303083e41d00d81440c65540503a540204800203052220200382500c03003170000c1d41540c030003000300302407640e0b00c4c1b60a041c01400300122010891040340c0d948041c2021502c001291400400200c01814500d6000c1411511202e030102d100307107184d81c00402c003103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 123696151 1250 123694901 123694927
    0xf10030e01060b0405040e07080615060409051e0c030411010c020f101e03050114010309081209030d05130f0b06240d060b0a02060f040311060f190b090417 68
    0x2e002c6049a04d4481341010200001c0d42d074002401c4041d80c1c06201c041c00702140102d0309a41155034103051441c603c0c9000c010500c140511b03400313030308410301d894100030080d8010704e2641500007821a10890654907910b00c41c0740c90006880180c180c4082d0a00b8107046c3d4024002510a64001048408607000140000e00b0340c520a0381c0d02800500044078612040413413082100c101aa107080c1407005604001c0102401d00b0301000c3c6a041545590210052026400490360101810103140320a032800a066035541d601581c00001003a1402c4001000904841c014852455011450304a04140c07501e481180c0c3c400a043daaa000d1200c58200548000c0c4083d6810362010b104105603c03469201110000c8508652002c2141d000800c01d0035079069021448503800003481c5e414007031586032800e084038441d58410154410f440740c5030922030016401402c0901c2045410707103805800114103c204140d5801c2918203405c1402040807800068280341200c0d052441c800700c260900038040c50b55 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 123697401 1250 123696151 123696161
    0x110d060203040516080a020303030a0f1509060501022a040506030309130504020a0b0301031a15060403051006140a0302061b0118050c060715021309020414011803020f10030e01 77
    0x700c2d00c0d81d0180d0ba1042004000c085894001c05d0301d48060800758085070080781d26844010144485181d0350703680402d42240b80e5106400001446906101e01c54a84055000406a50040d039025104c3c1c0a49802d002c45540f291a02d0680c2030301421402200c0300c403d100242402500455060009011140c2d01e9203400d0b02800000c0e1005e000401d40d401c01e4010300c960000301c0d421096032031034104014030216a02e00c414900d80260b1509924569980d4007091400c50500d141075503011100180c004203003c000030395008000481542003080650700c0802c2e1803031607a100343c2c503900300b81a000304002620301f82010b086501e5000d000c03c6400c00c144a40d0b217007194440240038024040300b8807004140701013003107801600c01c1c2c10b81e0b40a103022041d8403016a8840c1b4000c401c000c0540000b5524200800b54540b40300030305140b501076407510785520500d0f20400c0305c2c1c5401e40c000b0316031484600c603891000102d401100e0300070740882c07004100101804001540380241e2414140c0720201e8032130001003480384c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 123698651 1250 123697401 123697403
    0xe06210703080a1701170303070f02070503100515010206070e130f05090d020d020c0f04110903070b0a030b0f0906040203100312030912030c090b0c07030516031205030106050304110d06020304 84
    0xf0f202c1590180742c084c4400c1d400186c00c14107190030b8002c0c12030850030000007241c0d040001401c041044101c902000c0385411007540169405014400204050032780e903811250151080150042d08481140f004a07990a000c5075044005420210101900c2c100f64566110700c2402c4440401d142210840c601d060b81c07800d83c1c40b03107501d43c0101c000d100c0703082c1c0c1407041103518031b0140701a000b8044071070002651010043c1c4090701c115035840e440701041e003281e0100d90400300060283d40c030241e5180c030070403541d4120750241c101090800100001030310348503003604040c5400500c956180e44404040c00001c1d000104075010220714110007101003183c4030103981d00e41c2010740e00800e84040b04d01d400c0541054000490040c941810707a0111002c2d04044081c1c10748581040e0b1a0b00d03401400d95127441c061242d4005001e9002c0e00da40c1d00700c00d151015102003034078003401203d100961042412110740c4024451000090340900c0401c0000740007282044090100a0400304850f450307848107022644142c43c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 123699901 1250 123698651 123698657
    0x9090e03070501060f0f0509070c060903110d210f09050a05010614180601030b03100c032019081024030510050d0308090106150203040608010e06210703080a 69
    0x40c0442000340034007a0302c0141501751074207070f101490042c60046030202c42c02642e1040070071100142800d0320818400c0003882d0414424032402d0402d003030280207820202411251801255260b0b603000740107000c0803018400c2c802c040b1060590240748140241100c41201d081030b500c80f65502d0110f042001400151406034000281071071030040d041e1403200340645118010f840014513107d00043c0003c079150310110a0a0100303000036024000b900b01a144a80d0240a41c40d1105958055502d60301c02c40200d0b020513855030140441903808000c60003990781c8070143c0041d694905c0303400c62203810901e40004401103820303000c03601e903981c01114400b500300b03e600c2d10045040089080d949030207010b42103445080c40c0303100e0a003400040307440030240300c10180900052201295818100b5880003008010800d40b202c14001146402512a480380c072607900061030650011406c040380b03041060196030000c004000c05016103985603801701c0d00206c602c540c0d000b548000004070701c4050050401041d195 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 123701151 1250 123699901 123699907
    0x15120601060807020c010909020304050106031b0807330908030d0b01180e1b1b0a0210030b090402010f0302120a0f0e0304050307060e030f0111030a1b0909020a09090e03 74
    0x40010000c0c00c0c010302c3c0004640c0030300c40e80c4540340d030440b2049023524840700d00035a49541e90704090307003d071040341d00040c0090300b281452130f82c1d0784602041c0700035140a201614070455503044403800d104405012441030882c40002c02000c4a400140701c00340c00c0103414a084c00036605c1285038155005400701c0308003203858003801c282541c0c1c40900403040394600328031141042e040149001c2c06200040000012001c84418946542c0d505070030740303400c070544c4031501465000740242caa07203e041030341040307018860542c050012540207015840f400d91024003013580581d16600111748007020741c0d000038103040d820410200220381040825124040c104804507003903040004420807103000892000c4950000d2000307210b41d55000c100f00040f103566107040c900f110007450000f400c2c4844000c40030400d41c6000d00c0e0780c4d240c41500001d14840e03000c41c3c1040024910420b58582854003220420313000502c001c40c184040d0239140d0103060110034901d4000812a00c4081c200100e072106000542d5590000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 123702401 1250 123701151 123701159
    0x70201141c1b0c03110102130909050c0619260708090601080f03040e0c0f0a030c0314060f090403121103061302040608070c0611070b15060c120315120601 68
    0x680201030b80460259160154082c1c0110300519540703098000800b007101d102c03082c04000070709405448100304215038064035141d40d96500d100034504a0b1048a0034000e0303100342c0c040c5180030070545400044000031090100785545003200c4015100b45445400d20039404401d915038001b92036984540025200c0040d00c0c20304103021480c200050f80020400c2d40510101c0d0045140031003038804a41c480c2d040d2441603103c48045101900507181d41d00c0c10b10304017060480b2060782c50341104e4030b540003640b410000146003418102c020302c421685a50403801051041c0310768100a503c01e0b52050003840c243c6100707203290481c0025900103011030421301c1d0010091010600c0c154040094031800f0030400c5151904d4110064420030009182d002800800d00100d0103005050300b00300c601421000c4040c6d90344109103800030340c0b03000c2540c04000000e41130204108a007000d100311122100d940c402840c0081007202030311030b42d5000401652202c01c1c0355048002585031118902500c0e41610058003041d814 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 123703651 1250 123702401 123702457
    0x8070c050402160609020a03240b06040b040509040611031003140106030b16020f191401051915050306160807020a02011b030516150c05070c0b07020114 67
    0x8103811441c45a441001601141e9180000c2d400500f503000c140031031140c0707a60000030f480f042c4a80c03001e000d0410b190004a820b0b401c899000002d04c014450820031030350389600317001403402a401102441c00042000740854500f101c41700f54007600c03036100030644036000001d031004c81d0130a440c41131041c4070340d07802401086500051002d8849260000300305c980d19544484240d04805488061000400703044944950710a0010382104040b1004480d06049400d00080e25504a20380c00da484240030303001200c140b0818007540780a09040031681074060b0110690300000c102d4513601c0c40220701420b60020f40340d01d090099901c0340c100141101c0d04050b280401a10103140103242c0c10840d0040800c010050781c00805100c00c0d0281c1140d007111080d521701c1d081c0d8862082c20582000500141d40b48001c1286d009540c140c01c8280410a201071708080308150380500507200d0040a20180b40014080008044040c06800d40140b5105918911b0340308490130640c01210b0301c0419001060b640d1004d40c40c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 123704901 1250 123703651 123703673
    0xa090501050a05011b0305070f050a050c1201050f0a020d021201030602090406080a080d02090103060e040c230109031b050603010f08070f0302010e0d0c080f01020c010e010203070504150212070807 86
    0x1800f030030700c1e680848071902e04170207080e50400010300307018010418806026060041c500043d9000c4200c4400940908001d56509821550541f0400110801d82481007042c050513000301142038161906813202541600070750418000003500680c00d01c90303000010003549600d402140203002c016940c01d00d4900340826111103401040440e84082c00180020b1940c41c00c98001c420027000c0140c907a040140101d000c1c1007a03170702982110202500313100a101d58132200e14101c80c00c0451440c01400320710181141488855010380c04a61000c1c820030209068041c103005c140040d6099209003521440021802d80080e004058018120082800301201c10000b5501400004510682070b41c1303940c0c0020864402c08a48500038011a00d8640801c01000420805044040d0940369807421540001c2c1c005d40140760991341560130104d40c40c000f0320040c4200c0c0d0003040c044d13840c14603140c00e00d4115516200809841021403052420820300c20300c110000c0c00c50341c0e1180407055600c2081e070034840103c075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 123706151 1250 123704901 123704909
    0x3010c0207050907030207080403020d030203120709060c030834030c1d06090a081c0e2704050708010216020103050f15040e1011090901141003020906090a090501050a 73
    0x5403100320700780801d50b2030380303031980d0f00040503e4090f9460340c2c185040485030250303600007500002000000420150003001070443c0856002c8500c0c216540c1e890304031200e8046114a101080882400002207172241c039200ba440030031407404030300300d400e420300284c0d002e001081c04118494030701059400641d071601a140e0b030b03a4118586030200516040c21141e403040c0780d00106d4850000040c200c1c13400d859220707000005059003410f4500301e17600c1030000000015003d00007030005045103090403181c034120b0841225043c00d0300141c90040c5080400c0038007044090025281882003542c0026202d1090008001202c0c040c40c8000d294100d03032001606680700034202c02052803a4004020b0300b00340d0b200010410200845000c070711700e0f400141d46401c0c01c4017003a48142286c01c100c540b00000c1400740040410382001d80d00b10403032742e80c0c9036041c1c01d404200c01810390b480307032826803980c83c018460b8002e441382c02d500803c1c0c5460311841500241314202d0552000b080591a83c0040000d843e150900e00002c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 123707401 1250 123706151 123706153
    0x2010b01140a0f0f11070b090a0b03011239031202060f0c0a052106030c01020d050a0c020103230414030c030f0705010204030206040b0c0606060906090909030d0207030e03010c02 78
    0x10810b54003015000c022a107144801300109207141c00911341c0315000c00b48035941280140d60b20a0f4450404440c15031005010314018180440005601403401e8100c1c0d0483d01c8001c2c00c0d141490042e41e0300d059940e225480c1000c0b104640d040207440c80c80f01c1441a48000c0c0785100c2070046855458034484c0c000d210340340d810a40d000320301041034801980c0c00b01c40e4001c4d8007011207075454501410961341406041c04604401c441540041c0040e4549854503000328402c6089480e1610050300490341c0c0c5c061071242e000010001d2085440d000e000c2e1082000b202d10504011070640070b014400d0b056000e031820600130120481040c1300a02038415055140c001c9054082c2d842c10085c4d202c000e03a00d00caa024085001900040c0c04000d101003075041d2005968014003003551941d4403606003000c0e40241c546140140958008a016403808a044407541000034100904099110040080051000b8010000c60000700f000e6280c4020501c000c0000c18841e071941e04000c0400d0050500315036100c2a09025 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 123708651 1250 123707401 123707407
    0xa0b1c1a0d0f1110110105240d0203120f0403020f0d0309090b0a05131b0801120f061d0a0c0503010b0901090b010c06050702010903020c0901051f050d0609090203060f15010c060908030702010b0114 86
    0x230950247c010000007403001e541c02e024444041c80881d14210302c017903005030480720100da001d07419100d03e002001282d0003243c0200b02c8251007020011180351145004000c640c0e4807000b0040308100307801c4603109200003400c45043c1a660f0001c00c020082c0c0c80c22a440813039588180c240403989080321210400f0b0130307140c41032056050009040814042420240580d004400500e0400c011500103103103c00c034008240c034a10103110072441e66000b15140c200c82d00403142401081c00e05052107282480b150040c407142d0241d1030848010001c04c0c0100d1517034100407869003c000860300b01c0c0181401103015900024038800181802420074058503900d038410080f40d801000196141e54803540780d42c6909580307101d02160060151103610601c402c01c01c01d241014130000d01640940e00130490346000350b054900c1550b407904207000c0d0107011504003038920007810f85203505500c2200c12074805403003181c0019140256480d01844e98208a40d4080140e45076203400b00d2650740403024003400c4405040b4141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 123709901 1250 123708651 123708691
    0x70305011107033b040b0d0f0c08012901032405040b010809061501180e040c05010302032701150b03100e07020a110a0b1c1a0d0f1110110105 62
    0x940303000301c0311341c1200410030883c2c4082035642d03a0340540329041008214007000c0c0036614107404035041e103e2040d1742c005814540010810010b0085501a4408c0f502011a00101c40309548100f960000258100365031054041c02e0346248503120240c52040c4910740d01d00c20310300703c20401030f684021596030400c82050240300c0850000903400d60010000022041d01c3e1600d000100c0d00c00c03a10542d180c490030080400040c000c10148082030255020303a0b088a2510b03201c00c01075059101c20b541880c240303180008100d8592480340d50348142c04000c440080f6001e0f240c00a160340c9404590400810300030300006014612140b4500c4034002d001410012202e8640b200c00a900ea040321140540b4500f0706052188855603103107c10406400e04506050721030540712201407040c010300a0015869150041d61415000340e070490b208841401032501180c507005540d88908030741c035480100c40c140022501910a0360b1408000d04844c4410b60b10301036803c560601541c01d6039405054601c8c22003611111503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 123711151 1250 123709901 123709967
    0x100f0e04080304050a02090c030609012418090e011a0411030c03061804140705031c11070302060c060406060b04031a090c060310050114030702071707030501110703 72
    0x3544640c2058100303440303664a050460030011103100007940710302c01904100d03010034145c0141d07005410a1f9030400f02e40c0c1c0c071081c036100c00030707c0c0c41c9140d00041d181c1040640c5140c441e0a12100345c0b00b00b84501b0752103d0395103921809407000344005450a0751078811400c03605102140f41e955104041b030302402a8414102c1d006c109203c0a05880305c4901c000001541c907888002d14048916828000038400d0300c1c007402d201b86040c40781a00d2628601884400240710f2500041c1403828841040040c1c103003040705802074a00c801e6000100388a030007134070000405603a0781000307090820140ca000d818686040d160070000c4446640018a10000500060000c00c014600852450400d03401c01c405a40b01c2c4060b0b9483d061086916a5100038000700700014040702ca01246c08845007a04d0f102c040c1300f4622604109800100c0c0c003400141e00190301004070440d0a144800d07400000c5094800c00c1c0d8aa40b295070130b4506880b020001200002420f000f0581d0003030404500d010003044105050704054410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 123712401 1250 123711151 123711179
    0x1080105060a030207080d050402130b060901050a090b161e030f0c08070b0103060c02010b0103050c070f02150a03060e010501030c0f20010e0705010228020108070309060e06100f 78
    0x740162404103140200500a42c111120650462000c5498005840304240034000803203049008000c000214a035002140c082e03d00300c110003c05c590b0510006600440701600300e080b000e010014186800114102254014840c0c41e030001034a089440160404600c00098186034542c500c00c0c51003184080303a0301c01c40c00455030940d850524444401c07418a841c083c02084000743c0b103900c0c01070000041041d56808804000e800350028841001a90f005400b240c00440c0c1ca403140c41410001d207800100707000242c2c0380f0741b48024a0034080e000000c0030000075410405a09011a0740c8a4082c400d402000000d60f0051109207070a1000e0444200024020145040d88006103d9200c0f00071602807401450071000d0030000c0001c014045001c003030300c1c0ea581d100c0e100c0c060260051120700b42807207114540458184007240803801800556034011100403030005c144808043c1d40d8660003001407054000d0f03050f00c2d40290000c0900d41000c100c01c10080d01164045106068110000c0103049036105207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 123713651 1250 123712401 123712409
    0x180f0302060a11060a0906060b07030818073206090310050601020106050d0501060510030e1506030c18040506070201151a040b030717011a0702061308010516020615010801 75
    0x11942d00d52403080420348464403420180300080c01290100024403401d54000c6410354000c61050003525900e000c901440d10500300c01500040034100010b45203800c03000394088014040c0100c480d05955100c0303100d50f851038070366110348007262541d03580303110036401e500700900c02421165079180640000000743e46d070303d0300c55208500303c1d01c640010b81036a0013980400300816010b44800c02583c0d092904900800580c01a14810501001503200ca54802d10603460900d0383e0b03400600020107802c46900c21100000c086a40c548141c03650301c5229241d04110085407581039584100a05081c582942400350043c07030348086a1401061600c0a0650b08c448400c88101444003289012550034541a42c0703da90415580610004188298194418041007417070402100d40e00c40ba03601d40c1c1820b200c0c20403006001c0100d140900c000000b5181c00d800170f060483da0041010445661000b003a42515400c45540d080040c0c080c00101100d0f070144200307030b840010b0305081640e200d08000040c00b101c0046c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 123714901 1250 123713651 123713659
    0x60906040b010c0503040801060305060a0509032203060f020316110601060c03020c04140919050309040b04020705010f0c11010207020a0605160804180b01020c10030f140406050601180f0302 83
    0x5900c101c940d000b003040f501c1850f08201520343ea56121019103018120342d01c8112640d100381000281112043c0c8038442c020300124005c0d518002035006103085103602281c10040b4845c00c0d003000000121240f01d400042140703c6005030700c903c1d01910103002e0016852480c014003401c1c8a101d503000101146881c10746009041105a8540b10300b0128544002d1003085a040b07031408000018580c00118598814050242242c500c00c1d03410798105100c06168070000c140d68410301841c040b40c64903400206024034050801810542591101d9094550b40885541d00c0d9a449034069200d6521400800c03c28101e0002585031070469400724a030095548145020008041610540002c41036000d03000c00360819640c43e21191240085098000201d200c2d4024034680803100042d94008201984801402840722031040d10214040c0c000c3c145410103400c071b00d80d9030742c80419107410048549010b00d001d84000582813030b00d20300240c010114202049416030409004111044030640d0020642c1d505403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 123716151 1250 123714901 123714911
    0x6060f0f0a180b03060109030215120c07050106081c0f0e0d03030b090c07151d0d030501050324060409020a0f0b04180204030b1902070f080706050106090513200a09080d030506090604 80
    0x2a00710250303015214462f4008113801060000440c42c68002c0c0c030b040d9000c0c02c003c2100554a1344156a110251411840e01e03a21003c001c40e2001d00a0020401c00d084600786030512014080000d45980d003210340031000300c0d0b540c101d4140c641c01c1001c045913000001c6c50485140000c44d48802c4d4001410303145218109403650345500d0700c4803000c1b41d298003a100010454642074149803011300500340901600e40203100d10600741c0f004c07000107140b4500d08003000710780c4881d64070740505010240c02e019070240d0b005003142c02c0c0010340e00049100840144111400e9944460910020100160281035107030038060040c803040c030101d501040c00e1500b0882c20a01000c1c5d00f01440556800388c0240c0a020340315964540f404424003140300300034441346210f001c04104507a2103240540ea0700c1441d002c0c0315081507881070303120341000660340020b036454540500c20440382e01d59401d44800d0307032081c01900300040c0701300c408200c400000c0141502c00d4000741001d01151500381c0218481c484020480da01c80c0b034a41d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 123717401 1250 123716151 123716179
    0x306030a0605040804031509080904150b0c03041707060906120b030a030e01080609010305060c070c08010f0e0f010216200a03030305160305090606060f0f0a180b030601090302 77
    0x401440d00100e92200c814840c1d40341600b0407400d2034120384404c1d20800d44803101d000d080c4407948660244660f01041140c100043c0500380001058074104800b0700e40c002c1c480119030154040c0140c880c0c0e0080c0c40045036114108594413030103501ca26a2030f401c1d81c0c02400140030290708901103105651140c07400402e5aa030581e90798002d01035a003c01505801130030014018035502c5030f0b0100101c80700780c854034403945035039061064001d02444050619042080480e00d0307031240000404940380a00c44000c681500c0700b108a08441c0703441e000b00919a552a00041904424007466a03500f200000031810000003035042603c8210540c4020241c001c050706981c450542d02d00f49111200c0e0241492040589034580039004207403e90f488403041c0769030221a03c4031486801694403071000000070701040e440702400d00c5032135045121515604081442900d1014030400c0142061110b0b40d51008920040c407900b100c203540d050340048da0b610710100704110781a40c0094140d011680d043c0c41e0b141e0601c44d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 123718651 1250 123717401 123717403
    0x50702030d0e0115170604080306030109060501140306010605070309140a1d0105120d05090904020109080a0b0a06060806011b080c01060b0d060b040e07050a02070515120f0615030603 80
    0x3414072411091881e0965100225805600080b032010218400c0c0b4101c82d203444081100039207220103001644e0100c4002400148500051a04818064008100c062841e0b031688240c4d4026001140c91a09145400916103401c000d43c2d8010081400c12038500700352034400074400400340c0920700c11260500a1051192121000440285908070002da5403c06074150040040d03400c1c450300b44103039201c2c0c1218554071f40115826090440744c0d22658901100482402890070b0001e006038140b00b11000006100c84d010b10038011043e11516110380b80d454589480c1c0c003200e04540240d0b041020307401c100300080c0d80254101c0340d0000c060111421180c0186003440b881d10421819418035420040002040080540980031348040c4107014000641c40300540980c0380680d104c2e143c10004a03c000c510b585000d03d00401c007038040c80c4113480809072a10049454500c50010741d0206c041700094807103412000b000e255400c200c0007004881c0504021001079210300e403000c1300f0400620b0020102c0e1140d98 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 123719901 1250 123718651 123718657
    0x6060405040507080a05010915030303110405040608060403110705010f0c0501150915080a0f2010120c0206070504061805121c0206041a0402041d1e07051305070203 72
    0x80c000340188642d01d0300b840700405011007903c056031054105000464080b8075801a01400800320030501403040c03544d02c0c11000740540d000b1402c14240c04001c081441d0302d07075006550150086800815182c10b241c54014998a4000000490f070703040448107201580c0c0c030400c012000e56007450500c0d00d41d0042d040050051490f007142138400803201c48000f6034181c441d00320300c0d04040040302d54220159210820b60f29600c0610004008010034000f6000298400107510303078101458000d0805000100301040c41e0080c1178004801144001e4000101442c45000b100c80d24144c500c0a0107490900880103442c6003d5070141c0070a2020210f028000b078409104c1e1140140b5000b003901012003040b002081d2106581c1c4041440b0050b40140d6601c6a400007400728081c1e0303440000140c1824181a195030130a07000f400490f8015101d0516120310060041d1110101d40010080e02c0201d089010003901d05203100e001c648590410242084681d403003128030510307c03103480d001040d250b0751a00100d00b988 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 123721151 1250 123719901 123719909
    0x20309120304050c100e0a0e01030515040c03050102070c030c080a03080721060b03010602150106080103150b0301140612121204030c0203120717030115122705010609020c0d08060604 80
    0xc600c15184411030b584480382062612047d5000c00440d43c4541180d170300403109001c00f400315030103910801000301c104080254018040c8420805081d00c0341d64140c01d80e0b000050070b44001c0c0b02c501c028024041115148d500606560004029039081a5406020341200804400c203028580c5034111640c42420032b40c40100740ba82e072003000000d0b12070802900c03a80003030041c40c00610545032000c146002c0c0c0d1031040d050306c07455200e07001943c0c615555602c0e116800c402000312a5111480c01519860034003c6070740704100204241103d1410718180034072119a6407124030181e11240854807a02c0da84411580401d01c034103141d000964030b5040039100c080c03806030029090711a110810408100345006800e02034400c0720903c0d02c404410701c020601c0d010a010340e400d005c0301804202599802054400d040182c08240418039803c5010180c142070610b040c005041c40760040c0c0e91b420480c0030b100e580041c0c84034080031410608881e2249a031651500410300c1030040c69400f06559a4418041e20020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 123722401 1250 123721151 123721159
    0x1e120b0d03020f0606060c070e10150c050c040605060a14040b0c0307061401061e12020c0c040f2a0e031b103609140613020309120304050c 61
    0x4500d1528009507200d0a00c11800802e000300d07004981d062801900b00c4a0b800c40742c4e00140070041c10000e1481240d60080c25000e500710900303800040303110f10440003404c0d0141d1a100d2134000000e90901c0341c20884900452803140f85004002e0020fa0345020542c0c0d44ea2242e4035140300114800d0003150700f54451608040d40c0a0030215a50800700f0000008050040c1301c2c060078000207800650214040c8402e000b07020224000c090315100c0c5000601400c110b202c854603080d600c00705075072480000c90303221017102c07032040d00400b0805041d41001e0103080c045c00c0d0b4490041140031404116000003801d04000104000d21002104110310712458608d480c00d02c2c000c054440d60300030a14a2040c50700441d04c503d01a9071485420404035014510408844c00104030f0040c1944800301c0c030100000c001d101c550914070300d64802240c0294148941c0d480d00648820030b40450802030108240c10700043c1c008003049004104008200b42c0115400103900c00e107603644ac3e140c2c0c440b8076145080c214000b48075a00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 123723651 1250 123722401 123722419
    0x3150b030906041401090f08090303090910050a080c0f0d03170a0212070203030405060403051b07030602030403020c060f0a0518130b040605030f0c1504030c0914071e120b 75
    0x22950021640b1406188900400c2c103d00d903500c00c255007600d905410262440c0c80c00301405003c9101d000040c129000d0040c213407031074003101b80c00080c201c10090352032440c03000f8028428002420081c01d40405032002c0d4004001040310302000031600802001c0490040200079141710826014494840c2c00824003031451043d490800703801002034002c4034880d040b0409410100340d58500200481e03000350341200c0034040c0d82c1d4131510700361140d0340010501121010842424820200300f0b01a940c040c5202d8400541d983c2001c0c01d000b8542803a03661041d108042c10090104114904006c40312054202e0410585800800d00a4002e402c81c210000750000c01c140028507a410283c0d00003685000104c0b010491103440d001071564449400240b990a0391100600248900d461070002e40002c0c0c0d150320385440d2641342d540702d07400302101c0d5011018064442061106000200e02201d0b88020549440b84100e486614124110b40d24410b400303044c0301c0b410503e0501e5521a0700a04c49510300580340000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 123724901 1250 123723651 123723661
    0x5190303110a0c0201030f27050309030f0c0a0f0509070c030e09040807030306080c0f04110409020c030415020d05190905220513020a0e0703021c0c020d02120a03150b03 74
    0x70740383c141c0d141240040d140110301554603c10703224220075051461402c0340a881102012030710441001e13030658241c0b10600207041107603000c0080482240e0040064019884100b062019645140e08045900091180244807640314a901103a1126103450300380a00c1c03003a0300b0700755080107802401a8012002600300418001036800506100b48269010814980d40c1e10800e612030240c040d078160f0201030701c6604407040c50140c112018184082400c1460300390703601c3c40b040c00c90740300303001c2d003e02d507000031a00f000301041000c400c0000f0340315070010f0314041001c94030042c4184518001160003110350180080f010b4490f500400141c9000b03400c40b5000c050340c085006a9a58030000e80c401541042c000032801c80c05e140702d0490140d409800c050b000c0781007074440c18240c0801806c030400c065090001581030314800c1040001039619550000314204180002810514066405410b548c402401e54122600354401c40d40c42290528001903201030300b03410300c045501c180e031024074241c5000c02485 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 123726151 1250 123724901 123724907
    0x4020711011b021905100207050f04020705150a050115090e06010302031312050c0c0312070b041505040c090609020304020904060b0105040b030c25030e0913140c01080606040305190303110a 83
    0x44e054907011542070920302c0344140100c0c1d9035803103030040c503820072186030007141c10307003416009081d41ca4402c0c401d50f03451444074008031045503c2211f0b44455030340c643c40104100304c0910081115a0f040786000310f40c060500445000702d110103054030341016800000241c02540240884844991024109140000000c1d005041c1d4000004d1410b20303010b0040040c03c1403500140c1c0003080d02420303141604204168441c1002642d004200303540310802c0400130b8651040c24820305104602c210980b15440d42405031120495405030046c4094501c10402e000c0075a907101c81722a4000c0c0e2044010074810300c13134130040340c080c01241d002c1241c8440100c10702c03200e61036102c068450030020b0540c0e89688031071141c5c0c01084c000030303640c050085071540070740301d245040004120380e010140d050280d04103821a46d440302030041c806a00d13440d58000480b921007660f8000411a00a0740803a4464209425511000d0720360543c44048040e807005000042e04240c081c2d0031140706000150850360325198451006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 123727401 1250 123726151 123726199
    0x5031e090c030706020f10050a24090b04051e04060204120b090c0603040f03080a060b0d0903030c081501030b0f120a11090411010e0d0c0602010204030204050604020711011b02 77
    0xa5403003801140f030b011550070320001da0041d100e40310500030045a50300d600c1304001400c0c080c20103440d40381c56047e0803500c03444455400040c940c501c220200500e103020070310400c41b41051300a9202ea41444184201c0b1100c00d014107040340c24680d00c503075890701c6500e4000020311540d4481e00c4001c3c240d505803010700c5401e01d1141c3c443d48840050721006151a001c02501d40b204075401003484403030124002c00b1034440d404581d4414007103032001500b5511166100c40c135400001801c0e402c030741c54401c9a030030944d05014600d248801d5040811003424079011880d1408408801941090b94032038032900c09a4600c40000c041c0c00300980350302000c4417811101601c4004110055459046007000e010b29414130001441c1b1943d000040c40004a11500044800c081400c00061380640d22020342c00104030302c40d4038100103207404e40006940e00d14600c14041501c1c00146011710540c410300050020800d062601c60883d1000d181101da900040e520060500c2c0c90810041d41060021540c607840040081038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 123728651 1250 123727401 123727423
    0xf011805100c1b11090408030103110909030d0c0c0602190906050901050a110a050f030d0c020705150a12060605031b0304030e120102071a0103020a05030307080301030305031e09 78
    0x2500c01d0074599103528070550720300000550010700b141030005042030014441e4400360f44503007901c00700715001e03000280030502d080d0f80654240720000010000c110310349220807907111041d80d034840c4529220347c030075449008100c80b08900320740b070300c0c03400442921941122500c035902500441d1a480302c002212101e2071500c0000300810840c0c503012a10345c0c029001c0c0c4250040507900d6910b030400020080300c0320700c2c88040b62085446100d819800081c010302c108a01094910b00175601e0306042c1e0030400a852500c0410000e5401c00c107006d0020f521401980c103941c04443c1000d50351341c114104101c40c0c00c40d0781e8003841d0001e413a201000c01d000340d000f0000c41c060075400520400c0a440070720600d100c0d200607074004001c00d03414968001142464185c0d01d40d40481000014240103082e140c050b41c5611300c032540d00c120b0900380c00500c218070b1300c941c010000e400168000d6041c022a50b039800410311044c0000f030709222001c4000fa00c02d003801505003402c0b111400203285203040001c00e80356070f809491a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 123729901 1250 123728651 123728653
    0x2040608060a12021011010c0201090302010b10090b031005120f06010611060601080c0f04120b0702011103010902090402040f03201e04090f0b01030305300412020f011805 75
    0x201090003841c240490300290795000c8070220f41c0c0d000c0ca500300013502802d1082d240610880c504c2d84210882c00b880744951049540e00045244121454000e00f1030f000c1208407032250303206043c0001200e500036400c03001e98201308182c5549460704445448a60144d40c03006a000b1550220f42100302404269020402c5030b041c00c85aa59803102401c0d00d000d1800c0c0c5d26401030b64071020004000e036205004072030304904071031400c500d401c4002c410081d540e4000e41046007030403464000042080800b81c104da60008103403000b08105003080000d0041884184100401c90780c021030f01182aa0341d80c0d04480040000100030300750999240fa00c4591501c00104241c3c0c8442c4519040886040c01e0750078070000040e4003c80070070f9104000400000f424a07440583d01486800d640100180314042418042c5003ea200c1c50f0b25001106c1c510000207810709106400c5824200304041c49010710804550400da000d441508280c0030808102c1c9001c844c4910f40c1d400c0e6007052008007104a500d44040e000c04c0c0180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 123731151 1250 123729901 123729917
    0x2180918061006091a160620040303020c120604030810080d080a0f0b01080705130b040303031d07080a020f0301150902130b04050a030303020c15150405060d02090c0a0203160501020406 81
    0x81c1d440c070f0714141070101e50350580400b040b031b40120714031070381c0044100f602c01c007000180108c40d070141110000c01000c051036020000034040c0306060f010000b0382d03400b8004036004010802920301c4e148c1c03540c0c8040c200405001c482c40100b000409070ba202a00508000803c450142224180c02481502c0580c2e140303443c6854604406076030500c0d4084c0e904281070603114464140c82c0e072081201d496000441c10192041d0101001ca13503013003070000600080d8080e80e000f0444e0502103422110f10a51259100c540f40d218480420a0541c0810352110098040301d0b004011381400e0042070140c21888680707402009900c6011804c4112a03000d03142d0f840d14400c80449660300e444050485101d03030f001d0180e2200c24114100700191180d0010581c0807841408d03103040c00c05485403a19610700507900741d0f03003c0c400701d01e815816080c103105559000200701c0d4801c01c0c85415030007003200140301820314001a4800107050044c1c1e0300800c02c413003225000303980302e80c0d086e403d600340381d8001c3d001b600904000400701 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 123732401 1250 123731151 123731159
    0xc0d08010b16030e040f18020102070b070b0a02030606070203010513050d05071509030c020d080307030b090601080f06040b030708060f0a020405060d0e01140a0f0605040218091806100609 82
    0x21500361840e0b0940100322840c0d090403900c0135144d02c03903400340c1d05034401d1312400341d00716030042405500345010429034010180f41041c800603041c0780c5150002410010184035910204520789944e5030000c0e680180140d49494003804901d181c89030180c06500340d03081070300384030491141450b0b880e982c40c0a241030380c03061300304250122011304c80e8490280000070451006030a0050560000c21800c0c46030405110510095001c164001215481602c00ca0000700c108143e031900344c00342c030b1440207044428000038031340f03c40040c00d002c00c05408040305912840004210341c88070740c04001c0b00d80d0004d046840c0c950751122240c1d075031102101c0505101c034000b8045902d40d80300380203540594070000d05090400c0552030146004044039074180c20503640351419900708054980d005806400c800c100490b4410040c507804098460b15404140210310401c8030f01a80908150307602101401100c07100c0803600c0d040c06903018195111101c1e103076805a9810700c5003580303091480004440180c0c07154009150b503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 123733651 1250 123732401 123732419
    0x20c100504051c0611030108122104231b190506030a020f04060305070219020102060c0c01090611070201081b04090207140d090503010b04051512120c0d0801 69
    0x1080865004110140000e1280d89494401c400030503c1c8601200c50100316611890242c3d203460410803032400c00040103000c04e401c2442200d0031009188052454211044001789569803c103d40c03445e0a140c410104041148001a0030100b002d0303008000e43c0c440950030701d540c8070100c100e4108084e00e941c4602c00002c0c1054090810f000c650701002404251400041c0003550b03100410040c0e00c142e08200c0311000002450140c0050582c13a0b034000f49620300103402034074044901c540c801c40040ca991915006031390002e00d080d402284c10180507240d0301c036104021b01401a680d80202a54180b071501c6220071190000f03004050700036620f507d180e4031941e104076800c154445152000c850100418400501c10340c0003030003000d10403c0c441040381a461646070030143c0c0d05107030303500080000404004603d001d015503245420115410042c60501c0d4084002d0761000c010b040c0d010f40710f0005000e64681041c000301c02d03820745480050395034550301c1d060350b501e0b4a0070f03020810110305464004113084030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 123734901 1250 123733651 123733669
    0x1d070807120f02100225060806041a0609011205090307020103060510171510020601030506012102120f0d090e101508060415030311060c03160c1b0806040201020c 71
    0xb82204110300c0303011103a002d10210398103880aa20561040061254078a0028580012280007044003080306600380700c0c0040074400c000c1c00040c4554103048004519041c600101c00004404a13501c55940c2a6800180c61404910000762202c034500420030404450210003404200d1007660200b00c0c04d038a480130807101141d102c80080c0003620790308441c2c0c51030200214490f0025200c000d02010303070b044580069040d0340c0c00c004003c01604820010020040104400341c05090030b4400300c075010048901c41e040300000d0f5031010b4410054540078035540e520030701940d681240303400191001a220a080031302201294495003619038032210019000d080c0d64110041503030140c9246009500c203440c01100c500d00d0203807171154416070b141054400b0540307508803580251b22039103501c000302c40c40762400f03410860000c0c800d0721254401c004202d0160b90007500000ea80720642800c20b920748090400341446030840040c24489007078036101017048103001609611881c800d03400c42e55194120380130720050704 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 123736151 1250 123734901 123734903
    0x3030a090806180601180f0501080f100c0f1b0b0921030402011409040b04020a030c020c040b01050a12020c0607050d0c090303052506020d09020a0f0602100f1d07080712 74
    0x20700403000601c041080035031550405251b10b2000b1400d2092002d5003c11200283d010303890943c004158400e214070b05001d00300c007003461210100b044c882e01c0e51000e803010220300031900030001160021058456194802c06105401c581900b1301c501e045e001a540d1068412074a140241d0104580c2c01040010411a0700c910780c10381d105041402000d030090340c107801015515074003645407925040e50341c903144054108900d869801058098850304080e0802c041004e0160282d403e040d03503694240d80140440700b1548503844c2a0b9148075000510b00024010264000700b98000c00c4140b1840951000190455070485802000000b140718002c0d80c0203d41c40c80001c020440a024030000c18101c4041507440244240b200f0801c0080c65484504070ba0090580c01c000b10754030144c800c290b060500c02600070b0028603084100050030588007139582d26400004070026030311380b085190202050741000006038980a0203250000a141d00561542218010011203118120340000c0c42c51820400044a0b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 123737401 1250 123736151 123736153
    0x100603020918040c06090f1a0f0712020705010e0312030103020d0503130f05040e0102160204020c070e0f15090c0304330509100603020d17160c08060f150906010e03030a09080618 78
    0x7051511071845230f01e81025100304403001042c40400007080144001c21400c903405d034003600409003804000341c001401003c03071501030b40c0241c180c909100b0340c6600700d0b41500c0d011202c01400318000d2511914600c14011350145008a9a4000800b403030070b0f401503825907000300c03402d0242c1d00c4080c040034200d0141c214204e0550035030540001c00750030b00e03900410030601c52509540041d5141e0314420b040d148d007520b0700d145406002d810000d02007840440b501d20600c044901030080c1c1450740300f080031070002501c041c221141200c102507111005006403000344510804e080784201d0302d005c8400040030126610070b094040c43e42081c40b1161540f00e1031058a6004011460540c680c0d200c8460789031007440320303040a07102000300341c0003020004c2020b0307803c9100718211828541489080c9040c04800780c014415100c9001c1030002000900d200c7c040d196400303550140f0b445d42d034940100e4583d0403002031250507000c0091140714003580445024150341c4000d007100e04030344402c0400c900707190031400380c0c09007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 123738651 1250 123737401 123737429
    0xd05041101111c020715020f010c02030f0a11010b040e030c01050609010b1c2717090904061503150e010b03060708040305030c09100f021005100603020918040c06090f 73
    0xc0f8090000314002600c2c0e5074412200142d440721400c0940d0705e01c400500c030160b80424030058141c1c10034062803083c0c40300c40c400745052074111034600f90702c6e01070901d260040c800540080c50502ea000d500091030098001e10501c41c43d000510300e15281d0340300c1e450350b001c1035085c0400a580c034103203040b03460304a401d1003c0c1c541c0b034a90034141c0091409a40d2180f00742140d114114400400050342e502212002c1440c204031403c4590b1800b404c0308a0f0003a0424918801407000c1019030b6142810321f0f5005802c000c000c03802005105616040010b643c01c0101041ca0314410301195244543c00131900d00505002008802859010540d40d40e90844034000082d020300b001400080c0300d81302450b00074035504a8a414072160340005000e034082c00e81e103480044d000c81001124250304004001c0343c0005840c0800450604400a45071407105018010078141c000825001503102e0140c0e21100e8070b4284018030315401c0614000204100f0b602c903460005981d000042052001d203030825085030b007400c58100c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 123739901 1250 123738651 123738673
    0x250905040e01020c0604051c080c1b0c0a09020c0d0c02030a032a080a080112050c10050f0c0304060e01020d05030601031505030a0b010e0714070206090a03080d0504110111 75
    0x36242a40030801e00b55000d21625040102c108400c5d801148030b10041c3c1944142c04004144100401c803404040010b1071003445002c03100320003140d0983d2501c141d010408501041c0711481e006d42d0101d6207401c803001c000c0014015217941c0c081c2141060850a88441903100a01140d02d0780760f0a00c080d505400800304d00340001d005a4404101d80c002d1207140b6200303800d40410f050703007801c4a0710070b0f030381c10400243d2182519444400140940303944024841604c1c5540c903015030390103c000c490390040540d081280c0384240142c040c2c803c00305036012081da82d094007a43c940e071a48c01c81d100380750100d0020031100c074075980042443c1c041001d41b95981402d541c0c03030700e004601810b8401207042030202003840201e07242d28103115a21006003e40c295201c1540741c5400c140746098020f11000400070f08120004010305480b0403103100030b804450541e1291030120014040d005c0e20780c0003c094010024110050700d130b0345e80140b403045015022486c8404125001580c0e400c0300d041c0c0700d6a031038002c104080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 123741007 1106 123739901 123739909
    0x10501061d010f02190623040209040f11040207050309090c030123120d0206070206070305040c03031b0606140306100b030f0903070b040b250905 64
    0x1a2541601a0600103030411003000103040020301070101c0040c0d842002400d200760b0402c0c45006182417180742c840c0061401000c00400b5241c44284541e131040d54140c824481c030f0f0090140301c83c40d500d5a80e05d1142a582c01790841c1c03501803031440e00c2d005490b03d20107000c081d8401d00080d6030790b40802c0d007003044112000b8002007a0341000c00040c8203200c48404c3c1e50500c140c040c1945414107040400141d04903c8880580c0350600c12100407104860340065214005c4146d42c09940705615094812001d9a00840e00501070440c24176041000a00c2f400034400540110341c06980b11210994444060341c207603500812400307030f0f0b100c0d1f01d00315403509000e69504003508200000c0c50900c1c02c1400409408000d0203070315901052800180500c2d020704c04c445c2c0150380711081110b01e1800d0319000e0780c4604240c665040c42c0c2e4110710b0728038000c414601c07002503604154841c9604146448104 = true := by decide +kernel

theorem cover : BRFrame.Cov 123561151 123741007 := by
  have h0 := BRFrame.cov_init 123561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 123561151 ≤ n) (h2 : n < 123741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
