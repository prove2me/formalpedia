-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3865
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:54:17.684985+00:00
-- url     : https://prove2.me/submissions/84130a64-b5f6-46b0-8ae3-446f6dd184da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 694964028 ≤ n < 695143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 694965278 1250 694964028 694964069
    0x606060e011d01141c0c09050315012705330901051201021e03040b0609040f03180b04081f0b030a1407120b090c01140405190302030109030216050f060301 68
    0x40e10800f902c03200c005d170024080b1800d0580903228644c10013001c01c101c0440420305040c04200c5a0076081c1300b409001103a442c0c412030104100b40c40074080d0007140503200403144001d80d8010135004045800f1b41d1410500c540c1c84205c1e40741c07440c3d1100c0305554040c0f842002071b030305c0348511181103403c121000c012a014a800e124068031860f404400100045811498600614805140180c0c05141c54201564a800c2440346c03050054401500000615050700300081c0f042c80100114001c182c4c9050906a446032441c290350850341201d001d43d04112218003c941c00c0c515168642d00d424042442500785200c013003902d03904002e4000c0e012004d1440c01c000154810418180100800e80a1a060248034245020b070f00c00c00f034035020a50301a5089003451988201d104680c03c10304488100d15142c9070000300403000c0d0307200348500c990300c01030040000583d60a2081c018014004d80142007900e01c08118070f0f0b024140c075001648200246080151941c903030900790707415180c244004002159000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 694966528 1250 694965278 694965317
    0x3090a03050306031e06090d05070213020d06030b0109091e020a0e07020309152206080109020a0c060e331b0705010e0714010903110d021c0606060e011d01 68
    0x3c0494403551700452640e6200034001800340d1003400e243c816a80800392040b4112610f1180b0350b0040e500050b00005812040b080e540200700c004440300c40082c0b4a982c9584a80c050310090f8805521155a6401d01051065000c202001c0c0910b0450700742e0743c03080660000b4815901409060801840c1d40001140903008004840a403040200700400c0030060140c5500550b004048120100701041040c03070007094107a041005135134054648010980c24604a00000e4210210390810491525480030104245101c2c80c10304400d244090400c1c000c80003c003ea07000001031401034440c07a0288c102511240e244100c1d03400c60500d51070b0011400c02403240c50103d01072150041d2540d449c086007070700e098000203209421901245521a6080c5442d0019103e20855100145c00c101d500e003484c200311702d4041d41d41a8014802403e400009800c00883d8206848185003160119500d450a000054000121030b030540002d182c140c030315050142154071540b001c50000b906001c0a28039940c1c440601 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 694967778 1250 694966528 694966543
    0xc03030d051008010e3406031808071a0603030403080a0f030603051504032703080a2604030816050a0c0c05042301120c06080a02040504060303020f01050c03090a0305030603 76
    0x1900900c030703200900c1c1000391207101203c44c0c510226000ca410722103440c034840c0c1882c406c40740320788100c2585d4508101600940799034490002d180d01c0c0229403500050038840540a5036004d4192038800c6150007804980c40d250161403a03100358020301c030801c00204143d04403064a6072903e4100d1410852030001d601a00c04c03034000402d1406210f0701e5411003003010040364810380c000e6030f6075000f41c803e400b40e81204000c1102c50405000c1680070074800b080b14440200100260382c6404480e090303038210035512180f40c0e540206180b0b0f00c64001d00051580c00000765410100021140d4a20500000c0203030051003214000e00c01d00c81d130079100c0c2c0c0502c040c65200300b0041c10081e02c2402070040031143c6202130311a034041d0404c00540c00700080340400284506c00c2e010307644000c204020508110742940c010b031008000682054003004045103907129806054015807003600107201c20b6000310307080c41c29190300070114401043d042c420440705a40004041425035017504256a9a40325036021a080408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 694969028 1250 694967778 694967789
    0x90c05121b03100f0c0806041130070507060e0312041b0b030a060302031c080103081b1f051806010b0702030a23060a1103061318080a110c03030d0510 66
    0x44c01c1d034030035130b070441e03a070003240070940c850f0b5a40f251603690b002000b041340e6600441c1e680c0701c0024048009115454041020a040003440641d1100d910740c542600c624402c0b41e0b40c50008001190f5041049041c2c00340c0141c0700815000740d4240011008000601440100042c04154080341020b60703001d1096011005040e030105203542c0c91600e013070580c0c05400c4601c0200d00034461101c03914514030440004840e1440140d581510507444d64a403003100d44c1020584030103400d0340e4005481d1100c0304200341e4030f40300180d40340341d65006040800d21003202e038000c0248a200341d0401000c1c00c50701c40410001c0c195035101d640261075608034008203107009113071031005052a03108a00740b0071040980c050284040e03c00300403101c0c01d66030310f200f82040e600d8143c10fa80c0b0950041c40415002c0c035040001340700650007103d00050790150410024080c422180054640368400610304c0c090b16404100480303107103a01d000805c48101a10046940c82c420300124544082d6100041454840310a50400041c503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 694970278 1250 694969028 694969031
    0xa06180b0709080d020609030d02090315010602061806250c0b180618070302010822030807020c01051804020a050c10050a14040209040b042103090c05121b0310 70
    0x41c00640c00792692542d80142401841841c5514890610004a03544107030280406075052600d08199200650060481e00b41d1500481520501e010480401c42d070081401d0390007032400e0f040445480000b4610045801c205401017400c0084203401141c0c1a40c00001c0c583c041e194083c0040400c80d40c0d03081c1c804c1c004082e00110007e11500c80c440200309202c401c00c1034144e5035039440380082d000d080300120740d2211040d00b00017420805580545080341e03202605104a218140318455800b440040600003140440e64007414800c0c4182d0412510300d580380b0030309002e0314005099964175410070110031020712468000416880c101d200e01c00790784e040d0307034100304480405115955050250008881882d4200d1600780c030101195544a8168010f03074010b441d01c8400c1e1200c0e1215419208002c1003640c2c992410661803041031882c07442030001c680e0340d4ad00020141124545070005070b0b0f02da402103104010710b12456448044c00300d01d1407400403444c0e00c1a0f40c0d0030441c60100c0e0a142d1503140c0f091170315 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 694971528 1250 694970278 694970281
    0x311090403030f06090f15050a0e0403030b060a080403090609050a18020403080c030309010b220b0127140402070c05010f0e04050a06320f0301090b07110d050306030a06180b 76
    0xc03141c0c20030003000c4003051087c402030b101505050346a08072841056071144a0040400c0410f07251075050b80c1090181c0307030100319a800580400d85a171f000c050b0207000070b40e5050410007410750001280001d0302d503034580441c1082c54040080e030803035520f0251490a9071341c207a200300c600c10183d04803002103602446190701d50b0f01105450740c580d08100c0c0c0041140d400d140503000e40f8075102008104d00030618941540c02c3d003240c0640d9000709551654903042c803900c045405612900080c0c0c1030310b049403010b0221016410001d124150100d0b6101c068065401440f03003c1c0002c1451500500760f41081c82c0c048030041164908441160040e02e809400070310746018800f01c0c41d080c2c0c0288094449203a0012002c0c286004e11000461400e003415807029080c050180081c504818a50755200b0000d001140030012602c1d401a0910f0940d0000d0100d04031001c441c00301c0c00305000352915210b0604000c1d0231840d0a10100380c44403d040302c020300319561402c01603060240e019129022070741140c0030401a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 694972778 1250 694971528 694971539
    0xc152506230403050d0209061c0b030f03090a060c0f0b0408031b0c1002033105060f010e0f0601030207060e071a041206020c0304180c0807090311090403030f06 70
    0x181480d549400050200310860000c9800c0e04007a5402907600da82d82514260031040c243c002900300b2400164000c10420081038011260f00810403020941040018107480c1c10081500d000300e5180b991155402c00e2008449680e5003d03000d2044039400d0619200360650303490b0000b040c0521000040c2040440000d10090000d540040c40c458840ba24400c00d541031400741e8146c0c18000c2e41108025640310380780d815a400702c41d03000b0f160403807001096140722080c94042c00c04080c0c6401803101304040054444000e10108100e010340010418054041d90b50519a01c5441d101004050b9900340d543c8001040c00c6902c2641141d14068100c1c40030002c41481811081c2c4907140c901c1061001c40c2001500d2800326250b00495040351082d98044640ca21180c2d45c00020f500201070440340c0340002d110000714120f0b624000c030040c83c1e4031100041c00103001030000d000301202515900800c511940144002000d864000900240840d080441c569840c60106e015081541c40012540e0804000151 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 694974028 1250 694972778 694972781
    0x30a020904030e100806030a110a090e0102070b0a0612060207031704050c0108010801020c07050909030409240e0709050d05011514041406031221040305030105030f0c152506 76
    0x12040450f9102e4060301200012502e1a8082d104181e050f04001403240002700000b104d64401207003e09403a61141d44c40485030202c034008040300200d6500050b000c020404218200ca900c0f12903400108080c07824040a000b0b40990030500038042940024000c0915006034002d41d210035444003801b03202d150519115848103002c1c001c00b40410310791400440c2401040c020303036031650754180040c2501440e00c000c1021004010f85a424180002c200210b130607401d5000300c00010055410300c3d2150701c16140f04182102d099440303220010109400c0c005810b9200039010101c81c01200c0740c040440b034a0030105d00504407400002c0d10031405447c001500c0b400503854801c1030104803000c100c119911800c0b94440f54080316000e9241c0c2066500c0c0c01080958000b500c0d130320002c04514884058500680116441d09503400e4000c0354001c030040010f03280401410701d039803042e98058121142c140c008038680c4205800040001400400c008500a01c846804280e200540c100d518440503a42400780 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 694975278 1250 694974028 694974047
    0x2040509011d07082203090506180a1a0306091504060807090b03160b0c030708030c03160c03021b0d020301061401080708070e150c030c070801152102030a02090403 72
    0x103004003071480043c01ca603004100c980d11540d411100c41e64081c070800c0e5585090070015104905200486d04046125161200a4411540c00301400c100c080001d000304203044042d0361101400c11910601d0502c100c0411b4140c07900300405403030002042d21201c1103140449041c040c81504649042c00c00511010001a92000c4900b221010090403034013801745920fa01514402000714040303080d0030031400b2181c100a01050720140e00f528140030081d85c450005a1003680c0c4003903910400300c00d000252620806030160034103a800c100310002c0b841c2d90045d4131030b5191600da080d52500b1403406c04107515110001600780e0b0f40107000b048103a0701c4078551100c03103400703103c1176000466620024498900030030700d281c050041c1b61101c04501c442d00c41044000d1580d40d24909000106211164072040300b00050310100c400316001c0d000c81d5040601d150b08581d4000d40004108940d00001c0200346081c4001c517001c116031400d284000c03545400424500003260070000e40110416040100307265200c0601e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 694976528 1250 694975278 694975319
    0x5010e06041511070f05030729010605070308070f0905030106030317090a030503040807020a0909231b0415080304060c050c0103060303050313061d0718020c0705060705010204050901 80
    0x881e6018801c020481e140599007403501c88040240001050480891043c414842ca080300e107450099981c00c600c01a100b481c42c0c3d40c05540150300440540100c40f00ad0261295241150a048007520b005101c900041e12003028800744140300c0102d030348160b80d50000703090050024000c480c4d6924000b000c19100300099551000000003144205c2c03004038150307140300e4269450504584998982103202c3c0c1c17003100204d03031114003c4000a200002400391283e00d42c0070f080f15600e0f02d9400c0041c01c0e1882e421405419094100724001200419040c0c04440200760070303a00081d003503284c072010310340481d4181c00c50b148901c40880e00044096002880c040c40368810720656140080b007100540c1512150302006000c5501440003d244c95954502e8821450181b0b001180304600310040b611200080d65151000360801441488804001d807041c0440846500045183c001881502901c81510740509481035500003214000d005007501641e02a00004000c44002c0d656042d0941c411800800f20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 694977778 1250 694976528 694976543
    0x91514030a06230a0c0504030b07030e010510050f0301061a07020a0b0c0309130605010c080306061918292d0d0608030913020912120a112b0c05010e0604 67
    0x1400a1440b0b01850b074060200c0c0d06c5d1103040c28195500c026006000800120030156129280d032030b02c4c00309001e80750040d40c8501c0300043c160f04040c203201001c841181014081c2e070400908002144005074500da03010122108151211200c1c8000740c80b00c0a160701400c030700d02000c1140d955186000c40101200d13801165403020300d41e040881e40040c1c8801d8815a4040b428507090b100100302e916000b968010b02c010b251514000c1421025140c104010107801c0024940e04115104821042e051401501c0c0e180803810403103002c1800e40306031920404010108081c003182126607012041e403000a8000039101584003a94586c020721110341086603c1c0e01550306100c0700080d001f4001c0700702ca00654001d48007040181c1c9003030401001e5031180340744941040054605040c100c20034450407000d41d6060b0016503445820800c01003080c8840a00c004064210b403220a0850890b06100d001030000c0d044008030b011001541901c0041150f803020704194246400c010501401050300c9104a01c0b8214 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 694979028 1250 694977778 694977781
    0xd081819080c04020a030204030602030a0507120608070b090109030506010602060609010b090303091905040903091403010203012615040b09060f0601020c09040618080301030c091514030a0623 84
    0x41900321002544580031054012814150550910b500100080c088500b0003501c1c01e60b50b580d800049a00c1220b40c0c0002e50f60380c0061200c0342e903200b5880344800541c0303001444490305260803103454080d07601c2201100c0d0f400080c094070a0b4003036046034000356005011398106696900005c1e46030103003220380622803401c00c0008584104560190f50740004040d00031403c0103803803000e10000180c00d405084110148120009031682c8c0e600a5075030300c1b403180c3c0d5040d60b45450701102111100245880c0b500c240d00610050100e910164032008601850100561043e00341c8400f95013404d156640c06803501da680c004010510004031180c40c01246440f08403041a91041042d4244400654001d40160050b002c180c07240d18101080070740003401941c000070803601d1803429101c40a2603800c1120041e40100041040c08a04510b1100034030b041d0b4000d01000c04000ca0000319a1214020000f82c40c03072a400815084d2002c00c40c540c0c0a541c400c0c0f040140c2c44000107072400300c0c0c4002d40640240da60440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 694980278 1250 694979028 694979059
    0x301061206110a0801050d0218090a0201110706170c0405040906052e091d0f0c090a06050105030103060e1e100e03040806040803070c0503040e100e060307140d0818 72
    0x1085a00d0f100d110390300c09200f41d00b402c0410019000a040a07a803000222420b541001080d402c0c442c05000310f41d009009004c5c4500c000340048010541000041d04000c2d020044240c000d603620840004090f07076481a95101342c5c29035031901a5400c80c940192030700c0b60007000c20040340e100034001d648811420400c80340f400a5000d003401c070340d0100c01d030302c1c540c820082145072010703000001d441c3d100c0110307141d0511700c10700c605180008501c550f0945034001854088141001c0d280c0c9604030305144001d016180c140b400203011884107200040400e42d03200c5c0503e131010810f10144961910200700e8481c05964410035030b43e04c03108160036209032071a000d40b84506100c004115401c0380d901d400034242a81d03454132480340f00c1d00014049028001060320440001d001400240084c0080c1e07010102c65040140401d0240384858200040d02c100405c2400142c2e64000b03030032002c0342c0040441e03090349840070010520498480100410708940800c2c080c03242800d5264015035401c0540302d2221881040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 694981528 1250 694980278 694980311
    0xc030417010c1e02071710140f071206080307030c0b0108070e041b0302030d0909050f060616050102040518040510110d050c070c0b030901050c041505090f0301061206 73
    0x19040301e011030b90b5400c000384002d118401c2c442c4a074103a070060301d00341c5d9903580300c101c01d0103903160f2200d250307400ca102071842d8042244105000a80d1030401d4071698a0032001d0140c4070300c000b9007604103004007600c11500031100754200030060000c0da02640d4940d2064a0003801901e04100121845000040045070715080090f04038212110510512120703100c0ba01d5401481d40810744003107040010400100258508000007803041c0c0b074035518960340c6460075007071f40100c54000e4101150014103100b40882940d800043da01039000c034001d1010034801c249441402031095900240d0010751080c2413492204102c6c01951040b8021707019200c01140c0340040d00115654101d07100290388003403041444a6405030720143e40700d40e0703180303840703140c007049844000302820240c3c0402c2e10002c0000c2003201082080c01050b40000c0080d101905182c00c1400c9084030300d4200250204000011440320302c1595403049010501c0d80180080002c2a251a441118511038001c107960140c02d00a4012071003045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 694982778 1250 694981528 694981541
    0x7050108070f08090c1c060c0f090504020c010b040c091a07172118010e0609061b1603050705161511010e06090c010905061903090c0b0c03041701 64
    0x580d40c50a00c0b880030039100b5142e00e14050705010030392045580f003181d0768403810584410400703000644001c66926160036800c0c0c03150442c0300701c1040103224909500b540c000003840141d600440b4056240c1d03560400700e50050400503041c42d4031504007224810800d0304418114117a613807070845000754020414400c3d41e13034032070440c0003410bc0d9200a1700341c80008407400a099401d804160301e807406410048070700d08150f000d50304800d820034a176844600e1b505091050898002e403240c0070340094500303c1c2c100360b2995002016465406510380d4002d03040440c460490b00ca065004195814000042c00e00910ba0381018204840f607219a01002000c2030601206200b141c9004103040b40d99181510202c4801648407003582581d0740f581c4c00d802e5415401d002503482415405e004044164405000410141040d40005c2c01048100880751900a5540314040403083c5030a002c113034900c4034500705030300020f5540a04420007002c43d0101e00001c0100c0140b04454000340030400050310b40100508941e034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 694984028 1250 694982778 694982791
    0x6020606101404080102070308161b020405090f071203110a080409180206070516061103030a09081309020306030d030209100e0a1a040503010e0a0b04170f0a020606010207050108 78
    0x180740307400c0071215101e0401050242110074086003400e039038181e080e003a604640f808402240c544401c00454080484040c00d0812092504041d50410584884800c1040c0d000180c00303249c4130000110300040400c00500c210504074111a2003039580c2407400046e1034681ca048000070b48810a242196030700180c0c40700c04a801045081c64180f03413010000092421491080305001c0c0881c400f4056074070400a0001c039030180018041103000e0710011190941660820010300c0f10100c1d0000042100100707581c4e00042c2c4c44c0740021400c0034ee042c58203c0340640842c2c00e5200408100c003041c1e45030301d45c020b075008030002c0c0c0445801c903000880940980c0500f41d1160b4010503c074552440d000d04c680380494aa04025081c111500c1c0c5540d010154203890314001002c001c0009001c020030300b03091113030480c628441f6014210a07841c03607641c0c209680005d00b02400d007080c03500e9494000c05048046842548141c04525542d40b41060081e490b1136045070644c0c050300601c04c00007469405448603512988 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 694985278 1250 694984028 694984039
    0x61805030c220b0a0b0703091a160f170c011112040320010c03150b0702030c010f181517250512040605041401020c060a0906140c0a030606020606 64
    0x2403000002c03102541c0c1d00c00007044099160041d8115944641035114050640f009610f959503440d8100505070b407080e907212400315412410440b6000d0b10740e809075002d9004e204084207204869041c624507841020801030145900700301100705840050f001030001c2c10090009000741c455402c07800a49000314016a0482507480d40054000f9200e403054180b0031034145484080c4001d006291400c5403000122680840e58554107040c4449030507034131900620003010030b2840e214240d40802d44407520030300102e0600894025030001140140e030003542c003508100c07040b1500b40d42e6242038000c0400441054010481060713003c14601c00c0c03400d6031803260551940c02e103091408009207540400d0030103800001c01509000100c062440580030078002c900840c0081341e14200780c20100070131160a100000706038410071066007041c10120b449580f18400c1c4c10700090980c200d0a252010700315810014070000944020001880061005082406140d50b002c20206488080c280e90300da00640d41c036903108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 694986528 1250 694985278 694985299
    0xc02011214040303060611060c0405010807120e01060e0c070f120c1b06110f0d1206080a140615010c080906120f07020111121816061805030c 62
    0x6500429038140c0303450030024001110003030800c080c8090002a00c0880c0040e403104420000250b105070764001c1a8074a001a10709824950300640480c4a0341c0715890500c00094000b90030103001c0d900b5500d010110590900c0090031f04400316000b00414058084121201004a0400900001039410003544020515200079694641c52182e80c50001100b003045036594015000510310110269000d003001e40c02d00045051580c0030744071002400010301e072a440220b80e40b50038440000c040888004034280080c07100a842400f0010380b4064002e43c1442c4188001141001262a038000501000308241c0300c0303985802240040c8910080c1074180004c6c808950100800d2480c0020052038000800303151800d0503d40b51410760304c2040704c1c1c2e400c0c3d06600c07100b0456842c1e02070081c020924803900480b440c01c1c101d1080150b0320341c0301404804a509000043c46124001000740c004407034950246600890307a660f100401c07480c00b610f03848040c941d85140000d4a41400940500c80800081098800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 694987778 1250 694986528 694986533
    0x3040c060207350f1b211f0b0d0503030a050106050408104d190305040311030408010207030314070206041b0306051005030607020607020c0609180109090210030603030c 74
    0x1500900310b2540c0240100e000781208842c08100d03004003000300176852040000c289003045140a0300440f080d2030031050859541c181100404d040e00d44420340d1a8003510002480300560013000c0409580b500503400f000d5640901c00c00002a5104041c04441400039a13281c2604462a01461084203d04d41c0000329405a07810b0a401511600808024080d520304495030301000d007000c8407010b40010801d4100d2010711000b04d1525001c0e0050403005240b411500803c110001007144c04500109650b030b202003002c0621410500d011070020300e00310394640361220003080c000d41c441d0800b100031170701c1e1242c040d5010b00200180c0d4480d10f0190060016551151600c1140c512134244205012095080c00700026480344229400784009422915800d0708141c24146001030145c556025544030364208800035900003040b5280c01001d0b02e1654444a1510100d0200f1036080400405a007c1000109880c41e440c0d00c8011074078000c8441d4030841543c102c1c298100c80c0640800381c009154020380901 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 694989028 1250 694987778 694987859
    0xc080403210c2312120106080a090201020a0f050c090405060601121b030b0a031203020403030f180302270a27050312061f020a03260406050c0f03040c060207 69
    0x1c1989444068a030701258207483c00d0f1300f551040c02a844090b8442c1c3c0148112030348640aa6440705400c101049281c6160f00042d655001104d001030030711042d4181c400030031106010030420040060700c1c02240342000c0c6405a110401200d141e80006ea249100c1c0100ba0303014003406106059245180c030390601564422405002288005a0001082c90340040003a960000203080313a071242c0c0d00180c4a50840c40d00400480e0200001010401d0b6940d1071305040d001e0740820b8080302c0c0c0c1151007422a0301000349441c00603400396050f8010014800030444a4400c0e50820040340c044c075802c4010807802d2050294807402d14100240c042e50041c0a54000d01421501d0180c006070010800c0c80070b1055461358a41c50f1141d10b600200582084030204205500860400741c0049014004680c03c607a81e101c40c4032a440c0100050109511003010440c803a822200703c90b9880a111003103942d034581418549103030107652180c1c1005101e01c0b440000c040040701155803140c480c031042141100da1100b440d08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 694990278 1250 694989028 694989083
    0xd060b0a030c0f0801231602121602030f010c0210021305060a030b09060907020a020609041b08071d09040f06111b06090105010819030c080403210c 65
    0x40d0001001080480890b0070001e4100080c10302d81d184401e001e00386a49107003500d10450070b034050032803080e01146404080030501907001054442043c0c002e41c00e5082240380070000d20350070680c20380004036403111032022107101544038001d504440362800b50443e01800c9808182c41c0700700582119082c0c041c0200a40c004008512001c5282001c0d0b544070400144298010103c2e180802d41d580b051046500f003602c030055028004895414080c80e090308065181c041080009100d03090001d41055242c0d26648510300c0141c110050800b000240b440c050700d915003e0300c484002c1050081128510801c04115035000c0002808005054030782ea03580085040603400308580180c0ca03001d9100c400c000e1100546124140d031880c1c0484610705414403424610050032244403a4180001444a01400a03603a00e000140c00b419207103400311802d003152500c801d12401031400340d0010b4000b042c0700020038521422000900881140d041a110580d01c540c0e0f1000c000305000c10b10114491b41a00410004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 694991528 1250 694990278 694990301
    0x21e03030708073f0e030a05071a0a0204060212031b0f0d050702161d15031606030b01111c0f0905040213090b01211a031504021005090d06 61
    0x82c50070300781c088101e01048500203402501c000b03c800401c80894013003000408042c0194104001e0790100c10900e5449200703060f480010711500280440400845500c00d01100b141142c01503940d0806018000c06540a40705500041c8290300880850640900c01c49005206290100000b8004060307883c031590070021012990f0141400804c2c20719440340031316032151b10140d01400b0140600345051600709455040391803040610840c02c0c010aa203006001c1d005900170201056141c51400000d2030680031242d022001404a040060346580603001800800c00c00d0300c59910303c1c1403c41045540e00105440d50313105e80c0c41c0340310703418105020b2400c41103107486a01c1e00b9081c0c40d07240c00114059074000c035104004050060b00c10009844603128240740e0350400d00e080c070396000c0c03000342541564980c09000d0401a0b40c0307901e0b07201980f541081e182810340011f020f8445200d8001c005c100740c030302c007114241d0042c04024800000c01c0d12500413200700c1c980041141c04220419181d0340001c3c11a03450300c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 694992778 1250 694991528 694991537
    0x17251d0912160609060f0e0d0f0f050f070f02030304031a0f060f0d05190503030604060801020901050a12022515020301060f030b030a0b0408180114040320130b01021e0303070807 78
    0x100900d95816004190210301c8a10048c4940715011000a081403401d030014000c000b5031501f84440b8542c054116407002501104154803201c05040080e030b5a15802e00003503141c4400a000000c000062960039241500004080c1041d41e500340300d040c00c6141100d103551f21440303094400c46c243c41c01450000903103003e2070403980f0440c0810101c1c40b5008541c5015a9030350b03c0070080000c0c52a0034010b1070080c2030010700035800c02d20040c0010f002030140d101204140807036059100002d5849605540346c44140810450142508000106404140100540383c0040c000d404400001c1d090003100d04865103540c1d810a89040c100c001c6000301881907113540c3c94003544101001051605088500507400b9070025565020340c010401d0305080c1c1c1130f05885c180070f8124010700e2860728001c10b5030102d94201c010212000900030881540106030484240d000102c203070185c051101503481040c2800082e0204c8034038074610f1616605e81c0740107c1d01190b05500420000384003034441c500c80c1d604542242071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 694994028 1250 694992778 694992791
    0x121b042d0605030a0c180b0711040b0f090910020d0902130606020d21110a08010602070302010903060f020c16050301060e040c03020d171801080117251d091216060906 73
    0x109125051b259920403110300e000840d00780b0500400c9416005844000c031401c004141c8514089011144860041d600ca0710b50305c0b0004909030400d003c98202007440d85811940d40303d803004030400905070b1581c168000c0228400b03c0c40892041c4c441c1e40196000d035001004042c00c40f1200b110082c1c01d800341080400d00000070000003102500034800340e03500c4540229100c5180690041110b0416400f2000315440680100f0240c1d8003d400380d02640c4d00448089a8540c1440d90000a842405411612881003c58241141620100c02c80580e00102c00074409290385183c00540c0c09016074000d0007050104030204010318101150701440d40c45402c101c01203600855402100341c0180031590340b1150859003102c543c0d80d0114000740500130210010f81c004480d01c00f4140d0750001c09600020410144e00300002c42c6864460354001081030702e441d03103210000303000c4800780200103a030019403920886c90144a00780015040c0c1c0c08403a580b18030305c90b0f0310b8134039100e80014004410b0305482c51545e0b5034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 694995278 1250 694994028 694994057
    0x306140306091515061809092e021207090303030c03140c0c4b0c400515240f04080606010806090705121b042d0605030a0c 54
    0xa004d42181e0040e0b800d4241302d4406e200a202d880034004040d155150070444480740b82c0c00030481c1100d003030b580755218000d0794035000d00410000c1c82801103940391074088070308000343c403580702e5075980a4a20039034081c414001910001d0f070542e00305131003400c1c5031410580010040e24440d00070b0b0410404000882e14101e401c81410015500001021900401500a10b00000300900c003c982c21200c0b240100c00250750340d403d000c0e1140e040c018001e125030800e2803000303603a80b101c3c0c1c801e00c000d000f0300840701503801d660b0140400c4510102900740c0110300340b400044c5c8041c1c62920031000d0500c068841443c60146c124100c40b105003500581781602c40070b000c0d10034070700c40c51009070020303100140041c0b00301c0c00d0000005d0900d00f8001c00543c4240402802c0001d00742c2c0c00820344049020796285000c0540383c807102055459020000e0b55940400030800080900c60b03580703401f584213490b4800d034076a0300f603e0a002031585410700440303000ca1301c100003003247d0300c1e01c503030281681205502c0c140c410460f010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 694996528 1250 694995278 694995289
    0x12110309370f2a0b03010e04060203060d08030c09030f0c03071a0d1d0c09012106020409090803071704080307111f15050906030d14190306140306091515 67
    0x52410144580f070109071080f01c41070444a41024040c0311085a0840d80f40c14458080c102c4020402001140c020021410940f10302034010f010070390003141c25840749001980020240c01810441e03101e48544042401a00300215510b4100040540908609801c11004050a543c4200900542c40041207500d034664524401ca04006010340150000031120180b085c0c1b81110302040b0740e10801d582c1004200c040d20340302c03404480d08030b1004000070b922081c0c24628000d020710340c08010141d00381401c450801968100031071003400c664440084490045140c1622071804a80c0100403130300400c045076480340220700044856020500310f815022504070600e10f410b002c01c0512a8454070391b61040c10079284100c8103400ba00080e514590f551900e940000d17a0341044004d11414081d5112005030310b0102041103034940340000300d1800300540300120080c02007042e07124000c0584040b01e0260a9850301007410b40c050510640141018182540c01001001e13001d495410350005140c0c8501071501c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 694997778 1250 694996528 694996553
    0x60905130813080a210807120c1206141207080a0b040c05060a0f020606010302130e0c071b0510080403121e0e030309070f03080d090312110309370f 65
    0x1603195080100c3c14040541401d421a1605806128002c81003111f03da80c40001d2440411482c240130829425900302070740e0780e01c44161004a07040c10700d05c0108603845940c046030881d51090b0360064050454015140d100c00c4c0c28051101c81d0b400c0b103460180410f16120255804c030b8020008000944da540c40004e03010740c0401d01400108041030031a090700c0d5011301006510240a003410f61810501303891001c071482581c0114960328107800301255084824100340c440300c940c89403403c80e81c0d041d100040160850f15120b045c1c03280b042c004005040522901c90f0500075a416240c1002d544540c203200350240c0101001d0001c5855004c600700d0058649000f00c000081504014540e01e080000300641000d00385d13008103451004c403a03000c2000030000ea0480f115442030480002d079403c95464112209101201207088003400c00e0705a11078001d56030b000390b0041c40d04204030b8808107842800f40d100b07258950012204044090091500c200c0d035940c0344551184140c0c0b0082460320709070741d00c9501521 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 694999028 1250 694997778 694997783
    0x7020105090c0103050121060605041d07331710091107051f02040302030d031a0a0f05041d01062d15050705010b09010810060905130813080a 62
    0x1140c50030300003044001d000c400007840d028603007445158100113a040126561810000207810303c40400020b110701c0350b0080b8090540100103200c0b400d145100c940e400b81c00481405003500031081c0000318081010b0780700c284102640d0003810180f4031518001028807203112b2041c21f1200c840c10505c03000a149003e070f80305801003900340307a031203003013088200c100c0f600c521582001103010010743c80030400000c0c0000350070400720300c401e428150511040000e4003541c4d00c000d41500c20086500101030301354210144146030036907071350301680f01e8030104500e20582cce10884140301c0120314180003d09203900014441020004d8813071059000703690b081d0845226600c40c440b61030111010502c81e411145424a1828451f00c012881600301405407400d2128006034900740403001800508200e800c0d040141e40c00c5000b0314000c1550380d60044036880c0c4803030a51040c3c60a16060001c40d04603020311880340140d50a084409000850340c1e240c103c10350050b60141c00c2d040f81e0f014001405402041401e88151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 695000278 1250 694999028 694999031
    0x90605040b09100221040f1208071407030e040c1704050102091f0207091505041e050105120c0d020402090a150f0c030206132102280c0603050604020909070201 70
    0x1504031901820494010034400c8034a004102199005c4205c401c2c600f0400d41c0ba4921250790b0b21245003800d010180340700014070400140e111101801d0f000100288500b0842c0c45130f10041440483d403403090b11030284000c000c00c003462000301d1542800d0b40b122124240900780007100b041140865507070940121011500c41e90006441702c05406c1413460300c021019000744800c02c0801d860406134a580c6503000d401849580d81041070880d02034411100010b00001c2d00400500c600b0a9400325134004036500c030420142440000181804d0140416805a0600e4050280426041c003040012175407804266031058090115061603941da09001c80108000011f129140602c0200582110b804140803018007078a0f0b48060082900071074500e50220100019442c0107007207140102200d1411865141da9101c208109088a50006a03081315100d420b0401c0707000d00c548041d10001c2c0120050010010800c001c03040003154025003015400520040c805400e21040b040842c8008108076820001070f07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 695001528 1250 695000278 695000281
    0x703050304090b040b01090b090609100e040b010f02070911090a0f0602061312030519051302031e0309100306081629091003060306050f040506250c0204090605040b 72
    0xa02007032043d00c1400c0b8090310140200000700d00041e0080150381f00f01c030807450b0005500250307070340e60304101c0d41c40c84402807101d04031503c02c01d002010820f8244026000d94501082e08482d980200400440585103034020000070f41007110321000f0f4814942d5001c103048081c0185c0f1200d070f803094800c4001d441c02d05103c0c0c3c00342c0d1130041e0013460702e0805064414030750180b01c80da0000c10b2000703080c1a801e03143c600b004200d030340f190044403484640d1010800d01d01c03480c00050040c2d442151811031680b034002c4089445030b602d40401184401920200382c0d41301d038000c0050302043e0610301c1340c030f08010340e00c3e00340041d080da03803403900314188022110b0b03400c502503c02c3c4040c0402110140610700b0403a204010311a084680b04406003a4400c0100d550b00c141d26511384000310038400c2e00b04001030359015400b405603082040c004c80d11808155021200c0b800b6000c0050044100c1000c543c00e00c01500d541c100544d00b8002003904d0307070038500030140c2e0071a8a940d000300100d809409100d000710b1051a040055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 695002778 1250 695001528 695001539
    0x63b061c1205190302180d03020a0f060204081005060a090506030a08071a090c1003181527170f0c150603010e0f070306230a0b0a0e0708270703050304 66
    0x95040e0700f004035082c540b061103405013010401c3c01e1a0f01002069521620204c04c0d07007410f900e070500c26503000f0043c04880c0c00c40700c1004042d0b005801292110812995603c80481030318055960854181b03821040d40141009000e1103900240d800c644040c0a6070740300e040350b44071080a40e002040c242c4100105902520003030300d4410364980d108001d4405407050f00c1c1104d00145654500007404010945c4035070420000c0151462900c4146500600303082840e03547c900004068003500244211500c41c0041c0c60600c60b02d00700443c401c081e444454481502e802c11035000070b58005c00030f58084c4210901c4140e65210f030070040d032200011f010f18030035070328175180c0308260030343c0c80c08072004107940c00c150007280414000040c0f010540c0d80c00b0b240230905001448441c2000d901400c10440b03164444414041441c2450340f2480c2060b2042d24404d01868407100d0b500422a401c0c1c45010001c0c45540000d03182c4000c216814442e003500782c4ca1000c02001520382e4500d0881c260304240c81c079400c0028200030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 695004028 1250 695002778 695002807
    0x30b120f0d050a12050a0615080618010e0708131e11191202190b180906060a1803050607020f06010801060e040f0c0306063b061c1205 59
    0x3141c44031403400d54900782c80e0030801026256081c42e0601442d44403030103d512565a90840800b070414001c2040c40c420016a000b0a0258196880d81c001c181c9030410f0100a25144100c90507129910000c0226445810049812100003417014034100c900194240010780012030544026802ca0300a942e46540d505008981d0725a0084c0c1c14404c1d206058000008044020508202c0e4407061801207241954008180200c2c0c6a485145258034019008110696400050080c0264610002510135003110610508480c19a84242c0c03180003030110594051050503403080d1886880c1e02e00303180325503982d2194a004015074400000d40c002c450a00c40d219404c00c1a0f13401004510024042e0920b88070020384070700c0b400341c00501118a00c803001c200340040100e0390340055600906c10442c05070740e5520991918180c01c2201c1c0a04003800340c1d1079280c1100c507801850050000740b8048951140800c20a1000070b00c2d280c07400400d01180c144000c42c20f94001a490781703125465132075540384c1e00070001c3d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 695005278 1250 695004028 695004043
    0x3060e0c010c0203070909020d12051e070b010e06060c0111030603010b041802010f2a02011710091509090f0c08070308040902031e1509010f03031e030b120f 69
    0x1410040c0d000b50782e00240e81c0005100c011505140400a0300c5450f40c0042050305084881c007034694861201090070715640840103121204003c07124500c1401100d80260301842a0f99002e0070781204400180140e4060031507140d0845001004030b441c0000075000380d030a65846458460764510040100507080c2000c0c01420306209045404104c107241888146444007040c0ca0084d0400c2058101d00356080d010303140660003001d246030314110251042100044c0e040a100d0100d0004003010803040c0c0c004a5090316074043c2240b071750310100d154107208011000300140843d40400b0b13983c08900203141065480380c680302a0044130903040d50340d03a0b800c015951400641c0020b80702c1d8000c1604001280501c015034065502840c1e000d6503a84030039030904110110744441c0000d03800c60f1800d0056030342c81d0080220000d10b040e6003a0a0a1703a032101100c2e0682c0c001e00c0041c002c1a1500541c40ca80a0304420032403a45510381400200d600c01c901c040703041c006030300681c00381e1548006d004112900c810803024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 695006528 1250 695005278 695005303
    0x120705040507090b18040e060a09150507050306130f020703091d040818040902120a0c09060f030f0501060b070b0a051b0909040303201c02030103050a0b0907050a03060e 74
    0x240d50f00d40c503020300c68600c0d03c508180c1441e18504500c014600381d8130b80d0020000810b00d4001c40384035080c04001d1070010b01c00c1090480d01d4050306040c602070b62029001e01841a02c141d10317002d055030340d6503040c412110225403040c17065075a0340d0b114512010180c40640300301d5010b076a5001c001d03801c2a2a501c0341c1440303640c01694040180040100041034082141e0058052070b06030b003000b0001e0008100a0700c1f0090b0000d40c4101d41c0070008080c40000108441e03880e029031030b40320318259551041011224240115591103600d641d0034408141c608141140c900e01c203c0c00001c2071644d40c007000040340c00100e02124210403c000703200c40344015000c1d141d0464501000c030101824154800c03a482e100b0071400ca401041540c0c002420b040c040d500100042c41032040d00396060410b2842e52a02d90300030701480d045030003130074a003204150080c4242ca040c0ca9200b4001c1927008140c0e2100d903000c00b030040c000344847c41003d10109240c0c45403042030008502c04e00c4042000c0082846544c00c0c451700e0304d0768 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 695007778 1250 695006528 695006537
    0x6180f080606010521071214060a06110307060c0305012301090620150a1a1804151803090509041a09030d0e060702010b03121206010c02120705040507 66
    0x60086803030100c0c0c4142c005400b4204150740b581480c2604900c112207a42c601c864513003820800500580149079a4240106c0c0103003007004914454042011660130758030035400c49040e4200744445c1d07000302c1c21403148580a0080360f084c08582c0d641c100c00d17950200d050340c0000e603c41004100c1030000c007410103140380010788254880c00005000900c06504c0c0e200b50030821030184070040118101e070310008d1980f11a1004d45100110380c410f005500b15058400843c006e1501d218246c241c4041c260030b040466000300112028094452044e01041014000b603a603000b075103102c1d10b8003408901c1000c0c0b024400c11111042c60b042c03824081c190b00c1d0294040c0380210300c0c8204000001d070300c44c411103070b035450741c0807151840da2034504000d451800f03106941c14005241951b258007641d00020319a00c1013107190b00902144080c1403d250700c8019140b07940c4241c7c03800b8000c4e032203414450001c080e030020701890a00000c03043c80d0005159510030785660001608030007001d01c1503003003034082c01e0381c0988135060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 695009028 1250 695007778 695007809
    0xf0c03180909031c09020f0409032a05060a0b121b0405010b090105031906120b060a06110a06051e04150e0706050904020f13031b09090201090618030c0618 68
    0x134070344414480d0031081c1c0b0440d5440c10004115981c0c1c000100040b20301400400c10205c01d45406800c22801b60381002d104500d84540d4006500c1a0001c5e0310469848030141050f51280c1803110085e0a07080b00c007c3d40100a05922030b8100070030420040d000d10321591490b182900e04c02440300706d40d0103812408944204001c0400310b030340c00000b01c0750000300b007980380d4a00412260b00040101200d4118071541c01c07089000c0c0701440000f40c0082e00800e001c545160400380e031403005407054800d90b9130b95411a04510301840129420b584005e0340820308101c40c0340d400808034480780c8440401c540484000d000c1e80000301d00c0300c03280e1040d40215143c0000034809981800710150071402907030110780c8075540000b42610a05100015210407000f01c0c00382d68007864481c038060028480d08002c0c44020203e10200140915050150380b0107241c06844401480c2e0070500c1c11101c5400200400424400d60840000081c4144460b50300610762070f51540034040c070007600100f40c140180e2100710305000041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 695010278 1250 695009028 695009047
    0x4021e1914090d150608031c060b030403141e03070305042f040c0905060a0e0123090d081b031305090c12130807120e01031503080f0c0318090903 64
    0x214031002d080c2d0003444500214404c2e0880a010f8480c40e0803010217800301003030b10004914090300e00504c0052a100900c1750548480b80f03150217020440307024001440828048104110000080004a01e2200b0707022041da42c0c07802026265200351800300000ba61030080205004074040010b8500c3c1070811000b4400c411440955409000410518844c6503038440c0c04420702d006a46000080c60050021078941c0745e00d580c06403460388600c1419010607a801c803a4081c80152190500300b1443c0455103074103140c3da036014004e20100c508021101d5650030040f4012068042c60410307050070080e4003c50341e41582801c910140daa040c1c3c4002e000c1c405090910065541c06000d40b180c00a40000c0800c00d50703a18084003200d82d0010801502d0780900044100074090101c0130031960400b981c0ba600800c500703030001103044411008840709500c01084080c80080c036400c00408000751030058060600c01c0f034410701820b541c044011080d14558100c4d0400d590f060034000e0715882076a03080a582020040c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 695011528 1250 695010278 695010289
    0x2100b1008041101020f0a1a01241407050318040606030608190525091406030a12030f020f07210c0b1003060501060302090a0906080c04021e191409 65
    0x141c002000c600290f491042164400c02141410110b000c0844403651034500b0006201d00d004405495904060350011800e0b1160b031103031318401500380500d00b020907240d92044503e0300c10a08910902981003000e0300100d282013000d048031340202803801030a00083d03400c00c000c450309540b001c003c5c142015020072006001146450f03070b062011a1152070110b81e03107401030501c4d40841140100d810006030341d461003000403050030143c03403a51104004214500040d18501ba008403102d503815400f0f11408400a00c02220301103020447c1e042c0071454480e14982103040c1c0e002107042c907a05041c045200c20070f0000c40781000340c03503210071004900c80c00d030340c0e0740000c1000745602000740c68440d07000301280303a1100c041009030003990828001c00c05940c5528004010390f004026540c403598242c80c02140d0101c06104d0502100d000034000c1c04810a4042408040d41183c4242142c03410100001000c00403200014008000c20039030000005080c060094a00c1c0e0b00e10000301000c40c010700c9140c0503038980 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 695012778 1250 695011528 695011531
    0x5190b010c080f0405030a0305130503010506060d02071703191107031e2105040506100501211e0c1202031501030218030a110315040506061c0f0302100b1008 69
    0x3010b9032075aa03225129240d942482680c0c40725070584694080321042c980d000010303000c8c88601004102c10281e643c4101805c1e41d0042e0382d02940003d0030003485c51030860a50003007500e02d11521210b4001801d5440d42ca005400c111001c1c1c044108201e5000741e03010403481a50100a8001110b0b800c01c422520010310742500240d008402d003190004070856207016003407010220202e00310f1200820f01020000380900025103040b6035911519002c1000088082a0f0fa02642d0040e900e80c880a100120320b5005805010303004801c030356481804145882440802c010022503c500c081506d0409800050288980100c103d16040c070500500c16494401c40000c441038500740303001f41e1503841414080403070080e81c800d0503900d4450030341d00f0010800a801036401d01c8004405031112200b003060004440041140c000708a6042000003800c02d00d0503800b0700390540c0300d0003500020900e075580ca1725010265142c007500076034409198041d154003a80503407001d410068503c0000894400740281c06410b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 695014028 1250 695012778 695012783
    0x3030f021e1e03040b1c0b010302030915060a1706100f030302031e0d0e1f020a0c0f030207031406060a05040b1e040b06040f08060a0e0a080901020a1505190b010c 71
    0x882d03107042010100c0070420794015000c22041260f6402d411014101545125640070200e581400154040c030f40c0284240da01c68081a809007207240503a0690700205d40008200c254440c0b4848000305551688403408129601c0c0c443c018800c2d410310703071441e135240760351a0310040011030000b209100295010058820b6496a0450f038821001180d100509a01500310b00b80680740c40d00d40203503c0c0c3c503400207903901d4210348025500c0054400b00c100c44240e1061600460215408903c4d40300080c48402078030740340138024030544a43c1a1256100c1c03c0b4040038106c15085075100d441404000c2c64040a10720081c0f204035410044080e94002182c101c0a04100004607a21117903500c0110380c5964003c407292041c000d145965580d2100f0052448040354080c5035603600c1036000144006100340709400c0c0d070110010041c0046490340d1303500d80042d84607124180c1180079002207040011800c0d01c0e00900e03500d0740000401d0030700e050149041c051020091340300400f41800078905035a6000742e00d69041340d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 695015278 1250 695014028 695014063
    0x91e0a111002030a0503100b1903060819080d060e0c13061e0809070b0a03020409050604051021150509160b300106020c130e030f0a030b03060103030f021e 68
    0x64804c03c0e818001c1d1495881411a0f03100080c00550108441c9c01000703000d011a00c0400c000e0b0303101c01e440350f52000f8140c40213200d681d0090410340030801104c0589080e841d182c0340491866110f049500c0b001c90b00b603030b0f40d0700c180c0004903025007078545040d000c2d0301910580c82c04185041e1018034850078100d0a80c00b000c144071403040401c3d005076050181001800c0c00040c0240e443d2103600000740254014407460031014580000300d03190345040d01a46018810102590007581d044c00443c40c40c103140f10307403513000c0203200d401c00d0f9000501841001540c240840800142d034545514200d0410045103c1034a072556a0003090003506074180070f4840c0b03481d01502c4000005000c040c244980c0414995002c00881d039070b0000a200c50340007854030100841590000c1d000140c040c0f04c1c0080e200c05c0311030584503800502c21040d4007031f00100640b998500307a140c00301d503400d202c80119040a400f80c00c150300103241c3c101c005c240550100010345d0111a0350861142402d5271708100341d15030015002021911 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 695016528 1250 695015278 695015281
    0x907050c031c090c080d02010e0604120e03070e0c031005030a020a090506060d09050303070e012303070309021804020f03070e3403060302010314010803070b091e0a111002030a0503 79
    0x52080794040c6159540c0312038114045a2100e1702030f03540760407500d5132000540c24500d08101c0c642003c02d0080c002c41e4080a2035a210881c04025648244d0300d4070501d40511901000150581c8441d038000d00420600301001d0b924140300a42001c02489600a81d01071780c800d4110b400185c0319101c030441100c0f031150001031180c440c0c1d800181c4c1c610810300040c20440c1050006802d00002000550042122f901c2e80c0c080c1808010040d5107042805000d5980000324401100d0002800401968070100c00e10f03000488203007942c00103959030700041024032a11014010002103050014000c586018110020100140b80c6151061950320040c2060600c10900100d00808000c2d01c070840807495507800442d46035000c0400c000d0082160344000c2c0e0019007400c4c403480c0b0240002c000d10303050b1810507025601e401d070240c03100548050060301c0c501041c499162007107400a48001a108c0c0c1030204005400e402c1d8090411885a45540410a10070443c3c0c2c40440000c40d00041143c14405182c1091a201d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 695017778 1250 695016528 695016577
    0x1032406121121071410080a0f0609090b0a0b1203070f020607020303072604030308060d110312040609080d020304030b090a05060705210c030a020711031002090907050c03 75
    0xc0480c00c2c00030281000f9040d241140b40200400c04500b43e80c5078801009000c1c428004200345140c0020301080031030385880124020328202e030800292411146c001041103076941c3c00c800100c400160082d1200703105c4070244042016a8011030b805008100e8242c010102542c200c00d07200d102d00000181100c8802900700119181c42c0161070616800901b030340c2e03c408036130400200e61500e440c0c1c800424244071844404945183d0180d600352274240d9210070155851a0902142c02031090301606e81d40303000e96804c40c035030f40c9c1044070319008010001960b40722361500c10007a020007440d41109045411070030028444039400425034085941020f148030700c0d0b032250500030741080a42c80d8007800034000c0600b0001003a40280c02096101e8515480360505903204040100005c0144d88108201348100045101003030150040c0c04070500800c8011410300d0384030006490105a06c01c04004141c01140d403004900d40600203941c826013030b0804e03510340150600c60340e840344126281c29010070400080c8084 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 695019028 1250 695017778 695017789
    0x9050c0f0109170106151706011103160302071401052706040b0708091e0a05131104090515100807031104080a05010e010c020c0d020d030e0306010324061211 69
    0x1d00324003e00810011071885001d0107811240103003c83c0401010766070a2070f91140540700040c031401c0914045544880004481c0100325800b4514075100c1801050003101c0081604501c1d40c3c8a41c0003445281c0c42e250100d42e0034140b0b0314031203050041c1404080c203e00101400c49002d6036410f00f089510307000b114000740c11800b6035003110800c0ea0002c0384010821001b0b9004000450f800c44520180e0441c22188000c24054041c1c210340000041008200c6800c084004e40901110715501181003080100081480e800640c04400030503224001c0c4481b18580d041c8000c20603509139201c2084c0c56900d8005410bd46000c2c2480381019039030000e4443e0618038030203590140c100c1d174040e03c0302182c1c2030500501800c40421010341652a00d4880701c640c1d800015a03200a00001d440c0c11a0040c55400f08035501d51004800e82c01c3c024440281c0c2841c0c2d50074800940610b1041018090f0f00d040c002e48000310703080350060110032501c2c01c8001d001501c8030079503c006440d800440d54100e912114003042d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 695020278 1250 695019028 695019047
    0x40305100c03290a052b061d160501140a120b040f020306011d1e041b05120108060f0a0f0b0a0b041e05090f2505040306050a09050c0f01 60
    0x40c0858100c0c0c0c00c008029212055460780c80040394200d40c01a158005c00c07480030181c201d142120604807402560000d80c0e06c0803401d055001d03850014181442c0403060580b40c0d0f00400203146600540c244121b80761042444401400081c030300510b00d0000c40d82d40300340c0c501c240c81100d42401100b0111841d40400da07000305483c1c4e080a00b0030b101034401000c040019400544005000c03c41c5d0030599082d85080180595800340001c12141040d0741443e903681074080c4500c0d100d0380068a0740602c1c1300c90200f9070100c451380c0d0b12555440b81c0d1900d41c00c0e4101062841a0001c401f1a005881032242c7c60460001c3d8507023285540000050480500440310010141000d41b01d4100042c0900015009203260160045a4046050300c0015130b8120b00790355040c10750700070542d002108801145400c8610301000d64000c4140c243c03031186c1c0c541c11f00100000e22020010320001803000070188204901c0d402402c1d0445c440034420310460640d542c0c0c042d22040c1c00f29278240108074240301700245a1103285d410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 695021528 1250 695020278 695020301
    0xa120b0121081b060618150f0a0e06031c0e01080901020c010c0f0906050903060403050903030c03120a060e06010806040e070f0914161b060207020603070305011a040305100c03 77
    0x1555440c0c00100c44402c04800f6840384001e03026480001e4031904080012000c00040a0035031540390303817601103a05810301644012500001c61420b01011911280350b113001905c1340364071403507081c80d01004040c43c14101c1c24402869400c00051402c03255041400210b0200003420800d8142e625460000c0c024000d00c02160030315030030403025004454002d40d8015520559907600400c040d242c01c815161845a4144503070554002000030b0080792191028020540b0000e05032450302103100382e00351464100300c18803d68090f0010a010940032144610130041240317100002c41031800c00c00107440c8d04402000c01d1300803a120504294080380502410b8080c5c8004050800d1a6844542c03d40080c884607441e00802104040030540090482560b109141c1150f9034560940c0c03003603100000001d41e40700301102c1180d02400000e0050790b455000e1480b8110641e40060344d50301d032241c1d01c10b608a46c45441c81180c80700300018408182d01259020184003034690100e012081540120001d003844001c0c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 695022778 1250 695021528 695021543
    0x5061e2e0903050601092901050c06091f052806540209030102040b0d0510141302070f020a0303090f050a05010507020d02030c0411090a120b0121 64
    0x41a5001003100c07081c2c03402041220b4040e84c8540b1200b040701c0d6400c19082c041c4000035078030026a071401c400f00101d03920603d0010300f00000903090500d480320523a40004190010000b0701c02c000304190201880c840381c0790080c0681c0c1443c010056590304003040000034000703220032610381c40455030401e034002c1c4202c00000b0f488116a08600307218030000025a640b9403480782e00c2000e640004584245070303030207250b502c1003220240c2e50118000d42c0144c03d96038044d50280300001e003440c6c02c04080e01c400554082c01050710b103031001a500c1030003950303003140503010004004120740740c0303e04200c07040790380b800c101c01a910341007403c1040d07107040e400500a40c003a920712400301c101a88800c0110840b0b10840b03c1640c5c10b5212410044003030524056240080c100703020301c001601d04141007880c150300180c141d0703442c0354440010506581c02c020690101c0800010220000e051070072420303008200401c5450341e01110755440d294039200c10b11403c1101c40c600c15200c0b05118015044511040d400071b034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 695024028 1250 695022778 695022859
    0x8090c09150a080f0f01050a05012d0b04060507140601150e0a080604030e03190b04240504111521091e01050403030b0f100807030f0f0902030105061e 66
    0x13640f9619032034064604c0155080001060850700703030307005c2c05058130401d0000800300c0403986440320b0108004480b00310106800f030000601586000000e001400c0f003a80c42a5a4106c5030030301e118980e0130250030001a61041c001001140f034402d0446001052074980b890b40c078502e800001d1002442900802040e004070010300041541001001c2e61010303064051350710031410300da545000418211400341c502e0004100013800500d030f60a56420b010084207618084001d0000c416080350011035003200d007200d84118202c01c525108140e2110350207100309061400000d0b003c501c0b0707582084541000400503081c00704e401c000051100c1c000c804541d05507080c0c84016034071158040c040a56040d0301192420801d010701c4e040464034800ba441000c1c11150702c60049200c2251041c200400046c00c040d038440c20503603800c0e000d0052040582c841400410041100d00405007100c0c40580724621403545500c90f003200c03420165400500701070441c2c1c0c00010200748210b450070440700d01040d2500c06003002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 695025278 1250 695024028 695024053
    0x120703080c0d180e01271407090801180816081c1103160c29010305010c030504021e04090f050d080703020f1b07030602041508090c09150a08 62
    0x155002e08a540c503518000788640200f0150b0005003180107019000c2c1d950300c0180060002d0301d5081c5105011303400103154000064480310b0407650070750000380001c228502445150303580805208c026140c0750b0020800b0000ba092000b02c041d03000340c0300500414021900c2503c0e94400c013002040e0f10b4002c40303070f05e940b84070b1200c8009a80a1a24000e20030f64034284400001044040070b40e40b094003049212044100920030a58203442050800c0310742c00c10b540b500541c0c034000210600301e021043da040c90029411450f0850a4981c0f0303c0b1090704140c58a000c0101695440101c0041c030003054006220b03600919002c80c1c00740084100151240c40c01020364003c0020010b010001e107180750381c99105603250f150f0110168410380c1c00e00d607403940081c441c00c031400d024184140c0307461140314200c1d076145590799a50f0040c1c2c2c025602072000c050713295410281581d0402d0200e07520001c0d150240a02d41000000514020006052900610250410300d00c1030788910f291400030b8000c81007100c49020200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 695026528 1250 695025278 695025283
    0x40e01060f031401060b09040515040e0d02150c04060503250909050f0601080c09180f1006020d050f031914010f1a03070e010c0b04030207210b0105120703080c 70
    0x520080303510315258124001c1d03e88040c03107a08161400115405e184c1f0f201c0401b000060400905885503807000c0e9a845901c40d80c49220b981a4100a02d0181c034000f034441d000030b81010a40d202c03d07000e58030544100503440003071400f102c0a036002401d10949030f0711821604264086400c0b4068050214810000c20254002c0021011218582c0c814003035540c50a109448405090303030b940c0e010449a402080c0a105c42c540034109962002d002c441d100080002c5101c610070b000c2c1d031041483c40f000e506000390001c20114038405042103000030511074001c4d0400524138803172005e490750390060100115812039001e42c414a100b02c0185024403031211002d0744c56101d51028450358200750204080040c1444a012092a0a42c0211034032740c20355484041c1540c4032500110702030f0412000000c4400010b10700158640140e003e50300030918207044c019420292240350b504e0a080746101d41041000800c5001880e041d640141c480c4a510120700c90200d103001c1603608020302079000841c480740b811400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 695027778 1250 695026528 695026559
    0x703060503160b0a12061d01090e0c1c0206280503010308090913050a1b0503010b06040905070e13060306051819020a09020a030e0c040b0d060504080f030a0e0c01021902010c02040e0106 81
    0x489898080d48c1d0360340d90717110203c0741c2c0e142000704079070400e040d40c3c03409260241c0c1000c0f0306184440441686007403a80012001d03402401c62054804d02ea01c076030340f441c0076001300d4103500d000c090406a14550650722640020701035100364510550a100005401c800000c1d00765186c59403000840301c60001c1450311481c100301d14110002c170000e112000203042e160500604000c0480075000300e03d451704180c1948040c01c0001c00550a000c04141a5003c6864a5882c6109038044090016110f41507103404800d58a01405140c0237040750403003080e583c0700102e034100090064610300e10501d02c40e44080b81811195a000030b05503840440e10070003454050704102001c00001096403124049913007003004a801c0e40441e44e80001507031040d0310014840ea80071607001401100028200709107107010b4500c0c0d5204039000116152540001c131020740c0100458464a4000d002400c540d0003616405051b50500351400f0381003202003010641903454950000305440d40c144001e200c529152048600c24062 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 695029028 1250 695027778 695027819
    0x30b040f02060a11010b151b070e09031e0a0912061b02010c020105062e0e060f040503190b130611070b0601140705030307051c050a050703060503160b0a1206 69
    0xc050301001c4514007420343c9600651070120f1f550a01c4c1c844030a0b4544d401d888141c280480c0f040003c04640b003880702a4482c4240d840310015a5281511601200c0f00808040b6500c03018009010361102d040d040444581a541c0c80c4032140c41c4200507043c000007030404040300d40c038003224071802c0700308003075040d001507203204142d40080c40b40b5203030103041c03020095a901e003407038000b0b0211189030007903042892000c03071442d44c40c50089004040c1000217602075100100300142e903000000d0411840c1824085909904580d0a00344038284407500c1c2c0080f80c880060a8188140080c110a0100041c40c0e011400303862801c08001d48955881c5084945110207450682c045880b0008448644050b50700304c5507050343c0000910304603145c100040d160b6070811f0482402c1740c0c00b9200082841d0303d041c420306205003540300d8040390303d090110001d0304503510b03074200718040e400c000480740d0000c4101684404880f907010100e5902c101c400012103211030f442940030565810440d0018001059502c100c04944 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 695030278 1250 695029028 695029031
    0x6032d0e0d080f040204020702190e100509040f03080703090c140a05120c010c020a05090708070e060c120f1605070e0a23100b042304090507030b040f02060a1101 71
    0x65845209642c203003000c80300e02c004208040f0010b001810560080c0c00c403240f0181c441e018209606030903140710182c43e04422294500e0004000c1baa80c00305140000134501503d400300710307003499145c240e103200301c3c11006810701c80071002140c0a80c1c8a42d2041105070b0f00440341e4925643c41d88100703881903164402c0184100150300c0041041d1511000f80034040241400400c8a801600015100d07200d0500b001ea070301820a0741c0004180d21140500c0c1d20582a6036900d050901e46010050810325011000f035019203c180030440318100001084c485069420701102e44400440340c00e80c202d4490540c10301002c0c00850200c00c10000c0002d00c206c10303030300c2e445614401c07566814201c0040b6980403140030f8402c0380701640d4a8461405803c4550481c0c0491815807000e62102540781d020752260303204068807002220903540013200c000781d06500d0107049030188581c0d1290f44404c0e9a8030507074000501203007071a00c00f060400c4200644011555400350003903443c0c107410440034007a8030782c100d800503155 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 695031528 1250 695030278 695030293
    0x3031e020408010218060a1209060209090c070606140d06150b0a020307030f211a03010612020108010f0e0c0a09050d12080f042018010b04030507060302031006032d0e 73
    0x1d2030710100f030b81e0b2904090752320141c85406520b402c80141c10240825518290300f0081030321030380c40300c10b6807911030141c5484507940c03040c0b146805030448100c1c4d8044111400344840c204410b659020a40109079084480424450000c203d805503c0c0a1940302c01c4202a0000e400c01040750040040d04200f4000d480c0c07500c6280100409480040c043e20704040310680211071090a51400c3c0c2c0034140200344d00c1040410140c805020a013124802d4005e440003401102c007507021581c1c0411814050460040e0401480d85058101011843d02a02e40b00050202241280c805441403625900402006201348a000043e04150580607180310204000800000014402d080c03a00341d518050360380f1001c2c62508030700d4010320701c2414440d02c546c541c0c80b44626100800304101d10603264042c2001304101c42e555440c41c41c040b0300d807002c0e0b5808801410700610030091002001e98083c0c003166041d00340410415100da2820450401c0710340c080000004800c01810103002c03d92103c04294110350888000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 695032778 1250 695031528 695031577
    0x303020a031d06040b0f0904050c0910030e0304151404060f0f02160b030a060308040306050a0e0d080f04140d120c020a0b011707050312070302060a0c02060403031e0204080102 77
    0x15042250b01054005908000030004800014014141e40c2c41c606e10543c00c040440303000400b1790713905940b15080c0e541e01080021061410301181c1c2d5444806003803c10001151100c2d4503128069481aa40844021004038440070300441d03140350090900c0c2012559103864801c06020341c40070040d403c00160540e282c00d00c3c410700006003010448400040a204a480d005030b4200380e500040055920b96282c0000000046004016002445c4100408034031442c00e854460304481481121071120380c00b20414143c49a0080c140d01d420002c1071034140429038844c244510035020004944d10180b0964464141c420b5001e1441c0702489210b00341408044000d1f88121b030b481d007150328003620010103000104104805240d4105428018809441029642d440044d00301810b800c00c0c100101d400040d150708141d410300195610100c100c0040006000131000250f413500d0060008040c1039942c9900000006045030382c44070400ba603001555035544a209181c00b0350072854454213142c0c05021032508 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 695034028 1250 695032778 695032817
    0x160c03060606111c02010f020708030105151c051b0c0c1819021b190611040608010e040c08010e0309031b010c0816231009031d0312040303020a03 64
    0x107042803200c1c000c0c00190700110103201c92034a41250344e4103566882d01045400112030015202807030003100c032141c8940c580b03030500c60b13088443c06006510907030030010f46802020800d901142806010000601561908900114015000036903603400802055043d8142d41c001095408250165105c082201d1b41202003903020005640150070b034071983d2050020304100d43d0161a501030840703500d8059082581400381022840c18549a9031031100041e0707414880345024400064010f075190303c2c905441d10300000c19500041c0039503006014650041030078401698502e0000e49001c00080140c809501030a42d5241d000d181214042d00580b00c0c401c0761000d03a054003880640c410384445000d1034403030360303521605e500209a1a0400d41c000301108086100451a9251000c440006035041400b144e000303490302061030365000702103040040c418000ba0348900f000362941c2c1071408060200a07041e0000303007441c8040207620084440440d00000345580090303c03820300d0380261a0070720820f1040e0321204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 695035278 1250 695034028 695034047
    0x403121b12051909030c0206031021020901140402120702010507020f0c0328140601050103060b1e09060714011d0609120f1204030e01020f24090102160c03060606 71
    0x2440d603043c07003075410f6602d20300350080c1da0313814800d2810006400301d07a4001802c0d0f0b0019261001c803000c910300c0a0207041e0003880d8a00000b41c0c40f087c8215001100e900189807a070050080070000303c11005007580c19202c64040d5032800c00b0344010003419141401c00240202812903264005200e98003400c2c0d00d81d0307408149079641d41c7c0050003401c00200102c1702158000031110940480003141010040800c0c408007500ba00100540d01806643d4500b00005064400c40e8103c020800010800c2da0803608210320011040c100304000f041c2c54028032400144180a2410080c000c1e041800e500ca40707050045d40110a58070b0002d00c4003403441d00030441d030340e52420200d4407040d003030b84400c20b8000c00e0340451024218000f800041c05180c510041c00c02c090741c0d482920b0807400304800b031801159541c0c040c0100c1501d003010b000140040c001c0b09403501e61455040e20790310003010301d8101050031000e080d0100d075000d8444190030815440c0d203280501041d021440141c4a440c5068408103c0c17500c11a03100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 695036528 1250 695035278 695035291
    0x308060d020a03080912100905060708010608060906010201061d040b011202150d0902040c05030907090213050607020f04090b100e010b070209130510090c0b030403170403121b1205 79
    0x2141250859484012a41c0915640340c0d010540500c51b0002100800034081800e1007000041032202003032074258903005001e8a1941030044950050201c5a40441a264003480c1240c0ca11002d8032040e0050340103003020f030081010280ca0700c50300700903480069981d42c010380c4901941c1c42036a90740c150803064444140d00c02540101047c0e0005042c1443c88050700c031000b4107a0000411510950004040701e11591102002c60710220400441d8841400103000800b01760806601c3c05601c0014044581e2450040d284108070200c0c0502c00c3d07403181c8000c1010400040d1040081c0042c5041042003014100c1d16200e0542c03107000301041c0701041c41a030034100c81219040c542844e10701d07400c02000d4640104140c2105030701c8204040490002c00c80411170000154000401039038a05110181030310942221044102c20414400002d07400301d6512000000752041110702e403154a001c54031007d45081c03201d00c4a0601d05007489048400651855035501a100d003004034030395102c48820b80e00100c424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 695037778 1250 695036528 695036539
    0xb010203040302190b07030e03060a09020a0501050a050f030108060405070b0c07030b131a0703180c0b1b030f0a1101231816030204050c041514250308060d02 69
    0x801c01410841300010059500303214001c109a01d0700410402d40c1c008190030740c0007546012140300386080c18000250464041101130003110340300c3c0c001c100c01c14424807429040000000d11100002d03c01c20030358052401c06043d0940c1c03540d443c0304a42d40d6003002d450540710303405005070015078600e01c0b0b81150143c60002003d460510310715101d08040c0c0c0e800410020151040303c50303d900003841c800e11842c42030360011b642a400c1c10020703401422180d81d0b82c2104404075441d080724010513404200c8500b168250301050b599144407418030305840a98032841c011902c004540b66882543e01030103008034860f81d540d00c581d00160b10010909031080d18544c4200e100c01c03d8085958401e210342c003668480c43e00007440602c0703807441500e246044620029141d990410080500451a150048a4210b0942040a402c0070b08000e6184000700e440c90003001442140309890343c03600f50790015a4404500320003059036402c0881e19181d84441815811000104400300090061624504054415402411 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 695039028 1250 695037778 695037787
    0x5010207082d0f1609060b0708030921120c031317040503030a12050f070203122221110304030b0606072102012a080414101505040b010203 61
    0x6503034032440b004000041c00440e600004068050381000b50f4040314052400a00c0c4d9081c4442c1c1c034181003c0960402a801c500f40001008081c1c4403e0960719003d41110035265247c1750400064503201c0304400718405007032030107101c105082d84007024002c0783d58844080c2109540e00c03104aa03140c1710480b01300617402d6100310032101086181d2a440800d044d61140d09203001c1d11a00041c0c9107402544821000400400c1c1c4030a201e402401001e0b00302c81d900c01013010764281500060b40300e000d00c031151f80b20231850320f000402c91013880c80030b1007981c16100c40c0c2d842032004909000c001d29a944584015030311001d002c031003c00c1e120b015040c2d05170301c4120145090078110b6a0304220300c1d801030302c0d0b198410018461000407820300720a00c0907180a100d5089844035041802070f003560003142109210300d1000070101820718560544502c0300c030041c0b42980203540d036460700b5101d468a4416040d81c601c10707038105824868165010301c000003105268198401d0f0303550100030954001c502040c0c0103800502 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 695040278 1250 695039028 695039053
    0x8060d021818061e04020a0b0c0c0102120a2115030605070807080f06041e02031305070b0901231207050d1d1b1c0302060402010909090c0e07050702090f010503070501020708 76
    0x10505802510040c00c400c3c009603101d6003238003a0b8114840e60303c0242c0080c40b403101d5075a01000b803142c00f0074205243c142400303000700d0080d0101144484203180c0c80c1810185001040017030b8003080b141040682450302e0b00c0d0b2a420000e004200403104c40c004500e41b040420303056401034801c2481181d10280e9083c5a5844000740170207008507080800404a60144201100c845130014500c40c2c01d03105440d140002c07890070994030740b290950000d000903000304506810f690b03200c03c11110341446518181f03a940f1420304000343c0c1d80700d00076514a5410010f002e1241c004d074807200030965050304a00901021100008000590f10a440020019800a900c100c0202d102d420b2100c60880d0040c210340511082511030301c81114041c030110016000001044115a00b109000d40a001105410010251550b0781d0030004407040c00703450705c01c42d608000142c5491040b011550b00c01c1d40078210f64001d040ca04d101c4c00400000b07000302c41c4640241d81012a06510009041044510407002040c3c00c01004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 695041528 1250 695040278 695040331
    0x5061912091406062119020f03100f0c050a0c02131407080906010609080a11150f040306180b010303031104090603050f0d05160308060d02181806 64
    0xc921040d45940c4400c1428045000d0b520310444441500d0b01510542c90710f00b0405c034019401001000b15151404104201da11700050794081140d0b14501051140179940005a0b001c810010216403602c81d01400c2405c512094010b4031000d20641c0003030100c00400d14042d12280990307005034001038035010000025103031001d072030000004041c4e400900e0800440a0100025040b1004404140301364140020083c0c10072000b401400c01d40b404100c600d0403c03400649910341003d002d481c04011900100440d2f907510994581c1a1040040380c2ea501081231482c1d540e41c019100698019140031009100300695801d50380c9050340c0107000031020380c00c55906400803e106950410082d60601000c900301400340705920143d8000c0740144401c900e40b41c038851400c030402451400b040030a000078500e400390203081c01212541804c01944c9581d403140820130544a000c0040d5114120310180701d0003a142a003a0f501801618001d180d08600c40441c140e602c03801507440c240516030600d0582d0244624 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 695042778 1250 695041528 695041547
    0x609040b06040302090108030c0f2b030f1503140105042609030303040f1407030b150402070218100608013209070206090c01020f07050d1406071701050619 68
    0x801c050b040c15100e0b0040782c1c1c0368200340c001c00802d80c000075080014907407c104080382880ca010040050015a10030580740708554011454058101d04c000700c2d00340d029420032081c0f50150101042815010175281450000078842615030614450100c0d0a400741070142911a94100a6029080042100183c9008540072415100c14400e0201100075030307080c40118090713801a800c0d003007007841c20300300384000380d454540303900090340007081c00c00000700846000c0368400c804401c1542041c448802050103480b41c880002d601041c1c8a86100f0424402a240c6014200c5404c00344002621b814054407072080030700030b132500304410084103010a0100305030194001843ea00348a85055124080380d0007400030740e07000000d038000d070041204c40d180810101488040920041041c40b14400c2ea260300c5100600503a401841c1d9542c0c5441840782c490b08059512140004844803460807041c01031a800417590b00031010488034000080e90700e0224141d60303009800e0300c00e41031800c4100340251740c044030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 695044028 1250 695042778 695042801
    0x6030e070b210112060b03010c08070302090319080c071205100b040f0510030b060411040e0403270906050f01020d03150f0308040e0a020c0a3507150506060904 70
    0x1810b10703900c45003620819002c3c02407a11068888104d407451034040c013980c00f102d03109402607140c00c041901e40da5100000d9038010304e00b42070040c1e5078004180424102102502101d0b0441580301040c01040060310040460b152100183d4a80c0394442c1d5603001c50b044041c20240242e44041c65a0001082aa10200c0386050050002461940911002082d15801c40751500d40202c174107002c05c1130019111070715911030011982044a0440408030144601980c05040700105280d00054105402000d91103404480a2081000b40b250000d04503090440c0b40200b54620342046d000055a04000000c001400816006000b0019205104400402a0341d616688010402000003446880244400003440c01102d603181e03242d00780302c60b40410381e03400b40c402d844140c03042250300030103403010580c030000c40d40c400c1c1c11000d0000443c003900d00c2600c21045903001c002400c42860031054060005002c4517216003031703141d801c985502c0400d080b121304488650b0400c0e41005018518034080d813040c0d06110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 695045278 1250 695044028 695044057
    0x90a080d0c12110a03060b0a14030402030f160807150804031112160b0c130611012405010e030a030207210b0f061c031403040809030a11040606030e070b 67
    0xc80c2d015a0006880700c1001e5031035400c00c00600c1203040b60b03140c05864040c2c100650385502e441810b4000914040d10241c3c9801c1203980403012508565092008803940510102140c0a00554865010b4448868071034103200d886100340001d6012408481c0c03d2030180e07641c551004d5070b6100d80b0103540c0203480610080c502e0064880b80a0400c4400c03010380380348074242c0781100c4024000d18100030300c200042c050188480c0c051040f170311444070780101c85044d50318038034204150f100b41e610070a000d001e41165400001f119507113072000e54041e441c82402110026030f03542d01502e00103424991074109070580170b001a00846028400e4200c44e072a00c01e8540d6855040800d40d01e010344030b192201c40246e404000910000003401814030b00915880704012001c00340c11b509080581e8060300c24a1840c4010001207000f00001d01441541001d944017080c018099450a003454904141c44a04404a05104030314180020510078403034403410800b60342143c02000010f00340180c0a080c4d80040f08040b0004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 695046528 1250 695045278 695045297
    0x1506030405150c1b120d2412061103042a030c030b09010e1209091b0c100f0204050f061605031c0b01030c0c0303200c0a0506090a080d0c 60
    0x4008a0b034501d00c6200c0d000c140b96200d00c0342950070320200d4840d030050707403055000b00505840c44407184110341003d2504c40c40082c90f881102c00e00404070b40c21078440078006503003a20002e0140d801c00d01d800e070114811602000b180c403e1000303c05132804152030140591081c4100802011010080c40c2c030780e0340c0c501b005c1d15401ca940b9600d64100c0112901f0485136010341ca418026518000d016401003c55624044c0803004452104925540203010960307205010500100d040c8809200c09075000d01040109141d5032030000c000181e4840c006109a6041e9141019034203140d07902d031003501c00f6182c00410741d0314000514010400545c00c07003909401d456200d1040c03d000514200002c20308035542c64812188110700f0b1080104403462629054141400c140708c0601903039110f0401c0403096818203000541d00c80f142901d9980100c08104000c24213800a000c50100c2d070f001840550303c1e84240200c409560350074000d170392144d40d4900010401030007845038852003105c60b04a8180e0702100c4c0307801c42d643d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 695047778 1250 695046528 695046553
    0xf0a2607090905010603050c010504060c062f18060f0403030c0618030207140307030b0705030a1b020c1c08031902091509040f0606050d020a1b060b0a06081506030405 73
    0x202d03199000100e5880e0364513141081009414420804041e1090a0041c24246400b00c0540002080c0ca80100102e545500f081603000e00804540700c50f00105080b840440e0651541c4403407680b00c0e40700500015019184120307a490000121241c035048252040c1c1000d00d941d0342600d0001c81c0d0102142d00325113a0b02c15150803042035030052a024002d5009100240c50707c0f48084002140f03841150080d00502d4060021540b0341c000c1607041000c134034007144c1c2c82e59003185000040c200c00d04940301300881200c2e4444201e80c00185010114000c5400040d030020390410085a161040e500421089086c40007070281101c1c040f01060001c8401e802600c2d2030140400582c00c030310344010321551940085808205070070b01e0f101d0755410100c4e601c42002020304041000d4614000c441c04400d10580000352107200f17521404003240c184500711003510f00d41c0c10f030745460405404c400b02c0e403601403602214001800c600c140710081c0100318166019a00d210243c00740701c40355000801c159214443c0211200c907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 695049028 1250 695047778 695047781
    0x6030609060605120c060301032003070603150801060513111b060a0f0209090c03190f0c180609030209060f0d060b09010f0f0902031509070507020f0a260709 69
    0xa00078454100001c580d030504082008842c5102c4110405078000061201c4545454040700e040d01c3c0c000309100d016400ca121203104045072490711517014081d0b160002180b0742c158020040c0309440c1007281c6403090b00c800c4520f080303c0d107a01c2003540c45541c03c0101e103451100b0b5172042c142c203043c1041481c609091507000b804100070650070107000340e005008000c200400d0340f00f0140340c5941c02c0c1e82946044c400c140001c02802e0b026201001001d40040412150843c0211143d8110300d4480c0600c44070342c1003410b1030014040d00b501c101c00b01d160f00120000200c1c100c1404e00c01e481d0142c561080240c2160280401c8a0004100c0341e0402840110301c100b41c1d40d4607900340b201500c21003011415070300407001e2100c2c0b000d06070b01020386003082c4131062100b03000d81b000d0401550080703000141c4030f0f078404043c510f61900f0450304030b42100c203540030312050fa90300c0310040a07020300035500302401d00c0c50368040c0b22a92110b07100384c910081e0032100920300140022a0702066611050480e0b284940314445c680 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 695050278 1250 695049028 695049041
    0x50303040602070810060308030f0702010b1002011407140d0b190e072c01032703090602011b05030406020c28060e0a0206030c0a0903080a050a020c09041e06060306 72
    0x41c0564044202000740c400c04024400c00700c44d4a41c010300c0f0b039525540d00d86140e80805000043c2c203259810011b103200d40300358021500d41d03200400c1c0d510302c00a03d040c0a0b000304010010700a01e680f000c000651a14010000758004180c0c1c0101d05150414540b0340600400d40c0e420040c0d845566001c400301c1d04011403201202815000d11030701028149143c0282800c06000d0341480035078440100745452110349000a0103000080c203000c0740140c1c1100319501c900c40071620210050b01c01048407418581d00c4040441910b045400810500664010170143e800000081b5000200104000b81c0040c00700d4000d007107081c4040d400c9072919584c0c0180006003103140c0d2107404101e03c00d04801e0084c440300d805118031340f4a58202501c044c0f100307a00820007a101c0180020080ea60005003070800f03c2c8140c0c1610021600107014544485012000509070344c07100c100f43c1c2c0144111100f121035443c28041b100c0c003a41e401140c2c24218080004444c00c10b07405032038240d400d1941e6050001c0498410300602 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 695051528 1250 695050278 695050289
    0x2030d0c150f0e0609070b0301051e04150303080a02130506160507091e0b061204050717060a05071d04050c130801090b090d0806060d1b020106050913030903060f0605030304 76
    0xf04110b251600c4451421034000c0140c132607588964010080c0d00041000c03031f419914241c40d00c003801c24900c4103020706810b10200184d00b03d0720b0100000d02200780300707243c9400c0c6e910070780e20300b030240d140e14004006030b0013100e24180316000446803c0090340341040050030320003407442030243c604400c0d072101410031040364072020903182c0f178002880c503058030000f01d00000003032100304001000850011500c54003840740b00c2c54158144130041000d001080000c800180340b17410140040200b202403050f2030b0103050315000000c1d800c180125450602901e042e00a0070200100210296040d03402c00028041c0a803541240c52410898613145041c12020a00601000d600105000099145c0504c10781c000070078210103a003040d101c0c00d0142c0d80c0034288070f400400817903999440c0d0326a419203c00402a05042e10b101890740c0320f0401c469501034000e80c0440720116662041540c2d40078a80400220260000f4000f420a20040c400160340b640480211500c0080001d822600ca00101345190300a4001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 695052778 1250 695051528 695051531
    0x20f1212280225240e100903060b04090203030d11130816060f020d0c03170f041101020f1f0608070b030a0609231506041d1302030d0c150f 61
    0x2412085041c07900343c0980440a0300a0240f070600d04502c0b010201d4000d515a0041c3e50002c0c0000c0b40e0b144194404c10b144400103044100752810290082d00340050307484200d600b0b50a1064aa01c03d01d014403c010080fa0090080c5107000e500359000d00007006000b01802c1030510a100c820348540001da020406070404100901e680c2c82540118288140070b648604200113481a1002c40c00768040f468107086030042c1480084c41c0340500d01a10391071410803560100c003c17540304110b554003521f01424042c40c001d841c0c41031081c4a1000490b10340045107011142c40c0c1c0031580c107004a22001d480c401d001c0d1120300d00042c044c2c1c1c03218051414106c0d16809141031940c007005000b43e07441144030740c1e4002c2c0f007e21800c022004608458070109440d2041d03d10b0340780801400500507051201c0803c1d40718600505203603456485510321402d070111001e036122058001c10000700f800350841940034010350000c0082084104805048482e8105000c080714204102044c0c1112510340e40600380c28050402d10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 695054028 1250 695052778 695052793
    0xd05010e01140f010303020c090901020d140a0c020d080c0903010b04020a022a1f031d100b09010b030109090507030f12030e0a02010f030203060105071e020f12122802 73
    0x28440b021500035250700000401c0c0d03401000060340009181406031000e407034060856656007080c03070080c000d01e1140c031b20302800c020018004a207040135452052045032001c218500d00700d001242d07900c850b87c000e60042014100490000e90002c4086c10302100024000718034070394843c0200f000c0ea0400b030856000359100c0c07103a001007605a51507020700c10f180c889591303111303e501200040d4050001041e4407114004240d1990041c0d119401540142d03016104c10034420020010320f969030031946140201c650700d0842d14605070314190034000e04a40c0e241c002c6c43d08590800700080018034000030201c906107e440000000a810010000200c0d80142c130000c6040c40c2451001d002d40d1794100c0c203408240c000b01a1040142e0300200c079054003109524005840b41d4500700180c0c1c03148a1020007800c47c1c5080601c82c0f0600d0812820500328900c01d5035241e81c13020840c42409460200c00741c4002c0c46401a00300d014a25056101801071a011403a8120b08200000350000c60740c002d0b0095000103070007400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 695055278 1250 695054028 695054051
    0x6030509120f040e1e0a020d0212040507051203090d021302090a06050c0c1503041202071d01180e07030b0a060b03040506040b070531091b08160e010309020d05010e01 73
    0x104c22076800706000c1002214054030140911034004002d140c92001540802c0100d450071580c0d058500071038846040000d103090031300b44941d031039171944111807241360001806c401410020050300c85801000e440c100070b004555003040701c040a811004940d0550038011140660b45281c0741030010142070300c8540da10281c841d0141c0c02c0061081407280110415200d4448506425084990044e00244407160700324551030102e04100e5180d2240c0c04440401c0214150228820310712812508290802000d00152418040a8403000b00641070150000c903c20004150b4049445600c1507404000040141c1c94003072100c40c80d08245d50075502c80c2d0004041008002d0b2410784680c0140c0581896418103d00d81c10403052103248009502e28051100007809603a0030300300100300a450500307428000b01e02c03204060703414044150542000a11100d010a4180800c1400310100c030140741d8032200c0e400a410019005084001d804a810141e0110540d02160080c8220304034281c00d000045001020705 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 695056528 1250 695055278 695055299
    0x140304150e01020105190f0e07090c030615080105010c05210405120a1e050309030109121d150307020a0c0e1006110303040b0402030f060106170906040c06030509120f04 74
    0xc141e5281903a142c03006010711848090010000341218000120340c0102141074a005000e40000e82c0c200e80c4100c00000c02c0c500c036990854074161341159030411950b41e0715840c0328044000c8420503000309202c0d40050155510584410900d18081c1044440c080d08080003803007a4403100d01d8040800c140804c050080c1e24103402e5102c04100954010700c410003154032454540303142281503a14203440150904d0030040140213841101d0801002040848103908080f118070442c01500300020303000c6420450404000c8507a050310b03003030290219003c20030100c103292aa610182140c0b003503100342d68008000a812200d14400303001c0c07083c1365607002d05000700f4095041c18643c04c44814407102d41542e07079042d50000300356a030064100300d0030300c11501c80d40042810184620540c44040c0605000440d8107900300041800f0200d00c101907030001d40ea0041601d031507001c00c1d50010f1003a41045010801c41c0e1085d0003268001c1d40310025074480381d48480400c15190300c20b01001e2403445001c1010040034014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 695057778 1250 695056528 695056547
    0xc0f030304031d030d2001022205090c161a100801050a090f1b1d1603180b060f0d0606080d02070b0f0708070b010b07062a050714030415 60
    0x2c0904200303120f040e01d00001d032a064000f4841007048051400c9a440500340e0501e1031864400030001c554400b50003052640c4602280300c1c3c0d81d40040506000106400c100c0030b043d110350301040c0301c03070300b0714106000c184003491103090190741451412444503007071048218041c1c00360001c04a40701c101c91038400326900f075820040c40c00003070b00d140c01c0028001c07441e0b100e1001e800e260310002079504500500c2d0b2984c0010801c1e0030000140302842ca55241e440340209100f0f0040c10035036240241c01c00015802c90980c3c2d6500e610170b0303621007208801400103a00c94509034021000600d003181c03051030103000c030391056420203060360306946a6030b0410001200307204803500c03000544080e003020b6003000481c0348ca911461a0f403400d07110000440e04c0611000c441610b13906544141c2c89801540d5070490f4070f0075500203040981d90b00d071038405407030896000d519a500e000300d05c0004031404080e14100035200c5400c60141aa01840640440c4400b80d1060004201500317070b01d00b202e04440c138040c0300140002d80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 695059028 1250 695057778 695057807
    0x1050301050c04090905010608010507050a030b0904171614071706010e0403081914010503060a05090c0f0d02100309140105090303060d210906180b0a0e01050c0f03030403 75
    0x502024448140160400c4070242c940d04c14000c60018040e00d0b103140107014075071020070a94640f005115696502c0b00c02071504640f41d6234280103141c80b140411680b100d0a0350000e2080320610344040ca2072940b40084e00102882c0d41051503521030b1520303a145054080e010441d0350782c101c42c41c103000c10040c3e000c400001c11008002400191304181c280001c2e0000544080c081c807840d4400a440010300d03c076005210300c0311000a0251060b03c8203c14041002030003418400d024a038002900c11409118451044001e100208403454480381400381d146c4c9621030381030b00010842520805601d62a20390300300105182e40c00251300c0624104000b104000c11241c5000b030741420148540c115001080e6608910200c540c2654202540380c0740e08103c0080128401c43c3c0003490840302000e41190703d90b021a4801d440c1e42d0703500107001c2001d401060990040d00741c850814050048600d1203885194049081810326502c0d007005c03001d00602d000494070718105590710000030130081680c4284040a000c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 695060278 1250 695059028 695059031
    0xb040308090105090d05070b03010f050d050d0f020c150c060105060a0804060b060c0d09080f030f030a0f1808091f020d111e060103020a050306060102190609021807020601050301 78
    0x18119a98446a4400c1144950400201048601050b900e8183e80c0d22040c3e4490101c0d5a459502e04407100c403900709200d0f185800610440009060030a80495a04298028007418004004040940b01e81c00440c0003801148650303030603c10345454482c0442400c142c1020625102c00410342998500001600300f18002c5c0b10900000b403206400c4211a90001d43c84280420031000c4400465258015000071251501c1a041c4000b469038200c0f00c3c42c41503078100e1090b10004603c0348030044e9a44201606008070039001c00005100c656079910128400d458014049003075130089a50b034104011001007a19805000a103822040c581f0104880700c1940d181d2030401000c640d20806500d5151030121a020720103805107a02e18410144503030940c0c41d400d40d207100d4040703030380f18510b581c0d650302400200d006410b088d40200391850002541403140c03005900605030f541d81c4c28501c20400d8000300048038078580320b503080401070ba50541d841c011800ca0f4042c03900d00303141c030070f400900e411010780c4a203002c2e9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 695061528 1250 695060278 695060287
    0xa11070b0703030e07121a06010302121501020c031212150303070804090f1401060e03010b090117070f030c060c11090408120a06290d0c0e010915050d0f200c070b 71
    0x5c0d0584a601f107511201c2c0c02c84407040c0d41da14005802a04c240000301e007000c0000070410404a4500343c1040c52440281d00302e030300c00c9102000f0716036503040da0307684c84804560600c142c400980000c818182d224074086196070300304000c040464515041140c00300c80600340030805208a190910985000f101100418000a01100c00b0290100010b008020400100111107050f94400350006400c1442c00b8107510481c0da51050030022544902030b0000141c01050750001d811845006890300743c1e070304443e01c4580141303800c105488581c1c0c0100221440301e010540e6840c240d035641d528070f1142e8000c4060640d280040695035800b004010440584a4034141040c0b009410506100499070302c26840901c013000400609501401590030030102203041031402002e20354840310804840d0820780700e000d5005c1e01c8a1302c048210881e1b6420000250090081155054040d0000000d0064400c0005018200c000c621404e03081007402c000b26800000916901c010400c108404c02055001401402d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 695062778 1250 695061528 695061533
    0xc0f2d12041d072109030302120f07030e010e07062709020315011805010e040f0501090e060c0a210f0e01090c0501050406080a09050c03071403010c080106050a11070b0703030e0712 79
    0xd41c40c5100c4028441c2e505c1c440e02d01010700070350449034000d01c0300380c2d105840d203030161032062089001c9501100190810346900d01da82d02c140140c5c107d09445d00042c04403d410440c0481e00b40d450462480110700d504020100d081c0c07032850508002c2c0886c0c400250752450f080000c1089481902100c50401680f01e040201240e40c00840105940013440c0101e10010b24000040180603940742d0402480d281c4000060510003d9101b01c4400c1505030030380d001e565504201d4403040c06072070f48030b2005c00c680c000c1420717146500e001e4440e030b807006e03100c8006001006a0104e1080741c15001d0305440ca40e41d82c0d95140c0910508102e503a005140c00d281151426040c01e000a00c81c48010300307141d062603160000340c410003a007406010191100501203844940da22400f020a04800c0c8003014025480c0064022a00340304031815070590308203450301c2d4a03044281c1c0f012902100c50441050f101e004803000818809070700001861091301aa4011540c0c51003405843e0825610f6400000022140d0801e00c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 695064028 1250 695062778 695062817
    0x50702010203120702030921012a050903031201030506100b0324060705032d0a051605010e1603020a14030c01110a0b0106050c0f2d12041d07 62
    0x305880315101c4043c81340c4400e44141e217180241c07210741c1d61244141440815440a1403413464960901e40e0090102a0128880e001c882040c00111000c104201000d9141c440c040e01c001c02174000060212490220100300500d038512080e001222141c11200500500c3c1e000703c601000546111040c60385182040c010a101d8140107040540e051043c1662001d6284d03540c80c00c0d600e034130fa04481034980d20091007070020fa0001c0b0001c11310400c400c100682c421040c0240055030300c15007454039518500038042c4014426120180c004540c250340786e4080a280040502840801d900300038540912241144104900f403d9141c01089040c2d1994510712007c0c2d8001581031007808003070801250403001e0903078450608200040240406100300300003c1c482d9032240040854002c0102900c2d080e800440700c950311000100380c40c01d5401101180b108521810700350741c00e5810011301c12240058035207400d00c1d41c6030301702c0c4d0b020310f66000681c101e155000d0101500c07103a000381180307080c6008100001003a034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 695065278 1250 695064028 695064037
    0x90c05041b0e0f150d150801060608040303020f071208070f03090b0c09010203040305010212060f2d0f091f0e0f0f070e040e0c100309020f091e0f01060f050702010203 73
    0x83c42080300030300e1540030752a40302610b8101c0854251a0765241d403074a0022000d0002264648040003060354005041003040c841c0c0c20a494842e50b07154415100c0d40c400b20301035000308a00742c001440030040d202c00613401810388502c1440c0354030340c0062031800720000342c00300c240b2068490505041c0764010f0002148103170076a40c8050941c9a02c1c0d110403107400103d1030f40c0500e4000806c60b620004900b10b070717510f02c01c000e0381c802c1e82c0840303440c540203104201b402035900c0100d09214003c405002d44d134059001c0d0155420001c1005820305030300c680b0b1b03640020700c0d550081c0c03010b80d9810740400e2401c03c0000d40c1c02d9000c005d041d006107114000c0c10030300c1a00c48089401030140344030200010124507840e10440302550361210060080c003040106004043d120003102d6102481031500320180180039001340140c084458000700314600b0325400700240400d44800500454014544010304c100c0c1000b9202d0003400b400400f40c002c80f00e036040290140c580300f501600308043c480c003407000c0360060303034000111f8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 695066528 1250 695065278 695065307
    0xe0109022b0902060403030207050f0607081207110307061d0c100804020301140c030a0509061b090301020f13080c1f0c02240a0206060405070203070308070210090c05041b 75
    0x441c0c80c07541c0c10019401450704480c029840000000e0000034103038009148000d503001120300203c0029a0300421105224180005000d01e90502407140c66440309502107911400d6400d0540c0c44107218124241181c3c80108c08075809559406c00080c03031580d05840c18007407148100201500340d2040002524481c515500b4401c001810b4002002c648080d000b500300c410410202017883d052035448801c4a41040718420869450400001ca0580001405c03e010f1801240e901e52403038370080d8500041c3c0e200d81c040b01d41540d02000004450070741c6c80c0c0103000c0c0c0356201c200d45408600700030302c860030454540800c521551070b84011a018a184407070b10f60100314142040000d541040c404107140b03e90400c0312004403015030810701130041d507440040c03200c05482d900743c0721140d80345400c002c102d070402d981290060b44184440d80019000345e1140707400c03170464011200046480e99a0000791807299100321041c4618000400c264142401054882c1c1590398540d0710800307182500070700500100846 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 695067778 1250 695066528 695066587
    0x10609020f19090302060a0309110d0201080c21010605070201090807030203030306121e0303070e041107022e020714030c1e010509060c01060302010207061103220902130e010902 78
    0x480d0072440c080c4250f94000c540c007400150325004030304d00c05001081420300135a841e02c9010101010362520810440f0b1085d0b05841d00c840755103d075101f1380c4007900000341c18080d1046081c1501c00c00074181004038001c1a140d60760315507403e05440010808001d035444090aa403080d4000d1006940110640368005ea045d125804180c035803400807403500802500100d80c107450401c03102240307000800118419103e0b511082004140a01030000701ca1414042c3c8101c20010301c030a8005240c0b184804a8004124910031501b4101c0d10300580345030034412241e00980d00c61041008003120036140140d0411044018215901c0b600002c200c29000940203540d240d80d50380c00031211a03000e44c00382c50078901d003d00b40b26190f440b2198034a0081c00903000076805031084a0700080d105201e5076131200070386c100e0700185003030482043d503042106052801404040d8119500820000d4062014086060990624043e41441c3c06c1c5203146100c010f821000c54039004000c1d800034140b0f002105050589140309 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 695069028 1250 695067778 695067817
    0xb2809090c030f060504060b0a0503030f09060915030103150209060a030b06131e05030129010e090a09060f0c020a031d04050103050618030703080612070e010b0c010609020f 76
    0x91404259060b40c0000300000300c0d541009003800000c0d0b009500c22441a002082901c503040c08101d0480d5040c4240c95050703104121005030120b20340081e004440010702041d003807480c0b104c0001c840c04100c1901007841200840104107002e0721031030040805641c0c6204614020722400400c1507403242e401c18000745902c4501c40d03a501e403103000845580c045542c2040910b07540703031060340c0e6031b40200c030409110090306203030007190300d20701071040300401e860348600e80c00000a10704460707154421508030b06040c001c488d10740380015221a443d8a12030400040c00260303000b100e242c00411503010060b906601450402343c1c035001038000400c890700300c1e010f060441c0c2100c0c158035807080694008200940050900000004000c400102580149841199031001d1703e2203141843c1d03070f405190b10240014a02c1000b045803404d01c0070041d0847c000b00001c4d58080d40e1502040d4100000c207034010540d5440000d41401105401e200d400080c1089420070f40c64540d408080c00d44500a01c0c0c0341005090210a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 695070278 1250 695069028 695069033
    0x9030c05101404080123060d030c140601150f0f09050409050f1e210d09030e1f031103010e040624030b0f0c1c050a0e100b280909 57
    0x41c80320810b0010b5140300c0359901c0d1039420304c2d400703000c03c104444220a000700311506521034146169218401c041d0860305ca84510351000c40711700d000c84d04181e81c0204000110000c600741444441d02900180f111b1004050b98440000d2940e80906594000c0000d80d1a0b001d50707040e4059200b0044900450340445c0d21042030070098204414050f2890702441000c0b14401c00006102180455040c0101a1084541006950860347c10503244465001808002c6001e00f440b196000740c82442c0640707844e00090300907002003840c1d0103160002c0500d1840c14514010102c4c3d050040c52090351071012510f007554544014045150380250000b001503481e000002104101401d0f00303401241d40550302074420b42d59040c14581d002d81500e4007448607890200088091180314203e1b0b80810030030343c40724001d0051058000040c240900107481d06030f00c490a0701640300040200c201d144107540c0000030003030310314420001c01c40001e1000d201001d0001c601d00e003407a4111070391001128040240450214186e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 695071528 1250 695070278 695070287
    0xd0801030b060f1c14060112060f0e06070804060608010e031b010e03210114030d030e010204180209040e0c03030d0b0303040522050136020f07050a0b0709030c0510 72
    0xf500840d004551401200000105080f5034200303c0d004040f080325560203d0002621080700b400340c0500c0d1420308080d000000c880ea48040501003d802c07000980040300c9800d2401c0001c241c0c1c1d080000f408240500c0b0070301c03a01e4858240100704074002000f0200d03c41e12406d45074000c00702c024060145c2c601002d400c003103080d045051410740981c1a6540e81500003144004207030880b1242c000610140c1c00815240d051040d03c12040f0801002081c1900ca05038044010701100b040907001c0755024000040d80704078100f1740d20130210603c0c0c0096142e41c01e5405110071101c00703a9107050703036134826003452185480105c03c0301c1000541500100303600d00e602020078507501c1940e00c41900000c0c100c0d903000542407807146a403120780040b1030510441c1d03682d80070760000d1a0391000025583c00c0c001b03507102210711240e10003010f03200c03403007009410305464035109071660700b08980036107107600220000b20410100399201d550080301c504040d07450508640b1880b2042507180910340c0543c03d41a4102c1005028 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 695072778 1250 695071528 695071549
    0xe0414030c0a0309050409031b0507210203100b0a030b042f100c0507061812110910080c010305061801061d150901030507110303010303020d09080d0801030b06 70
    0x2400c8940e1100581d80c110780d204400581640055403056010855141c1801800c0c005e50301a0782d003554191103140d660781c0c000c2c0d604200300c986110701000000c0e2110a80d03c00c08000302030b51209280a40240141818500140c00b00074031fa914245503c2c0444d40e5562002c0141d03508214802c1c0103a90354545580100c1482038400b443c05001440461060040680140300071803d03510035004000c408010b0343d5071844084020240c0d0408103081c80302900c1500500f40d02b615821581100503980d202d03559105071f1011083da00704004c000400300c0d6042284546400000d81c0c8010300c1c0300c526120301d5035203852003034482c01d040507201d01c0424410f550b45000c40d01d9041f040e2503400c499507035400d4054044480c5102048044a6a0000d40e92a02c4c0c41d09407503c12841110f44c0c07500d0030802d5001180108002010001880451120004000010005103019510079002020380040300070002e0114190303a03025047c2a401030943c06209503100e210141101d03840071500003203454050016011052 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 695074028 1250 695072778 695072813
    0x501150f090911031e0402031005061804051b01212d060501080c07020105090f01020f03120105010305313f08011a0a050f1801090803090a0e04 63
    0x41c03c0e4496240001c020046015003032401e600f29080020907190418924126006503140d08070612186441c440c54018980c8400c0080c0031017a2002c0f00d036050218140140d8090762035a0088811031070a09111f40f120041060900740359201d5071841f0081101e25903043d04181155459400c04c1c0100002e90159000d01444018030302400032112a2400c020400e40c8034280c00681000301046a0b50411400c95181e0f6406a440924021055080c400141c0e003555142c1d04601c1200c0c88204d0040e810b00140a110080921075a40c0e03501d001c0004041d01c8019241c178401d0841c45080003088500d510003070b01441c002000c2010381003000c2c280003400207044400710101c00c000c2d000540c0b140c2804200031035903440c03c92540a0f040001e080441e4040c1c024019030080c030a90002c4c0c04d0081d8828806400e42c480c0e1441c00500d000104d0182c00025004030240074180490240c400c03c0b00d6030082c107840c02402107000254180f02a20340010a0089144070307013501d4210603008038041c401c0c14043d1128140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 695075278 1250 695074028 695074031
    0x7030f0b040501150f0306051c050f06040b070305070923010c050316020a0e0603060c07060b1c12021b06160215120f070518030c0406081f0501150f0909 67
    0x6030740340740541d8042400f00e0f4010009840e105c9092055000e0700c1004250b0f02c1c013510351450f03814002000000c2e00959181540d8a01c5007406e20141c1c0c10003000100d101310300c6041035800a040950000d015510040c09646c14003c00000511044100d00d9512050f040c64511101c2402c3c5003200503910b01402520103041800000b814a10400b8110040c5030b40c40e03c20f4032419031081c5e890b90007240b11002030351b12540c1a041580481e240c00d250348041c2c16454040c20000403c910108c002034030440341c4400c6003254281c64034804c01841801040c4001e9103045001030b02103d4030010105001039664540d89124142c0415100c209900590310080c040d0383c0600340701e40c01440e407d0707132503440c0e005005950650f2524000082e8801c000c010418001c500c25100c080c18504101caa01d2817100f041c4840070741500c50034034507015a0307076540142001031010320080d10306540c6140c0c1c250302000c00c5030400d40d4094103100040044100794001d05040b107126140a000c2024821002c842602941d4040103116 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 695076528 1250 695075278 695075281
    0x30b04032706030614270c040b040e040c06030504050c1909050c0d0525080411180603160f03111f0e030c010906020c04270609060510080607030f0b0405 67
    0x70f5010742c021815954103001080d4440741c504200048042c00c1c180d152881d00c0c0000090740c5041110161903006041c004030a403c0c1900d030070320080c103600558003e070b01c0e801480e0103020034842c28140e6000034040e035140500040c6007940742c00b0390b1094801140b6014004000c075050075100803d80074000342c040074109000c5410001100c010700d07000003281c0e100c1d01303140c6030101b04d0341e82d4132075144040d80d001c540141040ca80701000507144840b0080041d2400c191000480760250784a080399800500c070301207447c0490405e403040c1443d00400707264004510286a83c1446102a00000f0700100d1b0750100544c0300c0c503030200001c101070a00c114590703140d02a188021251803508003076590039405040e02110045035601c0c00445106e1020300c039030405a0401d105801c0581813580120000c039250201c03084544020582d45074100302c0d80c800c1581e6403036480000c0d004103e42806510b0300145040341c8210b400d410007102a803601c43c090082c0051541e9102c1155800300581c00841c440607008104010a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 695077778 1250 695076528 695076539
    0x3060603043323090703110f1201050a05010504021e0d0906090f0512120c0a03060305071d06030a03090501050310080a0c03050d2f030c0303100e0f01030b040327 71
    0x14010f046a03200101c0c40c44103100c080c4034100c9881900c2403054100405c1c02c01c0ca582c841c0c01540020b44442074100401050082c001d0b254010840651011700340009001d2400a081008850303040e00036a200701e0042144c0000c140c95100404140c20040c650255600f203407600707450061011a00080180741007030f0071034092282100c140002e0724042d00070348468001314049001280300d006c0300b15054041a001145200901070050b22062481b42000203045440b51191803410030250f02201070241e800c0c0f805400940c4010780e45403c400168011f03c00b48001c0d0350041d2181049004d018100800400010321481214040c840200804000d031a00c110b000e04001010000e180815a4180305502e045005031f031140c0801d004642c982003801d1001226805600e80205841036071800790320042c071039025095410b200550181072152114040c2910f05268078014080041000250000050041000c950075244a960159040c07030300303c5020200c54440d18108401d2107200301c40401c0d46030040b81c1d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 695079028 1250 695077778 695077781
    0x901020306130207150b01170108010209030f0a120e010903081206101b15061e050307061806210203040f0203100c05090405090f10090b0c030606030433 67
    0x1501040d00c0c28400b400660025a00741c0c41201d0009107201490b1013a50400801c1d540280b61510051421200b9290b107002030320084402a000ba010766580007590b01d00c0c51404100c3c0d0320040780c02e070010700060881c030340391202c40d001c130700b1103007405e000d0468421a0385a104405100265070b01c80308807a140d001c1e15440c1c0c840300c0760460380385006003243c00611600324098800b6a01303040c10034241007002025980c481000b02c0c1414400466141c441b1070200d900f901c84400d8407500c0c0b0643c84440e5004c3c0c604000c0520348012913000c203041c0100750343c580d0403101c0410341403410307101c0c0b034141722580780c0d414600190540d001e05850f41107540b000c0140300401a16040c04400107008404a039080072110808104484a409290002c00e004200e038090307500701900100d610104c0c04013652179403054560300d20f04200c2d0070204c240005a588126608005219007040c0d040510940c8039811458038201048041c400a88003510102e250241001018204580a06584858540d071402400309011300b10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 695080278 1250 695079028 695079031
    0x220b07030201201c090204020c03072402040b030a270605042f041508150103122307050a1502090406080102090108070807020a0f031d0d0c0519030b09010203 69
    0x40d2520040f90320038440042c40054800d04000c00248606120240000c3e00060000960898129400707205c2c11198007010300140c86440c0c00b0f08400c0f00c1080609d901c09060751550203014810038030500003484010080c1003681e5100f100d4040004100c0e54158400a4003030010102006400c020b990310000c1081d56000603002c0c501c80c0341c116032260141ca0202203180c5020b690f07d0b540351740c9128220740c9454550054108506c041c0c2c2140350841d00c5086480c108116a07045420076521503004008010100b0310a80800c0d0f994030700501c0654212044420344400a00f020030406800700703401040c80000c1c808000002d5101d40c1c000c960b003800e503036144041d400a9240ca44a81e2800000041d40c09040c000c42c2d464410503901c00c181c0d5075884005450000000c0c084104500c2101c4500002545880c020b10b00750f03009454000c218409941b4003122100c0c903114040c0581801d024800010300903906510694400720303105000c8450300b6020038a060035650024045114100034826103900c194001c6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 695081528 1250 695080278 695080301
    0xa021e0a0b0a02121509070f050706020c03122202121c08010609050a0e060402070503070f20011e03051b040906082505040f0f0c08060f0d0305220b07030201 69
    0x380890345c3c4400e07600f0680300724441c140e60000f4207640080c1c0070034491f28014040004030300b082030800025407100402c0b07070050031501000b0b071700024803041c0c030f02da405440f144e101c15485988804000f074100040580000081c0082c043e0035182030343c00c0d81001c14040c006007240349510700ca00d14810036a009005800a104050108840700310100345800d002190b1001d648404088580c02d81750181840000d40c8080010349071400103006440008d070001c03d0050155005005a00000c1741d4408103081803003148800906110440c0d0804086491100d02c0d540c80141a080c006900c1d91142891800c03441c883e040100c5540b000200403415003410361003001031344c0720745049500c00c008540a401c1900060b0100000f81da003800001c014501d0103810001e9541240340c2e0200340220b10002c00740c2a11003070b01d1581c0109010004000306802d01c07901d1040180d5044907101052200b98030040c015101d8840024524860300203030322061a041d140f0000101440049696111411300f0024020154400303503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 695082778 1250 695081528 695081557
    0x30717160f02010c081302180a050a0b04020304121827140108121c0903080a0b040b13021303020a060f1b08090108130206030c090a05060a021e0a0b0a02 67
    0x8001d20780305215941c41d14820781c0307485210352940440510030440d803040490b400469018221400710144d4840740c000d80301680d002c615410012643d9043c1d03004088040d016602c103000f0000490188110168824800d04041c448071203a03006c001c58150094019403006100b44c0304942411040c070f44012408141c1c40c0040001190400301608641d1080c4515019540600c5001c0042034814004001e811a00801c42d0001103615410f101032303c8603240250b010600001c20420982c50324091662103907400c9604101d0b040080c4005581620101620920f132035000c03070b54040004030b510460000e590020010018260740312401401c080d0003041d610001540c00300c0b000e400010400710768400d0342e03000c038040381041c1000b8011540710320010003500b20107481c1c2c1802400b6071580401940140c082056556039036100f40107102d48aa010703407100303028045c00c004031560a5800f050200c41390b04004400291b503501c18842501d8042d42100191800400c0014442d2080305036005004201c0c40c0420b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 695084028 1250 695082778 695082797
    0x1006020f0109050d0f0216120201030b09160c060e121b150f041b031101030b062106031c080106030e0d020a060f021c0b0a1e03060203071716 62
    0x310349080c0da090880040c0184e00000d180c2c00c04174042d6a060f07039600c1c030910448a90241c050b02e0390164140325405038503110107603a4940300750b507414010303007039101740c25034000503a420711515201310b410005a0b65403c020004a481040003115008040551500303000c583c07403490008443c41080c0c1c0801c4101c00412000380c80300180403408290700c41205001c0d050b81030182e43c0c10347c003030445502c01882151003002d15200b1007101c11080d41201c0c040c5021744200e000042100c070026003101c1b9101c034224440c98040c03140078060003440442d448a003000e02510200742d140d5201191800f03559154118100c0c840400403203500358494003490483c0c3c0e0b199030a001c03800c83e04242c0354461521703c10300310042c5c2105401d5408180c841c3c002c250f103640740030300061038070610700c104840c80f6107031084004a064403040800030324508030703501c0c40180855211100d8400030715050701c070600020344801040240c010000032101c1340548035414240e401c0915258661402c00c440c3c1e09402603085021003c200e2148 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 695085278 1250 695084028 695084053
    0xe01050a0509070518040b0d0506010608100e010302040902061c02120114010f0804050f1009050f07080706030c020705040e030d05013f08040e01170114010b03130506100602 76
    0x59629018400d00d41352140352507030b441400460250305035201da40103525051480071715140d00046940d014003600150155505000d0004c00004010f03119001d6075042102c10300a1009100c19a8112070b41104d00081d0180c1500c04a101e901071030400c0e1864105c0380c00210000c00b0b03690010003000c2d00c121401c1340303030382e88071041140f0001028ec0d5060014543c10180307400d060141400c19000340c0140200c41c02090006241807a000190030501007039a1500c1c0104208030b010400341000c5850070010304080d9042c400300750765899040c4121410580c6850004504500034046800540030260051090300d140994a65587d0b00c52500180b489184c07000000e003c140350a85111290380425020205c660030504c42c3d8640048942c001c000c001201e420240040d00d109c005000a1600c14101c0d21590b251600e003440081c68403900a220381d06069806404c40620b2640605458452201684a4443c00240741102510b59401001c030704c210814005003603101d20b05c3c030003150025800c403401c000030034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 695086528 1250 695085278 695085289
    0x6091410080a080301060e040e060c1c090302120d0e010c09080c0d03050315010e0d03030c080106020a12320c010f140a0203071205070309110d030206010501080a090c0e01050a05 78
    0x42e0b000b4140f140c0510061003101c0c494901c1c07810100c0c00901c0030800b03074003220f0a2424694291199203a024000a030601d03001d4241c555000c1b00660124100300403142d580300030351540c1c5071068419402400044400007038403154402d06000e00802d008000c040d81e040d4000d0004c0f0b0b034600502c800c5200380e1808552034500310040c0b03a209581030303807100c1c15500e500c03010581090000058a060000c01d2480180e02c1e10350701c02c44080207010350b90104215a0485000e0010034060f00712100315041001d00d03401141d20140084004051440c2c807420134410040a0f0b03c0f251503142604420700307116000c80ca10041c0c030b80042c116a005000003009010300d40813840045800440c105c84005c11358000103034209a965024503800001400d00010700c0c0d4050203008100e4100315440390200f81e4400c2c0315014007007089200a01d801c400e985d00200c0c1242514080c1d9130f004148070701d5040007209400510114095084006500e610604800b011a1144601a4181824012640290360f4048000754600d0035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 695087778 1250 695086528 695086543
    0xa0b0601111617030403050a06052703180a0b0715150f030b070513030c030c0e07121109060403051b0102030f04062615030115060f050d0609141008 65
    0x140011003031203034900300c039101c0104402c1d0360910f0540814071002010804c188110104c4038814500041d05140030510f4000c0b00c0004520780b840340b52030b2070607100101c85c0003044030340201e01d00300d09a114400b000300041c058902600015a1380303001050060401c046000c020319010115441442403102c107261113040c40d9094881d50325035242c10b0b5002c0010070101404e482d0802c0321172130528604a094041c1c140200e166030700071a43c0d019810340410601000e269000060903a0066590341c0d81840c00d001040d566160a40d107a01681c0c03003510b2030f0725007802000c84220340d10207040c150701c40c0d03a01d0908586404034040c1c200762401300c4e12403481070356102000319004d010060316818140b03810132808a4142456441e41c031108040d0903545245034441d403141600c00c0d0f400003202080c10f035000040c9801c0da44680c2d14524103c80442c020703c212030300204062000d03441d520f0025140c6c550564000050180c0354008003401385803041c070400303000c420901c00c2d01c283c0c001100d000c8146c0d43c884050f5a2140d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 695089028 1250 695087778 695087803
    0x4020d0e072301051b0105040c0305070e0402092404050a0c0809030f0f18031e010c110d0e01030209060d240323031c021b070b031501110a0b060111 65
    0xc092115450b1503000304060540015202010240182020409400c40e842070342d05032160420410100b0030001d042048001600c6c4d0b1f8400e114540c2425804140b000e0405402ca9001207070041c0c1c1c108801100480480020034002c00501050500c0c40012009188054201c1d0010300814006403103080000211401c0d05050701e0342c18541400c14082c0c241e0350300880010641e000d4100340f66003560394100040c14010b41030b12075545480900f6100a0b0031900250041d0051000e6208400080d150120311024014603500700082d20800c010012130084c811541440c0c0c0c03002d000b01d0703052040c8100d9441400c021034040400c8042e4510740c2c00000104000788001044500e0029241050b0190683c103d022811301c2d0b02164105407215044412b140e00c040e4114001d20340c0400d2000c00e00ba000c1c03211b044070412010141881c0ea04003848a0f4080c0b1004100030070180701d10b100c8840d140d105840184082442d14142d456840003403811000304031080e82d285000600c592640c440e0a080490843d62110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 695090278 1250 695089028 695089079
    0x213051f1a220914061c14030d0203090304030b0106021f09020d0b0a0e071d011e03020d0c060216380414031b01090905040204060504020d0e07 63
    0x291403100e003119803250150900c1c030849900120b2440d0034001d004005040115800301c2c044800012004040030020b000b43d200720811140d06440f650400c40d00704501c1d80203180c01d4007503c04254468918811851030141003440041081104a00400a00b06030307446375450b0706569903a44030807a0707640c40103c40d2040c0340e28502030012411807640d00c9000e100b4400740c441c0110360101d0302d0700d041c140c000311542e034002911100c442c2c44610090000c1006800031181103120b18102c04c5603200c0401050042c407003080403903c0c01c109901c14510b8444000e680c02001500030070098034043c54040c1642c070804000d44100080500d07211a2400d81c98140c40d80b00100105080c010415071039580c14010415918202d555003141d1140006401840540060026001400b4609080c50f1615400142101e070b0a03c0c4074141c4184e40c0e0344425a44210341c00480c0101c0d16488500024005100341e60002d6442840003506004110b55500711210700400390090b603007580c0d5a0501c20b0f040a01490807c100e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 695091528 1250 695090278 695090309
    0xc070b0301051806150a110d411909060305040f0303051807090c080c181005090a0f03020f0d020f06400605040806070e030a0213051f 59
    0x740c0001c208194080d00003020701c260f09800320a52a0940d0100014200190140301c7c5c030038488034204144081c2074032510341151803000c5903107a070f01d40c0840e1f41203403c04003c42070045044202020303c01a22032085111443c0c0e00e4806002d0007401c0004068030f00c0206003030400c0042c006010b803003010300c02d94211049160050313007650114014000146884168154a00800342440d82001f05401400303004500040f0a15880c4025040000c02800801900300403c180203030710300c11020100508800303072601d5207260480326003610ba81c00343c51070864004407484c00002e0120910044401103a0007601c140c51020011401e11044641d2080c0c081d4100150a00c00c0c1d4042c06c1c514020b003000342c075801440003d68503071407070b610081c01e03aa0080c5440441e0783c9449400d652811085200500650170a503240928250b01c40e41c0300d0400404910030b01280c180f085d04640c90038059030000130750040140c040041d8546080c0c005110680c1c0f00b92104280b420000d00d0b401000a000098841c0f00350000202d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 695092778 1250 695091528 695091559
    0x70206010602340b040609120206090d1a07020d030b010203090f09070309051903030c051303020f0103020d0203090a03030f06140f030307120203090f0418020904030e060403080c070b030105 83
    0x54200351604201c50b1401140e0902c0702d01c054240c000301800c010340c04281c1d0791b450070350020140a0683c10481e41011201c49060040e9689802c58244c200140c0307503400a120607003840283c4818180301d440e000b101d01c50801015075404101d0401056080d01c0c02c00c20b07455440012640c0703000754604150005620070700340300240740144c0e10079482201403801254500d040d0b80c5035410300d44008242600b02c0b1494500d45e04054143c021047c01404902d02035041844c8100510707091145407001a014045103030303200e18541d200e5011202c0707101d0150400c1d540c0341003820910340c2d2182c00140a8000034681110310700c00103502e0188008660103000e0851301202d0500412000b13003000d03c0e80b00c0e4144070402101000030301102105002610300d401654a0b05090300c02e0050344410254014466443d04040702000d0b03c0c031605d1800040d40540b8504115500d910b0281c9101c00c5c804500342d800000030800004000e803001c018000c3d4500003094403402c5944410701c0c20640005c1c01100c2e884160803620701c20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 695094028 1250 695092778 695092813
    0x30a121b1710050315091e100504080712210218010503270a1a06010c03030b0301060320130b150a09050d03050d05070e0319050c090109090308070206010602 69
    0x801040b030314001001c00341d44400207842d102c003520740707840000d00c118200084100f00b0310030400d00d0000e03007002c5907400b405104800d4503610a00d501151495403140420284400b000c10b1301c60781a07000040f00003d04800030050060103508840e81140c0c4a8000010b5001030030740280c0b100c07680d0002c0300c0c1203081c0c40d002c019501034000804039036101d803402056880c40864400021400340521018040d14042c90070070118001c90656161314400d005001d100959901031405011950107180002e001250440001d0141040d5800a07000700c4203c0101d1b25140e000318183d4940c80d0b011220103c01d0b115024a010584406194081c1d00440201c0071189440d0306400800100100b0310b0010007030b94a13407002130400c003981007007680000c130080740f021005440c500c2610f401102c10304258a040c2c98450019030744681044480b1101199402d0340000c2000408c038081c8119030051508040e9a160b2009000610340c422007500092000310204080381e001280f885e05036500c0ea0302a00c6100030705c1d8107244 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 695095278 1250 695094028 695094031
    0x909071d10110a060c090603021303121803033504241107030e01020a02130e0c0406080c03060f010303092303010513020f0a06120b01050c030a121b17 66
    0x2400c2c032400c40503500745603070180f0440042034898600085d0020304a0300040c940030f0690400410b1601c1000241298101c07581c0810427294801c60700d11801c60316200071590841808400220b601001101000301a000034a800c43d4201140d4280640000c20354460444135031503032140c5c3e10707600714004140441e458040124410400104500d801c82000c000c1c4012140c0306d9146120100d008102041099404518406c400740240b0003040041000c4e000030b25001062100450410340e1400e0300e03501d105c014080e1818050004000300805940c50001c19100e0001c00f0541b4420b001d030200040c030300154200c540d41aa90103550b061b2555043c03d56500819031511090340001e0014a00004107640901070340d4400d44074200981002109071050000141110907858401c5512050610095501050300c015440490401242e031501c2000180c426104502c2d0592803400002a56940a40c00001c0c10280303198507103040003112506018019640140e04594000805040701d000c000b40050310103d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 695096528 1250 695095278 695095309
    0x240f06180904110a0b0309060f101e03020411031b030a02070204050103050c010906020c010e01050f0c01290301020403080306060706150801090c080f030406120618020909071d 77
    0x103401040481000915014045404881c0700a0824000200d8140724084800800c0c4a0b030b000c50540c2000e480160329203074000c0002100702c80e680c000a84006058403c0d00080c40d010903040703005240c003041c0c0e403200e80150006a0042d801c0070700320070b10340100d00c089a1003041a0000392241c0d4001181d14000c9038805000e01c1d034046d8092284201580d2940b080500179031040d4010030201e0060400075002400e2607000000395004804840c1c91a40c200c0d8006010010034a03003103a40d0fa0919040765442c2c010344901c9406580303000c0e804070303110401d104a580e0f000c80301c64032981180000c20800d400d0703100340d000c010101c000c18000710f0100d00700500a0400f0b035210310004aa4998200001607070440640c0c030040c00c981d110680721050100800852010703100c4c080c0500003503005840407039900e2017540726000820031000c070b41040d80101c0d40c0c8a00098442128101031010703540401c50040c0d001500e240384605a0600410446030007070140b0100c580c3c2d01ca800040c10001001000130110700e00460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 695097778 1250 695096528 695096557
    0x50d0905030a0c030e03060906060f030708060c04050310060f05040905010f050c0a1b1112030d0204091b02160306020c030903011e11040b0301030b130515240f06 71
    0x44200050003400a4103040300c00b50f940840780441401c000704105031443d4614040e410560170b0000f000000304006921110694400140811040110385002d130b01754030155072030041c1010f210100d000d00e4001c00403550114222800c0300486c9181004482e02880b4581110088040420007820aa0042001e060048000003022081c14802c1010766030200c80008145100041040085030013544c651a45040d120004002d0400b42d6552400c5101d46010103104001448540103c5102001118500c00360341d9030540d01c483d5200c030b541002e4001d141510320311650001c040c80d41d140c400241400c080c0c081c6c45940b00700515548882e0700951140086000f00e000400224203942c0b400d005403880200d03a80d121100c1c0f0700f040900d0034210341904c01b41007030001d0200410420070403150251703410b480e0040020041d541f00e12a0703521040040002c010120b00138a404224078006040074030717100d042213001d0046081d102e0070800b81c0103880701303c080f036001868140d040110305004010b40420f120900c0c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 695099028 1250 695097778 695097791
    0x5250c050d030f080a02250807140c0a0608060d060b04060b070308040b0604140c03070207030b1305151003080306150309100c0206040309060f1701080102040e1312050d 74
    0x1148000745480c000b5804501440f1a9200050b8060f10349a801403041c0c01c02c50070002c107800304900c2846c00c0150b0480d1051500203aa0030700c164a81100d14040c2d01c4050b000990f0301c144281038641c5c4a41ca8402c0c4a6031a2aa0010354580074445003407041c4001081c6d0a01c0001c00e07034910000345458809142c00c07594504c2c010810030301c0c0d00c0040c40304601030348640449142034030f00b1002c08140105600e004a051810740c104814004181d9070f080440a42e90300d0712551409812031a00195910143c0840140f0092104140c2029210300d6003034017a8040e210703c5420640b03c01c400c200161000300c0c030104580000c201103810080616003005c0002e001184900001000311b0154006640f50b0310160840d9800241510107482510900345007800900311070316054601402100a620801c4c2c240449a040da03602140f15180314509074441a04400155071500074450007900940140d4034511b03001000b00355000034825005070755942c00340e5518002845108100c0e4681c001004000c0b45a44800c1c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 695100278 1250 695099028 695099039
    0xa09120f0b19060b0702090106081b0403080c060907081207031b03020d1707050d091e051c05070f03230d02070309050939041508060105250c 62
    0x221107014082415100900301c211220000071641e07144e104030f081c14803c0005a0050302e030f90600c18115010340c1024040b5650f0756102c40b0fa42c83c10444100c0440030002404020000c000c0080e08030000c070a8200d40d02c40d03a6000c0f03a1542c4000303601807413045a02000c48032125141001c001c00259229150180044644280e80d44104040b5602180560044184108140e03408046464440c4040d02840010b0a0151000c1c0c018400c91200c400a191a85001010710400e0070417103003043d10b41264804124514100651100001003031f4820408030220342012591140302515107a03504520108807100e030960b03041c2c641541660040c0c0c1519071800d44003541c2d03a03034503000e000d022801110140c0ea40b4004c0c43c0041000500380c100512a06180d000e101005180107410300221080884240d0000641604c562941010040340c8164007000030f00030444000ea074120044035003598032108125102d81006603448d00480314400c0d4060008901c1e10f10078803100c000e11821501036410306c02143d4498 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 695101528 1250 695100278 695100293
    0x62202030609061b04060503010302040b063106050f0d020705070312020106060f05031324060b0d0c0311120705070b0103080c0c030f03160804050402030415050a020a09120f 76
    0x112503607241030700843c040264100601504d10f121907880c00500d03280c00d003001c1001d0120702040c007001e80110764455003000145c540c1d100301d400d03200007400484140c4001020541448405441c400c0070960301c4900020494000c00640b64000710a03554141400707071007510440250080341055039144500007002000c41d205851a05149105a001084950504501506004140d480e8004100c0c1c00c1041204000d640b801d8501c40d581c0c461403a158241101e0141c02032100021106050385152800c0054903406141c0204001d000c8180e00340481c3d202040c0580449401a01c0711f42c00071800c000c2d4a420244022503103900a42c203060050807e000c60b00c0390004030500343c100701c0d0031120019412205110820850202d60001ca0040c01122103103400701c0d0b103d0003403014001d18410907012200400000000795800340070081c0086440b0b1420303080c180350002c466221810741c5450700b00450881c0c80343e8003c07280900040c3e16005495031070300b28100103a0340c036a141038441c00c0039142000005004c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 695102778 1250 695101528 695101531
    0x30509030a0507230610050a18090312020f070501060b040f05100903050d0e040506030705100e0102030906191d0a03020904060e0d0306140105041a0a051306020a03030e030c0622020306 81
    0x11401402145050030b546ea40d02c000350b40140d44103002c3ca00e010414824280030700c10481c1d0480e04c02040000c0103103010396041205060082e02d1a00205540ca80340d0400c401510801d4010310003804200d0366000c07035003a544918001c0d54050400084140010308216042001c0c084070743c03034160480d41e41c03512118200f80000d143c00c4000b84c10300c481414607140c980900c03500143c00314050440e0502e010000740141d162260014188010207043c02c4c83c2d81e0092041e9144500c0246c0540c3d40c1e8000813041402c4810400000c078086441000a412060380d00c550b007001c03000001d04015107080c04e42d0204030110400510494000da214000140d595400b800900c21100c03094801242d00341c18809621410340b104541241041000d00c03040204e440c08100c40b0f1500741c0b020390328540da464044001c40385807054a01c0180302c0b616502d40011115400125143e410703009070307401c1000b0340e8640c41e52520391082201c288042e612000100700c480310300e00c0340c290500070b20703c81c01400b40e4401c4d408a401d0950 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 695104028 1250 695102778 695102843
    0xf0809100b180a02030423061f080f0d110a1a0406091509050709020f0301050409140a050708160305030319020c010c1706030d020d0f02031e090a06030509030a0507 72
    0x4002c018003080051f00f4030001c0c10040c0400c2c0d440c48038800c000c0360640d6184024604902030060740243c0040000310038140000c3c240707030002c0d03522400090070700980c1d45200c003520000003208141504c80b64000403400c0d51005070f11610100e410302c10740000c111200c001400c1030342c0d015903400c4040005400d2604007802914910381c04204000c070b60402c1c50070080d9a5111034807050040019100d042952030403a41501c100700c8000410403141d0030b158410003d0020451034031304c1068402028414005141c104459452045039a0420302c508002c50013107251100600ca50303c2800410240c60310f54240754428100e1410060511100307152441c2540c0f02e480c0c0c8a404203109192030400380c2d82c143e2100742d00540175401030000c65100080250341c0c1d0700b42000d1400700146804d040741a148280116200c01980e0210113440b51b4031000355a445c2c0d031204102c01d1003010089400641c983c028040c20303102d00c03090000b45050600504013540c1da58015041101c4c900c6511807070302d05007402d4240030a00c040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 695105278 1250 695104028 695104031
    0xe04030210051f0b07050c04150f0f05130203070309080d09260a0f0513030c0509060d0b0a0e010f020a09060801120203070303050a1106090d0f0809100b180a 69
    0x10840308070104581002d45007440707010071900d41500c00c24160500354200e0740a004a40d40d50401c50074030a003411445003000b40d100c0d09240001a881212860400541d4000c6155604691342d4035294029003115109140d008a10901150502007003607000d186d01c5141c034200402c80d801150350f05801a803200165061459031103000c00d0901c500c980f0a806264403410350f00180001d070b8822102d15029200d80103040141d80208512268412003e070741c600c21081c40046000c6499292504618002c1d00419000300b01002c00600240f03018918030040b50342010b520702a075240e60822070050301820b9800f160304c0d9298210b00c1c0a2038094401480485001d40d00e03088642e090001c000c0c030020301a881903c0c4a80d201c860100035a5000c00c06100b200d07818105547d40304c84094094540c80d0385c406030110079020300b8041040640307012400a0010045e9601ca1071012446601510100429030300010a41d01281242c0003480242d800043c0c42000105a000050401b094040203050122404111039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 695106528 1250 695105278 695105293
    0x209010312090b0c0703020f150c0a140d0903060e030f07060509160b19090b071202011112010314121602010e0603060f0d060b060a0c0209070c0f03030e070e040302 72
    0x5940a002840a4210044402c4c070307003900c02e01081d80e20102408040d00c81d088020000c1825550000c1da0b5031180c00b1390b1085615102890541c0382ca40180b0202a02c6d40c08030200b01e1a525000403420000c00b04c0c0c20303100d03529200d095494580040c510710f00281b0081c80100014510365a490015180ca07070f204000126061078000c0302c090505151910780f803824807000750b05001544c0302401740e4a40c007030000c90031003503d84080d4040343c49907101d61022100741c0d4001a01420311002c0081e201800c0080d4000340551600094440b90303a100385490f0050980001d801071001420201c0e2104440000c1d004031141240d00c1640e289803030348204c0c140406c13040d4200d110002c41d604408806110401115090305601c0e02001103100d128800414900c01c1180034841c0c001c0100d598012900c011005d42082c0c0ca072102058080c1681c200850268030503040500020802807080040d846101d0380441e8901c2c0050159030b0641c0030340407403c04c600560180c03c6001c14041140400c041c4600d0191f402804113 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 695107778 1250 695106528 695106563
    0xb131104081e0c0f1302030603160e150915060702030a0506160210060b18010c05030a2102070f0206030408070b0c0301150e0603011e050907090e010e01081f0902090103 74
    0x100407000f110140074012a104907001d5039140300e040c48440c0c80c203180250fa25901c0d400080d00306542035218a0304180107c2010405d02c80c0444811322a0f9008030b10815185503400070002032580071101c0ea503110003001c00a646605128001c0c085144c400303000c90b041e145c4666162814204102c035070540100d011003031410095030401c00320300d010300c90010400609041c802220507034840d008840c0f0490b00c01810b075141c1030b4890384a11b200c0a400c80c040d2610b5110a02d001003d94000e59a01e1b096103585980c0c00c81c41e03a0785803088600041d4071001103a0011115801e01210390801081a20012024800070b0086002425554414032242c07d126550b5030401421410701404800070008000040f681c2c1030054030b0b02001c403810f40304500e02c04e610581c81c001c0301c40f55100440d08a9600701d079490342400030b201d8001d03000c0070545400990780d82650b070700c0d1008a00d8400702441414040d80c0090740c044900980c2d4030145907480d03040381c0045120146a004071348101000e0344200c42201c03d0302c40242c0b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 695109028 1250 695107778 695107783
    0x110d11091302250201110a030e270a2d0504141603080c010f14010504180302060105040b1c120815010206010b0c0106180f050106030b131104081e 64
    0x4000601c68400c50428201c1c607460400850018811011407020345011419a0b01450719201003020f440100c0c4c06101c090304e4000e00404a498840b40280511155114102c990f0b40c210641e401451003c070003159983e180901c040d00303440c402e501c9117840102c10003584685501e024144a12a44404110780c1014035000c05401030700080206a90010300d4010b50002e800b50342c0f04100c1c0d8018110030b4131940c040d241d5a0040030b0030801c41803c94030301210040c0301092458044c1c12500c1c00c4904001443da0500b015010040a003001801600045c0051100f0701e003e5020a94421010b4103036a6400c1e4401c4200f030802c40060401d513076503000001603000b0349621200c21940043c45884004110a0000c0040c2d81c800044c0681c0c000b50002080b03a2507242c409612a80040004084011030702040b00c40250090081c4d500d003450385420140003280c0300e4002d000d5145811809003043c0884123054054800406500c1c1c9100d0b44000100800075424000300641143c200351b0100b03010040007814006032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 695110278 1250 695109028 695109049
    0x120c030a0908070c1e050609120c0a08071a040303021207080403140312090d0c0201081801140108160509060d050703080f0c06160219031701031401140910110d1109 72
    0x400c0c1100c6803801c0c04103031106026280230580544682c241445c1d0b02650318201001c40c00e04940000d08a8400034088000146a5080b208955641c0d00c809100c2180b01403c1d01c2207000240c0542d11641c590714410400400414800d4080d00c0d009051039140e0303032840c85076410451030001641c000300d00c0950455007550080d402408000003480185141a00546039510089000e814001c030000000c15a040c284000e010081e07002008200f01c8843c069440f2040500303000f0803d5501c226013245003507450040d20001a0340c4000c0c10301c656640ca800401c0418040c00c40c084581d8050f0610001c00110b03c0c6001c0d007041c0160a00a41c3c440100308101031030040000e04900f199501c000400c4040c94002c01c64101501c0b0b0f1941d4964a0303c1c05050503500c01340300407441101040384400003c01c0c00b005440c44040c68103008000d000400080404460f0441d00f6904c0304983c0d00804400c0c107520b03107030340c0c4130002c605404103c1509049440c0d5224003100c8028104130201400001c83c04401d1030b14441c40c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 695111528 1250 695110278 695110319
    0x909060a060e06130e3322020d140a1112010608040f0c08010b040e01150513270b0f0415051506031602010c05120c030a0908070c 57
    0x84009460404010410740d4000d030550701030f5000107600c0214052401456014003400325601c00c1c10f0800d10619001070b5200d0f41c090444d61155a810344090001303843d541000d190041041d4204980300c00c04000100b803010303d4244180e0708104c41d103030408841c0182580c4007900c0321540100d1400745214016201d00e600c0020020030200400c1c1103828070494518151842d030319000406565505e404a501c41003968050880c00c29aa00001c250b5015003180c058400706803418400c8030041034030035080c0c4681c8200c00d8584d440c003005c00c1c802410b12150119000c5144032010031080004252400c54401d01d408a5212285c01da0300341c81408617540003241c10200036540c001c4507286c50b403241000010204000c8421a44420104911144140c0140a0118018540c0b50342c2e08100c00c80d0714510094914004c09075080504038109c06019806944098a42e01c040c4100c940d10300c06008055400204a540f450f0794411003200410002000703450041d10070005412054103000295240c40d0414444 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 695112778 1250 695111528 695111539
    0x140a0c02120705100b061c021e2505070f0b120c03070c24061d010f0b0909060d050a0b04030806040c050f2115090609060a030201140702090a02090906 66
    0x1000002d1000604d020159155800020303c0c84661000108030748500c00d06103e0790b1820790b148485001c043e41c001d2400c0d888012a0751182d43d45480801464022045500d000f001488802c5803240d8a5410601c031280c4100d00341c070880c5444440c0180c1c00406d6800034014614007080003d0044040c260407500140d130f0b007440508610305440c00034003120a00100a10b01450140c2c0c0302104101000700403100c0c141c0da00d013442265104c00f6842c4643c050801d00f14400c9030103000010304440c241c0700041c00e0300c14001c00d691078004040e05004e02040c010f041e494000e4405120035021a00501113641d0b5644180300b40c0844d0b04080c02c00404010003e00740e580304900d0500074220301c5412034125032404d000b44004c0368503040250340220903504108807921342620407108104071000f5034041804101c0c011100c0c0c03207003501c0304428001d01a0088500c1d54200c5640d5105101541c0124650800000c06140d07240c50301216501094410800355500c44107550003289002d00c41c07428034050b56000c0001e030340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 695114028 1250 695112778 695112787
    0x30f0f0c18030c0519030c0b07051e030a0e030703050f0303061e09070c2a0f140f0925020d0e090f0c09030705122103100b0a03140a0c0212 61
    0x1205a00c6102d613200e001d10541e822400c01c1c86800d14001c8a600075034100c40c103640410795510074081c0e01d5001c07000850304e9000314230300c1860f03010303004008003000da84440c02941007500f2000243e0b00070710f43c094030707a034140b16203500080000c1c001c0140d010f42903000300185840e820004280404200400c9080c003221544040104a43d02d440c0002c0340d00619a00d0203080d0308859044c80420382158200e0146440c43c84004101c81c0d0507140d044008941c08084552480c0d50368049990036003200c084100e0f8803122811882000f490080c2100360484002e001440110490494031070400d20a44014409a000100078088c0c040d00000403a001c031000713960390302140c40c02c070414041c2c4120040c00341e00902d40c040790710949034404000b00300103040c0291000802c0110ba0f00100d903a50014103e001070f10b40e625000f4502241c1d0a81900e011310302c038000d00000c190401c40000c5094000c2881002050b6444603c2d480758400c0c000c9184c01905d0a030800640300a00d28802410300c02c200c807280722080010030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 695115278 1250 695114028 695114033
    0xf020405210c01080c071b0f0803090d08130b0301030c050316050927150a0f060605120a02130b030604050a05070c02010e1906051201080109031e030f0f0c1803 70
    0x1010207000c0400d00c2c09102c4d950700d103120b201441c01800302c042c110f0b001d05044188100a50f480000c10380b04c00140552240c1d5940c504190b50b8400c1041d680d401840c00000403001075a540090004e40b04941c0c3c004403e0354a488000319141c1003648240c0b603c2640680804c41c9040600c0260f256054001106103442d080a011424a40005d04100742801083b5031103007110200130384906003c03d048050301d0f52103844001c1004014425110710a62501e050012004000b00c0d200d0031013100c5660f1506030500a0304502c200d00d0042c02400d891a403030b02003242c41854010419a000640408001030746c07241454014042290304c0100407500d0145040d06101181c0d03004541080380700c0d424a88405118140004501004600000011103842a071008540f050308140030308800964000d002880c0d030380c0c0e03011032800e03603000d46005008074074800084101510080742c00c010421a07405c0c041504078000d02403c5c02c5580720b00c1004211551107640205c0d05500422101d641d00760710604074000740c01e54 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 695116528 1250 695115278 695115283
    0xb090606030112022b0302150f01030201050f0c030d0e06090a031e02010b0306040b06031b010807030b010c0507030318050402040e010b0307020f01020705010615020a05060105010806130f02040521 86
    0x40c020f400e00c03440140010821035842c0c01d108881140e822094420505802c020600c011440150031030140c010180085420003800c2c540c4d0f841012140040c0d00c240c4d00c0c58005590070740c09078103180282c070300802c10000f0340f100c100000d01c540300b44000e000548802c10710324241000006800300415800c840092130119600c01403021101c4880c42c03c141c80c003074000400f6401841060121601030107004204404d12103034882c0544210743c10360985110203400000d034100c904500129038081841c445c0441d48052280c1e010000f202018180500b8510481d21128609200c5500c101c001a00d00b06103082059444403440e0024001a2402d504003410030101001c15481400fa9108000d030110003e103103948204141c4000d0000c100c0215900e48860070114068031103409030360110442d264100118038400110901c103590040040c2051303900744801110444c4014111540c0300e504031003030f000300d60704912480380b00040720140103035560b19020910084440114150600141c20784401c854481c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 695117778 1250 695116528 695116531
    0x1e0e0d060b0d050118020414090619090506090a120302070203121617070308010e042001050f0a1e0302090d060c17040f150509070303080c040305010e100b09060603 72
    0x200d03202040301d2000d40041201c5244910016003c2d6080141648a01d102882c40c444028000d81d8288090350840310301514050040d181c006140d4800400038810060780102c8002c60380e50340502050510300d54981c039251036429101c0340c3c084d03000504501c003041100c0708a20105007640c20b0039410044a6000644c6031075000c1d0751100c244000203652419001d20138405240c3d243d20840300a0500c2405219070041d400610044020800160002c01c41003078402d542131040b0b500c8100c0b8006041101c48220440c1d642000e440c1c1030210031700c03081142ca0102005007848800700e64800b8620b081c030141156031602a8106541030510403c02035580343c441220f0b100a40ea088100070901c8906100300f1106880c80661008040c801130050108101c3c2c0340c11641d4407140503144503000598810811005c80b0740550700f40c40340307030312510040001034002c158070b56005051032612810248e40c0e03101c050a65400b54482e03d0179802401e2a11045107051180d000704010540303040120349001400700340315100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 695119028 1250 695117778 695117783
    0x110105011d0903090a06050d0c02060c0906070510110c010b18040308090a0c06050a180e072a0309030b1b041403030706090302010b12010e03070f030903121e0e0d 71
    0x151680001d610781c90070421664400b134082e1040389000d80d03640303008081d900034660901d9010300f0800d400e02241d200184150240003000d09803840e00ca008400c00125600c4001e0031280c5000f2a04400e4115045204941c0c21320f100c1c0c07450380d41e90207805ca00300d400c407410800f02e00d101d00406074451030001c0001003002d81c096858244820355441d02c0045520f4600b05e2600144a0210362002090b52584078000e89044a07054603807000242c52035404000c03100e83d5004075a03142c03101c10009000d1500c107040c81e81184d943c03166502491012241b0790000840301010030350220b44064020030420220b4000254030101100c55400c082081c42c030301c1409441140b0401c8503401031b04103881d9a55034113004462207241d12003c20004840c1030f01d80a8043e002100d07040d8840c02003034076039006692040c002d0b6807041c04200c001d1071a26166554225040d82c1201040d01001a243d0020001404040d624045074016864401c5070501c410b5005645204006c3d820003040180703600b04031035407500e0300326410065 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 695120278 1250 695119028 695119079
    0x209030d1b2a06020327031f02040b070605070809031309110c0a11030601080d0e0d0c05060a05030603190f0311010f0612150902010c0f06091205030711010501 70
    0x602019004880140c1d403a6050942c20801d0000144075400100900b0b080b4120300311740c90b509010381101d000500b04100410f8154004d601e0000403640d10384940483d5000c05600182002d4441900940c5508480740c110b42d901c2e40d0301d00b0b1240c0503400164440e406000300700114540040c0060400645885110f03000310540c0320000d420b5044001c0d400e0f500400030440407600c0d01400d60905102d1111506c842c640240a84000402c0038030b03010034150035150061b1502da169060080510100556001c2c1c00c1d29206200c0e8408a1140d480a00600201c282607403070720b8503428904100350416030390124130800d0404121900c400034281d003032010949901810a0f4400c10800940c9602426466428201c0c091808102007110003041c1e45e4102004d0150000d80040d40842d1900d20031903e5a202c0a07012841c2c002c000c1c0c001802000c500340c0014810840450400d000d0340d00c0c2c588403e0500c2d6a01d012620200c101f114503079000500403603011000e03000b40400d500d00781252034201e0444e2692158407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 695121528 1250 695120278 695120303
    0x31c0e3705071505031605090114090d061b0e04090b181e16080604051f090602040e06121f02070201050c06010807080f01050f0a1e0f0209030d1b 64
    0x70007846034800805522034098900c11001400810300c0d402221228016084a6990028a0322486c1982c101031010f0b10707030086c55a03603202030642542004134059401803120040700c1c001070843c001c00803849850003400f120b42c01c0c0c0b2180030b0141e01c03940d801c0310f00403490b01400e030000c92440752400d0741042c03004281c50911038503003c119050031070304412044010219012005118000254131a100e00c858a0380c42c2a44e032100c0d0b890b078640340e09036400f07481907120f10003254505604a100905d001c40140d000504a0301c607640d158240c0e040b0b94070103d144c43c801030400c0700e00e003041851025405d40c510b0180c50a031401d00769100017030b003010303800480d52a4080f541d2801c5900490840702415121802c8842e0396940c1c4072a50b944030703c45d014240c1c4a00032000044001141400341c180134040c00c18005031140d595034030343c1d40280303c5000280e0512000005058061025128041c0e1510284401503a60b0040400b410b24181d0385c502d41c20b00300140f8200300001d040c400d00300003802940c0b24020380c202 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 695122778 1250 695121528 695121533
    0xc07020a0e07030f0608060604061a120907030605040c15020f060f1b0d0515060c1507170a0902010e01020703050604020d080f0f18010e0609040905031c0e37 69
    0x1030220703040103000a40362a00c042500d4200054042c2301d03080490301400101c2d1035504151203001d1950b240700040000f031014003108624020010340c0403800340207c1da4466500c1e200e031004e5800544054038606400402800030740c0d0000404903400106000070040804102e11141d5a03540c001c10400c3d0128402c408298680000c0a03103c0350420205000c03074580c00040040d0000300415105841d20002200c0240c0c168204803043d01c0011040401400583d00303407800c607100940005204100700103060240e86c074a103010300d81081c060204828002403a00603803002402281c9801c60b460b055505c4040200001000003c0c4560301030b41c16500c0c4441c9607014904140c440c001c401070b613031050402050b15800c101c8102e01410b904082a121a65142044001525002c10219185810481c20440c4022904050f0011003034148035408071b2317140075110b020100c80c9241800460b10030b141c0756001020040400c0242e4000c0500c008500b10780100d5a00501c08080480d0241c1002403103034682510030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 695124028 1250 695122778 695122781
    0x170d030b060c010906060905070c0c0b090103020d0603030f0210050c0a03020f07020904050d092c060a0801060609031a0601020d11010b04060306050a05180606061b03040602070e0c07020a0e0703 85
    0x240b02509000340301034003a03403a01c0070181109014404004d485d100000312824812035021103400d4111241d034500c02d060000800c0365511080c1428141502040041c546500520800c0f008600035996405410300c41c50b002420f0880003845540c4990030042841205401c1d00102e0b040d0800ca07080059840d5407000c000b40c05801007000181d405a080c80800080c0a00404c0103018069196030310030200e910f400b1400c40244000c840f0b0360100d046034020050010286241c7c40e00181c000b403501c0304240d59080f9283c25070b8866048080060450401002000192080083d0040d07400c6542c84261401c0310000350b4480342c0c0c5103801c0400c5544100c0b2040c3c45001e51250b02a254081c00070b20910f6181e0510001515096640e4080c1c44d00d007000144102841800c14a5009003050140106031914801c10038140c00900c400040324111181e006c1d003040d41040148000c0410b600903080300c40c81d2881c0464a030348010500144500c04000300b50051741c2e1000d105c0c0c283c1c5d0300c20400c60301e0b5442d480300460 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 695125278 1250 695124028 695124037
    0xa0f0f0c0e010c050709050c030613020c03030c0a2c040b180f10030501020d0207030e010203070201140f040b07050f06131520131502030a08011418130c170d030b06 72
    0x58047c64007091020075410100210f100d46016101e0001b606c414143c0d070b1040b071203040041c40581d0400e01c041002010b0000040c50701e100c1524009040c80c1034018050011320440300c00585110305280d02e1250760810307008018000700d08441c1c0900c01520341403513500700a4000c28101280f071851001882c180020000d500143d07030410000c41d2110085150100254025141034010407c0c80e420b14140350b10001c21101001d40c11381d40c0a981840300340000318190450030290030103071428880450301d2050400913100807802075000380442002030344160b050510241c0b074500825454601d000100b001e03110281c23440100c0d020002801d507030b00c5c14242c02240c02c0c119009440000041c2808140d04500c0130350060fa503043e5520852610100340607039480c407880b000790002c105c41e600104090030030240e6804e034049000e4144201c400d031400d12080040b03000c83e0380215100c0a0b00065050100f00d0310444042c20781c0840c000809104002419500c542ca155104105504e6282d03107003080c0c4441043d03030f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 695126528 1250 695125278 695125289
    0x405150a0e101a093c060a030c0329040b0714090a0605070215030403080a0e0c0f04230705042405040605070c0e0a0f0f0c0e010c0507 59
    0x2041038202205000c000c0d1581e400184074510a00300c542e102d05002c0d02c0b501d01c1064014551103c16001d68041c807884c084e0042c030420001d41c40c840d40d040503040012101181c0000e08105102c000b5100411400d45130028206d01e00a6040700000c0c40060300070341e04031003602e42296903802c0d484840c8029001130001d1981100340a800c01007440100425242c071203000c0e100d5500c0b41d9101c1c0c101091001c1490080440c0d03182d210324184400c00040780650014801a8006001d0342c1c0c1503e42c8118040356076106035000c030000360100c0f04119911189120784900d841680c000b402e0302510b80c400041000c100d403201c043c4910390390005c0e00e41d9800d030003c0340720094a10712490405807070248405800d503000b51040322030701c2d0345041e104110f0712a241d0520710743c16440c0d103420b414141010b0741101d050300409422520306031700b4400420007a6010803000d104070407901d800306005006088030800c2d5105c0c0c1060201e101e003481d80c1101d1090300b00c400007042200a1800c0b07000c1e05240d041a902c1c090090780300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 695127778 1250 695126528 695126563
    0x1050d0f0c090e0615090112060609021812030f041802130b1306020105060a091d0703060b010306080c0904060507090308072d170922090219030b0604050405 69
    0x30320000b464000808516030003007581c4043c4d6030421200030141d140e455042e4480c58010041c4007810000359001c0c26240980d90024101c2e0f00e0709540400c90f84801c0d6040348041d4084085000752510610029031446400051410b050b4a20460b90381805540551300409010b0f10042d02c200c40c079075050728980c2000100e14601c05942d80c0b03010100d507000d49540051000000d0300800d8150050041c6800b4240c00b80201007998501803c0360001c10750729609510041400040d000440c1c1d0800c08000031b103014080001d20380ca01400058215030320395001c0700e51900000700d890340390fa995001e415840342d0042000b103419528004112035895403600010940c000104044003406140c4032240c1e2a2070402c0c0360f00501e01c0103c4d002081200c200705008002c10a01e042c0095203415100c040c10740c800028007070f031502d048420038010340c4054000040354103955540400b429840c140401885401070140100109421a2218885807400900d003501460b16640440d0400008002c030b031101c401c5e031001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 695129028 1250 695127778 695127803
    0x3101e090c0e0601020a0519141014060604030201080c0a022a0306070f0f0c110d081c0b15090f0a060503150909122505030301031a0c0313020f130204051f050301050d0f 74
    0x2501c800514080030801c11000b105000a5030f503091370b20031034042da50140c591102c142d840b0b0350800800e9004070101c80440c001c1140c080d14843c1010946256410700805c40209044000706040c5442c000030004000c120030900c0c80e00c01c07241c010f292014820414600b10030641e6aa04125489516880900d82c10030f807141d21500c203121702c0e080500450100c180c203d0980030b20919500c001c1d0380c0d8420003281e109207804403c90107105103034024105401c000e0405411410900c5c001034052800e030703005001143d0000304008882218000d07201944008441044060030480301c800c2d076860810b02442c08503500000c40781510340411000014800890014a241003181c1c94036644940013803004a84400600302c40003010301c8090b007024441c007100e21141c0c1c03c2da82c41703800c1c003400281042340c1680c0050001038030828030b44131040340d40c0e5558070a80c0e025030340314035100c00c0c0316400c02072100c10f15540b180180d201c414180e2100c2142c1c11031342c0031920b44ca4070b1442c90600301034584011000402c0401104d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 695130278 1250 695129028 695129053
    0x110307030e072408090c0603040b040203011404080f0705070503070801020714070e0a02250b0105010e010810030602031b0d0507120b03101e090c0e0601020a051914 72
    0x7040505403020450503112966515607076104191807145035402c3c44032681c400c14031424032030701c4900e038080540030448101d20750000109170300b0340c400e40d42602d800c24140100025070501740070f060146c00aa078441030482c5040e88800105000f80900391811040024464082c00000c1200c000504001030030740c1c507402d5035170305030303600035032104404a03400492441c0e5a1050500030601a084507c4a00420341d542c0d0390380c00c02d8000b0b41c40034026951140501a07890342000c4004046840a0b10400c83d100940d41803e0015120201c1d44079001d04000c04042001002000c60607180200c82d0300c2400941c81fa2503104040007003415024505c03a2206010840000000a40c2c2213580076094507200c208050300d40058a106990b44940749030381542c4007101140d00c8201c035502c01118106c11070304680100410b951004256091340030141c880741d24554082c8040900400155044a400d00080c40303010200c2e07071520b031648076207140132070314a40e40d0a104c2d0a100031070098031050303a09801035840c01c82100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 695131528 1250 695130278 695130281
    0x14071d01020a1e02181303140d05100e06030f03090d1406090102030a0f0204210629030c03031c150e01060206070905040b0102150c070b01030308040b061c080d11030703 74
    0x6010781c41510705e8001c0c41d8446a5040c407141c041c2080c000c1d10b40b294600780d28150780306500e00d00c110890300800c00c00921448405d2244c18060541032240c40395091030540c1c0215902e0020b008140f20b0342203404078841d1050000308a0300e031180d040d10a0740d9a035000b810440c14400c510500300e6200c2c01030004003d401c0e00107500540c801c0702c01c0641000207040b40103804c1e0407400b450296420f108008000a0f240d801c01c0d00714500400c1c42107101040400c600040820519100e0944101d035602c480ea00c5a400c1c038052020310310711780c1e069000358140300009100c041c040f004801407902841d035640f80c1c9000d04844190080c0a401d4010740c2908075692818004d55400d402c50355400010100c1801085918003400303080c1c1c82e030790140d0042c26592022a09556140c60107010003100c1d0030100900c00010300e660310264001e40c001c0d218081d20703150500b08804480c0c80285003520405d944a10b428001c87c0800c0000710042d00300a205480d41c600852984c0244001c211103206803001008100005505 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 695132778 1250 695131528 695131583
    0x2070609090b0d050d17090118201002030c060f070905120f060c2a0715031b030c1b051b060d06080606030d020f03090114040905070507030314071d01020a 68
    0x2c850303810701640c0c3c1c810341608840f401c0749c11741003800843c604000410031402401502d203648010300d030007004604000624161400d4004805600041085032940c0d1040c040b071548103084900490171841c051000804010345070244602c16114164400320002d4108102c64401c00b4030700407a4264180006100c0c11a08120750303000f10400c8400704141c03070070240382c1c94080d0301080a0003001c0e158204010300d80d80141014407101055a26041044180b000e03421100416080b910b002030050885c00000b0290aa00c2d0000c5502c0d10020b0034810000d040068040402050080c0380104418030350006402c0748544840070101c0760070481e0104034500c0105065000c0c00045048450f4036400d0002643c54031103480c04009550818000c3e91280c0d40561580c2504020540d03200340b900b40c81c0d01104013111010b94210000a50111300f0108160709440b808264420112a40b80070740391a10005140300954001c8103503101848414103000d900030050083c9107680f0114800042c241106107607096245d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 695134028 1250 695132778 695132807
    0xb040b15060712030203150306011214030301150302182d040b060403020f010c02191e03120e0111011409010b0f1e03070312020c1002070609090b0d050d 67
    0x4400e8614030145088021500c4072a03012000d00d080303c0651005500a42000386246030911041071500110366040c00403502801802c1c4040d040040c40b03041c05c85803001c100c00000d5899000304014410f0751125480106c801840d4036015a40718881c203400310501c403803444641c0d00314050207070040c43e00d001c00c880c0e00440381403804c11038000b003d480208030645a10505481d00040c0402041c0050f013805402000144011304010b00000407a074041a0b0300e11015889412203102c180043c041c05908407664284040e4050300148c8183c01c3d80c451002c4c429018440a09001c2c0c0c03858640340c40d0740105000026020140002c2120b268014000c0462020848020805500e03064548aa80c544000d40c0e202458000c1d1000c1c5a0241c0810146c10301c144000b10b40b5031600c603005002001801b0201d0800954080b42d016005a451040c1401082142c2204d40310554200340c4042c0006071340410f01f1000c48043c1c0001040c26400b40d000301e54801480c0e14090f041c0c3c09107a44030b45040d034100054007581e24 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 695135278 1250 695134028 695134051
    0xa020c010b10020f1b130f02070206130303030c0207060906050a021606020726031207030f0216110a0b34030309030801080304150f260603100b0607020103180b040b 72
    0x80c1074002d0021598050f01d07100380e1040c500702502d00568001c7c1d1000e03400c4100c1d040010718003241c0f500001c144d40c02290a02020700c210f05024000c142c0d25009600030701c403480c0024001e083c10141e000c0e01c1c10700c4500032002000310100d070301807201e4420040d52104603003111507011100d448500007512060725000300510030008580845020070103814100000d079070700b8040c50405050680740e0307541204c00342c00c0780304150312820f4075800080c1c0d910040800c181400100da04002a03894660050a115041e0610031910f81c40700b003112001d214112802e80410102e42e02400210100c9a0204900900c60a65400c1c044d515501010340561040c16024000e444036045603030381b24602941c82c032850040d42050030000c40c8070f81000e8002c0c1042001c080560414600340416445845a40c01c4903090340314401c0150400c5c80402c1c1030910081401221001060110243d00c03c0459460701c65180024101580c44c98020030204c9030401700301c98150300014010322428079051610341e45800390390300a44d50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 695136528 1250 695135278 695135293
    0x131703181204152c0a081b011b0507080c03061602070b09060403060e0105064603150c12143601020c0d020a02090a020c010b10020f 58
    0x1600000398200d400308000501403030507041c5070b01101c8401e952a88503040c071403000940e102c1c8031108540c405100200302c2c0300031219a13403507081100005090380403144540001086076114a0303221959002e0f0402820121609140c0354036034068103403021405042801981d0000c6003d00f40410a040c07083c204804661568992825200c40d40502280d4000941c0c41100f08204489000c2d024250443e4020400c500742560b0380c940b0000d1b81c45940344402c540c0d6451042203081d00c1c00c40224004001000c00700300d50b0405200180741c50b15030001d01c403011241000354004000446002c100d0256038404040e00111300c3e040703418000b40c0103592442c804030301c0800c541c00c03c6803a9440f4002c1c8007085125219100d0f2104e035609003070341c40b01324251203100c000d803c02e050102c440d40d141405028034401c0010381c0c86203072090381401c168070303600f040c0b04540200c4a5500075075208170f80c1c10f0f0880074800c001079580f00015540d600400da80010207420540044c507001d106900400d54121818690080e0b8112 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 695137778 1250 695136528 695136571
    0x8030a0306091b050d0f02040f061e26270f24060904030c080c03040501031104030206190c02180609070207061e05071b0312030c17131703 61
    0x40b0343c25101d20704002581400445001c0b039054000c1c10100100c1d403c018036141c2c075040c5020940070a600f084d8007142c41c900080e08643c1201c20341c0c4c2c20b940501e20b084c1e5200070003002c81d862007405075082007003141c4d4408045601c0e011a0040981146c0c48602e040c48141200e4a05031707120800311740c0c01d05c503601911003820210783c0c1c0121b02550003110070781c4042050f0384510410800704805082681000f068480c5030b00001c1104d00108201c2c014900110307161440c0200041c103588180c44d030355200d90010300003000161036100a44056902c1441d40268840c42e6080449403c2110400a9481204030b00c0d14805224901d42690290100780c2d01880300c0e6407680000e0f43d46829034410390b000030380f20f1200403000800d118140381d00c10717040385407251a0141e0f9031180c0004021146400c0000312042e4410020800c0609080c0500c8080341818400401c004d41d015200c502c00e50034600010040c10300081003008030100002e02513602400e08000c120b03243c14810000d400489140e8840702018404408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 695139028 1250 695137778 695137811
    0x16020a060305041e050c100216080304050619140325020a0215090102031c0f0605091501140403060504030201051f0b07150e030307030f0c0306061b020a08030a030609 73
    0x2080f42c0210110085042100721000c44c009101c00903a050300480500300310f075a5560109000301012640103188400c000668044c80f442140c1c4019100d0f0310800c4200b0007611424280c9035100d03510a6504544000280c05603240031020078081402d4800200700110b498844400b601088844242441d00700ea100c50260303503d10310b5180180d4018444103415000c0700c6060002c240c8841d040c810b030390800703843c4a0094200c091044440c540c460b11055140318400032840740100409040ba0409494244220b40044101c89203601c5410041010341c05800d4001c404200c40017941d010304108000e15007030030b00900030320301540c2d84040140300500d0496401d84031300e407120030baa0350b00001a01d4444103a4488a0144100014075a440d48990140d44051000c0c005140b05010a803030100e178204130701e4800700880741c061f44c00c0014140742040900540341e0040349102c042c4282d02484081140500001e0011081ca620035600d0b807000190501101e42d06421200456808107401e0040c01c0340d50300c5160 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 695140278 1250 695139028 695139031
    0xe0c09090307151b0201141303140c0a08040806061e0307060c0c0f1716060e0609010207030501020d0e070807080303040f0615091d06091009080f16020a060305 70
    0x110380e54014000300000c9101d000c50084281c54450000828906544511480c0070403c880c140140c7d54503009800b08040d1245110b0340803035004126001511030703640c0901014015061180c502001242c0401602803c11542c40041d4004044a80304daa42c1c000c2e00c0d42d10803007191180d00441d000304000c01131298005014526110043c0070300301c80342c2000700482d81041000410740352034440d0f0300300141121014040c003018120928503c00842c84020811380b52a120000484080115540c1042125801100c40031108421581160740305d0081004030315010751900040c245500c0040c0c040c2140941e980a40b100c120303071034182c500c007680d40d22034262210710521815416400800001e400106951850311449110300400140100840c40e903034210b01440e041801c1c01035071074951084180c480310b45172074030a0340400181090f2800311042038551848140390b1074a07640342e0040000700300c01541600d81581e4802c4985440d030000e5035004404100e150b6069019182d03500700810494481d00805 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 695141528 1250 695140278 695140291
    0x30304032f060f0a0e130e0d2d0c0b01260303100e061203071b1202031c051c0c031407171902160203120406080c0a050910030e0c09 58
    0x4509001841c241410f00d580520701c44c10030000600d900c0b00940c0d543c42d0b5035900c3c0042881002610040740c0308514a0440c03504241010702000c100460f47d6000d0340e42c203105a40f074107a6801100590921406c0d1184441350304020080c070130b0240081034158041c00840c4804115091400c011200fa211341601c91000351030b085c0da80c2c031614005210600480d03020a40008002d0321042588031103044207421038100500486000c2d050008100b0003500da1412080035000050b1401c61142c03141d80020707603c020020800200410015500e80750718000ca087d91042460316680101c41e51520040a004060100344d50740031915002030bc0030341005503144070340f0a00c01c0d515100c0d0b490003550140c0140b90002010b000081c0c4401c503840701c40e11180d0001d821140d02c403007850500d981d1181704060a000c1440000e009410040c40200400b039800620700750003003e0a207080d50b440b1901c1c0e4003200c00323204044515030030a00c4038009065a9525a0000c80d030b0f95080e03030944419100400c100310b1202c2085e27490 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 695142778 1250 695141528 695141539
    0x100e0d031809020414040216020303160c050f030c041e0903081e1b0d0b22051506070201030e01090c0f031e0201050702010f170a0606080618010e0c0702030304032f 72
    0x32402c407406e00f54020308103130340c4104e61807001c8002a80007925590101c0750400441e050242482c0810101c20003400c00340004a37004e0345071528603000b182d0340e24080700000e48910345a05400c0c5034440c41c45800200a04134843c2481040480d08011b42010340544441c0c900c502c100d20841d0304501f144c0e02586c0203c24120368104c807548080b034205034580001c410350142540e15910854995a407000344811034545140842d00c05c2c00030b00e108400c1300c2f0014190f1140020f820a4060f035547d980c0103c65029609083c00200d4a0030600018014002080001c01c02c50310f649011811032080d003043d204807489001031440d94003460b500c4170042da1710282e0083c0869030a0211000641c06254210314403c4540b03812a0141030b819013440c07000c0400e8442200720369564200f48040d96200c0d5002c0e900c0700d410340c0c910380d2008030711507013954200b4148292900301440c0c44c08102000400802c940c20b15800070110382d1919103e04090303000c83d080000340104526154041941404200425803115200420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 695143884 1106 695142778 695142809
    0xd141b0f01020c03030901030906091e02090a060b0909070201020d0906061d0103020a03020603181209090f040209040b0612010e06100b18100e0d0318090204 69
    0x340354119000301002c40502c0d10000b0849400344802c1ca40081c0325081410f01200400880307400500b2a406040d05074045203a80c8102d4298900880e002e070b50644a442c2c80c40202d408031f20400d003042c2018090200d4903e49021140e40c4881680009171400c1c8014101e0402c84901010440d6515a1080c0c244100c00008405107400c15190001d95040c2d411130300011404d1300c80303103c007d00c0350700c001001813030540d01505184e10346070442c1d084601100409a4100c0c1e86d412441c0c0b55802510804e0004c0c0c0c16400301040720f401250094230741001a01c40d502c80c243c0681000f018150043d5003443d14940e49502440b840c42c0310011034001e0291801c10182c0102030f4201e90340103c12101c0280300c80300c0c410000d4502052000703811214512034080c11503098034020709009900740c0c0020351101c190b041c10b411100c0c5401405408408101042d11003107108124000c0740148110040d5a45 = true := by decide +kernel

theorem cover : BRFrame.Cov 694964028 695143884 := by
  have h0 := BRFrame.cov_init 694964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 694964028 ≤ n) (h2 : n < 695143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
