-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0523
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:15:06.022071+00:00
-- url     : https://prove2.me/submissions/6476229f-e657-4696-9458-7975be5caeb8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 93884892 ≤ n < 94064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 93886142 1250 93884892 93884899
    0x30105010609061209080a12150b03190e0318011d03060705180604090f1803050f070609080a26040c030818030f0c030705060316050313050105150f 65
    0x40144041500260800300312042803810100100c0c18020080041010b0400241400f000061846880358089008250381c407010100b00503600b00e6010f51180d03103017072b403080c50802c002c1403000035081c0a012012650040c50743d2804544c0c2c80005035400e0030b42d0b1061190742d41490120200742c47c1035a00c07e180484d11840c40b90100030b1101d0440009654680c0184a04104040015514040141c01d80c00700c0c03644e0000b4241b181c980b03407a400c0000140100c2140030040c00d00e07000400207960104110000f0041e099101e15103403101c9240650241e81c23081006980e2a91690118070002c2d01000040c840121995100389102d0300007203044014500190002e914802d000c1c00303020114085011000484c1e0703210200d183d40c2c0000741c0380c0c2d10528100d042020b9050181200c03480c4060808507041030140400c6040c3c03030900f0344510070002030340019030340741400c50005001c4400040c0200002c40d00107400404c10403c28078940c1c1c846080d0354080b03c1c41451040c91a0300c80710039003040400c3c420444800c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 93887392 1250 93886142 93886151
    0xb09010305030301090e070906080715020312010620100b09090303070206061903230d03380d0807110904120f050c01020c0105060a09020901050708280c05010b0301 72
    0x141c403072550764041030040ca04a95900c264a8003100c008002034030003491402c00a00c803280d80ca10341c49842d040c1c1c1d84214840d402c0410103200d1800c1c40881202c2c0d20140d40c8031840300607428010100c84a010403001a0703200d00b00e1803049a03c2420410980101d11201358020500400b51003e100c0382c01400760203002180d03c184240004030f90049007540d8002c409540c0440f001c00c4466400c80225480c1d4805061482e10380701d081c003030614008008d88004100800c072203450051100843c1181c111307940c003182e0300d2009502e4000011200c140c0c1c0f031a04c90f8910302088000c01c6040001da040c003440400312480d010000d210010011074041100c4035100840d40c9545500d4a5210007070a0350301f8418800c100028030a5a80c1190301580c250340c65203510380021503c035000c0f50007c0740203110035541c0c00c0c800e09803a1000240d0f50750038001c8910b14401a921f490514040b0790301c0c80b0141c6c04ca200042e4242600d401612802c2c4c1400c0c1d0321050b101d005030381d04098400c2c03a042c041e0848010100c118000c2c2d060 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 93888642 1250 93887392 93887399
    0x7140306040f06050402030c060a0f17011203120e0d090e01050103020703090909021206150103050f0603030f0c010b0409030f0305060d050714040e06010f05031006061704110301050f01090b0901 85
    0x402e55003404058011002140070b54407440001d0600c294034882e0791744040c0c0800d542c4446070780002e050350000ca039030b110b5031621080300c3c1d440403000f8801d204020400861500321000a03115544001c03c030191228003285a0030345105003400c1c1451f00950400048400004001410300f00305a240104028201140f805001d924014100ca5090023440074036038450a01504540f2074600441d280b40034007040e0342107824032944207501c00582c02c09031070000f03041801041041c03415101da00d0140b072004004600d09214092680d0703440d044500000c2c155540d074220b8805940f22070141c101c504c0c0c403c0c0e6071710745080b401060103400c546004d00113500a41c039030a407a9000540000d0102d065074500c04032008045840000540a400180b03122a81030148800001e03041d030310180305406451080f0b058841202019100c40101c641600c1680001558901141d0101850b510116009802000d0400c003d40c10400440c0c00d5407826515070140c05040d10041013160120720907081d480030308686202c182e514 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 93889892 1250 93888642 93888653
    0x150f06090c07050a020907030f0c0206060d030c02010c1202060a0501080a0f0201030e0c0d050a0308011508070c0206040509071206050607020102100b120d110d1b0f020604090204080714030604 84
    0x8001d20481d404075000441c20b0601008101e91868503900400c4544640b40c544801030141c042e242d03200c44001d091600090b046400403813124071840c00031300ba052032580305440417900106c4114080e418030002c201030074040380e25015400459200764009120300c0c103203050752100304d8405074045503441d0018010140003410541842402c25024038010031441903900030b02d03081644060900e68000c1120a0b904200400460a806c2103400303a2100300040c1c2ea55061540c3c6d403080303d2404c070001100b2000142c1c01d036003d0380003180c5450001d0032003424103880c0c4001c600c0b520070a90302d08000c91028100c0324800c40d05030003240040d00c025940385c0e0400c0d081e940042c1d50b89500b07210450345c15071140b4503c0c0c495210003244001803d020411140825200788010345800264692400a4000e408001c00340c507000380303141d90007801c0c6103961140d00c005c6078440c0b110b002e4618400301d0f07102c28200000280100140094030180840c000644007507031402d0903001f1840005400607029030800b0003003002044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 93891142 1250 93889892 93889909
    0x7080c0a05011e0309150c02010902090a02040f0b0d0603020603040602030603300313020d08030702070608010e010905060d08031017060702031b0102071e020f0405010b0a0e01120e150f06 82
    0x81c0c06040100e4590454a000207200c6614003403da216494451f00c010040e50540000002900a03654200180c0701c01e00410140e10607806030588000c201001000300102030f4004050b108d112280000d1015140d90000742c0130703402501c090310296000300620241e4502406591400c10311811000c0740c4039070494200d17110144240140003001d0001c00028500c00780902c174403000c40e60061550261100303920708802d07203400940e40300e0018800d0200110780d0a000f4800d144c181d40c4107014800d1660302e0f0030190406480014540d54010341100b0080c3c002404913400345005480450b000c0181509004d495000003040303507203440c0303258000d805002c842c41d0044102d850429101350905000e80390031202034007910503008007c05819071400f03403040d0b881507a000a40c41034030848008004091500810040d0b07007080c001c0c02c001c50001c1040e01681070192080e1401d0b010103050a081c03014011a561049490b580c0601d15660401d441d90340402004240075584905146080051801e050002c6407460 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 93892392 1250 93891142 93891197
    0x1051507050f0a080403030f0806030a0b0402010302070c030506011a21100f030501020d0c02030c06070e0f03010603060f0509160308031b0c0706021b151b07080c0a0501 74
    0x169000034816007402000d01c410441400e280084816041c020b2405104d2640280b1064000801009200c040300f4821044640607090003001010441002d8449000c0103a001d0000c07410705908020101c0015640c500c42d00055000c0c1c409040207624210340384200040c40c203a190013601c1c04021034881e03182c0d4055003040380c44117400d0282c155990204400e030f805440390003003906151500400000c224054004001014100394140501103001c0760907603603805407029036400e076040540040c2d925480f8603a400b06c1040010031000302c140e81000841d0840d42240c0054801507240d80000310110040c4c0141070704006074400030040144a400640d805200c02e000040000c400000411100c00c0d116000101c1082d00b480215918401810b656948154074806c1fa27015011385201002c13002881c0480f00c4407954050000960742d048031010746515401080c0c60070110940380003900b02003008101c180090201072009108e10003580382005500100c86c0e0140b410400b54079024421088006401b0481 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 93893642 1250 93892392 93892429
    0x81e0c030102120a0c05040b0f03040c060c050d030b01021e010501080c09040b04032f0c0f0312090405060607050d1d0301020405130e0114090d080c16021903020603041113050105 78
    0x101c5c450410700b220140b00300c0d4850414041b011030465031a600c1c0d0b0b0025401a4868111076140070760700c1005a43d4180003e00c060815045045507619040c0650003405c6441d00501c10f5426a0700b4500ca003034510102503076003002d503a555800501010340c0c10020b060312220304541980c0c3c5031406640301d40403810001c0c802010041c80103120611045034000c80f11001001c219461340740071917466055619403040f4a0f180c0b00d6130909034a21900e050100d814a020210a60401c1c80c0140305802c2c4005442d02500c40c0c0e0b0080f00030000c40c00413030340603c00303055181c48650f50310f28142440c08500c2180c08208104c103200b0392040004021503506c1981c078012201c422074002c03c030b100e10400b03510300600700c602aa00f00030103000c00b00122280b0100f0b00340008449500d0780b614503100d21141d000e01e80103003407406c00451764404d211800752800305203810031074456040107001641c403039001c40d046800a40c0c0403107070340325a44c003420f04601e00f0390300041d18040020010407140d0715000004141403241c1000d20078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 93894892 1250 93893642 93893651
    0x10e06091b060a031509020c060604090305090103270305030907150504030b2802091914190306060b0a030b010c0b010e0a0b0409150e1209040f06081e0c030102120a 72
    0x18041c002c2d0018560a600c90221741e802c942c3d540b10141c0a50700c1143c00f1500382c012038000420920b01441134241090f01960f070107090401c8000190001e00d041c0a00703144825400c04019592042d8145001c1003501c030350354090302cbc0d00f41160744070701d8004581c01113401c525440031240c203040c4c0d21074266000c03290407100720803032a11081031a100903400180c542c0e00344000d169140e880e803085900104600a01620000c0c031486500c000304004513081c1c001c005412000d41c0c41c003003051405120480f4905180000719801580e03c0e40e840048070f01d654001280740d1808608031039040c3e00761080300328540e07080c00c06a14811040e42c400003162014021113000c1e001c5203010440b0394101ea8001003022034054001c000085540c02e09003203456a141518405506040b480f003007844021502c8400e01c60740e03804050404420304104800340c203c9400941c0c8050b030b030b08000507001104100c4003200c4001140307034801214102981e5804d050b0328240607800382e03004103c0500c83c03076401c01040780d000480003800103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 93896142 1250 93894892 93894907
    0x509091213090c08010e0a022508130305010e0601051f200706050d1505060307030c050d09030c030305090318150d090c210f0602030406110c010e06091b06 68
    0x3100e042840e0440c10b00765203481d0f0750b41c20302070f0001c0b102410788103030446d40e0340e0b140c0d00c2c0c040da00305038483c019412038941c4510058440b415007590f41900340703500c5071010368207046200c405802c2940c4143d00c140c841e60745441c0000010b040500c9000e0150a00f966500022002e5242210710310989598080c104042e040320b5010481003045616010942c00050f10300099031810000c00c2ca40150700200b1420f8500f26444c0b90842c1c00602407011100060040c034210f684070031040d40100510085078007405800c1000d060903c06610030314010b54800d0710344100c141c0c11401c0080c2100c0e0000c0624403150300402403601041010200e08140c000300301d5003001d0200248800c0e08150280001042c001418005448100443d601410081e680503000c0c0c0d10207130340721f030b164086880e506417005866081d1236103000d00452440d80080d0b0740140a01d60105100d04901240d9503164001d24800c041a5550182d00c03451000601c29180c0244000005160300c201340500c0c0301c20f2070f20b050380e403900c942c20014540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 93897392 1250 93896142 93896167
    0x10516030c060c110105060301060e070c08070501050c0301030b0708010f05060d020f040603060614040303090611030c060403030c0e0102120301050603041703090309040b0103140109020307020c1f030605090912 92
    0x72940d4004003c0c4003d03501e1400190020180b203088040e00d5080000080c0035060511801e405c030395100c81c40c030100341c940040946403c801d10201345c0d00c88804000c0a00030030424052140290200d400d81540c940c90750402100b19200a0034000811580c003004101c812010b80c400e4081d503104807081590b030b02c0901c1c0351344024070584162310207120011034005138182d09588075004443c83c2d0341352941800203420700c510132481540402000302e401c1031428003455105006103419000e541003100e1601550003160762408904403800c40000341c54048103941654406060040201c080c001030000410080c6605041d0005026803401214080006028091190300c900400c0021080e80d60b44d03410101e1040340c8a60140319080d0046080907020041944644a6080780608118910240b6400c01c85218040e5001811280461180707482050050b0741d9007452141a004900400d8401091b880000e01075030010b50200740711301c80440811441240220b161040c2c0183d0b20801a43c412000e6102c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 93898642 1250 93897392 93897407
    0x603090a02120c120703030503011802040914012102060909090304030210020304080d09140112230105150702090c03070c0c08060a060e090709050408041d01090b0f01051603 76
    0x20b54803541000d00035001e82d4001c2074460000c070301540c3c0005101e094000d1156215800d1100030005481080108140d400303060042d8008800ca0402516280e510341001c0b05031011242140d20111035100108150104c2c06180703180514107400c0c03030700420352075000031701d0501a01080c6406414080f00040c840340007401214040c40c2c1c000c1c40e180380c150150034000c1d5a50080d000da548180305440310110b580307000383c2402048490722102940802044001100d08099800001060a889441541031007034a007078141010712041da40708030301e9803603c030401c0ba82410f91220300c0790b40c100030001980136031030b0307507142c0c4d5440f501402c0d550b55641c58880c8212801014039901070404200d2500120b80104081000e50245940000c28071a030b5448800d038018210342512402d0f49680015400c01451007190030003540b1500540100c4d0629594050111118090384600d00701401000c0040c001a4194481c20302c0703030101a116100c1d200c20000010300a0722401040008207064080e00b9000c02d03110300d80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 93899892 1250 93898642 93898663
    0x1009021203040f1d060d08160b1614040503250e040f05150106090512010b0301180203070e070804020f1c0803160c15050601020307050a080a0806040b0f060309 70
    0x712991035036551507450502c41c80f4028000a4481d4900340000109000500c90040c04000e01d0490311003036a0750b5a40e581ea204180000c908428210140f01003179019041610900d0340c1d440e503440010b030881c1d00920b00e50b510f00d07a020382e000050200b40a191400034542c1c000a042183c0078503900f040c254180140000d540c00f518060311007a003008100011501ca0304411440380d011134820030354135103010350b85140034042c3d800040d0050340100a2460154682d001c1c0c000c1c190000140c400071000443c7c2955000100c00c0c0700540c1b140d40c50011800c0c1000010002c0041c1412500c46042c8110004c155000140c0040d12545402000f071045591300e06900381d40d01c03402010754596007042d2910504a4104554401803030038584071509406018140146450758040401400600000c40400042c00045c28081c11031106210395400500100040c60009009042d07650310382d50f800c40c005042d00b100034070050140b070800342c1c402c0c1152100608007081040403148244c07642e4a81038041d1400f40c0e10003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 93901142 1250 93899892 93899929
    0xb10171513151a090f0105030709080109050f120406050d090204060b03041b05010c2a050603070914010905100804060b0d060213050607050709050403020a0f0305090a05040b03100902 80
    0x528007029402c41c0c140030b421074040c4011161100384880d81080705014080d40f0b540c1003100e01c10050303a02e41c4942c0065070300003c0c904144000c151a00c1c00b16085941c1002c040b51030740d0149a6143c401340f801c00601c06c010361440c034854582401e1480c0101140540311803c00031036260b83e0004110358403604420090280c11090b207840b480e003810000101c1c13540302020f00d28818106004252944075070398000c1403d4000f928841c0c0c40615031490400160404645806008031000108040e603030840214010140c40c1d403910005400c200303208042801d41f10895041c03080720390782005152540c10440c1070f0180e03c0d04191002d42c3c0c803410808040c2c00700c1d600c600c1d4400301c0210104100110386d409040140c40541c2d20701d407259210b50030300a4911500714003a00e507610410701002500000d40010b0b5005101e4410f6805440090f91500840303600c4030800c90210344040b54000031801e09540d50740040504a4081c040c200c80031011030349854000d03040c841900c2d1142600c1c019919000e40e609120301108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 93902392 1250 93901142 93901151
    0x5030c041d0618150d05030706020705100c0c020906130e12070308010519180204120605040209130206030114010c0c150207090509150402010c060c030b10171513 71
    0x8900741c4480c00c030201c402074410f0280b02d50f42c52501d0a100501403060003421a138654140c5040200306407055550030855442c441017220800140d00b60010f080340c01c0c850b2008006018a011030301c800d40360081501d60030480c18100410140e034500c000c450f040701c020341d400e016009a0b100310300d000c0c192030b800c85c0c1854403804060f01690003000000b8003480d0702a590701003580c0d0f01c0c4c0c1e08004652420311f00290b034000c00c02000744002141c0d50020f104030b21101000500d0180da500c2508004018280e06560b002d5407941000154100602515400304030a1642549035810f0b90009107a400180640b01694140345d02c05070040e4018000140c040360464440440c0503595a1200000d14070b20718400014003c01034000b805485070b020b124044c5c01c400c0080d208405440c00600040500140141c0c10420000580004a0340b54400c0c244840b07155540070400d5104c25040c0880341404807200c108002c3c4440d101c1440c890342c861500e8204130000c00d079000e000042e900003140c00c60350b0f0259070300c210f02c2d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 93903642 1250 93902392 93902429
    0x313060606050a14040806010312020307050613020406051c060c020106080601030b040302010b060f0a0302070602040b120907080a0f0605061504090c02010506040c0f080a0e0109050604060e010213030305030c04 92
    0x2280182030030150f10758070384030400303140c40101c6035500a40c440c060255201100502c005000143c01d10b0380b016862040342c1c2098030700d40340c0c24a445010345544101c070355240d03805401d40c101402031101030135043d110100101c01145000d2420a040038024120982c0c03046890803160bc03e400c410020250308044076200d5071241810a500310040e2022009980b80c50700c891410705107601640c0c0c111100c5820316040c1a80003c0507000707980005011a00da507800c00011070746605190103403401c000081c514001515007601802e161984580003913141c2e9104552580001c1d0300c0960704050746600c040301103180e131100b6012581c141c0d10510700000300d80f0040f9000c2495030103a40a00f1001415500a0200d9103581041c40119400c00c001c110001d00b4031044e240141c0d00071114250422030001c0000f80140024603d282121010003040350560803080a00042c00814003e17440d1000c5448000c52414200c2103001d4000609880700500b0310402100050b2180b035068241d9009040700c119a040b682c05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 93904892 1250 93903642 93903647
    0x18030206160305100e0406020418020c01150f05130e030304081e030613181e03080f06030601050d050f0610080d020a0302100f1d0106050a170709020313060606 70
    0x11540c032201c0d0000d000525000301d10034007a0a004444a00c020381c0e109090102c02c0d0340481d00144261183c3e502000b0014040389603403044542c40840410050f1581d00b18881c1c6800d46505e001c0c0580c070704c4582d04050280118851190048610840e001e20b600d80200000c64050100c4034103105060101000304014084650014042c807407038403100e180514003170360301e541c2035000c1500c1c21034210360044200381288480e40c0c004012000c40340d00709290f41d0400c1e40c5840e099410006180300320301d080d800b440101500440115049101c1003012030b12031800402099803440f0502c06c0c46e00c82e8000c0131134070003030000030f2080b280514008010340d0014a0080d0b4140480c81092044503454403544e08c941c0400e903c08240401b4196060b805040440180e00603c0c0250001c048581d079001e5031008205007062300300303000c2182405110300100790360346490100132501400341d102421a411000a410030910089618015680c0c040f000503101d40301c4014460007003906040040c80f4502c0d00ca4007180664 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 93906142 1250 93904892 93904903
    0x303040f08060c0a021b032e0c0801050f01030225050c010e01030207050a021011030309010e060106110c060f09100207031e1a04020103110d05011d010b0702090901180302 75
    0x1a89041240c0a82e202e40803c00a280b01c0c041e41c80c00140c11480307542825455031000b445039000b00400b00d561510440034444032040c441300320302542e684240d00780c104044042c012591941d4007410206807541c03500340840c0c4101c1c10b40c80c0083c10560300241d03101407290351185103030b0407041e1120141100c07440c9241840d0360356558001c0c103010484000d4240015031082c000c0351001a844000f80c07050540590034492120701d03519403241131250124500b4106841000030f148944004000071178501600c0200f0381c1014011303000002006800744801002c69400949407915400c140d44456550384040c0c4000c4007401902c0c8829404600410148411980001c6800c1500e0080300e10030b1640315040e10480304010030880091140c1c40c028035103410b50380300060441e8090b0040c100031074284241d42a60030b41d940300e00100003030760b50b4410050040001c060110040e440010782800d0f155414800020a6030142d810000c2c070824404000407844082900b0100c4c00220880c120840304010b490080c0d00d95 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 93907392 1250 93906142 93906149
    0x18030c0f1a1812031909060609020705010b090711030f09010e0a0303030504020424121a3111060703030e070b07020108100f0302090c0705060f0603060907050a06050d09020303040f 79
    0x10301c1000f00140c0300b10540c02c22640507640d0040b60b0798804c20020032100140c81300c0c40c000d86401d6581c1200080980050005201c0307a4410000002c0c4500d01d00d003080b81e035080113070140003008852600d0200c000000001c41d403516005849a90321903440c3c80049a00d034000003003e035085010b48000004064042c1c000700e0045101f00c0342032000841500c0080a203003800c0940e44c0c41200011410801880303007003413001d5120300503441002e2810044060310519001031320380c8000081c207440340b040c8410744a19a0710040740701003102250a1010f8441c551104040940240300d958000760000825003e030b4410f01581d490130303090303c180b00c0e83c03400d6a0400d900043c070160f010440c1100066161000806003805032484509580019429902031000c1c9400080a2050950301008aa000f1480400049128061075000d90000b4038003641030504000d000380820300ca682c8089410701413580c4034125641651050b2814648641c40242910080c3c101d681003e0f401d8003002402040002196140b2002d9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 93908642 1250 93907392 93907441
    0x30a0803091b030d0c05010b0402040e06010f0509030303010527040c05040f06150311040308040b091203030708150120060a0b01020d0e0609040e0105070c0618030c0f1a 74
    0x242d107400e490b0358074101c804a06141c0c15001900035400550190416075015070166000145002c0403034081402c81c0d05c590440e0301020105820401c00c0d6a100c0d0007840e9054480c42c0141c20a004500460365900040c0a41ca00c10000c010818041040d0345081c02064008114255424105030a14501821803809103d016a040141080081159006038011110521483c1c010400b8915040b0020711601c074806510b00801c2000101081c03001c005040a0948100780550700c4c803800c020000ca4404031050442c1540051040010b810341100c2800d034081842e03001d000c240e01ca90401242c64440c2000e4207001454400150b5220700800101144941e4600d0410408c4040c0c8200690380d90080301c110744c0004001f00c0901110782454006002c3d443c0014001158041048803a142500c0041b10705000290b94248481c007400f00a004901100c0a0756032604624825900c004040246004001d080a1144116081082402150815189003030401d4150310300784082100c401c980003043c580c08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 93909892 1250 93908642 93908653
    0xc06190608031606020a030207150605091308030708190627060b0313020f040509101b020706080c0c0a0302030714071818080a0e090a05060102121602030a080309 71
    0x19201c00000840e0b801d2010210b545009403071543d601c80103903101419120805400380500341c00203c000c0340744120111080d02c0820780500f0310061103040b8000808500245441502d0800032848020440e9040561451300c84450741d01c0405e01340030794034455500c1035141c2c034002002414a403000c4680d580300c0380248440c00140780c20240c94007504c1d640d01a20548200c10408510824220320000c1c4a007840605250380d8404a070002a0880d24102d0300c1c044560002407010f0340311a03a900c103030a0f02d003000c4411180a56103c001c0295510701a000711401c1c8203541f4041008100c00005031803a03814600300f2103100e248940340c0291207030004a41116922180712054516900114405041c0c80828140032041070f04810002c016201055039624080054907081e404180c0290060101810340e03140c001000c80c400c0240f110442c001040d06014500c1c00c404c0c041d041c1c1c0d01054240003141700c000100c0d01c0e61004010700c40c02407811400250300d40320744001e50341002101c2028500c104841c0e000c1d1603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 93911142 1250 93909892 93909899
    0x3150f08070b030f061021050105011b0b070c08040302030f0705090702030c1504020118080606100e210f0102160317090d080a0b0604030507090b0303070f020d06020c061906 76
    0x2002e800161103010380311403040c0000d841d604200c44011001c003130b20f00c4c0225410407440c0e0501c10910102d0442c840164445006000c2541c00a005401c1d8030440030356240d040d4216102d0300d030706005c0500309a04000310070b03500c402880782007400d44001c1c5400030107a550820007904031b1541d0350120300c02c41d4002e41ca03800c002500a4004010341d2860b01240c8081d2500d050088001002d011000b4030490600207400e0b9034110b1203145010000c0641000402070899041800c04c101406011031083e10800009038030401d1240c55948080c000d01d21030b01030305582142590507440c2014100d440c800b0203988042180f003640c50010030203e041e14042e40301c1e06200740124103205981c0304222610000c41d8001045c00c401c403441411513550080300050300043c01040e440005070a517000b03500a41e410740c0030170010b000394100c6e4450b60040d480120f00442c5404410341d00d0031021400000040e21410350022048140303d80d607012910b112a5110036110b1038540105800c01000401c4113000342103241c070f10f010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 93912392 1250 93911142 93911159
    0x5070501110d0503040303140f060102120c07170109050a03050913020702030a0f0201030e0106083301090e0a0f0308040c08010203010612150b0c0303070809010203010605091003150f0807 82
    0x40c01418114068041c0360310b6140c0940d665880070b8012001c2507514294480300e5181410014080d0103400100c038040d041c000300083c504a03000900701d0400004100c0f40c40280780015480e4200c400a02c040401d0b0240d00411a00408075690301600c1070240c81c00342010180e21200a01c00e5100480e512006a200c3c40054812030144007802509584070b171a054000c61840c00094070114070515011454141c14000c1500f900e0095002044560101c1440180103a2103e107880380d40b2060580c0c0b03210108000d0584410702e10600c60711004990b11030310380c04110310501c0741240050300a130140124003898038004042d904121070a5401408141c00401e0000040c02105d04036050350343c2d040144100404443c0044c00d41c90f041190b50800910000703001c11400700545000305c840d40c05140c480c901500054502440100480c075980d00c1080140030031908007040c3d130019141a54031040b181d00c055070940c0203101002c8150141c201d8403c00043c00317204070b0300c100d09407501c5201303035200c9030750b14102c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 93913642 1250 93912392 93912407
    0x20f011a0d0206161209050102010e01050411060304030306090204060f02010f0c050a140408060103080c0d02060103020120100e0708190206190c0b0c270a06030f020d110705070501 79
    0x26075802540038940324098502140642a510400a034401001c0c0c9503566101110140303149030341c04120f01c04420800ea41e02031180380410400000240107a242594030a000f1100455815121b044007001050600d8070a902c500040c000c001011552251100701c05400c1040c00008400150700300341d1660540b501600641c00382028a864032810400254815945e010b01c9c03e80c0501e124005120011713005108005080c000c41c0120340c00b580c1d070500d180351181003003401e41482d020742d80301000420040c3d03031104010070030901c201580754070341c5000b0000310b041c074a01c2031510502c5401c0400c01c0494810101340740080f142e074207080315510107100351600d075071015401d0080e40c4a101800502e030074901c2d40b4090f0078488210b00c0c2c03891b130b0040540d5500e5110318007915119540d820224840c10400c5c9406420a216861804440034801d4548002036401395540640c03003c054440a51008040541d0107840030390301c054209203c0d0301500c02c18000650030a140680303003032080c40c02c0018103501038a05d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 93914892 1250 93913642 93913691
    0x60a0506090a0c09091109060f030a0e0304080c01140426071a03040f0f020d0602040503060106361503090510050601020307171c0203040308010501050a0504050103050c0f0a020f01 79
    0x11010050f03071a00c5407060040806c9091034103c090300700003055040c0c0e103050041150b11489514541c413401c1510159040f02e80e414404c1c091176208010a210f40000028808110402440c103100118101c402904040c050350340000340100d01000d030f00080e040800300008486100070221500f0316900c8543c504024100d54094020071004c1010402041007000440034507409251590114070180d4007040c01c0c018590001d680e019801301e0140318500e010300c000344c0180910f00d4280100590044002000500329620b0b00312440c3da81b1a4030406140c102e00d10000340303c2c10144009a0802c0c00c1d01802500400740c0442d00350044007441c1c0306180081c401c50b401800185c1c020360800300140c1d81c20222008801408101850601c410440710006030108080d03100004405030302c03401e091801030240c0d001a00003605222042c403003011019884070944040307800910b40131a60b5120407a5072890b80c4501d10580298010010f1100020b03500051111800c2c000c42c03008200303031414546107031411124100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 93916142 1250 93914892 93914897
    0x506010806010f0e1c050601230613050d0c08010204140102010608010624030b030102030705070b1501050f0f0702040c080106020f0a02031218031b0103060b0f071e05060a0506090a0c 80
    0x4262590400c40ba00c4200640c20507145e0f4170019aa03201e00b49451f40983c040e104064030f000200f002000d070321b0b840ea204814280d410500303103811941d621280c4680d5001c0c084c081e0007951228024041d454284100070141100210b58868441440b00180380354510a03d0243d03090000000d03c07150148074040c22100301924410000c60401d0040030381046a9143d0001c1680314541c104160742d083c401140501ea2a072641e580c2d40304146424bc0f0480c40081ca0790748041c3c0214201b08059070021304680411841384012944c6800310003261815001d60f80380a1340041c50000c641e030103150041e101c13034181c5134a6001c460201003401c1c440e940e21050f1601c000d416802820704841005c0790130000d040703200c9a00e80c19000210480300407074030340701150a01c5d41852610140c282440d58051207160b0141100c08411880c0a01d9091904214811010004c04050039494981015000c01e00700c0742400f688003040d5030844c07c041d583c0001070003050790740610551704840410503101480c07080311104615038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 93917392 1250 93916142 93916157
    0xe1210020309150c13060503071d01020a0611040e011a0d0209040e030c0a1202072405121305010507051206010309081c0501091a0603010e070915030506010806010f 72
    0x10208240690405031682075940b081070101107202c082e80c080300c0e00c10355015808544448a05901c0020b540c0031340c0c0b210301480410400c2c400c6190344108170031043d0b5010380e200e03465440d06c640101c0c070300040050b016110390f290210390301082210400402c111031a2205691080c1d032120044458405058501d400d10030041003002500603403a000f030301070360324018000100a40740341450b504540c803408203402140c000d85010810001e0b019032081150851348000c1c404542080104880c40d420b26401030812103081e15489000b900c07c4040ba61900340e01003031554241842e40c0e10203624809010110307059401d0400180c03896120318242c4141150000940210b03856100065000f400c0e41c440035608490104a092140481035403c0b20380c90b00b13202030000e841c3d850700c0420022140b10200d843c1c4103130811989861243c4d290300540381900d42040415244d80c0760901c080d01ca0800580c0106440c00541d03041070306507034043c3d10151081d2800c2c1c80300095030b030b12070b001110341c444100d40540205030725 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 93918642 1250 93917392 93917413
    0x150c1603060b061c0509030409090501091b0f1712041d0606070b040f02040b030d090302010810030f0b090a0203071d0a0608030301090903030207150c0f0201050c090103020a0c02090a0209010e12 85
    0xb81c0040b1b0300300c07603000252850075440f40709070815111103480540300c0307070b441d450504200140e0074001154890341c1c8041030300090038440a0400c2d0541c0d4440c0d040c0c202940001c0b4686060180041101c5510150030141d4031591807081c0c0d030b802c4412200040e030f918621400a071441c00c00d241252070049d8030100110495443c0c0d528a14020aa60310507604196030b84d0044806480c10402d4141540390340d12241441480c41c4001028040c009251010404528100b000019020071010440541c04840c0d1752030350b603607641030034a0101c510300086c0d03141c420078400003a0032406d0700c44244a41444000b26a4940d100480101035400364441d2035510342c4108010403402c2000e601c4541418803a02c0c0c05880d24007180c803001170f00302a04070036407480c1ea5038480c100a416000900e610f00c010341400240101d14203840440000e02801c11624181500024541010b91041950841d110350003000681d407400c00d503800382d00130340200e03601d5804192948840c405903d040c03c4224034543c1014001c1049086 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 93919892 1250 93918642 93918697
    0xf0403060c03020705100b0a050102011e0905150403180608070207170313080c030136020f18070e1c12050c03070308070f0c02030c150c1603060b06 65
    0x20600181e10801d07030f0034010300002400034450350500340c640d02c80c0440c0e480707044010050110a507500aa055a1500d280108e1040c40b00c4018803039a6480d01c000600076040341021400d02c0740e100c3c5400c40400140d0100802c15810280704185404106078860000d46c98000070381b40380405444850140c0c2c82220100a10041d10b40e85c40301e051ba0a5050728141107450b09941c0050310310b600840c0454012041000c1c4d281024400c200e0a100302c4100892100e2160000794004504e43c80c0d8241381e00b00d8000e8500075922030006068602c80c0142c030a0751480c50380c904001619005444403000116540d40074041c42c0340c100409001030681c1288804010b4043d80d40865030720208203d1700502c0301c240400d104041c0c0c1400a44060f500030344030740a01d4985054001c2000d00005542001e0003510201c01c00580c40000d8900c10f0b5890603217a400028001000c055104e000d8103044c0803c600c151440d00c4081c083c04031185085921418042c000c02050b101000f51902920003458110903100600c1080c420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 93921142 1250 93919892 93919901
    0x3030c030206160519030f09060e06060f13020a0201062312030901021e0a05160f050a0311010e0f0a09091703091207140109060506090609010b090d05100603030c050708030f040306 79
    0xc1c500300090747c195144e0b8178400780c4d001840d060340d103d9540d03001c0401c10300301801459444a0121101c24403802e90400040c07180c440a9143c4001c66070106070152a0f50003548000e01a00c6400c070303000814840400182126080c40014500541c00e40c04000718580000080c0d0f2000c4030144c01a080d440b9803614808a070860340f08024040e0b202d55500031001c0b031404d0204094050f4600f10f100b040d0f50a085070503544000e298881401b800b00f0010400c046500042a840b079540301b40f030041c8541d00b02000155440680c1807295901c801c0141d0005107140140d800801154810740d1a179110360305160999500f0300040b00c4000382500034030030740c5001040c054001d00c01c043c0300c0c18040009406030103905086030030306202203513013954401c2400818500050040d9205000301c0d124a290340c100710480c40c103070107130a6601c0e008258088100c410880e0034407070b0f000d0701c0c5039184040282a503241401805000e0303982060b18940226480803c0019000c8102c3d41c2800203174420b43d10306803540d0354400051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 93922392 1250 93921142 93921187
    0x60118030210170f0103030f030b0402071713080303040f020d020102120408060a06090c02100518100209010e010503130b0a1e090201031b0c1506030c03030c0302061605 74
    0x488050901000596441000d0000e40101ea40c3e148000242010b19002c41d003405040342c54880100c50040000030760284803000da803000e0b89000f02c0c2103080003002c10043d000d00ea800a01e40b824541c0d00d80345404500d406040c4c510025641d00101962724010310b0b441c1c0c402941c02070144800c4030141c40250411007400d41040b48184111020010400b246003113075000386e00b140d501a0484018003107000d185000711009006000d0381080030040c0080007039a01c1031030811204c8400d44400029940c80c2c42008000300c00003e1400303039150803001202500c02980300010541c042140140440744070b520039410f8030f221b803001800310b2042882c107840303c1c105000020480900c0f15268a010082025001c5104ca01080804000f0456003c244005019560a003501c40385801d6122030200b05254000b010300a07050700070881c108401c40310101003000c0c12194001401c2d0b110380c2c9100008040d03002031401030040c00b80e070a99a4545a081690b440403100c014039400041d000e1084400110320541400000f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 93923642 1250 93922392 93922427
    0x120f060607080a050309070b04051305060a08070303170a090b07230703020604050706030203150d0206040801020708030f0c0a08040b0601020c0a080c09090f0616090f0909060b01170601 81
    0x20607030700c0e9036442501e903c081400d000007600403050181d407210030000710002d090f91041d42c0b8101810180414002c03204102900803103a110385c04612283c40340c00c00c4901800800050302c0545407a41405004002080048918601c4410004503c0c030200c0c8981c0808562042c6c0214254a90803821107a20740300c03000c1d1100c8d80d55081c03900600810400d008180d000d200750060503c038682030825904040c1b1941c00030302814010820007180c403203031801491036100200d80c4074400035524004501135028035044041a980300080200501090102a610800c030010100b0303850380d200154004a802500e105101182000000c071340083ca920a109501401c1072048440103500d003000100c0c555a1584002e080b0782245103d05010304041224a070f00c4000301006200c40041041c989075641001040d0341c4a0f80c1c100000751031414400c5c000c0c0c0d0b00070310030380d00310407441d946074000b00006100314030341210080c0c50200c10300169405568006c1d5a02412594095103944040054039400e400b1040c1445 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 93924892 1250 93923642 93923647
    0x100b0f0c0705180105100305070207090e03122e0b040501030209040209040606111212130f05010e0309010909090c0b0c0307080c100b0a0305070302040914100c0212120f0606 76
    0x1c0d0b03500d07001c0ca031100303c40c007600781003034107501d4107050191001415440c0002c0605000420686c0703900000c03202e084401c456400140d504d22510340c41c0c20b500501e0100e04480740100d0511611040c1c196036040c1e442d04000f00002403450742c5002c011154040e05c01e40480302c005002c00c2029600a81c068408000c0241015180004d035900207811102070360098404110170300204005003508001c01340c0c02440c0900c5031032070b02b074111001039070407400104600c0300030581090750410000301554524682d50701000070700030b891350100800d440f40c03ca141341078009402200c000840380400d0141e03120341500706640038001410f1040d00308a6a101d204e8810061004101c40000280c64400411200301c900f000b41400312140c030480070036210b81041491042c04410024004100085250303001c172507044034009250f8130a03240c81440400060000b140900980300c0013484104141c2111410f010180d09881d001c0d0010034641b5024000d5000c45440340d0308260004e690039016045650300319000a04850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 93926142 1250 93924892 93924899
    0x40b060a091e0f0902090f091501030302060615030c090409030504080a1505010806060901090f0f05090d0801080d020c0409020d0b0c04080f071401080a090b010605040806100b0f0c07 80
    0x554210640e14030b4001225060075500308854428100d05401d0b10b802444101425000510b02c19400360000302d01d000000003107140070404203c03421811507801c03407200c0c2540c2c0d03132f09001c2e40721082111821b003c0c810414840001c991018100c2c2c1c03180841404060403c400c61051000404542a0407000e0210800c808903600c0420401c800300c1f1403184010b060310f0041d00748840c0649406a120b41e50a034002c5003030183e542c0d40c1040281c1500e5921000080300e807800d11074034001d00b02c26414402610f141a05100700c511020807500c49103946515140190b1741d80703017035003580e0b140d0060011300140c01c205000c0c0803c0c41d168111028103800113041c2c45803040c546c2c8801103000c0056643c1c441c076281c006010440c0c088184000c0f0312942d010009844141d240111070a00c41000380709243c10010a40000380b10282c0c2c80d030080000d40e4006448064540c0c41d0a0701420319846030081440910400001840c00c200d407035460800d5511002c480b6042610901e40f840e00780d009040d050545014010020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 93927392 1250 93926142 93926159
    0xf0b06060f032e15020c040908030403120204120305040e060d020307060e130e030702010207060201050c39100b0a2904121b060203070b1801110c030901020c0117040b060a 75
    0x40a03003130ba15201461140d4443c2d0207071030b100c869542c00b801a41084405004206841d05031fa92058040c18850040076a411051001b441250000300c210500c0c19544001d156000c8050801d4911030086a841912403604011070325000d4440203505510220301071004922800389040a404081c044207010140704440b035090340c0b805440d9280c1c503403012030404150342c0e040100a0040401d40002c01035070420811a024501c03176003041d0100501507003180d8880c880004180300c1d400d2903880b210329584c101460300e00e84440c240400d00a506040c0030703080400f4070b45501510101d80e501c1c081100030040603070160f00305c406000811001010280000220078604040030420345100d800500b000d0a144024001d03c8002908510115802800301c50000380e0413600b00c03500a0f40c0503640854241080316602e0160444c0040094181404034901041c1c03480000a400815003d03001e45004644600c0112840300580950b21a042c1e00b100200c2d01040c2003030020703500f001c409081e9003500c50316600c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 93928642 1250 93927392 93927481
    0xa1101140d0e0c011404060302090d050f06010906050f0604050f030c0d030c020301060f0b0d09060e030f03012c0c0309010b1f08010902090a09050a02090a030f0b06060f03 75
    0x8140700d42d298042c100040105214000e2401c0003424440c1307803441d030015290114040c5001d40414180d0020381c80800c0d980c5d00066052042c3d008048540a041c001007003030725078000b0b02c640c0c509035060070f40220703103880e091084084604024203d282403034a414100505000628035482c0c240c01090300a075180e807140a205e4991070300a03111090050134920500d421101e55900c400300588a0500c14401d1000c26401c96180d9100c101000ca0701040c1400c214005040e4100c0d1b000360703440009081059000900c0c059030488601b03c5884d030407007608205000d5885050152404a4401c4500103141034400d90055500589010000100101400041250504500410780c403004900c04085815030780109864003510000f141941403a1903c00403e103110058068a9403954540c8005800a40542e0503036800365401840540495600c1c20103408504e0000c0d400d035800f00074840092654145681180c0403c492101c095117076541748a140e034840c00c2d00c810a000c1c00f40b48036120084040101c4c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 93929892 1250 93928642 93928657
    0x2040203072607140a140a090807080a1205070501110a0503060f100206180114010902040e01060f0509060c0c370803040312112407030902030a110114 66
    0x6a4010105141c0300d5042d19103051640e20311030240328000c0040c0c5561010784c00000c0041d06243c1510385480240c1505ca000490782070080da2240804c6080c011640004064101c5900303070b003950505915908000e482d000c0d0030f0809807800b148540c1d070040441c803500040100b140104000140302998803c0020960701030fa0003100012400b10520000303152001220364416801c4550f01a00806121b0107502c0b406c0c000c1c40c15407044a407a150780320262080d0000e404d00c05885105220079a1510328450094015000b44e0721070385180c0d1b0000c60740d84e0040c01d10021042c480e4072181d082000010410404d54006015903006000b13044c005103141d164940c1c1c00000003082049c5107850001100e80d182c041003040c101721075401f0b601a0070009028080300700d40582c0d0f0003030920125000c01c0a01a611194a959191114800c0c4044440b800140f00380c10380b5540c41361400c412450700c862004a040d9040a0800395068000c884400005034521900304a1000c06050140403000c1407290414945c10008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 93931142 1250 93929892 93929897
    0x20703030501050406080a120305070507050f07060f020d020601030821040b0603010c0e13052802070b01090b0105180f0a03081c1404030c080708030114030601090b0d0f020d0204020307 81
    0xc005009034036085c060741001d0200310004245606c85529041d03000680c082002c403e240c2d075840030070341e4a4856030803200fa06401c407003107544060a2155039641d50075184500c030000390300c20b04100d83c920b00c040b8141c4003500b2564000e1620780d080d6115000e59a10080c0080700d0700a504083c4024060021400b0b44503901401d42400c0d18940340c001e00d0f0039a0034401e083d008000101c08410002d0741d4501a5400600b031031803000501e550355400140c0c0e044000c1c2001981c40f01001030b400d90221039a0002e00007140714056050580c0d0380d070701c29070060318101d400d040e010075018024084404540c03c0048141100240104000170750b9801140841c1035507081681d4482002601d002c4001b151880d45410f901c03603007000c01001003141354042910401034002020010310541d62400d0200d0345055860303d94100e00b081d030380d0356520006003401030000200c480c041e024103400020726140380e215521803000c01030201c541c01c0580d595111131143c0b42c2c1c0c0040b0303400304d8034400c10340140e01d0360b01c06075101d01c0c401d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 93932392 1250 93931142 93931151
    0xf020120070203151006080a0603060504050a03030b04060e0112170a0e0306060303132303030a0806030d0c05120901030608010207030905010215060a1208070b0a0c14040b04060e06040902070303 85
    0x3401454100188003409400c50501300061007980102c1c1c041c00800c85400e071038100d60b2a101e540e228405040640d1010b0695401c0405000c127124004c5004001d85110b40c41c100020381185040c041aa80c541c85144140780d04500100618414500b000040e640b140100107000008040c400340c0c01d070408c00310b080019250b0050b9000c0d508040100d1074214500714001d60030149003000c0b00392500781c1070040d9541d01124924a0040c011300c10109412104028184d0b51a408038540c000d00988003255554860310440c03507c41c003c0c40c002c64010501d1070704070b40944811085001c1d41c0c1480d5010070906410165174038070000304001c00380b01078000e1074420b603500f2481c81d160000080c03620380d03010202c1e81c1404d01a0140315199540342c06400454201181030441d20085040070510380c0916500501810503c03400c000c100c05480e441100174900c0c81c0c0398142c0b20150150140281d0040b401203003013060003000306100050050140780003a82d0004c2c4041d1405480f000e180084e03070000300e01200469181c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 93933642 1250 93932392 93932407
    0x705030a0c030612030507020109083a080411181801060b040f051c02090906010f08010b031e0c0a081c0e010f0e0a090c02030d0c08060a060f020120 65
    0x4601a0207503650461400f84081400c2c0820707030b9000982c0c1a40201030043c002041c0e03046901a00003034000f81860380584811914115200c403462440c81f20104407000d0041e00d0f10040e08031800c01c080c00354040c2da5296055a42c0340d442606000040c10501d50081c580400780700707440c1d69040000e100c1c0203030180c00c500c2c850443c0d00140c03e540084d000680340c460180300901c13031694183c8140381103400880300581e8500c00c07102c42940602000b080650805c4407041040b1004400180450485040140e0000101c1e42e482d0a18205d801c4809100e83c150802d501401d0065200a1802c487c20400c400343c0396007140d850b00042c07044100f40e008603100c0d045071000516190b6044000714024000d1b0030b0041c89104550002001c040d40801c01d4030501103004840100c1d0f882e80c000ca40d01130480d602c82009040f0380d403d0040c3d92038000001c00c00903541003882c01240f051144d010680110005007000095900380030054411265103141d01085650b6010208032680d940e5081a044414071400540e40c0c500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 93934892 1250 93933642 93933661
    0x4170913020d05011508070503040c0f03050c010908030a050919080a0b070201050606030f180c1504050310020403050a08160b010609180c0e0d02010e060c250602070501030906020c06070503 83
    0x405030312545c80d00c2000d044c4a02c8040d0840f5501d50b00c01160b1408560342e6803149840c86101003a41c10150f003070f00740c03a9804810000c1c000340c031088034882626841020355030751808950340e10544502c40c000136010b003d101e0103414001c1001f00c03441042880f403038080381c42d0038030305242041c0e800c01996000c09110510060b1380c2c083c0303d11a0030072b030155803040c40c600d0b080b10700c0301703001d00054030008440e2841e0115040b006424040c0e2a42500000d0849071480b509075071a5545400c00d00030301d40311303004a6220200c0c101c285d200322821240d2003405408440c029032a08030554001c11241049100c102d11054001114022002d02038034090b19881103c5003080900540c01d111500c03225078084c50f04c81c1c1e1784012604409035074161303a07040300c103042c80600f1480102da01c7c4d5110110742d0342110010405235151140454808a00a40c040c030103100c14081180c503004e42d4800d88604000350300300300700c180102d5210382c1202d02039034004d03a0050314012408070f8035441c14404a4005001071404424400e4032a07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 93936142 1250 93934892 93934901
    0x3130312030504082a0a120e0a14040209060d0608031206090603060a0b0303070c031101030b060f04140a03021009061428110609060709150804170913020d 68
    0x4219240402c0180b038240d0703503914148140511a80030610040007409540c000510f0402401382e06002c6d5154502c2c0c03860018080e041c1e176002c4101081409441c00200e0070051240030440301400020700c0b48002d1501840b000b03600000c03907180c010a041060101205030740c0103940060500c0c10086a440a00e113001e8601000003608041c8210091000d00019170750018140c1d41014626500285080101d00001c1c41c41c4a200e0b4020030703141c41c40400105208900c007060b4042c450a890a0080e101d040080041c144529014499055424072092001c6040e030b0101880c0c000000d04041c5080d5125000503034000204204a400a074402406200c0540c0c01072075000368820808082e8100b111422940403081d00d80410750402c00c8454508c000e41034172843c8816502c050340c500303513245400c01e0002641c0316601250aa00801c01c0103000007043c6900a0303000000c4840396813a0f40e1a5255a5a000c81ca80487c0a101c40c01340c00600049400f5a00e884d014802241001c90050356052031264900654 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 93937392 1250 93936142 93936173
    0x10b0319060f061d0a06090e03190f0807080901150e1902040b040b0f090a03050706020c06040f0504020a03060f0b07060b0d0210120207050105010f0323120c070305031303 75
    0x75820303c68200001015120324208001d44004000782c243d031a140c01000400c00d90307020361012410800525501c42010005001c12445140f9403040c4514811094980c130b11006079840000721100001030b10148500b078481c1e0014400c00001ca60040b80101c0483d600720030360404410100f500c07081c49000303200f01030041c1e024400701b41c081d81414503160b450398150145101c0c41404100c001216003030351464504603401048028100d035000c2c2d440303051499a810f4036000303107005441215031148207850550161421550f10480f5040c03818188020310000c1c2d0840c02c02001456210140425030500420640b8041c02500120548032020f5003001c0003620096020395004e500350046041c09130315510410a00c80c81d85080005004031003101060080c85968005807c65103810004140d461108403440e08490040c035000280c206500c00c1c0c0440960411f80442c42c0d80d001c618814000c0481d6405814103030f0b00341e0160b840d0b03150b82e030300ca290039580150b402c40c000001040c0280b0802500c0044044c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 93938642 1250 93937392 93937421
    0x1e0b07020d0c020f0409030513090506131104030f030c02030a0501020a020717060c030c04080f0a020112020a0804020f06120a0f0c021603080f160605060109050316050d05010b031906 80
    0x1c0b415640115803083c04402056010755101d10074034040c14080d00444007013480000d020b00c06155204080300061070103481c6940300d5250f80030800001c583c6409651040e40340c8040f5185442c0c9981d44601081041c40710032414041030107810009030368107000f984e4585010f1800540e481d0b54282c0024105486a044007500c542c108000d012000000140254010400c40440d40e40c0e84400e01d414516001e5984090040e103e8009070a6002d04049010010240f00380c90b0417210304d036200b00c804180d014845503032001411b0710300007602614182e1050b44e07102e40d000d4506441e050910b90410540c04080312180109611014924020302951144d0020015503101078281503880403020642100306100191000401107141c03031200303440c0350803204022548501880d07805610303d05100580022030303d2a0102c0c406040001d110f050100d04000d1f07408284e1080c003540d604081c200204003203241030917180f540d6900801909510200050007001210341e02c551f034405168a040070a4801540c0400700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 93939892 1250 93938642 93938657
    0x5100e07020708032203020a0f14060903060411060d021605150c0406080403140a030f06050402031006050708040819050f01020906030a0f0e0106060c0b0c030105010c0f1e0b07020d 79
    0xf0300200680301e079514107014450781e42d1450800942c01788080d404c0a98480386100f4005440c00d003032204482143c8206050029500c2c80c03004001150290215103600f68020400040001e0500401005890780c010685424070700b04c2c0410300b0480e0040030707100004000c0c4010b00c0080c0101089000d100850002084801e8500b0b500401c000c0d000d64800c06040c0700c00100481c007018000d0001c002c41c982010fa159440300c6055038010040c15a039120002d86074030b4a800460381c1c0c2454000c80b4450888422071405c803914210040321554440c032010b40d03035440d09020109a2545c14445a0309605407143c01e188404c0359410103070b040c01c03c504a1100036a04c10405100d0a46408050700e41c004000f1500160352120500c0c0c20000c4c250301c0c40d5a001c95403030500e0106899400400c00482980141c0c103014140e0303178140076001030b84030038050180812036081c00100024034001003d170301e207403040d007081ca5503401c00c07a86440810f801e40c07011150340c581c1008021209070704014120120001c0c0c0b42608 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 93941142 1250 93939892 93939899
    0x20f01030e0a1e210507020d050c10170601030c0e0105090a080a0515090303060307050112090605090124051e13020c010209040e060f0105010f2c010206060108010e0c0306040f05100e070207 83
    0x801724421610002d0055500303040743e40a0203418048008445005030154085101e1905d0040200c00d16803c0d0306c4503440c2c402c01203129540f00384903030901d040d01034a8030620030440c2c000542d269084a000c950703001d40d43ca4070100304107100344050a0584c0c41080204216602e81c50310240c89580140941c90580c400c1c8108042c503500012018202c0b6030a0038803850b0b10303611120072809842e429001403d5207081000317000c6d0801c0150f20412011a400c41201082803801c0d054804c5501c45101381e035400b007060700610380c009030045006a400f10002b400c0f08140345441c2ca16000780e1f00414000441c4d42d5020408528a00b01405506c40d042c0d40c01014114910b0010108030710401d060140904100b2200a410042406007480003036400074100707007240d00308d400f91a410030109007428440c01402501c011450550148500074140c841c04c0032940602d50b1034204c0d0700441d410051450b40c0c8a030700c0d4840d0150041c3d40f07100303040c004c15105100200c03090400c0c22002034904054007400844d40101000c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 93942392 1250 93941142 93941147
    0x50a051f0605070326090d05040e0606030c070c0801021e070f03030b040e0f0a061b0804080f0405092505090d060504020a0e1e06030109020f01030e0a1e21 68
    0x50075520035003400c5845002c1c03414200c606440202101540081410b10058148148100d06200d440312804541c10110180000c45250140c4c0c030840548203036071008035039070340707007000140d0b85c4500d20344401e9003040c00c1354640e890003040c10ba008450603580003500c0003200b0840d021400172016102901031030301170b1342e55503081c13648402c5c0000f804042da44d16085000b9a10760704080f000d281c0f480100d450404000c001d0076101e504a24003205e10610b003007882107442a0b080322000d041c1d0242d4850341595604c1e0307140c11307090350b201e011284034070305040101003840d55404107154001c010b40300140c2c1c2d500f10400a84444441c074045003c0900000f072101041c2695000b07040000181e000c0c40204158680b4800300307961100395004008000a280c080000360b00c03802007c610542d80e1300c480044c550301c0302d60515080b2030070544081c2d00701d008041030b0082c55020390001c0003e245080f044910080541d240e41228000c819500300060000135990b00500c070310000d00340b80041d00c01028148001c42c140d8003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 93943642 1250 93942392 93942451
    0x1020316060510081f0506120717070e01090c110c030c12070b03090a0b01090b0307090915110a0f081e0603031606062d140d0f06050a05 60
    0x24a500d44410005100c940c801104038000c08801c005ca81840000a10364000c040196041244a501e4400000d407246004400e10a08084410140410b00d051001c0d04020429144608200b8031a07418001050320216103258000c00d00310b00009165810101c0003000605001c0303840030113a1002001c50980d690108545040e008121420407107188a4500035040c041c0c02d90210703000301c41c0442042103464011445c3c0c403a42d84a040103510f41ea8032200302508a5400b0615550980e01031001444010450f038400da1002e030181c1c6818522103601c3c081c4006a5034040d40764803228901048100b18070b40c2050004d00d22201500f820299440c04d07c1d00b46c05600b088940c004501000c900104065031000e0084801122481e24803096540031428220045c0140e0f10a4488043d2500b00b01c80c00400134121854016512000c040451850000000c012450810b8180e503c140009514400100e05080c0494200d01c903010109007482e10750107910458600500a040042081e03840352050425501c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 93944892 1250 93943642 93943687
    0x503010c0906080a1d0d0818030301030b0c0705011d0d050a050304110406080d030506150405060a0e0102071205010f0609060803041509030602040308030412020f070909050f070b0a0e010203 83
    0x1800400b641c1c0b6a502e800117480075915640d0007552505800fa0029004035001c44258119169102e10382c4501d05124850034002000324400e1b04103100501c0080c201d00201900304a040c5209400e000c1c0c540c440c2d600b16016001c80425042031900242c1c440f60040c0174a808014031401d00300c1c105028290060312134400203200a000c1c4000c450103841c00d58482d44044050620300084944600381000068000c1c00d05541c4548a111140d02c4000d03407142000c1218242c0e036020303001c0d038109800c0c0790068880700c0c0250a07240c1540100440482c02e1b0054903030780e1340400d010702d00205101d03840310390110445d07120b600090f4030750b420404d00b1703c5032a000008450072641110061440182e4841080762003030129000140aa03000150001c180f0003100041d47c005c5010b4580246100440603003a40d072002d640b50300f41d4082d000004104115005a441808a103010f0000e54a6940f01d402209040c1602d40d00000401000402c0198100b90704c01281183c2042c02c0c00150302d070070b90030703028610b024140c00c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 93946142 1250 93944892 93944897
    0x603250e030a02150708030c07150b220b090c0d05150109030b1b0711040b09010509150303190302041d01030503180d14060613091a09280b010503010c0906 68
    0x1c4400b13001110882280d03c01508000c45a8490601c03103401490780d031002c802960210740d0f003030700040040c2a83c820b42c3c9400030010103412102002d2600c0300741c490000808441060b503220103440864039030448640c40307181c1446102d6641c64a10807500101d80015040d50f030b00e40b4800111000c5647c0003c040410b59070070818040d1075644540d403a200a544109040c036200402040010410803c8804190b002404450a2024024078014082040d00912030240e0005204020500800c2d0402c004561b0a0303010301501d1400c1c2e0307441700081070740e03814051942c006540080d04012607400580501000040421880030651460b160542c0e81c0c0150b840c5030020103031404100f100c943c1c0d081c0e1304040443d4440d414403c20f100300b44640e42c4074481107520a0141c00c1803811319160080a01c15540000e90104414150401d951806600e0000c014180740a511900c003030000a18441a88220541029010030310004602c0c50040404001a80a01c1c00382e030429007000300319030300408807405480030341c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 93947392 1250 93946142 93946159
    0x1311030708090307061509050109050708041104020409090c03020f030d0509010f11160f090603030504180915090201140c06060f190602010b040b0109061d0402090603250e030a02 78
    0x9810b820f0039440356110091050f858510030401d4189000d942c1d40840705e005400304156030b668504c5e081030300c200302c030381c0c9000510660004002071036442d4280c441c090702070130041c00c1545620700c03841291142c0d142a200004010030070411854680c00d04608408103030050304846910b040040c01c64001d25003014140001c0f800101115440b6109095401030350008450b000840c044a120b205e5486010f05d2a07a003d400c500416418810702500741102e900d5610246020700e4903140d1400d07080d00d01400300030203403115281d03c04107008040703500882c510300340d0001d0b114155100140084aa072a140710040f40c0c00d0200080101d40842c01540c0036500760ba8140300c9141d140b000a600c4401c01d00c0002503120414004154140d055010301f0704200281c80400900d0500801074800d00709901c00d880c006003c0c1c9001130031101414402062040c00a0009820800400005025500308503038410000c2c0c60f44000050303c1110004107a1400d6441c2070003503641002d0400310780c4803094040041e0040c00c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 93948642 1250 93947392 93947401
    0xd02010f0f09030f0c0206070204020d020c06390c01050123010e01090e0402030106030503030c0d2f0a110d05030603060f0103081b100906050910020c150a0e07060305061311030708 79
    0x9400848e0500e5500810466aa4202400c0301c002504440b414040610030b0600240010510406402e0a82c5480b601c1540c80701c002c44050f164844011f8164210074800d0247c2c00c1d4010007401514060518000e503c100450b42500604010000c0b00ca0941000454484507100e070b6000f0141d10b0a4424115800c00c8903929800030a0140105620040443c4000070401600d0311030b2401034810749260400a106031003e65a903006003901d0014080e036481c2c0e5061781050120705080003403581003014140008541c02822010381400000043c2d200410340010070407415240500c5650362200c141c810306d07840d95065885070003090040c0f0800b0348031003c07900248001c0540400a4401444295406124403002844e0940c06800152696030f07481c880e81c4d480c204000031a0080d02c0c030844001009101014418404000c2140090444030080d035445c1c0394a44504001d00c9007002408090320081380c5400d0020601c0b00c140b1880000c6014280390141008003483c3c0c2c402100d0300007100e45021000e9444 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 93949892 1250 93948642 93948649
    0x10603210807052a070608010f061d0103020717070602040905060613030605070905090a0f0e0624060f0c070f05030102072f03030706060918260c0d02010f0f09030f0c02 74
    0x2802841d0000314803c4944c00914141c7c44a1000d060340c0c2c0c81040400000e6880e43d040d6120032601900c00e00380840d0142e14000b652084c2d001c4c0510b58041c2142c074844044030382d2444c001d94000c1c0d6040e40e4240c4c0000d4180f101d80c00501450341c0104082e20358914146c0141800780c071210301c5000c000c00064907100816001813181558a01800000f0162501824a0340c0948000d10299824034106424803409400107000400e0b50340c03144000700c04800b035040c101850110380311030321001076510000500c840c0788103000e20b038060f100103c5500010324190342484280c50406000744e100f644240c2c01081101c00049100042a1200d00c0381140d40a011801005540c0d07450a0054000e4040c40b001c2091800e128640c3c100d0360455a200c401000400c00c2c001c82040b0080c11020042c140b20f2000c1c0e43c0c110986448042859441034208110381011001c0c17030441d00f001000440000140e459100c02d90100e001481084071410104204000c0d6000b182e401400c4140700307552120601c054a41c3c042c09545 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 93951142 1250 93949892 93949957
    0x2030304022437030f060e04080f0a050417031e16080d0207050313090f0b060a121d010e0c0301150e0403020a05031201170105010f05061b01060321080705 68
    0x2100465802c0d076500a80b03e000740103020000e141190b150800000003041540d0200c10ba00450b0030100c0385141400355000300003942e008140b00820418100000900c40c022400b0752a01e94144d00003a43e0746416489030b10741c09000c0b030417418011000c204412452800d00c1c103a0402456484080c50b0703120311042e40b04400134043d1032000340242c040003507062901825500860306581c5212020403208038800c0030501111013218103550070280c10803004144c0b5005a03810000c0f82c141900115581010b20000b5000c04040e00f0100c0b4070b69140d5a4020039a00b0a101c070751080701055000704250600c82e0080480e612651040000508036540803400b490320900c485030040d60020112651079480c65201c1840e8403091180040c01c000205011901200c1801500d040700c25080401c0c5400341040e003040102e5100d9420a40c07512030310f401d06044079100780110f40003540500e210038204001102d682405480c580440740402c9200030030043c03415004025100d03d8011000110411100540c0320740c2c408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 93952392 1250 93951142 93951217
    0xe010c0203191401020a02070e0a0914030c010f020708030a0e0703060501030b0f070c020307050907030f140105040516021902061c0b0406120309030f05150403020303040224 76
    0x14007032241c0035010307145080d6110310400e1107102002200010f107480d5600301d006221208005030000c41040080e06181c040c0c05400900c514000208440320f60340c0e204640c00900000113040d003010600c8901402d003031260000c21038004c18294170302051951000c0d0984401000380c0080381d5503422038060030004202410155034440000c002c0b0b035031641821030350b100040351003694105403500001d00e9240b00f03c40b40c046080d07001e4000c0c4421424a4100401e01800070500010507507280e140b842c440300b180c056002c01042480f1103440d15410081400700303444c030040c0303401c2078825a100140c00182c0d0000b8082d03100c0c0141c80b00840703030b0200d902c0080c3c2c041c070400040c400c0307400740b440e4201440007140e8052601a0b03022201000709540d101410705100c1008100075002c40c00002d000c1000c07a206a114420080c45001510001d00b4007003540708841400b910240e0042e80003204100071810401840c14801d41c010060a45c00112038038000d280c0d1040f145400440354024a005800d51522400482003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 93953642 1250 93952392 93952399
    0x6041802100306030f061a1c200315010302041817090f060304030807020c01020f1203040510090b041a1b09041b020c24030402100e04060905040b06031b010e010c02 72
    0x7110442c102140903040d1030000000b04010040301d8055423601300003011048035410600300b20f1601c10b80755964035001c00054100c2443d006003040c01c5540c0d06025040449221804c0c4922550550050100304c490b40c1310f400030700344c040f0381000d800710351000024125007144008150340c80d10745130042030b80c0c2000080744035042400442400304064204106d02d02c0380129908032032500100c0001269114103114019415801881c0000c889015070300041d58094003c8040320381c80d038191102c0504850248605554001c030030720902042021100b8681d00503d0110300141260602c50111201340011070200235254400180f06501a203580d0030800c00c10309100300a04500c010a00c01a441d402c240192034400e0400c1000d00c001000c452100350408480c50701503a00319030b540c0c0c1c24005e0408038800d204040c48104002c00072144c1d500e0003094050300e17044001003154141840c1524084201506031f500c250041426210a0030001d4551001141c01b441c1480c8894a800e005940c0c600c84000080e42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 93954892 1250 93953642 93953663
    0xe04060b0402031302030607083309010305010606090b18010507110915100306120308090f012903030306090411040608010608030a0215070c0209180a050c04050604180210030603 78
    0x6005413001152400d0081d01503808607920410100c44c4808203c2d11016007200c0c010700340c4c254203803011190718480036400c007402901c00450005880080260f02c00c8a4030ba446400038403d0540c016042001000424103503414104c031010f4620558241c05055410070402081d400c0038005492400c0d0b24008029002070014100124568500c00c5410801800340d940300140805080c440d12541048560001880100c41155a402c8440ca98041c0054220748a103003101140c0e88028420900c2c20441412201150724000945210703e010703d1000d588240c106104102a640718182d003140c3c4031307921039000700818980c0c2002070010320341034001400b00d6103480000702e2820800801044008a96000c071048650444d4089a09140403140000010f408840c00c070010b00f40300181c42d40001c0210041e00e28000e103880e00510305070020f5800d58543d844001e24900900b024890382d5080202a9024030840102050380c4581d01c800b2800280070700d003011076192055100b94040405560301220104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 93956142 1250 93954892 93954901
    0x1412010501020105010609080a02040e0f2e05090309040908040f03230307020d11030102120708160908030403140f120403060b0a060c0303090c0b0d0e060108010b010203040e04060b040203 82
    0x40540003401400d0142d803910703001288103030044000b10119801103000300707240341c6e09a003400058140c0085200040c400c400907061001e505016801c280804000804c52040043e2481d0209034144119120744610b084140482d00c5d50120031142e04c3c89041c0e502040656003450241c8480c4100c5d4845042c100000d8408410400320f481048030165041031542d5212003007441312030f140c0c07040d00e41c025031210281030104c0c002501d009250003070b07240c000c2c001170502c001c2000303102542004403040070000b0300d0b000400030350b0a104141120061010329003482c02c02d05205031903079a07124a02001e03220807890007100010ba00200038035440c5d0308601003501c01da154038040b1400715403c40e0004458050505040840130309100c1c0341c04044444a44d502020864079840076401081c0c81d1030245c0314070203d640045046d1807040c00601c400080d62000140895021b0f061505019040e04001e07031a034140005d40509a0703001042d141500d800d81715403007168807039152030801000d02800c03c503080343c000300820 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 93957392 1250 93956142 93956167
    0xd080307020c0a05120c090703020403020402160302011515050904060b0a0c021509030c040f02090306070e030d0305090705060f0412120906020c0a09020a020c030f010501080c030607120c14 83
    0x1540c1d80c081664000f020507120010410f07649455013a1031072951054500030803030301d4441e0555412400380d06005207031545130b0b0081810b990101003410300c0100400c900d1410946d0920540709500e07411222180746505004e10001da9024a601940420001043d0410595110303070001d002040403c0075103559040154015211045c0e0035001ea1013200b904480e401d10086c004120790441800078090168012071204000c0140307803203107803210f100d40e00f032202c0b2034142c07005c20816005860548695044195140c2014505401500c402003014180300a000d0a01800110724043d0b850440e4103d486100803e083c0e034540c0181d920845060907024000307824000501c0070803d00e82c0c10b07940c0d114840707520340c00280da8031442c0c004450b03002013504604015285043c0d0291910107194030644c1d003081c84980000349801500381000c00181d55401c01001244010441a6080394040e0b01400982ca00064003400401e0f6440c400c0002988481007005461f118049010480e00c1c040087c1d40c8400400188 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 93958642 1250 93957392 93957403
    0x120d0213080106050a1a0316120f05040b01050a050f150c070609030203070e010602100e030412030e030106121a060f060c01051b09060403150b09090d0f05090a03060b0d08030702 78
    0x44a019840741718020529001b080311a000034494803001c140740d40c54005041e6101c90781c1414410802c41c50280219080800d4040c00e64403007111100420b00f400e103810460a046c00c180d218601ca0075640204104a03203908606141d0594115004002ca03407449007039890900c2041c10307400d2030f802800c1307000c110309070050b40801c1035a0003501100c5c85141c0390883c4c062034450030b000780e5002d644084500c0b084041c1c950001e591000703541003541c0c2840e0380c2d41854152100c00b0340c804c50109210030fa5884041c202407007444024010402d8019000c600f94907103501200d64045212030002260000443d291104034514006c4680600b20369510a8004003084c0280f406641051000b1008500403148000c20815580d0f42c02004000c940780c01d00d559680c611514603038800d010703c6502c03030291407c01d680e01940c140c0305025403000b900300135082e0359005040c00c840a84010500600380301031000354031584120f100303903544000c00040d408200c100090310100340344030003040c6840000c10010380c642e008c80c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 93959892 1250 93958642 93958649
    0x30405010f0501030308060f040603080a02071a12040f051f0c020114040b011707090906020c120403030804150227030c09090d0806011103070602070b010611120d0213080106 76
    0x20046001c1e19511202503036000e22003c0c00180d5050302140b85441c01e0b0680402000004000151441d82c0750380d0314440e60041c204880150300040030400690340009000c8078800c0b43c40d240c2901e8602c030701d03c2100003810f01503c09083c90078580703952010044104546050b0710400106045074121248000b40941001c020303000040d400d01c0380411156500004850240c0e5002200e1034040c0c0c00d24185141030103490785808194410703a0b01c0080c00000d188a0082814010000503a6610003000c2c042d10744860500d40c0300d00c000d4100070420109501145058105500c000291100980c110300380780a40282072030b01d007034000842042c0c1001e0040d80c103181100c04040d401e40d030381c0380802c0d420013040600845500c0c440e500700d2240300c10105d104070700650340884141491850155094021495a000b9500440303c0560024002c405e004036850b0250040106261040c80c543c00e020340b058881d0402c10f5052110000480c01c0304d00b12840b90195203050b08a9803811243d41e55400a00780604018032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 93961142 1250 93959892 93959903
    0x31204080607090503011a150702090903040e0718060e06040503060720010204080a0602030912160b180309040e071806030c0803090a290c030306030606010e010e061606050c0304 78
    0x400062601341170047c01840c00e81940f585c0080c0c04031105021049030100701c107030045041005907500607a42d1350b0303400f0300540504c030003592614240308400e50380140203010b45051086051007900b41c0d0314a0401c0700b0546041d890031940d150381081c0810b016003c0c541007240d041c000d4104001c990395004604820040c100d124052280168101442c201e20079800b4861590f000001a0300c04111a6001150024407500c1180c0001030900310804003508100000d04203240f01a04c0107007401401040c440d0809610746000035010013040303840c0e65030b00c600e44580f40250f4a03001d41002054062003030b40300070300103050640580005603621a0003405a40001c0300c034684040d0002c5200d1302d00000380d4047c440050030300d40f01d07182092940303100c4a0070147d00d5410013441003040108101d44134045c005004401c00156183d080c524201414003034000c008904100c403808140b03400d6a406658146400c80681e0032540e00e2450104c441d12201d5001c102921460800040c80626121803000b944914001c0f03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 93962392 1250 93961142 93961157
    0x14030c010b04060f05010804050f0102040605030f0106020c2101060905150102070f060503040b0a0b04090f12080c0a050a0e100804030f0806150901202d030a030209031204080607 78
    0x2401008103d8056010300701d4004c050b0300042c0090b501501181c1c0e00140a48125201b1488040160b0300b680d0140d080407000403008024008031134100fa00e00e502400d558005050720031080070100341c41c001c40c0842c80c00b0385648a221007018050a5000f00085c1c59000c40900c0345140c1080e5145002c0c1e0a00c000b1801131182c1c40e00003d040140342841c000740c518960381d4511316155602c44044540c005030800741c3c91680c40300e52a4141e41c945c49400c402030300c030705103650480e00d85081c034014008117000001c041c480b80750204094443c003582111400c1c0010308005840d0605900d0494655400569a50f0001000100c0c040003940003e10036100314460f640304003101a80800c101c4401c103042d103a49810042e50381d0f181c0c41000d502c00182203c0c60061529a090000460b07039000c2014910020b0009504028102241c1060800000b004400d103d40c990700100005850551f0b644030f054030325010141c0c041000e210a540601c4610000e41c15084215203454840da00c05031210015940240400e590 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 93963642 1250 93962392 93962411
    0xe0f0609070b03090a020d150c0c1703070804060203070c02130608120403080403030f121503050c0f030303010302041503080301030507050901090605091b0d0603051f0608070b0f0714030c01 83
    0x42d90101c83c801c06404002d0907404010303509000681070041c0d03040301c0c9010014060031403200300e4400c04010380003598906081000300e081c01e038604815440f1120508802300108a03000c0e4001100c1030b0490b07481301005a4a9842c804210354482422000941c8040803940c98944072859400090980d03c64400382d489183c11344050b0340d03451056100003009204107110400100c3d01643c1319280e10b110500701910b500e95419a110102d59082e83c92000c051a0714500382700f84002004500b00d2103806803603408030800d018000960764013052100078400c1e0703140c000c00078401c0c80d0300700c2103001180c1c00b66034103843e540c480c80e0441c0ca0b5002405085c4c02002610000030344002c030f0380100740494902604910064840c4020303842c0c0c542e0f20408482d00340c1000c2161000203809446040b0045001e030b0080e0007105601e004e00e2011080c004440c0b0076060501c48240440d5030003182c80c904480c160302c466a43d07a444890118058082e140014003440003504160312025001300041c88004501c800800c8426403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 93964892 1250 93963642 93963659
    0x90212060a080a1b050a170d020105011809140f030a0206070c120e01020a1209060e090c03180a0b150102100e0c0d0c09020a0c03110a0213050402040e0f060907 70
    0x195218100b071662105070400d01090b982001c1c80d88201c6401c101c0c44915490f000498840030503a4042491890041c1264101c11414005020004058030007407002d540b4028002c655500300b02070840d40f10340d88061010070407911407144062481e025040d2107640380480501503d0350401d5810342c016000766000a10700a00c10203010a03c25408001e440301d0800c2880d0072200c200c041628607040d4031a41040c0c0b00810300602200d10b00c075030039a46680c00c141c2000c40081c0f54100da450094000e0780458240449401ea20040c0d992200d0440240d0050401c04a29a880c1869100c0301a11f40d0105000780840c40702800880514450280c00b00c400581c0602104c074115004514210100d07008407285449a19080c41820540760103003042002d65600c580580741264030010040f4045132850103c0402c1581006083c0b6032071503000060f103200c06042c2c01099020b4202c402c028201540c1c2c20015086641c1d55000012007480e5000303c40041007050121540c524007a1801d1410740301c0c0c03600000c0c0140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 93966142 1250 93964892 93964909
    0x1020706112208031605010b0d081c060b090f0d080d0203010e01060e0a05010818030408010c08100b0f0304140102031006030b030c031906021e190c03020309010c0507090609021206 79
    0xc0f4100003d501d06110303001518039400080e0f404444654a854200c1895901c0301032030050b290084500701e03a107541d0746040201c100c968003005000681081d40c10016840482c0070380303171000816a8690401005840000d00701c007002c40e0014031600c400304114a02003c2c0e940610305861807010314003010f989403d42a00c10406400b061907100002d540148580d502c80c04002d5000310104004149e9210003040b03040c156001078000810503992040c440722541c2c2c1c0041d1854000c03820b4401c01c01d0302400c04140c00018880c0010340341308a900000458100001441c40824040d83c2c58000c54a9040c01e0545040d1645940728113000242801600070543ca0040b522280711080200113040c00702e203141c0700091220303040e2800d45120398240304141c107800040751648450f004052a55030b4904103204141d1a401c1480484010883c02904050001c1e07000403c8440c3c0501c00d0914403000c0cd16850404c0c503215a9401100040c5d0501000190000c4150054145044907490451159641506024055 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 93967392 1250 93966142 93966149
    0x605091c02060d09150905011a1206161209050102070506010e060607061a0d031812030807110709060b0a0806060703021504050106050a0b191d04020a02010207061122 73
    0x410104255410220f1603400700b02d50701d12901d0403412a00d900080b40d070440d05100300595a0ba5103843c6817404003940e40760520040c1c00d0032200d072a054580400d11559550006122030303008100c1641140189000c1d1140d040340c000c40c101c041c440754540e071030400d0207904441e00858842c490744d0008909000702c40840c1d8820b8101815140c02c140164840c503016101d072060340c4e14040003601c440b90807501d40c1c03100d01c0b1303000b4020f444800020700302000304d91011004d48c1c010001c0c40e21034001500041d0b4092213007504000903280144000d44c2160249080207110380c089074040380303004000102c5400c004040e0040f200303561104407055a400d824040705110350131000340160019100801101071a4049680140c024000041c0f243d8603100410000955600301076080403001c550070300120720640500110302d10601e461a41403140580003002c006005803070610407038000c00c0e540101d5100354140c60305641c0240091020b442c8103038175a0710547c04503220803800403030201c681e610102901400c0046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 93968642 1250 93967392 93967399
    0xa0c0b07210213050406030b01030308070c02090a09052d010e0106080304151106070503390d0f11190207120f0204020403050f010b090105010e09040f1b0605091c02 72
    0xd0400480941c0007903020341c80c110491070316144042626262880b40d030020314800c2943c900c82c0d504509015081401c010000030400401d911500016241e42c419160440040d07003010940c8941c900c0c0081c1465100100e20111b01509619a0f5404100c3d036042010b81e0a0705000f0021441200c0b119400d0305c1d254020908654010003082080c649202003180c1981010316080f00000128501c0c18100302c0c054403160700140f80802400003540200301b02c203120f2070640418007802c00e0021204007a083d401d030800c1504a901052070b5a8041d4290408140000003900c108000c0c0f48800c1c2c50310241c0c02c0400c0d80c2d490007c1600c200d40000e4000500a0155200010b05140e12885680c4125485201e40400c03600103409010000000700108440202d4001c180700102d42c01c0310500c1031181e01441640090304101c0d40200d11003107502e42c0b241864210b43c20600c00041d0030100e04020300080c4403510b03241d44c019900302c00043e00301d074060083c0024400444110b8600c14844888103400400024065072 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 93969892 1250 93968642 93968687
    0x14010f05130201170a0207050a03030b0f0a0509040b04060b0303120108070608010f0902130e0f06011206060f0e04060509091006060201150b1605070609080f01230703110a0c0b07 78
    0x1044103812200e0b50740901201720261800e01540c0e10716040c41c114110442c04651036110b461468a07040c1a10005880165000c0c4c0c401c1e480c140000d03c1c9a5400ba0001c0e01e480013010100c0d05111564000b00064000901100d41d00c1c0913500c8100354040f000d1244005500490301c02142641c031a40c07c0078101c40403032000c0743c0041d0074002080c0c000d600c28101c0d00d4040c4282d01000800060102500340308024405c60058245070850000d4200700c01c3c5072252403414504041880b4003600103030381c41c05003225458204510245400490001c10441e00030b5a0712541c50810803041d080005003181207500328003c00e000941c1e5411041e0f00780c0300508503030003100320380050900c540010342d03015080c41007841c0201202340e100c584409081038903541020001a4104005014075441000940603007901300300200201c0c140580d00c2b05500d0102d161741080e03075910701d001c42c840318465000200b602c042144a159a61149480580392800300042201d46504903400512506c1c003400e11030325001040da940c8078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 93971142 1250 93969892 93969917
    0xa0c08011a1909090b06040e0a0206041404020d06030b0103021f0f210e03030702070803090f04090f05010e0a1101020d0807080903130305010c080906010f140a0314010f05130201 78
    0x6011a0149240b00d4140310902c00000c100809004030311107140241c1c0003e001c0d05104c03062000707844142c43d00101c1c65120078200c04c01612601c085404030350061421070311812200c2e0000340a44101050f10600c141040c0c004001c0c80f01c01c0c103505040380d100f00d501441c04140854a50b02d5442243c1c1034001084600c65041034450050310820504011100c0b1f5882d010320f0700901900b12a811200807140f54004410044d000390100203000c041c22180004504148980002405000c400042203020b80e0b01c60424200304003150f8508010303940c0c440024004403a122003125900d0038100300c103440104c1416580e91442d40042500348041000e9541c5007038983e00c00300300f500c6801024140248511003049048004111104402c010b107101c2c00000c01e441000041c005c1c04c1480207440409242c0201c001000078040743c035000e1007210744810411214110541c00039055407002d40c000350922803061540190741006611030341036800b4040c020400342d02e0305c088840c85040b4055000b404038401c1032921 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 93972392 1250 93971142 93971149
    0x3050709020d020705030c0a1104110f07030306030212010b0109050603160c0c0f0b070528060c020307082803061505031008030406090f080c010f0518060c0a0c08011a 73
    0x100800b502600000d0314192113543c80519691283c004035a0a40080d1007680402c5104500400f000030304840a000c081da035116008403622880c18040c160183c0040c071181018080c0e0081001140c004107440380540c10b240b011800382070403004032070008d000c0440103d12803a1440640b80240d4051450059681c051042a5098500b002013914882d09900b80040d80f201440e02c420007070000d08404941752012864030502d0700b02ca410394801040f0214031790b003020003030a4241a17191030308030402103142c2c52004416800d5101d00782000d03103002c4000401185000944618072151400c000c0fa481c002c10b10080110704850b013500841300880040c0c003030349845920500c09950032841c0401000d4006070354610305132a42e03009a0280000c12142c60041110860600040700200702d140c0107089003401e034030300007402d940381d070032031441070003001f003140c050541000311080e46041014202e16a03a6010b0b58407140c0e9940c40160450710035140c0c03107000c5545801030144000c0c0303121801024100800303040c04c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 93973642 1250 93972392 93972397
    0x6030b032e09020a0605040302150c0606130905010204120213060503120904021312020901060c080405014d162c1303030c0c0309030602030612150108010c090305070902 74
    0x1480d00403502c824004000da962219036900a044a444003540c6a245205208070001d40300c2a92221100a0200d0020500040307040c90340311307004030b400040c1d80645c0b510090007803074101c0e07001c2c0c15984003150114110203015001380125000301c0f0030781d04080040d00003000742d40351406404d1705074215841c40803100d8840c20143c0142c207401403015040007034a007150517500c0d00542c803544428140a00f08c6056043c0300100d1381c003420071340c03134209030034401074592040b075100c3c82c0314050400c000a90507060b080d2205d9400c0c181d51450036030201c000321404c40d412005280040040d0700c5c80ea43c0300f044a684200001e611040001885802c25400d454180c05650f02c4c040e03040c5074003ca10350501e070140042d13100c0b02030782d00c42d443c400000d000c600701d1414002d0803a40111104828002861040000709801103408070850341d2105001d6941d81d6041f001c038890982e4983c030b264a42c89035420141c800081707a42d503107060b00d0a00b002040a095080012a40202035120140c0700d0b42185406200c0c00c00b80c2e800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 93974892 1250 93973642 93973723
    0x60e0409020306041511070c0509060d0b0412020607020d02072606071805062502041508151012030305040c0b16150e2a03010606080106030b03 63
    0x166540c01a000b0905141c07048500b181c04054100c16402c2403603aa00c5942498030500424505003500c941d215215841103008003072040b0b003c50001000c03a5100f1301610b012503030004d2094a2800e00e40352289506204048002c00b5015003030001d0021480001d2400c0c8002e071640c010001140f03043d1446100b1700300034541c6c1080600e1002020008802000780900032038055a0b500c118141c02000d0143c541d2690308554032480f070030019031250543c207195901c203a0341716200407081481544005001410411038031600b50810000000781c6050200f569401c1403803800e901045951007030101100030444d80103040c0044180841580401c0c4240d00c00c59000384100d44180003191204250051500700142c61142a0300c2058000c0c10005039040d42c0c518180c1d0301c0300500203800380080b840d03122461342100860a10f01507103282041504542c000182d90350150003040342e03c1d11000d0081040d00c0034012880400c1c04c041700e44949d81000102301d107400c0054910f600360302e01401170480004000e0304 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 93976142 1250 93974892 93974899
    0x21207060f020f0d0f1104091d070b1206040b010c080c03091518010306030201080606070c0504140708150306071b1a0901060b09090604020f220f08030a09060e 70
    0x1d45a0000e590920051402102c01d400e1143c5413140d00b200c140039a800c1186055126080c03034580c080c10b0f401c5000362000d4840b01c00f008282c5038070310803401d06070f0000301c05001c230075115011001660022030001000100d055803070095056035201c05100a66040004460025000c4020180483c0c0380f80c0c007410062201c001aa071030b110444001032a444207040c030142c0c030940e0018103800162202d43e070403841240d0a080900c04030b03166400183ca40600181003a0203004009011002c204030118602c019000c010002c01c2004015108600320035403c9a902012902840105131040c1060307540f1031116000500500c200d58901d002150b20341036054420160038030305501c483c0007c3c0700491022410340296910411450466441825140700da8050881c520f0200044411030711041b4905034081803e0310050b0340e0b107800e010507e00c280f2595844854840d544044121010b00d0100c01008881510301da5200041c0c8503071929031a8480d09a00002141c48902c041100c03e0181f94008000316005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 93977392 1250 93976142 93976151
    0x50406090e150607150c0801180506030c010e03010f06090b10090332030703180909030203090411090604090e0c1005030a2004060228020307060c0606120302100b030d02120706 77
    0x17400c9541c1a56404008500480c03c1d04005000d42134659002900d81c1c2002e6400f80315604140e40882c0e112108580310304c0c10442d40c2500c030343c1603403025008a40b283c81503035010452079654040d00c500400a4030a214400e100c04030000e008980324100f0007083d41d803c4504007200080d441c081040040102c03403400350709403541c40c407184141001d001402d10075010347c44100c40510030940317039120264660041e41800b440d022415011a5000095503d4110140c80025981e89800e01000560240706942507010342c0008000c5030340001500101d02102c400c00c21110308002d031008000010620691584c0022810320004400b44205d030000003100724030851614110241b031142c80a20b070301a030024800340c3c1c40072000e01e4100140461103100303691041c201d10341d182c0751f07680080e40720101441443c0412403401c801005100d811303444003000300154800b5183d00c0c8200d1801940300d000c007028840d10f01e4a403c1d440309c101e040100f0360010070001d42c4e02400710000501040b211640101c5000c1e100329655 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 93978642 1250 93977392 93977423
    0x60406120b0a2303120406080a0204080706020d02060108010203060607060f141e010807060203040e0a0609150305060f010302100f030209030703240c050307080403020c030d050406090e150607 84
    0x1001c08040207440041c905001c042c101c01c00b202201480a8a0300b4001d0f44514604403411254000b544c5c141c80340c6260070101903c0c9d00101d0381c0a8005e541101006004419001515580010348856000415000e1301c509030fa0f1441c5240c00c078001203070b0258100000300500e0001072407a60203c0c40c0010032900c0002c0c0e07082221103038120450100d807002c40c01c0f88040300b880300c010145031109006101c1d40005000d458203186009450340940d100b43c00032012402d0106d00d1301038094200402502d0300c0b1404001c0066a421654420074041c8006d80700da0013070902080b00c41c81c0054103030b810381c0e40191054a08800c113034021910b02a21890a10801d42d00b809041100d96061020324000d5015a80c68a2081c5055965244100ca1103d84401c803030315102c002c8030480c0d00032043d00e5101a19091050260b9500e090603070902c911414565854089d03286801001500b04001e0415105240d440c15101c5440ba8036000c2030843c02e840316040c0500b030b40992440c0386806070052808a00c10700740c0d00c03421002e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 93979892 1250 93978642 93978649
    0xa03050703170c2d0f070c030f081e07020102120d060f12050606030312070f090b030405100501080109020904060b011413080d0807080f0604020415080123060406120b 73
    0x10944102039100800a032401c4280f120b142580710724001d100003114803040c80444d41c4414414044180b101541c0810300b0014001d054040c0002150400014036010213245030201d920b43c02642080a0f0717000d00c1c203030b2858080410003903580496040e0020040b9140c80c161421540c3c1200344c00d0054151643c6000c107180c04404021001080c500d0f0031100420154a4001d0400c040244400e001c0e62060201006082c7d001c1b00060304010039003070112425024041c111076006054010140300304000051000304400040d0002c40b8416181d01040b0f0380c0d80700e1000900b6100304a001a50003c00c2c0300200700401c480340d021200c1811f050408844000c21566050100e8001c401022104280b0340c800b0000c151050001084e41c05039445e00d10011314044a028000280152182e103586004030001a003039201c81d4100c1c0d000c0c10303000301e03134078a9484050710003000d404090041105000c030b41c140180302c443e200c2035003d41c409001040305c2e007017905000c003c9034020300c4407050500103901c07a80b00d04803988 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 93981142 1250 93979892 93979937
    0x10141e130b0901050103111207091a03060909120706020310050406030b15010c0b010603180c120519030e060304051603060506180712020912060f07020d0306080a03050703 75
    0xc4403040c04600c40c0003280c100500070074160b0203c0d040c1400c014049000d1001c0b0b8040300c00c2c05181d07100c0e84895444550003100c0c82d01c0d02d0b030001a808169503211607200110341000d184580c0c022a5501055903481110540340d6413030b85010b042d0319409000354000100b6030703005503500c009219124402c8640d507000181c2602d60550064829042302c3c4180708000c59003210761051800e0070300300b2180b42e00315030b030b625641c5c060144203003420140c0e1b419a82200c01c590a241a440c00e401448242103240c44001e049103003030303502508403254418066484000000e10601104050700354840303004568154003031000c3d03684020001c5480b4050310384a1070036056078403905c001031401403200050b0b40c502242840360200024006c01280134611041050440d40070010210f020911040961110018070100e4208204000c0d8802c20707010f48400c021248130803440c80e078404c810b154201d5a0540107248207a00310344660080740000e0700000340302c00100e0701440040000c54030030728200f0840e01000080d9400031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 93982392 1250 93981142 93981169
    0xf040b041803080915100303050715090804141504060c0507080601060201060512010912030f09051504030f05030405070519180c09050a05030601170c1e0102010510141e 74
    0x1d050f55040c072610760020813074446038030300c0403846081d0360403c0381c030919544540784070003000c10000140c01d40801008480080205207110402d001c80d51480c54150029002800307005070f1341c3e40c06040b00c00a1b282024903085200080700e5070b41d20301801c1002c1110740d00f131101d200b80c4003171085240004003108100f140c240241011703400040d160b07041204200881340514a9000c00b43e04244080000c07070060b05682000325054100014080181c09035071010b000c2c61000a0040d0182c0d1031030029508205260b14441e9200342e580019204181c8026038181c00192400f40141d400301c0d505000c035041071001d05107480030400c09445803d544040d543c070341011030b1800c0c1850035194030b191491660007180807000362a00700c1302076201303a0406001c030341c0c5c031681446400320424010700284584075050069500c0414003038034541f505001c2e44810318003808844a0240151319182c00192031007861090b40c02a0b80e070300056903c07030441c41d1381088980d103000b403c244841d00d48140240d0040d03485110082e0708 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 93983642 1250 93982392 93982397
    0x506150a02060a050c0c06240409030806040c170c07031b030309031106090c0d0804150203071e110f040f06181409030318010e10020403060506010309020f040b041803 73
    0xda00d0500f00841c251080600f542d101c460301400b810350004c2001c00e003150301011034400303254a1984c08802100c0b840b60f1150032078000d0b18200c11003080c19031081c01503106000c00d550602581841000c110b0321000444600b14a190807800411075203c2e43d94003d1400c0c90003031400c1c500344500d8003200b00c02d2a034145000c901003555401d1f000d04054210502034085a10348018280c0713407a04989840d1521b1040c040b882c815007a040042042180120a6502034802d8429030302c00401488030203583c0381d014520940300300811080d07150a0107262030f2040d844070fa201220400110381e160602403c030740140140ca44c0240c031150403c00750a464400c43c001456551002d604a0700002c44d1003048541e8406a800c0580f165010003501e0b84000044907000000320080d00709401d074808000d80142070803207402c00607001e2800c3c0802c8440316070300a40b05480c01040c2c10001034540782e005408a410001009402c9000180c0b482c08600d410390221040d02c0300030304040f801d01d0446e442010082e0349a9400c401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 93984892 1250 93983642 93983653
    0x910020f04030b0a1514030703050d020d14040b070b070c0609030201061d010e04030c08070b0c0304060e012306030a140a0c0e040f06020a03020d020c1f02040e0a0506150a02 76
    0x24800e036810f819400c420f46100401c4079601d14000c519000e00709002e00d0f0041c07403941041800c907440401c007c01c019034015068494403e11030000a441e640d16020702000240251181c24103010500110303400c480e4240c4156182c0038090b43c2d800c01d034080040a642c1808907100300c11001c2590f03801104039440c442e0b03000042a906120108001c10004250a000780c10303880d0040c08a05188881103420035094140f09200400901d071040f070f940b05600f8000c0510700f01206115058040601443c0124070072002408054207160107107013201c280c10965034403030320010085c052a48034a05c1568222801801351408890715440300301d03911161030003540c03880e8400f0030714405114488100c4000b808408168503045d042544170300710700740c400d208042c000030750001d035407440c45004e6030403134040300b102d00c10039510b50701c1310504039807244006045d12500d98542e010401103035003980b00b03e070300b078842600e004001c42d00c62810540050000904464201101c0d061f90b8440c448110080c081e00c84041e4000d15 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 93986142 1250 93984892 93984899
    0x40e0706020d030207080d0f0b1e180c03061522050406080304060212030a02090d0317010911180301020403020301060e0103060b010804200406050a0b0408160f05090910020f04 77
    0xa19010106071510704142c414002c0301c002400c0314080f00d040142642c4023282c40f0080c0c2172448024020441e403503a00c800d000d03904541c0c44001d0002c14803440001c45141c684042042009003280104943c11040c034041000007030550302d810f29140c0c082c007181a2001e03040031005103000b11208460b80f10024104001003040000e846c0c5402010080d004000203581010b1030880084c6d030b514009012041c07204000710029996030b0a80d03041d1007003c0e10003081e244440d00c06040103880241c1c80e0b18118181a403040003c60280c000d13000b002c070740048800b01d4602c3d01c3d10124084142114000800d545035400704400800740e0703404d00a800c060001000c2050b03040d491032912404231480c081080e8103020440e0b01f04400300da0608524800c05480045112804d20800d00040080c01581c0059900c48201d000203d04070001801600941c0e00c076804888403070317044510071000c07940140316110b400c4c41444400e20560802003440c40d009100e04048811810810805905a8100b000640740c525400326041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 93987392 1250 93986142 93986147
    0x3060618110f030106081b03070302091201050411061c020a050310060c08030a0902060903010504050303091905101e0614010e0402120604020a0207080a050606010e09070507120c02040e0706 83
    0x941d448040e840140c03a144829402c014140414401d00c1c0034411540002100e02c0301c46580369030003103040742a241c0e1b00d190034003007c0c000307401040400740a201031491054881340d0512406001d00d404ca0041d10007810000e00304003850344000c001c0086000044406040c1d49418000381c013400b995500c4440e120f2074001d10080d81028650310507010403009007056000318203510102c070b4100d40b40001c0840d40940c0d900202d1070912402413142e8256203408100820b121012010b14001d0b0f00309016150314440740c0212008040c0e42040c040d240b03812901d00d85e0305030009580180d00b40c1e51381c82006108401d001100f8400c5406a61110f6100b12004603840059a403000c11300d02050021a01141001507008031662049801041d15020702d9001800005240c003c0100c1402442e0140c12544008a58038001c1d8440343c0550384980440c600e041103500500c0c0c48500a40303e06190350703515050151613103c2c60b51080d60309501c02c091060942c201c0c80507868a019150a5030404c40081035200e2621800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 93988642 1250 93987392 93987401
    0xa090c0e010f0f05030612060405010606140708030105090402210303040c0e010e0a0e1f0218060f0307030203040614131106210a022115090708060d0c03060618 70
    0x203050410200440030004a508141c0860101800380303400c640307136a510404aa020742010390b2054152141c20100000c120054002c3c00030742e50b09a89075503000c0c2c00c10252000340e00072040010b180748000d0005101504002c1d1440740d1090000345080c2d4812400c2c0f10418603101c3e40300d07503140940c02c008108818003003550251002442c00240300c036070741c0d8940b4581035000500900840f000d40d450b102c0b2056125410811469503c090005aaa801c1078080302c0d14000d5001500d45007031031300501c00340c94551808400b43c5400d1030046035150701d1130303541a00880080d400140102e60255540e2160840e446046011920602848030380901e40459414040700349610761060b148500e50810031440340380b10003101e90010f2415449005500d80b2810700140203030188941202c0c10700385044400c02d0f003040714115180502e448c5082500b8402e041d0b000e011a5000407101507002c01e10303400101d241e600b04159460b600754011103030b00400948980e184000c0c2c0c0c4040d80b004021740180140b0302400170f10b5104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 93989892 1250 93988642 93988667
    0x60702061201122a050d03021e011d01060e01060804060e100203180a120c03021507030606080106090e0c03090a0b18010c05030f150d0c0e0a0b0609030a02060d02090a090c 75
    0x20202842080d03a030344d4140d081c52034060f0500801021100408241c02048843c4840d54018145500d8201d00154640202503004503404c0c1040b0380d0110220031081032040800303442d4002c0350805980e0070424251840840036000300c4000c5c0e5108441011107a05002c0100748958500300965241810030590300c0300580f0102e003c040e9049140c4940001d02c140c814001004c0c054244404100070b01d042c01d03402c241240c0c91030104000c25104000c0300c258581c0c411010381c0c24130386401f07205036282c10046a9004441c0241d56074030364030350301141ca0342540c035015643c400d520f40103c0c0d824600c2c0740c0d1840300c480f50075203010500b08000c65801c40032820038000c03140541514a481707800e5182c0101072280c40358006e80426845130200340c01891a44402080380b8046400104000241e941c5810b0942015402c0340c07403180b81460940c402d046407609500301d4180322001001464040704903020400c6070760001c0240c00c6005d500b08200201a100e44a180f8018a001d00b0000383e00140d100300608000b16180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 93991142 1250 93989892 93989933
    0xe0105030c010804110118080c0a0b0a020307150b041d1c020a020906040e1207030905040911090721050405010c0203070206040603150f0b09010906051806070206120112 74
    0x7102090340e021581d19030054101030300344d42c039400c00300c016111000d515484800d40c004009021a040200103000d814095080d40c0c40b00c501e59481c84e1001042c0a41907281c4016041007051101140320200c0f1362200001e41d08000501c540f0500010b0200c8480010341000ca800920282509a0081c060400d0401c00c400791031039200d081d8030000307440c0e81c4000c1000748a9000c1c440491042d8585600501400d144181247c486021368280100c00e5001310100710300007541e00e84082054100f5008546035650720100810580c1d5901040102c00e90b00140840e08001030000007250b042d100d14140040a4001c3c8000074090405080c40c5081da20201c00d500103542c8100100c00040c5c540d44100d8040b40d045140021340a41c60403000001c0d100c007030b40315009500540b48045426107504008081034076007622074010850390b4031401e645038014503140400640030150380a01c00e0070080e000b0601144020907a924107103130100d4490980c3c07001e802000902d285101c4401c10041d03040b075806c020708880c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 93992392 1250 93991142 93991153
    0x6060f0306050108150613050d050a050d020705010c02040207140102030a0c0801051507080d060317090108071715030c030a0c05030607030203060f1203090a150912050714030304080303100e010503 86
    0x1c0e08040c17a82c2c5001c07540e2a02800c800102c080301c2010034a003c4002e4003004242d00b10728086401c00540e11180da03d800d80d0036001d00031511550b10300014030b901c101d45040c0c48a0744044015001c10000713400c804415100040304803058084460207100440c868000c6200010b00c9080521001305030440582003a070044031003001000074621000c0640c0c00031940308050682d590272103940c0001400f09940020200001c04002101c11070118014001e114000c2c0e0380c1015640da611000c40c5e04205241c0034401688401010403405c410b5000d024503440d0020f4121008401c1c4100400d14080c00b0450a031110729903070000344500d103400e0000e141c11644920301541142001d10025085c00e03000341034980704000031400c6056550b001c0c401e542c6140f400908c400700c030550ba24420032520a40b004d200c0d0000385c0c5494042044a4428140140d0580000013003010714145201c10044610311a44903905110500001034200c0b420001103208401d18500c1080c41450104c04500f1145d040e04102c1c4a900701 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 93993642 1250 93992392 93992401
    0xc040e071508010e041b0e040b04021206060f01051305060d0501150903150b0d02061c0605010314040b0408070c0f0801050a180b1b0a0309020906090906190f06060f0306050108 77
    0x1e1010300d94200c0d4201c401c04003081100f210b5001c4208051f442007048580e84d004000030b00c00c4a8000710321450080d501d19403615548560726481c1c4ca0125a07180d0700000c500d4032101d180d4800c0300581302c00da000c10080c02850781c40304002625500a6050365070302d161528018000901103182c2202d030b00545090651711141103036145101c480c002030300f81248513a80c003141c540c03682e2968885e03420345401903d03a80d6181524940d54000128090712401194148400050325500c88d10910300b4400c8501001101c5803600c0d42c440740264805031080c2d80082c018170051001c0f40b05020490024054004000d6102c1d00e041141400e60b240245010004c610b000e141e6200c003c40d084002a0880c0d110a543c045503980081d07119511010404400740018003041c00914180c056011542c0c1c680200e0b005501541c4000402030610700485008026412071710110310311080410007007203a607240c3d11011804e0103010f001d08085a200344d000740000307904182a540050b030548600c40152030280f0b402c1c00c05280 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 93994892 1250 93993642 93993659
    0xa0c140108010b22031b0f0f090b03101401030516050604210c08100f0522060b030318090a0504050601050d0f0203010203100f0e1009050403020c040e07150801 70
    0x2051080d40c210380c0000032940d9100289440c40264141054504140c0540702d04250085010413441c10b0080d0351b0222010800e01a00b054071400c603500e401020980c01e040c04082805003812216a0780c06108254020101d5412405240044c1d0741802c99200c656141d0306149103031200940300e4810030304c01090240255182c0004031000d491600c0d440c40d061101d840e1142040c104d041ca000b921402c0d1084001c03921200104005820540109007404403e00100d000400c580b819140f84628000c00924030790b24600b000d9540c0195030245000050310b03104c0c0000f083c2940d00440d404940b07000c4040708200b0501d07025110b1a0810b1801c40100f2143c40c1590303402e0760743c880601a16114514000003901000030000b481e1116170f41c0030300259240c3c00e00c3c010108002503a802080c00716008c4c5580880c4003210703d0f103070901c030340111444500400d2529099200621024005030110b000345101501551124020381c00341e0b1405100902d000d17868030a16240242c5010703415000c002054004002006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 93996142 1250 93994892 93994907
    0x90b130c05070308220c08100b0a0501030b06040e090304051005070c051c0f0506012c06010305040f0f0f020415081b0315090303010315020a0f03110409020c0a0c1401 73
    0x20b5240c10101030703540321400c80295055900c6003044110740c48040030020000541b01c0002214240d00442e0150b4844000c45401c0da000601c00a03000641c20382d0400007076100e50400d40d2000c0003d01254940f40d00c0305c0c800c41901108640c1d888040d030000a04100c5410407555401d00f040e00e52600d60b0414190b42d50701103c0300e1a81c4961072082300820110402010b6805500700c11903031241300001d0081e00d0f8a402a101c000900c9864110624842d0640c05450b040301050071180b0351041e950804d070360322401540182030261040e501081d000c8001700000301e4168460200c94024103070508409124410001a00c0c806810f400e181c944070841040441f100240c6845010f080c1040207075100300f41008240b402c800304070002c524001d09014409040c00220003941601d000b564407060b00c0300810b6486059118401940d0005001c8404180625210740d100d008258858002a4035095407280d100040e0f070014145032900360072400200f803c000d44403c103d40100b040f50300c0c040c4070300c3c030b1303200086d0040707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 93997392 1250 93996142 93996157
    0x20102130531020f0a0908010606020a0b1902040906030f060f0e030f0d0f060f031203020301061707030e0105090d080f01030b0f07170c042903071d0307090b130c05 72
    0x2c0c054201080079194664042c0d80c1d60040004842d41c9810390580010b00e0803070103204614095280050104400d440031801c0c401041d04802135807031649409802c1c3c1444085116800e000f29030920010030005142e00a5400443c0142c0c8103102c43d050320b081c841c04480948990041d0300349060010040d0000100950320905040c6408075124401c0c08030600190003910321040030b0602e407210210b08101210030744420b903800b5a03400310302000d8805083e000c9210030301403900030480e003aa1800e010000101040d9000e401840e011a805003120407560075200d0503a090091074200728080c00d0090751000d02c060b8007101d050044441549551600c500c202c0c0c020301040090382100c400240750f00d0043c0d00185504903c02204082442c150309120080c0e00039001f04002041c10b0725000c07254048565a5140134211100f0061560703c506100707555400100092004203012048078100903507041c0902c000800c641480420400c1101c130812640c2408103100c0000c8030300d4408000c0000e5448020f90f680d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 93998642 1250 93997392 93997459
    0x318060105030c0402071a091f020a0914120106060503070f090b07030c03090f080a1e02010906200709020417030304030503010501080a0b0405070c060f0b01021c1404060201021305 79
    0x20b4002a0030403109214265111f64682603204061040c8c20800150481070130f0040707180b83ca812001e400c1100268030410000b40002543c0781824414001c00302c41e503601900300102040d50b2458945e10090a40720b07036600034004650040100500720b50400d456410701c0410745451030400c0c0c01c0c0071414815000c6c0310005000c02074000d4a00782094003400070100580b04d031000c803a1446030345030225a0742d582c1002040303500e460180084100487c0465050b4030301d90f4140c440055190030407008940c85040362102003103000820381800c1405a0030310114001c4e0011400c0541e95134207101501d8080b82504032200501d500c10420000420340c048152410758100740b070302d58000c0d210810103002034201008001c0e4040e1400e8140003001d90031a405075843e922440080c0500303161075481c2e40c01c55001c24a0103001d6080056100d88644100001e0074049030141401007850301d02034070f50120350308a50052000f513940041d50145200e00880804010042112412071800494020726101c00c0c0c2010180503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 93999892 1250 93998642 93998647
    0x9030905220e0f0a051b010309021e060d02070606080601050102210a031b03050f0114010c06051e011214120403020409020a091509050a0c02030702010f09030f06020318060105030c0402 81
    0x410220601101840d8100c1c0c3c0700f00e810130481c4d070500548680034240842140b6084030190f2149502034007941c0380d840d030000c0024608541c9e00d041c1d003001441800d507450744001701b00085400c600446c8060684140114000155203040040b09846c101d410380103a4155880454080c10f016500d409084080b0a18460581c803075070750311000c1e80540106400444007080303140b281c01a10f64140c2c03126114114080760095580d84c2c8040c4a001040152002400548503c1207100450225000310740c0199004c45000040c6a140c0c04055913031802ba0441e070750100c5401c5484007804103110b0340c940e000e40c4e4140030705010215070f4481e4040c7c0c03185210003805252074442680c01d5540b400c14400003081142001d021001006038501c3d070101e0203010b240301041c034210100b0b10203486031003209802c00d480d1700114a8289190015150000c0c0c3e01400e008000000038007000082c10246072401d914814800582c82e81404550658210546100d1107001c0e070001c001002580e600040001e42401c00303070350059 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 94001142 1250 93999892 93999911
    0xb06150403120503070f090e13030c020a030521090d1113050a0506120106030b01060c0f061803080609070903031101020c0102030910060506030c0d020901090e0403030903090522 78
    0x101140119840942100c01c040c000c1c1840c0d6030803078004c501c80c410355500d50312215004182541c001d5801d0080800d4554207400090034441031480d085503440c0a4100001d258101d94001114504581c0041380d19401c0b02e5980c0310624050300d000d45c4440c2c00d580c04141481d0340a4049001800700e8074000d081e007100e81c00d240d07009403501c185004c0d005205d101c0920561500000f048041d02041e14924003801829400c00c601070700c18070802c2c09980e4003481050440c1d1a0a1044520345062142031f6544c000801c08407000408038072032034000c80703a4403401c1d81c24010076050180440500a14082c01040d2140070007407045e510074010802d4942c1070816803803040080d018103009010705808001158400814080e2540c800164503a41c044448024440b00e62100c0a0013200d000565031440301000c21b01c07914000c2245034018140301c90301031504041d5580d941c1d5052806042c00d450645c0403035914410700c0149903200c03040302c01401c015a50aa40446025007401c0c0f61200c1d00c04090701c2d6940c401105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 94002392 1250 94001142 94001179
    0x7080a031802030604030807080702030f0d090503210601260a151208040305100c081302010e0a0b07020f0604050102030a051e03010303020d021b100503090109060f0f060509040b06 79
    0x903481e90340140c21501585081c0c900904014015511980030804d1840041d2030713640f0000440f0641d0030401d80040c18103015a080201420302488102c40c0d034041400201c1840552201407103011103280a00c82803400c2c100009003a20744503282400b0804140d005500e282e484030b50102c0e400c14030300d40e40040e0012200164224102e050340080081a210507108021300a0751005007050301d0148003950001540c005464080f5144200104007049440001518000301203c40d9003411303006051411401403c0d50000301041e406d9009940b00c00000b00d10300f0258280882c10395120070080d903000785064100320020350740380905c0c461a020010002020308202000714a011043d6808106598580d616450301a4941d0192801d1000602c03841d1a038192a0224401480c8000405041c0c045207000d058011280b80d400105203418540d21143c94800142c503501c1000c11802480c08000755916000300c2d008240c4180d948928030030700113a018000840c03112014941c20000031500385000c0440541d08 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 94003642 1250 94002392 94002431
    0x1051e041104090506060306010c080d0908040e09100b031b06040305030703050703080a0b011b050c031f0605010206060a1514130504050c030403080c0a09030c0b040501031107080a03 80
    0x2650381050070702604144080038200030340260b840218052100360390b03c205020a030700040f80c031503002648001a00011600d010010b040b1801d0354440418400d0481d26401c8190380315074803161045070020100100000e040c0035075400300c1400710042c410442003000080c2e4420b1310501c1d810100c10010006038055888074111340c02503030705c402030300d40703510316400e001c1c040781c04c02c5100780d020a8000c0c0000d40310b01c0c04c6100320300c22680161035645011010041c086046e1298100840b22403198102d07032142c40d50108515803c006ca00d0101c225112410214030082c3d0b0b19503840f1074150352080c401c0c4045941ca160900d001e5808240003a03031040c0c00041c045a0350a60a44555400c020000d00242d2201182102805882080c2d81c107100503210752503100d0307143c4002c4402400042c0c0303650109042e01c4039a001021608440d1a002c40c009450f622741400b007040310b0380441200b88000800b04250b5806020302400c0b9040ea43c81e8906090150301c0b007c1c4203100b002d070b4400c10180e9a200003480d41403811340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 94004892 1250 94003642 94003699
    0x203091b0a03060f0203060f06070302031801030609090f0203010f0b0f1201090c0303090305011109010e0108040201020138030d0203070f061d100506100903110a03080a1205100302090105 82
    0x105110144d0440e40c110000d60042c0c980900514001010341500c0c03d080044a01081d450f030b005501d06405013075410310030014290703854101030b02c1d894002a9902d40e8050594258003c0041c2d030ba041c411b600c1058211404c8580c045240f900b05081007091b940c4110800e240c2e0b050540c0e10030050340c088002c250041990301c00081003149000004004c0c140e000e4404030070789106e50300811402c0c01e210306041090051200c054002000540c0001085d481801550382283c810300000c200c2117103440115800d01c204003806200881c0c2d01d040c00e1900c4042d86200d032580d03039050b0080c140031070b08041c0c025102d00c44d400029280e0401c4801d502c0030442d140d484902c2600c0644400748514503040c080c2c6441c1d10380300781c1000c5000c3c00d14003c00d40b58030b00a45c07188142c0d072443c3c5400b500c0e5441e65440c44010f42d03010352181e1348910704940000224070785030010104c03c913a60743e0700344141d906000c10790119800034040c8180720f400c00005000684690700980d042d50740031682204401d4601c011921034691490 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 94006142 1250 94004892 94004903
    0xc1c02010c06021b0f2503020402090a03150b040513020603070c051614100207180c0c170403050f0606030607050f071203020c0c1c060c120504050d080a0203091b0a03 73
    0x344150303560001710b52104105240c03416a03c8800081250400c940c44125103c114124402c00400042c6801d50088c0540c06010b002000110b680e5226400c0d040d600102804034503032101120445881e00d1b22540d580900790084484001e00d00c2d40101c0e0070780c00010504810300c08640100c1080c00420813442d1a03810000e00b2480c017a6449240340022840d50440ba00e00403204542c0340030b02140003055260a8517010700c40005151880d2988201400c502c5290006204002c1e9107100850326504040c000500c45041c0507544a01d1031911511301071551074807101941102d028000655404241c40ea000b9400b841c21580b11025003494655910440c40003c080c0d10110070a9004142c2580103071911307607040000d84854024100602c070740e00703010b04040d408044d8480c12046c00640d180d880600101164548129401171440809044030400e840c140c3d050340c080c01e11304e4101c9500c102c1160784241141402e50450601e00324040d070701c40c0c4041405c21000b400510f03030b41d0f050300c44440c0d0350011500300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 94007392 1250 94006142 94006177
    0x1103100c0c0b0106030e0a170903011a030f07210321060303021c05040b0f070f0c1a1801030903050903030d02090a050a1a070303020d0c030b030c1c02010c0602 70
    0x503100985406181c40085410250030b0b070001030454060303c00c0c8130701e988401c00600f0401850340d456480080059441c258074140c00c0c00102c540713460034441c419042c55101d111603400000d4108242c0317400c01806030380d120b560204d0030a01201e240740c0214241011401b40a806ca10100d1030705945030390350140101e0403041404174418510100740c02c088200c0b40242c0a075a001500d030130b075405c4130121459003000444c808020411030651071500520000702941002828400140c2d13a05c25071300d15662050780d0003112a281131005100d1395000031000041c4400080c03800c2000195125407207504600b541c18107603110420001d00d401138003152800d00e030090960f95286841c2000c40003c0d00800c0080f4000d103030060000c1854100401b842054440d029490031100102050f01c00c483d42c84040210708154003071140c0b4684126900910071800381d1501d001c1400303c101c406041c5444460500c0a2080710240001808454002c40004004d034081c0703003100c00c1c1c1c01181130007070180c4118151402150a44c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 94008642 1250 94007392 94007411
    0x60306020c1e010b03031b010605120d0206010608010501120504060e010222171515030a08030a0b04060510030209030a050f1f0504110d05010e0706120e07030c03110310 74
    0x11815102c0007100c4680300c80c0520840052600729a08060442d405510411501802d01d010030f258050608a0000103c1c855858a01041c81c42183e41c0c2c030300080303034450180c100616070140819030240c0040e00e08550250701d0000024544041b901075100250713a03c8012030140440707600141042e1901d50300966a4168a104401580d0003040308404581c1c1c40c114081950b04003a03003c802043c5188001f0070251140240c0107145003c0038081c07601c0118001001035558800740803e00c00107010b1190140c591070300450a4061b90840304c0c4031442603146c0304003032096070740c0e8009007203070b40500d8680103865030720160200b45000300e40320300682907105007044828003801c002410f4030540c0c41441404a81045500d002d01691416a0024440141f200307800d6103e007030450002550600907000400c00c441e1004d805410030141d0340010000404480b0803d2504080b0701800030714408001c000e00d01985541c4540009191a0000030b01d58607007011155002d075020450744034007024001c0104000220b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 94009892 1250 94008642 94008667
    0xe0402070609020409200916110a0c03030201050709080115031b050901030b0105010f1b0321020307080601080106170606030606130b04210f11010311121504091505090106030602 78
    0x6010846141c40315004c0c095000707810407d001c28001d55581440a2010b00c91010a44a00c500301c106080345210301c2070080040b503d0340070703401d00460103a000000c00381001d0340000c1040390240c01141b07140e8181030102c40c4a02c8450000d500300ea811808015170750119020740c0c4c000764540c1d480a40d00c00c1c0c1e4400040280002061006d048400c240ca40310000a80614190360508603510000e078415207420304040840c0c0500c001c202104591050580e5611104034039504982085e540700300000c0c01041000b09a507002502d03239014240d5410468810003183c034401588210003000d07903010380b0010011032401d48883c01614017004124809810003602c50849da0950703000b81c8600780180c0b8541101101400c24654070784a195085412800c2c0348080b80c442d8140885c0329030845042656a040d4140c00002100103420040040400724405050000400d494401100d5550748a6881c00c1404000140405500343c00c4014003030000c16030340d459010950042000c2e1780042c2a1500004000c0c20501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 94011142 1250 94009892 94009913
    0x4050a09020408070509070801120804150509040507022e090c0b07031205161b0c0f0503210909190c0503060415030c0915051002061b03070e0402070609020409 70
    0x40041c0101d6140c81d036170344d0402000d1a0191000380101300c03040d00600c000d0460445510116006041107850039989503103030700348407190701300da20000782011801628502e4039009242d0401c0701440280082415518000000b02030340c03c2d06403014003895407001c0c11092682003000505d4000b44e0664810b6a40d01c107a0b0f0040d800120102c1c00151281a584507900c894400c01d801807d00e42c0b008101c280305910b094400000c0c4050301b0f81d0b85000c50404900040041c90300f02c1c0a88001500300c078209150800749440c0007042c8005044c03c0c109007a4000110707078040c058640c128411100c1824545131010110303066030031440342c101020b04104001c0c80d4607401a000714007441c000c1c1c0d41007003d01440c80c01c0203440c40b50b40c04014845402178804003c40315243d0030001c1040800e40da0841da8a99510010b600b600301d4100f040056001441000740c0041c01c2d21288a180c40d00d440aa8a0751500c880001d0403801211782c164812540840c0325414004180e009103803680e40070340200401c80c2c01e42410307403281 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 94012392 1250 94011142 94011149
    0xc1305100302041d01060e0f0d02090406020408070608160c03120f140105010507050718021b0604030311070b0c13090e0601090f090f020f030c0a0311040507090506030412020304050a090204 83
    0x124122000813075002c10003402c54102c40450f5142260644100c007041100300c041d020941d48404584800300c05a0340b9201c94a00581c8100801a03555183c505001d00b010410f81c000001d001c030200800c02c420b426290381d4402200646807003d07044560380340686264401c220100399071860030200551a080d00d0303001d070300e0414140c28040016aa83d0004544511a400c4d00400b1600020310802c01e54103800401072520200010150400000403848204940d8040050640350f100ca001d10040c1070700740c8a4800d4480c02000d040b464200c15440da116012400351510168000018030b12000c5402c0d950a40040c0c0352100341848021006485560344400a0141c6500180b2b041d0308414000407900c104c0b15581e611140781c0345140040c0e001c202041c0080020701e901401242072100c0f84e81d545d1a0148084c51040a23880c03141164601800215000102800103106491805100076510300d0141d07540541d00a07003c841c2c1503030303030f000407419030003240c1c84141c1000400d040801c00200f20f40262096 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 94013642 1250 94012392 94012409
    0x703140403080a14070f08070e03030a02010911060429210f091f0b18010b040e0604050c030402120717070911091f05040b0a08090c04140c130510030204 67
    0x1203801d03241500190300c02545d1610100d48540c0c0a0541c080c0a945040c4c0d1141c0e076400d041588922000c0480d04643c000d010140060350344c0c0c0582c20421030071340a03800c490301065407001e0030b0608298600c41c82d000020150040b2901111003050111102e00c100c072a0007a1450b1311002c070102c800900d41500d0001c0d250b0b0006085210002144440c4c0014020415200111544032210b031807000030005020090429070003140900105a00c1c000014500d03000780ad55112181e80c07079261603030750360f1003100140955200e94180810b0122220704a820780350400c0c2c0440e1300001d5200800d82c100d01d8411035500216110860180f0442204070105180040314611742090007a400c0c4100e214040d4800c850a8035030216140303640c00003013000c10615809003401c0e82883c519040d01d40d400702106800200382180041c05c01e804010070b204040c04054042601500e00340300490501041d4040d4010003000020702144c081a14a104112080e440c2d0042ca00a0039107501c080b845d10008020390310034040e0420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 94014892 1250 94013642 94013651
    0x91504090b01030b01020d0c020105040e01060207060906020703030909110d05040c05190f06051b06010b07060c0302090d0b06060f03010e0f01080f030a1404080d09080c01020a0c030b0703140403080a 87
    0x154044d004156109a0503409440b45803c0240281c0301c0c01b00c05041681000030501c008141c44000d038840601070210340c0c000300407a82c0707070a00c010941842c603044203046400040c410800250800010401c2d01c000f4440440c00240307000c0c40b4003a9000f0301c040c0898160501040c00240041d88440030705544054032003115005180c0e83c002d0250f03c1a103d070302c0e64040402c0781003002a1282015000322201d4081d0f81d2a650581b0211034a488406c0c0c022641e500e4001a0b40020000c9a10444c400900c00342801d41c20904820001100e8000c80b9130050a1613006a0018482d6a0703410226050030f2408000300e40c40756110040072524050071a080c10100e6811400481c042c4c2e80028042c2e16070b030155000f503151140350710701120200411400300007016010301000c11783c010300b0b0044000b41c1c0398940e20041110724243c0000c1c5016207500c18181175402c82c148250204522501204c140da4004541618039100d5610450040c807100d903000c10380c07000d08000c3c442056030011f0202d0080071402410300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 94016142 1250 94014892 94014911
    0xf070303290901030b0603010902180114010801032012010e2a1c030c0c0b0d05100614090d0b070801080c0105250c030804080f0105010e010302030d050f09150409 71
    0x41411000703590640c0e200da0403a00400000703081113407031640900060004610409203901050082d0002c058049042819100610148580d8030071076410207000d02c0c042095501d5a11a0000408011a440c0304075003420450001526071400785c040306002e1100030009055601e0021b0349807001d85d2685201d204152440c141a004100403420b416900205000c890403d8a18280c81c0c81613078000440610840c2001140490f008001a000914030114071a5549034243c101000b1150010440c06030000080000e2182542c041214001812501d1030b050303480a06000181c042c010000c002441990394108100b51a9405030110381218413007400c85130f03c1c081800056503240140301402b00d0700307064138030301d04c00c00704000c980080c100340191408a8401d40303a8807440f1055005400c4403549074062000218079400900c2024018000d00148485650540d400203480e0076070703000340104001011403080c404144d0303181244c032403070401000d510680c1840c0f107084005811600c83c12102c40c4c640600710 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 94017392 1250 94016142 94016201
    0xb0909030906090904060b1302090f030604030e01050708071b1d0c0906031906060503060307091104030303051801050103060b12060601211d03030907050d0f12050f070303 75
    0xd41400c1c00040c112400d1250030000c1c040303ca240203200381c031041d4a5000105581d01d5081c283d07050300e0701140c00580d85a03250400e02c1700c2c0c000d40c207100d1802030384050708000200342d100d24101038460b824078000c0d13500e05c128101881c90f030150300b0000d0b0503000e002010406824000401108071040d020030b50001083e19005ca00002c40111a103d00c021410030100501d46070040095610103c0c5440401e03480200c02884000c8502e0742e0001e0340420303400018010907180130886440202110300c0203012400060000512501482c032000b0f09064a85012900e8440f0500000c3c89154a00002300000d40e50780c04e140011303103041d1070307040d0141d61303140c1650303a8140c07002c1401813044506850b8100200368840041030000140c1c03d94000740c0d070340c0b417041120746144140e4101c107203170900c8010740c0c0b40d0405440d8241070219a502c141e202d0540000660700203502580140111500040a0141013610b0700043c0d425115010315180640000600b104c10503815511081303910001000051012140e07100e00e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 94018642 1250 94017392 94017397
    0x3130506090616030906060905040b190b030c04020a0512090610060305070c0f1502180f03030309060c0702030a0b0403030905071a04120f020a0e07080601020a0c050d03090b0a030b090903 82
    0x202804035802c4a8000e469601a030400f038626841500000313600c41d908c545200846500381c13030480b0395034000003e011441d100c100104c892601103480c1000f441c3c0c96440001c1d41c50781a050090300482c6c0205041951134050029a5000e10558600c13070003901c0d041c030383c0c9502c0f41c0c4212840140c419401da004640c1c079200b41f207003070300c924030b10b44595054004584a805440c00c6408044809802400c1c03241021059030005d4540515402e818510424001041055001880b01ea00d4040d60091040000031140040e2007078000c14036081041d901c3d4101e00109061001540000c0d0003c3c035408180003c041c0d16921021583c0e00036002d9035101d50700d5030058401002e042004140c0340c9814082230116262101c1202e918510425054a0003046a4003003098001c032071b401818000c0b0b8280800001981000505034020b000748040c0200450580e01c000b0750010750b004a078010102024034500301801103c00c1c02c0540002c44030240c4802d00d400c2c004025140940036180112110800b082010100209 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 94019892 1250 94018642 94018651
    0x12040302010c080313140703020102210f13030606030b0a0507030c02071502070503010f150e1b0307110109150e06010503100b061306020a061a130c050f031305060906 73
    0x4501182c9441030b01e0b4284140c0020305000035407681d016000d0005100800d42d83d01500c568406080124a14000039092005014103000e151403540d41d00d1000e4203400c0c0480700f42415101320191a4140008042900252501b00400c0d50f45032181c04010700461038a40f9114000d030070000d10041c1d403138940840c10750b0030038039804024be1b1082c40180f1030a0200c54288018a00a10441e004250340320002400d50701400e04501e40c4590710012104c082900340f0820000d0103d5900c3c444080c00c0880354145075024400b001290400d0100c045010140311300c424000d00640c4800905c141142828a9000010581c2d6903416451800c22131140316040851050f0407603200038043e09941e0008003600004d000b0040d030302a407040c0100b080b1a041003074000c202c03000e04450f600802c802201d62070b100e402c41f11003101c80512900300c0240c4101655a0388034140039040e82074004103031a407112500307441758020a48000340707499012042040209a400c2c0200380140100100c4109441e1000420780b1080141c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 94021142 1250 94019892 94019897
    0x91803080406020c0a30110d050f0f0310090614030a060b010309021008010311060f2704090803040506070809100519050103030e01030b15040501080402150a0504081204030201 77
    0x50000700400c1c4280c0c080c00075030030402c0c03d40311546000d6941213102c00d034103080c0d20581030411507002900300d440d0031441d40180c198144140b9145e80b0080c41903a492140c82407030200600020400c10044100c410340e5058003180802c5a2a820b10100506060b60b59004201e1002e2810200003480c000003000c007240c100015000e45601e02180d102c46000e40f0740024154181a00d9024543c01600c9041110104005590b030306402941946051007042c1003000c4898469401032048203000c0c40d41400b1110f012450395845980034040c0400d50440409401400307503c01d281c1040c3c081030245200045114034807038406d0300d000d40e40c3d410056441d042d0684080010380d01c414003d0010380c4165010343d402626500c0700b44c0d01034544980c50800d640c826003003240000c00064a403001542c05014102c00040c080303c940c204400c03d1401828a4004c0e407252504001e000780124055460340783c260341c400c03220025415034409940c81c001d0481c0e84144981107940c411050201c04200000c016642501d5059 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 94022392 1250 94021142 94021157
    0x102070b04120503090d0b040303060e0f060d1b120201110706080c07050705040510080d020d1e030f09080702010801090209090a050703140403020705030c090f160c050706020601091803 81
    0x960100507100800e42c040f142d41c403003040031a03c00d559040c00b03150381070311800b5034610310304c0c1510700117051312140e0740905400c1d070700b04007440044080105c400d580710005035040000d10015060401141d04841c101c801c2001715010702203010080d4101d069102030003030703da41100c019103101e000c0c3e4400191048000280060010a04040f160802040040e0040045038600c41c1c958000800300d840c1074440c40c3c485070700d004081044447c03e00c03e40e500310700140040d01001040b01c4020b042601d019410103280c4651080c1d103c001d9000741d00c456200740da0410108078605403450044030b00d40c40020b00381d012031600000080e1040d0345000312410004060b01c81c860644807140f402000c1c06001c1c015805242d1500c21000d00c903412552110701c80c900960050a5280c5000285400c01114054072400348030101c00308050341040907096500702d03891840e802c82408800c4011103ca03484000000c0c841c1c0504100040d4443c0d0002c2c2c503e068408022080000354840545894140c40340040100802c404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 94023642 1250 94022392 94022399
    0x302060601023c030403060f051602010902030606010e1512010f1203050406030504020609060d0b090105060a2319050d0609020c0d080a0b03030409020c0609010207021e010507080d0203150102070b04 87
    0x44920f6800c0810350900303c90600780c0365951401520010740c00d0f1b245055403001003040e1200d2a2100100080e802e000030006030680d500440c1d02c50030300400b0641800a040501341c0291611080703075900c1c0144a18640c1c407440440d000401c075440a114516401c8201e200c00700c0c000003d000300d01902541500c1c0c0d81c4c0752030b1901c0000d402501004009036408101070001e24441d44482c002800d0408240b0000a0282c0309e00d0308000da60001031300010b0080b07a062281c80c80b60790f000241540c0410b00030880f0102d01c1145150610948170b89808400004446186142c4003030b04803020704800e9025220074440203031684921000c0340603140b49440542e101d80460088280190380041d042200104040b0b118114480828510342c49940040d0401e80e00240006115100f44985904441c6103802589884c00d10f030000341c000c0400c4031a0341824070042d040d00368142e014000700d80daa04c0c5e00c070102507105c50000205c44004e400071620714112a5034007510301413540c80822036006880440301950304103400e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 94024892 1250 94023642 94023733
    0x705090f13170c0a0611030c04090209030705061201080c0118030b0603011b050703030b06030405060403050f070b010905090f0d140703020c040e010204030215030903030103030305090316030206060102 88
    0x20481419110071503180e000e50b03401c0118200802e0420301d40001040f819041e49080300898100c03003d034aa0955003070041c030100d00300d11012a030032a00c402c8009a2590110400a810180d07241c0c4100c2d8000c50005500350703603003d01b595050407920010b040d241c20031803003001034079051244040c008018031203482c00d000003481c0480d8241c0004001c0e000256050055004201100c40d82d02c100010a101082c283d007015454050100003800650300300e4150f04155a0742035680001038002810321070040303000c0c01820004403c1d902c035107030065602c01043d6540c941c0700d0010181514050024064090850b07181000000d071070010800c10740e54000e0394805a4140b54107034028403411421170003550014190ba0f41d40c0d008601c0e007052150001a84c0b503255104000d03080280d4100028000c07410b2080000c620804802d03039044036014200032940c2e507500780c0d0302411072064070301a264481c20840c25400f07250b40010000c2c800d402c203030211501600c00b1002241d03440e04d21109400030b40c5264504640c641c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 94026142 1250 94024892 94024921
    0x103020108040803070e0307030c1502010e0c06160f120905010e01020606010f0c06020d0501150f121503021011010e0304031110020a080a0309050705040605030604030c110a1202030705090f 83
    0x1c5d514600140f980000200084c204541e5500c103075070107102214288180880a07400c00c1d585011030000700001506141c442c1e45070301e0403d0361903100d102c001c6400f030680360b125458001642d40c03040c0e07210f04141d418540f03080c41c0300c0c1c4030ba1000c00062002c000402c841d40600d1240d04440750580090040780d450f440111071030580d0701c2081003007180f8008c00c0320006065001400a200c1650740100f02517041c8484090b00121110510040090483c820500d880d085450880000215540855480d0a1150a8804e90080e03400290004041d07610040c2281e4400c10000000040100078086a505004515640c0c0114000030b03083c1c1d01d180c8940034052070b020354103218142e014015100800e1044e01d42022503000b01c40d850002c02d88460180040200030f201070b00207401c0480f0100049070402001c40e50b51000204004c05002d0180300140502031800d1148100d054001e00b8554826142c0e1200b001d81c21603008100d000344910040400c051500250842c803900ca40548074042d0f546090820324042d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 94027392 1250 94026142 94026151
    0xe04231008120301031101050708070803060d0f03030b01181401030b1314100603050f0f04060b15091903020105030c0703050c1605031e030a0f0908010f1401060302030103020108040803 81
    0x2010528400074034034405002c40d0490039994070000b5100e42c998141010703040400c54103d810004100f05420006000d0740607200e803290068a01d603200d949601c081030a41c00782e4500900306c01422400b20040603810b80140603040f6080c0e9404020f042c00510040d602c00941c040c1402100c8004c02d41013140d4445d601140440c00300810b8880004400484a011505003850440361000d0540401100b0800030243e14000d1410303103020807141c81c0510b42d0519030034000d00148241800c1d840401d00303104aa400078004400700909800e4042040c8183c40002e03800880c025002d2a5844203500103800f241225004407034040e11664a141c1e200c076485c0b1210b03881b2041c105c09206003400707100d204020800030722400c00891003101d01614203041c101854855802c505440d01e0045d040100341040c40401500c000620500f021844050904004c3c0d4010106030040c406a610f40f900b8a071580701503400480038104240c14008050342c0320032007101a03120902000e80481e030024081030010384040c0c02150300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 94028642 1250 94027392 94027411
    0x604060f020705130605120c090a110702120105010f080c09010905100e042003030c150601090803030f010f06052b0207060e060609010f210602090307060504060e0423 73
    0x1c09490700c00150704500b050704180c075025554202441517041c40d410b101e100103c2c0c7c1c40140301c11421000040e680c1c1c0d500400701c0c0903254a450701c580b080c1c00d0030401d40c7c0809600a00003401c1603a55482e5a009106c01d1003460004031403034500140c1c20902181801c42d00702c010749214056030a002640b800fa0138054041d0038501468180003a102003d4000640950f1090701001d13258201c0311582a00b0b5000198100c4c400e800802c45105003900001300004078000c1c080043d04982d492100507a000c130407641c803200031400000100300751460742c1003100d4140d035142400d8002564079842c3c2120075000700c1e000c100c40e906000d2048207084800398441c886c2d014090202510300440341e07541d03009441d083c0c0b803460350a51205050080c00d15046140c180503100004200d00d03a01e10b01348840481d44401340e0001020020111300109200c60b43d012115007003800b8044070000d5a8424000300150300510850001500b1351080b50054601805042481000400350303000e0002d44804140c2c5409010304940c41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 94029892 1250 94028642 94028653
    0x10609050612250f030501051e1e0604030609020a080d02030a111204030f020405010503010b03030a05180301110403260d0b01120c0302070c08060708070c050a02030303040c08010c020c0604060f02 86
    0xc50301c000e00c62003200703d009564090b5000000c10014098440682010b48a420712030040851540201c584120240040781c007602c4071604c250680740c200440402d040e420002c001008002e04c0702039007141e0300c118400c0d81e0314520320b03075194183c030f48401307065026200582040184008907440b404242000c44003980684400384d0303001c4071800f2264060350049600d540001744d41000e500e03091060310b005100030340c006c4c000c5c1118600045d440b0711400a40c50107101c07010800d6201c818403a13013201c0e40243c01030020005104001c1724005144c002d81310807a003060200e10b0301901d13910f0b91801e000c03080000501043c00e10720358800310400707045d03460903490412603082d009154103811405009511851610016900e084074240400550450340001100c0d600880c280800c45038082101a404103041c80c04030004030300da14106041c0550020082e5244c4804010300050080200400c4c00301d4112100030041508086010b80c0c642c441d40c001241c0c0041c080c04200115405130381c968199105602c142c0e034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 94031142 1250 94029892 94029931
    0x70308010317040801091101081003080307031a21060a0b010c030c1a010f0602120c0604110a0e04060b1e0102060712060905010909050106120c03020607081207080f010609050612 78
    0x900315000a00c3c1a00c043c07122091f032911650300240ea0b681c12040070b144162032076055441c0c051003880301402c4c1004047d0341e03003882042c081403000780349950741d401410144d641c0011030400210b41d611440c020164083c8201089084c00c0d58803584251300d0041e195205003000c561030607070300048009025908201100422011110822200c1b4040c1200341e100542c25410100d00a152259407245100f440008110003100c9c003100062140d4004c0d0312400781098002144080307020020790390f1006103044120002c2c40704000ca2031b00100f51101c0b007550011030140d45007641545010810b41890701513003000001c540720710301c00d00683d0f010018401c1c0102d02255a03260038400ca8800340e0204800d20340d03400d04c100c1003150a010389070081c400784002440c0c07000d940d20751228642c07551000a00c240c400003140020009204151441c008228408403054601680e01904840c400c9880c03950000508001090440c050070503c0140c407405800c4a00381068010300c02c005035000b4155103040131880c000d02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 94032392 1250 94031142 94031159
    0x40b01030b0924010504080c100203070c12020114040b03040b040c051206091507050409020a030f0204060e03100c02030d0b04200a02011401030f120c0209160e030307030801031704 79
    0x85000d40001500c609003400b80f520882c000752031a6241c1410041c00300300800c81040005036680b00d00c00c040f20400040d161004003a4518801d1120050803011800b41c0020b5001105084007810760003030301c1c3c2038075a1325464a18606481640140401c5e00018004607001c102c407a034280d58443d01ca0500806803989503c0040c08247c269240c50703c05911070300c2009140030041c405c03125500c0400b01c1401c6641060000070b0002d01443c0503100d02507a0100e101c880d10f81c8260000960070000700c108542c3caa031512002031001c242d4140c0140280300318000d11080488900c00d040c0f10105a5001d5800d0004455400d4040c0881e103400607400f40c2c80708141e190310400300444e08800245140d01581d1201e4010010f42550f81c0300e017007200101d0180c80108041440041440100741e40100841c0811083c1c95007580c0e140042c01003c0c0d08200018204003076440c000702c0c500a0329500780c5420040100030020141d9070b10032400d001700068040c100420000d14002d000343c0e08481c2d0500c0c41410a41c848100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 94033642 1250 94032392 94032409
    0x90b0a0e07120218150702010905010507030207150305160207050306150d02090a020316080705030703020703120606021b0303031e040213050a0b10020307020a060f05070c0f32040b01030b 82
    0x1d8540120081c0e0001c1480c0c5059038900700c44411240c070107400e001b83c0e81c0010b080030f81c191003058180800002c02c0400c2610910904c0060414041d01401c0046900b00040c000d08088a00300f00a40341c1c840040d50441c000280c140403a54010000d0106603103501c594501c40300440022071f0000d5440300c4580040c0d45089070a4440e0035000c000584900e40942040744c0c9201d420489814082d100d002d01107010381c4032084a0348902c0c1400c002d0380d14070a6240031513400481440e102d1541c0d10f00000815515030201e03842c11001582c106100030404a03c040541381d01c401c0d14001c03100e0b14546949003030a0300301420554041d000600c0108600901c0e4050010380341c00700d418a80103640d0f0051041c240c0780110f07131002100e21500c0103504001d41607021629083c41c4d4020f000074171050300c24850250f8440c00448079a1580214420303619559000005800c8000740a016000d40e800c1c1480b81042d509100d4100c145500c2050b0600d20400850030701c002800075920035410981c5400f41e48106c1c9d04c0d040e81 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 94034892 1250 94033642 94033657
    0xd1101020903060c0901171e04030e04090b07120606050304110d05061306051003110f041806020d06090b1f0201090605090312060f130e070305060405070906090b0a0e071202 76
    0x50360368055007000185488003c40d081f1503010301c0c010504c00d048020702c0300030500054499002aa50b2128102a9424104801e609134410f08000c110400c21440c03051312802110541c032018496102c0314021400e603200e41c001d5030f000503c18000500482c51001c494601050f014005800f0041d4644606003092400c030b5040016030f910f140743c6c90800c0258403905900032801450f0021550035035481221030800701e10000d101d41855007000d49240d51f26032152030300c2c126010100310f01c42d14a00e041406034020280c0c0c2c91015180403030025030f144035401505010300c00185490540f180b5048041a0f145100110f8800c43d981c0740800400100302c2e20429004402560043d82c035000440c43c0340d055000010410740c051418548440070a4541418000d44103045c3c0c000491001030403801c6624020080c1d0015101d40b041c0024002480350101e024025100390305000d100c400d48410011054800001d06150081c4032a6030401c1011400d000f030580001c068a0401c031002c0c1d680718000282d8100c1c41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 94036142 1250 94034892 94034911
    0xa15090615140102030306210c03030a0215061f050d020f0403150507030b0105031306020c0d0305100b0304050a030f020c1806010e0a03020303040b07210306030201080c03090d110102090306 83
    0x31003440b91074908000d02008031424030085140d4038001c40440c0b62900e900716407081210844c1c0e207042250109101d00c152040010301201d0b12074152079402503070380c1801755020034401c01c50000300d06141802041071100c5040b00090001c90b055202c01201c1aa00c40c60101c035806900344652500041410000c0c801140030701c1c1021800c017070769006c0008640c0d01a00d80f100741480d100c900c00c01e40e43c002065991245d00d614502480149505180c5d020380700361b501c107140c3d50141e00304042c1042d0f0154002401050800e20403543c407502e549030b0188610003901c0242c4075901c004491030000344a400907140408075441035555040d4000081000d8400303180344003680e0f00c4c0803410888656070209040310740c1c0703000311409602d081c5113070042901c80c030550150b415140700004801c014040f079a8417415002c0b0341641c400b10079011150340100182018002280001e510801190703100c00900107072406202070308098003464100805c146c5a80601c2c1c1c5480205540078010311003d6942030090510404c401d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 94037392 1250 94036142 94036181
    0x5030c070f030209011e140103150902040f0602070303050f1303150e0105090a03090e06010c0c0e090d05090303091011150610030c0c060b0d0b1e090304080a150906 72
    0x501c1041800c0034140c100b1030030103100e0710b40c00d41815401c02e0030746c0480c0c0c140344841c901c00c0c0319000100c001e08210189181c080c3c101050002e110161a4010000c5407a07942e0010481030b00c50314226100c010b140700140000d07006202e60460703565680e0081c001c2c0c0144031840d2040a55a68605078441c48260644030095035850011412501c00e0207055400301c9600060078441d031031903034060158555406001191b004913000942982d000b4200442165004568401c2d60b9607103a84407948204119140e64140c001e20310b007201c40c0c9014030b09840082c00000e001e14104030440c814049040382e41e040002c200688042501a43c0c803092206000c0d0000380c502202051034102c00784040c00401190304020140b600721440c00451b0b1141e500003801d540f001e40072a03480001c0e00046c0ca21341103040041c10b140c0c001c1060020124028840d01201880c0424900541d40e502e07198a4590003a0300c244c0c04d4039005200f071040009c9104403446040002140005250340e16030301e803a021180b131700c4888440c900e1803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 94038642 1250 94037392 94037399
    0xb04020117091e0c0a0b07050c030313180b04110a0e0306041211101406030c09040b0106121b0216080d020309150c0d020105100906030b0105060705030c070f 69
    0x30440d141481d08001025103114201118101c0d960022840703165400120914051003107401070000001001d4010501e8441e02d40754040750340280d0180504643e184520f240802541c1000b006030741c1600f2450010b034403c136140c916403050000c511070350040180c4e9034010305c0c0110780c1d0714400d02d07240c4a0300151154460400080c00350808070320048075403081c4d0090301008002105c00391042404010703032078101002c0c00c0000d122854800e80b05074442140b410025202883e400640c0e02e644101f070110100c03045281c0d01c1c000e00440f420243d6010303240910301c50060100c14000d4203110040c01000d0b01c001204000400d8840030b00030300b08000c000581161060b5940c044400e446280039081110107003d09281c01d1030080d5980c458110518001e0144159040400010000b84d0f001003501d80140c44140610790740c02030003044100c81c010110034401801048240c0544036010075203034840420103e076405d2030100401900001408c9526100800030445181000e00160004080d2400002e42c1d035400c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 94039892 1250 94038642 94038647
    0xb010906050105120c090d0c15090504050712111c0e010e1c1404030b040303060504061401050f090d0c0e0708060414070f021c0c1103060402010c0809060d06030b040201 74
    0xa0365848241081070901882d20341d20355a40c000340c0c201682d0811150b0711501440800c0034100c0c401ca01900d1500540c10002e10851408204501002e1035038868240c240c64408001c2114030948520000588040d5801d80c0b00c1c0281c0d001071058602d184c01103003003503130090001d00e03400d4035040c58401854840f008400101801d0040e141203d194101030001c0c0d5562102001a407811140360340c040048000a501000c0b48540498002e544c01401c0b030081c43c0343c1424040c0c0500380a04c0f4460107141351601c0080c680d080d90210716011341c0140d4a492410702089203c01d0715400044400da440016014000005080760004c000100050315103440289045800542549030003400030b801503003003441c04203460000303180c040c0c0d1008082c2050881d0700c07007280c4100d1601800b561038040502101ca5120002c540000414603014824034115018181203024541c8550090358001e011034904049040040d080328080c001030040501007501f042c507030349000300a0300c620303500503902d0156100030b01c015543d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 94041142 1250 94039892 94039901
    0x32030909070905060304080708040308030a0e060c0c1f02040f0303090f2114010b10020a150e0601050618040903081816150201020c0607050405030f0d0e040b0301090501090b0109 78
    0xc0241030040302d07a464007010403079038800140300800064001407260200060042628007454100180700e49a1801c43c04880017001c01c01c0c07015010740700c2d40f40003c2c5886002c400311400d1408403c050810300342e1800f840400000300041d400100c54090002003124070b100d80c803400041d8025500c1201c0c807403404030350b29241a081d4106080c9a5a01c1c1e03900d4044800c84890042082d0b845003050f08110ba401c03904a0052506076400c42d400b111407044d403645254002442c407085030041c0903100d07a003041038804904175503086c46801520b0304000c004208504d004009000d85039440b401c8c500040e00101c0000c0c040380c0c3c4101c41280440d9159040c0300041c8010b600b40f50341006c4210041209030607520039204502010302c1240c0501c60049001c0a0783c92003074060b103200300c0507a011100d6a00300408013824582041c0074003070180c07150300204000b42000040c0e01d00d40d0100340d1100b06030300380b0700c40621000d8100500c0d4141c01d07640311002240002c0d0240f0600c802c103070040d143c80c049541400587c0040d078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 94042392 1250 94041142 94041151
    0x60303090902040501140903010b0a0e07020d020a0f021212030403020d140a120218031b120d090608040f050f070911070201050d020c0705090c0904060f03080732030909 74
    0x2d10500c0144031698010741001d40c6018034110090701da10018000074054420b82d0642608281c40100004d460455500d0340d41c0070b10416000e44d084e10001d4142242c0c3d42c018503001908084017100c2e03110140c1000001e9114202d6000282c0b0300f040008004000e20784e0060340d04800503800101c008919580c0400c01c09441c454240c101d61502c1e00c10940100031918920a07403030090343c009030440050f903a00320140d030030b82d2008d400d440004200000d1a10344030f14500351240035107103081c413a400304400820360100012071902d5103590306081c285c00f202d1180006104070362983d0300c4540800421002c011001c0c4010800004040301f50900c101c0c0003d0320300024010460765400d020110060380c0090984242011190005840f0b00d10b0040c52442d1421035805682c1002c03180c4107209031401c4510051103100c0095a05101c1c0c6540c403014002c541c8558071003e41034503003e001107800a040c1004a0445801c1c0001004078094440307940300794110310480001c081c0d4400200132800741810006940d10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 94043642 1250 94042392 94042409
    0x50307030507080402091602010e0709020414121e010b0a15090603060807060c2604090e0c06030a0f06050316061e020601120602040e0a0e011d120a02190606030309 72
    0x544c10036602155280001618185940b8005101840202e200b580720790304480800007100c81550380d582c0d01d41c00075401801440b29464040c41c1d2541503040c0040c3c108450b5002c0300040051140750341c0031407224403e074130003500e055499015120050b0380f100405800b40030310f400031007400384002c40040c0c1214201d92101c41803509025041092801c00b113103450446030b180c24038111035401450314015803050044208505011518074651410510000c2e00a82e001c0c142d040121040d031020080e80c601d60001125400f9008000080a210003608010086045094080b5607a030b2a2000a410000b01c02c03801e06040240300760402419074041001c1c2c84880980c40550300c40b4002c140000d4441c00c050003480e02450fa409006420486154102c0d40109141c40708859581004840000602201c801c08105982441640000a0380343e01d4071030f81059024004100c00e03500c10310030840c5034201c1074a070810341c0180b20801988440b4402030301c0035240b081d400045c40e103040d0f140c046e00b0506242c010b003c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 94044892 1250 94043642 94043657
    0xf060e100c05180604030c0f0816050f04021b01090302011a010507020f061617130b120114030c030304120c061106041506120606180903080105060a0201020415050307030507 76
    0x80d11508907049580f060031012440c0710700010b010102e5018811640020800f5004070400150705a800c0201704c2a00c441d001500d042d82040e9030680016001c6018003544010b50030300038025881c0c160b008080c855040c1500e1714499808030b41c49400c541c003006054000d070b511a410040e803600404018604240b09080140c02d0a0068010901f02c01c43c240040707014050005086060a90714401c3c000783e143d004080010841e02c210700e5030a25081344000b41d1022024040100d40348010000391104c440000b1720510b05686440b002c03814804400540359018041d0318045019a10244000d20107002c816443d180d0201891402c004900c421380d0007482001030180c400600c032000840c005403c00d03003040d5281d00000711440e01d90700400180c0c1c010442d40d8901c5217000c04103e004d1b000b22003158000a0124401980109001c2c02e4071100307400180001e80d8240103100c0740c47c040014001448a0b48001420300703403a24410587e040320910300390040352000c420010600d6060080700e40c07020481c5420003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 94046142 1250 94044892 94044911
    0x30c0308011a1605010e030d0b100809210f0c0a0209010b040f03030c03020c040c0c0303050a050105060a12111b0c03070b09010c020d05070b18030606060915070f060e10 74
    0x1a15030240031183da00c58119448028140003094221404000650099130742e40d00f0071100d100b0080001500c3c0038001c0380c030f0701d100301501030140c0b0300d140c800c11003440a004541c0c003903045052071025009985034507030030a00075101000541d4001c1c002407008a0000c0680e464280100210503105a01100c15084101b005120040f00301650000322641828468030010251400b6400c000f40310413440e801c20300d460440500c40f60301506010959009480401c81e40e103814154400380c4009005542e0440c008000034810300f44101c180452071540360300005080b060f07009408000c1c0d80a51700c1c02c1c202c0384d4030640300c2e01d151b0002d10034404c6919080303005054803480c2c511080c0050180c01e540340e06101000b6054000c1d92035100c4944140360740031040d100b05a45510000c1e00035000104030300341c1c54052300f0100d04035040c0042e08a00405004000d0b03070803c0940d1003003010401409410415070507042c0302c07500028500c0c01c1d140c0d0501348100d0300420b1104020803028a08202caa28007252b0a06110f08503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 94047392 1250 94046142 94046189
    0x1180f050a0531020c0102130501080a1413050a05070e0612010504030909020f12070809010c08040f020405071110020d0c020303060d14010b13060303080c0f040902031005030a030c030801 82
    0x2030b43e02442d9003400007400c0e400e01c40701e00240a4800e00240035400000c48011605840c000d54043e980d0036256001c0c1c54442800480443d000242009a601c4010012078007039010316542201072803045003250084865580e915085c402150312a015546420703050094074542a40000c1042c059200200140d15003518000c0117403045224000c03645078006010500d54442c1b0f02218840c0b5000c01151038130b810b0800c00101000011074880c00e1551920000c40c4602c0e11880b9001e0281d90804885001c8035142c0d001c00c0000d0102801c0d08051006d401064408104148014000d4400302100140c540e01d114004074280d0b01c1503207182003150410400c00c80c0c00c0d03a6544120071825040030100308640b83c480c41d0240101401481c141e8042404041c603d8880700c1c0e07401c11001c0e28483e984400c25a00d91281711009406801c0d0b402407440b400f84014005485107034003075036000c44d02c0c40c44040d00d260f8030b00102e03003000140b581c284e001560241c01c7c0800d06810883c80340c0103200d03201c018075629200103001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 94048642 1250 94047392 94047439
    0x618040317060a0914040b060303040302090402091f060207031209050607030f0e04090609050d03020306130c0903080f0c16081f0f0501180b0103020901051801180f050a05 75
    0x800304544074050109000d80c031010701240c041c0070007042c1044240e4003010248a900360813181190945058000201c0d84c3c180401501c0c00c8a40c080e10703111158807103500300060614018034a60f826292440f44a8501460a00070300040c00c80c0c6d006040b2071411424054000440288080148030040c00300300555110b004c119000c1642525042501407a000000c41c0d0100250507480e9000b810031600500b84502d95100116151180040795003040e00c3d008190142d000883d28541c1c84148901544c103403000c19000303021040054034046002c2038503540c64451680181645e0104480041400480700c0c0c400c114041c26040380c00341002c8010702d0510610780d10001c5021000b011380b00072a017a80140400e0300803091a80040e9003d0001d580c462201099416000002c22a1a804c2c4100001c00754040d1003220356507481a0b48803483d0588454941c103503010f507410801e040000b0840c20001e101c110100e0b0401402600704100044d034a051f0811005800503000180700c1c3ca140103181041941c11100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 94049892 1250 94048642 94048667
    0x10f15051201030b060a0b0a03060f0914011a070b15100c020a150e03120c0d0503130609022409010e0f06180102121801120213030201050309030d0f0506180403 70
    0x209510b1903552201003017007501264007d100120010820200c1282c00d90007031819103910034440480c030f5a84200340e0301035a0b41d8090a4907003424801c0180034242c0b04404218615441ea0a414600007169a594940160484e142c0c4c0c03445009090044a03441c0031001c005400b4020b150190b082c4000d500000c1c0f440140f4410b401903c000e5101940c607032170280c1101d0951a1008040c0c603a000e40800070f803805c0390310500f20200c4030b00860181c105181c0c000c4040c0c83c007424928042c4041c2c2036040c1d58900c01040c90540070f03070340080300c00280c0d443c48a5331065101040442591030f9294680c60002402001c04c520740c1c0b5105500450110319a41c58580595550780035051070480600716500047c1c0c2000d5044010115501c0b0003d45840d0722111250400312083e000c1c1da0700000c00b50410040c1c4124050141c0c62022990886400c0015600c0340014680100180080e280717402010849402210180311400000395102c0003002554944284a0b501c2ca0066020041e07081c030789a54001c1030440c1024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 94051142 1250 94049892 94049903
    0x902011d01090807120314040e13110424060212070602030a11070f0b010603020301290918090601170706080411270105030316060504080909010f1505120103 69
    0x354051066880303180310000412980044d035203015162584820b50b0701e8074030001d074041b038035920503500b44554600c200c504036144072500c01103c0e2507400d001c02e2003001c800e00a0700c203501400050007007640c440c8076122003404086a100c400c2440c42110325a224407540c407001c19074014451482c070303d050344c07403c40d0103056020304016529a540c0340c100c4001c0c1a0742c00c2c080341c060b00214168003000505031032011250302800c071107202d50b0390310315049003680310901510014207218140c02100c06600c2181800e0003d640310403508050940f404500282040406c82e1228641c10f418000300300400d000d000c0c0075005031a000502582d0a1101c60b64400481c890720f020001c90700c0008040c00002c28800548a200401c501c2108882d07c00c081101e1441c200c0518240a103c00000341501c0c000003201c0c0c110144205002c0b006145440d058000e0200400c19108040e00300001c5c80950b50f0403440b00c2c06032440a8201802e5402d01c03020380e4101319410841c805011082005101401d00002c2c2d46044a5205 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 94052392 1250 94051142 94051187
    0x6100311040b0f120103080a1d1003090515100f05100c02100c06021303030f080105100302090307090903170106090806010308090d050f07080f06040b15010c0b010b0306090604090201 80
    0x81c0e54100344604c801c0304258501100010040181c0c2d400104490076643c0da520407c3c02c40901e80c2e450a00c840c52005a00c12440091403601900a4000c3c52070640698250b603803039070880c1142e83c1c3c4080f0484e100441003800603404e010513540c002819018000c190b8074100d03c1c0e8010f0901400b440342c0020013030f1191030302000900b00a4495842100c5c00c40c2d0156040d52558040818038034074800500048001c240a1071501c03995501c1450214100c8800400090b861041000241e000350710210195401d8098040c0101d4025005d001e002c802e1031207540c400e8000b5500180140602006070450030800088407400c1041000c00502d41741036a82180380d150303032445058001401c00030803202c01005401080030002040d400868030904640c01d90301900c1c410f1410f900000d4889604640081c4014410b9001c20241292000703030248054041c1840445410241c4901491803401d90090320f031064004208030072400c00718030f80c2d500088107680c20b01030740c1c240b940040c0100c50010b00d802910100d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 94053642 1250 94052392 94052407
    0x405040902060c1207020907050307140307020a0c08061008030c0c0603070918050405011b0512040c0e0f09011506020a020d03031803020102090414010f0e06040207060e010506100311040b 82
    0x228811500e210789003800f200c44601307044005050135008050160700c00c040d01e0300040d4041303000e10126449160545c0d80c21941110303400c110740c01a000940540218422810600006041451840050f00342c2200500b0340b0320b410703081820803100c1600505444e030418002da9014110001d8581c075600c1c0d040f14140c0d2255110103045038095103540c4000000b26141900e070281c44181e900c8940100d0040c00248007008005a01919604d46224108005001000803484e800c02e80000240c11034031804e80090020340e05c01b420b020300141511005003103600700040c00882102440751180811400f00b454800d64901790000e5296000120040e0185075046c1c207080804d8400c4d44004203d94011540c1210303001c0300d0400034000e4210782407042c0902e04d0110a074070159618820070381240d5050501003003450800780e0003c00d60102501e01782d00144c09001c83c10000b84d05008408a007010f160002a492405904001c0502c646240c04070a0520300701180c24a0121031003190180e80c91117140d10f588030038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 94054892 1250 94053642 94053649
    0x7050309090a09051e1c0c030306080d120506150a02060a200307050c12040f061209082a010501230103090c05060903031207030507120204060c150b04091202010c02030408030405040902 81
    0x21b490714500300d80091440c1ca6061680c1002441c2829402640c0030403110384c4501c0060b03640c2054820041c0824400b40c1c00e0302d07400f141c0740c100c254070600290100729046000c1c0c8264002d030304005800c0300940c10603010498114042c1c490300651000d00104a80041d8400d0980c2c269488098800d2007003007000100001d5800c010050342e0034244002243c103503126a0b81104140e440024060500007809140c02820784004500842c5020b58100c0d8420349031074070150300504182d030540c1c0b9400f81d4001340d40040c07261110072321034a8000d002c5641401d00a84120504102c0c5126a00d461414549003910300d50104045141200a9410664486a40d4101030b40042c1c51405103d032800d840008000c00c00150300c1e415002180180802d4440109450003150054240e018138001c040c0046c1540e070301030000c00d00520101c20000001c2e0170010b0060100c20110b010749000c48000d482e8060086000011a0340c2445400340361401d130310145060504042016880388158482c1ca032142e034846030040d0075941d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 94056142 1250 94054892 94054903
    0xb0403030e0a0525171902210606130c0c02120a060203040804050102010b030a051b060c011505090703290103060b03010905060a0b0702060714070b07050309090a09051e 74
    0x3d030000121100c00a604862000c002081031540030711412641000880721106003100c01e42d8104038000d01002c0c58040382e202860303c01e2100aa0348090241112000604a4002c17004850801d07000b40401380b400c0d00c240503a03960004075840407103180400c01009144d00c00c41d5031401d00ea0465142000200844049240068441c1e0160000d40f0020505c002c02500710b004200300e4100303030000e05c94070010300300305500c0380c40380c24024025420000c14880540304000c0221078841c001080c40381428403034080c907030844165a602e80f002c890711040c02c0c401e0740351142d0515840903a920b0140103a0909800000c0140a407034141c03020380340d42050300da0b040da0103a00160040c1210451860300c2c4d6030346030719880207000150742090140001e8400030034410412405c460305103030042d0103c4d107031580e603560720681200040000f4402e0b00500b0b80100d1314a40b11130052065a00600013162610b25120070801c404002803c04101517141080010010300b02244210082d520954045071102c84001d0060400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 94057392 1250 94056142 94056163
    0x1050f1306171b010c0203030d24080a03022107080304050109080c06010e0705030f010620010501060905120604030c030f1206030309170c130903030b03070b03090f03070b0403030e 79
    0x4408042640d41000001294540842d180044051601403800103448051760b541019415030410040c4090b22452900608580d41c2c00c0400082882c920081780075003001c09030031081d890342090420387e00f45076040101c000c41001c84101d21808588083c9012035512800800a01040000c40051305000e400e50202c0e800c2504454010395038111401441d03100c1c2c809001e007440c0b040007400401c04081c460340c00da0b8402d54030880d0bc0c041d541d0800e03034244c4203281d60a1103217040301c1c0f403820680594102802054000e100c0d41c1c55281c05242010108006840c0120480b5400e03071144013003102013940b0914807003481d601402c0c201c03000c4501c80c02c1200c2c00551640c451000500f0540000101940401ca4400b1100424802c182003e400700fa410748a25070172004660041c0480503641c1200d00e2584000800d5100b400c0018007440e102d00440d01b00042e03540070240100010040201c150b0042c0301503020100074001651030034000e55201610300001400103000c165440c0200d8403070030340c20098081d02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 94058642 1250 94057392 94057409
    0x15070602190809010b01050301060c02030a06111c090b130305040905010e0402010f020d0801051203040806130203070506040b030a05040804050904050d11121b1f14010e01050f1306 79
    0x321289103561040c0220900110301c0011500d100060807080b040c41840c0000728140d68113031440e40f8280c004c80300700d080c1c480b059a02d40240710740040001c40302c0c414000c240458203002604c40c1044802c1d1507940c0b4508603100c0c4403038109003402c800188003a06495024440010b1701c4200815418115410301640c1c1011140900e03241c0046240c3c0041140303e4400c500c00d0761095041c100801d0f080382c40d500c007116941d0110b04044018041858914640040f698403042104c3c1803a55901c002403034504c06407048e414400020660a09605040c4500e0000d81426a1f5017850b080c50048091010b11008005860259807880402d04100000046130b006100c01403654030319080c01d04040b92641e00020351440414030040403a019103601250400c0603500c0c1601140c10440401100369460300c941501c0081c60044416100d07141111500d0300040c550f10b881c000660f14885904403d07801c0068000d070424518041c01046640c0d10742d11642e0340c4c84016124078a01c114800c1210004d040d841c2c020008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 94059892 1250 94058642 94058647
    0xb0f150318030a09140d08090405311403030f010b03060303160302010c030506030105090703020603040206040e010312030e0313060e12060a0902090f06030a12170406060e0601030b01050915070602 86
    0x1643c1d0f025a1320410740d0a1200c100108099081c20070100c01a1048000c21109060204e5042894a58821a413240280d034108c440140985803100791400015501d0b40381060140000003403052058a600b0702280c4580251b11b9821314180c0c0c003205201c14803440725004400400200141c50034030a541d60105401103640c4a1240c5140c064042d16140e1140c0303000a2038100054600d241c140610390140c013111001c0c00c94030b400c580038445254801801030740c21404c2004000741e9810704401d4603000314003c150035804141c44560060503903000c01d03446400c4d80e0003403240000000c407038560384040f030726181408400308001743c0100d542d481500c0c01400341809080108004540507030030046680e8401c6607000e046665013544211503000998640d90140d2182903400c0009011103e14420443e6074100603101c0401d22080440c5070001300d4040b144a519224204401c6c0c4440004a8201c1000d0034107211800810700020300b1030141d814002d204008011040d40415041e0742100d80c0d140d04000150b5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 94061142 1250 94059892 94059907
    0x5070503120a08060a0e06040f02040e090105070f050403050d0804060905070807050307050103020c030a140f0d0c0809060f04020105181c0b070903030903080304020406090e0a0302010b0f15031803 86
    0x40300c0340c1005aa04000c5183d0b20009843e6181240056058410a00c0b1080d415100d40050100602000d0003030300c40550300700808900d0048803080130b841041d95000100d0700d80380c0510010202d041d440065400e005040c081800010700c0030851800865603071410b0340e10381d61142418409401c81c2d450162440c000c210700850704040100b04907040c0c0310306808a9100546d500011001c038460b076604800240c00030302894100c2407051030042c021707003250341e0400d0800c103659140340c1d45684400e604885140c0e07aa81410303000d940000b4440d034030454803000362029140404414280f0440200020304004000400c1541c8400301064145201e0018116007208505403010080306101c80c03009440c51200d120024400a10442c401010f89515603149170100b46960344103421504054812a8419155030011400300c40e03038850011010303080001421100740324107010f400c41c1c01c00302c20745000e141c0c16102000e40740c8030b12070140711242e505030513242d0303c0d81c8956509141d03c04c60560080507000004010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 94062392 1250 94061142 94061173
    0x504050a050607050406050405091008060901021233030f010e06090f06070207031106070206030403230405061204140d0804060b0a03030f08070e061c0e031201030f05070503 76
    0x3900503119004a0315180c0742d010003070b600da004912699000480402060200d420900300607074111001ea84100105529448114180f0358120784154541e036011035a48165511060383c55080241d20031524504280218000a0804603e405644411f01d091080c1c41c5620704000b0304001c00580c1000300500c0003900305180d1103400a03116818275100300c00982ca800740012404500500c2660002c040da10b15541d520301c4108107150105622050922401000da02c7c1c00307004501c1548269201c8201000703503407000023006c4800305180500740040c0810b01098485200326105801400501c241950715403912241c074920324010515280500d400b10440140c00c070142c0b6024a00c9504188a041d14250174840702090a00c000790014421010302d5281c14001c40d07206402900310301d491183d0300d8039640421000d9200994010b16078180d4001e000d1816540e01c00c1034280d41e6444042c0d0700c0c04294045a10481006000190030091104030b52010000d04118400041101030b0a48140b106401d42c1e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 94063642 1250 94062392 94062403
    0x50618010f0303140a0806090c0d0c0302030603100902010801061d04060b07140d081b090307080d1b0c09020f160308010303260103060b0a0305030d05012903040204050613050405 78
    0x1207001c50071001d48248132204c0081a24411344445e540c2c150710b5501c000410050b408083e01d16590068100720b452808041e50051040b200d442d614090b9403420254241031030b0483d005039440c142482c0120260041c3e0344141c1c0241169854900b05603000c815114500080d142e2a80e00342c0e000349000c2c2c0c0012550000c0d00504201d901a0700001420046030440c551a074400800c980e0000e1082d0002a0307400070800707011000070361030141c45414441c000c00860300e020007a0f0040d1079658010304440341e0311580540104034100c035001c59000d0342d5074545d582c924190719501444034055008907602c800c40b0307901402d80e4442c4217511855200d0300791900700078200308030a0006400150304a0021000882e0483c0860251413124a000845a10f103846500051001082c0740f40d1000c0d43c00d0b0b00001240041000d050165020440000c85504d46481500c2a0305061241d0172803d00324141e00c040e41130b040080d250300c00e80641d000f080c7c50395080005035000303241414064209151800340010301a002a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 94064748 1106 94063642 94063649
    0x212130306051e07030b01051903020f07030c0519080d0c0216030302031809070c0602180607050c0a0b1305040902120102071202190f06050618010f 65
    0x110719055070030980307484150705565a905006000c0805445801500c903040c104440d40700100083d04500400761090300d050b040e450517010540c0603030100e61061441c00c8610756600c025250141c0038070b0369400207465031302c5030440c044006603040c0d9000d1611508031984c181040417810380d4074090254500c076a41180584842010741005c65182040a5882a0003550f211910359610182c80d050041c0b455120300001814011000d030020300003404a6041b41c000350350b0340c146030100c004642d10f100358680c00040c0001c000052000114203c00340a400300d07004a03195640713024411b20790144008803926442c4109041000c0d1a16a004144061000e0961882030500c65640340c00ca8000803016900c41846561100c1c5099061246104080d0401c040c1c00d0b4648070b540b1a203000e00e041c002c000745450b2381c400110342c0c00e5681c0c04d40c042d01c04400c0d0700c06003a81e60b1206064901e51a0610 = true := by decide +kernel

theorem cover : BRFrame.Cov 93884892 94064748 := by
  have h0 := BRFrame.cov_init 93884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 93884892 ≤ n) (h2 : n < 94064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
