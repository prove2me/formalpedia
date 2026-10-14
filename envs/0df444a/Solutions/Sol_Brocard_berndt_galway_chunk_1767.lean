-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1767
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:36:15.943648+00:00
-- url     : https://prove2.me/submissions/f58427cd-e69a-4c53-abc7-61f5e4cd5a4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 317625899 ≤ n < 317805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 317627149 1250 317625899 317625901
    0x1207110f03030601020f0318040b0a1a040e010b12040b0702190f0507080d0203070204110d15050306070c0b01090b010908060708010603110c0d08070e1309020301050702030c06010e0618 81
    0x403105a481d0300846400e4010302584480c2541d90304000241d0313005c40d0031070b1200340104000f10144030040402200503075011800c640c0014407414202641e000c100c04480199583c0d609080140800c1501030f400340710a02c60410040e4a6241441c220030b4001e03601c4905a81140c9035460200d140c0310043d640400741c115030b0b8103440e0400c6078030104403840510034001d035800300350780f12641c0c1d4035006011381c401d0140c0c20800c10607005183c158000001c9620300b8206504102e0788501c51022034020304e401e007194007034042d818451480c0030030515501070442d03d0044c2c11100e40303588002085030103110b400480d940301c050020140c1c1c00f881901c805000c44000321a020b252426000380002d100380301d020701007031414400201c0e149090b011140b01c289e0f200010100102001c00c2140e480b40000c0842d130400c040001c058070542c0d211090311403002000c09000c108440a801010300b11980070344034209646c81048008544400424002e04551381010700442c030b583d96601090314907a0079003e445000403400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 317628399 1250 317627149 317627173
    0x212011a0306011401090303050a030216060b181308070c03210306050a030309140a170d02010b0913140a0501021611040603031407081b0303071b08120711 68
    0x224800c00041411000c581140e607030746601c40000c0603058100d9000884440c014000300707004130018200c070b10031864010715180c805a5034010500c000c120449219031994100100c9180034034102c010100101d002110a0070071001e20010342c0c0b0140f000911445010071004140312a20200e00c0040d50051652000c41c1150001c400803034003114002c1000c01c1c83c0020102d5079061020390a010740c0c4c0d042e200c45c010b1505002d605c5501088402403142d001c0100500400d0300c107085003418006000c00740041c07800c41120300c0b0181c2582c005000d080d0044031000100b00c20544607603000981250000c440d60702700310411450a040c02c82090b0094629800001c1105d400c0e201d480e800030044c0e004842d01405400f0007020401610038a00c006030000d880c48100540c14036070103000f841e81d90b200307250f02850300a013542d01901104040030b01e01ea1541010080094075a001681d9806208041201c985100025907803454a4019012031898008410f80041c070410300603507401400c4481c80040b14107690101d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 317629649 1250 317628399 317628431
    0xa020303030a0506090f0105060d022206050d0c14190c06021602130e0a0210020313030503030a0e1f0b121504032a170f1903110304110d021201 63
    0xc4d50098010007800b0300192410081d92980d03410b943c80103010034608014480309002a41009006041c1c2c4c04015104450b802c04030702411006080716100c40d625101150140b808480c25600e1701c0d400e01600c1b03d24020b03503110b00300440c0c0440645d000040940c00c1d101c00112030310129008004e081c11310025299111500c200107550005108a030400c0c0e020070001814005c0d102020901a002d2740240b00d0070b03005280070074020700104024030449040c56800c1d0400035890b40302d503100ba9240d41000042c0220300c0702a020708103509207000000d000c4a05032a0f444103000030a00c2d07081340204d580c0d070f100d0409595000281c02000c2c801c03000303d82c1c9444c60000103606018050b581100800c0348030349055081c0310b8503510078840e03038944500301000309219115250201d4403860442040c52081041341410107004010f003003a00018404141d1000203510060101c461040c943d0061034001d008110008a00014000364403109032002c000111062010030300181c0d00c6a41440c3e00e50078035a90101c84065 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 317630899 1250 317629649 317629651
    0xb10080307080c0c0a231f08041106070807031107051005030a0507110a06020d091a1e0c04060509010201060506031306060b070809060f040e01170d1d010c0201020a020303030a05 78
    0xd03074050700d81d0304c0d00180130003800001a1041d10281d01d0f0f190065000101034181031140e0a00c043c1c81c48a00d82003111303d411141d031034814203002082881080c04103212041020310448002510014580000d62b08c50300814010703001c0050070010000070003100c004051058400800f40031b403880300c6084c8070319004bc000d40c0044484c100441d19280000701418414840c5206401d2104041c1c50340c03816a0701d03100080c0d4450001168020b450f914428005403548408101c428400c50142c5443d08000540d0070b03100c5c0103c50710903001480c18040c0000e131194002101e04603001801e05641d40d10203140140d0241286500c0b09910120200400108001401c0ca50b981140b1030b010422107a03440d080d40b103034540100040644480c0c030a0100b007405040070310080041d81e0344c0709500c134100740d5614441e1a150b0026080b40700c1a64a04082d0030700000700b000302030b00300701050410f403510003500c8064810740c00e4803001540c10040030420040940e40280600041c1c05c0c3c0140640e6503a1504504580107024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 317632149 1250 317630899 317630917
    0x1d0307141f231623040b0406090b092d12010b01020d031107030f120c05040518160f030e01020c0f12160605150607050d0e0301180b1008030708 63
    0x5a01c0c2101800440c1d071a0707900d031050f440040c0f448503000354110120307150020360310303c1c200c0c1418180b11807045045030130240c4014824110039035961810944014858812680315099268060244502a555400009060700d03404024140d040034100700c00052000308000046c0c00c460f4002d00040b07000f506400040041030282c0840701c140c0c18107038049048032000c00c0e4071b03141030106011000000f0322906c0c081c2d0800c026444d141c00d140c007907501201c045449132511000880c800090030451401c2030500391000d55a0400040410f01c0d04400b00381c0c0c0c2260f95114401000583e5403981c08440c0203911060798244410021915a1030421055681c0e00300f10211300300d9031081d1260f001120000004a40ea2115040300c0c003848020390342e54080107448090f00369082c03d424600d0340341560b10340c0c0003c1c6c0700c002c0c010b10041c600c2c0d118868002d440b90000c8101c560203641030000c440050150342e607560740300c10350005000b84583c1d20710700c1001c1c105240390840310513400001503205c1480b0082d009028a45 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 317633399 1250 317632149 317632181
    0x31b040b0c071703040e0f06040b13090309060309110409080c0a0501051017071203030f0212040c0504180b13020a030b0103060507050a1422090e011d0307141f 70
    0x9600c95555a240220311600d034071b07610080001002c92020300c038150340203000a031002c03585401c0c3c00c000841a0700c04105240038565aa5059020f05a210b4040001000c641c01c08000240302500d9071f9900180b4529450300845e2200301290410800d9401c1710311140c1070106035403002c056860982d010740350070f6030121003c80c40c03250b000c5071141c0c0b0301e94004d2005182c04000d02c00b0302c2c0f030609400f5400100000030f40c240f5980303014682c14100c1c3c1e80001c1c00c51000b01541100546081e01d04000f00c0304a54010340d019a10b080702141603164a04d00b1070301600e400096020040e034030b150f501c00c4200303c2c441c03000390015200382c400010014000c01030350680c0d2181d00c00f84a1a6070700d0318121403071f006d502d2201d0001ba40201c4050941003111004001420741c0f00c1c1e034004182038080b000c000d05100360b0303c10501555104417042e4801e400b80320380952446001c4043c0da000ca1601c00c3c007903036409000d40190205c2000084042080c00820101510f071401c1008e0365a0f003569901990018044c1d244409460 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 317634649 1250 317633399 317633429
    0xb1311040e01080105061f020f07060e010807020f030904021b01090c0e090606011403062701090c050c031e12040b15010f080106030e01021b0a110a0b031b040b0c07 72
    0x2c8081170180602c070704800ba00c40c090403041800c040d10120114100c9000703501031000c414042d11010f2000102a00160316400d9171000610b0004000d09802400c0000b1034101004800201300c0c08002c40e04075800449026803200d1004010f082c1110480d0a0202d4541c6043e000c00100030028002504480b498566080182d441c820000e4541c072040b0340060001d40340200c5040304640d844040e40d00020042d11040010700b840202030748284003034800b898070702a07078401041001e080340100642400340b4a0002c0c2040880100309a5074080e15072040d0300c05010b01807203880c1c10800c03000d550094045040d02400790415060510300d080d004e1b51500000b101c0d80700c0085c81e5500406034001c080d40c403a80c4500c0701381c0c0380c942c08400900d0011604030848d5002c0040580d4029800248031020b86440040c0c85061100d01e0300c3c010021205140c0c5d80107122509c8204110240c50094a40c44100c00720708407608203021400c1c0d86284100c0d04400c0007010003241142c20040002481015a501d00c191010f00d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 317635899 1250 317634649 317634659
    0x80912031b0d0815010f0c061401140102010e030d020c0f03070c0e060402031603050c372c030a060c0e040501210807021c15110301060903060b1311040e01 68
    0x7000c0c00440d40340f00300204e516080c42c0654800c00e65100d0a021130b1811220a4140d03503594000d80341111080840748080b00014881e03c1c54a00c3e0b0390322901d40034002004441c0507028415101d004444190507036036400301d11001c0403001400307440e440380380c0b071001c0eaa43c1d1500c40c580b022030403c0a004901400031110001461410f141c400c40e405070842d45907001156042e42c000b18041d000040100e0040001842010b20f110407064a480d42080084000780c1074900c440a011800020724140340d0070081107407850b41155450184a404560700415000f5861081c040400d2070800800d0380101f00900e0954041d06070340d4000d1403402400d000322810b10059a0342d000d400301111100315002c000181b41040c10b800102207000030440d40348041c20ba007480560300865103020b60a4030380152076000c1d03040003040b03203903405100341c803944485c000c240c606550400c0d80052a540b02d5000040c070b03a95071404150500e0b9240c08000c440381c0aa403005101e0007487c110b01e070b44a030b041442000c066926038000496 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 317637149 1250 317635899 317635907
    0xb0a0e0627160309030c120e03030f0a1403010e060d0302070305031c0f14060621040803060109093b0a1506050a030f1211060412111603080912031b0d 66
    0x4c81601950f4219900485807200c00c1440d803101051404c0c40a0822504c0081d14107002411340718400e403094a40751000079201811040e40307080e81d40e000600400c0144031034030142c181290004001e0b540210a01c021380f40070303850980a50406840b902c40070403a0442c44c08269418000810301d0305080c0010580c0d10301c5082a100c07000e5950008100010000b80342e03083c603901401c08041c581c0032a40051118003643c9a0b5524190740c141d4142c0000400c00506580001001005100c00242003141040072014034003d003005020178400036401c42c5202000a5215090844032509102544c4102c0b503503141100310b04c0da0041c0c1c40b40c0890300f0000b00140307900e81074820108694105025115100b120782e00c03260089007080420090046692540c003000000b041040c1c41507100314906181604011805000009410100e400710340c0701040d5428415074041d50301044a40c08059240c69a5003a000200c080080310040145440f01280074032019111001d044820140002928803541101000326 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 317638399 1250 317637149 317637161
    0xa18080106060e03032d13030501060e0f07080a020901050d1b0801090e030d0c0c0c03260301061209021c06061406040605041e030b01120309090b0a0e06271603 70
    0x46c100c005143c05007202c203080d018040c080319424403805180c02140038484040c0911500295600d039558030043c0144051130600e5508840e000d17880d00c40524005000801003800248010399064002c980040036901400a0b119900e40e2410305003c0d44030f00400c16000d1443c082c0c0c100c2e0006010900010b090b041c2441751010701405400610300d05019041403201270500070a07003c0402c00016806004903130002c00703200281d4450340c3d9045a04140c4400f91042c951081c140801c070820807c010008140c101030602c3e03420001d600e0101c0c120506000050704c0039040f094100c0c415402e805142e08122881d4410800d5a100301031105412200b441401454000ca001c0d90010031410081441440070404034a039504100b04000c01d0f103d0b4403507441515006d000e9004200f45c05881c000c038010560003440c1c0308040c0070140810060b1001c1003002500c1c025541c030544002c840f0354004140d150b1180203003c840c00f500c5843c41055202c1c10b202d540030101e002ca622541c031084201d01c03092080d2080c003623f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 317639649 1250 317638399 317638417
    0x160605070b1b1c1a0f3610030302120901120f0912050a020f0c06160507090f02040503011a090a0e0f0a0f02090106051306050a2c010311030103020d0303020a18080106060e0303 77
    0x580a020510035022040d0020900348011b0740c0d60300046001c120b11a042c1540b05949440d0100c01d031b01d00e1032402a140024a01400c0b103406070a1151000d9668003c1c400718880b0881940400c4001a1000380d00013404139000142260700410445114103402c44010808a01790303031b00301c90101c030fa004c800702d0300d5000b41146940d10005c20400c03402d0140720045143c0825000340c058408455884403914100d91f5825001819a500440e041040745002e10801090340300c0741c500c4454241d6414002070051000500700d0600d5583c4012940b07259070308125840b00035a0301c0e02294244a09810a00d1001080240481c8549828400455440d1140058448030081554134051403418004c099030181c100e401c1003800c000e40e0100d0806031414010800c800800c8a060016056581800040940d5441c2a100d00c01a80410041006032a41e010240d07489406240050705c0e040d040c4011101400c907410800085102c008d03000c201241c065014504954247d1207502601d02000c0034161280200201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 317640899 1250 317639649 317639659
    0x405061806040503160c0905070206011d06030c10030902041a0301050c07050307080d0b06071a010f03260403080309060108010f09050d032c160605070b1b1c1a0f 71
    0x10300d500c05045174001c007049100d95941010746440782402002c440c82194800d0060340f18000400079880c803040d160000500d0303c0180d44c1c0070715048010980e03d000e103250341d0f8000e40c0300d107012290051180e4002403102da80104203000190844005500c60301d80c601c5880d209510701008a841a50150111108141d024001e181081429101c00090750045000031300060b45a41600d001b5640390801082d02c584203210f00032211080081114817100140c015a02d08048842c040c80030446d401400c51400340310131252100c0202c3c844a170b80300f03070003194401042c0010110910070808004a4841e0585043d07100800450540c2e10803001685d2010303801a013190020418800460301c0381d0011340340d0329220740008120034a0510703d10a030001f2044c04c00c05a411071040e4045140e90080c000000b00108d2600504108264039202d441100c040c00c9008440548405d100581c2c008105490300300303440341c0e06520a08641480c40020b82a4218031508000303118510704035919181c04e840c004000c014007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 317642149 1250 317640899 317640907
    0x1120c080a06061e080a0204180f0507020c01090902030c0c01050c0c0c0604030b01030b07030618060f15090e2a040302090a1517100203040c03030908070e0f1e0405061806040503 78
    0x4415207172840050301d410f070f00035000c100108520880c40030242c0c15000714913000440c2801d110000041301d07406031149007150061103002c40581e0b40541800309481268a0050707483d100c0c9683c0350600c0c032070306003138412a5081108000850300140c2c0545088041c03042500d04a035804030801c070b16403150b0f000080000280b940140045010450450303404296400d0000340540ca503103c0d48270314410a07149071041500c400b014002c40541c5440c0c035000f841440d858805e4452009030141c26076116000361400f516000e4006100c0790002e0030344544d0403800d0100e482e0840003100000300f41d98828042030f801380400d8404215052400d110320840108641e5602a01904180c03078140c07a1802c0d912608590700c00c00a0019101802e80700a5024602c1044600201441e525000d4403617a15030b4400b01003604041c40070002c01c030048000c994400801c80542c1c44980d10441c601c0205104500000c007030080c0302d41007100f046000036015005018603202036170136542d08a04c10f41d499504031002030064000780 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 317643399 1250 317642149 317642207
    0x14090607060c0224060f0307080c0d0203070b0d020307090b0a020a06050901020708120a0c1403011202011403070f0201050105120a170405030a030c020405070c020d030e01120c080a0606 81
    0x160101d00c0300da14520594071160440310013500031050300b585a814018442c403c0c8112450900074040000d00300b035000d80703003c914001038107071122045404140075150b1610040212341d07090080001a10315099043e0b201c01404e41e084000f0740049400c0c00119520304000305582500700705595001d52164002c2041d03e22941e5181d024000c060f00300d0f1169074003804800009003401016191810039500c16482c10b183c2084024280c4480071070301800d101044412120240d1a60100d13419503041d0304401000e01400d00c0104c485102d20742070700b802c41d6030200a200c2c01d5640015400140c03180d6600034407040c0d03221801c01c0108151440b150704580c2c415131610780000d0400c0ca04149440544d41440d0030650340d000424107007200700030b081b40010b489500100440c40e06220315030700040e061030300b81c1d81001c40e40d0100d040e804c40e1346000340904c20704c1a0000d42c10380c4604548aa8018510341c14440c03e21a00320150250700251085070390039061010104130184100c500083c2c46116442400740c0840700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 317644649 1250 317643399 317643401
    0x503061912060e0712060b1009030f0807080418020910140a030506060403080417060c13030206090f0310090c0b030f0c07031206260f0c010327121409060706 69
    0x21810b00f02c00da0003480740c005500e03500d0441c40e00302d0900408010445070b0a83c420820303030342080700b01d80c01031180b081d6003071011400340e0000102e101d0340191125070f203940500780083c043c000e59000780350144d1404000110712100b600035000303810f8160784518041e03282d141d041d21840003840e00804090300034000141a03a1103a0481030b08280d0150030300d81f070552251100f820681c820b4100e01d004520b42d00d4a480c0409042100360360008038509114203040c505082d0420003500d5200c045d10450380414520f180d80d84841c0700e10903201005044808264890113028040d043c51102501d140000140008400c00308404591140c030a0b01840c0302d844c2e446540040803a0440740064040100c0401070280290345403045030040e1846001070100b00103e800100709021000f0303c9000c140d00300c08251500b00400085005c80d100007402e01042c20f108100c048081c01c20541c00d150f0b6041ca285008409000740c00c1c0c040940b01d40156604c2c0603a590381810150a441283c4400780c0040d001c200f10301c086281 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 317645899 1250 317644649 317644661
    0x23109120e0a120b040c2117090406030605160c0b040215070f030e09010518010509190204090b1c1205070c0806090601090e07050d06020f0403080406050306191206 72
    0x1418003640315180c1c0d40d4400703c00401201101d10341004c0d0300748400c1c080c28602000040c101c000a0388803100e03202100c40d5914101103001440c14212a4080c0203540004068034815000604204a400d5590400b00003a0106850141c0c982144003080324615100307580d810081034000780d60580a8a039030342800700c15010002080d6030300d101800f034000001d030b09851001c10f00e0b00907961a04440d18041c200a04244182d003c0e5201b080c2500480d000101ca0720354103411145c040307501c807110b617603840c018401c0e506083c1214510180f0000e00410122141c5e0702c80d0f03910500c2600c1308600040000c11688042410352400b90010400700a00e61405211304010040c56100e009200e074807035a200444d51802405a452482c903800200041c00030040ca44500352507002218003c120341d51030b0034045080e07598840c40192480740c00103800c41040c0c3c00d003000c5070300465024210555403540d5010040c15a002501c2d2248100c840d007554810001c2902e00110a40301c0c0c1100b41040001242ea5050003015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 317647149 1250 317645899 317645927
    0xc11100201090512040905060603011211240d0c0503010803030c0c0a020a09050403111209040b03010612050303150910050103090f140d08010b12070c0302010902310912 74
    0x2482e4007901c00065414440b41c2c4c450030f80a80500c0e110b5051041d070300203840c0b0052260f40124824001005144400480344607030300c1d00440c907008082c2c0c41001041401140c040c59071000310f043c400301c500d014601002000c902c2d200080030001410181000c0f08d01e8402031107005808e42c81840807400340d40490000382001c4030140c0031a01000c526a000c0386181c0c05550082c8603050780e400c204801c1c15006150804801d82610142c2003a1100f110140900c0c045c40300d095000c0c0340c3c0c41c05108400e440235800b00b00604003c40f06c0c001080054a08280c1d05d50040b28424072034080c643e2810060305200390140c3c01450026040301c0e5190074800114000d2100c7c80d000d5944101e118032405c0401e130f2203012650341507440d1020b0001428003c0d0003820040040e03100d0303040054100651601810020034035504806946041c000f01c4c422400c04a02500c6c503504040d41c040242c1e02d4000b540d403d8500700501c4501d0646d80c000f2500880082c200c102c4a41400191040000308039021519208041182c4640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 317648399 1250 317647149 317647151
    0x10f03060f05100b03100317030603010b0f30010509071503060602030906093c011706060c070e0a0c11060601090308130e04050102090103050f0403050418020c0f0a0c05010c11100201 80
    0x240c0d588c0c840403061120140c120101010000c14000700f42401c0c0502d050800e41990036124800350a8007180c0301c1c0080a4224642e085120142c507616203e810200310460b160074000d2103682402003100d61107000740d1140c0c541c03109204003031112443c02401008104ca10710340285003041d401105121091b0701a0b0000c2e81e0140100001450003a148c90b40701803019404854a1407001042e901d0b41031030350443c80703490705025180c4000300e007214440940300d5110b1010344903203880e00c400011003864009550464041032604d0401c01c42d00300b6190b03000001101c4941d66004207100c2c103951441e00c0c1e0400b950f415000800a11050003c5000c170b0008107800b418080e0740b2800180d40b02103032400f000d82a10111031994000603210070540c3d041c010542c018404014940d2141042e03980602107101e203104680b00c80d04200d508003402503061307055800c0c43d2000320980710707130002c0300b2040d5498418030034003281d02d10020200801c0c25442922025409a0301001641c40f140150040113910140020000115 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 317649649 1250 317648399 317648431
    0x307090506070b0702300904090b070e01080604021801110f011e0605091003060c020a020904030c060e0610140d0602040e0a06120803070503100e010f03060f05100b03 73
    0x9450318070007400c107280100c0a0a80320305000e00c00070305101e03844241d41c2018004101c03641c00d00303c0f07114003002850100d481080d603a148401c007240103403184800c00380006c010402001006904810030340d034500c500360780f0000c03941c2d11603041001302e020300c3c0340b080c554030b6402d2260f17200d550203100310200342280c240450359001101d80d90309081d07a034002d5152045002d60b00d0801c800304528010000500012aa4a0b40503d4074180700d00300704960f40b0018180c15191030f03008050038000d001030040e8503000f500140036440c042c00c0c0500103c010b40c004503415454032103181c14400c0007080b841d000d00100034000c00e82500d803242d440748000300ca030041c540c0020003080b0000060070902c0240020003100b0071340325191404100c03101c2241c030203522031120008801d4407400024080c0c0114ad62105403410000e44a44401d030001e003c03001d0540200c61041031072070012518204031031044007120300c1040c0500549104e050014103071081680d1000303210203162828810702c048400616806030104141c0320030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 317650899 1250 317649649 317649659
    0x4030905130e070902040b16140102040f030203060f07080c0a05041d04020a2301050706020d05091c030603050705010f14030a06030b0705120a020c0f0f010b120706080408030709 78
    0x1959241d826078140300d80e950307500c0040b00d52080c0012001030a090000f141004d150680540182c441c0000c001c0500351550358000070001045489c1c0340089201c1c000b19100c0c0e480b613142c01c0900c420340c00181d100e40300b04800500244420242180f250b86661303900c0c16141c6804103908216008901c115060010502020404030003201180d080505028440b8802c0d040c6401481a02651500640008540f007132a09800c481c002895007558242843c2071030340e030f042504080c4020300440c0406800b07107042c0800e100c0c40c140002890f008c425424480c00e000f01c07160303c600f074045980b05d00c40203000f600f20100c02c00103580514000c0004100d5070401c0b10349807280e9100001e030b95208968400a0b1a030302c80003403040c031070640a036540c00086820154684000c1c0a0402d80c000402040100b00075000a02500ca40324140400250f4099050485031403602540a182c041c11711000f440e406082110006168940009101001c4600545520b40592074603122a4000d82c40140310905100b520000050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 317652149 1250 317650899 317650909
    0x70c03030302031e160809061e13060f05042f0609010c140d0210111602010e100804051002190302031b030c0307030c05310f2c100e04030905 62
    0x4030400b02d11a0345c00003c0791500001c0e190f9403018102d190903600513002c120b68074241661030080944c40c1701446103a551845640007009229980007005c050130140d80e40203050302a00032500461003014400c02040c200701404c10203074003540301c2d000d101031030654800517030070180010a1030301018500b91105028a07280c0d00c0c81100c644a04070300c1075000c01c8890328034030360600081c84800c1c1c3e0054244400e00d0b1145c401c03011030042480d01c541d0301c3e40c03020101c02168003a00f1034100100c03010f89417041545100c10003034a8004111000d0714a40158500c8102080300307071088440d44a950cc46110101010820440c001d420081c6402e0740443c104112400a410000c043c0d0b2140c00440d00540d500d240c58040281915501e951030024840284004160b1704007c0c83c41491101e14107400d0310704400001c07501c003034404280e4003000f03500380c0c0c4020104d03400c1c415085c0401d1004040d2000000d09050070103c0990b2407040b201c0c1411560349a8050140e2840240c01d030341c1181c00b80c60000b64407915840010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 317653399 1250 317652149 317652151
    0x3010603051e01051e31020414060901030f0503070c030809030f06010503190302030d060801020a1d090a090201030b0405070504050423010e06060712090911070c03030302031e 77
    0x303280703036000350411040c0074504071000194000b035500030710503070410034611464001d0000301c011500d40c10400190003180b080c00c1c8500c0f4404000b20003240034000807070102007010781c54400e038000c5040034907465100e40d42150f014040c1c000a80140226031840e1103c1401001b100780843e0300f8081004220080b494005100700503500030541280e803140c0f0704042629107501452244117640118004004a90300403030041445246070720040380c0103000d894200e0039842b4243c5641002441c0500101e180507056025002c120581e4035001c001089034019040c586800c2091158400c9a040019074507904580286075032510605011a003450b054001a0070780314116402000140049010080d40c0340c14020400701c0c040c10303600b00403142c0f02c0d2820b80802c044140a024100d14025022130550385851080300c945580186000d42c900b601540c00420780d0901d407003188202400d10b00007200214500d0200c800346a8001030002d8154510382e4141c0294000030400101e031000500b40ea0815440800d980d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 317654649 1250 317653399 317653403
    0xf2232060103060c030f050601090510030f0e0d09080f1c0c0209041103070b040b0d02070f1505240303220f0801051e0f01060804020307030204020d020309060a110703080c040503010603 81
    0x3044054861100900306c6420040d031030341a5080100780196640c100030390310140c4100345c5620029600038035007138010300160304104030781500d4803403240304406000c03942005ca05820798807808103130f07507402010340d40d62941a040c0d080341d040059510142004410495100d00c020309002e514603620340c0001b450684d0464040d1040c003200c0c0d00508142c40c0c18800640039201868500d03050070b0810300086454040c1460220702142d00068100c144607420310645107941c0d0204401c62030382400d080800c0a41026034500c00c800d510b4003200701e421600260300071600b0001034000c6040241460000c0c842d1000290f00c860a0440c0c03c8001c18000c0180082c01d01034a984400447c2a0a26103200300166038044042104841450144440d020962080d41d044404600d0006407030340b070354000282440c0e803e82c4000c1d0b106100094000051507190040c600c80d0a055050360801e940d400c002005684070b601f9074a621807420865840002e0103040d101c0e0304004c56008240c1419160000f0908451684d002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 317655899 1250 317654649 317654651
    0xf0604061d040c0f0605040303081503070303020a03030f14280203090f06150a03080c030f13050102250b0a02010204030f0c15050702030a11010c02090f223206010306 73
    0x4200503c407644028030001c00b650313410351200ca880e05500900c0783c0910b0000400b003104900c003084aa0080340c0202e07611100050540d00d01940d20700e00030f569a44011404c80c00700303080c4002c041c44a410741c13240724060004003440c03441c04d50700c103540301802022480c1c1c10b408595000701887d920740700910280d8414000080140402002181c0c1a882c10744028000d40740151502101c0c52581c5500c11604101c9920000040c0c903101d0b682d2400e4214000c0e0800350456002c0800c0b001581421500314104036842170b02510341101000381721011420029522800c4c00c44104c90030013040d600344005000020540c400107061a449940d64102d038550140161011035030b001080c04581e0903040314416030350843c10800c0c80c01d4260707404607403506040d841c040c240040d80c00b902e400e180d0203840c3c900001940103002001300d241c6510a4503100b10203881d0042c00406000040c61940c40424440c2541500728070070350b010354081c14040315000c20004807160381062200b51204000340800800340078605c2084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 317657149 1250 317655899 317655901
    0x10c05030c06070f09140604030311070b0a031a03210c120d0603030206061f08070e061b010c1119020a1a03010806100302011e030b03030414090a06030b0f0604061d 72
    0x1000f007030300034186c024000340c450b0544020880c0ea43c150445013220b034141040c9040e846428800c1d414099181e02c1014040c000240103a00f503070380b591006810301904c0030308101d04140321040c141ea507200b03c4146000503443c1c03003405503100380040140040f05094402c5500154110005802d140c008843c3c0400203901d5403018010541c06110095020340c00b6583c07501c040e02d188014508941f0001902000d0000000c0030402e4544038200c00c10400001400b80c9541d0224145e81c05030740040c090207035883e5441d149410b8682c2c0e2280b41504070280340c040080022801950781c1301e50040c42c5d400c04986c052042d840004d86420724039040382c181c0d034401180944030340c505040c203810028000c0486400c0d0403c980e0078030041c1c2c0c12071146031264004000102d0b03c0d001460056005000020070a40d040c80042030000b50320203801c40e40c400d41c0000b512107428980303801007401c040e180107020090114540c080021509a48140360662000c0d0003030010074896918034001003805c4c800e800b4400c20100d054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 317658399 1250 317657149 317657177
    0x8090a030308160e1f09090e0d170705120c04090e0f010b150d020c0a051c090b0f03070c1a011202120a0308070302070606050303130f0807030b06010c05030c0607 71
    0x209055071501181131140c182a0480c4c0092007410542c544c1140d40001c1842024100d4404c5070320801400c0e0001c2e041103031008941045aa848650000000180d00f40501d000764508100320036014554a440d4641030500c0d6040c411110040101455140703402400300142c507001500400308050070078000361107800c03100314085095607464080740c3c0c0950405040c020320741703840c6000c854400d40a142d0050300c03004030b119441e0801895100140c218440e02040d0020b40761009403070741001d005502d036110010f41c2d40f10100c049000e03003070a02d8800c20052001940aa00500705035803805d102e04424442e880c00848100d00341305d000e030040c03200c8800004600086040000500700c4d038400e208020800c0c0504c035034008080007002041c54040580100c0c0c00c104000080e0000c0014280040580c0e03241d140c025929090f40e1380340d12074002c4001064800040c424030100302182a01d070032601905190f5100c100564607400200e10440d03603448108600c00d06039001b07002250245040380c1c0e8580d02c0000d10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 317659649 1250 317658399 317658421
    0xc01110f012c03030c25140706090915030305032e06080a090c140f13020a0306060f020709021c051e07030b09040f020a030b0a0501050a0b07030206070c08090a030308 73
    0x20b0001005654000c00500002c0b030450000e4450030718044880d000185100c00c1c01440b1181c280748014079412245104108150012444909039400b603a1560503050380c400c105000e841620340c51007024000e003002031001c2442000115030004030360507481044407150300d0b01114480e07145010310a404400c441805150361004507e900305544e008140041c00c2203403910741d0495903a01c01d501c07a803d01029480c5a9440307003c00080781c0400205030201c3d403180034142e00041c0d40a465031800192400001291041c002c64036140703071802e50307402440054188081c0308002e5125003014525410410f42d84291303610b607800303001c0c85844140e00149210f180358100491805001d03000d00e0a050401107504613a480720f500c1d0603481500030320060070f1101c0500114400004030341000d40320296040822019001d1a00501d0485000380c540d40c02d9569902c5003003440d8000c80da4000e006802880c080384c0d01c14881d21000381e065004e504210700d0640d00f4000103810080c40c1c1d0040380820308040c10040e0710000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 317660899 1250 317659649 317659721
    0x2070305060609011d100816050918120a030902060a1e1e050f0906031014150d0518070f090e0303040206041e08061e10080c01110f01 59
    0x401c0d50340f8074495040400701441e0b5602c40d4490030b041307200d640014118030550400340d40240300301c03070541d05151503c120882d200c440c070740a03023070041d00c4100c040b400c4070101d03c02500c041c07002c102c0541041e2480005141c07041e4403e403641030400d034980210344050303558000100307001c010741c0d03c404c0040381841051012000440d0307085818041c81c800140100b10f001000103036440300502e05655556501c00485081e8050b1501294101402000f0424000034960380601528407552441c0d40c40301090082090709950481004c4440f8401d001c031402c4125160401c6400c51040030341d0450319000168164030381a95940302e04030341007006004015840345403085600080c100c0015500e180b400b500802ca5901c200d1040e2070610007420b82c5244202c1c0300600034070280944405888040c2084183c6000c142c0c3c01d091011000d0801d5001305500010640c03514049840b84d4028006181c01a00159021004800c11007802d0082451388151000280700d88640c60350400c42021001825409080303507425 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 317662149 1250 317660899 317660911
    0x3130f02310b011202070f140102120903091c03200105100807030b01150c0b010b0315011d011202071b1406042108090405040f021201180f081201060207030506 70
    0xc500100e02d60240da21000d0a40c1c2402029005a0341d20041d15044131417204061000d810034845445a901000064000307184a41c0b004031041c81c5901c1b0004030b180c491040b120940e90058140c81e20882105039a41150043c1d070281c2800c0c103080100c0454030905455903401d500713299540303000f00f02c41000e00a240c0300280480e0002014481d09540e2001c07480312040c02400480b0b507032000400000d81c85408030004403907002841c400103581d10b00340c0d2843c50300140c814460028034025032000d1075118801c4004220030302c402030707202c110785040152100041101540302080d02003000742c01107501c0e10010b084400c90303405480c00766031600d4500703c064a4152032482c4203503020081084100300070403a00c031118000c02429416040140342100140c4240302c62a5085403c280801003072002c04058030703440c00d001b0f44500100c00201010a400c03141c85101d5101e020242c0300c090408140707414460244180b040c02c025181c0307541003000040383d020903480307800181c0c071485044c41040703424421950010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 317663399 1250 317662149 317662151
    0xd050a0501120f1104110703080f06090411221410050102061b090a0e04060b040b0f0604090902130e061008031207030b0307090222170303130f0231 65
    0xc4403c0e82c5800811000d02030183c9000c020044580440e0343d00c2c1c0c04040c80d0788800d1501d40c0e0f109114036000c0c002003400c50305100740481040000300c8a003002c03046c181c8107560040910b46c004217913108102001c601c51300d1f021080700019182071071451030792240b070b4000c00d003110410801e03103040018034180706880e81281d0b045410040c28021085020001c00d1418880f524903207032117a515001180418a40398803403000808500203000034000258030200c2d2102090b501400444413a4040c014040724502c0c0b02e80d0003500070002009100700c80e40c080b0300000e2000304a11601c803e40711455040d1498030340641c02c00d41001c0203122802030031500c43c1d0014254280614104801da0288045d030751070040510b0140364540d41d030035016980a12602c0080d06000b80d0864560341100d180d12280c003403842c4000d130300304414400400c0f090702010307000958a1120004602c0c5940300400d031019499000c0d0100c1d00d000e41708031182c0050b07076035140b001405070424512103c000840c03030b082c01c1c100b01100404e00080d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 317664649 1250 317663399 317663429
    0x2090114030c01140f0a120b011715010306150207170616110a0c0611010c0206010509070c0c03150c1b0b1b09041b0e01050a0e04090c0b0d050a0501 65
    0x1a40700442d10840c40102404c012841d080c5400002040344200504181d03d11000600c0c081095003284c4242500c01d94002c04001001503000192030402c1c007488403580c240552000034468140c02c41c1c8034280c0c200b045c5000704466645a403d13a55101c1c0c7c0144000140c1c220140c20703c4130711700c01010810f40702502002414241051200100600002d1920808001080d000700e000540100031b0411890380c8100c40c060595594031b4005d140803030001d00d00c0a1942440a1141a00c0c80090050305980000301031240c9030310b8141c005c1e01c400c42052401c0ba40307030b4403d14000001c03a0301464103265440035032070085090000c0b403138000c0c6407605c40020021014002c001002c08504040001c590045469220080007506421540c0b5079006e581c185079403150606031107115106510741d11540410345500d07168024482c140c015a02c0f030090640302cac00021001d50b604180751400d034125180e2640207140d000300186e141c100b004448d0340b1039031041400301d403204c082c0301840080d8484c3c180101042c1c03407071030b0300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 317665899 1250 317664649 317664689
    0xa110f0f06070914040c0e03100905060a1a0d0302011503110108010e090303150307270c2a02040f090b1605042111100903120e150c0a080c010207020901 67
    0x303002c00004e481c2c0101e0342c070b051942c11a0300508000a00e207400900326066042803140d804050030000100b1543d90007100301251000c1824002c180c01d03400300300f4100807004c2c050020702540f600079048c182c0456480b4510030010690051550b0042e42c0100d00e161a4817840b540054842c0e241a40540b009220034001c00001d040003109a03900004058082c02000c00c440740080c2c40c2a010f034011601c2c4901d0307071041d1001034060b441e1625000c0058502880070100100d0161a501001580020b4403d051804000380071b901d14281540340d071000700001a100380e0003c0880480c0c018600445010311a142440300a1411a034500b40d0384800e0f141062420341807500c450051600c400f001e800500f803aa601800b00884442c20310384a0502a000800b071902460300240421142d100544143d148490100c03a0310f407040340864111400a40800610026010240b45580c840c076031881403409a0403507080024480402094070201843c000750b00ea54140c01084141346040e030207000700020010301c00c54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 317667149 1250 317665899 317665919
    0x207080703020a140f10020304090e060405150403050d020a030e2b0507140a030201090201110d02030a11160603020c0c04091e0804121214070213020a110f0f060709 72
    0x65a2510f2500c01071202c0d0034001c03401709941d10b0b540d158031040300581d004009a001019004440203484140400c4000d01c0c0c950b902e07410161030162141d0450340c00184985407500100741c00502c0707854260b203481035140c003a00032600105084030029495501c400740c0c4140030046100d1000c078140600c0002101c6002107c54055004002d0040c00707004110364081c0074000342d4030842e401c10350045da0380442d25440c0090007010048400ca02080d4200d5500c04c3c5400005074507211020719400962900940080940d00d40b00702500b40040f80c810003107141003d07000800800010303c0951400368458461101480c10000000314081c092464000c5a0012a082c0340c841100c0001600808140d90a0381c1404078540c40750340c009820310743c6000585802c105054440100c01401680c428880301074040306064148100e19010350b0040c004100c0c0d01c03825215a0040080b154141400c2c0340306102003401904080558402a94a4020200042c20100d05100c0240c1c40300c098541125201d090070022a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 317668399 1250 317667149 317667169
    0xf0c010807140d090b0f0103030507080f04170703050d031104051014070b010e0f040203100f200d06050f0102030703030c0c02130506041a03030702040513061b020708070302 76
    0x5041159840100d0700040c042c00303014042209030480c0c2a9109169a450030182984620890b01203a90b100003070b40040f5078001050589500d50b542034a054a00c1e01c0b40310007500710288162010404000c000340b07103c05040d200746949914400380410f03520b513082c03190801c0d000408050616003030860880d110203c80080780d003035807030444194492400e0104111140c0e91104401085030301c00046843c180841240c9250482d50300c80c99500241e0307184682d40305103c0059a009403d0b03400b41ea060418011242c003e5040707002c1d10003001802044980c144003c0e0015940d0540121300c0000c1e1121501c48203000c2c0b040134102c1036030303043d500502603c0006d41d0792041c1640602015513030050401c0541c420143c07400c055400a001d002c0107402600ca10004140c140c5000b0b00c9680741119120000141c1c280c24007003031500034041d5041c0305407a001d0202804004240c9200d2020a11a000008401d4400e82c402540c4034450121246908040a482d0079041c0d004040f03d0352100030b04000580d0360400603 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 317669649 1250 317668399 317668423
    0x90f1b02011b03060f0e09070801020309061008070303080402270a23070203071211070306060e100b160c05270c04050d200a0e090d030e10020a021e0703030806030f 72
    0x411b50781c03102407007400e00100340c00c41c0b441c3e54000424080810000260035004958040c0300000d10350340d9540301a6101d80c03601c00200444c0300e00001070050f2511b50395814540d60108140640056411212000804c1c101c400a19040e91507445107220078900c025010361462000c0302d070b07046080400000e5900c2c0901c00b8002c00300030140d121620380511030410312003040000002c1b51101030300c0e880c020b0301030700709801f0300a0380241c030200241c0c0541e40c4050500450341301444c000d28100d0b51200e01c1e0f07040c40c500d25040c1c41043d2400000640307502e807045a0603c2020144c01680d5511011007000041c40001d000854040c80c14041070006944040480b089603521460421107007800c40c0e00e6844045101c02d540e984900300104c0043c0602d440021241f194141900751400e94110500981c00c660b10172807001d40700e92080d11848801c10b1554007c1c010004640116200c60b000d009a40421001d0483c1000680c0c00517002081050740280605401030000c502400e89102800030b031070f43d82d0102c1c00c1c3c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 317670899 1250 317669649 317669669
    0x908030c1b01090806131232090d0b06091018021b060f01080c0301090f02061806040902040501080a05150103050c090301060b0903060903070201020601090f1b02011b03060f 76
    0x79000d240c1c040e282510040180400303840a9262080300d4900000c0380b5030003501c6070a02c44420071045c1d4440d442a05203480c4c0c2802140f92452900d0394000e00d001c0b42d01000c034940004005820b0295911030144458621500004007146480d07020301440c0300c0d0142c0f010f0340342109894240001000d01d511032080b030f004030000580310202d60180c102246810113600d205401034000748800241e206c800c160507258001c00700d0704030703000300c1c0c0503d8220380b00b000c005400d0500703c4150380010b2030032400402c10180e010302581c5001610400141d0158801c0e481881c1d4660f001500f0441d65800c41c4125611840c1c41c0c0303080041e0300d44144c0040c41001c00c00c6c1c181d0b0405a0358800200c2015000d01594070008014008220054450308a030b80b00da40184c403800e22074482d9400150f84a28000304444000f941a4040d0141e0303440c01400401905e101000701d541aa2610300060040e4070350f2541a241503403660020400800c846044811782c8100c85507001010704004060050350304840042c4100d80924032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 317672149 1250 317670899 317670943
    0xc021203040b1515040e090d050903070e0c070606181401050f04050a021e0a0e061e070201090305030a0302070c141809010b030d08010302040c230c0109140a0c09060e010b0c011506020d0908030c 85
    0x44000d07441c0c8209a4000c203d0c2d03260a0300808c1d94401030760f5081c03c001c40c02e60108800913000202c84c140c00e500344101d990000400b107002002c3d0425070051504041400400344c100b04181000940b1516803481d0b0b20b400f00000714800c1130f442d03031000c1c50348141d182c2603c030980f5240f0b12114400240d1300303409803a03000301d000040c02000c59204a4440000356000001e80c1d03100c07119104018065480a2403e9480341080840400d08d10146a80c1ca0112030005107104c140040380c8101044461008104403000d540e030741c00c03200150b1000d1004061546141ea1041842c2d0704602c100070880b01304103964810490440e40700003403006100028405032007050015900d41c0b01250145000d0000000c0c000e04400d00301140c4a85010009140000301d8440d1819040583c1c030742d80321104555481c0b150081c0d105003e1700401c00140c86000601510319100008140c1c888461031140c04c02049178480c000590100202c50300c1d00b42d201da0864007604005020714600250f20846a46d80d030200d4244194003a03080c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 317673399 1250 317672149 317672161
    0x110c010309021903060b041a1e030a1202071502011b080a1d100b09090604020405040809061b01061d0402131d010c021203040b1515040e090d050903070e 67
    0x3070a140c3e034643c022540b9109141e12840d00c08040c2c0000d880c81e501640c24001302ca0071a00541d01021500c8001034816100e000002100b060550019035030107805002e5001c0c40004200c00d4005030200005503002400194901050600703110f00c031070b03001c0045901d00302070b04104400814480e0500c841c145031480244e190008400001d00391000b030380041d40c66519400655550200d05401c22000d42d50301080076615000c00d0101c1c0f200100c65518580d0440380001e0f00601d49640420703045402025050706081010340400c4041c0e0024452a0070340580010300e5454000901071100606540385d03110038058521b109a84003100007500c000e1180304078041004406841b0f50100c2c0ca020200b0032112009031400072160700074281c440180c0014000c14001d84041c1c07a409040345e005580c84101130b001d9942e20340c440c5a000d0003000410764401c14142e400c1460558000103407002e049601c15190103070801c0a50149001190040f500c14000180b10b44040c5580100d118022580d10399200690351b5140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 317674649 1250 317673399 317673409
    0x50c0d09031413080708010504080301030f060b1507020f060c0714040b0301060f0e0f130b04030c1b0503070518070f0c12050a12060f21120203070210110c01030902 72
    0x490090325075101c0110791074002d464080000402c130360310201603c0900391111040d5003a43e1049a0107070261904100400001c0e1269002d8400903006503000591501601c0000700190b400992011110030023041142c107600e8003a401caa0910700c1204c0c1a40341032225143c0c140c440c4000d101e82001c9013021292580142c84540000c06d007901300a008101207030300c6507100b09102800740240047e072010080022085c0a025084500030020300300d40da151030000b079668143c020380c0241304030100f041076074034500000d101075010710750300802540c460170450500091528000195003e240318042070003081a2000409003583c3d007121684ca0604110518440700741d81c006503030003000300081c1541072006481c82c0c2c02800b8143d2880241c0c0c030b160382c40e5814200481030f202c5900540b0f1400c08007108c1042120b460714401b141040d04040c4002003520951a400821550413540300c0140e04000f99084c21860262840030013000c4a081c01c2000c00e610700d081c1941c0780b18054846040c107554048000940d0740e6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 317675899 1250 317674649 317674667
    0x10c02011b0c08060903030919081204031704050705010f031109011850060a11120309010506010503040f020f1f02100c0c0b0c030a0905060403030e0709050c0d0903 72
    0x680f0b080307407040d040c40d01002d07a60754003c461500b0b603402003c0100f41a0403541000c034844642010130a4100b0300040740399600904064401c50a0142a21707051010030480e54005104500907400780c000586001e002520a807910000750040520300f0104030903600e2030605072a2409020b1800301c2002188200d0000c0394061707500106840034201c821008800c0c41040c04400007040140c603200c05500699812211441b65091824020510034511b0b00c1030400138003a1034003404900c0e0a0090f0a1800760860404855000f02032450360b0000400a5a0009016180e004072084c6001071551400da20b0368103d50480410082c440c4010341492500c81c3c1d142c1510a01c81080490300491190030118065030b240000b0707580c412907d05041018241c5401260700078219600880d02e240d456842501c0800980d0006140041040e0350300e00d80c1d00802c02c02c001c0c2510841c4a52400a504d0b4101607000b858200b06905c801c044900344400c01040205110558a510040d07c10119150a040c5130940750166 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 317677149 1250 317675899 317675909
    0x90105060a0504090c3c0e10140f070c08072103080702120301060e01020735010f020a08010e01050a060512071e09180b01020309100c0816020f010c02011b0c 69
    0x3100c40700454841c0080c130007042d0340300c4d41c50711b60ba400304000c0e103c2a5040043c00342419484500110950001d0340508400e28500c4902480e9a240221441c0302c1302c225000004255414085001d003440810800c00045024280142003204004d2540022071a1501c404c0801010480c5850204100d54002c2048806010384d10300c4d030540b00d6840d041c1c000c01c21748160008600600c601c0d00005819104400b15000262041945546100e0400f40080c10310300100d0181543d0740d6101c000072210701c01c1e880501011503580e51801455451300039800c05c0501c0680129210b03003444102044426040002c0b01e5007540080d080028942c1c500c1b03401e40d940e00c070201c01440f00750510728061070301ca94404984425500d28010441c410f10603000080c046400000c080303800350780704011003040b6280a0b10014042005490424401106591401d400d900300061140d900a80c00300c40004501d0b00c640c1e0940b20260130b1a2021090b00c080c1c00003454205006241589400f41c040104203020161103c1e1020304 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 317678399 1250 317677149 317677187
    0x203250203092d120304211208010609060509060d090f020904060b041107110105031801180210020d09050103021605060c090a080a0c06120608100605090105060a0504090c 75
    0x5480d00b03039090440300050203140c10b045440e2540201a103003039140c413442c1d884410011400e0500b414280028282640140e5003818401d8009400244c01481424085403060ba20000e0315490954042c0000910303030040018404103100d0311038039031981400d4501c6203421300004104a040c0d030900728200250707488082d400002d514200b00c00d1050980241840352000d8504014400343d001d00d11489010351130005104600c400d600e05980d61040000e95084514019075180945e103150300d060071a00d9400c0401024400d42c912101940b07800c0809082584041c006403030864220100100051814040c86040c540e010603031021800e6840c07407034001c5907031010855078103081202490115405c50820244210394581c8007245032100801c0b9a501c4c2503014041840c0d09090110985030408005040740100d5a25840041e10b000c042007542810441e1f4040060024104414040e1541050b0405030280b40d0812100300c200345d03c4401c03203049946400c0002100c1c1d03151803080320114452001e020b282 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 317679649 1250 317678399 317678419
    0x3150f0409030f020c0103020f120703110c010c0f050c0c0d0c0b07050a020a05030a02060304060f02091512090d0e01110106050406061707020a020d0609020f06030a020a02060109020325020309 84
    0x190000d0f00d03042856000c0c1c003121506207003480110b0a07880b9140207480104014401640b060000822061704040350741801f00341e0f00180c00e80d01601e03411840d0320280b9607468000041c88981c110154000285251403c1882d0076000402c056950908014440c0102c5508105d901485220800342d00500000c090b526070701c031510b00301140c0d6012049016440b030207030841e002800e4600058400d611680c050700803803d55403a516201c0060000000c203a8155408000d035610719030748c0302a40b1100c910544205034940310a000c0c4200c0481008203ca0b10f10751140d04508011340c0c1080c40d0200c14182468010443c078192200d55001d000e4a41c808c43c0c10600309500840d2054000c540c11007070201042c2c0040083c0e4078284e003240d480f04292000b03500b10540b0f0318400301103015a007103642107600103007904003400003d5001c601c0c0750b0f204560700d2100b1035010801641207a41130000900501d96a0829425030030140100d144000c100042e0100e60040c4002c0040c1482c001d00958070000d0f80107120200c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 317680899 1250 317679649 317679653
    0x6101409040b041b060210060807030c030209280207050c010f1b02040f05070f2606120f0a03022404020a350106031e030c26030405010e070b0f03150f0409 68
    0x2e5803014182001c601d238217004020070042800030340001281d82000c9240349084c595000d0000c03145010380300307098a070b15a0b507010310740a8031010081540105a01d0040e80c428807828004d00309002d44004a04220000d4941c2800660100c035002d5188413690702d900b021002c900c00600181880542040c2150824040101250b040000701c40302d040e854490321014920b140d03c2c210340ba0382d4000b5052220188401081c05c90401c00700b00d081c0942d107a0100c9603880162a18980740006c109000c400603030020818000340d80240388205814070076403d0800890500d07600242c00814940254081c03003001680218130001280484440711089c0c0302d401d002c070400205058040d06d1a400295458444401c0103e410b1012815091300f241c2c240c1d0b80c004c05100345a841489115030405112440c400c00d0140b00b449280c4140214002c506c03500c000260000030203480c07810002c0c40d070301c140b0f11a01c040c400c0131070640c0d42d0070449a100480c10201041510640700045194141d44041c5070458644004041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 317682149 1250 317680899 317680903
    0x9030105090a020a0e0906070c0804030b100612060515030c091206040b0708060d0f020a0b0f07020f0d1a0901060b0403060e0c0604050f12010f02070506101409040b041b0602 76
    0x70341503000783c0303c1e500405c0d10344040b400c1040c2c041e505070f21507030321041c0004c0010b446015144441403103008042d241590765242d802410b0300a40d140b502000e1112802c204464200e100303500a0300445200707100b001d10385400100c2c0d180702000c9900d5105000400102040c82c80021612082d40081030881075407040105d4603511801100c0880309608a14081070000c0d00516066106a1000301001d03285203a5545202210f20510812a040300b44600c5c0455811155070181154400e44000c090b15030256004000c5000320605850703004401141092010800d4610701d600101c45150380c0c05191b4441e818100c3c010300f155486140c1103100420007108102640d044200340345128011250000d44d1681004024030561042a51120200c0740104003030030321254402240707100e0400042c0c03504501403010242e03400b10b00210340c142c00100400c2800c0450b629900701030070450050b10b80d42c6481d00e0102d140204046c00c00381c129121003000030100b0512495940d03044103082c00a1020a40c1c40700c0181d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 317683399 1250 317682149 317682163
    0x30411041d10020403020f01050d0f020c0307020a051203071707050a120e03010e100e030906071217070c0f02030a210306050303030405071a0c0d080a0b090603060712020903010509 79
    0x310103006600d4100e01c2e042c0a402500c0650790010581e4004446079001501d8603403182c411600219110400d03035096400f10300c007418888591030061907803a401841000810015604401c1c442e14039101c0e2168100300020a9a04041c0d000550741c102042c50b030380b420031502071080000c5c50751140d00050010440300750f0b151070108034607454042100915030105070030782c0d40c0c0100b8940c4650018051501c0f00704143c10a001120703009080d41d1030158182d000ca01207a004090a542001c103005000700300030341c8010f01002d0410030701d42404c00c506211000401e1403550744001b805010b40ca0103000117540c0c05001c00d680c115403024004d4192000994014001d12444010300040380c5026000101818040102d0384100d40c0500900410381c1400314024440f040c1031032181a040003488101c0002a041100040080d55525542d01d03c0c6420510107066924106503280244080c0b02849981e0700c4c00a0441d400200508041c060600b80b10210002400f402541a034590300b80700138044800d4000c2001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 317684649 1250 317683399 317683451
    0xc010f09030e03060f0f1009060b0a020607050c0a0f0c0909230c0d0206030a0b0a0e0f25030b1c060504120806180c0f0a210e070b03041104 61
    0x120040780510b03410140c40c0c0c034046070b110b04030a10041c000342c240c04803102090340c4100526003103140c8540312404c502c126040b5401c0f10f40c00d80c1000038031f0305031a41c04101c4560300c800e1902e031071454a035000c4a00750311680702c0d2200809150070003207044100f10241400201a00d0740040410600341c81d414401d4441e288108580900c82001c4252850040b01085504403031401030403500c030810300b59080c01030030b030310017001c08140300d980303028440e0643d40f00c0302120020302071071350389619905240006d400302c01c601400f18242000c0c1c0c11300740310000d8403000142d410711206081c00118500301c0b10104900080701d85064101c084040303254801c0003420380c4200d015034081c4220b112540d820b0f150a964009007980d075994028070189401031266031000d219903001401d84180b40c00c0c00807a40d1100c201d50009890b410114100e051003040400110214481d9500c0c0d0440500c20444c0d110002d41d26554180282d0340c2c081c40c004000340a102c00d91007000b03201480a08100058181980d5100041100d0303085 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 317685899 1250 317684649 317684657
    0xf0f060b0a0e0d060605041806060e0610050705010e0708011a030706081909120e03061e01230d0c0e0f010305030d09061b021b0607051903050c010f0903 67
    0x41000d1000c4000c1e80c40300740791034071482c0e50b890440e030070000d10025101080b651680c554501041d13a4950340110742d8400b08103040302c20b0b881c400780341440a44110790010f002484051040205e5991055295410442039041a540e038030040c1c00e1250161142444041c041c0c403410600041d03007401580020000340107110990b54140080c010141c441e0b046202d518001021080410035441401c440b000819041200000d00307400140e84403400580b142c1000d10105900d08a100150b080620409900c031980621111580414107a030000f074000600501010f01d001042c1801c01424210760414005001807034044079140929141d034254183e0300a42008601044c04120700d80c5002480710305991f445400366081c2203400300700d24000d110640c402d650071500e5100e0b00d030030742a0410000d041d4411947c007a05007035003400c0c0c00540b54540141d50900510040100801080380813604101e0740b8040814a40e41c0303981401d003110b00b07005021807070a107946170a6685421116a40c400e0034100e2094403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 317687149 1250 317685899 317685911
    0xb18070b0409060b03010503070504110c0a0606050901080307050d110708060a0903110a0c120f02042405060a021c052b11070f120908030408010504150207050a08070201030204090f0f 80
    0x4107080032801700307106141e0564046401131100340341503041320044c4204880200e04110078003458901e80542480b00b998140c1d41d503041488203041074150035001d004c3d110002c40c40d200155607299541c62012070340b40108208901380740c2d41c005062082304000d040790002c42e0418100500b1140040c01d40c2c103412400300e603100007081c0380d500c408903a4103242070b0071050351403d10b460181040103c1c0000c14080305d90704100c02c0c00c040142d41d6841117011082e00307407202c100048210641010a00c5150700a2803103a10140800000c1c141e000400c61811482903021a59102c1e4200007600c1d01c0c0240380b005404000080420082e2078075a41001c460002000c10500c071000c0040c4421a5620a440c005071650040c10300da14045956001c14008240b441c0c540442011384c1c81074054111f1b0415044012640d4440c800d10051140442c00c2002548605108618001c00d0307a5410303a139424007410080981a0126015003968000d43c1543c008000e0048180064688840340740028602801d50b1594a89000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 317688399 1250 317687149 317687159
    0x105010501110d0503040303181b140a0311030a02030a030c05060705071203180c090917040503060708040618030825020309011b050d0e1305070203070b18070b040906 73
    0x903011480815400b00a40b040301d000840481d020f51000308282c00341602d801840300e12400c0c1c0e2400a0b44140a411103800c0958119690100f4403100c0d07200c04400e440c0710075101056a00c20f14060100d0b40e02c00555011032042d040442c6c2041904074000e903240c0120604a018141c01c0400790941030b1141c0140c44d15036070392001c11f071114064000040c2a070503030003510540044c0607600408440ca00140501642a1540daa03900440000d400030200b403601d5829020401c0f0740980000d80c0708410340700081c202824040400c0c0e0b1150000c000c0001c005201c40880c0510245601541b01103450741c01d01742d1291340c1410f02030000e5106903070341b0b40000400007660108103144555800940c00c0c81d40074500d0f10200d0f80044810b00c100c84015041d030b6031f900c002e24001400c20809402d20000680340c2e410140b988008003c1440d0003540070361407003414002000035243d0b01104642600e0b41c0b0950308200c0d074903000420101c2d0040342c40304003071034400c1c2c00d00410344213540805001203032401d08bc107215481e115 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 317689649 1250 317688399 317688407
    0xa14100f080604090f05070b0c0c060301080c010c0c17010218060306030c010f021609061419120305040b0307021b0402070209150117010b0406020705010f021b0303090604090506030105010501 84
    0xc100800e000a61400105840b890150014107000780169a80b4400420a031101803e2140640c400c000c00140000c20b0000840103100042030200304440a60540d0324050180d0380300c031020300c4524100150802d460041020403000c01c8054440c000171000e441c0a1104024006d5029290f01c408020f1191528449450014100c0b8071031a00500500107000e070321001500d4070703041d0b04544002e6004414080402d05004407816005120041c00801e00e00d2400500007420800000e08a01480c00340101684083e0119401d030304035200b07204c400c8148002402c00311031030300540d081034080c9800041071044490340018000009083c0d101e4150049500408100891090110003074010401318001503035031003d021000041030040c1006401c0c4030880d02864455182608030913403030341d40418280041a03041117032001802c000c0c00c014000b002181c0000c3d40d07403c1c880c840800c44001c540b40c0c0c006180c4050044e90f900078805080d440d1101d40304e81908000c0d2104680d034a010303600e402c0001619600c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 317690899 1250 317689649 317689667
    0xa09060302012007080d05030a0501120206040b03060a031205270a270606020a0b010510140a0c0501110406031a18090304030c1203030c0e06030601030b030c0a1410 72
    0x10584501c0d8900c024403c148a88240403202c8000b203024240c00054000811711592070505126a151b070b03a40d00e0904d80c0030040f1101a00000e004034000028540140c0301c503412641074038075040c80c482c1c8a90b505400140801c030130f07030001403078400398161111800b6009800340c2036290301c0704562003401c260f14481c8107100c140c0050700c1e80d00c00c0b2514420000100091b4511001104074843d441200c8020303400001074402542c0010010b900682104050140c20300096000d0042102c035150f8184848074001e00d444902591041c880c10001a8091151300520307480c0401d2364000c000b030200c002c0fa8558000385801c14030480000c01c0c280102c0b516040c07520f824494007108000d000200110710036044203407010004001c001c184c8010040030000c84d81d001b0b1078000034181c040018280c04074514000302a02d0b040b40b01802031000080c4510f0080c3da650050302d60110003807030300103048100310000038501081d804400d034124010460102d0301c0c880f103a02c009184001690340742c4044040040031540014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 317692149 1250 317690899 317690903
    0x4050603030f09030712140f030a0c0b07020307061401060212040f140d1a270d1b061107060b0603040803010522021b01051008060105060c2a0a090603 66
    0xc000320b00840055001401c03c0c2403019086a82e45a22500d0725801207810f0042503806898024000802c2030b0104816240308045802175814040c02c2c00d000781000303241e00c20003008106c4000c00100aa40b08109444038a80c001009008142c164199415592020300520300140502c644842c0000c600c00100c0b0100c40302180c40c00111850f2200d03001c1c41d80a442911503010b040b44906a010440e044081084107641401029190034540d1031455030110000f51086103034111160310300411000b05107c03516070310b6030510506414201c51100841170403004020906407400d03480d01000d900d1107015101c010700c03411042000c02c0d410f80811019000031640280380a03810001845039081c950201601c00f4081e0310100305c603490a07503200c130607600102d40c0801201845d401c10042e0003800d00640b504414205d291340000c1e030420300202d441d01014011140121000207414850080030440c0c0c420004808400d02e000720350022000d0f014007001082d03a481490000c402007a0005d80340f00e44802c40c0c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 317693399 1250 317692149 317692153
    0x30705030d0e0c0a0b09010801320f0303040905100605041809080405131e05130b13140708010e06060603150102010b0a14041b05030403051312081804050603 69
    0x3512002102001e0500c1981a20300e0f80546036403210b540d02c8440c910030191015068640d00d070490f2200052440c0d6050b408521050100c0c00342d8641c0b01e002508101078402320010383d040904018000c1400c602d4200c40494040c8000640007540255550001e40100d0b81e07000005982903072120219414080d90144080c81c0980300da25002e0f541840d4040e81401d4400c2c100d141c142982d40000407000500341d0f6a001c4660b40392021030000780b100000840481003014010002c0e410203824012410310300c408001c001000c0c6401142e040e000d0380b007042c002150700589850020b100d502c0c00c4c680301c00c0c040c41000080d40c206501480501c0c40462694441c0d1405071955082d07546103000c00340301c2c2031400700d4681035550355020311109480e1000403402074410190000c84400c150b205220444050712401d4005c1c54400300301e10403903544102205d4125401d441c016480e001c1c156162404107002d80e0107440070107603000d540800c10041c030000e8044c0d1510a11340c4111040000c0c103020907114100c039425495 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 317694649 1250 317693399 317693407
    0x9050609032d01020301030311061305060610030f06030602041d0405060423161a04150e1504120308090a1104050c0d091b050105040f180f090f030207050303070503 72
    0x1018510301c803403194041c1d035a82c0010840c0700035940c3d0072a8001e801c1a00002c5409000703d540c44000c2114a402c443c4820418040030155124251101006802c03a44516203642e4044915440b9400901c0c03040e202a004220366640e0b46408002075005208281c1c00542344442c18951440503c403a520464102d40545400d42d5590748042180c6040051031040c07642440404035448803c200441411084061401a8608106080b00c00f08003110300c02c25200e604000900c40880c0c0c82c04400c9042e04d25090410b004a075190000d42d1600d802008800b0031030f0301003030014810103445401c1c500c403402900d451209880f81500c0c1c2d600d03004200d1020b81020b551007102c0c1c000d400e0503031207254407a60244a0604000c4e014014000740c4003000d800b50b840a50546104c810142c0408441c002800d090030017901d080c1c81c260702048400308511030300101550f1801003140d00d4000350402c0b040078101020070406001c044c81e0401e1801164203060f401441244808211810000101c47c56185c200c400dd40c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 317695899 1250 317694649 317694673
    0xe060f09250507080310260309040203040c080f03070606050a0e070e04180812250f0201020f1209070501030c0e2107030302060f16091809170a0905060903 68
    0x1240400d2070803a820444100080d0380843d10301805503009000c40d07044401558035107680b010100d149400c140c2800d20110032070680881d000806c90b074038540182e8000da2607668074101003103a040640d01020785801081a440c110490220081c00d00a100d480200701554544003480b0440703005000346001d40d04e210000c1000580141400c170f2454600520203d40502807250314a80200103840440728080c0108040720160440c1d90341540c0940c83e08001c1c070042c1d0440052400c001201c0c8803143c02d1103545014251032030300c01e404440a103110542c245130303a1903074640462203412003191403408038040c600002c2041e61080c000e480d40443c1c135503107480d01d400c981030410440c180700c58806408007038051156040d98505000fa03000640c0240c01519551400c07450000c20110b0040c4039409001c0d046060f8611150058403078410340e11441091010709140c5d540c039500400100305c1c05400341009a05009544007884020203514109544500340e00c1c2d594000d02c05680034268020358580c00514141003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 317697149 1250 317695899 317695951
    0xb0105030a1d011b08091507080a060e0f0411010801030c06050f040f1e060e090406050703021b0d0905030102040b0702060c0a15090b070f020a0803060f03070e060f09 73
    0x140b2203020180c41c11100205007070329421074643c140d500d80c00c01c9900c0351415005400800329030f485a650703006002a00c004003d01e10000c140201100203000c010004900b0fa00c000781d100501902c0c00c0100100395040c205030f201000802280d0842e2843c11102854005511a001c00d034100c1c5c4e0b21220b000f000505001055039690010380780c08105903010301000610080c3e80020100524450000740d01c0001e000402c0002c03407a69801240910032986002040b5445516840da0300c0f035000400003600c0c3d102e845045019101d2502801284074101d212154041c0c6c02203415054170100d512201c6100c2d80d640141400c0c1d01441c81088000d000a00001380981070140003000051070440c1030710391482e010f03076444150080d0342c985074804544c1c2d802d212040148004060703030018141d05104105d0604420000c0d40e4189542d002000700f0701c0400400c0345070b251194650080c01000b82a01d10840e01c07910740101a0744c1c2140d0003846101c40350076422183c10000f000c0750040d541d403101c0c61000318007014290 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 317698399 1250 317697149 317697161
    0x21b10140f0d020409091e08040306020d020c06090d0914010203040902250c090f0b0916110d031416090e040203070906090b0a060201051005041503050102030c0a02010c030b0105030a 80
    0x102401c4200500c1c0c418503010300c02000540030074100095210040e0034200080e44040c0600c4240390034040500780450102c4041d5070407241e0055002d80d58541d000d8403140a801074511710b251364440d200c240000340c1004540103032032461a5664020040c1d4031b404000001c210b40f14010b025801c2004244000a403d4001340b40c000700001601016115400c40501d412550410039034800100d48018800c40069000c0c1024500b00420f0030301c4041940000504010b9002d071014240c0744961040c026141e0141180300503144130081541d41c840c41624010b4040d204100c01529202e410000107080503004108075421003590340d031030075200360801019403880d560140c0143d0740b40c40764410010b0244a04e0240d50080c2c442850301084490780304013030100120250f00400150790402e000c110036001d50828103022a9401c49010800100c0c01e500550780001d103800c0a802c5500002c10080407002c45001400d86c40c0c1c16500801410752030160440855480600250005800b0404030b00b06a000d6007190b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 317699649 1250 317698399 317698417
    0x4050d0f0807090e040c0803120406060504051605070c050301050a0b180103050c010c05010e031305181b07022707021c0909020309030c01060f06030c0801030c150203120106021b1014 80
    0x418200c1e900c7d040e200b840d40e00100806512901a03504100c01c20085014080090405480c148070303e0904043d00b0581803820400d410401c00f01003482024041030050b048000d00c0c02900800840c2003210f0780901805c0b0001d401c0d0300450032504510301152134255424100d98106000e0085990218011680103445070f5003907031a9900c81001c0c90f500b10003800184808e54585003a000c11510b81002e001c0c0c0d440c5921f03803100150311607008124002c81d80741200f080c180390860b0601da4070380582c40002d142400d005502d03040b030075118180c1c6c01c0c060800c9802c0ca014038200d400300c554995801c418203076110080441c5600240c1520001c0000703a00b25000345800c030107000103403414124a251030b0ba0841c4c8040e8040410300c503141b4020441d550300b600c94007151112516004000750304586850b030b070340c400c075100d40510a1040c28107103016030300c280151f503550365035200d2540055944034030081d41d4282961080a031030061210413141c51400811081d069201134a80c0040c0303030500d8009a00542000700f0f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 317700899 1250 317699649 317699663
    0x307150c12050d06060e0f040c0302040f0b04050306090a030516020d0b0405060711010612020d0309051203040e0609070e011d0d15051b04091e0504050d0f0807090e04 73
    0x1003a0009003091140c401e42044903a07549460703035000f41214059965980c000c2090000466018013641c850390b2601700c94000c10350303000c01d0690828604500910a5a00c0110055803403c0301040c8280c00600a0080790021011125107407221180d56842e007541071001004a0790401c29140c1d030390804025085024002010030500d441c040c0c4602082c0c01d8125230464094008104020b410f9030401140c010158000340200400350078040d030a41c3c90703004010701a104102c030440c01020544100c050001820b8003601c0b202900c0203031711309241d0740e400038010780010441e050700040841c140003954034031600c00c0380c2e1040140f0441000559401031055100c0c2480100300c002e580c1c4c00d446145401900da48035450881d0141100c0e00c00b0b104544000c0d02d03c0703203e44850550032008003034039401c0d00c00307a428101c000500800c041c03000220b0300350003403c07030600709003000104010b201010401c1404d181da65210b4a1a1000900c4107d48000003218404045521b10300c00b4400c6428102d0070b90360251250741 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 317702149 1250 317700899 317700917
    0x100909020f0a0305061807060c03050c03040b13140f06030a020309010e060702030a08011d0705030a09050d05250209070c08160606051302030f0f09011b020c04061202030715 76
    0xc00c07580b8105800540b2070303a201001348400030802ca14020b004074400c902074900c2c1401c0c503400520001e10804060200107011074020506403040c41203900034908c0910260750382a84800c0c460211030588103024207900e00c3c11040501e42490410401045c10003030401b8611382c0e81d041d0060003504081c2032500150740c2c2e04042001e41c041000958081c10041d0000c644071484000010303c8190705800540c00510000003680e0340406801c00710381c10545038200035440b5501c010701d14004100c1d00c1c070b0140c41441600407450f185e9402100030700300e544108040ca2910080289050740c610b012000080d0003d810b0800112014031a000c4011900e1040c241e65140c5a0303040900306061880b0402aa0742c41c0d5120301c20002450140314031700310341610306030035821481c1213451a0f003019002090415501c3c644030025140d51000c1d44500f10308500c0ba144d0980031060144000d690714240d0a1040c000c0345010008280014041f850b45102d60740140213060150400303640f80201a640c0c100324051080e103130 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 317703399 1250 317702149 317702179
    0x19060906050a0e1605090408071a0f0a05010504091a070509040f020901110d0f0c080c01050703050a1a030a2a0b03040201030b0a052139040510090902 66
    0x80a5035010b08000c00c0003090243c8200c00541c200800d01d0104602201048130410142d01c0300c80c4019441500410003645801160030320b41608041022541074030307242101000600080d220149005044184040140c0da0300c80080c041140e908600c060980d1050b92010249070407407021103580300c40c60307152050600801e803002c103040c0c80d14558080b001c1d58007c1441c007041c1d640f04041001580d4044010815a40d03050009006912940320f5141000b01000340401407082c800e040754940050b00d0001c00c81490104001802003c090390307104611030400d08890985000c1100009072001c0040c0502038107800c1c0c2d03454283e100c000d1440c00801201c0030b02060398140d035002154004098017407003559246458800101190510b40d90b03030348642c0d00b0000034443c0e511440141403908824000e0411a5000c00b140b0f82d2500c0341d045520702850810883c0c0709c00c1d030b140e24a9041c8589400b03580c240702c4802c0d80c1d0308000989000f10343c030041e9284600b03020081081241c104081050028040240200e895 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 317704649 1250 317703399 317703401
    0x206270a0b09030c331b030c0c03060c1209101401080c010503010b1812060a0614060301150f0323070806030a031b05010b100207030201090902040819060906 69
    0x15038003801c80500e0108911203281002d02220b043c81004864045040202c620f401d0384280a03803202900c9001c4588200701d02102080844802030301d006510083c0180d80c503e000e03601c1d488203a47c840726029200e880744880c00d000030540e0040f11900c800030708150b00e0010303005402c003004044c0e000f584502c0003d810000844e10a040c418000008854042d40c11f0140c01032515090303140043c108034041004116800289059440900f80c1100401c1d5110296000401da047e85526444982c01004180b0802c0c0c030043d408602115081c9900400340300400e0100a500d0000344a10404a0060098a004980304510500c074182c1c1034140020b10341503010140c0da03101c1c00c2e610882c1d900340c1c5050038000440e41104400b9880f030000c034000d081c0c0e18826603008003e0440d098511141403e45200f907030030001c0a403c000d0b00c102c005030601e100b040701402d00940da40c04c644010f0340801d250040c00304420755035008a40036103141e14010081c51a0001800b4000800303101d0940e201603403090000001442 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 317705899 1250 317704649 317704669
    0x601200c0a0f1a04030c151206260610091808130501110a03350c1b0706020a1104020f030f01030c060f1205130b04030513060c020627 59
    0x4036510198030342010f44540941d0002c040e4014681001e1108100107141554000d003540c0d8494541e8080005a03002a41d6805506100d00c1c5814140800030440000ca0a02d80c480707141041c188081c0112107140d4261502c6003620003400700ca070510001d11110503260030000f6019a10138450300f1004107178a440b00c85400503920410700f9440c1a60400180d0f0303001812030348158528010b444011500e9401405090740c4910002c111141c01110100c1100e21070903206400c004480000c0351071500d128803000300d901a084800500107001040c2040c280d001840d0010303144075800400d0789181d07641354142c1080c242e224440e88a9020801c84d54251b4481014500a20b5626405003481d4154507040406076100c1e00103030204401c0001c113803002a48004046484640309100041640740c10b0541d82200c0140701e4041c0115240340d003032004050340b000041c20140744008e01900d002e074940e0310032607a55445000107540b2420610a00f0950226071449680038004404100726a840d150003044a1b610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 317707149 1250 317705899 317705909
    0x2070812030115080108030d0b0a1a04091a09010e0a02071e0c0603020c0d0e0f0904030c03030e0106030305040501030b01020f011d1203220f0203330601200c0a 70
    0x30040010003a0800c82501c40c48041020f083c868030541c1001c3c40266203009501240084949400340b0302819102c1a90010103030040340510b08440a07585034001e41c03503020b07200d90b0300824500f50220000d9015111480344010b4000c0c6406142e910389820341c440814040c1003406c003c0d0342003141c20000750040d0803000c01c940f2a070405030600552030400c0000080d1562100c41454010011001229004515040d444a0310f05041751481300100204150030500803045410a80100c2031109054000510000651190360280301248030540303807078261400c80c48020040380d401c0c00240000d6000b41c04c98100101c043c4101c401154100000501395919550003a01003540340001e030040b00c50600c40c400d5000d02003e161407960030301c141c0d02c040c40c545290200c1c1c2c09010400c1d01d5801c1140c2c514001030100d40007402c5908100144440084030341c45c4801d075540d15058040030030052501948503030b01c18881611113a5a0310046080b111031000307840c1c42000e2030301440b003075810203a0b145200c1c440504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 317708399 1250 317707149 317707183
    0xb0f010f020c09100501020d1812051903171821090a0312030b0604030b06060f040305030319060e0714030a0e07080d030e120301063009120c03080115020708 69
    0x149085c00190411620800c0c4008000c4000c007403a090b055800010b0084544890b41081c04c41414102141004c0d000e01058940100401d42c100078958080366042c2c41044000740c4041e41d440e00d60702c404015650304010410381d00b100719014400d07041ca044c40114800700b040e000c2d14061709500000c5104c41e41d40c004851400c2100c1c241020154503226151501d401692040d00d0f060550311910f003940c030010b11051091000154041d14180400705680046a00400f141d46030308046000d821948500381e071650489280c0f2000046000a480d1004e000700f05603141e500340380040c40350594050b4401040e852135684c07103110810004400b000f008005080990181845001115004040e03810b1a40015042d0b409461700402100d040320450741181c40350700b8074070b4240303400000110010320448120340c0c0200180c008007071441080c1d0005c0400904c1680c10000c43d107000e203011f5943c40801e000c0507000805860051044550300614055420054012140c0c42c0b691803190780d19110400d5005101c1ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 317709649 1250 317708399 317708431
    0xc0f03120f0e044b050a0216030201091106040b09040e030427150e01121104060806070909060602030406050c151f090501050d1b15210b0f010f020c09 66
    0x1c45001500b070001c15500c13003000d481c1e4240c05010960109100c000348190790382d03400220301e909069a040301c0442c1d0885032034854013011414064002d202620098070f040c0d24a181e05602c4d40b61900171941a211804201c608100050090100400c6d003003c140e5454407040001040031120b2403041c10301c01350025030361807600350300e54210800d1358802a0703040403d1030920014401888002d0a007030640c0d855003030303640424899003441c00c442895002001d401c1413401c00046941c10001c180c00d803040c882c0d17898409040d80c1d01c980600480e5001e21981005030030911041c80100d1140006190181d2100c00f102c0307545148018980541c001512610500e243d01c801d41110301c880c8414400c002c0c10428002c01040d0b140001183c001e5681c00750040046051041c0e401480c0e607003a0710f85000e01194040300c040c03031841c0300014004040444c10303065461800b640034a0204814015040608005420300c406094214010758030840c1404184066004640c1069919140c1580e5984981681e00e0100c1070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 317710899 1250 317709649 317709701
    0x9200d0606030e0c0306011806050d0b01090b01020708071509081c02070e0903030103060e15040303050601110c1804080c100617010921030b0409050a0c0f03120f0e04 73
    0x44444901500003540c01c00140b13203025a5022a100341180c41e265402c200342d014884607000203140c1a00150741c400700f4080c02c4014013114031805410303983ea00c00d04202d552124001640d03107845c280b26007030144e40880310a1100028503c2c00c00d03140300035801c095001c1612081001d00f8036114a642c00c0044810112061120764100902e10091000040200305402c00948032522803005000140c030150700c0d4040a52504401c2008804c2000c8481e015611410b04d071800a024100130745000340050020146070551000108508401810052041000c44220785011030701140003441580c0c000d03800d0081c1e00d42504140310550109000b403400207042070904003007140340001e41e6452111a890004580c0c0000c40e0040c0510003803050306000b001203030300400128040c3c513861456941080c01c1204400400c00c0001e12040c0c1140f20300f6031101c0c540e1304d600a60310207c0803480017600f8142c1019203a0915801050507a82405980c9040c003d86128600410182c407404400c2c100404900600343d46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 317712149 1250 317710899 317710901
    0x901050d06081c0801030302030a03020a05040503010e010b090c040b04150e1c06050c0f0304230703030e0f0919020703021e0a0b10080c0f060d0e0a0c0603020a080109200d060603 78
    0xf4011070b05061840300d9505646009649008581d204410f1540c0015110030144c0244207480c02850010b00074812a1080300600d80a0300004007a68050f40502c03010409240803001640d040d03420220b20241071525040440416050410f014002e000c1d2201e80180c0030b44500050780400e280184204884d41c81c07030b01e8903108940f801031103983c1102050102c051101d21860440790440d0f00300c2c10654403a100c0603403601100e02d180f1944141d0b8030598000004160308420460b945410850380c0a140e010840d09012000800b101c01c2402010351088036815000d46901601d100c80c040d104480314540c402181c00c1a1803805c00c0c551001d60300c500d08800800050158150b030200c400c00c444460303180380c4072050344e4400030350441b24480c06051400c101183c81c1c0c2c800381c5a443c0402c2e034041c4020300e1101c4485032184207580080c0d07610314901c60701041d003034004e0085030144852503403841c5443c4c0ca07081da00d80c01881a14071100401403da04510302190b1850003410401040420003e2500c1c500f0345c01074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 317713399 1250 317712149 317712193
    0x10c091d070c0b0405100507110709020a0c0f05030702060a03050426040528031211010501120f1a090105150d050a06150312030506090f0f04080901050d0608 69
    0x15032012010080005a070307840341e04401081c0c2d00c44a0702c08030b03895030701d0154103150360306410312040c0d0f2030542003125141d80540b2a0881c0081c002c150313072104d5198964202a4441c111840021802202e030100001d854001e90580c2240604c0030baa06000f00c903400900681d01000d0740740c001907114024041441030103894070149003200314248120888111008407503008030301c80c2034801c0c420485a000210309008203210000e607a1544000304d141c8915085007100c418040090021b00c1c801030b0404401d40502c1030505030307030040504582081c0d95a4803181100180c000c01c50f11058a800c60a24140d4040d41e424001c1e807061001142c1464002c900108604125615274800d080e4002e607040465004652003a005802c00004210f4041444944600c1411644024261014082070300c0700b041e81a03101c0b501542d01158a0802d94440d6001c0c190b040e481560061041c070601e00114000030281d10003841805c0f0181807180c02c0681042441003244c080740d124140c9600004140344940901010b0b00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 317714649 1250 317713399 317713439
    0x708010504121e02100b0d020406121b12020d02010e0616020906040902060319060e011820160c050a0f0e0603010c120c050d0c0e04050108191b0503010c09 68
    0x400c00798494020000e40d03030505e0b00c41c01e8103003982c4d520b40d07800c41703446010041d03c01c2c0390007403c18441d082d07440c1406160a8110030b420303105481e01010f0041e4010304405603170221494020b4132400c80b90f2540800c10b4205807524103c0c14000d0b20204210f0350785a01c805400c3d0200c410050b20340e81e2a21740144004084000c144601c11890881b0340c90050f070b0780009480d048405030074102e1111034400e441c00c008210607048140b403840f018000083d8061900e00b056011001c0c0e16040c040c6076181000750745100c604030740c08840c0082c20700031b298840d201140f41500103401802100e240716520b03000b1450b2141950404018044009404e103c000a038441168010783d0540c020040c0c07032460f24004014082e0042da208155480d41101003800348204180c1d0f490100200041200c004199005004084405500c5006904007000010003140105200c558100c12106a584c04c00042d60b0f8480181c2803219076154510081c2c00c0441ca989003403244130704481403520b81041c15810081d0001c1079403a0042d80c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 317715899 1250 317714649 317714687
    0x318030b0f07110601051c060b0a1701150e04030309060b060c030c01060b030c09130902130b09060f010926030708030415020c281b0612020301080c12070801050412 72
    0x10449607c98030420160014000b102c01900c02c0c80740380010140c1b02d0401040d50010340000d000c1500c03881d000605820160460080042007109100589100e81b6485040841c00380b040000300400e01035040302c0742042c811f42000a140c1e0a10002401c0b60708089000313042c543c4040f41d0fa0410020074841c020103051182103880c2103183c0401c85480912038007035101c1c000d00b40201071804600098004648481e4020100c4a40e40001c480b144001d00070744285a10a000031408204a81008a02a07417400700c180e64621000d41008a070444c0810000b5107100c0f0705180c0c1c1c600482c118400e102800c01c0340e22807501240d40e41407600305030513404e551750700380296944100450749040000180d50042c0d0440c40030400c64001c1c46001900340100e201001514410106145148140c0c0340141c407803c2c2c40143d19440504408035a403001240024040c041031341d80712906031112840c00500354011700741c3d54011180240d48500e5407e0a64405450031140145084624051180c03c202460110407858074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 317717149 1250 317715899 317715901
    0x315150102070602030c0703030e01110607120b060703020c061b0a0516300807060e0708010608190b040507173007020925020606120d0c0318030b0f071106 68
    0x861240ca87c030b100d1000505022001c0c0550b42144d010381150585d00301900141c0740541703416003015010b9140350710941d140d02d01d0720030b15401e107107424001c0da00c02c2a0141c1c02010b100d1103240500c03c0a501154039401c0c214408e1b040e04862031170422195801ca0322075405000c001c4110303403814420241c160070003401103404018a0744140c0086002c400640020750340b07000e004c3d5142c01e020406104d14070002d0f0040d42840207143e0750b01000240842242c0755035000304400d540d10080f0a072104607566001042100125195011524082d07149400900601c140d4100d5581c40d020581e01c01c5000d425441550072281d001c0d0a504200c290031000074801c00354900f2800c410300040001e070301c103000c4003e1044040c1004a01c681e003007500600b00030080003030000344c124001c140c06503a9940440b1000c0c0b003440403180390140024041420340c0142c0894440904070982540c080e140f01c8041020300202c050017880010203c1e0111110302d00514001e0071000490920340001002c900390309c40c0354441584510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 317718399 1250 317717149 317717167
    0x6010302010c120e040504050109030906050f0d2a1205010605071211010b03100e010f020f0405061b06040f050d02060106140c07080601031a180c01050306031515010207060203 77
    0x800071225648106181e82070b200d00b9034250b400c00020340c4c1c540e40252411040008119055200304c7c1141c1c0030740c542c8140c80b036498000300e03054410100c012003400c4040c0441034200c01c075500584284c4480d42042a58691110030004000f54543d00c40d100041d40525003501c10803a91040300c0c0908110315100340303403003101d03100d00c82d0f0150388030080810468174030100b8004100c00c0d80a0042a68000c05607114150f144884402900c4190032041581d441d12411801a001c20b208032503042c8079140c4940d003420319200400c181e40c1c10045401140d00710312040801e90741c600707201c0148918490031a442811450f424400e150808070b02c00b010555000c0801404480d8008641003800810920704030fa8441c2e0180b441420b002c001e60080035984100030000c07040140000c8001d25030b44a00f6011070065648a00381d000d03520080c02c0411054008a03401e0185520550080d031340140007404440c0a03d91700100700003d2030084a900c48c88080002003d480d130740c0d0510503030004120500c01182068558 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 317719649 1250 317718399 317718407
    0xf09030c030708090316060306080c0f030c04020c10050f0a1103090703060e030d06031518172503030c020d030b011b0201090b040f08010b1005120c0c071409090601030201 75
    0x10b94098014007001c212520a5601000303800c00381d0391901c004a401580d03817100a40079000038001d600c2280603101080009080050185140881c000c0017000a00054002d000003580208140c5c3c80c3c6010b03a8805001c3d0320410f000e500e000b040c040d0700701c060919004407003004955044950012000c4200248142180300140c00e8050300e801030400903c800340565800e01e98490f4000f040310003401c0402c00820305c20142c005c03c0e49110400810f018100c80c6514408103400c1c0c0250003040e1019030182e21800c601c1003800303010210090f14140d40d864001e40b400d9503204011040840c0000d0f2121001d04005a040c00390708810030a604081c4002020400040c0176043e04400550407206054085002d41e2300c0fa5454400a00100084968694a402c08551034841d103028a0341550300b020041410340c101491450380100d06540d40d01e06140c1d03e03030a8562421806445101e403031006012031300c480301080c45010f00800e40d400c440c2400441302d4042c0400048010104034041d00407100410250740c03c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 317720899 1250 317719649 317719657
    0x10080f040213330e0c071101030b04060b0705010c1b02060904110307260403090b0912030c01090209090a030905011803050d080a050f01051c0602120f0f09030c03 71
    0x10480d08000070391404030745070004140000e1059144505040c0d02c2030400c0c1c0f04010a003d4003100d01c6080c1d502a02c409500044480076a00000c8060080001e070300442d400098031110342005140100c8e4191082e40050190b070300d036070428082200b00040001c20001c00b441040420030040c2010803280300340b4007428141c480d01c0c100181c00382800040f080c406903201d80c030100e00b0702410b02c040754a03410210001403075014851540b00790801080c00e071004180b002c542e140e100d0f581c19074070340c40801d080028013500c503084482c280da00058000342080d80b2050900107444c1d8405084000901000c081c0104030009c00054410b4415030000ca50420200364000b0165058a0003030800b084400a04008032403140c0441e80003074003a0040a00c0e404100358803107030031809500c41110501282c2c0710f801c0101c071100f50178841e66a000d2078080c0c161440c4034500c4888510761340100c90050425490401d00410203108a0380082602300d00300400c02408050300500390800141c100071403d01d01507016072652481 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 317722149 1250 317720899 317720903
    0x190506030c10051216020709050402090402100203070209090d0e12030a0c030c05011103070806030c09070e0105070b16110f03040303030504081605101b090905090f030301060c0210080f04 82
    0x1e400240428054010012140080e0008403c500c0e00d16008000340c0d61010b0f450945c10060140d4a40054a00e0703141c010300340034503001441c41416841d03640c20400c1e09030720105100158082440768501581d9400c081c01c3c0715452001c00740c5001041320500408406400c4280b600c1030a0345905c14400d02c0c4c002060741d08801e03060034144c40f0b00465007001e94681d2000384004206608066001003001d10740300240d4040c08640e20781c14040e840b403404158492844604040d0410500f4000980176071044489200c195011b06141d0701d031440c0344c3c403001049841100e000c4041160000d000700c0c0c0c554000d0718404030f10140c0000d0300e4450502140301e5100d20443c4009800c05032200040303002d01100c01c04851340000c00142d00f0180001d03e00c1c0084e264a616802850780c0c0745018008030140440c18181b80480950341d0710f4080060801003544010040600307452078520030401e441c022040304000039400b07071440380c9400041101d140304020800243c00d1041d01000100c0b81801a100d9a111250b03410603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 317723399 1250 317722149 317722159
    0x51c1e2a0320130902030d11060723130e0a110f070c050a060216050402090f0d0c030b0408221a09150307050c010b060309030f0a091d190506030c 64
    0x4295502d90101580380310750348680c0180c03000c1000b8810f09031580a511541e2094042c1e03800000300c9081600c00060f0860711203420303000303000001d040c40c1c86404c50322400c594841c00c47c140324061030011102c0c2e802c00d404c4144920180b40061184003280a28660b0003408003009018508002200350828014091103400d01c0750040743e031000300040c019510b4007a18020702181030169980d0002580c0300324042c7c2e0084818080180400d0500b0076000702c07004804080d09142501d104401800800c140740007064429054410300800043c00c0000101e0040f4011429141c0b90700250303d10184c0340443c0680c0c6902c48501c20800c204411419803007100d80e9402900158079850940c0100b5650304154800c083d00440c0003080108158002c2c003d41540001c44000704958403050051250f03d20041e194038010754818060712030041c642000910190415150041440e50340e03100394601d1400240e902c130a03040c1e01d00100020700c0500c00c80d440200391151000c0c80141071270000310340c03910001d000710341c011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 317724649 1250 317723399 317723423
    0x9210506060f1f05040503030310181406010c0309030605010f030b090714010e01030f05072303090c04200706050708060f0904020634031103070c051c1e2a03 69
    0x83e9005000f607030018070000c1c0541c1d90b43d1406840c0c19950107032030f004585403244e041c02c1e85007064805103d0b441840382e502d00442c020392200e400644a141c00940d04a0420a400d50701100288260041034000c10035440c12001d070030700f1072500c8601c01c0c600a12155882d4000320003045030040d0100b42e940c410301d0a00f0b05940843d10341e801200606505010f000d80d00b070400d014005040e51050803100780d04040c030a100300320321a410a05015100c25200c400342507000c503607040c2c0c075032801d41d1003140d8500c1c03d035149106d109501445191903811003141541c1c81c0b0354410030058441c0d00029805c0d4490812200142c0071503540000485012002c0c002074050039000c2000c45c444081003040d00c0504100d070001e0f81d1810710000500e0b0030b24110380b07001c50000d24225010066181c000040d140210381c04444002681d003040148852503c054a0064803c3c40604000011450140c0ba0810b0b5154810340001403042d9410250a042145580900c200030b60000c5001902c42102c0c0700c5050b00e900007000d00345 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 317725899 1250 317724649 317724709
    0x90e040b01050402030c2a070b070c210b010305060a0b0406030b15010306050418120f020d050f0d06090e010b010219030e0d0b0c0307110a02060901030c09210506060f 73
    0x6014003484004594807402c20442c164a80807100007c0c041440c088940060711158101c0d01400b4a420013441c4043c0700c0001c0c40300a4003000750105a042c00003075082a08426241e0289400007a40181c81e076402000034802c1e0b40043c0e005076050502c0540e000c0c800c3c11f19599410500401c000c0160032040080111088160320941115008000c0104140850038101c10115201c4017002c1044030803880c0c1217803440741c960040c900f408185050b41c001d45045070144605481c29813109284013560501040f1a40b01c4410b244184400360086110004541010006640c03c4481d507441c0d11b4190b5000c40ca9220080b00c1c0307070070040e52842d40340c41c203c603140c20007a0105900380d80c0510002c007050100010082c1ca07030001d0b00558850741a40d034422440840e10100704d030300e8440c441800703900800b082107085925400382d0000c8401070f4041c60105156a0349640c91410400580d01440400204034150342c2401800c0140da9040801240c041120348203807400140174441225109500d45040151086 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 317727149 1250 317725899 317725921
    0xb0c09011701060f0206180604021207150e1002010b0306070516050d03020c100903090905070e03010c0e0a0e0c0912120f0a090e07140d090203070e0601090e040b0105040203 76
    0x7400301c5030240340505561100000340c84440e4800c0c0a0b4018460303440080e0746403130b00b001113148500c8a50064615500d5540900400c0c04416200c00c4103445a00c0000500d000d503001d07500e14001081c0d89441114240e90304110248020407541d1045a04182151030036a0300400c1d16604101241841c5580f401c45160b0031745007000c10311004e012030084600600080303030507800400600d40030b0400d9030441c10305481642c0c01c42d40c400c0706c0500054010f0314144106034031039109540042d0705080002c94541068002404e641c181c18040d00000d1405140100300c1c00c0600000001e00306042075400d140c0341070705101156004040030580706540f42cac988003401c1e1000340400141c00600c001920f40c2e6138102040840a5486003280c0d4000503509000060142c440c0203980d0b00a25140d942c1c0003134011901e80441e040c1d00949000c4500f06c1e40d414181c0b0041ea82080341d4801040380e12461119480c0440c00903084240e5a8041000c4031030f81003c00c00010f40802c102c0341910340c1120010707280e49490099271 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 317728399 1250 317727149 317727167
    0x120607030b0301110309030417030a140703030e06150a06050c1f0b09131a0903090120030705060405010501080d09121a01030f2d0f050c2d06070b0c0901 67
    0x4c04008148a102d11010000f0015107080c0000b4502c692955106a982c03442550695030004040c02d1042c103428401e04014500240030b840d000c00d00c89120740081d810204c040d180c20401d0208424154000e0030401c014500414503814401c0c1482009010035440e84421030a02c1c5200340c2e000111400041c039030307000c03844a00c00501440c0b40c44c0340010f149481c6c806544425250380c010080424031017690140418070504000c0d0185003402480d000560f0744440c0021a0080302250040d0140901c400708040d2400c580120001c00c7c035410f090400c1421528181c200c080c0303a4015202000345a50000d51100403030341810203241924019043c4200180c00760440e4007400100ea0000009201c5001044014103000f0304008800007440b010131308090000b114846103010f188041035012510b0380b4045061a4021002d84420413001d0000130143c1404d00c414100c0001c81c10031a0b410f0541541403240300c21400c0ea05585404125203403500d0900004202c00201d40c0001540310300790b4881d150328 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 317729649 1250 317728399 317728421
    0xa0f05010b07050708070b070605130b130c05090403080c07080f0f07031206032103091502210426071505091204051305090f030c0105060906120607030b0301 69
    0x100040d58603105452a1544888001c3c1da0034400d89101160365003011400b44115001040d241d440c0032403507a0340b50b001c0e1200400303960300202c242c130300c040214050420f028801c000c0c006c0d04d8411a180303454000c0e01d0540c0340c2c0090740070300910420000040e1300b0202c02500300c50b9584045482d499907103408003084c4100007000d0701090020594159400380580980030030b6109842c1c1610001c000e401040c2220000d1001034108010009044070301600f46456454806062402046520701500d541c60400d001c2c0b2443e0141c0c540c0001c00c9055440c1c4240c0c650708408071400101000d0625441c1c0c415011403030401d03442c031014a985014148071050084510b044c2d03115420900c1044428204001010100c5005a042c020702100b00e600300380950868040e940014802d28a0300090110078000b008010300008151203503138858a00001c0400190030355011400001c5400d1400c50140070200c0405060140506115600e070b0010318008500706501910920300080d00b0f98240000a001d01032010b49 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 317730899 1250 317729649 317729651
    0x105061309020a1512051602060105010f0c0b0c0c06100303052502120105010e01080f031806040e130201090e071b210e2b0f0639260a0f 60
    0x40594820b0700300c17207003030031544960f02c040000d540d411040640c50502e02004a0060b004a00107120540c0210001d041854003840c141c0902516580e8180002d141a108a01c14400101e000c3c18001010020a680011200d084148492456902810030300598807102d03852260400c1e8070320b051424800000c0314075002031032130200910040304e09000700303028060011a01d5030803002080c0c81c100050403103042048003004601d400b07008806110280d0702c0c05d416580c007001c10003000401c0b10300b0030b62160040b0710307501741c403001b060261001414108081d4401e0000300c100c40c003045043c0c1c0e003200c4030306221600031218400c0d0780c103507140410341203640500f0745450301000000e07002007076802170010111040a88060000592039481d035508059082c02065100019850b0500060b0b030f81c640303401c1814482c001c00308001e03a01200a1031240e50414018806c0400301c840660348902d03007a5090380b40c0040e81130941042c404004203c90101503000c0135055007100ca800726482e035495a001801c2c0c3d9a000d10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 317732149 1250 317730899 317730929
    0x806010317070803070e04050601081603020309010e060711010b0f090103080a11100e0c06030402150a03020906040303110c011107050d03020c0d0501050702060f01061d040e070e0709080105061309020a 88
    0x40181c201244140554051442c2800203250ad5000703001041c05100340101d04a00c84034010000c038043e41c4018817503c0c8030f54a60081103601d1004101060144240352600304040f100c0c040e44d5403c40d07803424007191007a104005142d0460311001042410369070044001641c0300e51b04481604d0981c213850039070105205111100240e00075a500c100c100c0c500c403000340c070360a2100d101000000d0100b0303200a503005002d400040602c150000c000c005218050801605044000c0000340907904241d0059003c2070b0038a8040d44200f40c148000140312000b400c103441c2c0c290b0b00744c1c513656582086000707050255407a4407000c03041c18000c014400400d038004100e01d0f04105c4a1401074060729080d03441f0b1015100b00004961610000382095050755000d0340c40081601206142c51848030814550305d40059460700c1c3c0003410b203001c0c005034014207582a00e0403214100341400a10210003a8003ca0007039240a05000c0da40e80c070a00d81911584604902148041c824000920f0a4955500c41d400300e00600c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 317733399 1250 317732149 317732161
    0x10b0f07051015080304230d0b010603020d0e010c090311061209100c050307050901030c0c0f050c030618030d020921100c0305060d26120a0e070806010317070803 71
    0xf400c103820341c43c0201d0204030400e0f6034406540c0d882c099401744118010000440b9591500494500900902c0050507001124801d44a40c4c052540a800031400650001010b40d03104145012314003003888400000c0220192a035002010a041800300601030703051211030f611999100020780d4500c52401d110900c4a0828014007940d600f0340c40c5008420301c0c14008058080307402141030b40d1241c990b584500c0d24100380000114000d003142070080062205840c61a4007007038101844541d5644104014801d81031028101441c02c41c0c020207030003002c0300103074044010340404800c0d40c1041e00c0f107440c0541c0b00c004c41c0700040c0300701000b00340f004120300b0100d00c2c00c140c10000045103415074842c0481040500610f41e8202c00b518021964180c020465050120001e0f140030b22014140d400200b00c0511880b00000781c040355408001c0c07500c0590000d406120100340584140d07c01e41c40750340000c020a500d06196a41c95100521000c0e1040b1310032a006070b8112a40707412500f09641c4441081e5907450b1070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 317734649 1250 317733399 317733401
    0x221104020a0302040e0109060506071704090905060702070e090318030705030d0903060c081608041113090c0b130501110f06010b0403030e040603031202070606030507080a20010503010b0f070510 85
    0x10344502c9001d0340031070000041f8000301e8880c407403c1da8400b501540c581041525040300c40c00c0d0350540502486020030000852040d684508007182d48a040601801d00745404002c0c50103000390440e48003c44540244840000e0002c1114040240052101074244984c400a41441c41951240e81c05010300d801d6140c0d0b8942c0400d0101c10780303103e060200304030036595208444c0f450301210fa015149216014861a85003c1c0d021950311501c2411a1300801441102148441c0c03c00501c07260901d85401d0540b0401003082d072082c000d044038411403400c29204460301e0742005554421036041c0584030505182c00760b01402601c181c004644220307005d075651030743c1c1419194454030054000890000148075103142a00030801201e0700740d80c910322600800d4803840000c1d80310807411140c0301d95441c0000f000890500102c40140782102c05068000d89600342010705500c61644001b60904002c07030725145a8004041d01e040d251a4500c2c25100e0b0044100c8641070310442401130900d215840c20348a2a0440d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 317735899 1250 317734649 317734657
    0x1121d0607271811070204090501050108010b011103070f02031005151f020d031a1903210f0f1205100611030a050904091b150206010509221104020a0302 67
    0x40b1401c94000800d410503511a0350501c0e004020004241490b400c1c01002240c103c03040e40c1d1450401c4619055003540054100d6640031000c851a946074801001800020700c03600500c00c00a0804a082203c0e00040544070302c6105401414240a20010800d5450411030b050705071140c0d0000b0002c5050205003540b01207050030101d44190040d43c2a120a40c65400d4a94540350483c0c0003040c0110346d00301c09401610390710440b942080b200c0c201141081c2d841c40c801d06905909100001c116600f541400c00e1201c8182182d80b400d06180c000d1b449000fa4000c0d131919001e20b0500d400c0c4400000340a003101c0e40c070003010202902606081c18408a05861a841c01c22100a5140d0350180d100c0c5a218980383d000b1800160040755041c42407019605198011401246c800e112503aa000321200c0d201c00d03844041c1d000750031000c65100356240d40980400046014150844030303554980f41800001089001c80d4020703074594035410208000b00a401202c495522800900079902d4040d003120040003900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 317737149 1250 317735899 317735927
    0x1d15031f051009083f130609090c080405070e0403020a08190e031f02090406091103071209021f0e120a05060a050f06150706021305091501121d0607 65
    0x141501752000440800344031100340020314020702031003540031243d03085002041d0511204020800043c400c0e0b1809074912000f501060f2510107002e4104441c110860b40303100c00d80d1040c05810360610010070000180c0008031120f83c02c2c091a281e5681ca4200d0800c9003800c00107144200c042400140c43c1840d46c0c00d40040c24580c0d981140c00d809080802d03a4075032004448211a0440c09a00c104203031464009180c1c040b4090000304e40a03503100300e2401154900a605000c0d01004024800c0c00b5610003001c111121071a40305002510160700018911003144445a01610040f400e03002681d014206000045000078045000b080044000c1a01e62486040803141c50040100180c156242c910409004030f0380004801c0f01c1d035640500b8420407849440240600e01c0d8248400400100140001d10301c80c4107519542e940e007450202481119400648040101d005079180311042d41d9120030110140e404c11003002c0780ea501e00307010300031040404002c40d10b0180282010003580702c3c1c04c01c662200c145 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 317738399 1250 317737149 317737153
    0x512130905060d031b1b030c0e0c070b0601030203040f1704051201180f1a0a0b010f170a150302120c09060117010302040f0e0604031d15031f05100908 66
    0x16a0700b100300095503544440c000c0c00701d4410900701c529050641d400108482c07050300c40c0742e520104052601d40c03510081e4011100c0c41c02c40c50040c445982000c40c29500080c44102107410400c1540e1105015030b0014901410507501000080501a40645a880690300841408030380c440c401902949a4054013030a400b031060007600d0700401d08144114540c800c205c03152400d001d001070380c900340301c2c2c0801002991980350315031a9000700265004400d0003038111220000c2c44165010000d07015030f8082c840002807006a4412070f2481030200036480c4d003c843c1c110001441000050011083c0c0d0540d0400780d000148010080c06d078031000104500040c0f0110f0302c0c15102d42cdd42400441e0502d03040b5501044401d07624004100605040d042504088074640c2c1c042200754a181c191440c10204031400d1f4002086070224480d00f0111030107140c205607054a5510903031590400509142c800500800b8148001c00c107103a0b099404d4401c07010240100821a462610020300014010b00c02401180c20758 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 317739649 1250 317738399 317738401
    0x308071b0f05062406090f04020702060a020d09090c0203090904020a0b0a031a091306020901120c05090103060b0408070b0906040f030312050a05190b0f06130e0a0e0a0f0512130905 79
    0x40701c001e080c20b0150f0030b4001c045615120440c4141f0403140c07513040707a03160025024008400141d86080140c0046c804a500400e000e62100c1402060140c50303a000f081c0c507914005111312281d50102c2107842c5244107030f844c49e98a44407440400c80e0032645600a040050000c2501e0403c50703855005804200090b990000c00001000204000c1800c203859494107182100e03801c40c005022500a0302c041d4005050215000c6c03e100508030a40d09021b449400041c00050041000c1d03030580300315806003880f11800c03800c1508094503640e45010501807100c0000022503201800d68807501160041e2400303681000906a507858080c140341c420121040060b03003800000346000c680c1c1d20800384110004c25039103804d0540041030130005c0c03204840581e04202c81154107034182d25400d00400034011007485c5c03c08800d01d840c1d8010031902e4041c0080c000c503414001c1500c840200082e118840907002000001d51044c10b10f0300f2032078140c01c112031648035000466085040c24503061840102c400c0d2075030500c02c3d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 317740899 1250 317739649 317739691
    0x1020a02010c1116120303020405190e07090806070e060403080d05101d04030507052410050306010b0405100504180204030c290a03060b070506071b0308071b0f0506 72
    0x721502c80d00344440054410401700a08818400a540340601074103005182a85810105e0880417111604410b520071a170010002c050015040b1648034110703240005100d400e25407103546541d0081e22100422502e81e456207490386d180ca04032401198418107c03640d0b40055010700010307050454401000c5402100c0000e040c444078211482d0380c48005061002d03503a140d0340c00b80d540d40c1020400340c0d005e01c520072011000d41d4001000300015200f51001c4151442e0107224410000381a0700050300070740040d0010007490721001e050347c00340d410880d4461a01e100c1690308440c82c0c0120750045424400720a812450045a07038001d209076402182c104022685415060720fa0b0421072070006880c0700d881640c86480391503400038040025151401090082e0741d05990801c41e08020815500354124005200030560846141002a11080100c4502c42c0e0140c80280442e80002c0284c1d080c094074125148005810322944551158005180308551006052183e40c5940841d030100d8141840821800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 317742149 1250 317740899 317740903
    0xa03210206090309092203021011070b0f040f0b010f1a0a050a121b05030a050f160c050c0a08030c0c030c060d150e04080c010b060a05030105100c0501020a02010c11 72
    0xc4aa0408001545881c9130070003403141d0b00c40c0060019404036855150013400c10701200d48409800d02a90080c0a01c0c07100b1079001c0215401592002c071000e0341040601d00085102c006031340d201148407040b607660741c1c8505082030313414040400100b07511103120020a8148540d6028410341d58078403124001e0070540e00c007440b5503110b01001305010440601003c5c2d1618440c0c01078075206603444201007149403494a01d00e20703c200a082e00d4000c510701008101c0010030b9440344c240d00c80c03031801d4040c0c080c0c101030900100d061800790040081242c182581c07800e1140412500000c24009810503003510342c1c0f0fa0005440307420448451800f401351103502102440d0000d408090440300400041c0b802d020218488000c5c040b449407105040d44000000404075690f006a070721803402080300079501c200341c5800d9403c40398003450703840c45800300384900f036412640441030f0b034103440c1305a4148000100481040d522080b0b81b0358000c009600019140503901c1d41034210040d030100c540c4915411114030b0b10017607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 317743399 1250 317742149 317742151
    0x6030f19180813181a090103020d0f0602072414060307091508010c020d02060705070c140111100605041103060d08030c131d06190306020f090a03210206 67
    0x15015590580e0010120b506800206841a0100c216082d00e07540c0d1310100d41c134000400060b00d0200d076110750150103028090fa0700010f480049800d18055811075000070020a0350a00260002400124002c00c02400340e040700c040a4024403040881a450740c031244210225080d00d8403164240030341c6649a0201c42410f03070003003100a024081450900345444000c01e01d400c203000041c28868000030740d001082c4941142e185103030b40600341d500001280a40b90040240202c410044108941030128000408002c10380d100c000059800c4a90300d80120380c1d0000c80d50900c3c14900425500102490860b8400022204160380900c07a810350194005140e0100300ca11176003000784243c44000242808006542c4003803020605801c01280000e861000700c032070f411003180c000038003401a495500c4044002d50182040306c1000369810411407058241c541c6201c01450a9008a02046042e682d0000d1750074181d00685511440340c2d4034101444000c0000d4020f080d80c50085482d1122035101140003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 317744649 1250 317743399 317743421
    0x15090201120b10030213031712070207181802060d06090b04020f091002070f0621380d230a020d0f030e04061518080d0c06060506030f19 60
    0x304140d080f190070f401030b40c810300007414100f030b400c0408000201c441caa00740302e0040005105031a55a01a5840c00e6600702410040c250740c4640020081d10010741d480781110a560500405e144060341d40c00048003000190080d4819408108a01c46141ca40e0111040390030304030040c01480da000d005e000032072003100082d24201800b0081400c003420000d4040d810100b0a1040f249856914518040e5841d51904018001a050b40c4081000c0031301034111009045030510400c000410b01c1c100c4c07091501f00d850752403064a05a03507060b03484c0301c1740101940042d002410780c10450105142c8169070f81c0468005064440707854040809210000540c440c0381c43d40a41303100380340380e40c030380b15100700d8440074404404002e200d00c21070748251a54010b500040a07084010070b4100450f4001900364a0241c850b86c0406882072010003601800041d903845000d010705216440a826050039000340c01d4980001e0340090300082448111801c007041c49201d0444541b20042d0300310381858600980e00581d802c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 317745899 1250 317744649 317744659
    0x3070f0f0e031e28060608070f05100210050705130e1506160203100e1507091a0c030c0c10030608030702010e131505011205102115090201120b 63
    0x61146621403982c0c980391001010442c0c040c40180c0002d1138905007102c0111a44040e001550000c0045502035240549054000343c1422410907450441703080392803092a100b4001041246000b41c0244660b44814200610501091408100152030303640180c403002c0d00280c181e04001550340001540b607000d100f124038000041d02108042140c41e41218081075008200c0c00300c2140181d400b04031044164007681404101d020070448107070305119485141c955030422080c00c00c40b010354040010425244400c80d1084047e840d9907034482503018102280c02d03c1d00c400240c000100400081181800c101183c00030659109941c04809842581c442c210982e4028410640158060b800c2c2c01031021014000083c0f088020340c80d0020799607680c030040c0c03070841c0c4e10f10107000a50b8003504204501f1605103051104ac180802c84007040a030328400c044203a01c50b20302c0036196aa074019600107064124806001035070078400200020b100f0071030201e020440040382c158000d401401240d4042d00002d00d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 317747149 1250 317745899 317745913
    0xa021015300309030605160c14120d06090b120c01031a1309110102010b010203031b0403020907030501060e0a23010504090c020307021002031213031403070f0f0e03 72
    0x4552074070034080011801c6010206110255601e809458440e19806680c0d44004980381d400d0010859601826030796511003910b0034400480c3c0c100002d107908a90140c1c8074014040101c07051410030032900808489513a000410804041aa41200060710104d50782084410070030000c004680c0c0703036107544042940154401074410740c000d0340325550894041c0c0155240310800030001e2034080d81c0d03045c844c10341c0d981d82c01001b044c800311031000d42d802a42800200070444250002039030f83d000091070390781e02401d0341c5d0b000b105007642c400a4500442e4041c01e030041500b41440b010b4050301c0b0074040c2c107002a42e4074010503814689500b20100b29007001c4841d044800e6010ba0002c055100c010280f4180141084002007000c054441d0700900c4034554081c40d22060b0510400c0030b0079400b0303c003110440d070040c4060074101003050700094201c80c030301c1083c400400e01c0386025a08400e01070442d074410070003c4100507400c2d400841183da0195159103610450020801c1030b40c040300615251501580029 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 317748399 1250 317747149 317747159
    0xf0b10030b090c3a050105040c0918060306150314070f031b0506160b060d08041701090804090507110703050304050f0d0f1b170a02090414010509030a021015 69
    0x1402004c610302d14007201c400d01c0c484c21001c100340e84001013504400035600c5403903440c94280e40c800c40d809003c045805000144002070010924445e0f40101120050f200319407a14000540e8400b80007141e12580a000c05102030032404140c901d2440103940c8880e903580d0059942c480494400309480c10b04034200341550139900c502e07100e03248807100140c550001000100d801e80e075030405808002100b80360302800b08114a099071034002c01802c0c0500402042900d800081c500c0d00c240e0703042e14511a1a189083c070200501c1e8050002d6200140500c0b00000d0013080b0403442da000140701b0a010307240d003415403032410701d03003580c0c1c5071039200190140e00207000c03c1c8070318545600107855054008000c005505400c1e21800a040e10140c02102c0b00458110088a40c000b01ca1201d00100f902c0b152070710307028404410300d03920780500900080c46008070700009030070010102d40740352087d004840200712030b141030412650b580e840100588098403a0a45140580c00e03140a03a8609104440300301940358500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 317749649 1250 317748399 317748421
    0x50a0f0e160512041109010e090705030102031302010810090207080304021008040f0212030409050915070504030c0603050402060d09051e16050d03050c101b0306030b131103010f0b10030b09 83
    0x2d0030031a00d00082c5030220000343d90300b001b0036000e4010404485554188118024540425540018004c2c1d0050040000b4a00e56520181c2540d07028240b50820345e5680d60580c07504007050300a254001d00c080742010602c103910018510592003a5000c490000010806403200c22080310014030050600e117040d4014108404020b00403040182201e0420340c4511540042e1142110030480e02e43c0000941c00c9005001d042054000e202420110300d02400d40c0c070740f0300003010701c1e001b02c40506489001040031515554215198910304646c02c211402852501c00d03243c031500c8000300340700c004141c4081a0341d040410294039107104d0b0320044058901d05024000c40441e41e040940031311405000500d03d00600340310030742800ea0001c50000c0c0010180392400200342e8002410700c201403604201740009080018003540000c0068401d01c1429014544426001e01c0c20500319099401c01500c8134448080e50003c0c1000c010032600301050b00300c2d08204a040394200c0a00035030048004011503100b004c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 317750899 1250 317749649 317749651
    0x3070f060615170a02071e140a0605100f1a130f12020405060a1203030905030c010204300c060c0212010f14062e030605100c0302010c11060105130204050a0f0e160512 73
    0x70908c103103600791825014141c11300c503050b9030507141207072130300c1c02c004c848407d00300000064401d41e47c0f003125450074041030803818206100240e4200c0b0000a1113100b074403808a004004003024044d2240c0c0d07944440c00c2520400b5141c104902650400c070101d03285140207402e500a82e11001d0301c05004407403581b011005003841c4502610700740010801e00d08030080030b0004101400360400b60410400038403500c0741c59454246c20b80c520010031448400c000544c110124000c03910b8610740640c0701c41144c000100c08142080e5014a00d42c684007004030406020f410040c04070340500602d48150f5510402d0000900740c1000281044140300001c01c56010301d10109440003c45140c00107000e80c660010441d02d404061901022600c0080072908155090048001d8000e5900c0d2069100c0b0205096654400c0107025440c410110340c2c049842501c0b650703042e00c1c01030200510229109a03900034085050751507005140000d140340300042c60102c181c00000100380655541c0310300c4c00c10010004442080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 317752149 1250 317750899 317750903
    0x5030a050a051308060405120c0c090603101a03010c09030206030105091008010603050615011b030509011107090b0301060e011d0a0f020d0e0105100803070f060615170a02071e 77
    0x50070b10180c480300c0c0c802500040540000302c0103261901b011305056103001e0040d10610b0000d80200085481341c03070f0200b88901c400c4000d5034002115180e02c4002801e2100d00840000c02c5403800c803040041c0911512001020501135000700052022102d040790410554000039400c128104010040b50501c180050360024900e85e05003a006d40700d0603410f007511002e9006903100e5102c035087c000b081e0f400e444580300010b02401d202c0080c40314041005503d030a614800303818880041081146a4000d00305040300c1d0340300c0820b5801d019201d88003180180413941a190003586003940100c0d82e10191643c6034142d8911201e2051b505208801140d400040149103003001500c0d419042201821400a00340b03080044801207806009540340a0841d08014502441001042000c015580b0048115441c1d650000000001c02825082880203442e659200603035161401014424251f8814400000c2c440c02c1c180e40205520395854403420384c0070742900901050107541c1d81c01140d4070400d00130002e00d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 317753399 1250 317752149 317752157
    0x2006040b092206030c2103030f020f0a0c150905211204200a050d0303020c1c08090f0c0f01030b0d0b13060b030d050909070c0c0303050a02060601020a05030a050a 71
    0x6555202c44006a81e0410311a07038000f41c441e039003403003000b9a18a0440c0034041d9840c034080301403080d05505070807035900c0d5009424581d0740d070302c0341c60007201b140c0407981d0000496055030307a501e0340e6034001070010b01c40010698203180c0d9070452007107166080c00b400304010307086070041200307420000c21000c000300300300d29954401000b00418046008140520341c4201e000e0480c24600b0403036681142010002c18900c07900c0307601003480500882c2c0c0c0f0742490402290f00741c6070050301c0c0c900b40080035281c00308034000500c500070b054810102a5610200345071040307800ca8103503048401d241c1005984c079035014549513440203207001c8410880d48298072150303240800030300c100c806204a45814120400c103468554121440c48041400e200a5009030042d5440950060903aa03c0c90702000780b45000350a4414070a0040c2808901140e1013440d540485a0700880c40804069a03071078007503c43d5109000d80d00250043d03030005066980080b5900740b8854005025520700010748804503045c1c0d00c0500f01d81d0601c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 317754649 1250 317753399 317753419
    0x90f13121803030f0806030a031e1202071217090715030f05090d090e091b0d1a0618091e0f06090a0303180305120406180f2006040b09 59
    0x1140c107a9024100550194540c8041c000d1004002051450000e20b124002e600000e00040000d5001050746004d801000d4030596030300000e80110f4080e010341a00ca481540007003400000c0c80300420301800360403065118034010ba07003800d00c001a0303490101d60701441c030742140a0402c40c40c008022103100200c0366240007d10014000042e400b240d806880d0001640d0285440d0002103412203940400350001034810701071071801003802655000c18420f00030380503918110203d002d40b561044040400c1d40112494245030310681c103824008000c0700d0441c8a9003209242c400040c080d04103540c020307030410303010b4142c000781604d010302240d0090b10403107154415030300101000d80d02400990702800229001c2c101c5032195040060640b050891030350030004650310b52074006900841142d50850050440752120394030742c10542c4c000c019880844103044014a441800c012030303c0140c50a4030b01c6100d48001e950303030400c2d940c22400d6683c540302c4c1d0030280800c03040c00f803654801c000e001e0f5004014100254 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 317755899 1250 317754649 317754677
    0x803070c02060703020f06100b0f0a050705070b12160f0819110306150906030a0c170403030e06010e060105090f040e0d0801080d0507020f090a0603060218090f1312 72
    0x2c0360310148081d0016000b0045988007094240409500414066074803010305041c066030951900c40c14100305910b9070005001f0030103d0141056546841d08102581d00c40c9580304a400410f501000000c0001a028000501c00118611101e134594038143d50b08a122050b03000c3c2900c0311780002e840800343d42c0440c200048400a14002c40008a69180b01e0030385a0901800380201d0300b00c58500e1b403105a100b4011080192101003d695000e2140da82c049500e02e40e031102031340e01c540410741e026a141d0400c0204000d241e0150001c0454105540403621642e98490192041460a4a1203400a502001411300d540381500c0d5200001400502c0040e008c03000002440c0f42c403190038a00c50200b100300c001080940c40078005950388007203604016142c61130302c0d80016006441d18564501c1550458081551010340c0c1e4030280103540d00c0001196120114004419480307145a58070388942c1c0c42d800080c0d2000c0f1754403c0b45000302d001c80342041700e048540c0e5507082c0c00320110700392000b00301010181e555 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 317757149 1250 317755899 317755909
    0x40605060c07050102060a09111320091e09010b0c0c09010603050f09010e0d03020d020d0f1b090521100903080109050606030714090f0d0b0108190c030803070c02 71
    0x80c5151001c0204081031901001a0400c00300402e0350020506c1c01c00002c01007101c04c84941807107142220120110383d655001d46000b0025a8008901e05408801e001c140e03005900090080100c120b03a486071905440b003c0e80900d821901500c2c0c1c002c111000100460841d00d0060060303121010260383c00502050040b0b41801e10136404400040d0301ca40520214008002d00f094020550b000280308012070424450381c0e820081c2049801c140d80050401d004030941e5042d02c0b071041c0b007850180301040701c2005c2000580b15030030820012245032041c62018034050001401200c101801e120784140740d14147c0261442046000d00190103050400c4000110b81d20808c00154840d0b203800d0210750403d201081101d200400903400b40c0720420500c07114540002a1894402d510b280b090b82d80c0c059200401c1406074031854003a002205d4448000070014405083c5060f034807102c046444510f54284950720006040b00080c00a01078a1810300219151200455000c2158240321001c0015540421 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 317758399 1250 317757149 317757157
    0x9151506030f01050415030f0f0c2d06030b0102100b010e060d0e100605060d270f050d050a2304030b15090601030c051b10020408030307080105040212070c0204060506 73
    0x1101c401c4070b0780140518503082c441c0007031034041c075400b214103141165215040f0b22000341d805801d40a034410894100500100120080c180c40c540c03010b4454103014400d400351441000c200740c04103c401010944c81d11034810040391035070590041c808001c035080d00000a00c0c2c2509182d0405c01080d83c0d0945c2c1d61a0079004051020b03c8a00020b01011119062801c0503410710054242900b0880100059034821055a924040104c80052081e00100c40003484c084001064407400f1004e10a0806000c0d06042d500901c13805002035628000c0d00c154100c0f050b102d401c10150100d01081505000002440701c26495900707035003091840d003500d0351280a001e0030111007040380000707240e4021402d030900c0c800c501d410034421b00f010b2003120303c5114003510038043c00b6440180195400d07488590b0903800c0021900d04102000215a5a070720fa0b4202d0342c0380c0c0c4c01159940d010402d00000080c01d810a4406c841c4a1580b051440105032a100c40858142c0141c40082e070780691140b20200362941c03608010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 317759649 1250 317758399 317758411
    0x5130908030c0c0c0303070804030303050a0b10020a050f010501080a0b04032a05010f050613181a0906150102030301090507120c08060102070f1505070201020f06041b0e0915150603 79
    0x180d501d403410443c0c00383c40c00b002032500c240a0b030401d01c07440c13001900c80e00a603400d5079410b080114007a51200e80d400d0003040b40d410540c1d400260341345210103458003c103886900034096010307590420340360302441e820f8400c2032107000c0040d4440480a4003242a0f00c041300e4000c0e01c2450b00c100c1400c00d452071218001c0003012612198076950081604000e001d202d41400441c8060013845540b400b500001c560440d82c0c4462508141c50f080a521111511001503645513400351301d009220080070f0610310100022600c10003107214a10100d442c1d0140b5015842c6c8040050740203525582c01c021702c40c000f400002d8002c009006100310280d4404a050080c4541c140080e0344892181ca048400285000c1c0c959020b9403404240c41000d20140c4001d042d107110b006000c0c2000743d950b825920040b46441584092000a80520360034881003200040c02507d0030035505240660080d00c8261542e40c80b0b0702135443c009654012022002040049068981e0142015013440c024070381c90408100154011210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 317760899 1250 317759649 317759671
    0x3120e030406122a030e030f07060b01051801050702012109060501053c120c0f120a0b09101406090a020c0d050306040609020a08040203010c0e01090513090803 70
    0x20700c18194001604000f0a054200500c00c02213141c030502c0400c40b0124801c000c0b041c111083c40c00c024066040301c800b195130f171812255104ea800728004010382007140200c40c030508000701c1206079032203942610070304a200b0010800c00301c16a40103481c04e9203c850b089050001660007005200080500c40c814141c425102103444889032411000b200e405800035803040ac5407420706421043d80024141c8201c0c0010440c80c6118040007a008508070103200e22903200c100d80e0314441c2c004c000403071048500642034408000c280724040800c8008094420b00b018698040c40b421004120004c0c54203820034070321401c0e14007202150b91648240e46040043d44142844541484043c1c01e00701e0405602c1a650041141000f940c50380180c2c0390103507030f01410100800440454080c4c0c1c1d503644a08000d2905950440d501c4d03040b4031000c1c02c540000c6605034403952071300c0407204a103400b555101c0f0700d0340c03016554526901d0400c1e04020840c0052141c041c5525954800c550003c1d040000950241d608110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 317762149 1250 317760899 317760907
    0x605130506130507090326030103030215100b030f040c171608070308031603290103150e060d051501080c0307080f030d0f0902130c230301090903120e03 67
    0x140180b4100707401105200341e1030981001030311a44082260705417948580c1d245c140301c091702850801c00004070061a0a260000000010140c00091080020080c0c03004608290780d1003409000980c40e606c692075081c041000014800d845110316035501520500312029180d0b110101d50301c1c1c08010001202a90b8082c2d5900c80320030090100c29401840d00400803c1c40508540d0380e0f5449000182108500035140d030f103003401c2d030381c0207070406800e0024460381c884451009441704240c50900d52030305408203140407120006003140108140948142050300f03003446e00c40300248900408008401c0da800c1c001c030800220380700c0c0400c5c0c1c4a4028000440100f02d041f0071002054200f180075401141c0c03682c440c004450301d00c3e8021041c1c41581c89a03030000607168000c0c0c00040301030905598003d50186048800c0000e0409941c00b54191500c0e0755903031800c007096110780a10703020521141017060300d8107200405c99910785400c1030240340d00c2854060800c200d6580303040280c0313100c018007040c1608045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 317763399 1250 317762149 317762161
    0x30f060e10020d06081902040207050a05030c01061406090f01050c070321020f190204090809180106110706020709050a090c12050c0103022701200109050708060601090b0c0106051305 80
    0x8010300e130103881030070041c14000340d21390940704111500e0b2070300030302071030300403c0300420f01c282803058031078064010068940e1140351480542c002d00c480d004040c91151410b4a00d4220f0074000c0990714100030107086074460f000340000555282d08101c4030700c0c80c544901c00c008000960180018440c2426002c2c511800041410780a400e0905d0300c0340840d0594424031031102003000010b0b0206080c1e8043c1c41c0012040900d0030440a20b1103481401900040021101c54620340030054070350403a0016521030004051442e00300da21403609200b2040181c1c07050509100b17040341e5911090300b2130000030001031040c079a03944200500e5280c3d4003080e09003401c461a602441002c0c0044040d810091904528280740b10745141c0e507142d072000c100380344250443d100b5a0300364003078a100016010624400c00c0e90030407101c0d110740a803090010880b000d01400c0130004003410b00290503401030005844d85100c01e801d09031042075582081d40c2d00712896403201c100040507101c0900d068040c20040c2e4002c14240740c02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 317764649 1250 317763399 317763401
    0x4050108010b060f0705030409140411032409010603140303010306150e01060807170a1505100203040e071b0c06031b080714070b100303110c0a030f060e10020d 70
    0x5034001038280c2d06015148207595120411180d94a29401d00191034104a042c100c2c9075015540200c003a05251049a42d0400d0001c0580c034459840340c94445e501c00b40701005d250710307100045000e541041d651808041c0356424075030ba41e9409001440002a0544d49481d9142c2d4990741d100f080300d0035080040103000340711003801003c24044241c808031221520380032500001180521a0604200444000c0346180e03200340c00c90150a42c0d0019000000c0c10105050402450a6a4001501030740a01c000a890903c030a140198194580180d4202460309207504505007004180004201d440c0c483c8940d000070707003100c49544074081d0540c0f4034074034100304000d8201c3c2c580440442400ca10001410a8607a100640c0703580500c0c01e00c2c0503c00c1402c01000b410f1b140c011280d00501841802d81002036031948240c0034001c40780a6070768052010018010b50f6100d000050741241c20a2140009102040304c90584071034291203140e0006582e5400c01619081461540e02e404c1825000240c1840003041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 317765899 1250 317764649 317764651
    0x6080108060a0b030a0803060102010212040602091c02180402130e150702032b0b040501080606091003051b120d030606020d0216170102070f080307090f1419081006050405 75
    0x2e10740d0420100c44803000196444180c0c82c80104121800400241780e82d1003134040e540001040010b141c06414585042806074120704510342c001c00b40b440307140c03883c0e031891620040007907001b4114617100032952070105030840c0000c04c203980208038443c207030050030014428401c2c4a11084040d0100170020350f40b03508100c2c1c001e08200210350091044009105001c002d000044408807080024001541101806848400b22480d4003038603100000900003404985584540021105401075548400c910030050449002c0035119910138450082d140450f03101402c0c603403d0042281a4040405011515041c001c0c3c8040000a03201c40d4200308041d0100400305069080307002510040c0540c50801c08055000d100c3d203580300c0380081e1141005802981110041da03000740289221440383d0030710900551042d80c0c0040060440340000a8a000800c03031441543c6a030794128a01c3c410308400c01007a50300303455480e840d1400150002484c09010008400340c03072800180401c05900d014100011620 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 317767149 1250 317765899 317765911
    0x120308040c0b0901120c03110c101d121e0d1a030102211807030b0403080105100801060503060109050306070f032a12110406110f0d0e061b03040608010806 68
    0x8000d200078645030b80c000f81e8a603c44808000c0000301594500407c0300a80048900d4401c02d01c3d000610200140d00400e1f90300d88816150b409100720078121200a00c400c01c07111707040749d070b035001402040100304003a001815641c000b5000301d0108018413100c003030305500000301c00a625a4035420700c40d030071121103c11400e881c4120002c500b032200e901800e01044500369100300c5040c0501d40000d0945c40a141e000700c00443c48011100341075180d25082070010030030780d006e401268405000042d103103000208400c403155940d507095040d9290007400e9030207070006040c060510602c1ea401142d962410499240304200780c1da14482c000d20701035005130071500840c0340740150220303421740c01805a2030303072035072040040144c544410000d00c0303040d03514020321008191910013400014000341c0164442c040c2c00d05044c88100b51042c01071620f1442d651552810a21008203a655400b11482d2400794060080c2c8440780a030390303160714640c0529500b0750303019805c03150100340d032500180030601040142c140d00c11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 317768399 1250 317767149 317767169
    0x1206040308150a090509060f0a06060e060703050903060c0d0f050411010810031a0a0b0108100b0912010501030501240b03040f060b10031a030309010504030615120308040c 75
    0x810552801891601e00030315003104038440007800030241c2c451080250042c114501d04020034100300000e0f50b113605d810394280d40254400804101070340020710a4104441654852913201c0d84400d05010168106030015401c2c05070500c43d61810f0f80b024402e080c4a04041c0c100590340d107211212400031201000300b100749191400080100113040e82004021000090818150940d1900304407104181e19402c0141102488001d01640c4414015510700a00743c10f40705002e11f410000c01101c1c604012640103020b5100071104111030301450008140c6e450010f450035400c0c05406500394290f913404c1e8412901070b0340d1407650745540240c190800b242c40342282c1002d081c46140c41075041c40c500028002420084420950b001048690b0340200b501c440064006048801d002c00083c0090a040c1080746007452103010383c403420300d008800c891004005840d0b59061a01315140c90008101d403803035000c030101c1005400f01d181e030551542400030a110703650321400c6285c01d281c0859410160780c04140e00c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 317769649 1250 317768399 317768401
    0x11e0b07061509020f0306040b19150f170f0603010e030403080301030b0f010602030a0e041b210501050a1202040902061219020304020603040813030b0c0a030b0901050a0b0f09041103061206 83
    0x100d03176002c08072500000d0440300071031040840c400040e5400d1449030710f02148005d281c0e0002e00100b4024501c000d0000c1c0e6100d204540c91b0568055824040c0e551565450b03821a2001420541000020307e030004009800061460300140701139265612035001955180c4c2c0200040041102151030558011020034260700d40d54035011005c0d40e0303130044074010810b005454500c0322840c0c5031a0701c807045401c400a1058100c135030708100941666803c14007980403a0240031604030f0f1640a028050403141c014200c02c3c0c146140c400b281e01c0349890303400100d03441925451254056a10000940309039904020740c00802d0500070402c203440404004d41d022038500600410000d80c0d0b5050943e540941c0080b00c2541d200c80880040c42444941d030401001503003603405201241c1c0ba101c024203111009514100810581d0790b04200381d0701c0d0300344112075004068090902140c60100041c02c4240b070810101414081070b04001401d4424082154044c0f85020040200754600188a11442c1404601904d09 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 317770899 1250 317769649 317769667
    0x7080705060a2f01090b0a0c03090203121c020f0901090e040506040b13020405040809040e06060f0d0314040306020a08010b071106030705070501091101020d0504080303011e0b0706150902 82
    0x210700c03c620354880390390119424000081108100160400700f02c100204250902c41c0b43c0455891303c16144500118588012940154068812800b000e0b8004008100080da00d00c00e4403a641e02c100d080384400c512065040403a42d4160026004248028003425110800a0700041c1002c4d45030340407e22110341d841c01c0c080840e0001c02d0440d00150803420341c00031581e5841d40604c40000d1404000c0d04246080c017048244482c0d4409802e003050119020302000c1c600c44600c0ba5100000c0d03c4465000c910160103d0003442d100c0809507003603109050a4126003400c18468210350455882500c079150001003c0c1411984030f00c17014003600125240a0a107001615850401c10056480354011031000011420307050185042c0d80440382d2250090041c043d0500d0700c0442078007000c07001800340c41040b00c9456014010411740703060f10a060011401c603031a1400201c10814512080c2e60005140c0c8400301c0c005200000400b20307a401000d01040045004140e81e40e03080807035000200d02841888602c034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 317772149 1250 317770899 317770907
    0x109110d0309060c0f08030f0a050603010207020f040e0c0909070303031103090a03030f20070c06050702010503040b100b0f1e0f0f091c05160603270302071707080705060a 75
    0x80d1400742c0703042511200c84d407134540002076000300041c0c20320030701004200e1040c0c40c2d402c0c0ca40c4280c06602c410300c504d46407a02803500303034010140000c1d405407210b20312114604059001e0300031000301e90203c40b400303544040031a418940a4031000d00d01d030482030090050640500604e0000c4540e4401c092941c640140d640e6100e04142000508040c0c940801c5560040e1301e4011040c1d03000c006150200e1002d005d49454001d46c800350085800031504c030400280c1a0041007603d85064060b1190741c6540d07560740e244c03c24840002d1446110826445010401450030009000708202c4a01c0c950343d6001428514540c0c1c0a513107510007000c0a0801000d2040c0f160102590041014880701f69240e40503040001c4203071905aa410721940040d000c00070500000140d60884c0d900c450300041d404a8807448210161240300200d0540c62982804a079090b080e05642803025500a01c10384031802d44643d103994203480400c40c0203040d68004034003440014024044403004002c11160743e032610440c500060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 317773399 1250 317772149 317772167
    0xd0b010513050d0203010f020d020a0212040b0a0813050a08070b10030c2603160b0c0a0504050d03030912030b0a06080f01063c1b02131806020c0109110d03 68
    0x15014040e04043d003011034409411960010b484083d0030354440024002d0032009400c030340f86040040c440c3c2c03688400308024000881c0d064a040540ca1854503040da84c081e1111040030b0010380d84114880b024901043c41446070040d0f031441503005540c1e50003203060608918802400810580d50701100420000d03035a10012000c8803000c0b0037092001080854400400440010803010750000184051a6144201452203071078440d0440702d0b2507450300d10595a01303010340310310503010582c100410302c690319040c2086a006446868080b8400a60340e07681070031607503805c50000c003094484000c80e41c0351820301002006005a45000b4801786041024245e03078035410311a40c018019050f003a890300003041131410701200342450340030350810040c100070b0007400a240c255100083c0c1d504984481c01601e21825100280c004200d90524040f420030540107000100c84c601d40000555411000101640045d1114030011000004d9020450400322031094039820910f1081102e50071800020350040780340c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 317774649 1250 317773399 317773409
    0x1050f0306180304030b010f050312030f0a18050d030501030b0108030901021c1b05071a07051507030216051e0607050a0305090703062a021c03020f04050409080d0b010513 75
    0xa600104800c4110f06611480d04080c2061303d050001148102030465201c044030416400c4502d4180c01c46905010380c001550508210780d6440701003200c11100f42c209000c009401e00d04221091303c51b13a01c3e0781c50407045003004408244c440d00104140180d0004150040c621200911300c2c1c1001000000d4440000107603095050450105c1406254850b400200c00c4010350065414003a086041c003a40c0c5035124800e4600c11002100ca0000c040c0380c2d43c055980240c0e001c001026451528015a010100010400020140e0912240301101082004001406d01907000f403d45000c0c10004411000c0c20303400c4020741036100f50140040140d04c071081718031a031100d14000503991140d54504d4100165640040d01080c24050700c00d4160302001801119041440c2500400040fa5881130b130b02c03003001d0304c01004141c81880d5401c481900a07002071441d050244499403070709445500050032240d4148081e1020368011425501d404400e1203160302014003400c1203820660040c40d0354480315098029 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 317775899 1250 317774649 317774671
    0x150503070f05041a03030403030c050f2d15010b04090506030d08041707080d0219140d0b040b12010203010e011d04060f090506040506060a05010302030f06041e060311040501050f0306 80
    0x9201340c0010000c580d9010b40e10040980e6500c076500e003001444040c03007d01c107032030901800111081407030001494528003400e0381c082081c520003001010030400100d01090f0b00300d0003055074052660883e5162203001c2c0c44800340c6262100e0a0540da0000c480000385414002c0d0300884d42c40c1d210369081030007aa80319034014944024150f4a032000c07030b950b00403180b00500f80840852200c802c56101c8c0c024000351b400c480ba544011010b064821121070415042c40c0c0205c100400c000041400ad9400c24603040e0340250000c00e89190041c0410541c1030040b2910301a030358084010302a4024903045036004203a2240300940b405940c02c0032003d81c0700301520052600b5554003500b068800e85410114015400c141600c40b20700d440d0408030341b100d50450f24184100508100401c0d80e40c02882983d020317140c8801c840c1000d54807003003840005e007001403440d1208540c140b230502c030012007402a00040c52040c01140c07403500031401404241c0e501071b00000d115411a102c00603a64034002901d55201c0c1042e04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 317777149 1250 317775899 317775911
    0x203040b0405120304081204090c0203160209150a080a03090f080312070314090c011b0f0210020c030618010c1407110609040f0e19120c021302030a150503070f0504 72
    0x500f0a246100d03175030100800b8041c0c846000c81c4100d5400240c001c0701c040340804c1c0700d1a08c0070304040340c482c8100580c0001030b065000303d000150801c00c0071180d000c203410f50300c41c0b88854110001049510107601035001540902c10501c10950300100400c01000c81213020b052090030f04e209241c80340030b00c0310011411301044c0006000d031882070700001c400c58201c0c40d2041c0541040100652109041000c990114070745c12020803140200c0180070138843e400402d1608251103d60800410303141c91109041140300f510090402030380e05003c1c0c035024100780e0206501c441506c2ca0a117094a040c07101c0d01050280c41c54200b0220030001d42201d1040c1c0d0b00040e045014041c03c000100035006401410383c1041c0740103440681f40b074999000c6d450740c43c0c4010465445911a5100b0103801c061610005c2c4600201c02c0c4c00c0c10b1b03080c0a07403141006148028240300700700c000b0698a40c00ca030400c40e4444091512008002c0104600031032140c0a050b065000c7c0c0f91440c00c02240341503182c10391003954000d55441c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 317778399 1250 317777149 317777179
    0x8030703110415110c0303040f09090501110307020a030206060108060a03060209010c08190206130804260118020f010207150e1201050103050a020909010c09091806090308160203040b0405 82
    0x2812140544001102d41c01400d00005008010704500007148000e03200e04445c20380d240c900003040c1c2c0e04946102c091100c1b06401e144003140602020002101d2964031090411840021781c40038502c10011903000b40000249810024509100640041d050003c60418000d15441d402c119400ba01e0704141c1c050703620b0715280f00484603062020006001300501040441e40d00b0340c54000c42e01c001d6056803c031807083d1a51144030a440e60542d100400c070550402c070400c000d65a0b803c048020301c075050074202c4a6001140c0403802d64045071508107060420752a00c0c2d04603d4814900c00c09984288010500380381010040762200176104a2075040c080f01d503851080b50f5680030002d480002e4210008d0200c0d5a49140003565080401c00481c440c00000c8005204d43ca4140305122038011190303070380e02c29645059600c070000e05011422000c80f0b581d055084021503c1801a810a140b00303944106203071400c07041c0711860a10004801c021900200f1040040410610035181650411108084405000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 317779649 1250 317778399 317778431
    0x91406031512030a03060b0309070e0c1b0303040311031206120f12190f05191103030405060708070309170a1e050301091d0d120b03250602070308030703 67
    0x4401d803607018451000076000d00e01c02002030701d1604401d13141407101a84500c0f240110340400c07250541303603901c0740404201d1380010b0742080e138104151945503480c018030109000c0d1071110224040506070f00010078401055880f20003007055044110107141030403681c0b6180ca06009000e408288139051002160740070b00010700485080e019010100da144086060a08060381c0100d140c9024640b40d003200580124080c00c04106200059030398949030a03590328589640440c0c0c0200c0b14100150480ca80080000410055011320f000b48000d00d524603100748014030301c060080c0f4a03410981020202000a08400d401c2004842c02846a0745c588052b10000ca81600b90384050483c82450003040380708103a08080158180d901c0c0a0090001110601e200700c6480d4140d408024a0391290a02169061150b1145100e1152680b0301003000040d00b8000b921f007100c540074645601c102100100c071060000c0c16150b000b002140080c08805103551103030095404020250000e03d03440d00c0758840b050700702c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 317780899 1250 317779649 317779681
    0x14030c030a03090209070f0834020c090a0209031f020d020a090e061f180f08071e0303020a02011119030915300b0a0603050603060709140603 62
    0x4800880740c4611924200401a04040744264041c404030404103040e640300d01520043e10f001d40d25514000d032290360034140c00a10044140c854a0300b21146d002c149036495500480c1e040da10381c000e10311114101c00308504240040c1403180c0c61032042110515a0310042451418070071456008600310640d98412406442045200300d210b510004003c8011508010080c0580389a40e40203043c03a6100c0c005d02c903000285890031510400130042400c2e4091188207520b140d000140e1140074410340d504d281c481c138002daa8100e03503000e0300662010320000b030b512080d05650761a000e00c10100c0c2c52175a2006919800382003406810800e42c00002c814a000c10480e00ea03c000200203080080000c0f0300300141019403900442304a22000c96409082c41d00c11140100c01e0a014800c1840340ba942d907095000420b0b152030032000c0713192104214650380c0e40d41e080c404c004168586000c505450a41c0405040039002004017050100e0780c60180044859001d00404010007961640c0d502d80391440313034500b1001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 317782149 1250 317780899 317780917
    0x619090c12050a0c02100515150d09080919120605040309080303010e0402151e0307022107140604170310050303070327030b040f11030706180e0103020108041403 71
    0x2003440144182881d16078054444c2040e13540c20b80743d195030041e550506403581901c03000c0041c41030340c0c00f10480c0e00e40f4542d0103144091903000f0525010b103601c89042904c403491401c1c0c070f5100c0049440021400c01c140300c48803110328181c040b6074080c18022820340315821128042c000c203a0342c40000702018021301681001e0a83d901c00c480e100d60751000c0340101e2042c06ca504034025401c00302e070b012840f49a03509031910701081c210350880000c000445483c40d508001c00e504111b01c104040e04900d6520744d14801c910203040c16110703a6403149403c1907c02421642808503035a44150100004030f030321050b04144040a900c41c3c2a52900e0b100a81e41080e14243c05c400d901d1701000921a00701078100d42c0341c0707401e0159070030000300c0c600d0034030f080d0305000b0741512020f0416154003001500198403080c00c180c0c0e81c4d100301d601440708000342020920f05849d540012000c10b094643c2d83e081042a801c03000002c01003410780f4819581990700007861084090002000481415940e40c210203003070041d6038140c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 317783399 1250 317782149 317782151
    0x12080d021e03010501030609140412030b0d0b040c060503041e230c0a0f060e060d02160305030a0608011e180204020f071b0b03160c0803070c06050619090c12 69
    0x8030707081500c401603100380b103a180031900d085000546001c490196101441400e001005555259120805903041511200d42010399800b14a10540d8034000b01180f07a5008004008507032070300386002001ca090b980c002e10140201441084001604965424258504050040d6803c6800d16004c021710b56007183e0714504070b10002c12403010440011b400c69030070104035440306410b42d880a40c0003801c2d0030360050800103841807410311014202440103048ca5168017070010325011044a00d072880f507680310300031400076100205000310300d1389034015040070300a0180204114205c828400c0284400740c84443c1050383c42d00d0005140d100501c22909109801401c295500e84403031900c217000b94800101210400c048800c00403c00141070324500544400818091031520350b28034139840c903054003a02000304180501104002021500a1030061084e900c8101e4590840d01c0d020041e22001420b05011f603e5852500c1c0a8001c90003040b4201c6900c218001551964a8411070300c10310103040700031004d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 317784649 1250 317783399 317783437
    0x4051e2407271401120e06011e06080f060d06060905011818020111030f04090f1802010c03051308160303080609010e0f07050c0105071106010f12080d02 67
    0x1881001009224010a56440703622464411941c6910b403540e4603410b500c00b11482060115200700710310031400b1141410300485080786202d204041d41d041122901b81908042c004011250440802e500d00941d40104201c015042000081c56514020b040403006440040460f21540318070316001c1c1501c3d01b2400500400d034035a13181e00b014000a01c20098031543c421821140001e00e44600203882c0d02d100000881c003030030354004450701c01c072000148019000822600080340030b408018001040d062101050501080703402030100d50070348002e0020580349503054001071783c1c010540c1080e590316080942d11a8032141d01c69075480c4650700101104c1c40b130455080071402100280d203003240e00ca0b907a490002d644480178025400820b1052000d403225600200c4c00c1d007011354880542c8030f89245050f40c03c0c02d0030114228290342040d45d03000d001c2010003542c40310184c02807288a0140c200700d0319400c1407a10700880107600c80b403000307006060460089100501c0f03a00b80c2e0125144292000410700d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 317785899 1250 317784649 317784703
    0x6060f0414070c0b0c0f1602060927010504020f0901122009030721080702030a1a09120a0509010806040b1f080105090408040905040201301404051e 65
    0x344068001d0152105540c2500250000d080b803801c4406d52035880b018282410041100345000b52098070341240e1111050080e9a402e84491214100704020324a0001d951054000140003000068005c2030040303004000b25000039085170201d851140c001e1a100900f2128800080300410108081d41400402030441189450044000e805204011025980d0a80c1d0b1340381543da840780e00700b003518107107409464145c02043d441805440c0d442d00207010f55034450703215591408403080030b5104001c900900c40c02c0c40141c01d0104404a05821000000c0e86449103549014100d4084c2c05129410402500d00150103600c4a1708981d402c20409403d42c80c81d0580c86100a6101c406c076110140041c070868000039140c03800440f110b0050360002c101c1480c06042400000280000410990501800e243e1030303189000724800d042444019281801c1c0740d8190021401c0130341d100014050b00c070b1240c6806000c00709030b02065408450350350340c0310100c103140241c14080c18040c9500b41c6000a85081284002c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 317787149 1250 317785899 317785907
    0x209041a070c060506040b01140d02041a1c06050603150409080f0c06070804030c02060d140c04080f06010e010b1b01020307090f0b0703021e0f01090c0e1806060f041407 74
    0x40394600c103d800b0320456030307900103110841e01c507402e4003800112082045c0c050880448000c00c0442c1022070094a01078655004400307142c90101144a0b1840000d00d10706009120900d4188141201c94140320f070f41d1501002424500010717014410211900140f14055602d552011800c0d59000485648500e0000304501d42600004544001c60007000001041d032031141000a00c01c80e49a1a01d241300e90b040c1d020b000030381e00910000e10301d855981ca64400010785004080e0f03c40d40d2400700c5103070f0780c82c1481182c5040c441c3c01742660115602600051160707460041c0840e040d600314000e103c0d1611400f480166100480c61918000d551000090002c802c0c0c0c060b4108050711a01e088140400fa075400340c0085510920b24045c0040c0c00c0009500800094202510084c1220000303d690381242c405e283350855072129800c450100308540c042010515500206901100ca015101c0d83d1701c2c1c1e4612556124a8010041407080c03000824016071651759900051220001486803e40d0b85420300c4094 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 317788399 1250 317787149 317787167
    0x801060e060405060d120f030f05090f121e0708040b040308182205060307080d090305061008070b09030a0602030a09031e1205180303070801060e0307120209041a07 72
    0x40c0c0118202000901a0300740204145c0e085580070005500000d806081240c00c0e135a0081c4841c1015250700c51030003102024000c060107442e0400140003001562890180381c0010051301c4012070b0400c0c0024105075100c2c2007440326801c82010465500e00e0380342351042442c4500d401030440c43c9004a4044103105075034014040e1440e64209260180030a03030308100005124126030980044420404c4001075283c1d045181c1168001c2c0c100d40740d59440302c500b14101480c1d061081300150301e5150410900008110141c2c1104e54558560155410894241e0701c0d03c0396802019041c480c000341d00300941c4c500b08100308105401160071902c0e0b0030101c10160180c04100c60560002e841c0c1c59290305482c95120941c3c01303105841e00e40750080000c08800002829000302030202400c40c030340e801207080600740000c40c07180c5551b42c0c61020070360400102400008080f80c000b4002c0e8009541800500c948181da042c1072501150f010030a9a86c2c1d1406802442c00d22082d0089001c3e50401d02c5141038002c0619 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 317789649 1250 317788399 317788411
    0x70e04030e0d020907180905010b3f0702030f0f0c0c0102060f01050d020f030d09030c080c06030403141303120e01110703030309030c1a04110910090c02070801060e 72
    0x1d141c60000020400c0426803240001075030003803076100842c05950142c01c080441d81081c882c2c8043e42646c82c0d11280c202c0b2400d83c842c10800c800000c41d80e0081c056580e44c1e0910a00741c1b8483c1c0c84050041e10440d9901c0d140c0e80d01e0264542c20790001c00d64560007001901d20150b113918455a0f80c4104e20425101500080f40d07070101841104140c8400d036001040c40e511940003442181e41d960310b0882084960310302948141d811400044000980d51020b001e2071103160142d03203803071006900d903283c0b120602c2c1c1282e0003411190032060140080d030341c500701140d0300a030700751915143c45c00804500d00c546100740781c14840c580c142071500004001490b4030204582d840303904d80d49910408000151000f2950100d008041d80100f2002e20000703001e0350020348818064542081d0590150b5204421a4124a4640c0c000b4011104010800c101d04250642e59002640c202940b4240448169000c81003401000e0406444072100e6104a20802c03080d07000b8040c1c14001c1c000306554002404541100b9542 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 317790899 1250 317789649 317789657
    0x7050a06030b130b0a08030f04150503040f02010309111921172b020702090c0a0c17161407090c050406030c050403061406030f0105070c0b18070e0403 66
    0x200182450091003103100410024007929007844205002c84010500961020741c08009200045501c5504102420b200030800380d500c3d5490341400e100760001c000501c100020040104200400164564900da00083c0d080c200400c902d801403900d12106180391310381c160007103034428161060b210035151714801c0303803200c1001410360800b0381915520f01d92508000742078543c0441140070500c0d061402400d0b44e100007603d003000048019656880b843e41d00c403050540390780102d072001c00e40c90010b41c1383e600480c20300f02e800d15084000302c1c09000c400303092102518400386800000700140541c000c0392410542c003075004401c0c3d081c44c41c0c8218145030344554032259100d40070000c60440d07428810b10003548056140d2030304140c90103030110040c0c030000c0980010003505020000008005000d852820480c100c0040300a242010905280c030325000e1110107142e0622003400503264100407444c40d81034101c0c01040280d40d41034981c0c91980d00000c012503041c4038159002840031b40b80c1c500d96000d01c3c8203070344e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 317792149 1250 317790899 317790919
    0x212010608130201050c0c030a03050c0105070207050112020d0914150f010b030115050408072c040b0112050c1309150c0e040b0f2d0d05100c02100e0705 67
    0xc01207940c818119002c180c212800ca00e50400340d8007407030140040c070030310314200e90002035000040380c104084448200c0104a01003000c0740d81080070f003d031503405081d138030003402c3d124a090002410800e440c400036110507400655244101001c0d00300b41413094105100125480c0c030900b920b50380b00c100c151031100c01003007000030500803100340f4101c034100c2e2030801c5820b00b140d0030403842c1d5403118403042014060140030440011150b4041c4003401c000d103004043c0c2103a282101d0030008400055111103c03a1907040420000007030200414141901c0540400d200c1c00c13000b42c80c0c002c0c6409619500c450340708540e0048003808004c02e80259610a00c19865070400c0038003031620350156508080c2010224059403111300c110304090b4001250400c0052514104d4440341011030004908044982c40414042d030f0340341040140c841a16113800001d031a284907191080c2c0b102d40d203900d099400381019030303160050310b1800e610070007081003007000381c0800704100303540c00d045c2c550b8400d034905c01e803400f8401c0c0300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 317793399 1250 317792149 317792159
    0x60a0507060627140a051e011203080106020303060a03031d06030a090c0602030c060a050c16060605090705120103020409111017060a12110103060b040806040606151205090102120703021201 83
    0x10103a0000210f00c159200d1417504c901c900d0401508008004070924002c0c4004058803904840b0341d5030090140c90300d946078568150900034103600058100c0e000350b50080091010039221450850102da03014640540300c04e1550090088603003500d00c01075400a804418000815525072102c40142d00c95054004a05d54446050380c507402408a00406a08400d0000344001d2203a003100394464041c0f40b02500e08009450a20460510920261215951100240700314203118000070f4011240f030424074200090180654000c400c14007000340956262a00c180810003000200c401d0340c0e00003009165410003005005140041000d516612074035490085411030518500050580b03121864030b100f1888182c03522516141440c1a01d4109556042d0008484010801420140c40c8140150000f404c103410014262032407508030010301c000a18000364139540000e2807442050341d0302e0300490039a4519111500a00825075040d0010703248c1d0040180f01d42d4550300419154410740064841c1d03980325 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 317794649 1250 317793399 317793401
    0xa3e03060a2a020106090203040f020a05010905101407170d0b04060b070f0218071809020307171e0c1b010501080606040b0a0f080703050f0c010905060a0507060627 72
    0x4000c0b000305401c00c8910719029103001002da1001c2e4001ca000100b44280d90300d0030304040b60301c00c4500b0364131154180180e004629220741840000d2400b441c100320854140380014016201c0102640f041c401c501c02c1031a444002c0800399a03403150001e0180c00a61079082d143c0407654414000c0e002c501e8901024161140340904c98881507544400c2282d0038844c6541c2c41e038200010515050360f0101c45c0c007200c40c070030ba94014000e91242d640b59480005007107130404c2400d03001000747c1060544600600400440d1130703210b616044000948240d40300c145d200d2080c180c8500d942c1d0b1940742c4900102d01e08001d00c8525000c0204500b0101307000c004030640461415500b259030a006403001c40c2c020401050480c07034582c100009100b8014540e140310b075690301014040140701d620041071a040804108107000041c03101c101d080c446103010706038151400000924155039030040500c00c18002c036001c0e0110341315800366507105a019008201c5180c031510421002249d43e48075541030700d01419098125a55 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 317795899 1250 317794649 317794661
    0x50d060e040b1009020c030f03070302091f03110c211608040f05010c0c03020906040e060406091a01420c0501060515180d12110c01090302030a3e03060a 67
    0x601005142050030143d80c00340190b00280ac84810550240440900c80e035400b010610080101100c90020442c0c0134005015920000501c0031504014032456510b84008100c40b9004402d500c100301c100d04080483c0c0c0c0e240e000d44502001000d509120318030411400303000400c1600c3c44500d0792a0322560b50001100d940d241b1000040203000240300410040c103011075002d800c5070b402000461a440c0c00d60086203855402c43e030580742251154443c0b0140092000c006103a0708201000302201e40c1002100b1124a02240303210189032086050044861f1a050399420700300f449041340d10032851010700080892805000640329075191400c005803603c4c02c94900c918bc1c000c6801c54034244140810382000c0b000b405854107030444001d03103610002270807803d0b41c200b580c007240d00c0d41c080415900c8140d902d400c100a2100d4103002c416101400540e5000500d4022154418160b00c44031401a0b00040310381e810540500c041c1c0360103032002a07548050b800b600302c030041c1901211a269140c010300030541e20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 317797149 1250 317795899 317795917
    0x30a09050d030210050c0f2101091112040201030b060d1b05040807050103090c0f0f0911121602010603060e0c01230307050a02120315040b040516050d060e040b100902 73
    0xc882d908030f0428070b4460700840d600681d8444418241000c4541887c21a07102e1002d400c2070a0754407102950b14501001254013600c1655000c210400000c091000d40e0b00c20340340640341910306c0c203001404580c440d400010100300080d2586844038000003442000e03000440403404024690170380d0006131403095098504683c42c0c140180011403900b40107500800440c00b05a411030310702c08021622400106c40795004040880520005624010211017101c1813401400315a41080040948440e150400c05400200d030000b02c660302542040c05038010711966000503c1e00b4101200c0c20b0100c04007149142250800b071301c0e04110710390032918075020f11030360b0304001080c2501480820031461240e0302806141805004a401e18480560301303800725001190741148100b90041e1000300303801d01d402800c14104094606010f20b00b0049060086490300740d020400700007002c80c145403c40101e400100080c1005186c00c802401c060070620007041c02100d56414010442c100016143d05500c00c45007209 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 317798399 1250 317797149 317797153
    0xb030601020d11030a0e06070606030309180903080c0d140906160e100e0a0306020c0304052b0201080a021201081c02070f0b03070e030f0a020118050f04020f0f070302030a09050d0302 80
    0x100c0405480b62030101001b242c1102042c08820001a0b403480b8a201540c000d45840c4141407401c1c14840e6010792501c00342e6456814090710100103600003034642c0e001040030304000e4550b4440d842c0c51008080c1084620201420001030146510001c0303000c5001d20140030f892124208580001c5d1f031000b5560710b42d00d030460303007460303240e5002880764844642c00c4100034004a240f0790381e510b6050980e0480d0710004841d4000141c200000d1410254000015581481710550307108109940804480400006810703c41c4d800c0008003000184d034103d40420300d485280c8101540c40e0003000d5507910510007440c1150052000b0a071070140002800c404842c802e04803051080d00342110b440340c64001030059410b0011220001020f5135060081c043e2014142000b84006001400010004010709101c0a41034400d10380600054894001c0c0d040c3d102425140544d44064001c500381d10351040301603074420004c0c04100201051b50100c000c1600340344075a0789001198407001081300107040e489000b005a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 317799649 1250 317798399 317798407
    0x1406040b030703150b060c070608061f0309030e0a030303060f0b13090b040b0907020604030215070e0d0f050102031927060e0f0304061110090507120503040306060b030601020d1103 79
    0xc2c4c107611000d91940d4401e0340100e904030b00a0701140590b0400030034004e090b04445400d1102c5e0b87d001e41526486042110220454240050380d1040026070407801001c00d03072a548000d05160080051030062a000750a41700c0d8540e4900300100144900c3c080d070088980120400101d80c0800310540b004007480c40d00200310302d441c11100100400500c0e8145400544400c03a0000940e61039028510580180c0c010b400c0c0ca2815150090a061b115404000b8209501003408550783d805010b006070344106481040260400742059808203c0f141320042c03082d0b000000300312310100c040540c003000c01c91039201480072a40543d07009404440c00d040321218440d03c40c215002103a081e03001134480740d080c40305440c0804142c000e15415a40550858000b144101e60002c01c48141002110401c50121800700030310a0990f840f180c840b51244980895a1911402a0280402802254010b651018040040c60390f030703090070403054108882d01409030043c044401155409004440310380700813580030314030b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 317800899 1250 317799649 317799653
    0x90207020616031b12030e06090607120204030b0126010603020d08090f090f061206220312050a15081615050f071103060c0f041404110a031406040b030703 68
    0x280c482c0c04401a400c0041c103410250042c1e1080e0300400d6040c0c041d40d00603031092810500542035603203200e510540c030750000040005c00c8a0128600f40c000c0c0c01807409a56484400e03900b90f001c0e00880d00080c8c0003990800c0000b03402d00402c86034070b90040171401450b2030301401c04002400c039003017480b010390014000c0708003e0000380c00000800c40c1c880d0041018a4405e451000f0461b020811138440c880a0034580510000c0c1c138052035000c610780381e038070010b210b00e140002c1c5e03d070000c40c40c00c001880ca000d02c2c004201c040501829080100c9481c00108000d00c2c0303001c0c00c10340007510420300501700e01500020086501000480e41e4401071110703105090b044c501c0e11018500641800341c1c4802040001cbc00441d040ca0701400003800c655000700c00c2d00a03042e0003e010181043e601600744c1c03603142020040c40741207980301015036088451000500c00040220360200c1c2c0504600725280c28590000204139842c030342c060b4403854441c070030b0b00000307007565a880d0103020461f082602c01650552200740d003040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 317802149 1250 317800899 317800927
    0x20f03070b190504091404110303070f020d110d0b0f010b1216050408070b0306090901060e130f02090f04060b1c020f03031308060f150108041407030c0602030c070902070206 76
    0xb4a0101500e40700740f41a90b618100c00458900d00095545900c0b420305002c01e1007504030500204110403405146030011669400000f0f1551131002401003080d0b290940a0100066121324411030151150b9049a01d0b844c0c84880303c40111030b030302c205d041b0138400800c4043c5117a007a0340000600418100d415260700c401c010850030590303003031000c0200c01c11000c11003401c20300209000b422000b0b687c5850f800c0410030060724080041458103140c0c0740c07000c00c214036082c584c1d0880c1c018094501c400c0f440b243e182060029080e410202035042080802840117484010388031078400c1b40038031003c01108500404024450140c00c040380d800c0c075049407070680940360080c101035040000604a80c54130b07500742c0720003a00f001c0c103a22460241e0072001c10040a00c0301101c0343c03640514146030001c1d245150100281040030302600c0038250000c0c0b104014100c5404002c00809180c00c02e9045403001d81d00c560080d5a81d103c00d03140b15160042c4040025920007134000d4030380140d40200294201008800480717 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 317803399 1250 317802149 317802187
    0xa0308150a062007060e040b030114130c12120815090c0a09092a02030403080d05040203011d0c1c0f0308090a080f0301030309120c09020f0d06080a020f03070b 70
    0x240c20082ca0926094260f0b208011100c001c207541c2e10707901018482202000111040194070324082d9045c00c042c0055890080000c40d440b030510b0381d45607008401d0f8200003445020f2900440c0d081c08400344520300740020420000086405035448d00e130155601d4402c0b0025001c0002182d4000c0f0f01100410f0f0101900d0020784802c4500740fa20507901965800c49400755004491201d0308030f000c4054050003040c0001080d10f10106500042d49002d03d140c0d50751184d8443e50000650180c2da6074042811036a0079044404010301842c8026240d501001030952541c0001141ca440f981591516899034a803034981d1816980d040010b40307040d50110f8030240e4030b0740c100418000311800f03401c0d041d800151a400240080908100543d9120340c150303d400703000b07021144c11500e10020880000400500358115401c1035950415000d038444211420010050280d02d641d540e201d8140007000c03035504c0c0c00003418101c1da40202c0351359800038405024541c45264078014990320170003c116420701840e03075104038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 317804649 1250 317803399 317803427
    0x405120a05072d0b0702010212121603020403060c08100801060812180d0c0303030b040504120f03060b0f07170304030507140a0206190806010504061d1c050a0308150a06 74
    0xd9508000540000c0c029070f0a0300410601d070f502281100544d6810091a444011008003261505928020001c1c80304002001968000d0682c50452004d07031090b0103850003144d0158052000e1600907001070414a400c641034a0042408940011044414018441101c00c2c11014045240120310303420115032240c040b440742046010002411601e0f9480548200345c02443e1840655066103001000e6900010035944200e05003c00d01002c50050300703420003006514100292000040b41064001d00003582c0301c140c4003007010803401035401d00b00c1d00500a840c490040301280030010343d10f008041c0000c0ea00034000032001d00038840051040400310b000d03001c1c240102c84400d81c155001a60541c010403c00c1c11042e07151814010543d0004016030f00210b0900f0071a040600b014801890b9044d85c408040b00039011220024840e19101c044403262080180038018140c0c007070400301c0e51041110b0086000410390400070750329403019035118001180052001031079074a066002c44281421000d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 317805755 1106 317804649 317804699
    0x4050408210a0507140a030527070e1608010e043e010c080f090a030606031101020724050c1006090e120708030106030c11030406050405120a0507 64
    0x64544480052800048c25039808400c00421200701c8000a4a913401c241004120309011842c40141c6580e0b0054140a840c0c02800107440983e1307043d820001028500103214138101c41811640090048018980c059070f4401042002c3c0152004000c504036030f001b140c00c0c03108803c9407021003014242082c000154194441c40030510503180e2168203003000154245036903465070040000b0f1600040f0400415489150000f2143d2054001601510034964002265400352500c00d2100c8122100401071040d041000c0e11181c05c100481707119406494120b414404440c81035000601040720082101c04000c00030500303000c00c154644400120800544d00880c5103101164112401761600082d651201c980c112208142000b980c1028000000d000445039807120141054883c1150400c110220f0f01240980d10314440324014456001208108121000445410000301060398 = true := by decide +kernel

theorem cover : BRFrame.Cov 317625899 317805755 := by
  have h0 := BRFrame.cov_init 317625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 317625899 ≤ n) (h2 : n < 317805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
