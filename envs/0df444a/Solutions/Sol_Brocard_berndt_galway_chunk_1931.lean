-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1931
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:11:51.298694+00:00
-- url     : https://prove2.me/submissions/4f549818-6cdd-4fcd-8156-9211508ec73c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 347122302 ≤ n < 347302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 347123552 1250 347122302 347122309
    0x131418031911010b150904050c0c010f02030402010807020616050307200109050d0207120206071505100e010f0b03040605131203090605071b0201111c02010b10080115030e010b 77
    0x681001c0700a445000e038048040c50650f00356101200960b110b2041a10500114010a0210784041d00704540c0001c86589642d8400300a0041074018911503203000c0003201c002d60b00e0b50046004034000d884004203607541d0141240c1c3c074a0211038031456859070000204003180200003864100c2c02a0600c1018542d1546160014080700700345225103039110826101402401d101c00d0740040e481d403019088003405c00b0400321501c0d0000200030b02074400002c020b02400006e0f80004078034107181105100d00c2c18062040c080c0c80310580184a45c184140000040d4406030402160449031a0700c055400d42d0303101e0300c440b8002d150089c503441129481d01d0003200041c44212400302e510a51740c0f400502c1c4a01d1382412002c03104002c02c0002800456404406e242c0588420740000c0350782481c1940f62080c5038031000341031001c415044400000002050030f690394040d0003422481409a80311031a2902e418000c0b0f0741000c0038803c10f00b400054965a1540510030340240004000303820012400c000d491022 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 347124802 1250 347123552 347123587
    0x17070e0409030206060406080102120c0a090506030f390702040603080c0703140304050d02060705101b14180904050f1c020d0309020a061d03070603090213141803 71
    0x48005800c00401c101140c60141f20384000387c01000001c605040700c0c47c5100b003003403801600c4000004004103011100c24482d81c00c0201800020b400300e41c50382482400b520b907440c030941c0c800101407807010508032442000c045c08283c4092041c1c901010844034609000f01e43d0009900f40e800a40b2204007001007102c41c070040c074110003483d000300402880c40c100303201c0120000104502a8108120811480d034a0b249286081c0381c04403040b80d0f4a60749407a20030b107840080c0d9209484107042981c8603100c042425001901503400c0d0300c0c2c02c3d2011500111001c298400c2a180090010b010000203503141800380707005505c0f9104004440400c0c0107a4501850325092003140d00b0050301c7e107030500c80d100c0c0e4184454100110b65050134843c2020aa0018190384502c0c014141081600c01d03401c22004e0120740f0203200700c0d00180c240d4003100c2d1180d0009000d01030544040e4000d00002c0e5080b81446000d1240c41b4000520841b11030507526034144502c042036501ca806460762109111000f8542080e200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 347126052 1250 347124802 347124821
    0x70c030c08031209060c0a0302220f080d02070f27150302101b060c020109200414090c040c030e030d061707030512030702012a03050a0b0117070e04 65
    0x56440d50030320121080440c80003010700c182d07500484140521022444180c1f0300101d034904015131241c200100341e650010540c01e001c00401c80080001600e1000c414000040e1026201034520740d5007600c10a0380d0314450f0f44211115000803d0003000709414602114040005102c020601c510602c40502c0694a602e05500d40d54484071038100704624100460104912150a101c144001810395a030490f8194841c0545181e46a448054400c2e200798082d2003001d500010781d1090560540c0da440032507050b030995a00940c904a0303514046400391074103502c05e0901300000c051000c192420301c0b0103410b0760032000c0c0c149a194034500450000030300141c24101d190300380001c2c1c018500b0380420500c1d01010780740391481d0080c13801400410305c0070448440d00002001c0c06913a90b202d50404074018182c80348a80b50a00c05000f2844001038588a556440f090707698040c821038035071210075400c84890112040c003203458540317009841e040c03601500798824101c0c2412151070381140003190540d6402c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 347127302 1250 347126052 347126069
    0x618032e0c030e03031317071a010b09150a05131d010621052d0106090b12070c1419021203040f03080d0906060909020f150a05070c030c 60
    0x10080151000300d10030705900c0012440c0c01d01080805102c0e06440341700241281444c80d060900c2801400200340d055542d184084210558600301c504182411004503a200d03845107404100020340324051005541012100030240c1000c00039502c0b1103032003036001c114403505104041c002c42009405000c0c41c000141108138079491400300c21740d491030766100140c11000500a03c2c6400049019181c9039000340303030721507010000745a160040140c4400050b28400403e1081c0c2d4140c20001000380710026040302d0054580f22445902d908007940c0b540074408130240d07481d1101c00000c01061040c0d0f0140003480c000c10700070239202115650241081000d00781c644c01c82628071598400c50409042c00406100c110b00614142800c010580030014141c2c07001400c8003d01003903140701c0760482e81c450016103a11560800800e6580c1e00c40201805a404083e4465050350624031643c2c1081030b114100902e21030341541c1303012059842952103800c44030090f80c4148003014003100003410f030a0200050b00307208 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 347128552 1250 347127302 347127373
    0x5180a03030302072604120c05060c0115141318050703050c10050403020f0918060108060609060105280306080102161e05060a18020904030905030601080c061803 71
    0x2414017520781c15181c2c15030401c0341c24020755040e00d1800c010685040d82d0380d00c41c07a0f1226010300d00b0f011140340780581000740e001c100000c184540c800e05600403800010340201a400b0f690ba42c19084982410156055030001d48203003d50140b10741076407210100c0d908105041040c0d10312600c5175454440b0700e41084846038400f82d43c80d101c81c87c4c0035908107c012240e2a11514181c219800300300308500342c2000364003035059500490610700c40d004980d20400415402c89002e580d546840c1076445800f81c0c0d919002e03000b03c4000c946194820801c9600c150008139011045250860384402d81268214050b0205a0b40303801c00304002074203000802c2010b43c2d444040c0131220b00d0303052401d04813044444200c5940b409884a000254003c540c080d40462000000100f054280b01640600303c1c0000c002580041041f041004240e00080d1070001d541043d41114074036078890120640d03651004030820751216041c0145440d94240304009090000c014040da4400302c41c0b510521480b0078190700d006401c1880 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 347129802 1250 347128552 347128567
    0x16120c06060b2502030c15030f07030203130b190606080114030d081f03060908030f0a0507170a02191e140406180305030a030c1214010605180a03030302 67
    0x1074080c00014204150540c0e1a0241a40d00b0640c14905508100070700c0180406500541d0740c01c1c85100901e0002030824003010030340319560035895000f00c5000c00c1a928150100b00840e100e807081d41d2280303004e4010302c0c8201c8026102c009104200804640c0311519900d12030482c80a140a108000c1c00543c8031013116505058601c010713a00f0850703220b4001c2d0311191240382690f921500c42c0350441c0003901e070b010700b036030042030b94040700492500f001d01840d00384000d407420802620001c620500c01d11129007a652112407103603064490030b840440016842c003030182c0402c140400b409030000c010000042c41c0080303280e1100c00c140c00310001c4102060403420240900c4d104504c0404010420340751107800c981903620005a1406a8054135042080380d40b00003001c0e503000382c0c5c5400030b540c005044a440d05a0101d0040c09001c201c3c03000d60005695081982181c11030b80134625580c042c9280180035607080000458ad56000b0319694a052034415a41504076201c01711200c0140d40079580c05a6078112 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 347131052 1250 347129802 347129813
    0x504050c060a021b0306040b0c03070c17040503010b0f15211f0b0a090b0f160b010f090608030d151d16020d02060604020a020309041112010b0f0304020616120c 70
    0x2804200745d010f50400804c100010740d18400d000d51042d103c01b05261130b41c69018017114102c0b040c1e5001000540d440ea494605e900200b4003500071108110024030918025400b401140c18a10714040d81211900080c14102e10b082d101410000041c0c2c440f07078980301300c04d101c00c144228007074400080b20f0313240503500008251000d0410029003014489245860740708840141105030314882c0742d500e4480824204e0640c00c1250032603107070740320032603803000d2403902410841e140c1c034020700c07031a20b0002c081900007543c1c410600920040340d615801440c1003090070360b10100500600c00b40c007481007440c0c40c0302140d81c4100c407400c154081525520400d0b5490a0800a41e01031500003000781135500411080c2d009a0b40041c040e03500480c20760380540c41e0820480264554007401480b10380c07003424020342c66013031a144d401400c0c8130045034003500da072030742d1780c03100344241c4e00c145c803000c1841d10f030100006005030078207500800485441d407130301c103160601076190169071054198019000500c40c0300326109001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 347132302 1250 347131052 347131093
    0x6020307180f080d0f020d0e0d02040203040b0f0105151602010e03070e0a0c0c24020c030406020f1005010312030209030c0d0f140601050d060f021909060305130c03060504050c060a02 80
    0x2d001741007582d051040d0400207541c1d206184003000c00c1202d140b41400498a0385424080c0b5164094000e41d240d04081c9045c030b0400c0d40441d04035191030600350001415140811060144030700c01051546007071582064000b0422103a03034140e040c800c00e401c4940e15610100908001802c403503900010368200701c280c000548049441c1201080307060048080400c0325458400b21080e9110700c070b000c0d010854103151000c2d0040d078000c106907000c082000100d0746e030003041c3c1d480c1c00c4298006807052a0b00383c4850208a52007030001902d21010342001211680c001e500815100074001d0480d840d40300c2d038000107900903801c010100d585591840d85101009212304144a10384000c1c0c025107060760602001c1206076086060180c2040e48820807042403242c65030490f140d031000b2a4000078085107900c0050620711301403054400082ca80700000340401c158868a5049a5100c4c00c1c040c1c809103140c0f12038024000141050741c05000e402c84144071035880340010a603051a40c0c000d010340c003030303a12507450540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 347133552 1250 347132302 347132323
    0x503010e0f06130203330f040e071a04030c0b12060901060f0c0606091a090115090b0a11010507031505040e0303060d1e03120506120a06020307180f08 66
    0x1400001805030594606480c0740ca039104001c001a103d55482e6444010103010041c060074140c02d100036002c2ca03040002910411b900240d50460161601a0034801210010034000c141c98010010034031450a02c51103801019003010401070410740c480d107402d41c1c81c0910b5845040304140008043c0c041e410387c0004144d2103541256085290b601d420380240030814140b100000700480140340c60f003081615489803029248200007049028000d05803803416200340d407840e5101c2e0301708800000d002c1641e540c50102c0c410081d40c40c0310403036151001d0011705800c100c40500510041c0b6890441d400002d101c0c1c0c80c8100311554003c205500e01e04403413440492185c200c28042d50504a46295500000040301e41021003903944103200300203030601d4030300801034180d40a4040d01c601e00e030788249603000b003880c129040500340401180e150b0700c041100c00704501c2c0102205800c10344007400481d10544c051940b00310a41805180c40071590b048d4201114507401500603441541000e014500b810070422a40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 347134802 1250 347133552 347133571
    0x308030106030212090109200414091b030327011103130f060e0102070b0d0207020603040f0b0609060d0201111011040e010b07020109270207051b031c0e0d05030a0503010e 75
    0x400130301da100c09516150011150345003501f15008ca1085480d03030303403083c07001a20420700d4a09900b000b40c038103529140c03102842040302c01050180c0c6900d24000c011184003076401c0f14403c100c0c8008480400e5044142c00002d81480b94008400f050f4040500080a01c0c50000d4241d07a1040e040282880e14002d031500720401b040358804200156980011b0b04c032043c0c40c4581c1d02c0d81c0d2184d406911617406032041d003600a40180c00071050008000005803824000c0d40700383c9980085035101001e2000c910011108560300081e2120841c0255014480d5207818407400010b0720010800041501c0c02e40383c0350125006120000a81005440c1c030081e80d440c054004520780d980741c460300d500000d008640a02a01c42c0070724403100c02800340340f0700e8100e4040f04a0080015500c4212508005444504d6041542480500e032500c0c0f610514010076001c212a4051229005107501d54800700c2c0c00c803403003149150308848080b1004020a1082000d066240900e595070340d920b42c1400c00d403808485016100115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 347136052 1250 347134802 347134811
    0x3140d11030a03050406150b1e03270a1e0b090105072f0706030911150d09050c0a0b07031218030302070501090212031306021501091503080301060302120901 69
    0x40c0c418044116160051a881c0c049a585c88500b8810014041600b64040c0100646400075445540300080c01407642d0074002006c009207007940c0982c2507c01240c516200850780b1280e901a5100640b80340205003056044480825583d40d0306801c400880800704000f03640d92407203900f00480c10890302d6114490740003d000d01d0400d40700250455459140d850340340c542607202e134510030441d2682d2090006210045400496860300c0140c02850001000e82e0800d2050030000c10904104072402c0b00840c0c00d15149103840340801d0400011f25000ca4202d889000c2c0742142255075440000b00c0000e00181b1050603a00c1440f40350203050703d14501040103504d800d140d10340c0c4508501c06412200749030181405a03513184035103000c50040403000300003540901c5034200c03039009400000107032403c4044084003680260301ca2405a036101d1020400c42c41c00740000c030041c0701c0021a80c00c050030107072000380003848240c0c89981c0c944131074000360003860019501041140e202070f01c0701c1d180b03904003c04000070071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 347137302 1250 347136052 347136077
    0x10b0a1d181002031e07080402011110240602060f070825030c110a0b01050f0301200a020c011b06110f040603020403021305010b030a050903070b0103140d 68
    0x3000890038081102000d00800004104440c1e29244070018500001510380060000c05100c000b5001960920b1029258080c40052090111000c41c041c5101d80c461145a80e21607004403822034000c0ca034001035010f2000c41c0d920012060151100c5000d584501c04000b00d4a282024030454156000004541c018010b000d130304003006000301d42051a6281072500380c3c0e15152600501184884000312039000c00f251500d0713441d4164030a04031600e40f0340e628207a000817020baa990390060000c01406c06888040100130b0340ca412145c860000e0000b8002007030001101c130007070b2a000304148450310f401c0d0380003c0c41c03030310710703034103214008800000b400d0100071040303c1c10030f28201c480141c0c0024003440c1e0b0b542c6000148200041610000348001811a58480c0c8605008001c2d400501c8202d0049005103a220034868942c02894140c60181004a046a480c413054901070710020300414000d000410415000c03410080040e4040c50003001402c20348003078004201e11b41011105840c0401072b81e040b808 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 347138552 1250 347137302 347137319
    0x109050c1315020a0210020313270f0f0207030903050d020a08031503070302030304080304060215011a03041a01030f1a070f030b0a091a0102060a0c0207090207061d0708010b0a 77
    0x180c9254010803001c10ba4101c106a1030700f03074039000181d1301c4242c00c1705c82202135500100500c6403050078094010500d50300c001442400306540286400740700d03680184c45680c040c550000025a4014038081140041040854220ba001140680c00264035410078810710804011003d600d00d00f0784001e260068140e240d542882c04007410aa541d01c01840002059507002c000c01d202568005059a649903525100780d40c0e258418800d017070140c082e00c0315802c45d116001421904a40000d40400004001c0d040c408a5a40c8001c004407002c0100c83e81c4590380c0346002d403909010b581310b138111144143c0030341000310b400c82280034040910120141042402c84e80003403111008402070030003045124403400040e40f01002c80d01304099481c60561080c0440b078480070282903103402030b025201c264403040c7c000c105a4901082c80703000350f88a16401c1001c15510741c0103209443c0589000502403d0507118100c0f800701c0046a580a948095170a2100003800e114800c0c103868100e50849180e4a0b19211 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 347139802 1250 347138552 347138587
    0x7110706080606090303120906060a0509061809030f0c010f0509010c210f0906090c0e040b0f1003020d0f020114090a05090403140307090305060709061b080d140109050c 74
    0x9008010128544c407013034a080069940107070b0403010b02e258601e441794106580e039000302c880d2482082c44030030028650034a800400d0150b80064400e1200d400941d1000b0f80c205000342c103200c06484200038882d4001064070280401c0c1003100004039001030030320706070707019154044c02100311645403c280b10203403034101c8040151164199808810f0600100c00c0301c0046c42081400d80712182030002c0c03030b0104440755021010fa54482c4c2c00c1907541c1c40d01e0b5400745120b0101120020103036801c0e003010480b518005604030382d100001c0c1c0a0b50420540300d0b80400d5103449600012107883d41a0b2000380f04643e0018002c0030600344114038281013000190019503031452a10070fa034011440070012070103061003900c40b00d8441d1541644039a0320706140100501048c0c552000359100d0040ca000b1520300ca1043d40343c60122107550f075030324454215081c1d001d1080715100c04104d603024401c000b0b0080418083c041e151900902038103170b2180758500389428058400041001c2c4008400708504405003260412 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 347141052 1250 347139802 347139811
    0xd080702100608100903053007020f0a030309111005030906010b090a05040902030309180f011d010312090510170a060e04030c0c030614070e010908070501140d140711070608 76
    0x3004941c20920741010355641c42024204004684074448208803444131051230b40b034061f000c1113409410741e03426604070380700e002140c4410305642040b8500d40c0464469044488041c1c00741d680103d240240031b00081d00043c00d02c40a01c0410f00200411104010604c03085004100403159a881c1001c14000a4110230040c09114030450345c450384101907403001c00a640301600b001d00f00008410b02e4195244002c0000c0b94405d8000013842c0c000b01d041c0c1c1c580d0341c50745220b4417401c1402072180d0031640d0303100400600f40212000c008040b00c0009503942c0740c10403181d8801040d01c4088041c035149042040440004018108040c2001800c008802e000c0c110194069010b141006142d642031070024000c141d075610140003182086140c0040015844e6814003803180c0342c65000344503c1e0100152001d4009106c0c3c0c2403507400040080240754095140803e00707208800c02c4510b80020000346804696440084061b401c0b888010051015080321503e240038100170000c01c681c924081009141020042 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 347142302 1250 347141052 347141083
    0x6060f0c0705130b120a080403060c0509031002131a0a0e030703060f0f1a03060103080c01090803040c290a030902010908030304121209050a02060f07050d080702100608 74
    0x1500100d09409101800152030010300440540c00c803481510041c00d12040b416214003800c0702100401340e800100b41c1b00c00d5503c803d03024101483e41d16004002d003442e02525041c040c003000718291554060000d4100c1d112451001602c070341c07040111400c01a121b4000000164802c02260140c0ba032200544d00ba240c21440d014600c458807901003414880c0d039610052901d0704050300c4c41c4103000300360050609802005800c0001024000301c0174018086068481d0b0103801100042c000700c1d00c200d000b440195054400031071418219607034080c155100700d0b81629803004407102848050402a10810044003024441080c044c0b40c00c5d13408454480d0340c03410743c14595180c0100d021a401344041c04003d08042d42a69243e2400b800c0c84800550034900010004950001002d0740001c903100395074400350000c00a1040d02219400d12006602050b4183c1da00c0a0500c180c0700003c5040022000000c650f56601c081d40c1400f0102900c1c100080280a40c030b141002801c1c07001d140b000070200c6062898a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 347143552 1250 347142302 347142307
    0x80606030a0603050304030f05060a06030f120201110c010f1805071203020c180601091a070201050304020a050402031312080403170421030626061308090301050411030f0606060f 78
    0xd9140d0700101510351000b460360101180010a00002c1c0b104401464000c1d81a1035084e0303501140b0700100c4d01349000091110700d40b00c21308408104800b00080b0000c03500d00000035544c82c1504401c4540e00410007040c1a03079100c010f40d5408954030300821400074002c100224051100e13984040d200e0095014140c82d50000c02d04440070b040c404c00c58020000303400790004203c00d61012548040410071244540802c0540d04002101d810407808068020104000315084c0b0034164011500d6500181050342c2c0218164400301e4540e80b42d00c010750054203040c40c0e1100040d1035203412400c414209048805002407041040702080d00410b100f50071500000864442c5d030340c0d602c1c01240c50060030382189150710710440d03001c9650307415901804c180c83c12648480c440380e211840303005041e0b01e048010849500000701088000b8940b000802c045849040c1690800301003001003402c541c4102e50617100700040301d42c0110b05d4142030040c0000307503400300c01603c054500b18001c50401d101c0da240200007407000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 347144802 1250 347143552 347143561
    0x702180403021c200c01020d0e01030e0d02010603050d0e0306040b061c0b1909080a080601020a0516090509010207210c020a0803072f0616060f1401080a0308060603 72
    0x901100b03d845402c00712640c48000c003200c0080900f0b00c008051404601e04c42c8030040440c01c0021441d42c2c4800503070040800500b110421510b20440340c84030780c103251b00c3d00300b0489802414407011150100e51b81c00001c0b8a459414000d00c0c6c0510903041e8024421528482d124545001c10790b80c0d44250000188541034075010041084c880d810b40d5004c8503640c018010a040100361702041e0700411000003200b1000240142c110211a80072200402e0b06808110340d0801038090160b0719400f0344140107941c40880aa12604c0c00c154940c1e070700455104203520240b02100c013a102c0c1c90741140d643c0300210f0a0000d259182c0581da07503189500c0c255222082016001c1d188100c0c020089154050004d043c010341d14800d659594001203403c603000f0404043c240484814140810040e01c054075008194030a0f00042c08410380c48020b000902e1340d0b400485c0320100d03010303003e0020500306c006000520000b2800011001e510180c0000407103802403414040843d0340607001c96002441261034603900d0b10f4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 347146052 1250 347144802 347144807
    0x10804030f1d09090f010605030f0c040b0102070807090b1512130212030c0703050111070f170f03090303190b060f030a021b100c020105061f0201061806090e030702180403 75
    0x41039200a0f0b0b11850300801c0000c0a640881c00c424030a4002c2c0c028088181c9813030815856001c591107000780c07513012443c9490249069000155140e0041c0103a41b130700f54850440b82d00f426082c0e001040001d4580448c044641000032440310030f00c1c0003911403800c0000d1590001c1c1c0c0f03208060700141d01c10304082400e50a40d03940000740840d413407208046a50720840611030541341c1c0c20500c001d13079955103003680784e210720082d20f0b085070f4105912503030078003d45009a071056407a50a500c06800d280300144407640405600d40f0040d0b004e030f000a8015503c91812080c0c0c040701c944480708200c0020305003812500d00362958002d48401ea0000c03540180c0765a2517044a00080c00f90000c014110345001c19078501425005c1942c0d10a0340c80140140150640420181e09a4405a99582d00007a2580c0c5541d8029a0f0341c040c02d084003a540700101c1e80540e00d00018040d00010400d40002d941c1c0d50720104034415051150703140c140f140310080c41c1401e03220f40000b00010048010001806176a5001408152 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 347147302 1250 347146052 347146097
    0x70f080721023c1e0c01031a0d081e03040309181103070302090f0406060c020a0f050f010302070206070b040b090f160b07050f120904060b1c02090406080a051b010804030f 75
    0x90303081c1d0700c4042c084c5030015282e949541440100e0301191416032002d91403520072070420a100d1020381031003030145d00d41d50303088110392201d0038801d84082c104148444a000040046006500a90320404482c4c280010444506000810039240c0c52801f02e01601f0000c1d2041602d40c050190f042c0140c0301c070001c4001c98010700d611a04c4a90240c5054004a0059008002006803034001c1d5940410a030710303152044003490140c059075901000d241031030682d41d88a90018140e0905c040d10300c4d420480342d641c0300520000190b030115240e420200800a4150003044809403003980040146115285400c6910504a19005010842e00c00050840500100700040040400319104403041c0200d94540000c00350840c00640e88111f081500018804942d103041c1d401141c110100741c200000c0c0302540340c00950240c4c1c0705903005615202c0005038400240060314100b8068800f600e0380c00000c1c2c40b410800b0001451190600044030140804a6130003102e940f0712044a050000700c1e1803498810a9401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 347148552 1250 347147302 347147323
    0x1031a0a1a1b060a110705030d0f020d140601030c020a03140717030109060306060b04061b051612050c03060c040e070513031113050705070f080721023c 67
    0x482010a4403421160700186580c4646410113080002e0001e04409071030500c0f50f0100940164803c1c401c01e81e042c410356001c010803080d03030035005241920541920055031a040c062610305820b00c000c1000550701401218018452440500b2800030b951303402800761001045002d01e05070000c1811010807141d000300702407400c24228030316141e41e90b031040c0c200640309a000844a0320f0404c50006064503420341628142c50094031240b4108180c0300008812090040054401c2d00c00d108038041d6111000d10f0540c050811034041c000d0582507030030618540114900498001d0f4003540070498042c6044090700c1c00d6440e0b10011000340c0e15035101c00c0340c19003d100d0181404003455070001040200500e020070480e00e0668480c44205110980401124030440781c2c040450010442d940c000f500307080c015040c1b640f0982110b8140041522203400300c2c1c0410352a00079042c1d03030600500c90a17804005000805140c1c03030700700c2150355021424000c9414110100c003080c40c10b5040100e02031600740190210b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 347149802 1250 347148552 347148577
    0x216050f0a030f020d0806010f271406040602060708180114010e0a1e090501091a010815060310090609050a0b07090b0306030d110312090102040501031a0a1a 69
    0xc80000c25503038445850380000c501091000318040c021500104040d690116079881e1810503a80314070064404940740e007007a004208060200741e00056401d84603040c80c801288100d100c0078109050b50303032031100290801c6d10462045c40200446640050410f601002d149441c401d1078881650014051180c2c00c40030205501b00118203201200100080c1d04030f40d0b00030760190312511a00c000d44200d462514003400070a41c0c000aa080c40f641c00e4020362005481000000b0b1015145c0e100d081145c0b00d40c0030040300c1d03039500d40c0040100c0601003008400903500c48090034040c4c1841c1c80000d80da410070b425907002098851071030300c2c1444400d910062040c3c1e00241a50f078a0419807a00060b0640c04650500100390312441c00b0400401c0716040d00d220b010080c00070003c04541000649454a82402d02590340c80b08100d501c0c0c0c04a001034005d401641c01c840056250b0741084005002d88405400b600100c8022600c000e0b02d599510040000b00c4103000184040100503260258042c032030403008220 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 347151052 1250 347149802 347149813
    0x510091503050402100e0d141006080309040e0706020c0405100b0703030902010206130c05120c0a0609150f170a24080105070e0d0825060f150b0706021605 68
    0x40303840c0c0681005115510807030305405400407254090303541c00e0742c107a07125401c008001d60160002d1482120200b00d10201c800703c40f0390707230f015078482c809030b58064001c01c0d6660004144244282041c0c012070a046400c00d018101c0c40d070500030002d684040d81030226104a40359000310b0280701100d00307910003411a190000c4d03aa00f00e6070401801401841100700c0c010b104030b0b00003442c803d03484080c40d6030865100144600075842c04040100401c00581011101c1c050f041034043c29030384800401c002084181c5600700d41920701110281c4030900d50130280c0c11301444c80944040664461a6003084285010210741980c88003084000106643c1d00d120380d846806403d5240e24040b109001000c945404000307006a6440c241c0448658826603002d5801583c20f40d24000040e0445015090303080c0c2c40251401300c19020400343c00083c442d4042900c4031681e6201140c40000c040c06140c85031b10544400f1603c080c90440c1e05c0040e407051040107010143d001c07500648140c8034261800b0f075640c000c000c0f6071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 347152302 1250 347151052 347151089
    0x705210706090812160c0f06020909040c0e151f210e01050604060302060a050a1806050a2d110a02040608010b0901150e0f0613080309010f18051009 65
    0x40f030a902000d0742c40c0740d2500c5800080c9002c82d80c3c9204880282c915620b5800c011455540d048081411040489203150284509245612040e40091055001c1d8001001142c50005111b49180c4054491020312407410809203260f101c0c0b1100307541050340340070702d000d15014460003103c01d440d0b507200354140d1007907007043c001c0d46482030340060303c104810310001c002c5500d883c020002140c00511009400503414015410414041c0019243c4000742d4206202d070782c4020035800c42255003541119011030b101003210801c0b00d620410302c003000081000010303240107207480f611968812401d040c0080040d03850410072240c404ac1300700704040d640500180b0090b5150801940a00823603646035000e0400c2400000b14680346c0c85c5060884409603d800b100350000d0b00074482140c01c82e00030150040f40c200507050010842803001002058454091503d40d4000c0c400180540100c0703031100108410010340d00d850071a200014821104210381081c0750900c840000d90300000164800358281c0100e480c0c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 347153552 1250 347152302 347152313
    0x7080f0402010c171801051809100801060e040c0e090606040c0924030e061e10230f10080c0915120106020613110f010e030a0507030b0a02070521070609 67
    0xc1040b440400b81740907210070342c000119035501407440400c5041082400a403c00e091840300c19030400d034245182d80450382c50345452400d45e55558070014101d41000104401c0c024800c01e43d01c0a414403015400882c28a1040d8a50741e950141c0581d2240b07a481783d81c0100240200e00440c0242800b408400c441c2e00aa588030401400c05141c10010900300314010a6a50010800922500300c1686044180300c10051001c10200020b1042c00002c0110700c2c00b050382d49110710300d42400c21031030083c1001e003500d00d001d114a0100d11100d85000e11011003484c6152904404440c1c0d21400182d0741c26200c07220880014440d00e900920706a01050004600b1400401000c915059415980032100140c40780c40701600b01543c0c003480a84502d002c602107804030301d040e42d48441c103420145846100d00c079205000a0400c481098121810791001108008100300d441246900a00400701181008800d880d8641c0b90500041e1940041030701280b50480b405000d0140d80320140c005a00300240903003850b10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 347154802 1250 347153552 347153557
    0x80103060e12220911071104110a05090a050d080315030c010917011e0b01122f0c070e25090b0702040e0d0f11030307080f0402010c17 59
    0x19100c103400c00d203800760680d90000b010003102500981ca580b5001c000c155807016026074105148031100f11500001c1c080b0390a020b044180c54551170705030b40e204011f15008540b1003400c00043e01a90804040486402007401641c94409084c14520740e1041e8000000c3c0000541c0d0b0003960b0303c0040c4803c840107006244019601c42e89140d8111110211200c003050750704d510000d4600d00243c0018400d0051050282590380002011b90002c00c0382c42c0c00030f46a00c09456580344101c142a5201c045590560f88100d8031441c1210a900801544c801000d0b185032184c41c405501107102c0d004004030040300c0190045540c3d444002083d00d4032141c81d50480071001e0400e42e0441c24002c1c5d650240440d101760b00030140007140c0640c0300c0d0013410349010400c4a032500090320590b40160b07200f048034003400060001403075041e1300b6540d00918007541400a40b6049903034040c04002e030720034820042c004d074000540c590007881000c04200a41c0e5280300490f040641d100000b00b155440c1e0307000a00f00c0810201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 347156052 1250 347154802 347154809
    0x120f080f0a09060c0503090120061612050105130203130f050d090b030f01032409110405130519110301090b100506070515090f0607020a020a0e271006060801 69
    0xa621a0640e0f5901c0121650140200003906030b400800c40d040d601d60049903540d02280c8000c811241d20303c0c402c0c4020381004003c40d00b24404002080c0041c0c492a40107500c030001c0c03d0040c804110550408001c079036410045031000c50625400004070307102c460030100d00842c2d139600c10f00e000d503803040b0352610986845140c00b003180405c40801e40404c1d52410304058030301c9481e000c0002d060701d1b8a140c803485103078544240c00c0f00c9514800c0c445040c4600172030081744141341c0100341840011b043d05060204555005140e801c0700d021401e0140d0002c1d17008100c61918440c80c2c01c6001c00c0819030b0420843d0740c1c800708011503241d8a0a4401001c10030503002062060004070006145141d90302e0600400d07200e100e000820f507811042481640048424029420601031001c852450445034076051528605403243c0d03001d81d001810356001c5140603141d130009090350201008243c14041d80d000310381d02051400c02c0020740d0317601906519841c100300c030000d1485075544c01d0205039647c201c0900060020701 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 347157302 1250 347156052 347156057
    0xc120105040c0306120819030b0303160c080706180608040f0605060f04020403061b051306110a0501020f12090a0f02010f2c0f0904120c030504030507062a02010207120f080f0a 77
    0x80c10300702814085d100c2c61030309d010040c020310310342940b516404010003006942118100b00001003c2551082044070b03074040c3c40316845408480d43d024820703082000035a8840000c0103041d104001c0010010195940c003103a12220204454503000000b034440314224100f00e170000e01c00b10b0000140142900200d91902c118282004210480041115603114000f00c1408071513009034204640c0c0d01c10701c0310410758030700081502c0c00004281e82d4242a6805810348401c100408034110440c0c038191706006801c8a0401e00a0151508075562581d610b034a0803406414001011f4128502c1d038011410307000d1160200c000010304a0010320042082d14644050a0140312600c3d1091071505040603110301854004011175601d0107080c030112852400d0810480c04c020003400004001081000040c01410480e00c1d2a24440da8083c1c0321000e5000c41325118800014805102000d41d8001c01c2640039039001791071200c200e500c141040c00c40c0b030344001402440001c00107030340040390602001402044c0b1556 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 347158552 1250 347157302 347157337
    0xd050408040e10030309050f03030706240f03050d031d1f1a0a03020405220c3312090c03080702010915020601090c09091a03060c120105040c03061208 66
    0x1803201d00c3e10500004012a2540c0e031b05126501e8801000030078a02c0003030440c0d00e010040d40d03411050ba455200100d060511089050038a03604604035040034101ca66140040d45c3c1c41c40e180e4036030301d050410202e03050654500f4942841c0c0120b64000e04a410201e080300c0701c1031843c030990700c0009042c404180e0401e16214601c07581605031503640030b034800c0003081c2140301e0307003140c00300401802c01400242001030907a0141900d5201c1da03451086060040b904490820316004c40c400903240002c03012007900401d03035440001c0f10700c0f1000045000c2250301d010280258101c2641009050f504005000b052190200104104511008080c894802c3e610b0a8819a644483c0d00ba049108016000541c01030710060012200550040307581c2d050360325052a006c0e80d00e038051011101202082101070080f82d400410700d040811580da0800c2e103000080e45406275a49070a2107210040c06090320a5844a414964040c440c0d0080000340080140ca0300304070307045140c220408e500c5801c110300c480d4901d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 347159802 1250 347158552 347158561
    0x305151005041e0e1510060233090304090623030f0a030c02061207030b0f0f0102071a0c030a0503040c05090115051c0c03020c07050f030c01050706020d050408040e 72
    0xa000f1403a01d200c1c640b025045200c1e0881c840009001c214a4100c0c291268111544015050800306070007003115010300c880490802800a0420345010320903603061442c0002614000e1900d2511200f0141c3c5021141c01c9485e6221280d00b1481030350700c04c205080c217044000c1440a0300a0540740320400041c40c0002c0034806105254854400400e80341668102c1144000800c0c0985410007070036200a00251030303c22128800020008140c40440002e0b5442e8060301643c1407109407118540c0040b40d008a0420708040001e503606014082c4a21000380b000214000b62106810760390341440c0c40b8140e81d100c00d458000207100e81c008032410b440c81c92752003000250505209200505880303000003490700c00c4600701010b440b1913102061410055100d1080150a40d2552060410840070f035a00582e0b01c10400b0038a500e80074503038001c68880c1880d07140b00c2a16070b500080100740c0400a003010b644070728240c18000006c0c05010303040302580b42460300f040200a0101d004106a8844004d420f46903282c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 347161052 1250 347159802 347159809
    0x240801061508010e150d08030603060f0f011203020a02030601030b0402152502011701030506070306050f03061b12040803070909020a08060f03070b12010f05060f030a020904060305151005 82
    0x48500034100402c00700340041c44061207a000541e0700c083c103420125695011140481e0a580c0840b00035070f4104000300a2207034070300e81841810b4101020241c0240c0c40c2c00c001442241001c410710450303100300104e405200425009200d5012102c0c0c0003010f4070000d695030f04000c44041821202240b1440c039102d0401c1e508001c1d282a03030405641c42e0b205031000c1e0054803407108a0000f01000703905000d003092103401944107105030140610f118001601050a00440284c182c4000e60442c0e84643e89400050b000c907100041d149500118000d40440c01d802c182034008200c0c8036285030721860003800f0081006001c9200025401154a661410080c82d69010030031300300c0c080e4001440014007180089026454001c80ca941c5e51a401000d41e030540d0307680c00c002c000b00d0f40150084e02a01c00c42c2001004400c0366a80281c00900083e11940d10300348441c00390101070300c00100060b000c503a01103554903040e203960784010044c5511404440c69110320002c081c440e01c00c1103c415500141040c00403c01d8107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 347162302 1250 347161052 347161079
    0x1091d0912071109070e0303130806090304050906040b010302090a06050301060e0604080c01210f050a0f05010602070306090c0306110c160501020d2d0906020c0d0201090b090424080106 81
    0x1508580f000c0d00080840042206090000e481e800800040c005141d40d240ea05100604070004801d846920f510300d40b0017407609141d8000d03c001900e801c103100c10030030ce4896001a950000b0200d0b00002c0c13411030100160001e010b480e2440d9004840d03580045105600301e001941a602183c0300e40b04907890000800c2a20312840c056100303541c10082910180f03500458400c24240800e000e01082c00d51a8002c41085800d40341142c2a0b060701d640c1444402c50303c0d4403814032842007040701400258103005019680e06650320004003d659208120740034000003228000203544d00003018401171203021024811600181c418020a015000c07030107030100007807413100341102c206030054220400c6000081d0741001c503c01002e1401980c0c40484180204400468201400143c440395030242c101030009141c02c0070510100d02a840b80c588180150f81c202e202e24080700c01c4404c103159a5440c0a002c20040c02500c403507402108811082c405540401400c004190b940541c000c205c0950360b550010b4600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 347163552 1250 347162302 347162317
    0xb0417090f01030b040905010e0d2304060c11090a0b040b030a11191e1a040b2a07090501150c02090f1b03040602040312031a010e01091d0912 62
    0x10203010140c554a5000303400081c1355020040c400113100020b03440340b60a580c1c0c00c061100e0260012003110700300c00d030807502140d0390548014941c1415403240c01a4596031150340540401e1181070b41100041040742440900307044c4014041e02c444e07090803c01c0300050190440f01c1d51050341003a8039400316050001e8a00b03c00354202812411004260040c040100c20500b19143c6001d201400899040041901c100c8003a0b460b800040b4a5440c24440260403180d001086c02208010042000061601d40507a81c1c1d03d0f419864880051888010f80011000c8080e440c5109010303042000503030550380c2e413181d0304842d12101c2c150021015203208460003005480001d5000c40c04001080507002e01044007588641d08d048a0418043c10000f040c1c85500308890841d6080e40000d014400c00000c9620b50454145601b0284200d44143e403440e412182c2421b45681000721946020321941c0c03080030407900800c0d80080740380070340381010380d90b0f05c40d248211400c0f4042e11800c1204001d00780c01034101d8040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 347164802 1250 347163552 347163559
    0x60d0203060406150503060118050c030f041b0e090d0f050702011d0f0d0602070302210306130f020715151d040507170c01030c020d12050c040801090b041709 69
    0x102d648694503d401405081c81c64428090040c8001c20030740c408001c4180039003014080068a00b0256004030140c40005150030420750381030051160b170170f030b03410314240d0855802140c05000416408015509c103105620584080503803900384902c086004c13031510399408213079036906034001c442c0f001551944141000240002e0b03140c070200410503030514030f183c00198000c00600005c607002002512100c41010290341440d4000340c40c9007099010400200b50102d002402002c80d040007200b90300c3da0000405082c000c20100140030b954001681c8400300f045042c40046440349a107040440d500d002c00c0795a410a81e141070008800d404814041804885100041380d2040441c80b440c403a0528002d07000700d5040c800c224010424140858a542014a155004008400001c00010144c8004000400c20b40d0844038400114542c05440001d05e001214804121501c0d4043c070b42c1080d01c070b80d074003014003035281080040402c0005c403105800345006d610301800340014044101d410b803241465080c0e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 347166052 1250 347164802 347164813
    0x90303071b050120040e0105100e01050d1b020d030f05010f0501230708070213110306062104050a0b1f050409050307060e0c0a060c0b0109050c04030503071109060d0203 74
    0x8801040034914501d40d40700c0e10022801d0040040a034207404820a01010f12141c0403074240000b00085044034010f003421a040c41149040c04c0c0e01078000500c8010040c10800d000030030400c592282e8000341145417801d06100034801c40941c00a44a0a920500400090410a001746107412501503141610520080b0350310f01071403c0c0040d0f030b500103044054201880c030003900800201485000d082a03a0041c002c00b50f8400c840d204101c00362817426086030096140c84645891540d032003095030b03072018083e183c0a03524000d840c1c500d2115085894911414441603003000108034000c100c0c02142c6d07108414030103503500c5080310070101d64580c11004501c021802001c00c40c920341a005041c280d8003c4041d43d02c0e00040c1e444901c16a03d024145114584c043c0d000000c4d01d05104103d000200744915200710f8002e00c075030303880d091a10184101e1448075110008600480c8601088a0056510804a03a5507900a1a003000302c00403d03000c05110b607412000254050920552800d49654010007030074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 347167302 1250 347166052 347166077
    0x5130f1101030e1b010e01020a05030409050403030e0d0c14010213120b0906011811220e01050a05061b07050603090f160e040b0a060f0e06090c1309020c1002030a09020909030307 78
    0x1126620101d46e420304600c1002c030b070600422420710040016001c0540046004d250504003e01500c403502003511043d4090070040d900280e005064180f02c9901000c107c50035401510302c00d029005030304120144000818000400c8003040c415004441d00c1851160490758620081613202c000920489515980c1c0340440444d25000798010700500c2c14010800703040c007020240c82009000c8050300c490102146403c1444000440c4a400340100000c48285028030f06100201c0d60318050101404085070848451146201c800d0120f14007406000e483c2d15140d01e0240000307603030307a9414200030350307107000364040303202c2080c44141c2030000d031144079058000580b2240c2d5200e2101000408119541d5950440401c1c1c0103002c0742c40388001c02e0a00210703111030601c84208082000c1c003504200203000e003002010301c001d091024000c1124502d41d00140c032540d4910b95603051140c03900c0c1d01d19409100000f00010343c251750b404110054020796407200c160b0b5850003016540d11040e5002c102080787d10740c1c0c48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 347168552 1250 347167302 347167307
    0x90102040b1b10060605131403030f210c041e14090402030a050708010e01060821030a090204140406050f0c190c0807030e01120b060d05130f1101030e1b01 68
    0x41ea940e660400c01c6843c440410901201140c0c46504048000390001074032036110034141d01c0410181400f4685090780250300c4000a9491203143c500550047c408141c20301d001030b1a80b41d03010003044000806803280340902201000d50700c107000784480f000290300341648803041d12250b0341c181c814070101014208098002c10200c01d0009200320384c9807003400740301030000c5e01c14044000100000750000c00e042e501140d4403420b68020750052001e40d07011001c1d4a00c1609411440402108c1090985941b51a0140d05034080e20103503034082d40160a0160a0703c0e00c490020000b80300da4003641041120fa1150948044ca51209450700c0798200028445044140c0102d114000c1403150b50a00400701c01d602c0d41d0303e4003280c00010059000ca29500649101560084c25441403c401000100000d1480304002842c6000d502c4c54400301607924000150100c10ba1402d100e150394004441d1611140c144c03601d500425102015140040d090020400c3e040c0000900c080c42c107600794210390040401c0f01c004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 347169802 1250 347168552 347168587
    0x507020409060e0106030308103003090909151817030c0c1902030106150801090c030f021801021603050601090e160f05030c06040e0714090a080102030a05090102040b 73
    0x20b96586503545034a225034402407080f00d00852007074841c450380707140041031655004e085a001e218040c80b0581050202030500740b00b1941e2404d42c01c0460702420311741c01c0460340150950040c801d120701e04110341c0c0034415034403035075000031f0a45903043c44004c0d050f01c025409401501c20082c030a026a040140014040401556015070b07650b0f07a0070305000660104c1460440c1a02003613005c85044849001076080030b00906001d000241300803040c00d0301c240001007030715034144070b0f810300a503035500074008182c0f00307800101c0d201040c0d8070155107842d014100d40c5d4042500c601603601500c282215110185544032160302100d400c14003900b401da19101101c4003410420a076914280101c142c8840c410441c242c46a010700082030f0043c1c0340604000030b040c0341c10051070300b040c40707401d00340010071620070081400c9602401c2071910032440e08c40d40d00c405009000d12120564000380d00c000114200f1f10541c0558030076107504c81d00784103070380340c500d0002e00704d10840c0150303401c0100404c003692000c10307400030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 347171052 1250 347169802 347169821
    0xc1905031908090a0f030210080c0f0a02120d1a01030c0c060b040f1b0201141311010207030501020a030f0b0a05030304030b0c0904020301031119080616180e0103170a05070204 77
    0x1000c2d40b0300080d000028241c80207a4000380807020a00800703001f503040080c049a0b5001e10b509082190b414400042a8140143c0600200c0031800207005e480103482408446001c40c3c44007540c076101c100c0c0e0500d00001e000031011801d809102640f60b480070307610900a4490f141c40503141c99084011545950024049a03000030360815240d00c1e551030748844500c0707903000322005d5101080100d0340c401c0000707096500d14054080030080302c90500a2003d05103154a0078180d010303036154419040d440040c1e060900c0d80d40702400552001c42d1180c443d0390960000c10003080d204500f040008905403c0101c80010f0307003e02609548180010300000b010241c9880e0000d02c00101c0b00e0601d60407100150585c0d201340c00c11500c40407020100281824240d1201403c00c0410b49000025410100210340c5c444000708250343e40102d40315403145144c0140c81e440c2d01c2e50300d0207a010a8403611640504503200080c4030860724540c541e100c100e540c10180302501d82c0c140a40e69040e107401c1c807607000c01018044081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 347172302 1250 347171052 347171063
    0x100507050d200a051e03010306020901020d03020702063004060615110d0318050703061a0402090f01030c0c14011b0f020606010e040e0d020a02041109030c04090609140c19050319 78
    0x1e0941d0020442006e54000e61040401584e01c0201c10b000908207074031686540c00345401401400016500d60082d503040040c50845c43c030380407010500d005081c02c84140042d0b01c0441303400910082c02103d4100310160f8010700b96141411603840b408450b9010010303a1381c0041d40051603100d01c2c280c4650040565200e54100c51407a1601c02d448036402c00c0041d0340100c0307030b0655400300480b081019a07650344043c4011207045040101d8040415141d01c0558589810555a440a03c550f03030b008119101066400001211b003600b501380d201d1b802048980c115400940a1051131243e50344620102821a00d00b41c0c090041e60b260303d4015a2a000d0807181d866200f500e035100b06c0071280007000780440100c4941e0050021a42d80d0050000701d03170030255000402e80f0104011640c5807000907101a000d2030540c1d0020300585107040400043c9280b2a00400306c1d000702c42d00501030780d0002a0420310600c125801c0079072000c4081e02010343c11280c891160107402000e0340c5002d10105215410b402c60003031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 347173552 1250 347172302 347172337
    0x9150e13020a031d01050702070b0306060d050a150e0f0f0403020a111f02010510081b011b080304080703020f010501050904081309110c0705190b0c100507050d200a05 73
    0x1020102c0354081402d084c906a60f540e102082a4540c2c1001220010f0141c00d807480e2a509001c4081880c6104243c00441c0103a2250003007001c8440b90350000506950000a24040350385802d901b0341844019141819800441e4020504d074071a01e43c2c8442c0244d60503001052804910340d1416440f500403180342d603111000c10400ca40c5a502441c1091142f102c3d42e00000d0039241c20301c140030040c1310540003c07205034082c404010a507030b80c0c0b040c2200030100900304900800800881100600110a0000c02c02c203008400d10080024241c0640055440303034007510b07280015084400d00300c80c000d214496000390080d0110b0082803c1800030862010f503800d091286545070a00361003550b45080c40d40c59030070400281550701d40c4042c44124050139040b070f0a4110301d0040e4400c07090a0303c4e50301815403440c1c4e0020745440c000800700036480642500210034040c5140c000000b60050300f105440c8503100382001d01c90080c24805c40c0c00c0d141c001c082200300508001d003c90f401c55994010300c4400c4c0041285c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 347174802 1250 347173552 347173571
    0x6100302070b0c030a0c090602031b0709111c0515090a02070b090c100302070507140117070c030e0d020901030b060a0e1006090f0e04030c0c1509150e13020a03 70
    0x120351240e8850034100f040349a480c20b00e00c18100841c0d001560001c10403403150303414416036901208607890406100c0c03081e0010b58642e1002d604202590340510100346c50709050f07070a460141005004000400c0205409507142d040c080401c0d01c0301168000d0856900070313621040c1d0301d040c140103900445000d0300113051881a036103024961105545c100c02d182c3c07141461300f003940340491003022501607070f00c0c1c10f50500c0c06588d00e081d558001801201340b0950b50703003001070452348a07243c04c51107442c00c41a88482c038140b204001c1c0404140c1281a00021480403021000c0e00388190f548078250340c094503465044e807079616041280840a040c95a0100200c4030000b84180c4070403049014455880c4407000092800501a11140c481c0c2d0006059030001041040b040c0c2c841c0c040203034020317018285014042080d15000030b4101e1140c101c0152810b80b4101503a140f644404620180d401c1010229070380c441911040e902e0717189110150358020010f0b0b1400004410b40e07006031110a040d0b080100320710a1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 347176052 1250 347174802 347174813
    0xc030d021318050118091511120103120f0c03080a0c05130b03180d02070605092d0310021305010c0204020c250e0f0c070c08030307030e0c090c030610030207 69
    0x41c42c40200b4103900d03440184031186003280c0040f1020320443d0100901c0026588082c040584009500c2e0310301d603101c41034401d03415001c084402c98025248860050b40c1c5078540900c6800180c001d600000d0350400c03880080b40d0040e69039010580d05078031840096550354003008041e200000a14040210900045501d480c16190f0701000e8044542c01503201e11702001c2142c5502c1a01e032040b9200e070302500ca040741d20ba03008110f10081d00c440c0e1515540d0f501c01d240201d604038401e49107000f501905e403440a400002e4405030103001400460598611030807054800099009002c03581034041c0302041704001e0b030b40c0159406125644003600260424101101f039604ac05100301030840100400325200c0850040b42d107048024041c41e41d802d0040e41040040b031079074000020807070200f02d100001c0784018000d420f401000205403203011203079640340013003000300038049062801056100d07040070f40307400c1e242c648005441121403211641c2141d4a0400308020390580c029240107160342004000f02051307 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 347177302 1250 347176052 347176079
    0x304020d0b06031e0709050a05010b0f1e0703200f0615030a05010c050403021318080a120c09060306270b01140403030c11090f0606180d050f010509030c030d0213 71
    0x42980c01800100745446052400c1c0c87c40200500d520910342001804003520001c01e80d07065140e803005443e16181d20110b10f80c902d0f40345061050341c40d24080742040426034030107070f10415411000d100c00c84000890340070350303a1462500311418040c1c021100040407141d01600400368004002d046580504c1161140340c2160058038a14002501c001014810741c01c0661041e9014440b18008221200a490703101c41512501540100141c800041b19440b841c42209000440c500604040103400941000606900068441e280c0480d0078080002000616800e107000030740c20701e020590030150b00c08148401014403150300e43c180003603048110440d90066002d0400345100b0f8441ca98082d11a0420744a05038034a402c40d4800c940c90300c100003011142102d2160131260a0359440d88a0900c01c2068181404c1d412406411154410118041c410000b4039100c408078a4402000152039507411103860744680110400301d0fa02c10400390080d040300354020800081c1e410001c000250310340c1e081034540d2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 347178552 1250 347177302 347177353
    0x120e0d0f05030a03240e0c09100c060f020c07170102040806090c0316080c12030d09061a030601030302070605070c0509090a030201060906120b06030f030705030a080106050304020d0b0603 82
    0x590003c50115403007070305480703942c3d02d21650040164072440000070000070014140100c01e043e09114000c5862680500c01355040020000c1c40c6100344011a40d0080099081d0356003038640b00d090981da103840e48800d1003110303007400c8550042e01286040864020140920f016400440e65080200088000c0f0501400f0300420110b4040d0a08021000805d890301d03004030113000f01114540c400300058800020b050200c50010780341d1681c00d114200005045001e40c0003001d19060a00d501c07001002902c0e400200c021812a0810340d0342140041455519807090000a0250b841f400c001e22410340681301920b611407152800003a41a100c0300803d050b41402e4420607a50303881643c030802015020b001d0300c40649599101004030503d007204500c56001e008102400745000800880e100780c0701880100d1082d6030641c21a81d40d01124a0455940c0c2d00c00d80540300011005000410264400d0702100e00507600102044907511281d11101d02840c40030b01050303418410380319018170300e003500014043c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 347179802 1250 347178552 347178563
    0x4061d06030c121e1b01030506010c02040e031e04030804030b0a090c030c03060c0f02030a0e01050d14040b1509070f1110060f06030e0703080306061b010f18120e0d0f 73
    0x18100348130001120400380c0d040d00d22034200c02d281c2c0c9403074900c0480c5107030154024038001c95151a1000103a40c130150f046c00182d0032504040a040c5038410000042c4448cc481040007240c004002081c49094003da000042010800300003c0020818000703840b40c00c14054100040e02d01400e580306486c2c038002d07500803680358014031803c005102541c450314043c2e03001410103040e540407014000f034503032052300140805d0106403800030149911820070348510300b0b1201d03c20406403140c0003041d00a2182181e04980c1081658002a0400b00b0340d001100051170181c081080764031115025200d55800003542c0d4100000811007c141900400c03d01040f00c54a2a0000d102c0d8207240500700300070040e4105009050a21000215401c4001aa0300440c0c0e048141507443c3d0b21184c0010f4030a10420002003512014038031140c00c0b140d410350180e2803a541d4800e04014450704240021008402010003a04a00c11803c44a180b28080c0040020204004041482e116816a1400081c1070642e5033500c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 347181052 1250 347179802 347179813
    0xf050415080d0e040b011701150201110f0408010608120d02160503030f040506090a02090c18030703080a080a0c1b23030309010c0516081608040b0c060604061d06030c12 74
    0x341080c5c0306a90100b502132810211440c1d2110b100c025100d4184950181d100082619a031a18402e50144015031481e041e165610380321910a8242070b00140900c000395480c0980020300c0f1080084c0940500b04156401e50514442503122002900801151028485410480c400051042c40190b200d5020300005000504045c148203241140007084130400b68402c14100026958040440e68403802000200e50b903105900415081d035400d0118245c0c241c4a0f5032004410042443c000c2c4c504c1e9661907803110959900c8805000544040031609000700700ca031072070554074504503c4c5203440140140c9113103900d110711b044031040364500300c050009260008010300402540030b0060040d2112640341540c1490300c40c0c00100003a0b404900020002040019460a80c541c0d205501c82c4445d00312100a85a40d03440c0c17800305150b0300c6445800043e0081000080c198502440340609a90040b44d400002c142e00101200c921030f406040154588590840c404880c0e650f01c0d00071011640280143c40e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 347182302 1250 347181052 347181077
    0x70e0102010b090405060f09030a1d0d0c0303020d021b0f040b040e07060306030c050a14010c1412041508160e180c09090708040b0a0c36050102070f050415080d 70
    0x80c0ca90784048d0100703011b50001c2005106031544080c400281082c000b802d83c021600520004440d01d2110900810044807a0b01c008240340c0c002c82c1c6420703051000c1c0c081c1c51b001800c05000d40d000140b40c613130f02c40e802003803044000c00078109940120302031a80a03000103211400200b040e850059a94004030000c2d45400040c000c0020025850000307000a8812071201418040102c0043d406003652034108040700c0358100a010705100030450000c0c0082c00d403450301d601c038084c0000d0360b80280100000800ca02a00358802c03845a20700c2885001d040c50305542042600104680c900e42241045502003100d86d8410b2850207901d19541c060510100c1141d03840d1406014440800e000400040a0100c2c01082001040c81d003610aa4003100106002544100340e104c10346240c411450081220500019003610a422424400d602811080880e4001c42c2d506ea004a0b51a5102d001e8428090310f41c8808006078146034220500700e044003149580c000741c840e2005887c00031080c0720300d00058803104650 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 347183552 1250 347182302 347182321
    0x10e0f03031b040e04020409150c0210051f06140d0609090209062b0602070f0609050c0609031203060a0815010f1a03060904030302210f010b0a0206070e0102010b09040506 75
    0x202d012581015014105450000d03410f40e002d00050010380103581b070b01c0d000c5003000000141070301d40c001100c200700403015518200a40d152039210711810001c0c605004101d803040c5490030500141c030303500e64120602d401c08000300c400303141024840201c41c00506c805e8003100050301540000c0e01c0301800004205080b40108101c443c00501780034054191200344940c0d10402b0300c01704003042815401004c0601d103a14283c0001c0c4180c01c4082c2c0020b050907155800c00565401c409403a034000c070200c511901d6071501b0805148500940f032503155028414011480c1c1a4401840d030006c002002c502203556921105c40c201121485520b0782c032f51500c001441010004000365001d41218030741c0500000101c1846040d9200140c0341d103104803032140000c0d0405110790100c0d0250504000841c142c031903503608529201070300347d4004036000c01c800004605c1c446c03103405960200089900411890b12096415240da0f0061107440f81155281d400408154039005182c600172803041b8001c040d18a00501704 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 347184802 1250 347183552 347183581
    0x240b1207030e0709090312020324060f0a180b04121a060d08090411041202150a020703020d0c0e10050f04150902091206040303022104020a060f02010e0f0303 69
    0x1090600c1c2c03215481040c800083c0b81e0b0156810032400046910b400d08040e1060541c10081030301280c0008104143c000d034180b140906002440300d20007554800404000890107041c25804180a0604c088403140e40300f01210003801c440680540e910079150740c84283c2079030207900b1022107031018201d00300811036505048164041841c1354211182400720000d0302181c070503900030f80013100100d4151000c1d90baa52294140030400b410b0303141c1c0c4035030395183c00c20b0003960301c082a0704c9298202605290510b070501110359904059002d0b00c01c02c2c0c19a400c004000d03c00a5007078030418074040e004164031385800c0a041c002c140704140d0300707501c52034207080004070940c03a4a01c9010301d0a14028100c000303003042e040815560a0304000d40c0702d400b402c0102d044100154498050352180c102400241600341e030050210f04108400d1190b414000040007a4a04059800075004245030034100003080c41848841803241c5688000304400c008078030120300d42034031001301c0c2460f60000024007a8a60f8030019 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 347186052 1250 347184802 347184811
    0xd02041403060a05040b01060804030e0301060602010c0207061803080c0a05060f0a0c051c021b030706060306060e0c250b07080f012309040606031401050708060405090a06240b12 78
    0x5050184c0d2034155519110b81006100721024041c2c0d0700045030416020307480040c40032401030000c001039540c84600074003901114070350f07a000d030085900210300c41344078174459800038a0100d1495446803031559800c10581c05520280580e0107041030f00c40c000340d02440524004e4607092000c28141c1001503005084420445a00042c403104001c10b81c082240c0d040702010003413000b440183c80340302080158052811403900e00200d404001000010040664000801e9a0082c0740811131103440c2e4030501d4590700213454411000c8070500243c00d188aa03211208100065a1001004403202d0740d03503480c3c1c1100941741023010415140c208600c0003401e4903c00d00600300c5c105c643e00e0031a41c6418860b070344094860b000740154081800142071000030f1300000011584280540340c1050400100341c001d26050700c90350005244d01010030000e00d02030043e140070b003e80202408042c00656907120040200a10116030861071420f500e4446034500c4000c03005244c80444c440e91240c0d83d80700c0c4010b0020040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 347187302 1250 347186052 347186071
    0x906060304050a14120409050414030702010c0602070c03150905010c0810051507120f030b040605010806060319020d0204062a140f0105070504080c0a0305210d0204140306 75
    0x810007010460005001d0f89440e0001c000703040c0c072540040b0342800e2550031100c2810024001400083d20b07411030744104d108038090b80d8032080b20703101d001c0061346034480e94101900107080d00b1a61004034040d5402050b00078881c0c0c40c1364030250350343d40d1078103c41c02c070700c9009000e4207680e000d01c401840310030301946c451402c86241031a02803030030b07244110341b1006e40e01440d4002c0c000b005501c2143d6409404807542d258208540c3c1c0b50507101c2e00300042a4590303505405c8002810410810240c2c1410b0054505540c0140c40c0c10210382d032040c09000042d000103003111aa2406404103030036001031840208000d404003040541d40d00d08100e00a00b0b02d0359189d00b04010050324101040c401504251006035440e4001009000895400d200b030345402c4060040050551815050003045a0800c000f00101d5004c141540c42603e420010000c0c0b006580c0300c050541d80100800203688078003005280a4040b2989250303003840160301c0450200e070040d4000005503410002062081e00c0c0400002d0750080e00c11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 347188552 1250 347187302 347187307
    0xf0605100303140a030608030f0a091410210f0e01060b040b030403080612240601020d170901090b0a091a070f031a1816030605010903020d0204020903030d0605090606 73
    0x1581d00415100c92545060f03038070007010400c1c4038100c1c40313508450000e04081084076201d002c550001c100907404882250007140c0341c29000141e0508640d8896661140240400e001007000b00f820703110346100d4a184140503100307145003001501144a401036074140c003240012607140072019103084582c0740e0400320340788c0802c0c001001021002d000702c80c0e100d949403814180d1030711520040b80070400020f040300b00c0d40c0180b845814a460a641c0d01e00048050400c0a07402601d075078006a031250306e002d6858001801004122940000171400c0c03c3d0005840f400005441c009903c4003041c0000984003421499120518030b0140851908036003d12000094000d0442c20300150181210901f001450245078883c501070190f01810004402c10304005400082c0483c5104003580085100700d0f00b4100c0040810b000141c80c2c1d1080c41200c05585040e110b4a001c142142c080181d00d016a90080760f01c03c1d02040486110744041c00075051942c00d100012800358205020400140340c01000c3c04e01403c8207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 347189802 1250 347188552 347188559
    0x30c050a03152c0604020f01050a050d0504170f0301080d050c06070c0303060e0c03060102010f02160222060e0702010f0218040203090109081c06050a06080c030c0409090f060510 78
    0xd44800d00e080c000081c0c40022900301468500b03c80c1d00e00321800c24008800c0e440050704940011400c58400e42c070880720072070280006401501c850164071040400100c00b48190307210b401890384115082406202801880000d102c43c42c44660f04c03c04454080ca0404801004880c008000003240b1909500b0118107122010402c1607440c00001d00980c00c0002d00003030f01d0706140c0668414030151503107002d079032280c1c40c00d03065843d85644260703413603030040d8a04040c03245003002c14800d40b24000f580b1450014108626001c1100f40340540c601e216501d07000e042c00407215401840740c40000d19081583e1243d92824101c080c0c00c40744000844626240100074030348900c4c01c100d407071841c901c904690060703e940301c00641a005090300000241141f4000890005e0182d000c90b40c0481d00454034414001039071124144a082010780c45004c0119007c01d010031081400c0380e0241da8003500d01030885090558641504055403011201958500d03828805070050142a00607554080810751000903200d15 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 347191052 1250 347189802 347189813
    0xc120609010602030712050408030a050c1e060a020702060912070807080105160305130f0602030a0f0e150403050d05040807170910180906030c240c020f0406080a0c030c050a03 77
    0x5c4e8400c018040004070b104612040e0060003502c01030002c400440ba203c864482e0043d2072070340100c0004041c2c0c80340c00e0103a151415400403040302d80310081c020b800c458a814007140043d410209040303a1100c01800240003a07282d0040103594501210010a01d00d80b40c21002428091260001e0202c0d90500c8100070600454030036910707040840e0301d400100d6a940405030300240340106001401c4d50560310384081880000c1d006540541640e000401141c00c40c00380540c112050351701c0a42e00ca8012400080440c0010f4008503806406424100e152a418007416011100c080b50200c80da0300340410981c0500c400c030503413120b10096452410b890080034400082d010212075909030100207101192100f8444043c1e094001890280018000703161280f40072148803085000300042441d402040d0002c1805010094040046035102c3da0304040a540038000131101c825855508140c42d18000a0b1120007000281c5840d8003c00c81c400c0da0b00d0551509100f03002040c2e208501ca0510b10300140302085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 347192302 1250 347191052 347191057
    0x510121121220201090506031504230406150e0901020c0c0d030e090421020303150402070b040b0a020f0d0b120c061204110d050a0c050414220503030c12060901060203 73
    0x4010900c00c202e08092004031210b0000c1d402c01764004901000344140703070002048042d24628100c9060040f51600f1000b00e4503c2400e82c04502d104a5a501280110f20a0b52140c07aa00b5642184020240c1d01c9690b01c10a03000141d0b90541140c0d4000b071515503000041c0003c45800b04102c0300c00101c035680f5240103149a183d09840b612070105130001c030b01042100f01c003c0e00320407060408022201003410300a074403900211050a2410710b26449071156260501c226242d0030350043c0e994100c2d46450703c13140b500080050491380c16603820000d00c0c240c1000d1001922618022110129101070082c007400360f8402d202150b07003850350000015843c10f5a6030f4062340c044540c500079800300c82d9030350b091035145408810790554100744141415024000045441508607008003000020320780d030380041c0001c0b0365000860760b0301e0080050110348407002e0051704407101c18410454a50030b0415440711030071640143c0b61030b8140600041d000740594000c0d107002e035000c241124000c0c1070f5890300b000030f500d0380b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 347193552 1250 347192302 347192341
    0x914060703030e1e0a030206060a0803040e040f0506010e0a0b150d020703030b180f010b0406020d0c050c03100b03070807030206030a0b21070f090b01090510121121 72
    0x507031902084140c200c004c200a620000d104100b8900d190341005801751603c4071510282e005014030400140306d41040303000d8404682890008600d40340c60400f900388041c1000c2c00c21101011011401d2000c26420800b1074003074045421403a40d0f0b400d0a841900440700d0580d180c502520081083e4141411a04103490803184120005030f03661f01140b030110018615a52903551003590b0345228a26a00b080140c01c1c0718880114400e0030b50313600c8a0300d821050081d1320602c0700503440400c0020919214900070b0000c248074000f01c44050b16120b00082c01c040a12010904065442240907140d01d81001070400611018002d84200c90550700820810b00c03004098181994954207680030b96155658281d65420b00309510b201021810580d094642606210705c000350350042c00045640440780c4681c0c84000c40c16124031110918100511101300d001740748900c180700c2c01d808200508640ba0190500289409030b007507075034030010140781c420031190008189000c0310b00e07000c120328188030360041000f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 347194802 1250 347193552 347193557
    0x3060106080714130905060307080a12031103070e01180305060c07020d1401020d060e0c0703030c0905040c031b08040308040f0c05131b02060907030b09120a0f0914060703 75
    0x5aa9100740941c1c02c90900c4000c50554040044d0207072242012000030030035107810f42c4052060340ca03074004141c0e6600c130318050719500b9081078002500003801580d1001d041c00b000d0902041040b803031602c400842d001201c4080200d1002c0224070b0141d0303805081012403110080d4201c040764110740f251035503400003c20240103040009151815540d0700141011615417001c0070380c94102400c4803081c041d41240000b8080642006008517600440211241c0724014081c040c50410081e0b49044015141d0a0030349010b0009098001c2803544075800b03458010306083d200840c04000e5400d04c3c085c040350300d01038181000030036170900001940c1b200c0515082034000000c81103923001800d04407412502d41d0b116540c040d0150585a030040102d4000c00c43c1d014910700c1941403440c00030700603610f526080b60480105c1c1c21607801400021036101c482c41e005800d480071101c800120680c443d07210740c44003002c440400c030f2403140e200210340c0c0210f489024200c0703510588201c0c80300c04041402402070920003401e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 347196052 1250 347194802 347194817
    0xc090902070602220e0a090206090103180b0c1c0501060503041403121018090506070c0f02090a090b070216060f0509150d0b0616140a080301150e0f03060106 69
    0x2d00207690103030b50444d42c44600f480301e51000851003049901d001e228251140340030500091101c4e59611a01d8412038015107100e02d0510620011001411141e2106a100648a100001080c4c0b60000c40b445541c1240d01c4c0c95680c2e6905416120026404124000d142e003801700500c29940d101c02500c1d0000ea004106040401c580e0703241e00d04500491000e2000c2c080718070f00304100312900500d1801160180305541e03440c070414050340c5068841c040400b4046130301c494041790b001846122440042070181c010007042e145503500040c03940700c05a403070090040c0c0303c221010510099580341038006486000804100b4004800c0d80c002458601c100e2050060381721404449a0044044400003a4000c01e00b00329035450040000141e004400350340c1c0000c0ca406001c1c045810850115200000308a010882c0b0a1050341e5000d2014148007000c021401510401c0d8000b846520145000e48811049400728418030301c8005d02e031619058100d403190240d180c2051050700c010030814107654003882e0421 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 347197302 1250 347196052 347196067
    0xc020708120c1213150e0a0503240c070804090212010f06170c0904020a0c05070902120a0b030c030607030605091501052a100203040c0504020f0301090f3b010c090902 73
    0x8060b08030551010b40c0c0c4101c5401038000c0c041e0311003d5141d103106c04880062a094480f0281991048100c1d0850440d004400054140048403982035510941d80281940340440c40c1c3d5036640c842e00582e20440c5000c4d004038405000b000c1c00c007007050261407a080c0d5118228039151004041a80c0200040255003089020424180041c0100c89070101c000e4401e550760780c9004030081458104d6202980c5500841e500403038160080c0c002c98001d540540016051915410011001001240300d516891312840103c04000d460501020307114004648001413580c5c54a020f211507101c0c01400e46907500f44001180c102030383c014007600c4001d02c03038415800c1c0c00704650407002810048442c1d90f040500c80c440200314000340940041d40f03c0c612942540780d400369070b14248005d07070191200c0303d035520380c0510040c015002c86a02170140d1904401003c10305c201d200c4032119100035283c88004070254a008099103100c0300c228031035044820b96008002c400d0480e40024100c2000380a0441007030b0f000108030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 347198552 1250 347197302 347197327
    0x30c07030215090a1a090d0e060d050c12060a380301080706020c09040302070e070201110d0c1710140d050312012402030307080601120c020708120c12 66
    0x10b00707600501590704a0504065901554500d09444201e800303010030700702e20f6600f2400e40c0070580201e5100f001480380c07482400c0252000501d010700c09800c4036041c40b07403440e50b010902a042c01103200040d41e075580c142490703c007a03801d10018001d902030030300540100541d501d4401382042c0704201280d1070340f4400440944d06030121b0136511003a60500b010002041008020800350308841d015002c5030b0481451f0428002507801c00c65000d80560002c42c1c00b04180e0f05614000e40e4814964400000d0600f007803400740c800c642002c030402c4401e035030f60502d052031560080c4a694608854100c60505864011010305041140d800307502c11200c1b008602c2420741c0c440c00d03801d00096074444203176510303403200d105400c100c001d00b4030981c140d254181100d19800c64140c030508020070b100d035018518603591540280c41810f0054100390401585e50035038412900103114210f543d00c01a8013a10a061800035100d151441144000800880030840d12640000c00144551a8480d1090103600c41d048207a08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 347199802 1250 347198552 347198563
    0xc020924030604060c1d060a030203090f0a0c0510020c28030602030a02071b030302060a18060c0c17041d04050f0d031b090b0d0b060c01022101080d05030c070302 71
    0x240d940602c50042440104503079a0880c070182e00e825900c598400e43d083d500400703031221001041e9002142000008020b6100390001c65000c0716080c101c0d032021000d11880307403400da034800d0184c8412103025018010741c82d11134034840000400d8802002401101c400180b0380d6180c9155610058140d00382d6054450f6100d29490021500b04400b1900c03860b14a1811019601407041219a140080c0f04800640d504107194425030384c140c0d00420361a40c030742d02008014205198404101c1d1141c03083c1600140940c0140d01c45c482041d980d0040840c0c240c41c040000d00c03c4040c02002c0d07000300380020310058081e90081748041d440400988015291420082e06105012803140103034000e400c42c4e0204140c25400400e048030742c2d5220300041c228038040c1100d04070100c0c020000043d01c00c02108211442c1d907000300d400c0342c0c0007c029918100c0f0201d20182284c0c0000100030700707a00180a010108000421000e00518654010b0804d1b101e100350010400d11005181c00e00b0807401050040516208104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 347201052 1250 347199802 347199871
    0x606210109030e0906010c1e02031606030c08070f14030c040e090a03020705031504030c050c0a06030e061608131505010e01050910051f02121210060c0209 68
    0x704140481d41c2070051091900c0d908481c0591900300c0859865480f0307803420080c8640002068019200701d407001082e82454103000c0e40e0610030542855420000c000d103810042105c0c4d10002204001d502c07000c1e042020003420030043c803071526074002c00303140c0121a81105541524149a69940318040c055040c01aa00003840720004141040403580c0c00080f0500010f0081c2c00711940071703643d0300400da910000c9407200c246070b803240340102e400a409800303504411842001982c28051407000840c0418255074002e500294840c44100031020701840243d4102d980c410486905079801c44020f444201c001d040000c9400c801c0c07241000740041404e48400700c0c0110042400696591240071051000038000d10344550344240c04030b5036418107801c0c0702c0300f240c0c000740428400c03a2100b204030030789006600003041907000300d0380c0c503200c417250000082c010161717180b48400301803d00c01c0301e42c910b1500541140c4148041d403240310000d0b9581d0f400d481d0f482046842e804035040880040241d11810a81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 347202302 1250 347201052 347201119
    0x3050730021603051b01050105060f030a0b030f0d030c0e090c030601020307050a06060609230906060c0115060908030c10020703030e061302091f050609240a09090e0606 74
    0x5500c0b40070598450018003500c2400a51aa81a41707200d042d0341c200c030310031300c10590312032010000240e9a01c480b501450380000505800a215989034004ca8201404034800c00101e07081030307a0600d04c558041c41203d180f04014900440c10007486c0003c07a0840601914401c62004003000090301c2d68400c200b101c40c082c4d4000246c0d041c4804c18503001014102900490010034641c40c1c2c080f42e249014041c0f48041001c45054440020220040c0b00f540300020301120b4029904000c1e1081d2003100740155285c2089400403201440d15100006042c000b298102030902d820400106400d0540081d0014105110001c016501c407118030301540101284000451b4601907001044400959a0a11100c5a0082e1000d0300c40340d40310307001880c000480b90000342c402c0e04d5240003840301c0d0038600b010701004000680310042501808072211469051400940050e07080003515505041e8000c11140007425001e80500c45142441c000e07988550009024500460f44100008d0342c0080d40c3c888120f4100b14403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 347203552 1250 347202302 347202337
    0x30b1503010612060c080609040f15181b08010203040201090e130c060f0f020304050d060906020f07050a0615030b070c030c2a050d0203060402221a010305073002 71
    0x5181400180502c1807a003004500ea00d0009041c0e8203123220443c2c46254800c4015084c20865612500d07a007016230b1005d18411b54800414041e2141311400388103890103002e030186c2460001000b40b4105c90503070055503031a4010703c24040140d070040212802e440c0190b404100c035a403080200c2d51030615410300034060074241703080010b01c1d503005400071020349801e43e0780101c04415000107a0f5030388a24402c076a0007103000e40300310000c2000c540c44407403101e201d51005442c2c194482852682c81d0400d070025100e5030402c0c03070460104803051007003000701175226041e84d1015141d501c40e0b024001008188400340010005103001701449822080c110642c0044070100b500c41c0071014a00c10140e0603a00c141446851001043ca0300d08813000b944010b60050082416035616030a000e032103c1101d48408180440600030044101140100001e0311010625590703464004000103094071006000c4100340320140100324134603609800c00064103411070a9070784030481030400781c000030b1007000111b00600810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 347204802 1250 347203552 347203589
    0xa0c210908070c0302010813201207080601180911010309021c140c0d080d0209060d02070b0613050f0406020a2303040203070b04060206070f05160311070f030b15030106 74
    0x83c0840d03802034a000f030303070f40004a681740150807050320362055002d0060444040d0301000c0d03105885a601c00ba01002d0b045208034424040f07242d2600560380c01200c0c00d504041e00601c100d858800300c1112090300c507a1706000d4003045858441101c1d2041000d2810151100004800e54071910a408a03140c040c8080c200703150818105081d44503a0036289030803902a80082100d07505e0a260550900360f004008a450f14600c8451107000750701c1181581d030000d405201c204142d55151001d01411805005c901e50a840d2240400045001c1c030030b40003064901c1c0c0001c0c010b41d9000c580036150310541c4280700580d1052000c1058590380100707107082c002e01d50309042040000d4400c0001d18002d501c00d400303c0e0f86031a11100c809442c2d02030f5004c0c0e040180d01140004040078031440395508010028108289402c0082203412089900d9000075000b10348080e001c0c021070307a03003040030500410740c40e040c170300107103080d680d03410030712000a005090385619450b041d15081d50300303500944c01030001e03003044880d0411 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 347206052 1250 347204802 347204813
    0x405101d04120203131403072402120a05030a0c0e0628030507080708041514060f0907050405010e1c140c01020703030c0f060f0f060503060a0c21090807 67
    0x4031411038551080d094000b1400340000255030040c0711000c00404406c1c201456100200c08050ba000c1d818882c04000081c00c040030401c060199000d82441c00c11280385410282c98850620005000741004002c4103c802d5401816a5000581c564001c26100006501220403141c6400d025038844c0c1e002411002d900c50201c2a5118074141c030b44011f4200714050010740481d0811600da102049040e40090091032103822600d034020b201c0c0903240070315021408034030100e400c0019454600c44198007841460b142c040b0103907041200803200c0c40d1103442d0217039004045000d5842181d06011080026086940c0e503100d0103849a0441031611800c0760315030138400b00c62440310078040c5140c020700e05140c0c1c081d4408a910320960390191120146a6020341c1c941d407011100300c000703540c425545c030080303111181c440c020b00c5000100c1c0740340070441600f06001c0601702000a00107146091504000040c03894101d050305510451500c0702c0780d01e082c14801c01c01d01910040c0c000810110000420704200007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 347207302 1250 347206052 347206109
    0x1503050106141e0307260604030c02010813050309040207030302040302090906040c0801230a0f110901030606020613020114070c03080d050f040321061a0c0c011d040510 74
    0x20b08441c55030394003142804081c0254100740a90307030507410800b01402004842e11441c2043c890302002e410140b0a1100458107040382540d0131400605040698804c0d5030744401070035048819060512101555656210f0f85c91255122407401140c01003540303000d041c020786c1a0707001541c0141100c00549020901d158407082c0454044a0701c003450b84010800000501c1070250721403160081003000c03000a149441345074001130007044a1078070703084c000702500018040d40032001c1d1401e80950701c3d01c064600140544400d0f800c00c02c11075100000304007020030450810080d940c0c0a003000d40e040e05c40d4074803000c1c0b94490b85502030072a042d40c0c0c40010801c002000241030f10725807082d0411194580442070a5864801d403001b8000030907001004441050f00c0c0710741c0018042030807000901b00d584144401c880c08401d01c0f44d920114000c90140e5440d1400c1c040d018804009180c802804520055102c4085c0400d0826902565450000410184054103040045c0c44000c60120000c2e610102003c50718 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 347208552 1250 347207302 347207339
    0x30a20100504060222060504140f1206060f1c1707050f06090d17040b2a07060e071a0f041a130603111c090614150d0b0a1503050106 58
    0x200c1d40850811100d406040b001c1c01a01c00550711f0074074003882d110288050700c480d10300c01684100c10740b10320766480e95a200c0d05403000640001400442c0742550811841755030300f104060042d003d03440b00300040040001602c000d90f900024052131000324046030410f5000b207880060a80c070400c1c98a50310031500141c1d8501c120300141c220b48125445010413121070070b01c4090750081010b183d02050000d9513200400341d20401d0540c482214002d820f2a6802c0d44a0b000800f4103600d01c0026402c2c1405583e0255248542041d00141202c51800242141c0c04030100c2e07007011040310105000d801c0700d9110044a000f08003001140c048030454001651055020084d001e0301401d0403a0000745a9000b0300030380f490441c168141c2c41c141424420714650070b02c07042c41095400380c1c2d00c8590702d00188081c42001782800d4810074205592401403030400c8408445209244254040c03254503000540c0040801c0e40521101804512503103820044005142c0581004029500788580841e95100c51071094414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 347209802 1250 347208552 347208577
    0x10c080412050f120604140c131d0103140106080a03092606010b0d02040e01060c0b090c0d0602161203020c120903070605070312090c050a08030a201005040602 70
    0xc039040d0041c1e805104203080003c1003c000d2155004032085030080380d51008001d4404200054018020913107481c0c1140d069080800c0030410040a0720f012480102902d2450300d00130408901d003c8408078440b0510004024602e4403070f40c00c0c002002074002000400c0010211aa01e00c25468068990030041c0107840d0707950359000c120f00d80070036080e04044035880700c040640f589901b000d0340b010442d0320a82000710251740070000052140c1c0910481030080070140d0322500c00d0422072400309440c0c80041d0006290707912456807110309640d00c40f00382c0c200d01c1e4002401a680d9000e0b5446020500d4039603c0542101d0504031252001900b54000b011949a0300c810307a032980c051529041c007240141c1000b507805a20a820601c14540a44010000f075406410180040e20020708031105980010100710358841c49c4c0300c01001107041c070032a418042d0401c840035600b480c0c0010380c0240400d00319980c0340c007200b9075902c0d0741e03840f83c0c07041c001c1d140d00310352040342844540741c2820000c000e9884217a181d4034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 347211052 1250 347209802 347209823
    0xd060515130509070c080c030a020f0a110f0d05011e05010909050c100318030909060509040b1b09060a1d03060106050d0c02030f16060f1104061b05010c0804 69
    0x5420303084084981404034000740c1c6010307904041c10711503900001403000003030003220000c00000c1100580030b0500c80d4846802965134005901c4000c2c00c0820481c90040150300811045001035114014429501030607103207078404040540c00140c0c0710041520150040d46000c41070307005031140c00002e41148619140a004690340c84000404030b88850101401300d410a40000e9124600088418070000e4289808a4105400c04110410284850045003c909503100400036151701e801000011325007292404041d203084d486101510388010300c10300f10681108101c604500440c0150740807a0009040305403200c034120405054951201d681c42c45800707201400c02c44034900051028145d8006a95060400380241405400362046002c04000e6001c203002071315219000034040e181c0724400300c501500781070450508904850022000031032407400c040303458140030008402c480442d003040c5403080304101c100030003c0803142d0b003440c0205594208442c4106041d80301216502481c020300f40c003032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 347212302 1250 347211052 347211079
    0xf020a03020304170a090501053106120b100c02040e100906110708090d05070302030a0605160e010e12070504021204020109080a0b0711100f02041e0308030f19020d0605 74
    0x104a001308050200080c0c5645807e1065500c50700c0504a01d80f8204c0400c01a6031001001022000001708103529141c081c00c020800f440d400180d0f00e01e513140c046002c000140014005c6509105c241002038184110090400b0464860358042440010a001075601010b0b074032100d54081c0c044800b00b610942d0a03c10b55404425a240407a0101540000c215142543c2403040c08042041403105603954020642c00001688080c81000d00461050310002001c1c40e2902c6521103602800c07549608114045c4180100c0b40d80290300099210004c48020307613250001601c0515100b225000340d40c1081c0003040043c20314406414060246101f620b401034401d0300c83c000e9954400c80f941018003040c0411020031040d034042c080d0002c0e40200c603401d4800e01000905205c06540d0121829000e10703600260070003050800240c521000c01041c3d8551403001c0c03654a51001c14003015000c10803154a80010440a15504030003110704e2030804d109544074810402c10600602c2e080c401c1ca40101500020764 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 347213552 1250 347212302 347212343
    0xa050402030606092716030c030504020120190f030f14030a020a0c020301231005010909110c07061d0402120a09030e030712050c030f100e010f020a03020304 69
    0x1c0b44540d40c041d103481d050031800000c101401d580111100b00c0c2e81440320301c22044501544110f13109004201038000380103141c20006003140c25046c140e02c00c051504041c800141e80c0003141c1e415031441c10010140904440c4106410452441c4444c04079440302c202c4041041401201c0c040c4140c0a034491180c0e6411022007034559103454a03440c84003500400c002021512198085e125102042c50401413100e00303903011908542d20a540c0b001d0454980540c01c80b5514036078840b69100001c5140c1080303540c035180c0040e004090034014000515124501d0300c0c00d21200100ba21a102c05d12401c91703401540e601005080c10348401d070215031400352138442c4d0740142042d000311100420000c040680650352449400c00806c0090011000c03c40319036541381140d80c0400807203001d00582d4109080b040d002d40b41540c94421600b000c036010750420f0076810f0395981e001c245070f1078066100d5400724101c010591400d004003205c0004845561001c02e11300c00f071540c10f90141d03100714400c51040c001d003001403205 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 347214802 1250 347213552 347213557
    0x2a0506010905220501021306030b03010c0905060703080603160e0703140c0f03041b0b1c09050c100e100905010e0a0317070813030302030c1b18060d0b150a050402 71
    0x104103c1c190b2009011084040541c00305900ba02480006080c00d8192241c1008101c195106500181d114a08024580f8003803090740c3c45805581440460903160001044190040c020054144816100001d825071014041e121205540000c40100144c4032500031440080507154040080c0ca8482102d06c5101042000e0b80070f0151848100e08046080145603900d50000b807040700ca14503101b80010b0761604980304400a80100034525848008403a10780400c040804104070485040c00301c210085140840d0742030854005850403440480b5492003643c0c0c4d01c0034188031a400010032a03603629a541e000c11103c06480302603807401e0100c194501048403096460102400c6050003954401071500c000c0001c118552245040b1410034443d2002d50300d03040c8541e8801d40160b00001900c2c0c078556428031040400410b44010b02008292000102e06001c200c0031540c0c5002606a0108800303680382d002c0090801e030b00040350001c070701e0a15290b032012135800d44903038010f1480050118542c98039009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 347216052 1250 347214802 347214811
    0x50604141e1507030b0d050706180e010509040807120206040b0f0f0106030c03090804080f0c01050f040e0c1902010b01120c210908040305011a060a02030a08072a0506010905 76
    0x1060220030b4080409800340001d000c0105069541c404003000e510f80e000c0151055014401400607a441d040002c0c00074410a44481901d0340c03d42018800052208101170644170300b91081c451603515032420440034860000003070210804810364080b40ca900080042c4075a1081e0320302d82a40d00d42d02c0c1a610000303416540b0742030040e443c81c010b0201600c80d5100c050741c06518030300070030591800d8903801299440f80c0c01c500c440e0381000b0001c603440d65042101003100602031a0440c50b050710300c00d03260820b0140b8042c440310a10000041510000310400b6107950950b4040c116600304064180a40240700c20314040d804148030000f064040c60b01d0344904c0f102e0074141d85905154280c002d0b0540b1844c081d1010302222176a0352031180c0c000c110720b54082e00c040d61052000290400e8900c0079019a1100c0b000c450f0b100703c0f000c10a0040d4107601001b60340000b4071a040c070703c940f501d0710b06c41a0341100c07101401821600021074601c0300ea0800b01c80180b9058082c0040c0c890a0340c880c800101070390001c49 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 347217302 1250 347216052 347216113
    0x62401051804050402030741010507081c0608100c0315210b0f0108060606040f03030e010e060307030605090f071b080c030d0f0f05090d0302130305060414 68
    0x1c00d8810503061680103c0d5125100030f0954800540f6014000c0c0031660b4029244028084c807074041c2003a44440d2011004010981824504c082d49800001c00521440c84001c10b04140401e407481e00e03e40310050040c51810000b02441042e03162454107958102000c20540c4860030301615803640340c003074407848400340800031203403000e141488160104500758640e618090305610308200041126a40107a0040c845036080c1e40700b651400111524110019008600c1f807a0b041004210701c0346809040d000302d0380d00d401d0141c10403c960006072504d025910340340d600310380c0010030800d10f40d42c10345c84241603850841d45000c1079100c1d1680024030030f00c101d6203100814080048084004100c2a254050070700c1000803600d0b104e109a0007600755041104c89800541d00d40322842880011801114420303080030324100018a051325040ba40e440d03102c0743c01c00034035034002608540400503102d40c10103140c1003000c13100c0c03a0801c1c0c42d10044810080c02245104d0241745032280000d400091203004152052 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 347218552 1250 347217302 347217337
    0x3080720060d0e06060f0105030604151701021308070609031202030904110918060f04021b01060303020601151818090203030403080703031103040308060613030209190c090810180506240105 83
    0x70022f1100900ca20703400c00c0404a554940002c40922203141094240d0000340051b880d402c4440c120204000c907504120041d801550b4103204c03482d881240c0100300c03030300250000342c1003401ca10103905600c941d5030003a1304641490ba04440c0c40440340c0040006a02c151101e8580c140c126001c4194104169003071503010300c0c6000b5000c4a45407540140001c40d60700c0601801c400c3c5409240c60844000342d20441c05a0813840040000000c040303008040b03032201d800d0072813011a00d112061030080f42e50080310740742c54100c40c507115034213003551011040960140c103da075180e85a003409141a044400220f00103400c040c0207072a4011603200b9240106d903d07444c0d0038441e40301d000c00c0080c542c00074050180c802135540340c0000903a6490540601400400240440b40c403601a558020344215600000900142600400400200103088020b0034000f40000802007095104100d4160071540068500d114000030f220351180007405020034501040310018040100c50010358141c000c0680100c081c1000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 347219802 1250 347218552 347218561
    0xd030902180c270102060609040f061113090203060a0503070e011a0d06030807031202250f06060609060e01080c12090c15070b0f0103080720060d0e06060f010503 71
    0x200600940000c840c1d400702d400c1001408844078a8110310104192102c4150400101560180b050b644c014074207680070415850030f41c5600303030411f02c080c600804032613496480c1e650a54400082d6000300300d030000162412030383c41d0710710000b83d00f05540080c464034039141c0c0081c8520300010040c0c12598241d5040403584c0c0784c404610703903903080840c170000700500411900861011900c5880b01641c030940d04d90b92035050a00300240100c00280008090754410000e10100304010104501390721954140242d0a1110349055030451485903402408581040e001042c03280c0c20040075030030f8400684d21aa0f200122100440701044162000c2400707110401c9510703000030b806899190321462401c102e0b95502070110224000c00e0351040000200b250200b0543c04100030103401d05c1e008150640400d6407075040d504c4a883c00c0c8200ca0005190390050940d48200502d100701d145c0b4400030051896032100050308451024100d884400d034454042e0000080c5c09250988182801c1c01041e074405043da5207 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 347221052 1250 347219802 347219839
    0x60e03040f0b0c0c060712030f0515100c0503030a0c12141b07050d03020301410310050408040302040c03050f06150c0303010b1b07080a0303020306040e06090a050d030902 75
    0x418070902110f4081d0507103a03001500e03444d000740b4611f84580c074a0101100c03030000003800c17140c8692103c90040e05140512868050540502101c118125807070400b420100303900303480044c00030301c006215000c0441008030405050344146240602134541503580745009040c10100c91107100200c06e95105540800c0e0b014003d6010780040f204034228403031809040d81c44d044d02c0e00003000304c035100190f00040144000101c400140b0030103204010096807458445080d8402c4d000c0440030740301440c1868078031141c0ca83e07040040c5030709400704200411841c1414282202c440c0c0c4140800ea0069040909688600d842841028802c0c00c1030030304104281c40e2442003000c80c502c002c041e89540f08060240b42c07070540f02800107500030030700c65000c0744d40c0744c05100c0140010012000c0350515904106410405e092020070552107050345458016a01d5a039030000078018401d10a13641034610402c4104401c4080000d00c100c180b60040d0300f1100f0000100c00300b202030301d0035044000e401c035011640745200c42c403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 347222302 1250 347221052 347221057
    0xf100903031d0409110f0307050a03080a030204031a063a061d030c0106140303030a0203041a0406050907080f07181b02030711040b1503040201110f0a060e03040f0b 72
    0x200340e54514402e000c086000400303540032508242c69803032010300703940080c1c43c2500c0000d0b069102680a40200b610300300c006034082c8054400540701e00f10004020750901d00c03980c1280c0140d90b00070301c8034480c030400c100070180440e42200c0b12030003000032900842c4000d2000b541c02032901c05039070007032484150310300f06445c01c04501641219107070384481004100003030042d003070603120014100554413070880030718842c2551025130240c00c00610020340344040c0e44010080b01e074021280351015903a6201c41c5000c055000d4140d65890101240100740000c00ca229000302d4021605101190035664603071a410391640111314403500d480c0d04c040720030010303140b4100f1100b408844041c07001800340c00c40c07240d0840d05c0302204c00d03d03030060308001081010021020703403c0c1602d440030307070701000b8181244001c90008240821940307095040400080c1c210ba2003a0000c0c03a030030b02c0032800c3d12003205902c4a40f03552070a04003011500141070004000400d000001507034229a0440041d0b14810702d82403104010340d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 347223552 1250 347222302 347222327
    0x509060901140316060e030c090f0106050f0408030a090612050606040909082503090605030106090314010207021003050a1808030403030b190b1b060420010504030615050f10090303 79
    0x6002c1c03084044864941241c40c10024085d40e00c80c02c003004a884101403c0030790528a4034400d40e80c000c14024244214030089041d183c150400503510340c3c1c50320f0850031a02481d40151050301c40081c0b2413140c036a002e01e079001101c1150b01c41c618114640d501500540380101d48194000d441440100140310541d00115041401010401d141c4000070324104042180d0000c09150341802840707283c2010750000110f00145124940a8213550400100070b00b806964840506031005480341050310070801e6044968555004080101c02c881000d8090081c000c04c580d004a003510f40000c0c41c00c40c1d074500c040d82003956407280ea00d41c035596070f0342d405030700400002d40c02c00e401504202080c01481e0300c0c400d650000e000310120b201c1d1101e41040c0308885d900421805012980c10850510000402c081c1c0e28a003080000d007041000f00940d01d0040340e0034041c030f82c009010241070510007050090000340c80019100140c81004407822a08240014500c103182e560000410840d402c00209100f651104900c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 347224802 1250 347223552 347223559
    0xd1d011409130f02031f0f1e170c0f030106030809060f0f1620220b031905010510060918060306091101080702241f03030c0309050906090114 62
    0x880c0440c604800448520840f907404141d40042030200140060840c0c000e18182d803294904400e0403c0c001c1c10000782c49208100c90200808802000e045e050340c007a9024140b003c01c600f850051424050384e030b03030410300c0460340190001820300d0f0b46800c041c010103059035000125149448000300902885610a95820020326814060039082407000c000611002e0541880c0034080304550500c003a2018500c00441e52070180d4103250000c075140e90008111f410460b0a10801c160001d08540d40505030b031390f0311140e150182b0206d5201c040c80000040751941e01540007080f00b652072021101c400b140302d0082d00c010403014013080160100c0e07007554010700d5000d000003080c05581d0b65540825070302d8408040302c2c000144051800c103564440310140c0d21107041e200400704264510100003003402621811078008104000050082600c048085240b5060402079082c442e03607030500801b016030a1100310006010114000740d20b24001c02d460380940401401822541d00c0d000d2803600081e03105159580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 347226052 1250 347224802 347224819
    0x12030f04050f1306060f1803020109090f150f08240402060d020d1404050c01020d080604020d110708070b01090c12050405160b0a1103070506010e1009060303020d1d011409 75
    0x44100041c080c684c000d081c0c0340c54804d990a030f00305000d0b080320010707140c403c101d541300c21081001d80c1c1e0169020013100d4254600160b5015801e65400142060000c7c0861540c01d5040009042174003841c074200f1201c0c4107040e103182040303882a000130710465021659019503170f0000308015182c100000e1130038142c08040185800d06000040c41075851a10703140350740c3d80d8400304003c144a000c0c4850040381c2402d201a0020503ca0b00000d010b1040281409002d0742d40800c42d004200c03003e40c03240f44100e8100d00507175213520303240c60b143c2e61503400613034100c9002404d007000041044250040240080c1c1d10b88402c1d06240f14441001c005001c000d105450340c0c400d0758614282282104001400b9058207070303540d50746005000300075000c10382c2003403040c282d940100500000300b00d0100702181500c2c0410341c4254151200d11032007400803200e411189000c0d02d070400000c109a00090320541c0c01c017054a40907641e00d402241220700c00c0a5010040c0400c848881140c00d8541e104000c00c0074080040c007450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 347227302 1250 347226052 347226079
    0xf07030c171006080304032306010303110c130504020a06110705060a090e070306090b0303040f0e1503030c060f0f0103150c031b03050411040908071403091201090212030f04050f 78
    0x10f6800c6070b804400b240d0030004041c0b05020320410207140d00f050840d9901c600510f80031482c0d46d240d50511001e02041900c0c6403400142c8414444440c250304014684840e20308c00c440c0035801032a050380c0c12031190302401000902c580c0250760003280707181141d026145040c0382405100c004d0340716209010411200560110305181d2401d0b0311406065140d0700000c0d8241008412000c6882c42d0301c181c3e100c1c0d44180f10801c100c034106142042900e91b006038040d0305884106075800ca074032541d035030541d041c0004200c03c6041d01e40010300c2c0380f10710380645425045850f20074020361b50300030030b01018042d5040494891200400c40d004000507012070314000079210507501c500a00c55010090010000f88c40308240414496200d401d0100c1c4c260844040080b010b0079981c20384644503080f0010b10b1040341601882c0486020306c02e80f81e80c54400b51101d940e91022460060080c0800081284203034a0a80a103d8101c000000c2e01c204200a010082c84c00b8100b104000c0c0c40c60003110600d13802443d109400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 347228552 1250 347227302 347227333
    0x50a0809191505100503030414060c0d12060b030415181407080114090a020910120602040504051509060d080c0d03020a110c01091401030e06070503090f07030c17 71
    0x40d4070310741c09066000c040144030b415000545001600f0b030f055101c00244140001d603004006ca408036050000038110b00704101001c41c800f0b010340b900c8441c4d5801030340043d004082d004410045071b040c44890401880c2e8a640304819140010f45e8041c0c06481c000024184c00140d5901c904010342c54050300d801d41011640c2c51f0144a81c0a11000000d6005540104034904003401400b082180d084030012413464502146980e50050f80c8010348101da8a001141284040743c10400242c249806002c4240d501c2e030510b076001e948070344030b000d00a524041c0062418403584614000800b00149158442d441d024104440e400f106401035802450400103168484400c100d07910031100035480c056198140300c4400f4024203031031803500400790001d410881450fa404894403050b0348182ca0403100c041c5244004070001c1480300042442841040148201d50b504400554440c44001040302c1500003290710450321560a072200a00b030f00c244003400e210303003901803104550344600c00007240c0600740d02141e070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 347229802 1250 347228552 347228593
    0x51b011b020c01110c040504140712111c020609270708100b030c0307050c0102070507030c061103030c030c1303060b090109050403170a06120c05040609050601050a0809 74
    0x4400045032450280a081501403007028580c8400b42046004900142d0000340c0b19241d504403244503960301e6000034100420251407942c011480f408603a07600da142c4102c51200b52191000341c4140454402080d8070340b6040500b0316074582c44600c0c121054009a003440025002400c82a0b403015001c4d040d4080d20001c0d101152080026540920b501d040a420250224001070282c4000002c4054103008600448041300e80103450010b4240d944c3d034a41c1421a024003c0e0325213541ea5500001d4800107120300080d504054a000302607000019640d007805075000700b04034400a209800c14030001e078814288401841d8488101a0410b10b4200302c1e43d400c1500300c605400444000d0303921040d00c1304c0c43c10010802c90142205038810000c07030070b264901501113840d0981298802288200098a0070a56004100181030381501c003107803501e951501d01c91401c424001c843c05280340c804009001c00d450302030f00d400b035281a110f0701c2c40c00340300400132240310310000d00100d0b81340300c1c40e40d110651040e0240f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 347231052 1250 347229802 347229821
    0xf0711042003010e0f040b071d060301030501140106091d0402030304050918150408030604090c0b03011502120a0f05070309050907031a010207060e0f031e010501031a01060e01051b01 80
    0x3401c950380c0d8103020341030344c4000c80600f849548403106002c000006a0540c10030303800203041e007041030348501480f506014808000c071000360861004000003040100c150070001015604032001525aa00d800040351451600d11400d018110038007006405c3e400a641c0f2142c210340003070162803501e62030748081826040709a84841c54038400c000e21864844d01440450702011854020034120305250721081032034080036060a02c501c1d48c0c6c40c0a00f0070071070001b200c03000400d10f548500c0d8903580d45240309953319403180da0520160040d41d8013100e500b0603400c1140d10450f4070352100b0381c0c40604040120750580081030224103000c444500031a0f50380e18a50501d10440c5c0c0307598007181044006034100210301c072025056056600c5500c0620420790031403002d1842210650310103001030700340320000f4a84440c403603520180040c09400726a617401c044d00720f141a0384c060700e620200b0781c0045c410480360020902c180e00018451000e82c40103907201310001c0001c1c440c6010024413480d100c2c0c00b05400c440d440f04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 347232302 1250 347231052 347231111
    0x7030f0b1504050a09020711061c0c1101060b030c03010b1e0f031902070c0605210f061c1502031302060c1510140d0203070314150c0f071104 62
    0x581000f16140c168400009440340100650400c3d159a5600c001c0800071080b07a40300710400b103029040803a2024102c02e0344501843c090180551040b4041c1681c00002d403810095400e00b0000301d03051000a044034095117019080c5403450f880c08801d64481d4002001366105200020689400c2c1004203004d08002d480b00720b100c03a903d081013100301c03110b6280301b12101d05103401880044040340c071058903603088880f50300306a0ba0fa5802c1950032004d4a414070540500503010f10240441c5a03200c000851107040207440c135004d040500030130003d00340c42c498801000c20078801005030301443c1c82d8014580240703040a000040c010694006640340d041a0600c5109500098564003c00e030f180c01036030780001d2001440d1101c103003003000300340c42d8100355180c8034000d42c5040d41c00c13403c6440802c0f101d0001e613000078842c0400503591080b43c2d10341e81581d21341c000440d03407440824103900c42e003000c513015502585003040c940100d55803510340c4011007020f6140c0c00f6582d24015040b115402d001e6028941d080c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 347233552 1250 347232302 347232307
    0xb1602011505130e1009050610060c05031806070605010b09040b04020c0a0b13080406020d0e03012306010c0506310c0611030c030a05091f0807030f0b15 67
    0x1050000c0c2103810003469503201185010741003049403503075a10200065030502010031030004c0d107480d07186000100d100c490803484c6058a0b001c103000d0086001d50080c6c1d4a013150001060f03030340b01c089a60441da0100501540c10810040000c0e1112014046c500c5030090032050400d425034071040110348003640f002040784000600301595180a00c1013003c01c8004960441c00c042c90f100d096a602c5004680040030802c851010070200d400c055103680b8695486526540e0f2039450380070085d180d203020800c001c089051003010007891318040c001c130800c40420041003c0f41000300c0f1000159420f0103051181400b00742031340d500205000b801503c1c4501e0081100b0030f4282a0300221031821a00c17070800110441848643e6000079205601110480390145054040305d07581ca0714150031403003100c00800282c4400a000b50020750404080d00c0d8158085a003001003598089041000503040040880024141303000104203500070382c00020424103201000400c10720303031004500c003881a00084414903102 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 347234802 1250 347233552 347233591
    0xd03090e0c03180f0304060318140106061701050306133e09011a03061503090a02040506040b010e120106050d1a09030f040b07060209030105070903060501080c0d020f0103090b 77
    0x1e01c40d602c0b50034030403503000740131005880c06500d03200e0281e8040c070420562a5540b408640c84000c41c1408001e42184407202664070303010005000384000e00c61400400d140b900740110010442c1d0569040320300250103042c45a0301ca0340445400928402d0484100001100082c1c6080840219408088031200c030a40c200030340e074100141c0f458440106a01c1400300030300601c0400c545540d080d01514080c0701035a00e80c1c4840c0c1c002140c0303a050540003000b000300441048102c2c07078006115450240243d4040003a500c54500344020303500c268404501082101071003903021704010700001d4042e4440000000d1950316400051041100020305489101002c0141d1040303100d400081600114020004e524019181001841c180140d01c5800d00459000c0382440a10440d501102c1030041d000300204141d01d0000d0002e8800080f038001564003d2410002141110303000070f0942e90900000c05403da8032129508001401d500a01520304064403911482c00003510200c0d2940210800300e8941d00b4050f6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 347236052 1250 347234802 347234821
    0x18030602070f022110180b0f07090f0608072f0f01180b010e0406090c0801021308010b03030f0705010e0604051b09060f120c03070801021b010908090d03090e0c03 71
    0x1490000c00d0201010135211551304c000000c2101110b14407100205003801859120201d844005038041e060701595002c00152801201d0802c0c82044140c1703a6090454450142280098050007050302084140c000300780400e0041c5c1e69480d450001268400220b0411140300509400b8240c103403006070b0221301508040c410a01507090300c942030089506003044551280319035201d040c42006140403800307011400348030b03c5cac1e005444425000a071500d0203a5803600003c1c000c3d803100990f01040c841c00d010204070380c2c406010700240010010001c604202da10032101c004c950001d4800ca030559602c20190b40f4404042c0142c0b4440c50064015046031a0171003a1011684c3c580c3d560340744165020010005150369000a100329102d094603403114081222102c14508a480900c183d418840d0b0301000401040c150002e241c01c2d034082c5806191400040d103e18261448400000c0c108101401035508a06022075000102d501a2901c15406170b82c0750054010a002a548c0d0000c598001082000050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 347237302 1250 347236052 347236069
    0xe010603110603040b0601080903070503030f07020c180c0c010609090c1d0709091a030a080306010210050105060301060e1302031e0115140a0314010b030f0603120a18030602070f02 79
    0x6400e42d1403c0c910b180aa070f9540c45070740010400c9060046d24404201481000c0003038961459100040325074904240d068646120f008980b684010310551f45c148080d03081020302ca21112840403440c101640395011801c441d03030050f140809203996545800104ae00742030159103c114011001c1c0c10b005810a035449081041001540071000220800c0c0301280d584078000000b242d00b100d200003030031f00e9030980300b0345202d00410907103515120b080e80c5141444007000c011400b94070b09800b1180e45e12100746204c002d0b15001d108055000c84181300420026019490b4102d9080b402003010a841c060a50607408036002918170822240082203550b101c084000c00f010701500508010351000d4407030140c010901001d481f00914510b1011541c1881c66029801503003007410f2000740c4c140c4640c7c4542c080089038000722074205070f100a000110300380d81800b107864254195a1600c1a141502d40d41b4192098132485a4100301040c0500000010481c14806003880c40d1084103c0382d4500e61500400c6800c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 347238552 1250 347237302 347237333
    0xf0210180b0d15080606060901140d0f0506180f0901140f040c0e0114040b13180203060609090a1205040b0a1106060f0a0302130f15080d08070c03030b03100e010603 72
    0x40361212041c13242d100c0006a495201404480003580c581d21720004940c0b0400442d5031480313100c00864808444031603a040031481e05d1240700c0400c40c503681c43c001c1050f00c1c1c800b1094447c4022a5002043d00344860b61407841d0710240800c00841c4a02004400500c20031040b00c3c00402d592412081c44100300c010880440100094054441654104079040345e940300907415052080d95500700d884c1950312003581d8000050b568104c20825141004d2817103030740310003041040f44240144000602140b40518509001d1050f41d0b000b4940c0c0b80856451600d07003200e240141c0c0602000b4440000c640500e02e005101000f8580d45c0d00035002d40d280030282ca440400790180e4842c1402001901403515101d40c880100d0f42c0481c0c0d40f8500383c0c69410180e00a10100c200d0314089400d103034441e0110340e0f401e00c40c242100c01d40c1d03048400504110004036092081134541100180303203840c4081c04a0310a4000c02429a0011b0598080f81c10550341e0a00322000c40b45802c10030394589204200344486c4900c00d0209 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 347239802 1250 347238552 347238581
    0x1303020103240e01151d0904050f070b18040213030b090f011506020d111b0d0b040809030f06070806040b21010c03061a1909030803101401020a0f0210180b0d 69
    0x12102d4070f181c1c3d1b03000d42c040e40081e240240300001c002002d00000f08603011030500214203403240d0a803561825400c81e400b8041e8050a00320022044007542001d200701e03000102103009105d0103504503592403120040207071002c0b80c0d0340b00b0001e1040c1040f5081c032807007494007104900c00d5a20342c40c180002c0d04014665082c0b10a0101061040209550100309420040c4c0c80000760b9003000c561400187c200010500042c0c152000041000100001d1034018040d24000f00c088522070701041d40c0e01130307503400308950201c0054501800300c0c0c07590602c3d401015016500400701d51100300c0600080035480078000040005d03039103075a0454081a018440ca0020b4020801c48425402030b03005804201c0c451003007030034607042038115041100e51055039108051907008100c55070b030b0308000080c3d03541c8105034025162010020080d102c09580001284400300d40e0110420350030850313903020442c10080c1510b1140038403800c1503022040d04289250700d400f40c00046001da07160404400c440044507210090200e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 347241052 1250 347239802 347239817
    0x21005070f110406180203150603071403280c030f11190e0607032a15091e06060311030609070b0904060b0a030209040c051303020103240e0115 63
    0x204441c40c00110a20390010402e840140c403980c0410024690740d400800c140c900c0c01e4030302c02d06a055800443c0101c0403030b100300c02801003040c2000030078401500c10201081c83d82c0a0641190405805036501c07140001c000300d03220f900480c0300800d01c40c004221404107a581c0e081c3d032201c181c040c40740e000304412050080141000d04a00d0150511944010f0403090440700740c0c40500a201d180c0c0d01d80c0c1c16101414546e1981480e00d00604917035071584080d2504105011407038044841070b540b81000d9034000f2807400c00420703000a410010304040700155860a040704a2009003803016121407001441050f0002c3c42c1841d5040c031403005050766034114801d401c05014800700b40b90000307071002541c4a1804080c3d952200d140000d009000c80d611505401d900401c07a0303940e0a07010340c060041c495060310103110300119003400725241e10a5182404080d034130a4028005544243d0007041d01c6110300700540369000916414029600302c6611a052000c03142c070041c441084500034101210302103050124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 347242302 1250 347241052 347241067
    0xe0907081e09030a051b0a0503030103150515130603060501060903060e03090d0b0702191401050603062202030309040e0c12060708010303031a0d030207060207051e1512010b0304021005 81
    0xb07449114021903042003083c04500322202400d41d059002c60306407007204441011f00c4620b0700b191203400c00d00c4107480802c20042c0d02030920516000306849005886401c20195280504102250034103080d01d4410a9030754030b01000048140c460345010f00456214919440c0c03030b43c0f5029058601108455003142c005011001080c1c42d403106d4030104990162641c0b41d2035a03000812890308540e00681d204044070807264900b402501c0c0b802a1001200da00203010580d1a50103050340e88600766200440007035200280e142c135080c10511801c255200900b135a02e001440c0300018186c2c0d6001c00514204d801c80c40c4805254a02034030014100038191000d04100d00d04004060160300d01440041c084c0761301e0700c07000c100320301c030442d00000b820600516000c2c1501c0ca0381802540d0301c403103010b244050f1080d003c02040c5803401c002c458140c2e24100c490700024442017028040e0508401d00c1401d0b050401344855418030008608482c080c03c8284c0800d44c40345040e004104044244503055024002c0400080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 347243552 1250 347242302 347242321
    0x2701170d0512010e061309060c0806040b0907080a0e0714030d0f080f040201030e030a0306090e0312010320060412030f0801030f02150c07090605031c050a08070e0907081e 75
    0x90b044500912001030241c0e1102d001c40c41000d1b180e04e400e002c544c0b42c54a02001c1203583da100ca00134a44076602c00d00c003980c601c2c00348001c0364036804105910091a000050019100c0c2c04903550140604c00042282441d0820442c0307402020341008050700e60400008080c3d00703040040483c480402c4c9421907404c0d9061002401940d030140080c0100b160b580c00140959000350000003c0300303150f0301126034a44102d10300070010041405035a06903814004244030740c6070300005682d140340301e031119031504c0c5c3d2a660354108540c0c21001d103d0402800b110340c3d1070303280da80c10010307200808058404569808203440c0041080111040c044248000d0000610204007440b601c1c424055040e104100300c02005100a80280102c4105046600c02c024000c58034110b11b400c11000c4480540440c0c04101040d844250011001464003000a0060141d029030601c141a11600900c82d4240048088a600042a480300003116900b011840c450203000e410150a42e107100510290407822000d400c00e407055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 347244802 1250 347243552 347243587
    0xd080a050f1b0d0917070c06080106020d0309050f0601060c030e031c0c0203010f1118100509010810050303040605031602010903080703091b12050616020c2701170d05 73
    0x42c440b841e0b008100d6103103803a2a540300d50062500300402220380c9000c20384802d110750001c0000c032006410030308002000e90154190070f0603180d1a0300030340300b00ca0f80c2e030a04400410070044141e5042c421030000c0b40a800707090003158040d101ca84e686805042c050304000d44440c030f410030503d02a60160340150b0000c03803800c00510441803030380f408003440031880c00001e01500043e18907900003458048900000d00012000305002e80d11202845500c1055070100810b4840309012940851002c200c2c0c222990322410320554081c40403100f82a509460700007191643c1c200d500300c130300401e4000013407001c41d1413440c0340081e00d11309900c02442142c1096600900d40c80003d0921800d05031140c00d17000800249000300304006442400280c800703a5114103d410340200b0103c251014042d10780815500303030542550244c02d5296800824980c3e80140a001d0b803045003042c600749803004003003144980e0064880f00c5000302103c0700c0180c003d0079011840381c1420700d00c0c146041802020040c258085412646 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 347246052 1250 347244802 347244841
    0x9022809110d2c010209091f08100f05130210030b031212070f08100510110a060504050729030402030f03040b040303090b091804080c0d080a050f 64
    0x4a5a5980400040603034014211500350b110b0070900030800220600701d00d003a2990208903803008004801c828a400c0344a1604041c1d004002800014051441a0324100880301044440c011041d43c860015040070601174444666646503200b044012105009158104810241a001466151740081d15141e01c0e412070105054658900d20081c2d5400d004a0034181d1070280d1042c1c0c0da00f03069001e415248c60444801c000b00c0d40641990b444103205000c0d01e4410008400c000d6a07544c1000104580404500d82403010130144420f42c03000703c4801c0c001d4040d61841400041074505180c9095401c1000380d80102d488006103c0e0700881c1010300017051100c0c00b1010107002d50340c0e22240082810100360840c0014503201c00100003500302031520042080364003d03610b140035980c03100c8240c1568800d0540d01c9a00c00700c003440440c8000307004c04949800c40e00c03680300d251402c84035800b00f501340a00c2c512400c0102e00c14108101030160a0b0140c103600503134038207902105103400800300445003038158 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 347247302 1250 347246052 347246069
    0xa020711040c02100b040b101701060c0c0e0c1303060c08011509060315030503030c040810021204080d0e010c0905030f06090604080d0f0614011806080c0919030303090228 75
    0x14900415120b50340807d1205401401d8078404040c01e04010b0000000c00391917251100500000003803691080d007400b0806c80d030110028403200c8c0f4050641e090a20041c01070030641c2c2c1e0802152000c40742441c5a00010f5106080c0400c186d80e150310080e101a5059101010301d402103281e4214140d07100d80d420040e6220303402e0020f81090061030301105503101d50001040d620002042c01048200c2401601c11108007004950443c1c02c0010928140d02500204601703051074040850001910310016046c42900e050340060070455017854942914881900748004c1405450140042d09081c800c0c3d0103c1c404d42d00c010600c0c2e08042040560f5000c00034400ba24400011462034032120b61500000d0030b0020340101480000d4035034510420701c1d44d035514881d020a840f21901000761540c081510101c2d500740c0c450200b265161000d040807907000c00345040d4040d0900c3c7c211882621104552400746000e5a800540450103106011181211030065000f8412402e403400009062651003011346030b100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 347248552 1250 347247302 347247311
    0x90a03060c0f09210305160303151e140301020904140108100b0307050d02120a110111150106030e030706020301080105010f0807030b0c070c170604030807090605180102150a020711040c0210 83
    0x42c20704807418040c6a450006100c00340d0082808e055044d0810304c100300c0e001c80e28001d03041d5501401140700b1000c0c070005d5116407031400b0411044010208038400003102600151501101c500001d00f181c441c842c00142001c10f003001840701800421400c0e07401c0200203000c00c4580a00e0f400039070340d2000d51140d940700d022410304600464444c02a407094000c400300c1180c060704070a251004950140001c241d0001d2440a0a003010800016001014880546203648584d00f4020100c002d460320000f5100e2510040110500048032480154000c0c0820300c00040c541d4184180020811420380c03011007564864401407002c1089030340300e10342019224082e15a521124038207440c240711241d200041082c0c2b9004503130362406000c560640700e24070903a100341440d81d4907201074810842d00c2c066040006c0342844601041a40310216803001c03d41401140c00301c10041850a000c5901103030903c00ba2030700441d4890400c10402c003150f6218000f01c07070074400e601c03a21000942d42c2c034840c00720088940e10b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 347249802 1250 347248552 347248619
    0x30d021209011709060103050c010e010e0909210301080c10050d0519090503030601030f052404060b190207050301050c0d0504060b100e010e1e01050c03090a03060c0f09 74
    0x700c81e2000701903c0804507400e2850f081092540f41d4409200a6078580204450001c0e0b40d8451207140003041e40503142c11310780071000710a0119161000b06084020320520036541c41c6040901300d6107540359551044d0382d0b030303c1d810808807904043c8003404090040740c03922090304856402c01c0c15500005200da6000070507a440301d005030903130195079014520491070170306254140540880103500c903402c281c80034002c0c110410b0541c000c5480c201d440031130000b850130a003401040b1891b01d0b10805100184045030541c1c03140e4840e81558071499803a00d01c0380c034401c2c004541680611400f002040101c000f084185000359a0903998410a0081c05a190380c94000804000340c60b88452085d0a0281c81449004003030040038010b103a08810781c0740070030340714140e00c00e0600c1e090036040c401d0704000140144e0f4444840066460b604401c604040f640414490010541c580320180c00085004110108621800d00401303820084110f011008002070200d050240040807904116100c11040ca6040e50302d08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 347251052 1250 347249802 347249807
    0x601060801170a020d0803070815030c01051e0c0c090702010908090f06120109060f0e090d14040e040821070e2101060b040503060c0315062104030c050c030d02120901 73
    0x4044600030345c010a800b10600070311141030041c61285505d5101c207a00c98442c20140d0403400d2587d0450b0b9410b0f0300c0700d02c8001e0302c3c0d44908087c007882c0350b500d09600c01d030347c8461001300000e8007c071414102d00d5111140e0040303286804030840381c0181c020b00003000680c020b074507800402e00c108038995014640f0203201c0d203202d46681e0100c4145040f10345240f401e55840c0e21040c00034220a20030b510602421480c00b180c0340070300d003130014080c2104000400303000c14042e0050783d040101d007000380c0700600d05100016031000c000d5902c91149206454155454012001d9220040c4094510f142043c00c07240070007540f513400c001d100d040c94504454044498540c1280ca42c1c540d50a40b0304130142d542403503c0011202d400310007500544000b03c00340c90940c0d0342c03003803041040d0104403005240311040149081207402c00d1801804c01c12a1a020340c402d403401c0c026152450001034608030001013840f807165013071000911030302608010442c0544188148030324029130358800f83c11541c030110000a10898240e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 347252302 1250 347251052 347251063
    0x30324040914060606121605070b01030302060405060a050405210f2214030d051312050631031d03060c04060909060302010815151b0f060106080117 65
    0x44010000d224a201c9858500d440020180e2140c120348a607002060f09031a0020580302c025159508030b43c5160b50f02080080a4044000c0007001d105040121502144200401da4042d600a070000e0107281424035080303140403070040c500d1000301d1428050000181011880e1070380c5900308041f801030804c03c91034403080c5100714000d02d1800c0500148100782800801c1281c584801e0f84044081c00d00c2e41d51195403444030b243c6000a5040e004607a01903101c50052000d81601c207002d9418525503920703182d02542d00140b941042d1010781c001020050408082e90410030180440031035000c920801c40c0401c529009000401020700914215800c00c8011044d0400f80481c8000c0482d02c0030f080c01059040302354464054680000d060517404206603409001d04070407240d040e0769105a81e52001903078083c54045d0b10003943d001c3e42c0d4120a0307064242c27041c080c09c860b0220b1640c100740104042511850030600d50714048454000c88010403001e900800d155044034940307240442540304d04c091740750512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 347253552 1250 347252302 347252371
    0xc0206031602100f0903020f070e0c03040f0210080a1508061b0d1805070b0c030316050d11090a08280203210d060501030b030d0e130e06070e060c0303 66
    0x62038462200d00c002c1060300300b1700e5540e00079000d5801503043c0940c0c103511040107000302402d6002d4000890303e00340c981001140e01a008202170015031085034001100b40640e141c01c503001900e034500341f21404405200c0c03038801d603070080107000c241484c04804a44940006200800c844400c100c2e280800014008503004003401e4542006911400d031118981084440300c2503403180f142c000040f500d10a401c0c00c07134100b40003c0b0025429941d990311650400321105442c481008418064010054000d000e41b0340031300b003a4009d00d62507500d05014810300e01c8007503200030540d60000410b5541c3c0700c0340303901186428611041d110800403c40c00440d2034914400e8042500000005040780c0e83c0c0e80b604080e0003404c00c41c210510500b81d644004405440704020340c43d0b816009440840001400b03000b903011486400351402c85c0000d454500502140c400c41c1214150b0382008040010f0746602110002c2c82d980e040f504942050801c1141e00d960703000c000d0645201da807580010800d1490b405441d1080c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 347254802 1250 347253552 347253583
    0xd080712020408030c0d030e03161b15031a0409200f0d050c2412100803041403210403082107020f01110418050a020f21070c0206031602 60
    0x360154400c401b0342d43c0004140c0000080c0c40c2108021500d84003200b101c20392061107903550107240d050307201c507800740d50010200c0c40c8030741207041c0c001100442102c1e03d01030040640c0300042d500c0315081e8074100c440e0083d61400d01c0b451600e011080000e41d010b9907046500d4841102c04405012500880c0040d41012002948aa2105c0c040070420500003800d940345001035410700030700b504000e0f90038005c0c10500072107405404240000c1040700d100110b210340c800e4440f00643c15841d55425101c0c02d607401a0400212404118010720300c40c20704000744003501c0440898082d000e00140b24088490055000041180d00000f80075200305450000c500d41c03039032101c2d40a040500704014040d58400100e09882c07401c8d400d040c2d0405070640e041c0103840442c1d040640c00140174208864460080c140140405c003071a9003488201c01d203d840d4000341400806500b84041881e0046240d0340030044010501d50070444000d0241700181c440c201070f21341003410100c0342e4402c2100020300764244001e070b40101a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 347256052 1250 347254802 347254807
    0x30c12180b10090e061302091003020a0b0409050114031c0207080d080405010506010305070f03180f0c0305070801020901140c0c120d1407111513030303050106110d08071202040803 79
    0x160340228110b042121880007080002134400340d1600d844140c00c032070504040421207040303005814420480d40e400381610245020407a1a9030006802d203401c0d400014030001c0c0483c0601541c40c2600c20355014100c03000e01c00403148550000213607200c0074265101c80107c450703541c001119008100c454007801100e019508040321402e001015403000f21410b413400e600f8070003c074407254040c0c414240141c4031942c8001c4000135480f0150040c100c24045084000124448440454078505030321090510500c149001c0341e140d4146149444a03030340110810303074410000410b039131381c000c84454104804480d42c1600d50b00c5403100c03142007055a91840da088420010101c00403c0c01040310078412000d61035050442443e101018124054a00300612080c02c1d0000c107541854000449030326804c10a103990f00c1d0880481200350181d900354402c4022070f88070b03401840041d8210011803001c041c1d50004003407031241d0000051006401418203c1070080c000c0380d114602010740c0444001d4a181c0040380d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 347257302 1250 347256052 347256061
    0x10510020a081813051b0310170a020f01091202040f02090d050106050102240612010608030a080a050105010509060703080c0c12040e0c070839011a01030c12180b 71
    0x240c1031030641c03d0283c4260b51340d860080b107004191145500520540301d0001c41c6880d43c98210080c3d07400548800d492580c040d03400075450780c0303030254212902036040c060181c0d03061a1060190410403007030864180402e6103001e002e11641240030b040c0709a01105c0c013040c0540702d4100c42000b4441c015045421a000c400300c3d6040c0401500300c54201d400a0b82181c502c3c24080d480782000c41ca2180c01004440c1080000c200d05103030180d80b171a1301061010001454581c2e607200d4916590081120b00046003031070041042c40c121510509006040a00f0018506140000000d0382c6104218000301403000c000003180c10f9400650030780c2d94030b590000440c2d840042c40c0f2604199604284543c0c6860045240000c0030940c032a800d8403600c99201010504141c4804114100292040a01c034a04488807a400740d003030509010140400004400000e40340c2070f407542001100000c00c006c03d0505003000d81010000781c0c8085290b6144410030750000e403211501c401c08841e043c0000011789052800c1d024070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 347258552 1250 347257302 347257327
    0x2130c0c0b15010216060c17040b040f080709110304080a020a020a1701050a1518140f0a051501090501110316060501230303090603130b07080a0b0414010510020a08 72
    0xc042c004090b001c4400c04c41c0e00204c40f1070f07840d00345c0c041c0300b00182a100100e800104c4204001008a1000f0b00160810351255100352143e0815844400c0b42c0c62880010448030340700f8003003c80a0700012805100604c1d05001d00c1c2000d100c0a000100328040001da00c05016209000c407050460780108038550440d541d528154035080c0780480340c1e0440d4680400302d004610244140b550120000c44040b00c5240303055251070b001c02d8034000030052251500c00400c0d807441a0204688120401c2100400c0c900b070076101601200e07001030011552a10542400380142e8100b8640f20840c2c4c401d103030420019012200c01810360185040800220a00e55200c4042040d80e800240c1603550100300444481e120002000d00c02c20354030303181901034100b00705820050401000440d80000ca10100c5020703900655182c00381c0e03520440c0c5400000d030182040c440810607034040c175107403810704a0f81070060f85640c6041440114061240c3c0340300714a6104200f003818001d001070200940c00203442522910b101004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 347259802 1250 347258552 347258581
    0x30d05090303070e01090f1a28030501080a0b0a02030604060e09010603030206060102030a0507061a100e0f12060a0c18062f030a0c050316060b0a08070302130c0c0b 72
    0x443c01180440c500c0141552090a10f4412900144100c040302842d04403081050032002e07051480010081002504c0d850340a401c034004010404141c25100308403a500904403401a0008041c0d03400c55041800850740c1240040e40018007084010f03503e0b11480d0000d4020001c5600900305104110100414a5410b44c0144e0850707009400303840203a9642c0c0f00498403031081d01d00c2c041c0880d40034007c59002c56a5540b00c252101c0755405c0b8010801d06060001b004a0010104e07d070024190440c41c81d010b0a041000c21300c10350060f41c1c58041514101e00d00e5031540c0d00207010380300790f40e41c5d4512200d4040c030803941d450a403010302882060091300c1d1034005011120520b603820000e59084c503d889001c02c02185a4000b0009102440c10b000e030050341203a02d210888810b1b00c1c50711051080a18040d400307e500003149109600c00220030001c401481850603140c0e0100e20710350400142040980c0320f1048001d82d00232681000568000c9460080d42e09064110b00034001046400400074545840c105 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 347261052 1250 347259802 347259811
    0x30b120d0c12090b070b0a0b060403060f0c0203030610051804050415050108061003060b0a15020d030f0212011512060e01090e0a02150d02040b0f09120a0503040512030d05090303 78
    0x1d00441a80728000192421486840b514410010802202d400b103100207008640207110303108041810803008c00021203a800a400565503d556040b16070240c00c41c5100d1101101507034005181149071540016070401d00d56409038041c0100000c1d110b074609079011070305542000c001c00420560800d810521001e00c0c0c00a0b11070b04943c0313003c0c004100c145001034518800d140c94400610041d0442d9100009031242d8000d05400646107500130500988401520030645015802855405501d1000409440300d505199440a10422211041924000c20356041d5490b11030b8145c01c000346150112000c038122070701e8070313640c51601002007116549006228101c80c03040100b03101603100e640d48940c442d80d1188009502514002c100c03003c60b03046101409044144000044c00e166692007520495407007101080c1640070700142039900d0303141940c4c00c00b1091070180300074101c1010540c1c52940d20b11960158a100380e040b400503031022a0200216414a4444a0701340003a0401008031030b9290810359 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 347262302 1250 347261052 347261063
    0x80c0108070203070c140d0b040503130e0610030513062d020c060402010e0f131d0307080d020319020d09110f1302031008061e2203030b120d0c 63
    0xd0101d1038191002080da4904c40c0c00c822050305e4140380051203c07511841e99081c64000c803030014040045040700c0c0b1041e1045026030051584d45807041d5151507840d247da0000740c820514541071103011b4a0b00c1c6c4a00c002ea4001d410000340361385a0b040d900c0b494083c0c0b18001820f071802c003a842d42e40c0b14145001c98807078042d890030002445012440300390590040724040300256000d400000c015600c80e00cc80982e000000c0c2c10090410f0195011594590140c00c941480c5c80d00c42032130455028014200b03446045001c1c010313500b840080d9440010f175105180d4000b00c0f09401102044180c0000900652030340003480c0e0031903841c0001c0c80c9290282243d403900780c808100c0700c201d0081c1c0d81040c055080d01600000e1045e0040080003a40070000d400241940d44000d0f0070700008515017104002c414050103241030340c8040d59101c4003100742c04040c020700208142810550102c0001d410b0300d503c5103016403506010500c507a92501103121755070403a03010290791060300410b40640c1d41007aa0036480c11b0145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 347263552 1250 347262302 347262317
    0x70902070c0e0705090f130e01020408070603020c0303070c050705121c02010b0609011d0301020703120e0d090611011514010e060708160f060f1a03070302010531080c01 74
    0x45500310a10501200c2182c04940100b02c4080c240c076201c1b10410a40e90000c01c0b54001d44c120040c00001c45090700302c014043da5001a090142803c00c22481005085500c0d0641ca002401000c240e101e0102500220901c55850040c0f010090b05000401c094000a482e440e018041c640c600d681c3ca031140c0d02840c0300350580c0000445081c5c03041c0540c441074007000c0c0c1420314200d045001142c4034007000024513158010610103080e2075a0a000803c0650702942c1da003910b80703100d8507101080768020f04c6542c1d00340c0c1c00000d200d501245c0100e074120072504203046c4010107090140d400d41c09005c81c2440b20400380300d40e090210303003846c80b2911242d840500b0380e00c1c03203030590307030082404a10301c0741010140c02c2031400d000301c100310b1030741c544150703c034901c03a100448040041e5a07a5400751400280e8042c035554803484042ea4640070761012200f03521003140200080c901c2c54001034000c1c80383d030780b04100310201a01200c0c0601044450808069071351000611500d5558030480e4840300142e5440d40010b422 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 347264802 1250 347263552 347263559
    0x603060c1e08091b0a0308040e040b0c03060d080901120905071a131e0902040306020a0e090f150a1a13080d020316030c05062502010911040203060a08070902070c 71
    0x91004203105071091002403404141401104e8406440041c1007680b0200a00021001030200340250004102d01c1d80f00c070096083c640f0780030501c1400140300e400c460302c041c804c0043e55600d043c50016101d0b0002c007400d81d1102c0ca200100c50041442000003d294100f8001c04200b00b80000c8480488031000c4913503120120030004107031144620032112510240420301070000e0b0328012060351904040a10031007031565500e254000303030781241e0700c00d1341d1b01740d4045601c3d10f480c5d400c480b507441c83d4070702101c25030254645200c0c02c1e00415000f6021040c0b0001c0002e60540c10340f6003401e440060110510104d00600110a5100ca10390000c142c034444460401d00005280b00c0014928007908402e0b0055400d0540c0f880500c540103400300c1007601041505500d00006c104240701d4640a62a0034201c1c5c800741c000c541006120f611000d4000045a24210f07404c004035070000c0009050900485000da560740b2524002803138103410307803c2001d00740100c0b0f0000801611950003414410f00c90421320007071a65 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 347266052 1250 347264802 347264807
    0x60b031504240905100e0117061510030504020f040908180621070306090f0c0e0102070617060a030b090d031b080403050c16060203040906050d030e1002010603060c1e 73
    0x4180d89448001000d81c2d906100488454001c19480031018896138141036944180c050b070220213910020701001c0008003140e641c5801e00440c0e60060080307101c49881ea408002155103414488108810035580b940410115a50348400c60b100303480c0100f040c03140700541d0800020b5980b1444140c00814110a69032896007004010f940080c10074008610814183c00780c170b4910070000420b83d104040e940d20f17000c5043d4415100d111000c4800d60000606510340c800d0107000c00c840707565041e0541d4402c00c8100040c1d54880c00000342004002c01c1c0c0030707803500c6440c041490501c0503000142104d00f200708000e001200040c42e86080402d65409210290039000e40c548408140050a000141c04200041c04070303010704001c0c0054215142150070700d020001c4410749120a5030032410058000150820449580f0300810300075002c01c440702078007401c1a035005840301510498190080c9003100b0340c2e01c101c50007948000011604503800348090890184000d240c11000342101c0a94075918485100c501e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 347267302 1250 347266052 347266091
    0x806060d080703080c1213030e0103050415090303020c150f010e01030c05090c090d08090312090604090e16120b070809100209032401080606060c0a02060d060b031504 73
    0x1500814602e107090303000d40b01260140002007056240c04002c200c40300307880d0844d92a203442a0038602c40c1d000c800c4a02c0c030b8020030740c41081c074200341014208000e02c07000c68088d0705a01d41100c51550002074894062a00b940a801486c40c124a9801191007200d018001052514843c00414010100f144e0700d911000042e0030081c00040c0c21170300303440f0080c44503090a00c0101d03041903107034101300c1c180002c25000a22408001030100d44224001c12880e4090074100040c09850403400005803c0c24516000302d5514042c5126400c184e940700d428030408518140240d43d54081798240040106072588070030309803071452000c112044010707000001d80d924404c4001c0c50048041d600944032240c0d071a81c00300f01a411045a40d40d150203013100c5001d10a0724203c0b00708142c07030b0201c08000158500701c155400c00c540184ac0f280146c3c010880400d03200e60110f80305440c194111a07a6413140802d0b102d24005250a03089909004000800c3c0034920165000308040c40703004680a01c03c81409020544044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 347268552 1250 347267302 347267329
    0x501020307150c050d1a01080a140c1b060a020301080d0305090c0d020411070b1f051008090c0904050a06050105030705060f030a0b03011d2e0c12020c0304080606 71
    0x401c2c007007200032180015508040140c041074a00b15042200315041e035011240001c0070180714040c541c507154102d582120704107902c490803000c05c01c0b02040d05102c0038806034000f004010024000201c20924040784042c001d000f084503c22180c851a2038451040258401e000f160380d54030034103000b048014840c1c01214400d4144102070481c04e00041c05000e80d00f0500c02003268400c2c1c0301d1150030030041040010700b0500380940400041818008499000b10100c2064024a03455602040c401034441041c1310800c5003203031402420b40e0342c0700c041c142e00b40b616500565502641d003030284014000d0000e8004401030280c141000a079030f95108140d5034031010310880390455428030417080907c0b00d07080a15400101ba100100d141072030100003d0844110003070004440c00158445080c08100b0000082c10003150b401002038089140c80d035559545a201d906280300c0c1d1902c03d40c0080300d100b62803003185054180030564540c104480c3d00d544a8005000c0c1000038451440012814902aa10304186 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 347269802 1250 347268552 347268563
    0x62604050a05060a0c2705060a1d150919080604111f020c06070611070303090b0a020a0c08035b09050403090f030b060f010e01170907030204050a14010501020307 71
    0x20210001000446206d00c544210079640030040002229200d450043c08200c071180e5540c1c00e08074650084050300740e04ea9841a00404581c1503024070320300894112105181c007102c514049201401740904018020f4000e44800d000300d44c240420414824200c49107124202c0e6140003d00310081c90349140c3c9040c201403801030340038440d0420036080540c01880e00030301510f004110450100c0400d5550740c0140e200714002541c0f4410b00341400f00c1c03e54203d4020f1030035901549070900100000b804031000c214080cbc10320000101190450b003810b50080c034101410300c1e2014041e04110013000100b0001460b000c1c1c4041381c0300c0060000101021401c03000031204c15416078117800c0403045402018014000c40a00c10000001320340702152220060003148528140c5d415460148103100c00306e090115001c1c1440752180500c8c200b680c0000f24550781050307000d100300b016038a0300c50143c64a00641c0c030103900310b40b07464144010514150007100300a11075505010f00c03030342d0312401242d9900c40c2a40140c030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 347271052 1250 347269802 347269817
    0x3030906010611120f03040201090b0412060522060506011805030a080a020c1c06060905010506190201200301050301050601080c07031101021312020f040e07062604050a05060a0c 78
    0x1983e020300303491101101800100c41c00c50048494a4045500107031a030003131248080304200442d070303004c0c900b20040c1482040c5a81001e24085040011402000e4002c01c140c0c2c1700d4000494000c09488100c4030f14282411400500ca55420114010501640c0150014211004c80492100a840076070115038010f001084400c0c0c554841d0030098203c0700c2c901003103004036503994581e0359500039821400000010071010100081c64044101c400d286d02001c41c06040c2001040350355110001d482400700424035107500c80d00c80c094101c0c010983c0d55000c00700180394003800080120700b50302841c16980280c00800140c4c84903801580c000c0400c4036000c201c69010011030b03000071b1103650900c400d03e0000f0b001504000c000c01031600c0e90308440d0007640982e4112440801035103803604200d501000e09031805c00101c00284013240c0c0b00c150740e0003610140401a500050680a0090812904409204024440c0c24245021a15040c40007000c0c0c946200f410082032901e000d52180b0700b081d01c1c0c151280d80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 347272302 1250 347271052 347271059
    0x9060604050319021807021c030c05040506280507020a080a0f030f030905060a0911190b0903100e030306010908010c0c0f1112010507021b0d08030c0c030a03020406110303090601 78
    0xf40240c071090040b41c014400d014050710020000061034060051a0060f12000f51414400d40c3c2e070032800c2d50802c00f0581840800722901750032804844c20348006035135046e07a40141c070f080d0100150408101120441151803045002035200014148003442116020003141e580c04c0d4181c2d0700c40c5045000783c81c2031415030320480007a005000c14015103240341004500309034552203060800030115042d443c560744440b80310b810080ca0b448101010703d02201c01c1c00c803034284021840c2901c4540c5c041d1b00d5800e00001091401540d00b000245a503207803086003070203040c1c0c500b03201c1512500b00f5100140424003207000442c0c0c02106000d00001d40c070050b41c52103a403c0d542e403203001e101101c0b40c000746d600528202140034aa201c0c04040014001020004581402d02600092406040c02801402d40052404000180d9100c4886060700c0743c100e50f45541701d132108507116981e440ba09038511001e20000402c107118030780640181c4125072590f26040101c5050606045e120312003200d0300c61203500b0810051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 347273552 1250 347272302 347272333
    0x3060f060a030c060e01030608060f040b093f160b04060612050601030201021207020a17120a1211090d0212010e030d050105030d0903050601090c18030b06090606040503 74
    0x55a10000040c8036200c842da603921200f41080711030f04400c000a08103031450a065801d4040d030001410004020400c80c5001d040103182040042c100800d44c050750804218202e8042005a03840e401645181c040480d81340040751001124036180e020b05034030403406004d2000503400b40d4006081032040550402869a07500d4480d482c01841103824581c0d4010108140400c202d551041d64403507402029194154000a485c10000c0c13840301c3d41d2036004010200c010b803544100e50381280c0141d00c0441400e06155501d60a00c0020000e2440c80000840c01c0d240580d80140c84c0104007510050800204200ca00820100d10070f00d11610f41000000d0711080041c10114042001e00d458400002081c520301e81e012400c0d903100110000c1070948a0340140190f107401e00980203401d1040c01c1920303d0500e1941c5494035000141b1440301480d603a4031600d40d055014044100c0c4000100750501c90a075100c1c6803446d0f1110050321898010408040011580d0400008442c1542c80080040241c581d82c0c4607071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 347274802 1250 347273552 347273581
    0xe09070315090c0915080105090c04150b030948010212031003140102070c0314030c03120a1505011d060c030316020f010615080c07050601260601050306 67
    0x5004441e07540d510b4400c0032842c0f01080310040d00800c100462417494038892036150300071720b4204801e181d1418080c01114000001c00740080e040690340440c021415101d890402c611550004007200f200000300842c2c918081250440c02c0a4811001180242d11000d404d100b41c2071501954512605028640740c001094024003010f00b0501c1114042d9040b00c060f0380c2e841d0030540d00070480904412082c01008400c94810545402c004001c40c10403c07a03803a0038003413991030320002d06000c110000c130044c00071042c4225070321200c440c811256034081d003110b80c121f20b0800311103096005107000b00c0f09050b10365165a060483d18141e65000040100341c3c0c0f40401d91380b41c11640c0768045c008000008801c00144080c5104000c95010320700c24244040c2c010342000300300b403500c40c95030345800c200b17100f1800e8481d80c11100076182e24000c0c945607111803a00d591031003036580140043c455900001000301c6244810303441c2491908001c815035800c20059030761441c0038000c0c694550803030340006100080b1034a1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 347276052 1250 347274802 347274833
    0x30405041109030a080a030c08040c05040b06070b0f04060513050618010e070306020c0d090b070b180a0507080d0329030a0210021510151d1e04060e090703 68
    0x88440c9008602c400003031500e00c80a00803070310f41401055a05026400d8420344000b01c8240c02c1854040c40c1035520b07400c8a0809000b41da00c01d40e51807130006042d0711040e0039907108952140e080b01e920b04044601890107441214100c400c40c1c2050001805400d2450303084044682c060014007654440454038400c0f5040040041120340d07a803042003000381d10070011100250301030040140e541c00404080c5003810742140301030082c41060364041084500c4902120800d075003006c200c001607100c03100090014401e0491040c01845100101401d200b0003254103c202d0b4045000c4034210075520b0001e0742520750401c400880d84500d840c82031080540e0800740703c00301c1401801d4512041c260b80c001142440c4010504006a000710070b6080740b16000305401303411600c0e83c1c2514181910b02160031281e00c00c1400c01c0001c100b514a8012029038a1003008042248003d0228003024111502042c1c10148021054495410314400082c0b034a0300c80341d914010035600028012140c299280d14028054003007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 347277302 1250 347276052 347276081
    0x4060f0b0307030b1c060e10020c031602010309080c0c010905032d0307020415060906050403120f030b040615030b120a0803040f051005070e040506010f0e0f10021501080f03040504 79
    0x1030b0b90040c8208880200c500340380301c0c6d0030001c0c0c0805035032a06850044d01400c0098490706c10030402040c0c40e0004255040c40000841c030081204e501e2004078084c04598100924209010805440180010a440f00002e40c02ea079582c00c8160b5030020540d540b0740c26041540d04119012100c00c18483c0401d144100246c9182140e1405000b90301240c115442c9820f034500c901c152650920140e40e02c41d610310010201d41c50420709250a44d101d030224510650780c0401442901d03601c08003954081c0c0c1008824000041080003150b90340d161900e68401916100c0c00003918209580072217160002c82a44031311326100c0101a0021141e481c248ca0341d001400c06d442d40c4070907080100020760104420031850246040c04140c0d81800003024003254410070415208038101010854942d0307000d010000000c0145c50018450021400401c182c051560304c8581c10181c0f2000b107110071034000179002d80c52400c1901c0c031b66003a079075a0906902c1d80c055800100c3c0c01d820801003080b681c42c00e90095001c218846 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 347278552 1250 347277302 347277319
    0x4150f05060a2f06100303051c0906060f0503070608010e16050f04140f1f0e0d080301090b2b0201050a030f1401030320030904090c121104060f0b0307030b 68
    0x5400080404001c545201c83c84021103100b101814144030060b040311080303980e222140d0841c0d0b03000e4900d001d00c804031109041417034202083c004041e04070340034442e0410020400315445010014088541e4000c1900078403c0b0080000d541d88248587d9040314001d21002c4500e4136007005090080c00c08580e000700300b107000d111040031301c1b040078018001402070130b0a09501d140b00300c0600c01c030030500d9140284151402c44020b0700d000c03030381011484469650b1a1104102c0c0015000408070179240b200900510804000829604031562000c403c40004441c03e90a001003a2407148100c1ca00850b1310116018034074414005501440c080d150b50b4200c0c0c100400c00010104a1408492030010700055403044080104141a004011207805071039a08245840c5c441e103483e03040d03680c4240594580503d5551007550140700310355920402804040c017001900b0301c140e0814865079004068410b01c039500c0e040780007407840d82d1600d81c042254102d07124241903540c1c3c608150000c103020943c050304180319 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 347279802 1250 347278552 347278577
    0x20904061703070201030f0c02060703110c010f02030910060b12100b030702031b0723060c1c18050904030e040b040e030715050103020d080a0e1e04150f05060a 70
    0x10701d50500d062005010040d5180d801d00d0000500f904d01494003003452901d01229421400d50215442c0d5001c042400c0100d10041d04c5d01c4001c00c984074500c40b5030465480c1008801c034040c050780086014001e02d000315507080c2c03c5600342e07004480d00386c4540c5031100000c101c88000c04006032500b0358010b11032485814003682e101e109820646c0b007100c0e400300507000001c1404500480c03081074280080d403000141089402c111008000e03010b0340d10190040c00e00c6020b51401642e80000b03c43c01079003204103031a100034080422029100c0074040707140116007044100c00d040d0000c69511000c030344005120725426111170b28292444041001516001500e4610a481c0c0c0d0315580100c056090402e4000d41d0b41d041d041c01c2c01342080c00c40354900104541040c00410150783c1e94542008080d0300110901d94946410a041d1414850303c0d80442d000300c0010b00c0220050f20502405440c8001a202404802184102c82001000502030316084090360141030050781088800f5101112807801d00800311203c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 347281052 1250 347279802 347279819
    0x406031a1f0504120f15140c1c0c030e06070f0219031107060806010e0306060622030b041104050f070c170c0a0f0c1d0f061804030315080705011202090406 68
    0x42e1031001d0380e400c00d40c017120390100035036409000e400c55141300c000c03c0b0000902004104109014014030040c03031001c034218881c41c0300c2403840d03c020010305900700000e04030701c18003502a000881030702c20340c2d029480010311582e00a031111110055290302502c940b5070003901e061140d6100f510141c0410201c25503044038000c0420411024003050b89907a100303864050001041205c1c1001944e01981080c01400307100c3d19400280d42503000c0e08402644804000b0001584025040c2d202034000b149907000d010522010044808840c1015502481203075209140480320324810384903034000908101000f008030f000680322112600f0115207040c074001041c500f09140207110303601030314160003c0b001d6008202c2c1c2002414010700e109049400c10b640034a5000c8880c41e0000e019000d400403050020b00c3d180c1c5c440046110345880f80495001600341380c10018010714009520104400d00d219010a13815000240402219416900d40710305626007822800079400003071040340c200c7c4d19503101080e19603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 347282302 1250 347281052 347281079
    0x30e04020a02010506040c050c1209190905040501150303020a020f060d0212011502060603060a0f1103040f1109130201050f16052a1e010e150406031a1f0504 69
    0x1c80380d0700100d054240501040101c9011f404000e00b481410020224054404155042017156000d80302d41c4a1641001281e11aa40500444900320103801d022507040c02651006002d103002d20020000c0b01070029407244400313a60300010300580d00c20003d00d4018601a941c80302c40303180c00780030780d41840d101c14015070682e0001c1900c14a400030840042c400360f6070b500d0482d5500341e00740c0300070582820074002003034442c8000b03040c4d802075035210b440f680048002d640044000c1509110056542d103450f060052a050400c00d007200ca44455500340300c15031504503420b81c0102c200c43c1070035000d40e40b0b07640151450b0b440007642506440003401344803088503010114240850140780036100151401e608520300358001c00b45110107041c844000c24950301c4405041d4846144003284407001c0c1c008000507103144100c1c00d1500c2d44620140e580c0310701250034a002c0c2040343c0e0310352020b124a90a25481c20036440b056007413a07400c01c0201c11140d60006200c0b407000702010050500c6880c15840309408201903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 347283552 1250 347282302 347282317
    0xc1c02070f0507121e2d0206070b0612010e1209031e0d020d1b0204090f02040c1805010302072a0f03051e010e0d0305070207090203011d1806070309030e0402 69
    0x4281450084041c08842d4040340c05d40e00c11503221101c901c601d952080c800d01c05400840c2d130741e40080f00003031090604400800d4525500205080c1c0c48845034545a111a0400c54886004540c030b46a041b95021050203000700074141d080240001b42c0c8a13100012030b0b50041c8090710b030305204203116480601501c0c0114060a84018040e002050442101919002e043c41130101004569510746004c80078440380380c5941e5030f0468002c1007000c032900300740c5001003040070b020b0b5209180c0010300804642003081f5214443d42440c01884199036640190224022503a01500341c92000800042c0c0301545200400300c010070b0345015005d203484050f0580a810309410488441d840754400003842c04655103103180f0850600300034003106260202c0c09403a01c54aa40c0842031684a0011450039402400130802070150007601b151203680d00c0240b8152005030322032616803101c81002140c000d0b407803e126600440400001419a034480c03420450051210450503020040c0d000340b84e403902e56450005107000f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 347284802 1250 347283552 347283569
    0xa0909062301050304120f120507030603060b011809090c0f060507110927011b09050f0102010b010c0807151e060b0313032a0804030b0c1c02070f0507 66
    0x458540c10820301003001e006a418002c0038000c0000080058950810700707451850042e030780e4100440140c4403c00c0300c034207505c0501d04020801500c0340d41036100f0002c0728000e0f8028840710b41d6440c015101340b507100c106580325490003c0706000307410b0725400040e80d41d803107003803103564083d03841c100c1c02d0300f08050350040400504001500e4042c007903c0070002d0030903031003101e2410f507d0400380982000d600b400000b400f911000120780706500b0100b035010217a15103428624a810b9140b961004100c0c1c14540200c030b11800da540700a108a510501c90454642c0707041e15081c1c80801c03941c9460145800070034003201c41d2030940180c030355104114001c44810303415203503602000f429001201026200c0e2500070554074170003170003000340700e20329190440700540c1c160524100312400130b841c0300c1084014000c40c44899030721150440c00c0194400086c0101c078003d030603c681d5a19038002183e03151090100c106100414004000c800600c554010100d440c03003920b8060b040308007961941e043c150a45e104510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 347286052 1250 347284802 347284829
    0x2060d06080307150501230127090e0303010b270312032406190903050a050a0323040e072607030f05040b2e081e0309030a080a090906 59
    0x820034120104d03130401003161400e01c00c641c185210b00c141d040c62040c01d04081c40010201c449141d00400507400300f8103005030000c03d49000010302803114009032045440e981d1410f811400404c5004c13013501d05031030b103d0700c80074074119580c90915485200c1158201c088a9021407a41d02684e00300200e889989080c803d140d00c91509507042d044801d601040300800c290583d07654080b075a04d0000321485c003c20600650f86802c201001201c11240b281c1004056100d40c2021400340301e00010308103400c62280daa451028060000041c00c1c010a802469480f240c0a00051102d05d141900d030070b80c4160386190061821400c24541c0d525540b505802000c002d06180910010a62500825000e1320180f01d091010f0b080c16a200e242d2858000c08010a02a2071070a00d00c80700313201044920075403100541c014200b600c1726a46a04c80c454200103c2d01144403d03403030100d0300b00110070b4400701034004020300195803039502c5a04499200e05001d200b00f04810070046510525440f41c8800f801030403c4080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 347287302 1250 347286052 347286067
    0x20a0b180a05100e091b040b07210e01211b030b0312040b030705070209090309030c01110a110307050604080a1b0e04080c100203090f06010603060b04050d02060d060803 74
    0x1070569074540041c1e002c0c0804205a0480c141c1048082c1480d0005a5810b8007a43e034215104c0b1030f15040000f070b007104045c0068000b414a4088010f4510103018440c08902c0d190340e4908211a40c0c40940d00314003140d64411011150340c014001511807400d009802004c1440300742c001c2044800114203c07122040305640c0702860781e0b15104407101043e00341c008020310501c0707800515260242c4d100b0b0382c541c00000000901d809110300181d582241e805041070342c4034144030180e940c40340c0005d01c8080c000d1041003020b920760f6220b1361000742d10070006c80103419001584e860700c01002c007106460701e41610070300ca0700080da519040024001802c210700588001202e514040703119035404070442d648507031142e4041c0060860241d10542099105009a968150f0141c080e410140c0c1d0303040b00e01001e4804010441c180c407010034641110301580e01030315050703070f02d40c1c1d025003c80f0528050030100f42004d010520003414030b0986901703020300080c80641072001c60201d00040e5101a04421030a420105040c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 347288552 1250 347287302 347287309
    0x30906111b03160f022403040b09010b0108070c030e1002070306060503010b0604050913200907030509210c060a14010602010b01050d02090d05011109100e1804020a0b18 74
    0x20700281080340a1403401486450811031400101c42c040c0004502c3c090030011540e4207054041e44c40301a92403826090a850705043c2103070012182551080340a00004028540c113105030341045030161100c11050319034080460b841c115105d0110107029200c080c1400a40d00d800044400c00a00d070300508580d030840c0b504c403050718a590300241c0280e040000800303050741c4a800395020384000b520301160039540c07403900440055115101416002602070940c20f218103402e100c0c00e030824140d4007804a911840c0c022800ca45045540c007085400c0081d00315034103251056810b001c50780f008146800c00e03000340d40300e41c1000c0341682d009145e17981e00c0300c2204400314082c50290041c90280020002941d00b10b001070524440c1c034403c152220341c0080c0c007884903540c1c02c8188100d030b904040208042d20722140072900e01d512240c043c602c141c45807138800e00c5a500c2410f9651050384042e00150422030264002c0c480041d010307004903400041440003141c0f49016070f0240c0b0b2071601c00d0220039071f80000030052 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 347289802 1250 347288552 347288587
    0x19050105150d02061e120916050613090b0303040315050108070b1905032d0405010605040b0a09020702041103070e10030e2a1801050a0905131203090611 67
    0x4030340103a040465220141c0d9400c805d545d43d50b25050413808501d4600004074206101c1e0104440312070116009000b0000300000d001102940d950032010303812515641044014018000d007052031102d04c101c184000707400c82e040140d0410016040f2810552207a803062410701d2410100014aa0b45100401041d00e08121300002400030030841484c0c450310032032590400d220f074602801880000404a440300c0c0010700e0702c1040e14490b2142410341501d60360412000a4181d40c01d462a42c2407407004181c62800c0d01c102c44034100018409240980340c5040380340650481903060b64030075a26110503002c54031200040d403280e08030399034074221418808100190076008102140405103090000c011407500020819482d0342e200c5810350f8503824041194500c03140442141341c04c04c02100344100c1a58006041074103803107003190300480035902d07010310104032001121240702d806400040d0b20003040c620007a80011911901d03020030781c064640ca070b03541503444801c820300c0b11460002d0b2016010241c1c445 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 347291052 1250 347289802 347289841
    0x1315061409012408091e0a1b1206090f020607080406020f03121305070503010f02120a200f090a0e1504060e06220e0a05100c2019050105 60
    0x204030a005402c0d20306107981d00c042d042a8180130440700454030051041000c0000803a80d41c01c5280381d0014002020780792144e186080740d08102841c07c0400c01d4403030a10341c000b0f90b0442110a03419008a441d5070010b842524029101d010a203000d4101507114040101078403800b0351840342c4d9607880c21900a16105010904000582091000403481c003951190316800c82901e900c20a1101e85600f4014108001a8031240c0c4c1980b034401d03110a40e0007140c001e010380a034902ca005000d07a5900141c081520340e80820b5480c100300100c01c0d40e01e050224800b4166071403022614604080340003000c035041103000d80011610542c00703420040425841801e940b14a001918107121091808507054400d0f80081d018502c1a00c03810380420300d440c0544440c1c10b240817090070502190100d070350040d49592001ca01600c1600451220030407119060182c070344001825030302c8060044545040312840340b01a003e02c00315000d000c1900600c0c0c44c400b181e50003458083c0d0000600c5045c1903500e154030806040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 347292302 1250 347291052 347291069
    0x30406140708030a021b101a09060325030501150e01140d02040e0109051c020706050c030a0c0c03060f14090c0105070605150d0b04031412131506140901 67
    0x804000040d42c010141ea400c0400058050303150120090307080004400d0315062441d078803400105000c40078250308080d015078039200e100710313901e0079400511a04c3d50003154000c0d00340d0300c106840046202061707002643e001400715031010380c0c0d890fa40c801e800d446041d101c1600c5610005400c3c4100b101e0141c5031f0340107103042010031480c3c0e400e03180441c01307541180130084d100d03a544640c4801c490340301b0340055600d00e520500340d44618042d5a5084020f90802070030300d0061007400d00120b4024000e40460304030410a8ac021800c00c061034904860032038048004032040444040d0010014000c0e0190316485056a0380c04101075030111440f0000d801d0040180c4800e50140d0f80503001660042d04640c8050780010010480b550340140300d803035118496403003c2d048004000140140101c9078012801240320341d5469000c901c01e03a400c0c11450062401804950381102d01151a00f864035030700607a000e1148000750019144020108116203083e84040108084004646d0441c9403540c0500c0c00340800b00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 347293552 1250 347292302 347292307
    0x1140f030a0201080702030d06090e0f06070813030e091e0705040b07030302030a090f0311060c03010f14041b020f0106301b1202040b091b0714010501030503040614 72
    0x440060381d41c0301403100207418801d440010404461090080b80d1825002c65401d0150503a5840722800403c03000d245100f031806076110710107942c04d01056a82c05480d003566442042d03100c0d1078000c0e122f6000004200c0c20700c80388403e491401d449180405100740b007820061202c0002100100a41480060039401004403c00081c08102381e9201558492901880c0058403a9503c122541c0140445070002d070203115405d000108040c0c0c8200600140f405240540312551102d07854054103002c280a4034040c0c1014075000c0c0400d003044540984042402400407406e14685003601242d152100c00140060300702c01424001810309002d00001807103089003011240e04800c00441441051082164000d181011081d080c084071810340484004501c0780e005805a0f00c841d910320715a0304440c00c038003440c2010314070841890960140c078400ca002c114000381d094600a00c0c40119445280111500c0c0c0c120100300b410307103409101c1d040c003a40c030540c0110b40e1541010405440c101c0c00f58071400d0311031000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 347294802 1250 347293552 347293579
    0x8010e070c05100c090f09020712030e030f03150915010f2102160605010f050916090e130501330b09060a120f1d0106050612060319030203030114 64
    0x5800b42d11203c1c0743c40c000401e184440070894044881c3c0d8410005059440d030b002c100711400b0383c000c0c43c10a10882025403c150008010b0702a2114548880243e4100784010588514030b4001903074084d1052480000a411800001c0d68034202a43d10b40390101607018100615600701824405503605c43c248840c01c3c03100081c1d15100d00d24404448820907030080351003081c40c440355050030000e03580204d0038091076850b440000d01001c10351040d1441821401c000c1161200d4100c00e40c91042220358814002900f0030686c80c4a40390003a2031702c48500000701d076017030104d8000e20440b031524103529914000b001c00034a69458501e4400340d1004281c030020070402c910703075014040710840c52050340da40361503c2a00c1d0090341e40d440d007480c0c24808a0300705915085882860f40c0402c109040003441d0381c480c8000022410f08030761481c0581c4d90011001c1120b100111041040d04e5030040e0002c0841311007001c040800350340e100003158100c000d42e001200601c03001c0000b00c440744440c001600c2c40c0400400c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 347296052 1250 347294802 347294813
    0xe061314030f03030a151a0c010507030903020d0f120204090518030a09060e040f061707061404091107080a05180f1003020c10020a0c1a01050603040b2508010e070c 72
    0x15140341c105655071b0016508100300840b00000510980300e07404901c19a00d000468561300080d00d1003085d528282c001080e0034024880e0b401d02c5501b5a000740441e200300038017525000741440c0440c090240108121141892600082002c0c00340500003040d6030500740001c4a038041c8010400c003c0d40c1083c0540b03201503a111984808881d0b40b4605040f40450440c0414000c2140d400507100032400c2200c0890114018040c00341900289000c48032526a1944206c4408680d01c60548001000b040300f0090000d85030050f0f54440061510305140c03007403664404104c1d13405401c548000c0350000c600f4006c0398130809010203c02d0001c2e82d010f1302000b185c4d400201c4100c0340004400030306502007007040d000c071410000340b81c418000a10456850880c0d40c00038004d8054084101c3d001c0c01140035a05c9001001000340d412a0405450141035854a540300c43c001311000745000c80098140c201c1c10301407101d8140c02014640103803500c03545541460026001e80800900c0401401419030311a0000f44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 347297302 1250 347296052 347296057
    0x1d09060402010c060b0409060507080a060605040504020a03060f03230106030201090e070c020411043002040b1212130909050a0818091e09060c07020609010e061314030f03 75
    0x96091030300d02e80d00f00141c64404002c041d0981e00c00d40041c0382c1b02c460310802195501180c0201700e60b803107043d070f20340d552664182594110300a5000282081c0001c000c01d061503009048405102e06000c40d00325140ca044000c14413060317100fa0380e8007003001c0202c0a03561441601480c10b802c4c81c030090107202c0c1160001303000c0f121280708100d0300600200014113902d00c9214855081c5074000c0091005601d02c103402d1038690006e0080c3c540c0001804142d99046080d10203200d5050305e158a00d4080960319000c01c40188501d10b40550000c201208458403404180141c61300d940c0300314041c0d600c80c60800964808107a86401c115000d80c03418015101007800091226a030a620010b115034480c40d145001c000003101180181d00b1081003014041e07403101108503508004003010645525603654205255a41002e507001000c6c020200311000c0982850303402007180c4441070512128090104001c15010b92205251000444400009200410440c03092503148042200146140c050040303407241c132403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 347298552 1250 347297302 347297311
    0xa0e0705120a0f061506181401052104020301051e061215010902070606050109032316092a170c192601051822050d0905010f0801090b0d05010e071d0906 67
    0x803600613a04002a80c031480444040712f030501c684004070032a003400030b104c10304151800c038801c1d420500010b01c1c8065400c00e84c00b114500503500c062607222041440013182c000f24010419003d43c01d00d210381180d456003080d0091100d410300590705d100908048046861a401203030411040303102c10804500c50140c07030b4224010710521500301c558407407049840c0c80880780c15030202c868043d5000070320407a26800107103048500680084910b25030648079010034010843c01c4045801510300c8100000060b22140e404110011102d180c65841c1840321603140070b104100001491a02c500360b003204141d03155014800b01c00f0001e8010354100707070001e1844000080c08030075501125000525214020046400c1146032070106181e8803090704255440d55481d01504000c00c008030400151303948550200e040c410001e54a1110590920072848e014150310382510754420805684c02004c1142885800c2c60305a0310401084031601c0e0000310700b281407820f0701581ca0341d2120010806908008078220760320 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 347299802 1250 347298552 347298569
    0x705061f061707090801060b07030e031c0f030b0a0b0702030d230c03070807230d020309010e0d020907090602070504050402060d110f070c0303080a0e0705120a0f06150618 75
    0x81d80e44550443d41d403405544044172940c241400000c03100d403080d0040200f00d0003640d070014210310040a05543c1e042c0100c0050001c40f00d40390000d0040d104401c04460200303140307000701c0c0f54003500c0300241c43d00c4e203580c01c02404000001000411841c0c00c004281035043d0700d003049008030038001d150710381c50220090f0403800091b002810b000c4002d810300c1160046c03688041425202c01540c1022110820f940c1d2440780d02506180d88040310341c0380043e00c480c1801c0140e00852601c5440001141d03010300982e101c5800c00ca0000300c050040c1e48482a4520906082c0e0b42c2241c603c2c541000240b81250b0f0303600040c087c514040a02c405621620112500c1420022001c1489402080a0455481030541600c005000814044100130512540d80d00303c078040e41e0340045d261101002c2e03c044a80c01815013119611114013000f03241044125801d24000001c01c0c0c403554989900c0e114a105003040b42160034a83d99202480041c1d010080708019003468a88005032840c540f0340c91846101500400c0c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 347301052 1250 347299802 347299847
    0x103050718030b13060e0d0e06030108060109021e070302010e01060611060402040e0f030301060507020f0a05091f08030a08040c0b030412050c1614010201050a05060d02060304020d080705061f06 85
    0x2640c0c1380d040c609003006078812001c02c201010612500d444d201d10114030400a541100f100e070340e602c1c0a07800d81c0d06070369480002e05a16440d000c002c03c001d6000503211001c0140826401070360210640280003043d0194002164a4828030315190031a00030382c220000307200c4164107003000285c0001d401039215a0548000902c2d003000c14400340b40502c441c41001c46440000008a0380c40e80c00320240000604c00d844110030311000a08100d5013501c3e070b018050708812282c0c00030703501c5124582045901010001f1900075241c890402c90305662000307603d240440d0b500c03170510080140d04c0c1d000c0c4000b00742c200c08150560510355a2707041c0d8000802c080340c041040108074555030030418460910340005042d1902400d0f66141019000c60b0700007000640503510700b0002529002042c022a80b0854009102001207100e2707600b00300e85500040c0050b40c118000a04550005d8907080c02045401c0c002e4009044900e050003a000c444c01c510104100c005c00810710030808144c11501e52810110010005e01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 347302158 1106 347301052 347301061
    0x9080106060503071d030d030e070503010515010f1e120510030510020f1608041a16060506010c20030f1207030e150c06060103050718030b 61
    0x102d00100001501c1c9885000c81555100018812940038080721010074544880c081e244008680d031989040c480c2c0c0010044a0b00505046000f8022440d084807000001c161542d0310505100c2148140c1c5012406400101c400d40c0948080107001800002c0082011060194005d9000d2502002c290703591118110181901e070080b005001e40c0c0080d0075404000d602c55882c0d885130101c14001030402c0c5d0402c104440b01d2a0180510a40b12400e0202044100380100347c80d0103050b07000c010129903080511214a01c20380c00038030000346c3d540e52000594010840000040992000300701c81d02075001156603d0b210303045c00780c048800c4208401482d90340c03030304440c2603202624000e01c09080002c0c452a00e100844d54040d081d200d40000c0b19030312000c0c076009000d41341c6150300f0400400c03202c2c1d6410311600d40d00c03405900c1c0c2025145205041580101101c0c04090030000f109070015 = true := by decide +kernel

theorem cover : BRFrame.Cov 347122302 347302158 := by
  have h0 := BRFrame.cov_init 347122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 347122302 ≤ n) (h2 : n < 347302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
