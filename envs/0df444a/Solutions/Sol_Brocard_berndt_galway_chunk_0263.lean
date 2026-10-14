-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0263
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:49:30.641036+00:00
-- url     : https://prove2.me/submissions/94a83dc2-3251-4f0a-a55e-4b7068e7d3a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 47122306 ≤ n < 47302162 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 47123556 1250 47122306 47122319
    0xf09120309020d0206030c0f03010b0a020106060206150d06180506040b100501050f0c01060b04080706030b12100b1210090507051813020102030904110a0809061b030604020d1107050601 81
    0x8851001d0380040401d00700c2c64081c1c0a201e4a644064070780101160304000f072200306031443c0c0007103000f070600e010780c0d650390030a0300e0000b42184c0303881e00084119001030062143d010060140c1c0e24a046048404100e010a50301c0c08000900305e000c81e01002a03c5004d400041c0040841c5c1140705502840c2c400c11655507560b8400c2d0070385102e0107150701042e428800e412003550418054007000402030300020b0380a440b003103c400960426032004015a001203000c4c0320b0150306000e0348448140603900464007851000c17450b074a84160701c0c0000043c0e0ba95004641c0b041c1e1301c0c8290540401e0141007079900c0e01a001c210035010307000b60300055901e4440c5000c006051304000040442c481c0c10000b20062945401c451581244683c40090b41144402d0020550035a10b51142c88980c0800105541e40e490640001502d4a0401455a58030f90402c01c00c011000100c00048603000107011006542c0e684c40e900010024040c6840d2190741b6454180340000e01c40141d4020500c0b40d01400c225869a070303a846 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 47124806 1250 47123556 47123561
    0x1050301061d150d080703030e0105010501050702060c0709020c0c0109080d0c0209190c111b0901090b0604180603020316030201021b04021e1c02030105100c0507090f091203 76
    0x701d8111400d001d95000d25041e2402e115140d0843c0328101c00c03082c40c8000500084001000705001c2e1400e04000820504154251143c003204c0f41418000344113641c034103000030700607000e040c0d8040d00a1800007030410202400f40007640142060380011500c40010408050750b0308d114113140e9005c40d4a0040c04554840001400c000441c80750b903508030400034903400e121810703402a20041080301081003140204a80e4084c440c1d81d80f20940d64100c2800214010343d02d130060038540381c801103c07001d21070500b17a01c5289200d4191018403802180000120001c90220302c140d501140303ca20340b0140440c42016540c10070002c0b40d0084040703940c00004502d03140e280480a10000340940e200b0800e8001d0340001484d07012400310014401410301107102c2034902a4040120440192840064412414000c1240c2a60103c01194046040d0743c102030100d00745103804d804080a0000002c0040f080120030000d09010300354224082c00f80c3c0ca202c00194000d41060f00045507100520240410441d01c00e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 47126056 1250 47124806 47124809
    0x30102040b0702040b03030705060403030c09060f090614090618010e090c04120f060c03140a02070c05042a0905040605060a020c0907021c080108070e01060903140307060f0906050105030106 83
    0x1c1c20354619040c01e41c2e080200501006003240d41500041c0448004a84148685e80c4903a0191301c001c00e090001090061500e07803c1d4120b58244491242c9401c0480d5000c003060703042d81c015080498508005222140040c0111464075501c85000140140080020180066030345420380310740c104501e05508101d501e98003201c49030442c0b9814032041101462004080d21294040d852220301411075850b583c041e82c11f0400c82101094940c4407114405107008030440e40808290b10460519071590345014a0142d64401c0c6440356803580c01c019544114405801605a0200c40301104c0d82000d0a01610400301441494411450410300080d5800c0000c00c41d8461203032580034240d9241007004100b802c0303101410707880840c810b081e51811140c8070210070f01003820140e19458810743c50b100c6002d02e0039815420080e01c44004000400049401c2a0007000b80c030780c060743c190441e4180c10009072540c0034a52000c0e0085090038550701e03a04070240e10100c0214001c107003e202d140e80b984c06060a0300c109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 47127306 1250 47126056 47126069
    0x408070e0c041d07120212070e010509010c0f110d0308010603060801060b09010c1104020a1106060f0f0d0501021c0207060b0405010308040515090a08061905010302010903150e0a030905040b03010204 87
    0x4a10200b8003c10305080041d600004a044c1000095588141d4404070380020301c00b8101001190284821150031082c20b2403002024a8000d14001030040024148007883d0070040030403103410f01c0e40e410400002e40361842c00d84058448141a481414010401c40c4284207100201e440c00d03502040d201010f0080306c059038108403440b450f0500c40310045400d40d0042c1c40c1074030210f00c43c40c40c081a56540f80000e0120a040b5035840d401641101138203410008094161407040d00c5c120661400c0c0e8407018440c4004010450b0407c0c2c440306141403032406482840ba000d1044a0003080302141c85006a01510846004a1041044d282e0b600c051104450080c00050050760042c481000740717180882030410507404942d0f40341c0c206119880071420900d0305070007500e030680080e001c0001202c0d1601d8040041c2d00d080d401070026500d07640018188035910301000e072803404481d17065242c0b184039422102044200c44122002591700341030040920341d890098510550078500f01c00c440340750500070b07030302640d52 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 47128556 1250 47127306 47127329
    0xb10050d0320010c02030d060603050906010e0c070b0a051603091709030c040e07030209060d030503060103021b060403020d180b090f04060b030403031b03060b0909090f030408070e0c04 81
    0xc298406440034041c1d10000e2010800c1c0c810704181000c0213004041010f9501d40085880b00f042d814040f003640c14075003058003010b203010100400d5110000d00681107540071000d880039516034200c0301c2460f205210010b000f01c4085000d01540d01400e0f801248500340c2441103241440072135008500791160200050038491120440303548070362008004244021008045404032480540810151949031000039415040032908200758240420f40700e51003103044542019551056801072701600000d4001410103502190200805170300e0700c0c0f03606811000c10704803499440c1a180080d541c48940102c003001807207600b0703155030b0703510340ca0103a0707046d41d20303960340340381008856010b01c0041d16182081c2503000e07803900000036543c0d00700001140510301969000c20f412002410280691246d9222541018a0010200305200550301034842e00710007103914181684845503250300d00101c000d082d010030300000500181d0f6410016082044400c5035500300c119603030b00611201540120310881410b4034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 47129806 1250 47128556 47128579
    0x10c0503060f042a02011a0604051f09030b0a020705010b0a06170405010225060b060306060708070f060c03140f09070b070c0f030606030501050f0613020f07020607030c0b1005 77
    0x30341900300b400001610b142841c0b00c40308100039607680c130301c034882454050b035954202c0541c2110007001f02c4034501c80942d405442c1500c1c11011403070800ca03880750a14801d469849a240c0079200c0d00050001715040045902c0341d04100c03a00b03800070351200703504031440e6103800c00015640c14646000012245162145100ea10304080d80441088005004940c0c0303560800070701c00038501e0b400707400c030003000b140c0c4010f01620b20914240d003c40e0302003162503104042c10300410907140e0300c1e20f040b19120385c1e001c00e10545809051501007411408104014034003403d01c1d03214800c0e59855405a8608003000c0d100f190152078454034818124004d654042d1980c025080c08c1c001c0d810040010210035200e2109481d50035507135101251890041d820403508292203030820024003d090250507040300c4075203400c4400b0b080420015100100680d880c1c41415004680f60941d080032400741c0d01c000e90041c040301d030b84402e2880d00034442c9030500d80c01c50f0340201000101364a030790468200c03030a42d10b02625144124 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 47131056 1250 47129806 47129809
    0x30b061305010b16050102090d030917060103051f0b1002010b01030f05090303040605070c0c080a03110d021e0a0602040321020304060e010813080d050a0f09050304031104020708030108060108010c0503060f 90
    0xc2d942c62009454540d004c100c9450b840d101c2845c0c0c2750316a8000ea03036554102e0b080c0782d16440304e503408050001940e846400107102051000c500000d50801394032902a40c00803c0308080090052075a02d503900c6060a80781032840b54064120523241c02c000d0f6420011300c40d0b01e58082080b20360a844001240e84280f00150004806522668024510382002c40601d51315540c0c48072060400d8011203110f40015558000b0150003141c00c52292240e00064250511419802555000181d2402c0c801e10000c512412100d81c0c00e1155880031074100700c0a550300c945908290880000364801846101c0100e0219a0180d1001c01a00d0903100c2239038032282c0440d501001180c40600182440014001031803031040080c0c5901c0003407241003c840b07000f056601d4104450012507200c0da4546000c03a00381402c00c0c0020780c0210844d4160b030b0b03000100340f084d0000800414001c1c00b5141c0000c3c018140040007040b0030200154460481300480d000340009030003440200c40d503000039213981c1c6d001031090009080c5c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 47132306 1250 47131056 47131087
    0x1090b19261b0c070b0d1107030c0210030609060b07050f030406080c091804030206062e030e0106090222060201020403020a0504020309150c0a090503070303090608070e040204030b061305010b 84
    0xc580c1c0c42c41d45800c10411034006820700b80740c0c0e4829188850000b6190300c01c2030741802080c0401c0340380c1400c14146880c40e00d025040009024000344512204079922030030a000740d0002000c0e02004000300615a100c00c0e050942c0d41c40440181c131140306510b0b0400c8000303400411501541c00e036030344980e8151244050040540c0144105a500c000c10b00c01c000350061000d00d1552059000b50f00502c0076003007031028403c010300100990724400c9541080c2407030b030b05039042d001c0186c86c0301407500003540000a0404c60040034582c02c002e804c0c0d4000258070300303142c840602c5483c0e4243d040440110301d80e500e59060b0b00702e110b180702c000c0d00200003030743c2080585495409550700100800544d507180c8100300041012642c211003c04030389501082c05480140d00440000141c4816070046c10300c6800c60300c028041321518440c2c803017001b00f403c0008071401c1c80740750b0014802501130415521030740c4900d0560b400303030012101d50b8040d0300b8152001040091034011a412107403038100e401d15102146250208 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 47133556 1250 47132306 47132341
    0x20a240f02010b060d060e0a09081c06150509010801080106050f040914070303030e0f010203010e0c0304051906060303030c051306050306030703080d0203150d0309120201090b1926 79
    0x1995611000d4003000d890f0100208031403811030702d00143e024144500c0d021f020802400901d04140340112610004400400310740911a150281d0310103105220001780c05803146410031810410404101d0340e280f40c018016040400090f210760030300761b80340c01c9807908031600c61080316405452542100c4a60a081d842807002c031740111402c6071402d50041c0b406141c643e50741c0c13040300040e64031074401c03181034818042e801c64207818400961565140a00050f2010806011020f904c80c000000c6000c00800b00081030320034441c0d20060ac01103640f814100010010f61105a011a04021402a2a5218100300c0e2400c0300b202900d82103076824804101d44070340000b0841da405201d03920001c804170b22040050458180b10303040144e0b5074509141d07000203450000100c41d000d180d0183c800c0000a400003e1042a28030404210f145000140012201e4072103660103c1501000011030043c40d2000580d40b0444d100b10307031100c1d4998000b0079001050428100600070320003116101142508052125a40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 47134806 1250 47133556 47133587
    0x319030c0206071e05070f050904110a2309070906081303020f0109080705010f06120602031003080a030504120e01050d0510031a09070509010311090406140a09020a24 73
    0x1400c03c40709a0b15900139040c048046200c0c0d01d42020710764204072042103048040d00802e842d2801440c504404516041400340c002003e03e004014614070075200d07000441c0003000605400420441c3c1c2c0402c00c42403869880400317000d212400001405a402500c490b02200d4075507441d100c0d50b036101c01b40020044c080085c05c40460060054805001e9000d009450301070780a00d071a19610305980c0707801030071035141011043e05903040030b4040081c045600200c007403064010b8000b595980d40d40e01806407180301030b0070007401c0340703004110804c0b400e03030541c0014807851240c580d4000255a180040c0c034021013100d421800a581004410701c0c5000c0380d04900d4200c0100c0340b28080c100e44a5842d030900c1080030046000c2c9250340000c0041034002001000c0043c8816a90346110b0750642d129a000090302e09070840c0102e8400c00440c003000050351240d101294005640d103101c0c102241240007901c2611000d9202e025101c0000c143c1103d1480d2102100015403424126550b0000c0f0070341d600d036286d0300302d40d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 47136056 1250 47134806 47134819
    0x9010b0f06090103060e090c03070f1401050c010f050415050f04021005070201021c0c031e090e061801091a03010e1504050a0c0803090103050a0b0102060601141e0304020f0319030c02 80
    0xc1b45291500c0d2a402603d000c005400d00089580500d4688485075200410750400c9200400c501800084582000c040c03c4c40d2169440d8140d102940c058140d40c035122204500d0074042200b4030064840748509022100b4050001e82c48102003450040c0058501039800071140f03800c82081401030000b464185d00c18019a42014252682e5652500c280050a004a88844406801c0551040c5000440244002408400394a0304801415900c440c069041105000c01c08540555603408241d080704071400030b02200356840d40300c0200944014016400c503001c1d030b0304c100c800c94981070003078803003d10800004001c800703150300720f0302221540035200352940d0140c030002c4070100c2c01c2c100420b0b0140000c90020f55a1300010400102142c1c0010141200185810b8104840303030ba01090940c5c11810910300003000c00381c072984003038551080070b01d50f04000c0c2c0707003450060201c0c8030200658400e60007101d4841281c40300406146e11441e903d042c841052000019100010340034070b80b070030022400640342 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 47137306 1250 47136056 47136059
    0x4020f040b030a0501060e0a0b030d02070b070303061502010e06070504031e030903050307031805010512040b0c04090603200a05030304090c0203131d09010e070b03220309030b09010b0f0609010306 86
    0x209401c41b01035070001403e00303259004020101850780039410106030b040d00186a1903004034002512010503000e44e81c0c007098000740220a243c465040a40904404c1182030740510f800f00d4003074001d020300101d0581a0042e038001900060048080e40c04803600f04180d4015507080a020801e040321b010300031030620200040100201e501003028002d118802d4903004030503941250140c0030f5000543c0458104030003081680d864107003040e15a600070341c3c464108411030b2106a052401406182c004030500741c81d03c0780c00000d0043c00d00242c604ca0f464594001c410219040c01d01011000c0c41c01740c550544e008000130032050010354002003030030030980b056a0406012007103000709070310103601003444642c00044030108043c02c4070700b20b0b40140d022002000560800740da40368840b40742e442054061400440000c010f084071060703041c1016112503000580280c1c0745005450691349010950341d212468000510010701445180c4405030002d140480d241c03207400c200100c40e48466050740c10513484810 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 47138556 1250 47137306 47137313
    0x60f1b050d0603080a0528052d0a020304030b060603130312020403060617010c18050d02010c0204020a0203030709150c0b0a02090a03060b040f051e09070b030c030a060501030504020f040b030a 84
    0x151100101c10307035070709940d914480080304040c40031001040e1100345503c03201000d079401030200c41d00d40c0d627100030f05a8092001001c2c2c1048103e5160203c4615000003044100c040d4007000504c1a2841000c020300d00c0e80328007007800002c0c001158003142184001440c80042805801d100310f000c00c0412003d403425480c5d035500c3c0305503100780d0b1160400c18010a00d070821440203000d00c00b240040ca1030300808400344007030200d018030041d1003114050701d80a80400c0139644102040002e40350060300a40d602c20010000075682e82c000c035000300c005150114007140f4403600755401d008034a51030352429000b40507074548030b400a46c054000d00c0c880b98204000b940d1600c800d03611500031400340100103940401042844142d5110000c800d0605103800c081203010b20600c41c1d150244c076071f5640c0b00801980d40300006032520380c15401a80c4a0000481042000e4107000000c0d44aa00c030b420062084a503110015829544140c500039880f401403049002c1d6400d05500240c0411402021207005440548 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 47139806 1250 47138556 47138573
    0x50d0804121a010b070c030b0711010216050609070612020306040e010c0c062003040b0402010e0a0306050103020a050901060e040c18091d060903040308090303130b0304060f1b050d0603 81
    0x7422030b402d0401080500c000400c4040791030040081e80f28031840c2400d15540c00968090b94000280110609400720301d1320361007240746014400b000c2000319660310320187c5900288a154070121405d110b40b5000800d40203001c20014121001525070154260031400e40348065000104425002a664600d0040c1d045003405034410f10700480c0c9079006100e90906248056502103100031500303038182c0c4140040381004c4021079074030941040171100c070ba8039503200482d006811041d0341c99001441a20210902c001c0d5403040d41200d10880741442107075a0745042c488080000d1098502240b54007501d0a0349040940041540348030510340401a807500060a4501c444103800c059070003540c605000105c900018640c5012890000050000b480d00c440940d6a03803045010041c04a000452018040d443c204243d80e01c4001c08120440844c0d224400e4040d503030011142a40c2d0f0f14148400c0341201c007854410315000c4244c2d070000303407042458220306403519441581044010381c4e072044000301085290 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 47141056 1250 47139806 47139839
    0x102030906033c07020f0c01390b07030f0b010c031b1b06021204080604030c030e03060a0203040302010b0d02030d1b0b010605041701050702060f06030c12010b040c0315050d0804 78
    0xc10f9142d08a092100009107480040848031101e544490b02460140e07030461a03041c1d42640601580204080359020150001c1003201740e21800c10010070b6032004c1000450f14079106a40781e9908000411710691110b05883c0c4801078a40425002c030910301c0030038071800c101e4030b405125603000260801190340e039038502c91901081182c45007514406000556052040403d5007030300302e0501e4201814510040d4640c900604020f0a0110a00c5440101030080b007402d54014401010703500c0c1840c0151422010b98000c41d070440055180c400040207610b00318080c1004550003500500095441c000c040d25407200540d12412544841403092001400c61501d0f18068a025601c154455252030901e41c219245011001490390428040100032613001034190741c403040e0460b5862950321070002007030070110322860994000994000f010241c0070150055880614140c40c10003240720300300320442c01c80e54140020a4000c41c51441044180b0702000180b15281c0180d052519190351040741e0f03803d16184 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 47142306 1250 47141056 47141161
    0x50625060203011a090a0b0c070803071101170f0f0703090605010906081203150112060305060403020105060a08010b01050708030405150906061014072a0e01080c010203090603 77
    0x500c001380111400c2c403c6003c14590301414402c84000003150365040303004280000310f002c184c218011008108a9009111100680e07548440e5400d00e00380102589640c1804a00804003039204013641419585c40b070b6480e054417091075110301c0801c000d40da202500c1181019103841116011800c82e125143c000c2080d4100003440e90325105985007024041103544540c04014803c02c1814840c1148942d10360009281c039403060ba08010ba00310090925400140c011300c41c603400c020425030150300050140804550b4204150756404031725098070780050300a40002c10030b00003100000d0200c8065a0468410003d03105c03040300b000a2000306040c203c64024640c0d21400c1803000074240030041142c0340c0482e141000c264180e80e00c0c1700c40d00388940540180031403e2040c1c100e1465580050090003068683c6400322515a0340489001e1102d083c042c0002c140501c0410014943c00001120f4680c28041d00450940d1348001c03450301946403101d500c016416544503417158400b580c0031900b184000e13 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 47143556 1250 47142306 47142311
    0x71101140d05061008040503030103031407060203040317010b0c0705010804260307080609100303120905030309030702030111070b1b09040c050c100e03191704082203030905062506 79
    0x140002000104c204a200c442c0602400e5001d000200c1c10101c00c82c2d064a406003041005a02240c43c0d0702420310549030040c101910100078801010350202601d13182142c0c002004086913200d1141c05031520038460b11140c2903011000c200025401100741a6016004035850b04680c81280464545107038600603446440000004101c0b0040d040121550810300940e541d40c007030302d02074080380003d004d280000b0f41804401507800003441441d400a0141da13500c8003d40b031302d9003405c0700095540d03048074000f28869420b1182c0ca0030744200303000039900c1a9800150005581d19007400407542c200c44004c0032a031040c0c0800000c152501e40e8010030180740005c0e0f0b01c00742e6918110316514240417a4400e989807542c203000505140038400020369603805000741d007140e10300c029000c065403541d0764807816500c01041d0394208000c0c4003944003c1c0c102200b8140b01c2d8049180c80d850302c860300341c1d11800024045400650b082c0642d05084014144070fa111030480d05a44095181165102000c080112080ca4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 47144806 1250 47143556 47143561
    0x609050315010308030112050c041b110109050c0f03030c07080307020f0405040c05040b0402120c0304030305010e010b0414130203040b100f03081801091212090b040b071101140d05 79
    0x80402100d12849041503107400360b9411961503400074403040c494800c40001c0060302805208007070101000e52a0010420000301c001c0551651140280e11602804112107540c1001603481c11b000c3c40405981c410081c24000101701b08006420700800310003600341c07001340618150201c0030404f020203010410011a19010940304008200d8540182180164104028000000c005090305829240e0458020a06810b01b102080c0203015016103060000d03821070500502080e4200158000c0b030281d64140441da0300c92074089401a0f080c4a800e80136202000308201c00c030340e2648495041c80005050f44888000681d9000c141d800583c0d00381c40340340000050183c0c280007850050002c0100c07014503c02d45141da01c0f4100ad602a1140004060707900b20442e0845a00ca80c4446000e480304521320103101560f410111074564090f0f11810114180300c0700440e118850105460032951443c0d0302516011140c1d848a00c84a01c0350405410300507041c07c1c0008041254010341302c0c010b1162000911031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 47146056 1250 47144806 47144809
    0x30405210c0d030509090402150a050301081207120f03020d02030c0901120e1207050c090702030c01060603050f0103060c0306090c050901080f01030b010b2514010506030705131505030106060905 85
    0x107400e1246684242002400c2c1c8000a4020f0184c40e141d074400ca68603480d41d0f43d035001140d00c0d00001043d80d2491880000e03141416604003003e035041e40d680000b1522000d54004210f41c10780b02c3e61030082c110424605640da101c6100380d042001980d81464054100744021903128180d0300203581d000c101070300114501c0381da560303c00d0141180441024040c0441001c0520681c0c840c221a0b003000d0360400001010401d1010402624005100c081d20f105d1032480c1c02c000083d140d8021600440d025428034000290440c403a0090f140144240390307550300c0d181d01e1a41d0b1500200481d070078960a258850000250342003143c031400d40c68101584500d59205941400107040c140000d01010400c4610700c01840420a8030314030a0548446601c0e941d80c5950440800c0202c1c000010402402d0f200014480200311724910044145a1154001d008175101d050406449542a0080c90341112008901102080042c1c20803400001800d00c141c21a944810101c1d00355050b07030700400042180d48004000c1e5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 47147306 1250 47146056 47146063
    0x42601020304030c11220b03160e06090a0b0603340503090f010203010f050409020102030f03100e060f030a03030c03140405060f010e010b0f0a0516060b0901120f1403040521 76
    0x441c5002c0301e04142c40141507004079901070680003030f06c2005544124052954504100d041c6c61030303001c04032012032169520f0a88246103421180d07140034840c0030001c1881222240107003924040001c00c0c0c141596170380100a200c0c281a45c20b03200300400d81e00c2c04081c44d00d100104020340c4500503590280d40b440e03c0e250081ca08401c10700c08000b80d03071040004104c062403480c1c00d0010f98008035800704601901c4d00040349580607183e2840032100780001403150412492000c0c01c1103441c6d04141540ca6070303846041040c0170451410345034260b0420440e5000182c40b0f9840842d0040150030000b40314001c828020f11044ea017214121000e078005002d000040a0080c0220300401c1400c1d801d8200f581800c0c004a01802000300c28800041c003c00c4203a03119004505503411010301440b09483c1c040141007002c090641010480d010703591160011030761109004600200b25000024139065040715079a000c00054040c0b000c1030240004d00010074a5956614644460822015060344407441807030100d05 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 47148556 1250 47147306 47147333
    0xd0f0c2009101a0a050c0d09090b01050c03030a050406180503120108060105010f0804050304090509010b01030b030d050f0d0b041d010605180f130212031c060b042601020304030c 78
    0x1225041010450b07400d40e43c0705010410322041c81141c0707864640d00c0550300c078000e808201071580144108400080d9014418201301c91031010148118680c0038010f44280c401c000c0b1007100350704200001481c03151145c0101340c000d4819040003510350071001e0a0b64115400400c11100b0360800a160106019001e000e5400352194001408480d40741600207450141c06443d11424421444001003c1c4581402614001c1c64030f502c05000c0c07071038403513060707402003420803040d0740442e24203e031a0820f810001340f5500d11813001d8855903e821180c410500664001e21200a605500c520b03101c1c4403925540108071001c00090000394520500ca4500c900303507201900941d0058581a180c0c42d50f104a41e80c10a404c418461800314190721800c043c80c0d0340598210303010750420744d585203910440c0301c00802800f0b00e03028070040b0900c2c5001181c84105656951048501c202000d100902500f2040c0f9001c00100c0c840703408c224142e0030841e0085099800449042e0041002056030009225442e5601207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 47149806 1250 47148556 47148571
    0x608010807060807081302030118050d0e0102030a0e04061e050307060302070209040201050904150b03090d0c02030a02060a02070906081b0d120e0a03150c020f0703050d0f0c2009 78
    0x300940c240b4100a101070001000c02c400c0024444c0421030303402510100c50001c98002c2c0090100002c1504041780454500008950b14070030701c0260000340344101d0b15461410016406545001c80b8030f10102e44070511310b0585980036507141d100281c0090500020b400c100703004110100410300d048101400d180e030650000c42410b0042103407800695890100b942d100354242031194a940240b40420020a110055a091040c0006000c07800b4040000514400d45400741164042c0c0c0e0304050440b204020628025010381c000302d544001490020f010349000e40c803600c100c03a0115941c040d5607040e01c003941e214082c1c0c1d03040307450041628170404074102c038031070000d4900c1e810104050780c1c1d2105504805004104110000070002009e0b40c0d11030202005640040b101801540d8034001d04004141c0540c1100251152040049580b0000324203102140c4d001009460586c3c88603206450303500b03209000c0020000c407040f28000180c0f0030340700080544524500114140000d4050010100f4081d007101d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 47151056 1250 47149806 47149813
    0xa061502030f07030503180a05010b04050603070e0415020909250305060f040504060b060a030f06050a0b0703080703060f0303030906050c0306150d0b10110c06040303050a0f0207080f030406080108 86
    0x4004051520200c4000f00d601d8074200d552136803400c62501480d031105208100354081c24005009000c0d054103d400c50f207900701c408012940b00d00c0c040603030f80c10b141d2044068031030810000501142c14903404006500b4900740151500800400250303e800048031601c400c144825801c00d00807590002c500d100a00d6402c04100c1c50614900081020726880141c521994031140000c0410407030340c010706425840a0036158584000e4240500a0081028040680c52038510001214540a1041800caa50110300d0901e00740b45a10304444900d070081c054800e1540f10341c00042c048140ca07014500450007a900000c4070f00281c54000140ca0b00a4101c1f080e1000500c24080709580760b9403441220b8040c4014155201207044209000d00382400007554007181e03521035a5022600b014010342c102c01c1c408203a400c0d1002100400c40e49000e14000a800500b091004015080c0a038400318280807050048030b90161f6107203041440d00183c0590000b140d00040341c1003083e0b58004c0501c6001d8507900015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 47152306 1250 47151056 47151067
    0x5012d1107090b06160606030c090b1e0d020d060905070909110409080405061303020405040b090d0c030f03050601021504111507050c010c0f05010227010f02060103030f030f050a06150203 82
    0x500c050049101c000ea01c0c4017600164000c100c40390b80481c00035544181c81c002010399456650004243c81e10b40d4a010307100c040000c10b01000085041e04031034100a1406218503c2c98007840f803460401141102e07200e50b031b1403000011580420907940108045200851000c02d58134001e1082002e21001c01d00503030404039074000081c24001924140c603426101203403500400c1000ca90b0f0143c0c1a8000b0750018501024802401010a8590310845154044403060120018100c0e10642801400340c00903401c1d1981d8001580301743c0040b03420000501c12285030382492440d13140c0f0303814292012110000d02c00c21101803030800d89860703942c00559030040341c286080b0762900b58540184085c12410400601004010004203e9400c86010f4000008544503d1403e840e03000711140e0004000b100409180702041941c425481c0040d042c00e01c2d0701920050b46580d8003904c103400348055103410325031245004c0c0c0c0d08400a1080c075200d500d03807502c007040e924030b0310380302d2140700c1101000c1e0011900100075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 47153556 1250 47152306 47152309
    0x1030e011406130605040207080a23040b0304020d12081b0c060c160c08010b09060607050a03030c0210180c060314071107090203040510060e090705012d1107090b 71
    0x165024105440080803c0702d031450ba00700410703498101c030794020701c085030354002c6c42502d602610380c42c030141e204c040310240b03603142e400307401e140441c001030303480340100020300445d031201c000b85420a00c09044107010120a5030384d85030451400741140001003640e0308101c2a40c481131101c8590030000a40c05184c428103a06175904c03000700801070b01d4404030006003100944040300650240315040451100100e84561a4501810446001c64410303400000071034001d1818038100e590b11503000d0000c1c802c410f010340d0203601600090007024158003400190f00f068040c0b070b000343c0320360300805400340a00302c406281468a0b0600e41d08444101450001d401d00e02603191000f030358100700e240c10305a03042d000f035102061030301d01c50f5008220454004004d020400c0340020710b0440c9007440c40c1003440b05603140d0300b220741040c404985604032030344001740405c01940140b4a1820700c1c000e81e004c00800d4a000c4041812100f241844100000c000b1544040d90780e1061150300050604a2418001c0241000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 47154806 1250 47153556 47153591
    0x6050c0c0109081018080f030a05090111070303050601020c040204120302070b03070c0b13050703150c0e1e0a0b070b040b090604020d1202031903020406020c0a15140c07030b0601030e01 81
    0x29282d10119507075040540d6501c00840708014211b44c0304010680e10000c20303005190a80040e1a20b24015043c00040f8030030400c18040c814981804038441408c00e41a40c404402414001c0d0071a4158050201c0900b0a512607000600150511201c1c0d00c4408809240080c0b4014960380099041501841885403155000714808a19500314001120035128404100301c21190750400400d1071180c0d800000400040709181d100000200c0300401405d515007100340d0341920f0050b0300b0b5500c1040742056400c120b00c04460480b040801802c124022901e0358601007440d4805481541c0c0c40c0924001c020810640f0341c00380742c0c01050f502c0600040d061a07400310300700401c401c0000704101c01c820400e10b5031520030400c1d514142000880003242c44000c0740d010300203611a02034400140110081c00c201400d04040312002c50b003180025900d078850510f003c03510a150480340364042841003180f210809010410b520182d4012503265046007850301c005030441d19116180040d50341400d03088803003c503810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 47156056 1250 47154806 47154823
    0x5160b030f01090207081605010c0306080d08010e07020f0f01050406060b0f0304060902010314040c05030c0a060504120f0209011508100b030f0705090a0b1908010b04150302070b0106050c0c010908 86
    0xc000145e01c2e14054901140503000d01e030b5654400130800c80c101414486c0540044207000440e803800c1010300c3d2928205500c2e01c9801803442c3c013182c1488010080340c020502c01c03d038000060310541c0c95600202c2d2527a400e0108600e00402a0383d143c0051009024886c410750004080f200d00c0c1c2458020102076503800360000070009401da42d503c0496000b13690007900020128984910b200f061403070030307151140e803458441c0983e5020b4400d24030f0304125820421904825030765240c481c40e003003070314042004500d83c42828080362015580221040103866041e04035010340000e0390542200b0402d02e1009001010051411806040b0030f402005101c01080481c3d070404240940140181d81e03950003600d4034400c6000641e001803180034001000d40f0880003034003036111606580301642581190880b1084000e0080c46070740340c8200800c10070032405608006001c645030801504210b201c0d05d0744d04c3c654200341d02984c0800c6000031800080082401000b107500d00074280b50600604001170103030f03a145c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 47157306 1250 47156056 47156069
    0x606060903120819021c11030709050405040809030706091a12040605060a1503060303020f070602060708091002040b090f1206150a08010906020c0607080415020f090a0305160b030f01 80
    0xb034007281c60740107125614a5100031213503056548054070000f0003002c0714040000c00c9518949030104c840309486e40300312802040ea03a619400d00c0e0741801e042000034080980102c0d1151020800611a600c0034020f1100404240d1981046207203450078000d1080180350030300741c0c4074004121030303a600701032600559000364010314006940e950304408540241c025412202c89004034540011b01182e25801072429a40300303a00342d40903208000c6915586441500401016070007420001d10014812828194030031507000464040d07090882090049074002d4000301407942001848548a00b01030040303085040055030180d150225401e5115280c2c2000781c0b103e2034074000c80e074008440d40c1c2c407803038030101416040c002003060700d04914069000358071001c1100c019010300400690070300e0084440c60702c265001604c203410205a6280040294015440707295607900600194801303486200c00c11010314401e00080450b0000303506801d202d008198400c0d04072403400c00800c43c1c00003851480394110f031351 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 47158556 1250 47157306 47157317
    0xf060b010201021b010204060f0302190f170f01030b0f091e0f070f03170301060c03050702060403140601081216022b0b0a0b04020309030a11010e0d0309060606090312 73
    0x8a500100e000e07210710f10b01583c81340c24280d103c41180c10706500600c1103401030388070041e41e0300e07505109409901556030300c1a1608101c03181c45603028000c03124005909000d280212001135040c9103003403188404c1d07074540c560200c0f4200620800910000c0d02d600b280201c040a4050302c3c010320020355525210203031020700b500f040e00000c4130140030410018242128030588000ba80c5508084084501d10701c82925000328032480b14881c09204811241a41d0150780c0da024a0304454800350b41903407080744100e0f000f0324204130000c0418400c208410545008401806155150041c06c502c0c00c010b094000340c60003010441d80300b00504d00280402000c0c1d06850b04003410301e001005400850710005406c0900c07105800342d10400452105040c4182d05d040c40400501c00c00c84140000c07404100c8000200b6402000204001c600070301040004010810001c030303000902a20807400c1103a81801360300800d0b200c13605042005424050100a498545082c000407440c0d611030b1030303490b4480d0752038100f03111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 47159806 1250 47158556 47158571
    0x909080a0c020f10180504020406090e1504050a0c110c0109050111010e06070c050706080c030424020a030c09050904030e2b0c050301050703090b0c0c0304090e061e01030f06 76
    0x103c81d450204500e210090076400d90701071494002d00011500a03400ea4a80a002e10206a0345010702c2540c007510041e030b440f40703940b03400d00000b2a0070300400f800415010440c5075100f0003d40e140d0240f00e02c0344170015404112021000780c090100100508980c0d45030f00203002c041440d91340481500c080312401d180c410800100300302602d00415a01540d1a1a4080c4038100141360760480003e030801480b420480320f056650307400c12102c08006070f6000c09282c0d02000810042403402801100c1591410500d8900282c90b900030380480c3c1c08a0b0030b20f000b01e0740725685203c0380303a0030100d2900181010340d08121030b4900760b0b500401c860701c0789003070344c0c41750090b41c1b5a13a0130740402c4102c0c00d483c80b0080d8048030f030382020750401e1420b140d1b8510480d8865070034800051130307141c428061030718000c2c0c0c8590074030764a4940d101d4107030283d080604500301512041c0f00c0002c8182860061403001000600640a203040086a82c050b8803440301c03c0313600303004694004000046a48141c0c51006401810008881 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 47161056 1250 47159806 47159809
    0x3120f0906041d090f12030402030f0a0308060a05030102120106030207150c09050901080f0a080c0f061302041b02030a0503060409020603040b0136020c280308010909080a0c02 77
    0xa018040302903402100c080b4012401410880343c0d05410003d00010031260303600d00c1c5015030340d002e008550302455082106080100244800035542007840101599030803030042070b0140c9444080c06090380015000340034003482c0e041c00e070361700405044150001e5107080700b42d04981070b4041044c070684003016400203881c401d001c02c80d160710416100c00042403000c01c2c44400010186051405520700c100c800000004500e4000182e84414050742d40162102858a403543c4140d5040207a102ca041c2c02428071303894000c0c01c1800410f01c41c00da0707482da5143c10202d03401444115410b54400440d0164008059142c5540000c1078400c0001e00380b60050362a5684008600a013000c40d10081d00a87c01000384410082114450340c1624056903030f10700c0d0710900c0000c0380e440701100e8414500c1040400c2c42c245a904894004140c60703101d2004868442204803000304801c9600440c2000b010200c204240030140d0180715540100f120344070038040d074240b90f1602d850f035111b40d1700e4007014095800e540b842107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 47162306 1250 47161056 47161087
    0x906011809110621010e060418020d110103020d020c060117150f0c040504020f0a0e010e0a0302040509150106180524070201020106051c0507050d0507060f030f06030819030504020312 80
    0x410189100407840b560b40e0561b1a240b20302c142c1c0c10911641c2052001503483da0340b4002000d1454000304044200c0030f40391648600040c000b504c45040580801c841c40c41c0c00c51a00051921042d1540101015850400c03001402c4004026608c81034100c102c514011050b40d104058120401d005601425140c85209981903c0307039a00c51a0014000310707140c01200000405401d03100490344802801502440045500465440c0d046034080c405001c14000750510794401c1c0d40c842126402c031030101504803003010510360240c0c0032900041040341d00c40c4c0c14000c0e020021009080541e045080f91041d2010148800c2e032402a900102601103000c0007968800d400403030041802600002408031700480800e04011994025502c51046c140c000031070f801e010703018144103a0080c02400119040c02003c84440d143d00c0c600348105501c1d8501c004005c0154801c5070003c0d803058505540d1031414040c1341183c10300d06807041003072610341801c010160b04e01041034011104100041ea07611150000b04923017 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 47163556 1250 47162306 47162347
    0x1020624120118060204050117010308030a020c0705040e0705031b011d06070f030521040f03110a0803070810140d080a050720040e062e030b09060118091106 69
    0x100c00d00740b6201009000a40d4006d005485003a84d4680c6200600c000c030341e120346800c1c4001000d4100400c00206160280c1d805051403c108105903501241d4510006003a142040d00d409110b0704510390800c913034641004440c190903084075810261851640c0064414170011440c408480e801c0b45850705580da0740c6046400890344000e00200300409418024856003118814494018103a4440d90051422401142c82243e01144207416903282c2d587c120f4003031814005e541981d100b0000c003903000410404c0a18403413240c40d641c6001034038001c601c0011014403680850024802c4210080e003c0d00d030343d103260204a42100ca0340e5554003064200f1105072041d1000540074140404003280d91440301c0b4840000c80c5001c45080c004694007804550700c88005441035601c07500c020600d580c0d20403800c2c01c0e0654104005000d92a080e9480e04c520084840844a50740580c21610043c00b907800da2545044246403030303550402031646907a54042444140e860305601c181e202150b02c00800c0840f042056 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 47164806 1250 47163556 47163581
    0x12060f0c07060c030501030309060923180f040519050a0f110a0b0405040501081501090b01050702060a03050402090c03010b04230d050709050a1109090a0f050114010206241201 77
    0x44003d20b40310004000705800e010441c001509000001240362207002c1c00320684029000261040100442d4800300c401031201c007030b4105419100341421603030b2030300003988207035001e07000071456180030700c0c03d80d040c4180800d80c80d07580001d0f00380ca48041900003030711440c01a40020409010328442c14152000f180c0e0b156001da019412510200e0001e4403070000e4000c0310740c03c0e01e0500c581c0e6250070016841d030701c04e0100354083d500050010084400349402221350448103040c400e1401803e0303000308440794000400c04010a4440c0c051004509044010031350000c000f080c550308650410020241906c50342c4030742480c130810700205003594004c41503031007d142c01c020002d0102114500c0d255885504511504108503d0f05001461884803401038075980d80380000c00c2da00d84180c0c83c04100e20b03424068030301040c1d25591484010b4408941c801c26019118400c5c084240341d40e010002850204002c2010a000580040c0c00310600184050300d88203640071541120007a1b1821039480c01007600c4076559 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 47166056 1250 47164806 47164811
    0xa0306090c020703050105090105090309130908030c031602060103110f0f0612090f030301210525090b0f060a0f02030705010504030e1201020a0801140d0f1401050612060f0c0706 78
    0x404076981c001840301c0481c2d10a82c02448aa5941c0c0d0400c0d08907013044460204036041009044220315000a0a42c164a071a21000070041800d44681110f90401c81d261451400c00006200c3d030311603010742ca1150f180391480186155030441da2100000121070200c1400350324580801c000b150744d030b9078410440700d60103085243ca80114025002c1c11030760540e24210355004401d10441b000c0e00c00b0085906a80d0051186000304000040d62658055010f10036034544c041d000307214408480610020a41044684504581c6420680c940044403812150548100b1807010408141d45404082d50701400845c03e03c1ca450380ba90107010380c110b106403070005003594a407030108010075410244048800385e041e1074041000040d0f4611500301d02c01c401854010950000c01000b02a00c1c0800310304401501074800c1228010544d80c20307075801040c410403103814030605c0c542444020240700340c03a03021a0884444141c100c00c044644d031251000341030703281c0d01a000000034014080d0403040b41e03481c60b0703c10300c00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 47167306 1250 47166056 47166071
    0xd0209090a0c1b1a190203090c0108010909030903080f0903030a020703050d09050303070b09160603020c010f11251202010e0c040507050f07020a0905010806150901060e01050a030609 80
    0xc420080c1020400c14002c0b40c3c54100094540c00404011604150700c2500440c420600c0c05040d00050f4000b0001d0006015041c0c58500040d81400039602a801440c02440721a41000c00505140016000502c401e46060b01e2000820703030200b141d4048a4100840300d95a1148151010072803140c0e080b1150984400908401061b0b130006064040b01e00802c00c0e2900c0e80244442207540307105a1040c42d900d64801d0000c807020070030021a1503000300070344c400c4034400c11005660002030b600c15403084001c254041640918031100380a0b2030740510090780c0400010001c00354030b02c0c40d4000c03038115803821040b01c1404900d0010225024031030740d4200401c07510803180c45034024081e1a030400b0107122400f031071045030014117103409a035025055079210325050010700d0094030328941009009aa11070501e8400003002c46240c80f9250181c481000a42018544400d40a21906020a2180c020b1100000400040381e100802c0c0c0141ca80034a4a0382e5210382c010000c4016000540228404034a000b16 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 47168556 1250 47167306 47167321
    0x60c02060c1e01060504020901050901030f0b031f18050304030b0705090a260604020306070c0f020405040b010f080a15020706020706061511060f0106080408071e1103010b030709020d020909 83
    0x1401ca0540321070b80020720606440f0010302041c1d0140d00c40c00307408036501b400001103940c060b80103200500d10120000603c500f00341d000900c0c14a00e109042034041981c0c10b0822680058011401e88101d04014500e80c031b40c4694903940d4911403484041c1c003443c166004105038502c02c0003264004d080042c98225a5178885403c00b540b50f040c0e0080009105005891a1a428021504a21031900140681101e941d403401c00d68618104000484481c01c041901400580d240e1040d28001c9001c0c0d0200c00c0c843d810080d00005650903500141c61690040c01400c0004203402003501301c00c07444040160301c50941d468008007030b010f66800100550705012001c1801c20320010b8202c0030324810f60310043e0b41048451350036200c4905641c3c01502000340300c01401101d000d0000c03950080e1180650a1515034140c492500d40c210032441c1204c03240f004805481030280002d0300502c1650124000c000c2400b000002a648550314459607100d075402007220004003050703a055401508016008600a00e06040b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 47169806 1250 47168556 47168593
    0x7081b030a0f030b010c15020c010e030c06040302121c150302030f0114060f0a05060c0f03040806090d09061b030302040518100e01050d0303020d1811040608030a09060c02060c 77
    0x3800b0800083c0f410400c91107944c407410745084025005840d4000c00e10000c4e4900e03001e5480001a40344640d280c000f40d41e104042040105040c032110700140c91281813038a0020304014154070020380440007801881d44594600002c0070882440043c0054540702c1c24405070320b81390a0f41d0000c0c0d0305016200d50300c0404103064104455403c00089003080e1035032030344100140500781c9010340380c102e115000300384141c0c10f04900821084010b0401c0f2030107030b40e0390800c040c9940d1043e040710389d240c0c2026052180905040011081507102ca040402c0390307504001d0f0042000d500d060f500020681d40010300341c14180a030341110b010345070250010707604034030b503030f801003200f11069901d03400b103256030308000031892007040c8442d0584500034200210394405444c214040d40101c10380411082e42c5400c9140999158286400281d00c616100301400d00d40c201080100c5000f9400044142c0082204001550344181c0310f90943c0e031a410409031006e00350003c038406004030b80d00102140b007110303806040c807083c48 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 47171056 1250 47169806 47169827
    0xf0c03170705031905011206150b070c030b09010902060304020108060109030c0603060501020601080c030a030f030b0405040303060302090601031a100504030512031902070807020f0d020306040b061e0607081b030a 93
    0x2c07640c0d0000d132501c0301800c42124070901c40d00b4200c41000d480640010001d401481c608418001701c2501c00743c55a10385c500542c0488c00c101d070401c589000400403c5808000d0b142d01080310002040000b50f240c000c6041480003d10027810440901c0025102e0380c00352107410051034109000312030640c4ca038640030f40117066900405003d440f40d80f00000350718000003107070804204c0240c060030681c8585e070307000d440c2200701d8440903090545829455803d51181c0c031415118501075540403640b1451401489030323540d03001c0c01a6042600b406840a008002c000c0c041e4103030b850680d80c24030300401e02d0000b103440780115003000348540509044260800e0f1020051402420f00804042011001c00707640c0040388101c501c01840054140030310000362401c800310041003400078013000104141903001904142d0121800c079101d0b49442d041c0300750342c14205911310302c00c2c0c50281c02d40c4105043c0400600580504240208200000a518255000c594400c0701605c1c4000c002c880c0c8035080b0500140204007036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 47172306 1250 47171056 47171071
    0x62e02100b09060a060e0a18090b0a15170c09041109240d080d09030206040605150109090203090109020306010f05240d0905070b0403030507020405010602010c0f0c0317070503 77
    0x50810184040c42c1c6050268041c1000418149116107007420554441954a05455201e892010f00041d44440d040c4001208600700301c002801d64503602e840a050a8082e000d080f0851034144d001c61601000300c3d912055035030502d1074840340f5409048251800b445400c40d5500400100e0500040060000d00d55050031700031940e5000960b646c401182d19641c840481e082c90400004d241d09031800c115450400300c5003d01d102c640b03801101070740b032070903211448001c41c01a40070038100018084c0d184070712034201c0b041202e0102a21801e000003040e210b003c1c0146441c01e0ba0000101d00c1c102025881840031540c043d007511441c2d80d5880710102021400d00ca200c3c040e1011165402d5814800880742803603045e010000f42c00c051040e049003000f001901e004844074480c00c1800300b080c000080241c4000c40c03080c0c0d00d2503560391a034418482070f5041a0311860640e81051450340810380c00440e24110303100507143c0711450482e1350500f2540043c051f80840c0c1800604002d00540640c410011807160a1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 47173556 1250 47172306 47172311
    0x5040507080c0306130c03060c020c15090102030a050f0705060903070302060c041a03040c03080c0c041404020307052701150e191e08031803060903040e062e0210 71
    0x290707041e00e5915069600005981a001080040e20241d0300003506591203001d0314514070303182c1c0c0f0307552400111819403490501503808480082c5c1280f501c03a02c1500c2c00d04803800118100b0300c0d0040040d40d070b4081d95403407105001d404241290402c13401383c00d4821443c4c00404540560421000c01034580c0d00c06c400607001030164000268001d64030b00c00710b0381118410b03440040c282407504204291500041c02c200c03100d040f015070000206e200140600307070009540f006400c110b0824070030130080340d40e8140310b022148002e40810002d80c1e800f10742c01003218802d07640e0b105002c00d0b00e2594803030000d00309800580d42d40e6160010681d1003100743c1e00b80c104805512030000c40c00d05142000400091800e488040400504013401308081030107002076081c21248200e600c468442420a085401c43c08138510402003540c00a807492508028a94104104601030743c50203050500d403160404d401800140540c061005007a4001c030212861181481c0020994001542c50000203484d18100c09000284c41e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 47174806 1250 47173556 47173559
    0x20601090e06010509060d0501060906080c010809030f07080d0c21020c0601140607050601080606030d0807020307030f0915091a0901021c140310060f0507020f010c05160905040507 79
    0x20302a104100c00200741000420300d9a20706000c00031020002042daa8101941c40072050008009018180c05030805200103d4807074240403041d031406002988250400a0302c20902a40751000b008403000d00790301d03c403070690b00c80c01424451007512910880080c00c81c90207464120055014106504c0200030442000d4000340d030050407800da01490b0040704840e00b240004014403c8550914200d41e44041d1290781408025147c19007481c209138000d07440d07900142c00701301182c034061280c1d8080d0300d52810103c005003048200259240214000202403001140d1240d0ba21402030300c1000040070202c58400882a210301c00a101e6201442120203424049009482c0f2140e01400d4070710200d0180e0003002c00c81c1c107070b21010302d2203010001540c062100b421041101700101da07005600c21004803400000d202d103040401003034a03e140030407400300a0140650801a900e0280c100c01e452001d20708052060703800d080050030032842c086414054011058001a842a1500901d104a0080c000d485055 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 47176056 1250 47174806 47174819
    0x5070507050309010309031101020403050106090c110601060f020732040c121a031e0c0a0f09050a0b03030c1501050307240e0301020f070605060d080a03020c0f070b0406020601 77
    0x40c011a100140103802c18444401c80d5440780c0e00000505001e880d000803a05a0140b003030b0f0890344142c2082d1056519004184991038440c01043c2c0003000c10703d4140381200c0c0c3c0103070194440d0410f0168408000c51a00e491180700c3c4200700301c1340a40082040341e180000441201080d00d0b030b40a01c4551040b044150702821071825100e0741088840d2a01d40c42d10505600e850600202051400c05948210303000d010f1003580c0341005a140d00909170705203188081c00b1080820711307003085840002c0c1f040500c0c120a00900841e15070342c0b4100e0301c4010020030a0f45a05140001402c80a20840d0305848003203140207603441e000642c0102c0c110596800e417041d03601c4500b4140ca401b040d01803120184024518011014661000d41554900c6032030f0510400a200e00007a0a9a01c01a83c0328a80000441e11206000c000d100d01c2e50000340880d460350002d00c0603594042a0f008240b1a1801c2c1503000c204102484003c0c010000102005419500380c25150f2007041116001805020010300c580b80021500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 47177306 1250 47176056 47176067
    0x72f030d080103031d0409080c0a03120b030c0405040312240902041518030c0605030a0509030c06220b0103051501050904030e0411041d040b070309020f0f010e030f0c040507 76
    0x50f65055610510f414410810b00042c1c0610110a030350015980c28146000c1001d40010701642c0501c0809481300125a09005140720340110310f01150510340f035410030040d40c00140440c00c1c0a0242d4000c19559218201070f502841c07079030306048100c1d0404001c1c4491501049021000200f203245049031141c0310407244003280503c1c000d000c0c40019001c00c5074000b5000b5080541402c03080801c2c9941107440b0707580c1460f0300d40a44d000c0400f02d44040300b408203500c014012264090740400045040880b401d02c1c6c40da4804004d0040038240b00520344010b6800d11a001d4400100d4102e4a20080c559491800c6035440b03c2001c0c9400c01c1d15105000851036141520405000b10b4040d558100c004210404000080407880b820361704690702040300203404a900020243c2001070004c89209620305410010810391000b0700746800c03d482c0c01c0d03031040169203501140726411400e4800c0703003001e10701130016240b0b1618103040680c103105800401030784d00c00004400f55808802d44c1d09108075192650213981 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 47178556 1250 47177306 47177309
    0xf050106021014130c1706090c010323090f07060e041b02030a0311040e04061a040c090e0903070b0903040f12030906050915040603020c07050f0312072f030d0801 71
    0x20045120f004038004802c8441003910740d034020f171304000005664883c0361050001181414149400560803c400a00148107452680030282020702c03120300410380d006022801c0c40200c04200000e4400300e40f4841c800c00c00d18140c0000030b022503013600d0b16440098030600700365181034401d500345800c82030445a1510031200100c1c040d001542040d01006040c1c2c0500864004e83d54014010303c400100040d0703864105004d140180b2000420008560710764580066510001d409242800507890502d540a03400608580300168180c10707945452503000c2c15031088920180440c5040c0703060200030034001c401071003140c1440190f0918903a50311044010341c1200324000d000700d040b40c6000c02504d0300400003030607034140041c4064041c40d40801c1c4030143e44c01640240000076804124560380d00d41c1040008041c4c00b0440b61481d19480800c0081c0d503c00040007410b541e400c0c082811410410601004000750116006614061341000c40c40180c045044d04034610074070503103103501410307030050b40746a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 47179806 1250 47178556 47178581
    0x10204030302060612010f050403050a0f03050c0405010c030201060803030109061d090307030305040204090f05160611030702010c05100501030b0a05060103050601020c1504050d080904230126010f0501060210 91
    0x343c40d035240310400c001c01213903c44000c01075480d1103104280500500c55548968842c4d184c40d074480d01c1840b8000c0c066540c000c010024140341909121280d070480c1d090754100c41c800d00e45a14012490f2404901408065100c05894440400040382a500ca500400b0070340354280881d0090259040d803c00c00044140c5d00030115420411401003c2886070700065400b074000b03440810003e58a940d041003d60650109407040c5e00a00c441c052900301d0664202c008001901c1e00c4201004442d41d0503480c0d10402800a0610058188540130404280b101c2c10150f0360042c4100a5507940c0c1c00c011741c1002c000c0b1100c60b151403034440029110b60191203118080c10044c2c0c02051202c485005101541858200e07040c0188030902002030349549941850500c40d100e8100f1a866868200a201c01c0e1100d0142c41041580400c4c8044ea080340c0c100d94032811540d14440300c40d2003080c80300e050311030f0f210019003840c81c80d400c150680740201c0e80d13030f04254103e030301d00c2e801c540e218558290300308100c800301c01c4444e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 47181056 1250 47179806 47179813
    0x9110f0403061a030f010b01020f070602060f0a0e0a0303090c0506041d070e030f011a06070302061b040902270603130b0c0906031612060303120c0908011814010204030302 75
    0x1400420b506a120761410580312880701c42c0b5602010010f454140000e21030510390b0f464202181c0d155038180020444544500000c00c182810701078041c1d1525002883d000c1d814124200040409059800c150120300b40c20007030391071000740381c14014090410340e6026580c242c0700420028441c01c10b0380c21581121220020010517011040750a0280d1801038920810442d044d01440000d0307809019014525402200014412800c007411000c503d03180b0898520a203030512031900803d8011900950040c4804000301d404a1039407000e50503030141c1e402564280c0d10104503030080b02a5151a0010030309402d03094614a200401089054030080783d41c0c00d6000303204d065040010b0f400441c0c40d600195090b2000d820118142c000c120b0b907420844a2207034400d90700c260b040e00c950b084018a1155030a2200034030041c1e0458a0160899030307403003560007645070382d24182d094162164140317002400704d0300c000380328045a103510a50b14001c103a905503a1102801511048210148229422294980c025 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 47182306 1250 47181056 47181059
    0x8150f0106050703020a020901090e0714181b04030b0702060a06030c21020409060501030b0c09030a0209060f0d03020102030a0c020304080c0402090a080a03050319050f04080a0309170409110f04 85
    0x102c03803d8101020440c10b5202c3c00b141d900059903103d100c03074060154000d0020701d2600c810042403800c4026404040400c00628820740f040c0c40d400180d50071802c0860108145449400781c07180c01400712949020391030004200801000983e94050b80583c545034219042901c804c00c200084a0980c800205200d031160300c10091034100300ca42205118140401d090002000d8006c241903c00102c03084450039a590300500030043c4020406400a00304d100040c00c1203503060119548610b0844007904c04d2858500161441e5907103001c07034100c8600605a545802803900c0d0290203500141c400d814914101403c007c12280b0000c05d450441d030042000340000d041c00d800780802988071600154100c0c904a9011505001c1004014080c900c00e1b0364903581c1e841d0204c9110ba49400f00c030100f0b00314608203c2440744c00ca40c05440280c0140c0c000c001032381d8803405954154024501c410000b0440062012004c40950601d000b82040b26480442400620003003000c5c0b004034820244001d5954506010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 47183556 1250 47182306 47182319
    0x1150f0f0302090310060e01060f0e040b0406050402130302010906110a0b07020102090a032f0303190302130314120304050613020301020d020f1b010c0e0d0516060908150f01 76
    0x4119402003160070010319004181c0f020a01780311039031076103251a0ba01c2e0501004a00c41c81c48010b0b004001600e000f158048031740d0002861680c003d601c451007070fa00e60404100c1565290310110060130001c1045658034002c0b4076001e114646848140d010911240303001404030b0180b80b503079684031862406054803000d181d441030400035015160100f159803d004800f0300c0c1e220700702c0001c05180036010345d9242c0400c40d003400d84800000b070060070311000c1c0700007030515541b030000c1038505005410360303c2041c140340c01d14210000d000c2c00c60b100c1000411701c4030020510540855402c80740902c4400d42d04010a003841c0380c0f001d41f00c16a8000c00d5070340032200007203010301800826190b41d0310040000d482c142880000300c06a8200520a030441c110000305006100c00c044050001c1d41501402031020020f1008050609810200074602466584130103104200090207812080860300701c00e10b06154075504000d104251300d024a00551092400310311000c0342543c0030512079a0542000c1910303030309114 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 47184806 1250 47183556 47183567
    0x3071508090706030b010e19030f1b050f06040605090f04020f0d0e010b030703031d0603040605060f030a0302060604020702040204030507030501050402100221070807061406040b0105040506090906060c06010308030402040501150f 100
    0x9881e0b80304561000440003981040d1520590b078010b00d580b00820bc40300c440715000501e2940000c2c440c0340e064207501c0160f1520801c2d0360445409082558170741c2c200b940071909104060340c00f207502c00d200040c48490913400c0c2020703040e0440d003403c0400410303180704241d81c00c840e181d00c9000d038145d010034010030003e0b214003040d00508401040007504408a03074081559500191011203030f2035103400c05c0114070b0502c05400a40544114000e0041148948003e5107610002e041d0354003d90300050f80d1000d54441e42c0485000f1503000f011610210fa590411600801c0c042e181284940e20641c61365050b0380c80020785100142e041070b4240e10081401c80a03264540c060001100c1811044c040d40303020400c00d200b144003203505260403100920b440c00402081302c60f0044121b0500100f0f000600054444005540d002074050f5913540756600d500c00090402d004910155072180b150310000b204001c054005140200d01c01d490621050362103d100d0200c40107410100000900207aa050010300d100d103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 47186056 1250 47184806 47184829
    0x10b03070f170316030804031e0f050903160e041b0308090402070f060e010e0d03110f090f0d050109021f020a03032403050f0d050a05041403071508090706030b010e 72
    0x1801100c3c54410564050041145104c42c01d80200c1e03008820030042c1500081c480c0f410365143e00b040400c1c6c4244020203041c543d40320f040d040030014080b401420b903072410420403200d68600e01503060030b41c0c0c0d680028030000c0c404031740803241801091204010840034401c02001e4a51003503049041468000c01d0200a42040c00207551a41c80349076000302159003840342001e002042000860b14107040304440e403804030029040300070945803601d9840d083d0550415135a00341c0710810420364404401000070a100c1040d0060396025401448c88c104000055000c064001e109803100780305045850550850b00950750340440250704504842070019200358440180303115120b03803503e8a000702d041035030f071a10b019402c01c40302c66008507202d504a0000b00310680a6aa042c0b4165107016100d610041050281e44140b0020500141000d0710300d0760f06010400207007a040c01204c0198a680c00001c103400415030750744503280a15080480e22070b119010385400d041041c0c452110bc01011402d00c8000b180d103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 47187306 1250 47186056 47186099
    0x1020307021906090618140609030d0e0a050f030a030507020703030504122420030103210507060203070c02011701050105030c09040204030b0106031d0a11010807110109080408010b03070f 82
    0x440c0301303940000f241417141503040c405103041020f5408041c5400b04420f503510080c5181c41e44008100560010000b044900140400401140c0708240410047ca0140c0001000b041c0b40264290416102c1000001e030040101955003031041c0d4850407000da8640b80c05010180015108110a100561070300101e001c41510480c40e50803800c080700d00800038000c0c040b200030203280c2c603080f40321442c1e41d411050400ca00e6081d003032285103514681d68820020b6103500400c0c10a65240c103d410094007580a0f144c00c660000400e641c0c91400c000c0003040c040410100300d003c102000c02e4a04112082d90515040e2601038407514510307142e01041011071b400c5403203c644c0c0127030200004000105108000d9000f018691008a0030120001d40304040e022003011858260780060340b5540403e01d82d03988102111000c1c02c003d080740d01e80510840c0c3c04070b075082c00f1030303880e6080540e5032080203103060042044032802402040726246540400d0303114443c5105174000c29111840500c1108500d91484500d01103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 47188556 1250 47187306 47187311
    0x80709031a090f10020a1206050901060e01020f06040b01051507051015090e03030f130803010e070e040e060a0c0207240315060503100e01031a07031d061801020307021906 75
    0xc00840c42d13251150391414002c2c3c00c2e8020034840281900300c246260700844519090101c1070901c00403e440c0b080510480b820007041d400012401d900a024540c003000008054425610f850308281e045a842842000d00035940d040c034101c01d0021020070383d4500c1d0743c414040c19100030740150140c054400d4031a244c3c4c0354000c0280008442e030740c41c85080c2c41c00b403094026542740e180c0040100030018008004403601c03100d581a80d0300241400b01228152800e01000e1207aa81b03e20204030795143c0c074110300680041c5404407484072030b1030004070a8405c4414040a00010340c0d412812a01c807616071280018030041521400c0075050903110b0325000404030324000428008446182d208041694000d1011031400420301040c01d04003019480a07001040c1c0d003c005500d141d994001c1c00d040c440300407800c1c0320f400300451031061003074111101007890301d051160104a02442540c4640f019213a44c01da0000e000c200c81a00702040c000e5034411041d41c0c020b08003251114070031540089420104641d182c3c1d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 47189806 1250 47188556 47188573
    0x306040b0f031509010c02030703021009060212090a060b030706090308090324090c041806051f06050a0201050603060403080f070e041104060305090619090507031a0601080709031a09 80
    0x40b4200041e0060030f44520310221a800c02820090868000240c40780454000b0090103000c0307900001c0c0c120f006d58110400045520a81c10807500900520ad04803c1c000650414062008000505446840d0203402e0400c15803a845d420140d40790341070b21035600840d480c1102080030a035030303002400782050068262051031b510301c19100456a44020070f0480400000d09211070711404110007000c404041d10100b00e9400348040d62240d00342152001404980c5540000301401c0200b2a401c100707000750350145020381e458140140a41c0c001c10a128015881c00c0005000d602c6e00040d03185c010b42d00f503145d6170b56039101c9600d0303841e60381c0001703060301e081c402c0003070705070380030f9152881070341208014451015100c40c140315001302500ca02030310a541551181e07041c0003c40c00308a2600d006000070340300000320540c00d8074129003082001c0e440641070a01c041e5100c02c1d030220075180948030741d400766114022551051015604058903000103400e21500c00945030185c03038645a943c0e0481010002c42d04602c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 47191056 1250 47189806 47189809
    0x1b0c0304030c060801121104051816060e0f060901030903110f1c020606010e01120603061505030f1b10030902030d120c090501231b15060d03050306040b0f 68
    0x1a0300903482100c0c1c2c0b0048100400c41182d004d682580500404d22054050034645d03202d040486c802d1600080c840c5988002050203803c10103102d5600d4841141170300c102000d442d006c0e466100c100d108501c0403179501044940740e8035000c003669581500040c4100d0034000300000450007042c07002e00171001d221241c400300040200070050081c410492400800d25203030400d49800e854154040c0d42800d41d4485014001d16a070401840030080034217107018120742c0b000f2003024001d4805603001409580c50301c0c0d041030145e50549416000d40764107070101c1d6010f0b00840c2c8d071071340e0b03a0807401036010748103000d550618050300e071800d04405101e2192402044072160f6030002820b00400c03000034404120f850f03000b107481d08164020701c81100180e08082c406103280c440043c0207424030300c240d168280b10000240c9e00c030350103003415505108000e1613541c450700441e520460ba00c000c0f1030034150100544800040701443c1c240c0610900a0741035407258110b03244c1c0c0041c0b0025003141c1031981d6102002c082c180416 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 47192306 1250 47191056 47191063
    0x30d0503010902090f12030702030c060c0606010f031b03050103020a08060103030c03050c0a150f050a110901050309010f06030312050f01030f080c0c090903130f0f030b0a02040315020c010b04050402091b0c 90
    0x401146c0c006199565101c0c410185008040252640550740610140120010200f000395200c04207080ca41c028105d840310407002480e00280c034004060142c81e0700c07421203034540e010905070303842907607001092500d0703201d020350f250424840200001c980444400029200307101030602c0b0840705003240c0c86541c60395120a42002d04078800051940d55941003820940680210b40d00710780040010421354001071020100c500c80c00d0009810f0000000c0401d00990307095100c1e25201c20407203410041e141e2070b840c0042880502c28030110f90581494086004c001c84254010b0417a644203825995200700c83d030759041660417128410b0500d0191120a00890f04c0d151011303442460340d90003942d51034282c4913111140070056008407401c4e0300d04c1b00041c8401d032510100d08042d01e401814082d4181e490400c090046c1c03040d5040180401700e030329040240b140d8950040c040080300f002c000d10000f260402440304440741224069407002041000ca200c0c21480e4502d808030b07080000d5868648808046244c0c507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 47193556 1250 47192306 47192329
    0xb03070c060f050c04060302090f040c0c02090a02040f090c02030c0601060e0a210627060204090b09060f01181e030201140c030301090b01050909090615030d0503010902090f 76
    0x8114462190420854948a412000240b281c010005401c1003020700229000340d0040f442415070000b950503036035176020804803e2050042c800d11510400480080a06080d80c0341207000c0d809000114080311228000c0d1802d8030309002921840c50310b02a40350b0041c091b03180c15a07003580409c010300c1820540920101e40605000c0e140c01030041400c00500040c90960350241c05140269a1442c1a1054968185900541012000c14405441700c0404d50000c1107000501884c4c0c00e00c82e10303a00b0811250040c00480d5460b410070402a081c030024072004c60340445409600828040001c0c010398012640b81458203106c1004074803ca4a4001000780072901e4010b1840111950008004641c1c0c42a60791402504070720804e0305100d046412141d0740e00040c00380c81c0c3c40c00d455810f20314850b44958191030b86200c00911262050401c0000c00351224001e1b074420304229030b03001e00585d2034200004c1c1d00060081c1d80d6a01c92444e1320340003071032000350052407180e035000b40d00143c29200c0740d03a011031099 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 47194806 1250 47193556 47193571
    0x70306031208010f0503030c0312040614011401180501080601080703021e07060e210901030209060a030905010606020705060703080a0204030f03080106021504080304030503090c030106090e07080715050c03040b03 93
    0x303502d54142418020f00018903404507210741d004008404c403501d008010f5501c0c50155503c4028240c5503032401101400c135541085120301400030001a08038030350003915031070800030b0320f440e034024822000e403079941006802120b0101e61140007149495204aa185a000b119440c005042c4032241c41d004850f02c40b061048200c13003c0108a4070306010b0184217060103800364034010700030070a00884441c2c00142d0f6410018404101040805059010350107c401540c030040c000c2c1c0e501c0d004910080e00811444405503495881d0800218089000249860503107100820150400015940448000300e0003070203041c10903000e01c400400601c591182c4041640311b40c5901030a5070608000a2803d09030404140c4c5200c00c0c4000c0c0030124000c0c0741202e0f001901850050b507a0f54610718400e24140701c804405415620340003001485059552081a0a66079801035440c510f60342c808007940c4d24424003900303580304130100046214500580007000c9050080c82500c1c246541c8803083d100b00d030411940f51 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 47196056 1250 47194806 47194817
    0xc070206070c051509120601050901210f0605040b07020c0102031804060f0305011d01060f050d110a080601080c090c030601111609021306170114150c010f0b010504080a08030703060312 81
    0x41703652421400d0b0500d0384020100511f05989081d000a00040b010702c90008468a40101017400c0ca40b15440c2c1d0300c11a401c5114007002445600e80f041c0105011902914540c1180c00802d01c281e10203d2400f110000c1607000f1030401d4500070340d003125811081754050307110317039070302c00000d80e500010800800841c001d10000995900580310300c03e40107103040385050b00c0c7e4580081440310403c10381d4a181950301c15140021071894030b20703000c04662048201c0e07982c03083c00784a0020306402c00150741410380301910291a00155014240154901d0644501c200040c062001951652280c05203c0702d5644007400c503141c00313220f03140d1000310b4401d44e00007203600e580006001d904241000c40b090000c1c4450310303007100c3c501515030303003891310010600907110100c1a010007203000780d80d529103180c07070740c2c00c02024507580300b42c5501d41c0c500904840e8445030406080c40300801c025800756060380c080f108403a0117480049100c0d6200340132544002c01080515683e0907010000c10209030002414003e1a10350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 47197306 1250 47196056 47196067
    0x509010e060106080702060106180806150a050105070b0105040b0409080711011404050d060c09051512071107060507021c1209050a06050f0f04081903090902030c070206070c0515 78
    0x480c1001e00580011040c400d01406001d40d40c0e42c001695070441d24a4503240c0b070081850001000b0780c0285900083c82d80c4201c50034800c8441000d81002e18400c002c407098001183d84800548240c0910319014001d4074282d40108000d007800e420007034941d0710042c80001d02440c16a0781201303070303009071501f551013178104c115010700c80d40c1102400416903040d40850b4145890030000030b050310b03420030008151039280c040c03000020340920485006030000524905d01800c482a034407002e0b41004110100d1f402513400480d803082e0250014107020364544010f000c1d8030342000010345d51640b00c90000c0740c11040cbc4000c04900c4a9040c80f4514680380305e621450503400c43c00000500a07600761f00100d00c12034090201300481e0360000704880e001184131003155242e182410b000304d41740c0a2a03210b80030b14000c4040c42c400546045520000b818447c0d00c80180d003580719001801240000c4507040a24001004190701500c0d060300075101d660f00c02c00b15888070320740b1080400c55450085a06022001c0003041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 47198556 1250 47197306 47197331
    0x30a0305210c0d0b0307030807020613051309050c090106050a080714040e01170d0e01230705060601080a02090d02061b01060f080d020a0c060e12120d0605010203130509090f01050901 80
    0x42c00f001301c0c1c41140107041031410364075124500e02c10307180b00a100340c200051a03420403d84154200c01000003d000e2171640c4002450a409000c1c00c9404031510700650100d00900e150500d6858181e4840d030780c0361030801d071700c0503410b84501d40081d014106201c1c4660b102c6405550780300092024083c0120304004c0303135251611441a41c0d030017802c01c0d1240e801c00d1060110041c1d0060487c6012031007413802403a601d0800b4118120100314151011583d40001428024130400241c1140144800e076141069507031344da08404100d00030b0308a0035a01a96080014001d1314190014000c0d514035000d10400da8a56030b403034a03086500540c4450403000117001c040108003020b00c844104a0f14a001511031101c3d03950350202c9050060140c8400e008030321903180740741d8030ac0c5100041b5a00c009c8044031081550540a40d100d40c200071058407015080c80000705603944044240c0b64900100c208050b1140e00700030402c26203020090030400107101d041d11080841b0824018140504800000010852901203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 47199806 1250 47198556 47198561
    0x10b0304080703090909380609060a08010504060509060915041506150c02010e06070203060a020c0f0d03150f261f02030a05010506030601050d05040c0f03080a020714030a0305210c0d 80
    0x1010301c0c0307800b01c503181e6540401f1a03030005603900820881d0700084564610300000d6440700c45800a011130741c031b404204401c101883e4440b0380680b400c241191641d5442c40d600c0c9984000009030180d4040110006c1400144204240d101d1261802c102103540e0391148044445080841c5241b0300240d9900c40079000e658205180d14040700003074030014034000c00d42e004280d60304c801801507280a54001480090683c040c04640c010384102c009490000511340c90040c050400095040a645008400042c0601400c20185c08807034210300c1104c0c506654601c230b104044804e080241305409800360001d649006981c030908200030f107410050301d03801c0585400b0220b68051304554042c801c200b052041c5eaa0b00481070f20302450692202207a1523035507140511050480340e012014144050030080200519540a0040d048480d03084425855813010b000200400340421705030543c01c0003c1c8580860300c928000e00e0b50b4100c0c0883d280b44c3d144403450602d50020304a5208040d45000300314109000301ca030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 47201056 1250 47199806 47199863
    0x21070308060f031203040206041205070f06020309100f02070807060336120908010f0204030201020f010501210503040e010e041703060109090504020f150901110105010b0304080703090909 82
    0x2610a181c200701c00c0300c00301c3e595074824100f1306003152004c4001011581c41c1d00888000d405070110452213001689019541c6981c0740c0074200b00c02c3c0c600f003404100d10b440081698156040103004030403400700000280c41d00300707607200c1540440c010b5000100344154200001c2004245a82d00007c105e4505412042d40d0f41132007107001c460006441c00b00070a01d134500c00c100082c5411000640060b9018802950801141c0d44041c441c1c0d401c0c940304000320150b540c007620449000fa0241c03400800115400703802c88009003c1c02041039110b4403500540807003002d030f10070001c4c4600d00312450540c4602b4080707000c02099115110109100007000100140b6022140180107100c4400c0e0540c00c2c4032001814099050007440505503035000024159030304c1028850b4000405000010b03041024a03182800f03a000c1040c1790b012484015040074008814820b043c101e6080001076401c42e12250b80e0001141d0cc0224160100108440f0101e0314001910990305124880c0c1d046654252010011001ca1a200c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 47202306 1250 47201056 47201059
    0xc12021c0c120e03100608010902040c08040510180602030906090d0503090316030e0603090601140307031104050601031401080604021003061202040b010210020a0809070f0303050711032107030806 86
    0x5106000082c000100307002501c140e4248840d981c040d0300003080c40d2685a202d4129024104200000c20340819401130300d0b26402030764140051100040180c8000d401560b009000364440301202c1d0b041c107120341c000042c80706820100000a911921441c3c2030303070401d81d401800c0341c21040030b21608840400069403100f130941031490075803600d180441c0d01e0380118610480b806a40e002410308041c030030f00da0540c080340c1c0205095100d00313200000566072142405400400400744d007450500386400502802226442001c0d45140403850f028003014040150006060646078402e1560008c0c3c2c0341c00361070290059200038020380c541070040040c1c030032100c2c420070709040c039044c0c05000c810010880148503540584000c03c006240e400100d10304041650100922440442d090360319507071001c0594040c2c1c0c40c105c200c1e440c0e00e44801040c80901d00710710005001c101c0030030000740040d014101d180501c59005040e1070b95000180d1101d03902e4a034860740411707180000940402015044001da80c0c12038070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 47203556 1250 47202306 47202317
    0xf09011103010e040c0f0308120c0f0406031e0612050c0a0f171e0709151202130e030a0806030f01050105061b010209030f03070c0608040206090d030c12021c 69
    0x3401815400d4610060061040001c040400a4244002401c07140014014410402501e581c0c030f0811040310340100291402c0c00f402e840218a108440000342c802d980106030b21580f40510b01a0103800610600c4520140d4802100a01d0f02400c9540708410060605423a0800342c442186003081c2002d0700c60201030310404c803010f0180000071030680901c003550395117030704d101007403000c96561032030650203507004003009211145071030140030049400d0048440e845400d01c444000300c800100942141d00030b4595a15609030400054034065a04c0c620149000300001818504180c17080e056902c0200c902c40814220401e010341810204407810301102200300070403065043c01c000400ca031180280409905401d000400b0780e2030400c0d0f04aa84083c401421120110380c181c03001d82c0c81750000300b001d4070000001d130380004405000c0c1e92014842c039801041c10703103441419400c005504505180030350400480c0c400c650002401c00300c2041166945400174111008028811184140c209600108011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 47204806 1250 47203556 47203571
    0x501060801090e100902010201020c100b150309030307032a0e010e1903030e030c120d020d08220602040315060305010f0e030702090a0b0a090c030c09030201020d030b0319050102030f0901 82
    0x50340031450450583d9400c0b070201e1a20305c5400100e0281c09200c04104d4140103c8405101c00c03910390740b15214a87c001e545d6880c0c840255010305286010489240a580c1c00c10030004d8502480380d8428100c2e6000e8200d090741540184c5942c0c04941600c0410001266045018040f50741c3c0040e070307500d500701084070010f80e45154504a0602001c4511004062044120041245580c1031100c1c0756040806862012271151000d05a0b549240c5141e03000050701030004841d41c40e0f0301c1500002d20584440751031007000c800d05131000507060608402520f00650900003c000200411000031482001940104400b41541051401c4070840900180d840f4a044005a242c81022098176103030b94044072006440e0b03407407050307101c05070000d107400310b41c040c140d040040740214443d0300903c0c000e80d590f902045014000c2d4000d0b100752005010107409039200481c0395005a200303070820040410050140c403d52410358000309039204071428122004e940105c20041640101c2c0c4140340e000c41008024490342 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 47206056 1250 47204806 47204831
    0x30501140f18070e030f060a140105010c1104060f060c0512040f03020904020a09020307050a02010608010b0609041a10020307050c0604030809090a090b0c040512070332010f050106080109 82
    0x52200c0b20311441140001ca00051505025042c44000b100e00a8191502a0710f03c001142e03c0350300c2260b0480226103084041501034000b2000c160683c2c1d41a12281c01e282160740341d84007990384140c2040e40c065110440403480030f0403955100700401d480d850b0300d1441d03891440e1560801c0b1150034081d5442509200401448400c11505400c40c0d0301991030384200c2c1c50798000314181411503080244c00c5800041480206940400180180740160b4000c01c2400e8440782410300342c44c2210002644030005011100f8640360991182100c2e030418000b070302c1c541071840042a007629445107000007580021a002d418400300380510380050100300e03a05840c2c80c0c21580c0b600070601078949101d01411403d00000c0d8182601e81c004124907401068940207460401720304802c0307038081d0042074044d03001c940c0300640680000a00c0420360ba40181d40c51840016841601241c0046094000300c440c20000c1c14407101c1020300c10999070317000401010500b50704058015007021010f0b0b000d00890743c500003040e000d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 47207306 1250 47206056 47206069
    0x702060f180a02030d050a09080a030e04050a091a0601030e150406090c030b0109020306100512040204021e0408030403030219080f030a1d0105010f090c0801050913080703030501140f 80
    0xc00302888011008038103070a0018038202004030000d4140c0f20340d00c001900c03581c04c840030b8400001a0b5036421502920380d03a03561340316075103600001c0105100e0804030340545083d4002541c414030740e010020f084940d503140c0014100c050004045648014414841c003540e050040c180c26500c018020314803180348000940311203800400c01340085940c0c003044400c0144940120000b15000a9501d6103540c4600000c40294010745110b071217400d9400501500da070264007036070003640129604102c00da403941c003880080d5111240c040b40e90410240040c4025407107501405c06004008019a2600d0962038064070b003000480362664030540300e2003035100090154040b43e00c0001800c48a40d100d41350035400030090510042e02c44c2101048400303503603000742c0541c031850403240c0c0d1400700e000072a900e8100b181200ca143c01424001491178005200e9030030400206c40d0410000100194122543e0f1104450364008000840011f5110001040381c56000000b20307803090411a0f51803480400c03000060750 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 47208556 1250 47207306 47207311
    0xc02070f0b0702030a0506010803031e0106080a1109030f030306040b030c060409021312030e13150902090a05060705060403030b010f1d120712060f020708090607081306080f0702060f 80
    0x280910001520b0b0700310b441c28014000c005074401d04071420395849800807610707904101e64070403103501c0c03c80e403034140004088601d82c121130461719541502d403034a10445005d054400407030300c02c000c4100140a05514108943d5035100360300d001071038030790414a00300400c0e145030542d80e51299024003241500359071840d00720b6013125019103005075a50030142e00080c090000c1da004641840440c1074400078540c00c60f008900d41d0f44200e400c000032402084008003201c0c3c0022072410036a01750f030310a11060245500900d0f9494009110b117000f2540c07400042e1040c0d2104c001211160040c105000030540c0601841e030344c00c8000d00342000e0700c00301e90f90001e012400c0c05600d4a4001d480c07220070346c041c0d01c4040a520302d40000c4420348003c0c1d40c8454005175680030b00101116400d2030030000c400c111246209888145d540f0461480c981003580c4108031084d04001002e50314210b0410202c03000c407084030f01400c0105545d807510f142501d402c040e040d681003c000c0c4083c096402c400100000079251054069 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 47209806 1250 47208556 47208569
    0x140f03062202040603030503091e070911070204090303021902070e150d050d031b050702030a0206030c040f120311150609090c04021b06070516020609011103070c05040c02070f 77
    0x2101800507039807109290109940650801c0ca001400310900d0b503c4030007144500201000c43c2c0c610885aa90048100d2810441c079043d030b0029981840182110307084081030b10900e41041d81881c4860700060300700e40311304900310b010a81c00038030004020900c80240250720151300203406081d24100d0101c034045801060070084501c520705225495680800080e03c054200040325024070102c10054000d00c44e906600b902680c00031000d005180c424812200300e50b03030240c09045400c01c95424007200d50405081171100da83d00340300124030280395064050003402c9a00c03c0d00b400020f42e04018003241203800e4498406c3d04141e09182906042c1100140c2207941996011419913580f07582605040b220501c41da402400010b074100e20980701c180300c40300c01150100303490f841d864411055030b0070300c030304c24001700c4001c150700b840000361801c40060b01401106050800c0700c15140034080c1c2c1150311099045504020140301441681454414015000350034001441d1071404d1000c3e052080d2480c0c410345 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 47211056 1250 47209806 47209831
    0x8190c1206020f070b070912020d12020316030e0103050a020f03041103010f021602030d0206070c06020c0c04060303030c020c010503150906040f02041214030f0d02030a0908030907140f0306 83
    0x200e08014959044550040740f030300d60503494020520f0076241c0c24005a40304000940e44420110719030540008211700964003c0400c0c9030f580d12079546c03400400f00e5942000a5000c103001c00000703c40341c00a819040384c03003079464201c114581c40001d412520041c06608095106200c0c000003000000e04498015401000030100c80102e01d002138094508921101c0c4070900208a040c00c0a044d0325500316007500c220180c0708a415a44822030f6070f003000b12240000039140ca11a4004a6140c1e4014142188001c0540d0f117251603000120303066411079402140007d641e04d00c00c0c41d40a505219a840e018801d184c26031640c100000c4205440c000016a144074001e48008500c4664556000074006105a9002e545450b503991086592110341e0f402550103c07107003040d14070b40e80004801c07901030b00f1114007203d00f03042c5072900510080d04010b000c160001d9403101280003041a12029605c1407400701c000741003d070304060445007031441c4d540c0041d009910032440040031366800f04001d5880b00020281 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 47212306 1250 47211056 47211089
    0x6010c14031309050105031902010c2904050f0601081018061802032e051806010801020a020705040605060f070f0f031e0503040b040b092508190c 64
    0x240e000380003168000c0c0688000100301e070300610080010340440700c254500b00096a039038400d040e10b40044000512040d1480c1194000660041c0c80400440e07020381c806165002221114002e01d088141307119044900200400c410824100910a81440c00d00054035140d4545000265200701d1680e90b90801c540720000400e80151000b813104070207410020502c410031603590008002c280022060740030303004541c0b15100c081000a801280000c0e00d00440b20400d07203810b9540d00501d0050315a400d441415102d048419008000843c064102c1c10001640c07841400006850302d1741c203030300050049007003c4040226a44200036914128401d0640c259110040e2500c40c2e611006554000d090040c120100300a0540c098542005000840303400380c407032018184151000d010440d4020008480302001a00003800c0c600d4203900581e1000440e84039849a4111f0780306518076445d442c89003003d02c4d4081104038010030100611015007000b100125080d80c40300340c5401c02c280078940040914019 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 47213556 1250 47212306 47212313
    0x7060b19060807050c07090c020d170105040203072001050f01060e130e0a20030d090e1302040b03030408010e07050103200702150301030605060118060f0c050c0901060801060210020307050306010c 86
    0x4c40b101c0d03142082c25036180031f40300e50400c0000e04481c00d03003900602c141d01400307a50501070190704000f6540000318200d140c2c41d047c1000080d500041618040000758065414040f02c4e158001034034529110001c101c500d041c04400c915020142d0248003044140001c000040c0c55890000c00d944662130400304403c174000440d02e1a0813071020008107080e02002d1030200b152051651a080d01c4001c409480030340152a40c100c4583d41035001f01c98040c405540403503600c518011001c01018800340c004140803100d40002030458006620075529651203201c0020026000d10200c000307030400342001c00c1b5043d20031111031010704010111251804002a00105541d03c80c18214002c1104bd52410b94940c1c407850904068102a070380640840c440402d03410741046007503d1102510722a903a003c0040106400480340c04144103016a07907800b807000c195003583c85601c486400303000d030303074541c0845549030401c02403520086082420030940705000340020389a012013165041542440c1041e00c1942c21705 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 47214806 1250 47213556 47213567
    0x30c070209090a0c0f060e010216060503040314190822021c0609030e013b04020d020c03030121031409060c01050702010501140a0503060604051e0c07060b19060807 72
    0x403c09000d00b8040440024a203c25542010135108640e548424581c03200005907a0b0700c0c600f0031502d070000d1a0b807005109482c40b07440078507130140c064a0301904404a0740c00b41c40c0702e6070040e1a421482518030511801c0309800c190440d8100848422100d08850780c0b46444d04003c503a4200240f0810498540c001c0c0341d5a01e0b90040501500301208000c0b822003880c018101d1000308600700e0100d0550154152400c1c181060ba200e50034508142e2150740341b080c941540460f43c65054154402d500303114413207651400744068091700003c500210790782d5050480d006103000c01d00c124064684c6030402a040042d40c000040075100d40300720051a00c401c1351400294035800b03100c18000c655880e00c820440015030540206048410b00c42e84a40c904c11820300344a5411413030300582e078240d8402c00200d40c0e00d0425910030b55101e1529034109071524540c44a44c0c582081c143c0302010081c0c0041407000902038a40318140304c5003821600310002244c0c041902c5000c49041c403c0d482440f40a20004418134040c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 47216056 1250 47214806 47214823
    0x80c1204030c050d050910020309130c020313030528080d09020d140d0e010302040308030105090903040b0a2c090402090903040909050708160807120602160b060f06030c07020909 78
    0x103400d841002034013070301c000d1464000c5102c40c0e00c5205409542c1c03aa03240040101e803040ca0740a410150903000032004400a071000c8804001140f00400140d013140080e406000d001d1445000508101640120030741c072a42131081040955905680c0b4a5000602d00f008503805074840240110300c401c4c0c50f0002641c414182e0001030700c0c0900400c1746d24070100d004a080b10300040070b6194011410f0101004404a00590000404900341000107201d00e18003080881d5100e00054110fa10342901c8550121194000c0718102000c00c2c1c2ca121081c41c18015480c10b400c0e40c0e039440c0410800c04c0f030203030001070b81450054800f9001c0c09103040030900105080c02120081c140820091007950090300d0402c0d0707980c000b0f1140e81c001c2d00801e510310f400780300d11000c000d080b10720070b500800c112810280e43d0710000303c207914100c4070f080d070807c02c040044002d80b407403011450042075102c01c82d00c2c2801c240416040d034110014458103042003000f0540d8006000e503440e0b160190382088040d40c03a9800180ba003800d0b07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 47217306 1250 47216056 47216063
    0x1201912180b0406050a231803040312020606030a0b0f1801020408070504050a0209010804020108090f1209040c08040c0b07020a12050c012003041206020d050108010b0f01080c1204030c 81
    0x40150740000d100480312128000e920494040202d41e4403001c84030110360003025500310221040e40844400d0001c0c0c0e003059007003030804800d680340220a1403118903680c0542d008071685004158000d200b1034041c0580c1381e03c800143c010b00780014256844c000c40741c00c000c1250380f410b81c3e03e40c0454060402040c040402045501c001c66031a038031141102d9803040280f08003131140341400009030f285040c5000340d850a0106031500149a02d0703d500540728400700404a448900c2034103085800c8180811454083d4120580125510404c88040c80141e40340b000c0c1303c4050016180074040010034042d200e4048464040500392289070f1840050440465580200e4108805003000003d1100102d0600e040c070209803242d040d90003503103c010983c062061000c0500ba00300b88010031506c81d4007225041c0d02442984014506403400c0710b104101d400a0300050480c0c0c1d55458444c182d82080d04000b460781d4401d0030140114503050134000103a1040c903840b4940382c0c10200c08541054001c00400020983c0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 47218556 1250 47217306 47217341
    0xf050607060c110f1b0d0209040602090d0812010302010e030610140406050a03060506040b0916030c0e040507090504050c0f03061201110406180b03190e1c0201201912 73
    0x78030f604d681e595494409020000c501c03e4002000362a020b413481c4880b43d805822a00345503603d440d010300a4004964158112900c240302034000349400d0300420010400e1207101d1800c0d41140001008051209400317402a0b000c401444070001c0120300c000110b901c1c84444d1404801c1680100c1c001c2d12040c0d200e035801c03440002d808420414150482e03032003108140c804026040c0e9100822807601020381d02d5002c146001a2421810ba11075000710f54104c5c05800d004c00e401c3c0f04200454101c0b401218070200080c0c190609008501d00ba001d031a40040343c1c00c1d081c0d070130000c80301c40a962600c4040c0002d44284140d4403c460546000c0d0460030000d0014807079642c07103d070385450281009110b6244201002204000170172008880030a50f401540c4103468020344002e0f00314548010a80004083c510384180c00550480403640c030040160300000d54008141d992003010100b00541c8480c484212580c4140704895003010710203001c018042f000c0c94608441c4620420360f100402c3c580c01e10510125 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 47219806 1250 47218556 47218573
    0x40b0411150c030c0d05040308030a02130e01060f030f0c3222050d0305090103020702030c09090d09050d0201080f07051903091505041509030e12070509010f050607060c11 75
    0x44000c0060024602c1c1502a02c01e01c40101000700c944d1f100da800010305600040c0007040e4980382c0c41d8040d180c1c4085c001d12140c0b050b034a4034004215500241d01c0400084c00380c003202043c103035060040b000208039144091140f4011220090b00c190144021852090101d110304014000080010f45a255030040d51956071650a00c64400040c0e20b04210a90526000c0c00000d072802c0114480c603c01d07825513603450503d075031100110069400f613034090343d00d0311036100d800e19250f4138100014082c1a1800003414000071200300589403031001e07880f661013819220060b00150340c200300300d43c0d40305140c0081c100c4255124070041c0c0ea18010032042182d03040144409000841e099840b00120b9030103908140020000b0042a20680d58100c60041040c056103244820080c030710b130030071500f0384d100f41401c4d10900d103048003052a115210003e041d095020760002c200301d0905a1034603016140382098121502e00307010120703c1c144200d000003001169a204031ba01c10705d104040040200e000c4005484104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 47221056 1250 47219806 47219827
    0x2a14010f17010f0303020d020a050c370906050d050a080f040305060709050108010801150b210a0906140103080306010c0311060f0f07020c01140901031829040b041115 73
    0x18442d6004c210098170440307000c2148507000140203a00c15500100030840d50003102c0a00c5079441c0501c03264420000324144800c5070781c0060011054410710821040031031031810b108801562160740c070440c0510700241d00400421004220310381c085400c620500e0740c0700100c000c82c5200c1c3c400e903440a0000d00aa40070310100716408030040c012203009076903400d10746c1d80b1114980e01720f03141100c6105050420f44010041c1c0380c01c0d8400b80000803c8080000b606050745c244000031164121115980e51343e69804040403c0740b24030034458000580501030743c4540c1580c0e2a555a480060803450611108030605070400d88680d0742c41000c1031111050b40c01d036040442c401400d0700f4090300d440c102a084000028625403000a2400d10200305a4810718944900843c418a950002c2082d5042548541008000b01529808803200c1403084a20b4101d41e82d02691010740602e203107215020032409030050002190030400c1d010b0300550000d00c80004015020000741000c075000c14905001e034004180c00300d86 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 47222306 1250 47221056 47221079
    0x803010b04060201050f0f1f0b0a0309060c030908040308090a03020a090504150c020c1908030708040306050f010501080c0a1707030204050f0a06200f01092a14010f1701 74
    0x1203070010f400a01c480c0d15002904400e10004440504c2a110150002070a10001251405144001041c081000c3d520b807000085a5400b81c041100421740325002030003044902e2040d444080e025107000c00403081980e1b2609800c1c86540b0021b44508400711706801144e070f5085501d001594024410480d10356103101d010050501120b00b0f9a40c4106254000300301d4019000e0030b020742c0c0095024102d0005403000704160b4201c40715965130b000c1007141e804510143c08000429517103005500c8030751954554a408002d0741c1005100307c030703010440d100400c0746907000803030140c020b00d16034030303c54407510300b100304480040c10540002d02d4a0000d400348500c580e050350040044e02d00a45038000201e22080074005110f0b414411640050700260307407410f500034800c2c254a99a401c14040c0c902e525010041503003961049001130314210b00784000940740b90b9090350780e40c520302d00518070a00414500a400034106402e00340213818043d00c01100c0b1000380c4621440020060071401501c0b055840700102c103031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 47223556 1250 47222306 47222309
    0xd05010b0a180b0f0a05190801060b360607060e010c0e1507020927030301080d0815010f030c0504030b09030a020106060804050a030c11040e010506030601060c0503030c03130803010b04 81
    0x401c10b00e00300f0009450704004107401d9150401400c0e05d8405464041401100d64030400400c501c141459000716030004207002d200003c14040d244075490304d03d1558a11000800306d40390366030b1812014058042c002e50501d42c00c902420440368261111958105200076101400c41c0c191503500e800c1c4418800c5400c4108010744550640d000c000801680e0180d08451164607006548000e4130300000710040e07669020143c080c420603500c00441c00329050600c2c6960400c3c1c000f21100c0e085601901500303603000d884d49500c07851851180030304104840010300000300e01e10f4840b0416407034420030503080303010b0404c0300c0085a0050000308180780c1080b08907140d4116442c0040194203001000170224070030340ca2240200d410001034031071300c45259001e0b600c0c102000c20854843d02c905043c80310646d0f4500c16440c000510b00008103103482e1010826080c03070b5058203c1e00c01c0c4229400c0000c0450b40c00001d6a5000702504881030743ca40700c03081944109140144010312051000002003a402002c502400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 47224806 1250 47223556 47223599
    0x105011502010c0903020603042103020a030f0b0918031605010609050604060b04171005071106091204030303050c0705010e0708010c03110a1b020604080c13020703020303060d05010b0a 81
    0x39816410018220b080e00e03200d04500000070b21105041c0050700d032803002150000d1240c042c88007000060f04800049010b00c00e400d00c007103070340811484420381d014091006030040a4004004200d6500700040c00044003038403400b0b800d03d160f84046030720402001103030301d80c403880c0582103c40085490f1460181c240c070301504d13244a00b4070011400c242028080d150603200702100150806050041c082040707200d84101c0c0f00c0a120380907600a143e502d921400b4000d80c86660340011801c0038907442031a00d140981401d0056120208040e6000704103410759041ea80c0c540740200c0d080c0c407403540b500b12300e00030380d4000b800551030107509600d034100003d0300744100c0702c44100a20100404032021740c115081c070811100c0403d020084054924440c81200c0c00940c000501c0e542c402015401041440d041500680c45a6000303104120441c500503112005010040405600d4101c4644d0029100c1c00003401c0b60380030302d811909401c1001b200b0340000c400ca481c05018a8006956080141c4940b1043c25110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 47226056 1250 47224806 47224829
    0x70f0c0c03061a03100203090703030f021c0903021009061e020a0b130308090c0609040203060301021606050a1d0c0409031707020c0108010b091806011209120216030308040206030a110c010501 84
    0x45c0301e0301045d001743c1c0c0c41154040003034140306182d503e06846120380d0550074011809640d058004d041100041150041c4856035030000035030451041c00046400c20075608284403210300300f00a0725502003030590900d48100004a0461004a401c1e0320b000741000008003e07824080030408400410203c02d1006400380daa80c5005ea19006442500c401e000901950003103c2000740183d142070640081d60440f001030001331506405200303200985035400000c03a035954480c3e09100040340755018104d00f250000131000038140c481d80c01c90741da660b07000050900039074944004e1014076008200f90484401c111003110524580a1002511350548102060100d04c911001064200c041012703107030a54409000031011437800d01c00441034001c014806030412a50200d40c0080c4a140e005000300c007442800e900c030000110b203002901303040010340d00e064110f00248042010130742c012513854000d6010313118582c0e40d48501c16203002409030401c0b112110000012381c10000041540054100c450f00c1c1c281c3c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 47227306 1250 47226056 47226073
    0x20403050304091407090e01030308041a090c0108100621020906070803160c080324180105100512070302090d02120d18080c01050f1308100b0405070f0c0c03061a03 72
    0x6d80b2404058015480c49a01740d00041c80001d000e0750b0f80326002400750b1515020a0454903000c0c5450000b101c924203640c1210701280c204d540c1008006402280d601441c2d00241e080000c000c000c541414600250f00c0060359900702001c417154100d850300c02018102c0e581d00c0380f4a05021005030320944600c289031040700d170403880b407500c40c039031014407268040c14076481c6444d04107403050024040e8410540301c1040305030541c956070b10003218804440d0760340c01c0080950f1421080254141c0704003144c9003401400c00c4134400c110801540980c0c002000d040040e200e4a003c40865940810098002e400803001d10409080d4440001c04c0308010100d56103100000401403c1d205110446100d03002c141c1d4450144865190b00481c050003c0e4280004e2150500d184a810031001c010142d1005038160040620903d0204c0d540c000e640f54004203403020700581c00c04004c02410040134070645800c0104000c1080c2c10003040140c20320081da00800240800104102a05003503070042c9140b500c00d110b2000b2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 47228556 1250 47227306 47227321
    0x4060c110303070308070e0f0a0f030b010506040807030305130f120506240d110a0306020a0f020102180621040c0501020c030a0b0705070305040e0a0506040605040203040f080d0204030503040914 85
    0x4448480360315641e0b040051b115001709036607203a40b081e02a640215940710810341030312141600e41c0140401c1c080440c0e503e1950916004c1030006030402d030300401d010803090110440c00201700c0c04595061404560b182c607848204a1146842d82000101345880f803400501c1c2c0c042e0710142d00c0d045e800703442660b50130303103481030071410881c0d4019603a6007030810000040070318905621418403560242c000c1801074001203001800c41c00917500200c1d00650302255100e24664844c0640c9500f109500003149411072010211454525100f085417040500050340380039005d89000d4121100407080b06d44901d803c15180c181d2406038103006660051140b0104c140311407030300198036916160042c02c01092a183c61804072226441714100b41e081c0801040001449828000010b120300c00b00100001c150800c901001b0990720030780c0c40300c0e01c11401401400003050400003102c030307040d0f808a4649da0780e1040d004108068095544044c206006c041400150034a56420081f07806013001d0010782ca0307035601d40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 47229806 1250 47228556 47228563
    0x603030e061303020907020f0a060e010c110601031e0609050a111801090b1c0609020f10021b1309030e090a0c0c080c010f1a030106152c0604060c1103 66
    0xd400c80c000640c02c0c1080000d81040d296081d0030845501c103840f0030340d9154010a01d03048500d001124815582d040b0000501ca0a1049400e0901103240511000c241a00c04903551841030002920007548118007030f0050001200c0520303c0d6a01041c02d11004e60b090400b9a210307604100c041d5240321031000c7d5402e02d4900403202100010641892034056420032481c0c4004290080807039030042c2d580315040781011400d0807e1400c1d28807440c80400d0911540c81401b17107403082c1500c894050080c2480400341140c005c03554022588542000c84003020b14400080c007095649004d60b40c03030914184404090687c080c0300201a84c0080d94030600742d45031714040404980c116245d1400080d40001c801001841c2500107040290f0a0350000c900741750800401821548a40c40744102e48503215071721440360400307018580007030043c0d10400c0340c00380341d02002130142210410141c80003401da121000c40404400403541014002600581d01d641d103e490103090403036201c6098400303c1d08403101e884a0718000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 47231056 1250 47229806 47229817
    0x705160f03030e06070204020721050703080609100b19090803040308120c0c1204060e0f01021e071d04030912030c020105071e06020d0c02060c040303050a051209010603030e06 77
    0xca619104145191000c45403a0a07210580da8400400c02c90400986d42d14005014614002c01c2582c0449107148001c0c0c0b0343d085411111014080e041c040400880c0c1c000c0c80d0227510030425201c40545a44000100d089000ca0703410442005a02003060355942e0fa1008040940c440b45880d420001911214615500c3c080c61000a180120800c50354002a1520724103a40000490300901d04040060050f41c0c1003600c0488503900034074000c64200002c9611950300110b24206582001c2c0141c90f2400013910303605a001107001d80c0400d400d042100340001c0040000420603003800c0c02c03107003158440c0075400c1d03402981d040d0001402c4000c00308901c100c000c103203480154140c69000100c1c0c456401941c443c3c119400079524a0500034118810080c160010421144251001a035505414507814110b482d00041c503411980070302d0801148010500c100c4003607070341604000d5140c205403001124240704e1400792402c010302c0002030101c070681c15080402030b20722a8072000c0030000140c0500002d40200d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 47232306 1250 47231056 47231069
    0x80303040b04080f0c0111070b0121032106030f050706090b0a030b0a0e090607120b01170a0204050a06080708011d160311070305070b06010804031218020a0b070516 72
    0xc20700440c000501d0b8100800c00d201d0449451804d010b42c0ca405c4da421030b1070901c40414100c03030000380d4030204a10107143d18094203040c0c008080c01d402480e20408122810a4001c05001c2d91924100e20b031304500340410790544c0030100c1409459282d26211140e0030006400b118107104110002c568940620400c40603580c0640301c89040c0164000c04402034103181900e142c010301001d07808603000c110b51018500c140c0900c001803c060034111001818804491540600540b500e4042c4030207a910800400310f500590020700c4182d00d9100d013080003481144d01c0a580450304d180006071440c1c101e005144194038640300c0050303581c0c0c0d40050780c182c0d03a00480b900c082c6194980000d0103500e8509031844c03103109281740c000741041604440010070743c0f0502007540450360106030315082101c03913115660f1106003840c1202040c205560041c055644e2000000c407000d4881300f14400703d1f0002d40102035144c1e0002d010381c245035511062440d19a0000c401a54640206a122030380d158500d50720700100d819 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 47233556 1250 47232306 47232323
    0x3030702060a090c0308190f1b0f0204060819120503040c030210110d02030c0f0c06030c0c16030b0708070201150915090203180d0801051c02010e04050403020309010908030304 77
    0x3565039444000f07045070304007150304048020010002c229082c0c050051641e50201c081c0340068100e00107420368000f201c40000300144c941d00c3c00888420081001041540030240d01c1c000350281c400500500300d660012580c5106080d110b151081d416031451041c507015880300700702c4840d482000c40b40383c803045402810410b5102c40810050501e00300c2c0d002d040c001ea1401800e0360b208544080d0501c544e03100007d00591001c1022000168107202c10304445960b03000038880300c004540450a540001400003000b42c6020805611002c0140400b1410b15203001c81000070945a10b8803424007802500e0580c001070321440000c0a050051046030404101e1030441c0711060f2a1401440c041c00704c9001c050015410140002000c140900207540100b01d0001d00703004a408901415252140d442d160398100010344004201704e468140c0011800da0030303041c0f1202c02141e03500041e1241210792071816000341c90b0070308210501d5030100103451829000da850310750056944242c40da50303003c01c0c1d6006e040320710f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 47234806 1250 47233556 47233561
    0x1030f030c030c050d031b030e06060607030c0c0b0a0318170c0a0204060806040605100b16060902090f0406060501020a020f040c03110c100b040e030a03050c0f210105030303070206 79
    0x240203000e08003070144a850a0f0301d41d40e900356140c0741042d1000c50001c010944900c45d11109141000340714014503030780e150411031008101034840d139032200501900c0c001c42000542c0401d06110351168110681c0082d42100700030f580d07407201c5017680e100ba011500001e160130210010a85a805060040b03904a0b0826000c07605c0b0301c41142e490b03030111626061354800d0032881030068a4500668000307120b0880a810b25181c1402d201003600c800a2020700c07441d440c01824801c866040c03054415100d06030340000d02203074940c0b4141006104c2803602a6204031000f04000c05490080c861902c9148288418080255540c005907668a07200301c000b5400070101d01c41b10201e007400c2d400581140304604d80825948442c02e1070304180d43c040003450b01c0e5030b0815044a04214818010ac462140c4e040d9070810801084240c002d4807809003c074500704064840c40800d0203000c4080a40340c0c1920354600031555a075010048025081c0c05000001011603054000034a624011040c1e034030560198019210300d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 47236056 1250 47234806 47234813
    0x503010f180b060609030111041d100e04030201020f0c0a020307080106060909050402130903020607020105010501020601030b071d03060112030206130b040f050703150b042d18080a030b01090e01030f 87
    0x590b4010038541d0400c50500045040d90707401d0103105880094002090b84ea0b034100000c07070303a01004031100842d030003078070100b8082140d0440f40c0d0a0f04460071103000384425210f07443d0880c060700c91109590309248001ca04603e128401107800b02d0300510807000c40341c00b199100c800d1400c3e9411803083c40042004141d00708400c501075080654400e10080100f0100941c4a160000b1182040000d40040c0e1049042294072502441814050102400241243c0d8595502e003103141100414000c02c0090001c41c140e40c01e01e035685440300c40c0d4801401c0c3c40306580c643c041c1d40d6241d0301d0410260300600c503071404552040050990700a900341c1044600d03c0303554641e00d6965402c1d100d080c0850700da1003840000404100d000012102032103800d100880d001056504000680f4251b400d40306046004811040d03024100c1d104c094914010b4181c0480d15421004000410003811100500300b0310001400500443c1e250b480402e01c0c0704244c803200132450311000c1d00f0040403424040100082c11411200c0c020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 47237306 1250 47236056 47236073
    0xf01060f020706022e0906140f040c14030f150a060b04141207090c0302120609060d02010f020a08071401050106020313030b060f061804050615030103110102120f040503010f18 77
    0x5404010f095400c05c45e00548094044031444c0400f516095941d81b1101d00b101120601140c10001a601074840c0e801c02c1d4581c0f10420703603e4400c26111680c0307030100f1001501d0074000121800c14840030303160b0995100c00052142c00342110284042c51500201086203480304041e901a507104000010403c01d01105001c001c0c3d00c20082c44c4941e224440c00082d510600b8005d6003002c0b0920703607001d40c541c800420240079034000031b40003d11a039030100c1004030030f441d0340d064090916024a081c089213110210180d00b07103a19100058400d010016403101440b041c586074050034002c80f4002c00050382e80704000c0740c5034003880c9410051521010010800704624031480c5030072820003401000407011050004030603901010050580d00c031080c40075289440d1a04c155540040c0c1501c04039001c0d04480d42101461105000080c000f0140e1403c5005a91003003188031400c40d140c030040c1e075558400380841200c0703411a1280724425820445802000c00c0140070380000484d0103039500080009643e5030852 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 47238556 1250 47237306 47237353
    0x604090c0b031b030108011a120604020112150e0f06040e1905070b04080c15030606090603100b160506060102030f030a0b150417070b070210050d090501050f01060f02070602 76
    0x11400d4921811080500b0000021030081c00c0706c100008511038130110089400c1184203440303124a44016008000480c00702e4025405035092a00f102d400c5004e080b108010850000700e080c5030402c4610110f190440d044480e40500d80c0e10150354411742d140420030041c4e403051080481d140e0032692000c0304566116203240406481380701a0349509880d60401c0351944c22982c086400741d840105c2440103400c0c01a0445200c0c0800c00300c3c01e18501d0300d800414400d11a01b41000c0c0241800400611048409021100500780348103026940b19402e040c603540402800d481501c20b401881d0114100d98000401c81f00b926003000f00700e03815545c0c0c98420728010700c629148142c110364009840f00201d40d914004002415000c00314404c445c003807014440c40d001c1ca903048000345403400c1103942d0160361804402c000c00041072800d00e07a2003088900f47c034003410099a0041840d800c220134011400c080b900000d046e0360035aa02e64007403241c6400200c1e41e503101881f03060050f03004506100d424031801d0303a80c0071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 47239806 1250 47238556 47238571
    0x1090c170c03150a0e0c031207020105120f040512040e04021003090203060106081503030708070215040320090901050403081501051204060b09100b04050418021003050604050604090c0b03 82
    0x4200c407400401003401e049401c00c50003916030200c81040310f0851244504c03001c3c51406001822103028006c0403941c0c41c3c12003a186690303004042000c00c110380c8501c081b241240c804641e43c01039810010b09064164405450854080c05400c0d80c000c40403d411007960100d851310f82d208040e0751030700d4081c042560740701d00c4108201511a10303a074000d41ca040082600030440c83d6600c1c242c910707145e68450001d403038020200d0b100f50804c20144000c203200c40140c2e5022501100c0c20390b00e10960107078500480c49254401420a59401111044511110002c601030f943c180c41c040b180d0381e0303040902800c80c0d0084400502040c0860040b91000c00e00303011500c15003806050051410102000720404002d003118212905038030b5071101d080310f08004a0b60f80e04151200c060308152410b02c40203207010300450042e42c0c0101d82c0c4203c1ca503242c0b080401060040b9401070324413403202e460304400801078002100c0e01390061381403d0124907982028400c00001076003011003140010b090206007200c0e54005030450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 47241056 1250 47239806 47239813
    0x7030f020c010c020d030f0605030a02040e0c030a15050a0504030c0f020303251101080402130c02070302060f13050a050604050105070813060215010602031216140c070f0801090c17 79
    0x5824141c002d2040d809214116001461540c00306034000301034603010310700d21000d6030a2900400803074900080340201d07183e0480d004102d5403034106a0504e03080040380d00a90500c9030f40b04480611104414103450004070300b60520182e42c500009400742c420a482c001c00085001d103068020543e4035494071071043c40107040e00d01d080040703200c0340780e04082c0710201c1c1100c0004a8507241002900c6485801c84942802c02d4541c5141c6900092104003026415030041e64481036102c10040c401d01030b0401440d4001c103081c2c0c0700e0084008000c403d0708140901210040280004a091300c0c0030b24100b41110780041505103031078201401150190440f5804441d0307048184100300f001d030621040d00000c0d1805a0040484400100d2181c2c0c803c1c9041c0e10801c1550000c020050401c4a0680c8031070740000c1190b502036801c0d860010450300030f203280401e0014410046909403502030041358810813507060f60307840b020003511002c1e000c0c02c983d00d1a0f001800d200101400300141500003a8074180a00300344d058 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 47242306 1250 47241056 47241067
    0x70e1e04020a03060e060a120305031315020c0606090103050304090b0102010b1e1503040809150702090106030c03110f0405012a05010f0e0105070801030b13080c01020415080f07030f02 81
    0x410142e8100452060100791607060a01204c040080095404081103c4070b01c80036160501c1060701003400c520140400c100040010001c56408038104141030748a13041d01c41000c0181a403100a40180c040d044003800f48001183d401d140000c0c600f4140c9070080d000c2c5152a00d013601c854000c15030f43e080c042c159501c9500d1140d095803a0708416200d21400300682da01811603c2c10403080ba030741e441e810b40152000740184404605407a00341c4404c01001c1d0303080c814428038201101c0450046030b03002075220a1f41d000128210ba4160809040449651002d01a003440c1c0f040038081da00940001101152090108012561150710506103e000090301c0f000784c0020f4021844030711038805801d88440e03450f00958840780c40c05120310604404031310001c0003582410745c0e0040144106100190810180d00040f400398a00384010080d112340c888040780d41c50441c01e403140c2c041c0d081171007a108c01d126040c541084283c000c41456101c0e0f0f801000310b40c81c5907034124080d0300030030440c08041d440981c24400e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 47243556 1250 47242306 47242309
    0xf0c1709010e061807120804030b04060207080a031d07030201120b060c03070c03020907110d0f02030d09060b090108010204060807030203070315030302150603011112060d0209101d070e1e 82
    0x812400f4503210860b0501c451000b80c405403802c00c190384020b00002144242c5c0c3d02048007c1c0540f030aa0380d2042411404c4c7e2124100305c400380c0501c8402074405c030000640c1c010056016400352182030301181c0900c042c131a130640400d480b0300503840003074040341c003618020200c0682c0d60321010308483c000301400d080094074004145540c1204070122136207014007a0500c15890180e402d550300154a18001e54100600e403c00b94072030000f00d00300000c3c0301111240c814014028001d032000c6032200003040081c0f03187d60919101800010003800d010b040e1700b00c00416128018021601929550348071038945442c2c90004030000c0d80010b041400305941c40c40380eaa14000210108401180240d0042c618040720032040a001c44000d000c0f2442a0300d404122540035039410181c0710764030350741d02c2c0701003c2d43e50324070204522880f084402580070403a40c080083c070142028050040d108401c2182c0455021800c10071002c000617643c14000c5080340700144003d00e014000c5184d0502d041c104519640c0c594030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 47244806 1250 47243556 47243563
    0x603030d0b21071802030618040302010605041503020a090207031b05070f091a0a06080703020d061703041802030f130201030f0c0801170309090c0c031b100f0c1709010e 74
    0x104841003c1c0c114001c100030000c48000c044a107004000380031131540c2060400141004550400c10100a600d440054140b40c001e5000400030f01c0041c00c180700916002601d4074400c5443d0204034803c1300103401c045130501c800d1081c2c07024154551036184c801d51091030188005d600c460400c0790705120380d0030007050000450705070100815107980046801c511014110500c1d620411032180591030081d800c00c1400d45c000c2c0308a412040c90b003070069980f84400101c102501c200d800090003ca00646209501c0b000040200122850f452a91a18050301000c5c4400e0788000d490760000c5002500c049108c00380070301d41c41c61820703105060004026000d05089010364074140303440e0010402c1280104044203080340b00c00c800c8000700c4091072616a404e40020102c44014040c0c4440c0f41020400303440e004030030001c8072908518400200486003170826601c2d0307281d609041c942550741c1007000e505100282809018003200c025102c281c0e805e0802c04070b512002d500180845141d40d20340d044281811800d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 47246056 1250 47244806 47244859
    0x230904050703120201091103030702131109061606051008030306040b12010c08040b0105030d080a0507020a050609010911060301050f040506130905062707210b0f0a060504050603030d0b 81
    0x11380000c00c0321003e41c100203030b41c8440116000d010342c108010010040c0d8482c5508150905c4400700000e45c88215070020406000c0d901105402420000d03803c550000701035800c4103d42d2140a06000c1c5a40d0000d4642c1e10b21140c2c0300d4102e2560040c03020a40c280341940080089980c00341070001c4002600701c0344c5094035202c07821180401e810000b40003c2c4107010204502414051b401000c00802e802001010001d009015544d40c2d80d480c0c02040d016403080c00000340054000341154110708120142500074255848202c44101101096105034101a02900d0481d50014a4612001c0b038500900000d0038001b01a20f61140003052040e41031196441510b0446015100900691408810704103c00100d40360004034030703c50610300c052500c80011610182c2d02a5002520071045100301c8000780c02403004020010350042c0f00304800cac040d458801c07521a000084090011903959030070b0200312881034584e59010b41040002d03800f031018507000300d0081700015203410180000160680662001c1d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 47247306 1250 47246056 47246093
    0x20a0902090310020c03040306050c070b0709230a05090411091302010305060402130b070303060e0c091c11060f0d0606080906010f0e06281e230904050703 68
    0x100e101005401d0030040c98031400f20400e4214174046010440c541d076801140720040415480b00e00140e0302c00e008105030b9082550240340000c41341001d4901418405080c01162440030100b070002d10414400301503803c1c5000090207400001d405d01040c8800d4010041c000c0c2d514100c9079064240f240c50700c0d48a54414411140350300000b010510004041ea2340140145108a00612204501300c0b4210850400c03520480038181e036945940c40c0c10f4024140b954411004964548200480213089400403c9003020448161108403048400483c58035181c9402070480080c07d070240d080c60034200001c11460781058221030800d618210f43d0001e803a540d4200c500003800074030500c00703040010424075014001041c1c04059070b0b400c3c071818810302000101458410b8144490780582515441603500c0d06000300c0059183e110b844403d180050801c00040440d8580d14640000307000e1180c403444a080402c0c24200b6400014203020020780c190060300c1991107010707444000001031811180b14450100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 47248556 1250 47247306 47247311
    0x3130b070201150b0c0d080903030a0b12010504063305060d0b04020310030308010b0a0c022205040507030312110412050c0316030605100302101206050d081209070f03060207050a020a09 81
    0x505c20510309000f582400101400070040c20300c1004a400702c1920b5000b0149100040d11580f5480040e9000000d191019401d51030203013440140080b5070050b0b192030101c101c0072824929651414074649102446d20811a160f0314030074032140c600302c0010120419210700100d0f501500760002012684180e4907a200000e041408100701034100b00c5542c0104028031605040034503804025100000380b00009100340000005004100e176142c5400b07017031111559003000b0301d2405280c400d0b40d52041e0700081c0c0204011000b030340c41c0c0c500e03180580041d12207410801da00f46803400300402c840b0074809404507003a014020421043ea1400c100b501040180400340300002451418640102d842c040d2482d0445c54800384240056141c1c1c20446050032981d00c2d01400760741c45800c902005044540050f5401003800b11084107001644001d4000d07000380c41c0081003c0d407110341507240c0c0c2d101688550756001d81010420008034500b9030103404000c0c0590b0550354104919400201d03100c0c1300b03030459900d055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 47249806 1250 47248556 47248567
    0x11070b04170f19030c080d09030f02011d1504020402040b0a02070611010b18060307090e0a0c090c080103020607081905041401030501140d03020109080d020c0d0503130b070201150b 79
    0x1d50400600e0040c00c40d8a02500d0700304008280704a1007484080081c040c4400c0040c0d417801c1280d010200c560340308049a080010780c9080c90000c021000c6c214250005600708a000c100e4403210450801204400000400f0348481c001103950322100b0080050b43d03c243d080c400020100109002070030032000070740c041d1000340c0c14548054900145060b260b5000d0380341c03045210054a980003202d948140840f01c20490b80e0f80c0700300007803425040d9005214074906040620142c0c4c0c90002c0d450941ca0700c900d818184480d1100304c0c0340c3c1240c1800618078002084000100054140900181131071400b61803590301e40f41c0700c042c01c901040c4220b02000f000801c0020100828422102244000d400919090000303500d4055800301541c0541d0100b486808000d0790b400803d4001d5028654080d8030680031525961101c00b00700082d0001c0d282070700386018001d8924081840f40007100d214001800024500c107440b500d6105074000010300c104c0940d980e03904c2d00e420880c4801c050030010a008035486070b468 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 47251056 1250 47249806 47249849
    0x601030b1206070c0b180601060e1309060c0e090f070503040515100504050c0c070504021308160f0e01060f08060a05090f0103030f05160b09011d0102030108060f06060a11070b04 78
    0x5d48001e00c40a0900d40d10444510180c00c0440e800c0c0c1100c3e800d10b00001024903000008558032721585044071001d2601125004000d00d031b4008408000301e6448101c0d86000074801d00201c44402c4131200340c540342034000141060f01620207140c103d4024400c8520100c1c01e80310903142c03400182c525445100003050200f11034030345809002c1d4010643c0c4002801d25050b0700c0b1a995a8040b4006c8034802e5402282109c0d0003034400c03e03003a0040903200120f40c803c2c0700620403840b0a1900f4002c0c140054541003000c9940d1210680d000d0407035501c3d64900748032580d40c1c10b0480d0b000310040d003041e60052a07d44006800d5032985200340c084d188480010383d00d541345240c0505800e6034071103500113102003800000d540b44580742d44000784641205003a58030380e58030700050303004040400a2030002c03c100c42d907148034800e0550242d0305a561078021180b4584444883c0c540c80300080300c95560103d001c000ea09072661044800381e02800041040341c001da80c48551980040d003041d040110181340d10101c10008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 47252306 1250 47251056 47251073
    0x20c0a0b130b0c1c020702100e04150b0702030d02010e030d0b06160303020310060f0516050708010e0d030b01090e0a090203010f050a0b150702011413030213020a02060a140601030b1206070c 83
    0xa01e20394111b03d80840e560208a130540c2090104051204c100003218050b03c0c0ca407c419400e03407120008043c0c03a0703113414a0707035030507003150300168081c0c0f1076050450b1529005200d05041070078020000d504041c4c600882401910090f01542d410072410b101c507040c0c8100040740c000b000e034401d03140986c0307070300d04030350007418440159001004100c089420f41203070342d410104507a00c91f8852244100d59040740d003811458458130758003078200c0c2d40c03034040030014103c000714000700415580d64091018500201c01101d51551600030030b980d03c045040440c40394039460b4090f4442d64070140c00464002d098540700c0781106c00c01c40780c503103226441d900030503058a00361181a800b05a901c03039186c1007441ea03800003400e082c80c042085001c01e20006d034180342c002c10b181d400300040da401071844080704045895000690420a0340401520403100421640822070042000710b04c821003e180041c1d81d0b080046003d041711075141a0421520040401c41103800c0c4240c61003078801d515003140e094604d00d412480d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 47253556 1250 47252306 47252347
    0x7120306061b020109140a081b03120f030105010f1b06020405030114040b06010302030402031603030207030b01060c020d0b1902040306020a09080a1a10080a0b010513020c0a0b130b0c 80
    0x2101d8203841c4030b071001070b03810406800580700441008000c1501050224044020603040710760310307100d00600301391043c01081c0c00c0c0c41096001c1c2d003503450085c250b1661a0a07800b0f82205140102814401489103520466040d04000654078050200d4054407006800d007644a4000b5103400744c0003d010301244c182409143c5015a4080031034a25141c00e40b164020440b001e050f50f41015000000b003015580c0420001785100e030100c0d4045103090f07a07441c5c0655100080d2100b26006400c0c4400000c1140c019022034800680192003412205115a03980076071b114010318000d4190340f1101d0340c1d2380404062003c0c00c091485100016594078001001401d00c034243c0d40700007440d620141d18000002d019860250101400503a64211034450200a200030100d0346c221404034454118624184040d40341c106040f9541900c0107500344011440140903845030500841082d40142c3c20100003610907031078182d1000c40c80707003845003664103a0b442d0070392007000780e42180001c0070100b020200c3c601380500c80030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 47254806 1250 47253556 47253587
    0x2114010f0807030b040605090703120206040b060d05150408132c0c180a1d0609091204060516050703030908060106030204050f04020a031523030607081b0712030606 72
    0x74603a491640c84c3d5501d090003c000400700d944500c0800c10341e443c1088400301841c0c3c4047e40321041d0f00e001c40020b42d1500201c0d410b94001c0320314004100c0c00c3c141070f4401e20509070460080c1800040012811602e420080c00840c1c00441c10030028000d8104429090050302c00d200c43c41881071140140304050380031002030114210000e009202041501c601142d10040200c0c55002c1501050713400900100210350001c0101c114406991250400041000d4401c1000300d4510f041510fa03082e0301c2d07580d114807164070050154100720034003030705000e0000382c14010300c0c403154015005501d030341c2e180c103080c1580d208030040b0b041780c4e01c18061203009100150141c4032a00d011810140b40000040102d061041d500d4000d50340021110310191103a04540151549400385a040d1036968081071410865100300c909081c040f1010065245804600c040c0905000e0361524aa0340300c41c07590f0f4600c0844c02e104540d025400b00441c40020b0b140c8082c1040704c02481d2030010f142032400e1405068403000c0300006 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 47256056 1250 47254806 47254813
    0x70524071d2413090e0607140c01020a030f0f0501030503160512040909200105040909060f090506060a05010804080a0305100e1e010801020901020d0e120601030807020f030a050c012114010f08 84
    0x85d0403280000a070550310030700f20b241800d551022500c021540d0300ca02d00d94040c15500002d28601d0075034040d00080c0305100d0803c0304101035480c01c541b2100302e400c02c0c04001c003640c00800030a00440d10418052201c035018200707803038040d030440b00b80b00308503802540591003507170302c50354070500740a14640c440c0070303c0600880c1c10060f1404c50000170420703c203600030f031032810355100c10107010b00c56036034400c0e0a150007207d4104281e11042c10016070381d4008550302441200440000705082d4440d08080740a00d0344001103070b080a581d654150090000280b0b03c3e50143c40001001460540b0059801e02618213505802c0207010100054100b07640140c100c80c020343c0c0100314507140c5907070000da40c008102e41c926040d03403603000c01e100103484803c0d1101144094880c100011081c064aa0b00405da241d100311100140018030030189910b0ba02e403040054100c6c1c0044138514030340c0d40600c00c09806028140d07081041110b40b034801d10200d030005640c24030080c20800c018481c0d01c500041400182549a006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 47257306 1250 47256056 47256071
    0x2c0604020a060914040f0b030f0a061109010c11060c0307120201060e0103150e0f0d0504090c0309050604080904090206030406090c061817030d02070524071d241309 72
    0x2e000c681e04e00003401d5005d11390b00c0c20300c500c8600055002040b154001011791b03255151004401d640d030032859805940c268544074810b00340710340e0b0800300c3d04410410384035103007002c01d6501d654241c8007000c810182c000500b00800e900c00c4000384000c009503446050003a840380d072a000028219095038005800d1500450b00500204114410a001580341c112010400711070b0840001c0c140000c1c1d40b0100315520428000c10303801c68028000c0c0050b201c0c0f2100030441100e007002c08906460382e80d04003401c00e400c041c1c08140415941d00040030b0343c03980948041003020495010600740c0d80111410398230280e135902d920b41040501040d580052000d440c150b000403c0b50808090703062040e01c96041e0a120b21900b075850102c00748162000c030801c0c00401c54403a056410115200d07110750500522008202146200ca40101031202d400b4540565402c90005100b02c0010b4096070b54144070707a030251351080758410b10ba440d41d00c59a01103910103411612000034070f5080d40710440c10307006041c3c401d0070441c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 47258556 1250 47257306 47257319
    0x910031103070e0414070e07050703030b1e10091206020301050405060d0503030114010c0606060e0a08030c120a05070b0103061e0b030604030e0a08010f05071403040201122c0604020a0609 82
    0x80c0903404c1600300c001c44000040a01500d49000426406100c040e0180e0042080c1035801c08045c00781c81e070003500d051005850b0201086044a9801c6402421040c02e60010000342000c000041740c0700164144241910344425910090309141d160880341c2e81d03000130050195043c0f60117071941104c1b065074007019210180d41e07001c0d1203010501549420b41c0b5000961701340380e031243c000c562b900d5030404410016030b511000020480c601d5041d043d4099050f000001907006c50000c103c401403818540030703007c0c0081d05003001c00140e1201e0b51580c101f0106010000200b9956003402c1d00a42c81202c000604007081c40d9081030450015030480a8107161003002c01c903940780480c1c260ba1055061600c03810700000100080c50b21a8103400080c429880c002820a02d102c4030780c0024094030072500c4110410040c80c842c0718035840201d400170b0002d260014290420111500100034019000f6001c03001c40e04803d00d032603200a141c101c00070b20f42e03201074180415418041c042d100509018070701004050b08007503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 47259806 1250 47258556 47258579
    0x903090e10050607060e1608030414040605030f0609010606030209090f0604180b04030e06030411040b041b030b0a080a02030712080d0e0303040201030f05280605091003110307 77
    0x419094a400d5100000d02100704440d110005010b0080101c0d880d60580c0c20070343c1c01082095008111031003904800405400307680c1c2c1510444005034000e41c50242001d9100e01c00790003016900d60402d40320500898165418440d180316519048028a21450415052130a581c143d038842000d1601c100158003c41d210a07840d903602001c00c541900c100d45231310b0003040080400c0d44050804513103043c030a4003080000458a401680070365908103030040c03550208406484242c0b0b00506c44954502410458241604081c404400007800003400300741420f0b0300d404406501d01c1038030001c1c0d5a045d0204843ca072107a1110302811102c1c0041084510030f80c0801d070380304060b000b228200c12080d01c440040107840c4040750011181c00c1028448680b01c001c00c103640350402c2d03600b00c1c0070a00781007c02c2426851413068034131644420400c13800020f1940d4800719a5008450003140b896220b02011a560f2500011180940d00e620a803034040e619500f031007900005c0d200710080c401d81004404019600041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 47261056 1250 47259806 47259809
    0xe1f0905040c0f2f07030606061704060b010c0c060f031104030201090e0a0e0304030602030105100c0302210705011a0102101103070e2e020d03090c0b0a090f03060204051201090309 79
    0xa0810705042680c1104110008950941c038814042d03c2014136030422074017180100850344a00d40920920b500c0d8070064680c455210940c0c101c0080100000300452816044002c40047c1810b201d10104030700e840e07188240c241904902c000c10160001c40e1603a0fa4148100c7d2081003c103c84503050501316800249802d20034071540d40443d0f100800325003e040d10b030344003071980c5030803808030703a69036560780780c4078010b504248180d03031180b072a64a8180f16207025450400585506901818229030070340f007258035a9101c5400740e01d804000744030300c0001030740074452502c511454005000085880c003000a01e48200101001405420011700030750311450103081d00c0c0c024510b82448402428400e0108500c0f107485441d000c4529110002c01c140035010101c200241c1c000356007558440c40c01190160103035010f01200808000d000103080000304c26103006440310500c1ca24200d50240c1d980c1443c4400510141c100792a00396002504021500d0499023030000e180824000340407e02190301c0c060b2002e6020b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 47262306 1250 47261056 47261087
    0xc180c0304170f120a060b030412050f0f040f080705010504030302030a0e0402070501050f0a0506040902030c04090f05070303020d02150609070e030316060605030d0806030316030e1f0905040c 84
    0x22007041c19072201c250040c0c860300c5034030f00850354480c815006400c01400050340c05da618280f9190b000314041343c6a804881c03003a90030580020740c0c0405414200e503564050303040c00740554014410351625000c0c0100810051000702041c1d0282c906120245c0d041c07444942c089814807008010400009401000303841c591081030920118001042011501920400710001d1480d46420700b00041e041e080d4081c0c60140803c00c00801c855a41d5000b0300c411500c01c1a03010790b042e400600d040c141c6141681242c83c0d06c0d807040c240340c5c2840b030055440c2c07442d02220b60001c0380540c11992400c5445a4100074039105041000000700d100d04040c0c0100700304c0d08000e0010801c0007122461141591002c10440d080c152103c100154411b0240c1410030041000e40505440b0303006450502801c14401e90005000b80c00040c0594a010158202c910541305115422014000003200309402a940c004041e000d01d401108100c09446030040000d080c80d10a0f041203100e140707088030742000f00ba845120b00740280706 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 47263556 1250 47262306 47262323
    0x60203090c06272e08060f0a050d11060a02061f061b020a2607091407080a0906020a030b0906100203160303060b030108030408100902090c030a0902120c180c0304 71
    0x2240080340300c51409103407907000c0d800d651100c2c080640074410b0200c0d1302d21865070380700c8858844404000d050945d03408241e81c0018113410600151821801c062040391041100382861805500800e080e60407030825000960800010030134030350040d41c030a6269a01074120603c2c8540ec082c005810f2807906001c2206100354103148108648078030300c1c24000b500100701d459401001c0304d03005814841c0ca11035081c2180c041c114000815007840e004804034000300301840d1035a952948400c490140d4000c002000650702e82c002ca0b40400c22901c0284100d02c0507540105076120701500384004001d0207001789001e40200b041c07060620394003000340d84440c1c4801d005050440380301c0c2012009081c40d50456000000c00100003d44048000010411140102d040d2220201101800b50860301440e00c01394111341c1580000c0c0d2440100b03c021079018014420000310f40003141c010903000c4040038007144081d8011900040b840c549225031003140c000c24801c07a0713400e20f40015005414000540000c0c4400d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 47264806 1250 47263556 47263627
    0xc0307020321010501020d081b0a02070902030a0b1203070f030e0118080a020312040605040504090201090b0d0b03061b07060504030c12022406061210050409060203090c06 75
    0x900c01d0040b01c948016481c240c4803180351003100c1151902e02031098a0141c802d90000382070b010700803440e43e80302e070742040c081d10070032100d001520365254060b0318281c0c114027503054003140c41d642620207140118902c020004d4a0a035050510594a901060300c0c1100e900521049001401003040454010f0f8103150104144500c180141e50303910040c80c0c074281c5000e46541c0070074410000215405100d00890443c0d13141100051b03200403511481c080c0c8400540e08000501180c1030540095421a10625110070700e940c1d51683c282160b00529241070361140c44252140d0203190800c0541d3f04100200541440399000e03607204640b40c1f1134000d00800084c0c8800c001400c9c913006190400b6000d801030701e06140c601d807a5600940305d001100129941071480196844081c0100b0b4999104150140110782707080600440051070140007071001008084845010650741c445011f03803280540b0442000d6242d003410f060150800c1416400b00b801400c0910100140c0c462140b4150340b1034110045000101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 47266056 1250 47264806 47264821
    0x20102040503010c11340602060f0f0603150709030c151103040501020703062f0c0105090c0a1214030a180b120c0703021203070e0f011403010b0903010912020a030f03020f030c03 78
    0x20803161b00240e6200401e2000207081d40c001c1006440b40d441c2900104180d0341d143d043ea075103034105448d03064165100c0300c042c0704a480030034440c50b0044150306010000035920f548241581c141074100e4075440345007844030754042e5040407140d2200c0307074094091802c0c207062000007580d030400ea2001034001030b1145181210580780010300c042144d5a01548201d9181c1206803400c103604c950895a0300d0341c6000d000818000c0c011a81c00c40d00d0038020510110307a0f141a00144202c0780d03c070303010340d1340e40c03900303410075060030010801801c0c44000798946410403d002084880c0001c00c0b5070001e0448141000300540080e01c2c821015880351007086925101c5030b090508070b103405960b5030807000c159000010301003090313000f8491480c01c0b80111103803000351040c400111440900c6400f280310742072060005000d00f1620b80c001d07001400c0050000101d0541c161250000d1417000d25850000d6000440307000181503100400205100050a0a42c03800940c003043c1d034001d20005081c2c003003941c008400314402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 47267306 1250 47266056 47266123
    0x30903050d021e040905010303081602070303030b0301020d0c09080d090503030405040c110a0602040f060c05100203090a05120c0f030403050703031d130e06060102010902010e090c1207020102040503010c11 90
    0x525007035100c2519107451740c038404020042808244d002c208800300040f1068445280c0e8030000300b03140d0140010a1543d80c055015021801406505540034094810070800320b1180d50b5521000e170341e82079441490b00440714105042c6020481c1049489035041c81552000400c5908840b4165000210307180340e04c41c00c54064110b606112800d0159400d00000d000303558000e0410394105000000703219660704000c3c1c0b900d54105174000c0c20f0760012031286448020b181d011f03542c0104030109a9120b0441c0382e403410704140d00701001d8a091080170400415101c5c040003420101c0102c40001c43c540b5040d80c03030f01035407084944001070400c82c850750340d103a184441c0810041c2140d0050150004403c01c0210900a840c13504000c034154400c10001441d10343c814046c44803019011f869110f1041c0f5400203001c4c210500a084403003807102000031a854001c0b03060124818081980010380355820003003098207450136800c075281000520510080010700110300c412a54480b51000c40d0300b07031006982e000c01e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 47268556 1250 47267306 47267347
    0x70b09040e03130303020d0507020d03030902030705030709050a0605030604150e010b04020f070302010507020c0114031302060705030a03060b030106122f070b0c040e27010501030609030f030903050d02 88
    0x5180400303e20f80303890a0b0800224802d0303d2194095070301303d806240048510b4006c1000c007a51018010410401080c02a84207403003c0b4005025580415100c5010038a050010b5000003402e907a03070001c03c22080d00b103205580141c04120003078102410107407122011045002c002000c5160345000116607140250b00c1602040c00c05001591500e10303141141c140e68101102c1600554207101c00100d03070500c00b042c0c0c1c0342c000005071a00084481703102035001e040e8100426010500000744210005030b551980a0306141703103e6030096640d500d000d41d004086c3c5141e54401c02c03d4410520040c011140c100080541e000c01c07096001800300b20821884a0b05215890082400d1080402442841c00d03090004c11515009012a003000c2c1ca40c0c5080c002181f00e81d1280c00080000700c0c0c04901102e4564000900a14070028600248813518824078210b40081e80121561544c404920042580250310880e05d02d0031800e0401901000380c802419900c00c5048880348503a000410a81414541c02d01d000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 47269806 1250 47268556 47268581
    0x60c0309060a030608010504030e040c031b050705010f060308070c14030a08030a15080d0906050301050f0409050703080c010204030c1d060108071407081b030f07020d02040219091403030903070b0904 87
    0x3c122304050401401a0300130f81070080c00703076007890341840205009000e03580000000b0f0895050802111108030349a421402c2d0840b203070b54075510340920021050268a0140d4003a41007155640c80034030700440302040d00e030302c80210800c1111a407141e03a6004204103d0550f0003220a41e9255507488080000f04480b000220320490f4442d80400c0320302c4001034110001c02c0a403104801661031340402d0340e50340000d115203540400f480301c08a500d420300e50404801644581c003140c000d144c0341c3c0c0c2e13540703c0c41e00304400d041d9a030380d030108081041c03100b0a90340b10010540d81030040301140d4000b0750324000e080c00509660502c40300d4000b041049105204116296180b007d06a40f2100d40c0d06e0034001c0740d8840b002c80041d500f000d40059120040100484a160a0400708a85002e940780d00303100310120f40d024107a0348540c2c02d1001c500c20a40c40381505141410703a5581c610002e00703140f0b503402405900d07640c1034000c1c0e00520203106241ca001400b00c1c283c50202100c292103000b03a80c0090058081056910b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 47271056 1250 47269806 47269811
    0x5030c090d03110c030705030307060e031303110a060306050603182406190506030403030c020115080102032a09040e1204030c0e0906040816060608010c050702040605060c0309060a03060801 83
    0x20003031643c0314200c408400d0341d000a41e4000c001c41000c15580707145500402c0c0d45a001000540e00241c02c9601035007980a075001a40d0a1030706011900040d90b88581c01a26480d0800341145c9191402c01030342005001c060030100629070801e400708980d4080140b60b484000c601c0d1203d083c0d4440304101015130310591800c0c03016245441a1210700c101c03400e0722010b001d030382401102e1840c1c81032406500c05659020380f9803811581c0d03544040300988400b600c4070095560314080803c490034142060750181080310000340e42c0b800d00010604c944d4404200441e40944882d007102107845207082240d40c540002c0714045483c41000a8490409215801d08096203000040000400868075504da0403507010200d814426039418401540b1801c04890052154604014540e035200200355a111101c0c0118000581c46071194031150840341c52012050100f10003080300d008510302406208007034036003901c85a0030001c002c0d10403a543c1c0580c286281c0b040d0344c04541c2c1c07031030244030b0b5100d00000c150105c002d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 47272306 1250 47271056 47271079
    0x901020c03010f090c0806070503131406010306061d090c040b0a090203011202010801090b011715031e0c0109030c09020a0507050a0602071703060901030201050c0304090e01051608010f0605030c09 86
    0x9000707024403442112030b400e051750f000075101000710307200744601516120310f0314503a648820314551200c9803504560859040001c421903041c2040000d0195224035000036a150a040303512803603501040d010340000c10600100a051280402c1d17114400304203890110703540348010700046602606800c40443d1310320100000030301d01c45800304500d20320b000381c0340e850440c6d88030280e1400740c5e119003c1c49030210340800c01d8920315040d407280007640012072140071850501301100083c10414001040b0308010080c3c0382804500b4000c2c008180b261800b404c04411951469680012203190b030722405040e42c1d408206501e038103005104965890754000145d840411151a1640085d00104000e0304c006850b0b0305030a070b22031042411640920401010021542e1942e8011200740d03108180d0080540420302c07001458941c60700030140c4401900c000800e09203452920039040c070740803a104004111500380104030494480485006440140c506a9560741d26071410845900c640140c25400c02102620b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 47273556 1250 47272306 47272331
    0x4030f11150a0c09081204150311030f010303020c0a050a0e0901090503070b0901060e01140d0201020111070c051f080c070201181d0603030c0d03050402180f10091107080901020c0301 80
    0x80900b0300300f030075100e44202c1c0e519a492981e40304002c00c121803a400040100344840014540e28682d20141ca2401140c3c41056841c207070a160001d03661480214003410040c8101601800080b503c40c100baa07a00051910f40000507906154500c0742101d800c5040c0301060b0203003070a4104561945c0c021741100d0b074494680c130345491400303011030301c804131940b07403443c0480c8111440760500e04076070421910140b28a0840d0412415122102040381559640c110f107940800b00540509a07090040d401c04046030724010070700440d400d95001511840800101d44030145412114043e084002d01e00c159448020a20040c0c904038080c4418420050b034101000400301900b03900c0a41c1440d0342c840551803502d980041c580e807400b968401001e1038000c5508000c40c41c1c440c4d4041035000d8002080704047c49410941e0062080013580c684c65030340249020001400506103069000304404641080035190820303501309507006810703000f8400200050742e095030381e100304424081c4d190018000c1050313030008603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 47274806 1250 47273556 47273561
    0x3010b0d03080714030403090302011b140f15040c0303080c1216020d020a051b01050d02040e04021002070e04080c030d0e01060f050405010308040611070803040305011409010504030f11150a 83
    0x80f1030400040c00000001d601d20002c60540380143d9050320349515860940e801583c082d0f010101c2c2003921000081880042404242c2100d11400000d024111511080090506042d208580c0c00441009903041c00002103840c00700000700da0b050315044080c4d444901076240c542c880c0c8800ca8140f41503000500403944410a9a030301046865000c60340c0d2403175005810790b20703518011009040c07a0008020445881501c0302c4201c0414414500b061822110b04c503804200d03001904146411f40c2200204000c5040804608031a401ea900062040620301221041003413030007003004003800b0000c01d44c0d80040b101041610b008a610000900030b485d41c00c5c03104d44c028880d03841489540b0003119000680b40c01c05120b00f6041e60b41140e421032809007083d405550301c11102c42da000c900c0c0700f09800015815030900180c00910322490010030311381d019505450040d2000380141c8120b9140400340000260814080c2503202c0580c03c2003004001145403c2c9d00b040440800341c104060740008100c8942c00c5507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 47276056 1250 47274806 47274811
    0x1020708041418070e040204030203030d090b0f010f060e01050c0318010e040c02150601020307050a060510090c0509090901020c010e070806010b040e07050f090a0b070506060301020a0e0f03010b0d0308 88
    0x30003103104404460070000501d01850f80a254041c001c0d02240c0801d120307014541e00c00e103010307202500d000d036a070f07001c280745034040005010303460b5844050310204078441007038a410450300b050400b00b079410010751010800703003849803a0038440001d005601a0340610700b911000704d40403003034944034888000c108641c0c610742851203000071002c0340c50040b14a45441000340c03160040d0b0040101d0202d030194030f012070b1005040316041d448203001401c00030300c007080989200d134400e020108050624480c422035261050300815080340c10501c0030112960b00174143c4c2c50701c0346d044071014447e88076000954020322481d80c2c0c285195003015030b81d6030300707000003d190405c0f50800002c031095a0380ea943d43c102e0f50f000324051140302d42a4100401c21962040014044090209200c249841d880000240d2114090f52000601a00200d200c2017880300070301130541d11440503002540703001e08000b4001c0c181100c15100d41d2154940c00a20380180d2025880000d20603000b030040700d40c2910701d080203494180d04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 47277306 1250 47276056 47276069
    0x20705010c110105150d0c0302041e05011d0a0504060603060e0c0f03030703021203072d0e0d03020d030e01090b0408071401090b0703020c1606030c111902041d0102070804 75
    0x50702040b5103202c005115041c0b05800d2101e40140d644a85010420f041c00b20030b1080d2854081243c0100c0503030745611901c0300100c041030780c002d218056840e181c0c090714016806600300300703910303603500720340c10321a0300c0280d400322940f007000680d5600c5140000c020182030308041c0104d880d0100181801c0b60004010042a070f0840d070802c42480c2d050304042d52403040e40380080060f0448121546180007580145802001e141040c43c21810807480342c401e140c492504100108680c0c1c802068050341044044500010507200810b0b01445510043d40d0b400c0c861480c0410580c0d0f1b841c3c0034a21003002c0d0b0201d0135041d401091980d543c10642030290b20740d00041b07025207440d2100300e103502241e241403082011155128810489654500e0010340094100c000100101d018500c2c1f00038555001540090141000f030720005005014107500420030702d903207818041d442d44014490a5101007810010803c140c1c1202c1c0440d61030034444524002d1291240b407c1019800801c005003001148805041030b100d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 47278556 1250 47277306 47277317
    0x1d0601090b040b06070609020d15090201080f090d0e0d02130203060906060a022a0405130c08030a050403110109030b04060509100c051c0605030a05060a0c0503010b0a08100306020705010c 82
    0xe8010030002261640f040640e0b200c101044030000080c038940020b406180014020010f145240d1109070301042c2c04110030b0f80950303882d804101190b0304103118a402005820007428185080d06145a032221000100401d004019450039000d81d14140b10b8118564042c10041202c0703004401c041c01380d0010344445215090100029066040007016904c2200d041d50041900c030441e0070186120000340100420b44580c2c054240c5500c2d100c602070130780500c540086c4084a01c98504007508200c0d000d41007403030705401c01c10407280443c1d449000d440030740e60810070310000c4001c520b0050700d201c58282e000800d00e000714800c00040c400c1c1070380101c2c41540f2400540d00c4c0c16045000003004c031070140c160200481d00900c0503643c1ca10201030b011003e2040b1b1320b000034150f80c4650000b85440d00c40030040b581c90340072000f017040e41c204038001e20540c48654207001d415941131810026640c001c44054008008031030340050060401090040c0065421800455555100d07040540c080c203d0344042001040d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 47279806 1250 47278556 47278571
    0x4200303040b031915090b0103110304050a05060903040f0b030901020d0e0d0e030d17060a050307121a0603070611192108010311040c02010b04150302090c04080d030c031d060109 78
    0x903003809140c0030360f0000b100c0420901d013880006c000030100d03c58407074101030352050300412002d031090041d805079005030004c00481045280407071030003800910042443e001030208000c00b00e4011302103020746038608c0b00035480c2c0c0c2d01e2041c854024000d80110002490520702c20714260b003004658107180560316a038603e0585100303014103694505d400000b40000b42030019003429006044241c50f0011001000000f41aa588000901d0481e054100a90710626a10365408204100e8600340c4002d26994460b015850a0b40019844078041e2280000744102e59608800781041030000c0d00b03001c3c0c4516000800442c0d1403d0100d19080060700c40000d0b07600c0c916503100e006001d151024100c80c0d1142c0c0d62500c00180d0380c28000a0503920a51209641d00c0d00300050b42030f80c076030250700300c00143c4802046440740f0390b004105095201910802c81290200f105000c20240400e600720700701c0c1182804510000c520104900030400d40303081455012080840310440c0708003146545c1240c5c02000140041c4c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 47281056 1250 47279806 47279851
    0x4050d030212070c0e0c07081804090f0b010612090f020607030c05070b0901030507231806030117010b010f020d05130302030f0f16240905060d0606030c0503040b04200303040b03 78
    0x7c2c030907224090581c0c2424003180c0b80044074050401c007800000b03031001c02c2c10760050792110005854114200c034040c0c0500c0c018072130300fa44607403030b002c0c90701c07030300b201804140794540324001e840129000190050f08002041d0003414024071107011819409004c4039030381580c0c2c18007040250420711050380002e083c0000300350710510504031403440c01c48000502d200342c00462584209544441042245034180010440042d91070030003440c0241403c031141307800342c1122000305007120f0b008001c07507050115200060030415400038500e10841c403103080460b41c400034940503500d07100541d80005e50500c11b00d94102d030a81c078003107480d520310b0b1240001c5626400e00160f100022101500400108070705a2214003555031482c0c03e0500d801e542d13401c02d0f01d8629100c101244d402d5200100307201c981610303958104100e552501c44c04000c0400d600d06075083d81082d0340c1d8401845009031024000c0511408180440c0c02504403c02000a00904880c0d07947d607154286129030b041141c5098454403254400e0840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 47282306 1250 47281056 47281081
    0x915070615050306060f04113c071b21021003060b0901140d06030302071d010308070b0417031009150602030307081308040905010519050604050d030212070c0e 70
    0x141e60300100648601d0b035854090106c01d4a0308440e155010341c0312400402450701f1400141441e4504940300c4524074616446c650444042903061286800b003000c000d00145da41c5c50540350129070010601114284407c00440300c5001900818070100c5d80809600c100c001b04079118074694030a85031002d06e040d200300c050301260141e10481800440801c0048800d41c4200d00d45040300301c04614080c00c0c016414221011200250022070150344851800d114410702c1485400c00ac640308074030044503606580d9049828000c0180052240e070150b00464204000e0400b4a0064140b40c0250384d101d1070f1040c0c807400311640318803d0f9040d01d8a890a541c030f08100562120040d5003054008600c1c0d9190007804860b194002403480c03441c0c0510421980008180070018401052003040c08140c1c3d506210411425000102c07100a020040d4001045541c8070748003960f04440003100e00c08680825410140d00304810489200c0c64464001031060800240c449002c00342c503400354000c43e0a50307520007807400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 47283556 1250 47282306 47282309
    0x180603030503010b0903150108060f0a0c05090d02040b09151302070506060111070b0304030302040306050603010c0f030c020c06030a15170c04110405100801080c04180b0403050915070615 82
    0x2800800051007808280303001490380000250481d00e1f003920059219503084401e03009803109400010522000c111691506500b18130a40c02c108601c860030007004d0001d1107510440c600810045586409540d5260b00c0001c02c0680640604254030b4012142c0c2e012026210b0000c1c820f159062100d03c080d03601d0320a480d030a59003c0c1c02030a2035180c00d4015100410070b12401c84852054400108000c4c9075840a503010364072030386006d030f1200d0862500c1c40650780002c101078000d1b8540413000c40300c0d99210f0040c01c1c40182c030742070000b508100040100c1c100040034410700c1e00300c50004103100344049a50b05c5000b1140e550319900c2480c684a0050032613540031890071a00550000960030300b40d00d00383c2e2050003000140c00440307250a68030000705240c0960a6081d5011503d5100100003070320f4203014000b030f90030003294100040b0704000c0180509512044029140b5600c5100241c20140594100d03800d40c080201080500d891b1541c0305885035104000448119040081007000714948121800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 47284806 1250 47283556 47283563
    0x602070b03040f050714030118020d0b0c13060e03011103040209041212090303020c070e010503070b0d0b0303070506102903070c020402031602060c0c031603140d06180603 75
    0x21195140c100110401e80000c1c1069801148a5003200c00141003004050000c000100e1110411800c0d10201400c4031001d04044c3e0030000b07600342000040e6030704484420300030b81c0103451030096180c0c10795a090b54040c02c40055a030142c1480041101600090700d0130307103500124001d01042483d5501c2d040180402d0781d0084d00408a4000b140001d0741018800442d0030880c602007640b11801c1d0420020707141041c806a0101e5400280c0202104d810b102000103040840a60f4025501d45000300e03650310158400d040c0c001201085055904105070044a500c0900500b12501d45c0e55505050761101d009440b101001c0038400c10005031305488804049014070b030000d003082c2c119078082010490b5480100b003034040118030406500140d40700c1c0701841c0107085000c40c07003000c084440c0010340390200141000c682d00301e003030016418406002003100c0b000c0300822801d0340c02005510301500da4184410410150a4011031604140905a40000202e17040c2d070000700003010441c41e40b01c0403140c4038000175 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 47286056 1250 47284806 47284813
    0xd0609020a2c03060a020304050c0a03150e0c0a08070e0f0c180f0409080a1407110409020a03050106180c0f0f08130605040803010618060804020f0a08060906040c06090602 75
    0xc00140b8803089407090b01c14070006000003a44004000281001c0b41124520b03081a03000c010b10083c403e08200c041074000d4141c407940811421925070440c401d403604c10b4411407546a80b4401b40282c414810f8441c0b181c0041c000e00b4809407141c240c207807507105600882c506a0000300001c3e0b84607007280441c501a40444016500e042418016005480c07201c45000b60488041004a0200e40f1207100d4404014020103809071203103030510005044e1040401d0001c16040b091004501041c035250412130001002c031800078155446102280d080c900c0c59101030615480c0c248000344002d050034400b134080030b600300c040003c080b0300350081c1e540103400a403030030000d03911a80c04d21a150007203180a8010f01607a00e190000b001c160327103031380540340e080b1000c407000c031008401004250342115681a144060034401100302c0d0802600414a42c0003d002901c61103022041410640f5442d400502501020042c0c0305c00f443c0c03840d101d5a5070a002da50840d2009415400011920311841c021801d40b40740d980903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 47287306 1250 47286056 47286077
    0x70206040b190b0303031005090106020c010e0f0a03080a1d06030106020a0b09030c0a0c050405060603010506030c03070302070c0602010c0917030a03020f09180406050f071707030603170d0609020a 86
    0x7004148000c0080192043c0d81c3d0b2000e01440d0740c00300081c62059083c460b1720b59445041405025211768103a211409640c8100021000c507a006a4115488281503030008900d07400d80700084c8000e003480d44060180c8000180b12428240d002c01d00b401041c0340d003504011f40d4000c6000307000c0c1610092040070300503080801d50100090340009015007009006040b0703424041c3c3d178540241030140300c5008883c16843e01c02c003040785080c00d01409900c841c089a0f89401c66260502140042c0300060403005400e80000004500902036415a141150400406103456444a0010b4028010b00002c000801c1003480005111030f02ca04040d034000702c11201840c1072501c600030540194110b4210008511002d201c080ea180d1203500c140141d0a00180c1680003e00f0103040c0001103481c060030501200110740c00304200c03682c0010310b900002c400d00110036042e6840c00021070003011907805c0205419008103d44504540380c00103042c4407400448100030041d559095042240b040c2100c40303002c110303403290 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 47288556 1250 47287306 47287321
    0x210c0315040b1b190206010909030504120c09020711180c0a0309080c010509150a0c020304060e011107180c020c0319020114030f0a0f0b0307090f0209030f030a0206070206040b 77
    0x5000f500520303c406000381e2a900050340356415000720307801307543d94502007800342c024030b904001050042c20754840c00c020100c490b0701c00403c14031550003a815200e001c03403c0c0200300141095840300420890320110748403440b51070402d070829600ba0b00c2c0740c89072515000170481c0360720062340c10380200c18604915250080045065018243e40381b41a11540c405206a101c0c4140a00403544140d014501038060900540a00c0c0d42981028181804176850150300700c000301e03000401c07039080c2c6800d0b0810800303034010500100c400300240e40c1c10000034000c2c2c000c009000120164070303515481c0c0c01503041c07080f0b9800300d90403661010f9000c1c0301d59042d4000305012000d004420b044034403082c01854400c1c201da0b090b003000344c1031364000d0782c0c00c040c414020750400141d06101c2c41040c0400655000a0000390041f90000361350f60458010940e1003685d031036609039410a59030482d41c0743c1c0703000760076114002c40c40581c0035125000b00e40d20741c0143c091031700040c04251001c200b040c4904c2d440b0726040c0d001d44403402d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 47289806 1250 47288556 47288573
    0xe01050f0a05120a060216120f0903031404081501060305130c0e040515070e010909020f03061e03010e010603020a0506070507060c08160b0412090b070f020d02210c031504 75
    0xe42c0000c40740144c40c0000c0229003140001d0800540c0381e03042040134900d600d00380c403850040b0707009402003140901d24448440d074800c801200f280d8240c5401c00d410001d4800503c12b40c0f11700e60050346244940040500402e685107010790407500107440412059441c49182234120380f88010040402455150500204550411094000b170050342200c02444c1400003c80b00d152095811002254010105080540c0d00008603400340041076415070a003081d9040c00000d60001400380d41c45849684509010f9071490f82c082100c004d0014000e000c440c800c10300321802000c1c140000d07030141a03180000724160812408a4128a03405001400101d19010084070350207403541c400c81d14000f00300700038020300d03031180c0f581c00300c490140204850504140c40c014101850300702101043c803200c59410050f6850900580f2801340d00081903407461803042c8001101d0b00c0364002c1c000e511101c0140c9286001c1440c1001541c02c2c0ea40004030744526040108041e52030100c041440c0066102500050004909a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 47291056 1250 47289806 47289829
    0x12120d06050402070c030c06030c080601030504050f10020405040501080706050415050c0d031d0105060f01200105070f0f0806030a02010309020d0b010b09030106050a081509070e07090e01050f0a05 86
    0x8400052850384490000c1c060ba032209400742d03072a801600c014010301507058442d40003450300c2d04080000c1c05424002031300c1404010202410b060b6118005400d102b02848240400081001a280c01c2282104600005d41103801401d02480c68140080754143c00010060191540c1d80c6a06040138980000880900404000f5800304202400300a0f01c2c4001044400540b0895407408a000700f44120715110000c4030300842c480b070703030b04045c01d100c080d4440a514800034202071809900304102c0700c0c00244c01d40c1042c0b0003409190f10300303001c02501550201a04084020031380e5070f0758503002048411102e8100c02d07514183d05412100c60000150300980c0200c18043c4060000314980c055a1150003110070700b41d020140c905000215120146401e104000c0500000c440000c000790510b118140e444110010030058403402a0100d1820072040141c5401401e03040c1d0b60010500e060b00707004001c40e55a101c7c443d021120348001240901c0d0075900d4071034800c00a4a410400c80c5040204a103050a9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 47292306 1250 47291056 47291077
    0x303041403040b1306080a0b100f020f0a0501060305060f0f060f0f090f10210204020a020102090a031109100b03070e0406150305061903020d150605121b1212 69
    0x100030000b9000c1a40001d003004c030804904055802e490003e02601c1c0b1200184580e4915107010b828100c1607441500d4640c4a10481c40c145d1040c01894505900d0145070550f28111071052086070001c000c4150440003d80b8032640c1034420340d03202c0e0044070791a42e000351104081d42c0056030014a20b42000410003083c0c500062080c2d0420381100b01140c01203005546200d040004041082001d0b0220807054000740506400d503000c3c96100d4440c1c44804100c544002c1c4603c0c0c0000350560b24601c04d4042d43d907256001459101d68903039034039050003085c419000150007a15458000b4001e220b818040070102c41e6000902071540da41e0190894402450000b02948103565582c0400c0b0012100d000004500103a01c000619040a200300003552008201001060301c011301c052005884400c2a00c0c240382d408070f103e0440c1d10540c40c002e0040c0180307800071340c4c001e80c40d003070406058040040d07400b00c883c01282d90410100664414860600d034400304c521070b5540005141444002c0d510020a0112070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 47293556 1250 47292306 47292313
    0xc03030b06091002060703060b13050402090a15050a020f030a0c03111c030e01110406021f0f05040f0b1b0301052b03020f0d02011a060306030a050d1e0e0303030414 72
    0x400040c003418a181810380c0160301c617008009800344c251040c40c005d480c0e1009490308082e01841c1e0900507003e18040c4900444d004a24000c0a03120304041034054003416600c499040e6242000074107031b0300703d01003d0b80144640050280c024901004441003280309603214204011107031020354002c42c000c0c1011440c0e20074500c420610280622280c02c400700c15070f42c04240148a1101c10b42543c62001c0d806584900c101300c10007490b40c0001d00281d10b85000b200d4040600340320b1850f01c0080096599101d03c0b039007040700300f00c00c00445120a401e0103108500c280102e8440d103d0f880110424000009505002003005000070308d0102c80000c025080044980106001940443c2c2c040b0700103001100964004c0828050102c400c0c03100d003811140300d100800c201160409024150842d500c810b0b4002c41c0000041585601c040c801044826000421542c240318a01c0000340f503000d640c5444074030035160720010340e030301d40c45448100710000c0014000c6003103444136220318807040900c20642c0c10522 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 47294806 1250 47293556 47293567
    0x103020f061210150203030f0106080c041a030f01080a1a090a05070b0405010906111c0c06180b070504080312090109021503041506080a0b0a110d0605040b0405070c03030b06 76
    0x100e024410301c0f607030003108822003940c5090503103c11002e404a81030250b400910401040300001c401e9141101c5240c1b5000784140c650b002450301521070b0ba007040040c6604c00340c101114200d040f00841c02400d11500300c003000d81e616130150362503d040380d8004018907c00c0d050410504c104461894008061b1400e40701e445046590b007a191040030741c04071203581d130041801c025542e0450341a000074202070401c2101c1d0081c10b540603880e0307022501f600b1602e0001500c907004051081030b40038855644100d0802c42c201c0a402d08103816031548800711241e15030710000628551080d415a01117801480045050004d01900d80301002001001414999a5503408101594030350090380010b84102c1082ea90724102810080708102840b101d2580b110f003020002c02000b0b60000d2080d0007142c12030700c3d407040d82d11019510000b0b408860810f03c4610008982c92444c600990310032404c45104403401c0003038800e01d00070310081c2c500440c0c05201103064540511f022078029008442c883e8002815245042e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 47296056 1250 47294806 47294827
    0x3120c0311100e150f010b0706020d05090307061512020105030a020708030103121d060a050703170106260105060405130f0c05041508060907110f010608010e061005090103020f06 78
    0x61020841408525120412003240080501c003080311200c030070920f8500d501e017400100000690610400e805070800160007000d210540d4140d400c2d540c2c08030002d000c1c500b84004855035a422101095034100c0c07a04004003249400441b1a0045a1a080c20110500c115400540301600020150140c140c0c0800c00c00001840404c01980030b1407140e5015034070201c108500900728100000441c2d20900c4210040c440d551303a03502520710181da50706d4496925485442c04a502c031203005028290402044008600190002101c111840315040d0b501c205100c40c0d4007501500c0c20030300c2a40e411400030030007445541080c03410b0820b000c1c008800400c0340e11108000e8800c5648121400c000110702040c00c0c00740f010b00400c10400f10703005242101c0c0c503040c58000504d861001600301c009112004e11000d16061050155000f43c100001c020841140d440107154041c045400000666000d1728000942080d1140c4084d41034400140a07803010381c0c2590b0a000e640884101d140d0b6004109000700b400b03d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 47297306 1250 47296056 47296063
    0x5070305010501030804030c080c010215040f0f0b06040c05120a090521040513020307020c040b0f06040906090506060a0903080f25050c030d05070b0714070b06010206010f03120c0311 80
    0x13140710b4031105940e98a10b040000c07107220aa000348607031750850b50403803c0030303030340042c6041400c0302010341140140c03a80e01d4051100c0d08000c10040640598100200c20f001c12441c17030780c1c860300e020380b02070000c0c1141000895044c89800e200900c1c8003d9240400c280340c00369403245810920490865156a02003034a01c05c0015960542c031181210000707090100d400d2510005c420031303c41c110150b045003000d079006034541804541d02805582d0fa16170340d0310b05944001d51303500310410240125964603103c928240107400d481c016860800e0a05001c101203090242c100c4406049035655040380070304581c0c42d00013640c400c0103150281d65044c00810007422252482c0c202c12203d8180801d41440e503850541e0809038806d5000380303c0d40019804140d41a0408100c2c2d214642c00030740240b0070313035800f007050300c00c0d0201001c280b500c0e100200c0c10508001c0451032003402198240c00300d44503a17989500c21003004810703000040c045d1450b5940201182d0040b00b181400302d00c6401c10900745e110401080c0d1a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 47298556 1250 47297306 47297309
    0x7110a0b2d012c0903180603040b0604091b09020d1506021c030204090606050a021203010b16020409050f031b060103080d020a02010b060a0215060f0303030103120201181a130b0a0905070305010501 86
    0x44c0d50000100055528400c840b0841115800c1d10098210303e0b240e129000203480c0284528060303a200c441140421031401c405001c00b09030201012041740d01c035611400290081c00ea5405094500180c21721078400180380c0b501210305980c01031006400d0150400d24010f0040030981c2456001d10000c0780c1c00f11a402004003401d110b503242d0b134540c400180000c1c5401130106d070890304c1040030401803000041500480f412252005004040300f001440072400508288002410601440c03e540703041003030100007401d06078024680350707030031000303050301d664540710280f000518480c41005840c12042090300540303010581e50000150400040011400b5541300390030728070040c0c0020030709070b80000b1000103030780d0000c4090f200b1003005100400800e0352444107000c041c180c2c485a500c18059240300b50000304a044e510420308100740500d20381081d80010b00f81c011016803209500148041144485c0c01c43c20a4002100c885680c440030507e5004242141c1c003690140035111020010602c00d0140a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 47299806 1250 47298556 47298571
    0x10510090302100c0614010b040605090604030203070906080f030f09040509010b0d050d030e01090c0504200d05040b0a050402030604110303040302030102041805160c020907110a0b2d012c 82
    0x250301c50980c0340010490707144030a0510546186e00040c082c901a10058405a030380b5814503560b15a200302c0014449c1c006c0340c3c1300035418031905030080340e19800e5030401d10407901124226034a180c214100c00380c5074004c00805110303101d01408014201e140c5a00004c1e00294040000180e00a8500210744036103407258081c5c0302c0da801028020480c0b503040c0306a072035142a00008200c20280c41d0740355581c02c1202c2c41501d2084d80c694906004400c480c10500030746081c84510a607889560b40d900d1009001e003150300342c13214800280002d180710070340e0040600c03c65004010304880d580f103944500070b5041480c4140d0701848188004001602c00344000c0c005403407000c14a1804048211485082c0da078010710314980742d41800d100c0d40040303821031490280c8581c1126030240c0c95607020303c100c5819020041a61283c854072000030284100c50507210301507084c01c4220f400c0d00030040c00d1140c403811880c00c0c8400b070890f0900104586c1c660004040080181c00d42c0808400008130214543c2d0310040d910036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 47301056 1250 47299806 47299817
    0xa0b03010c2a0b011505040b0a1106010509061c03050c030703030b0a1203080a0c0318030807090e0108070308090f060a2006070e0d0201020c0301020313020103050108010504020901051009030210 85
    0x1462046201d208600c42c07400c2000044405031441ea00c4070349910040c480c81000300109401c200f03401e0b01880a845c06400c0f03494110f51110801440140b182c8815900040d260145800104941c1403920318988604400340c071510f1b004000660010440c0501c50050b001c016040c40b0f044480c05061000308100c0340696230200b482840d0008001240c45580c1c00710006118a404860019410100c1036038854028a0001903086d41041d0581c054055090301868aa0194102400705600603400f43d0190ba801c0e5142507107203031034162943c40b0003800c1c010131080f903201801c04c100284065004205045000d07200304964030001c80450b00a410030170190740422014600d400140341c06d04000f04149141000810342030a1022002d40302c0d509645050707000e03c40c0584190300356402040303114484100a4001c65407460202501e0000c0035201004078006030070100005440c4a05001d140d01817600140040c450380d281008014940c50120442d00c248440400e0000240e0b40da11400001e941107074685 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 47302162 1106 47301056 47301077
    0x8011404080c0c0d14060a050c04050d03120207240209060a081806011403010f0e06070f0c0602030a06170f0705060c0307081c11030108060f0a0b03010c 67
    0x245801040081311030040000700c00203000b50440305015180e440d21000e00f420180d44060303400c034151b403c3c24070083c00b0a2030b0ac3c0b540426400e11a0410104501e144100c5c030069801c40b11007a600c480640c29403610200d65000c40040322040e0403000c514154288001030100e008a254580800100100180c0c01d441c0781900120643c1c00c1e08216601581e4030b244819140400b84a880d00035400c1c0921a5452000c0e07008080c6265011001752985641c0c03040c08650802c02e07403402c1010814a0100c52000c680248011805003c200c80c011660506100c0341c00900c001a6070b4284040e4040401000b1200d030208806050315011100903903039482c0004220f2642c001d01c900034114080000e0740000c1d500a90129112614040c40240325002009000d01c5007400248240d2060360440c600040300400f21154441d405000b210f8001381f00c0851801103403c40d44060346010108105510 = true := by decide +kernel

theorem cover : BRFrame.Cov 47122306 47302162 := by
  have h0 := BRFrame.cov_init 47122306
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47122306 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 47122306 ≤ n) (h2 : n < 47302162) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
