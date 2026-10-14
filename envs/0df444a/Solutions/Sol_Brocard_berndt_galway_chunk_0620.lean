-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0620
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:46:06.903765+00:00
-- url     : https://prove2.me/submissions/be5cc477-3045-4357-ac9d-17c2e626d756

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 111330935 ≤ n < 111510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 111332185 1250 111330935 111330959
    0x14010b0904180c09110307020703020d0303061d0a0c020304081e03210405010501050a050906100216060809010513120f051c05060108091603170403060e030c01050703020a140310 78
    0x14001c0c3c4101c80342901d0103000004503400e100746000c14541c10000c01a24640019144044a03419a4280c1c40c5840d541422002003046400054600e1031246001c5100030b03c50220034091008406e0400c07a9401300101032b41e4a100b54891041c081d0490aa0700c00d46420399500005040c001c2400c4e02d10300a11484448a154882e02d220400d112a1b00144020300ca002d00c80d050241c48184e804040080c10140010000c2c8001004240700360071310861003410314800d008401001844a041c2110180c80c1c02c406031489108036114040c5601c0c20001500f02d04680940d44909900f00448200020080f401180c040c90702c48009411302c081085000b0540c000b402c0784900003102500002280d05102c0001000c00101900301c11581e4814040c03030480070350000320303a02100e03800254184080c0d041143c89055004641c400b0340214034201c000d6084050110050454010700300080025540380310042d022801404148000030b0809032400703090b554220025078020b02c00b510710f04216a516503d000301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 111333435 1250 111332185 111332231
    0xd14030f180103050411040e0a060507020a0302010506090c0a0809011416030b0f15130e0f090f03030709270f0b040605040902060d0b13022205010314010b0904 70
    0x2188000201d020720040036224408012100346028080d90030f09445184407004c010040600c920f44c1d0f1040038260038410442480215031181d824082440d0803400a134841d041418164095402e00d00009d2280c0751240c125441009407030041ea0402c95401c9040300c1c6604003c1c01303950303190760343c0c495070303900103081380825204100700c610020440e80903400007400d82d00110300080c007680c0003c0c000b02c11a6a0317107004441d58103801440319110414070f02d100302e80358445d0b48080e090125100c140040c005140c64514440c40b03070001141c0240b8a09540705940384001c9541d0b80004100310018840c2c855400d801c1e424622684242c4401a0705101c44c940c201c2c7c4101c0c1c400065107075541840ca2460502e406664001d000880f41084035800750740203c0c005221b1141d890711142c0c1d89070411659036685051904c241d840c9020308540703503d0028602a811442c03202d2a4036020004903000547c0e41c4a401800c41e1083c203101010b5182e4600f8400c4081500101c2580364040c0c0c40e104c2c0e640180f5921a000b40e8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 111334685 1250 111333435 111333457
    0x207021c050706111603060e030d02030109020909060a0308072303160b070e01020a0f0302070e09150a0216030305070504170715030b03031204030306030602070807120504140d1403 79
    0x80b060345081c40140044611445940e0503400c0b051030104441c60044414080740d411138004070707825440d80103031070842c406e104292032194404000030541c40c03119805006807060a41704005903481d0901007008490041c03200800a00c41082804000340840f01500ca001082002102141a50450143c150b4100e200f0410070707001c074007641c00c0602c020202c00b00d401803440d042413040f801c0c441000035101d100f100006010140608424130806100700030500c01071000314070128280c103050380700c41d0b220602690a100d0a0207240c001c110301e820707144216842040010140070a0701d80d40c0e541035014040082c02c090a00105000c00561022103060000d801c96066014000c1a030071300001804038540305003860708051403e201c01060381c9001080341c402d000f051416000665072468200c020306091b0b00001c0c4510300116418040044a9015003c4580304003201d080c0301e44080310440d0940139a01c500c030082d072401c41c806070503820410000d042550054558415480100f03408901d56807100c00206 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 111335935 1250 111334685 111334693
    0x10f0501060c0c05151204170403240b010504050f0a09051003020102011b021f0b060a08041a040507060e0118030c03030809120a051b0a030302090f041404060207021c05 74
    0x80b08114a00c12102c02401d81200c001018541041c0550040e008000703904240c109a44041030501c10b000e48002c03a0303c4a41d1100e0742e030f2151a4a07189010a41c0c14000b00c505003403902070070103500780324000c40d80000810307501e140c03c0610701810003840365181c0322007541021040002040c0d50149001321441140850710401c149032862000a0071141303040c1190020045114403412030960120780c803d8401c0c050a4010080e55811091800800000000550101e4006410b168141d0032080300c900ca1400f4003c2c8040300e07640c2004145000900b150024500c0c1c02901090042e24040c048103161180103160110803c0850002207200440c03603002582c80015a000404c10140d00200495018010703030017401c0e51001d00300b8003c20b18000c2c085c40710240032000c1102807507840c202405411030781d406412500300700c0c55414058000e6201002c0c80c0e0043d0b4010b0070701c0391141080c0c080e0360304051407030304036180300c2e40c80d0340b6100001c0d048100708030787c0b2005552400d02484d00e0a40b8078040300d80154054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 111337185 1250 111335935 111335957
    0x60406051e1b03041e0c0320030c19090905031e1204030e1201050a060501031a010c11060c06160e0f011b02060c0d03061404150611010f050106 63
    0x407062100445a500016002100c100000c411208151501d50101014203584139140ea28202558410b8810040e4860209042c1c2a05100d00240001d003140d00421400900090b40c008400607051310300c5240b0b40650114908111504001003a489018030a0302c1c2d8086164680212000799070442805988503800400d400c1040c400140b220100c40b58880b40680c41c1c07a090030400100500005c0025092184141200d000b6846182c941e415400c02c2c400200610300c0c00314800780061441d4000d95000914101801c05550f0499182500c08a016190181800c1d115a20718590804840f00d40e60080000d010b00b440600e02005030f00d010f05c041240240c1159030b1188002c007100070550000740300e0044000c098103103036004101101c401038150b058071030203006070012402e1480f680784640014812054080c0509a2585c000130a950844002178030b0000103000f003006581d031560f52070655640c2520104440c41c0142c04a0707190f544400b002107040c600c44645c100480360309920440200701c08040d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 111338435 1250 111337185 111337201
    0x9030c0706031401060503071b03021e100b0102060c0d050901060308070506090c040b1f03111303020306130b06090403090e070903110a03030e011215080f10020405031f0e06040605 79
    0x1c3c50140c816031400e14110301d08200014405460043c080b140311190004004c2818828441c1c44412100f65080540f103943c90102a80c0d240f2014402c2d01d0b00030700c0c06262004640c400f1611038041d51042881c2d80c00e0083c425405c0300109400390840a4a650b2120000f000640708005010000d0094001c0d114605d041d01280d403c107025541043d1099140040141c2a90b5420341002c1c07489450001215403e014110b068001740340403502403440c00f8001c04c0f800e401d2080c0d04214407d8910036401d54081d601e8019070b0240340702a0150090000320460001082420605c190070303800750003803800104043e5225000307045180c0a480101c00a048164180b081c882148900c4440c03480540e540c8060303a29684005000400203040395040024040d104119600b041c0c100710401e90401584000c0180e0314a052035030f03030303c0e007454241c0c403070050f00c280c00690401c910964040300c501401400b8480c02680c3c000b02001c070100d0709114007a984042d002c4603040e0030898544128800c410008450403c192 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 111339685 1250 111338435 111338471
    0xb0c0c070e0103050304060e01030f0e010204050301060527130b010603050115050a020606090a020705010623030a030e0105030a0219030504110303040f0302090c0c1002120a0605010c0b09030c070603 87
    0x1c074a048041c140010030010700000f0071607088554600d0502d503000a00c1004038081d01c9200717061a1040c1c1007180a45030a030040d07000700100c48040b002040305079039034420f10078410869a5051194071300c1c483c164030f400301008030b10303540588400c0c41004428102d51f41d1500d0004280c0022000a03600c8005101c80c400e1a0160721460085050050402e081044c00940e1200d005020034040c06804010071190030894050341c0d1a1a4803800070302900352203441030800c1c203c4801446401c01502d01c200c0ca028240172a07448504c2d50542e50b024a04074041c0c006448030780c000342c04004a80d6013009401c181c0d00c2a075020391461f02e040da401207518181030500141440a26804034440d0300100810030040541100c0c0130100c960603241c0c15031598415150070703444c0c01907540c010254006c100041c29240e00326802030402065054020306a521004254000c032900d134040c1034081480400c107900132442c80c0281640c429040c2c02100d1408203100d11040c1404559445000407980380c050400034044910 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 111340935 1250 111339685 111339689
    0x30e0d0c050d180503010914010f0e030412030c020913030f052b0e030f03040c0e1b030a0608012d02030907031e06060605030103060b0301052707030b0c0c07 69
    0x460200c868060039200d0540b12441409150103220101000c0702056081503618002400010003c03c41c2402ca420030403050b030684080314403d546001025001004180b00300c5250305404070081d810142001e0700c0c100362010195059092201c0211800300595030000507034422502429a603d481000385030191200780018016001d000c2c0130b01c07074101101034541c0c2078041641c21440b00c00c101806000c05600400e0b002480680900002a030001010a00001180142d01c946003036004559203021458108809a42074148008546085030409109e0300145170032401480c000202c0359035481280f0f003181c901001512820240c0400482c00c0080400200c130400041e1031305515500d042200c0a468148900004126105070107030341c0240c280e50603080e44d0013980f14800b005a29110840503100b50001d11040b28881d0402441c40c520381018000e0b1405030880742c1480c1918010b1110030491030303800811a26481c402e0000000100d6a4085082c3c0100100880e180e42d80881c040e800c1d007060394039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 111342185 1250 111340935 111340937
    0x20f0409060e0a05060907230d020307080a09080301050d0819020d020c040e0a021216080a12020f0703110607060504110307051002030406030c0e04020a12050a06030b0604020c070e07030e0d 83
    0x40101381c1d111140c201f03901c2501803400c00c0640c46000807105644150108201c4070080c0400c00c2c4038428203c0e801103004840d603441d2001580c0c0c5150403881603683c2420700a0000c00240010803286c1410320424064510690800e400c1400c404620303404c118460b40306200592044e4440624190184900180c0141c00c1c1c40500c2100794820080d5603a014140000f8050b080080300c5120303480e414018444029048080c940c00d86503102070143c0e403400d0074642518010100510301580c98000141c8401151144001e441e00c0351940d00c0303082c0b0181d10164903c1e00a03070b041003020001456845814821449040441151101502818a00302c040d030400d50180c44000e0320110403940000c2942c1c01c840c1310b49804211f845007000d0032601c1d201d144107801e0300b02c0d0021403540011070f000741d41c030b201420f40450208010f6a500721618251101b034440540715841c2200401c80d81d080030740042007413014500c01caa9030703255210301400c58101d01b05d5a12000035650045c2a0034090140100b40e031f44522 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 111343435 1250 111342185 111342191
    0x5121b150417090d0209040809030f0c01180e06010804030509131508070501050301151701030302060708090c0a050432010e09010516051e0c01020705010612050a021003020f0409060e0a 81
    0xd0074010440c3c0d207130000b80280c8900b01071170005041150700b0084030891400501903076042320b20b244c88590360340440e1700b0807404140610107214083c10b060080c001200c0e2811030000c0c5a48511005460700300d4058015400c200c0104111852519410300c05a000b807506030307000400d445547ca10420740f2030544c1004c10030740c2056008000c680c2c3e01c0026a130650328603810003280c40007140411303940c2c3c1090030740e041d2620109900000c285074000c40c405225000945840f2142d0ba1000051074607441c51240e00c5610824002040c000f0b402d1a51120440400126031100e00071a0040b820000f6441c058400c0002d00c403031030051052102081509030004910310082c001d41c145030540c5860000b01400e0841004801300e021110440555140ea12030145c040c2d001d80e44000c074181c00d0313001c2d501141043d80e01d0360810304001982ca2080701240316a030381210140c02915003990030460900d11107040942056020322200c1003c0e1400e070010f000411422600242036880c203584480b1084008200001c0310307203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 111344685 1250 111343435 111343447
    0x5180c040e030406120b030d0e032b110703050102030c03040c0603110405130207020d14070501020c0901120c09020301180609020304170a14070b0402011103040305121b150417 77
    0x101c00403d5405850250404134403860100c03840c0401840d01c040c130194144100c40703540300d03429003006007c0341e140b00540c1a03a451499024483c004000b000402a250310380c0c2d40349101d031580c031850008410103403110503a00256600e0700e0709030036600203441208040c1000414481007000c4009450020642802c0501c40c110b00b0b8242c0349003901032403042d01e004060344101801c1d0206158100c6000b15030003004001c0300502030905c905154403007440c0440500c5078000221b969800011040305581c401850504a0381c20881030710a2100000340860f0308035417240c000b20340c580765800918082c02c0303c0000a43d28a40801606040d603a040e0300200c8010302c10010301c8041070b0809850231403000107c0280da0b54105a08080792001d01040a805500d1000700d041d0080040f480e800c1c0b40124001d136500c403081c0001c19200e586178400c0e44801000d660214802d14111840b070000b0340a0082c0b00c0950345e1385502c03407540d4181045440d0306940001c407800010042089019011201c0080344da50391241010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 111345935 1250 111344685 111344711
    0x140601121101080a0906020a02070501180308030a09050c0d051006300809041401030203010c020d050706050a0b10021015060c060f06030c17071203080103030315030605180c04 77
    0x70840d004441c100310800000456428040e0483c10819078050300c219030b10004604002e480d88824052a8005141c0140c44040803a10b010f0b04016290001e404901c0d645414401c2e50003802c8141e021034541c003500300c0401e01940d0b801500c9a946004001070490700003035103c060129805600501000002d5040c00ca100f1200b2091074220242c03101300001e80d510b11800d100c00349002e8201401e41c030034104211425010440c580681c100c80c400c6d0028000d2164010b0103a0b201c802d10208040045c1c0b0a01c61440800c0107031b080301d9086030000700c00048000105010a843c25038041003500980e10004c60200918210b104129034898500103007124a4200304009083d440015006401a511085480b0101c2007560200d0011503000c8880484107135501c4a03180c0c0e03001c00700214403042c0200d2100191041150012001c1d050f4155901d00080e820360b642500203180301195544545c01082012000610380c0c03150500803d00505800c01e40420122507d00c1c3c151080140390013103061060401c2c0070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 111347185 1250 111345935 111345953
    0x180507080621030f07030201062c04060612060504050c01020a0c060c08040b0a02070e0702011503080708091908012409050603030f070602072d0204020d0b030a14060112 74
    0x10a0301150100590400412203030b251150880c07002c5014080081e810907104402c078010240607120703400070300510740da80681900f03603d0b00c451444075880214040301c400d01825042142e0261045400040740e0f622071940c01c03885000941c04842050b40c41c0c0c103100620408004000c9210303130174070003401d42203941d54455080f4075092007070406020341d0840c0300b003c00042000b0fa801420780d007401c194440300d280d8002565400540306042d1041100300c089080c891041c05050800c8151401c0340441a28681c0c0340070842d1300684003550080024400130665a0f113020004503284138244000c44d145003402c04040c00c55910603645541e800494184410001c000a4040100c1301101c8002520355510408a419803150000842c196440058071000b04503041e405803000c00d004203088425413040300245d41e8a24000d84660598541c0940c40400610740b03074004101347c01c0010400b00d909100940803c1c0b80141003041100e01000d032503691106c103103003085540c1c010700c0464041149108a40c0f02c803440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 111348435 1250 111347185 111347191
    0xa05040302070303080601020a0b040507030b010e0c070231052403060c0a030e0a1203050105061c0b1c0b151801091505060408030a0e061821010203010803030118050708 74
    0x9100d845c01c0060480c1c2c5c02440b034094907a42203201031000d80341918045840b804d01d40001c4802048500c00800c07011405001544140c0403035402a25209040c0c08101c0700c20403c84100c11082c4807010780d280720700e51001e0500c004c0c520761130300070035503041c020300500d880c03000c500c5814009001003d40346c01d1560006580c80e0050040341c0900c0e9a2410510101c0c0034145141e020701c01340c4222540002045041c01030281d035011141d8080045989400400c681c074454070328402c400f060312503580e2529a01d184e100d64540c1c0ca009000c406060341601c580d440710385400c08180e400c903010004001d064100030310401403900b8103c40100036050340003500007002c1018003e19000650b260200c00f00e01c03444852741405070000805541d00d0f25a0f5030b04142d41ca9002242603c00148000c1140000781048002d54040e040100925211185101c6c140000c044d242d6000344090000e11040740c000e800300388025400781c010b420240d42e4a42c10442008c500e50242c0e4641444030b49080e0810020b15800000903030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 111349685 1250 111348435 111348437
    0x141905040c0e090f07050a030c06050a030b09190e0102040f150c06140a0b0306070206160c06090303290607020d2a05150c0312060315040b0402090a05040302070303 72
    0x16058455042001124010b030300548407050140c014891a1500020b10121a40c0c040d0112039495440b0814044400a0ba2200500c98030806000f400481d0090000d00070621280c070300010200c105500180d64410260381c0450f0840419224040c115000d00074a103050309024020362a00d858120807504500d03051060000c864103c0c45042095071040781d0854103942c0011040c0f000d100c0d10070700b9006142c0252010005036152040407009404c0106a003072080005030058859543da00c0311001581c81d0414040d003c104042000300c0015100f4400c1c0d0404034025a000118045e5903039120f2400da0800121900c000310200805d061070391607504580032594195404400e0000700d15010075882075030103180702c1c3c011a41c00100a40c0c06600056002c0314030440c0d0040c810070012b41c028441e0321401d130b9040c02641007080400e81e9090001c0c045500002c02070b08440c0a12030308000c5c102911801c0e90301711109552501804198900b01c000d041d0045001a800c1085041c25940a581c92003140700c010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 111350935 1250 111349685 111349691
    0x1006050312210c09040506100f030b0a0816060801060c081e04050916030b010c02060702120a080d0c090506040617040c170619022d040f0603020309011419 68
    0x3610078014440a628000302c41d580d090242464004000d06421026000d40200e00d0440003442514010150101007040e0303880b4540030301103604080b009000c1a0700c86640004600a00180c80042000140c000c0e50f05046141542d5040480c001d00800041e80b00e082007118112000010a0200c0211007601c03c82491034030858142200380a240c0c000d55110070b6102c0c421900b004104541c00145240b48201942c081241c1906140150b40c03110030f00b500650803100c02d0108200508003642c0a002c2c418228046505860303050341ca00384030741c1c400100c07107501076240d250481021740c0080094000e008200c07000c1c2c0c10b12b030620100401d50100092030f962003001110202e0b00340510284000c020740b00311009941c8015900c50703034696404045d900600803442422031482c0f081d50750f10994200302840f02c580710f030000103401d00c044007445100e0b40306082c1c081004001a4440030f182120000c1003030b5100036807039103480e52105084a03e050300d065100320301c0004001c41e200140d010740c00d00e141c1480e800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 111352185 1250 111350935 111350947
    0x5130314030a060b07030203130e1005090603010608060717010605041a090f040c030b090a050c16030e0307060305060f03120316110604242c0c19081006050312 70
    0xa40607241560144d07542c810300182c200b0070315902000030411720b40840e130142009070347c40240b0300c90f04004031000f9884c800204018001c80c50002071040c1c0060000740042901501c1c1d101d441d041c02c4050b2204004600b4445150225018214907180146000d060a5092903d05030396a00ba4010010110559200000d041180d542e01c1ca650441d03000d41c090000c10040b200107901500401960610724400c2054400040c80390720740e03010b041c0c40351040e9015241040c000401080030500312001c01c409006014403041d2994400700052001051659004561070800000b80142801c003c01c0c9a8040d400502441d4030303148000e01102e80000c01ca0410f03841001041e07004032215445e84035610b1540c0a030700240b2050001c80090014481c02410401011000318420b4104172403071420503d0328800080403c11502e030106000c40b0940c48041300b59406885030600180008450b1907040d00d40042020040c000c4034030400c00c46001d0032460004002c00da0030310000130380c2c0f1440c8034031400c0b0f109000102 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 111353435 1250 111352185 111352201
    0xd020103140408041809020a06110316050604061d0c0108070c230c03031908180102070507140102160b0a020a1406070215190f020f070302100513031403 67
    0x11248101010351079031030345418980341c00c002c2c0340e102d07201d040c1c0e61220418260b01228194428034807002d50003015800ca00780340090a8a103011005044103881c0401d12298079a01c0c031400b80d58075120f10400150507589003c1c5042070403105861042141841c8042220300c1200000500c0f07402080242888103103076850b05412681503555070001898a03505a0f00d0005051110041c0002038420340140d90091502c1c0050540d00d0045404060102203080c50704003c0900501207160801032110b11000d440c07411810403800d90784051400c58003680401020040025400000b00011100344083c2015a884290718107403250a80a000c0306070b48005003001e10f4034001c00c40d14104940c4415403041c01d100807900d440d20394070304030b80c106e0241c05241d98000c601c8500c14255031050111100005040c4900384264008000740640000200d600300031610030784420101030040c0520076401001d0204005c04001c0c00c1d070320007070400240049401100d4000075004454408038040340c0b6842c5440381d4807510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 111354685 1250 111353435 111353441
    0x11e02040513050a0e01020f1207020f030304030302090406030807080702010e06040807061d03010501150f0c0b0a0906060e090703020a0b0c03030c0a090509070f1d150c030403120908060f040b060d020103 89
    0x542c1d4050398070029403103004444400184c0381e540c0c40c43c0409c00a95946040c01da869050411010645400400014001a019a01800080c81301800000d101070b00d903036500449500c40b103003c0d502c00c0310214000c82150b03803200b90381032081025035070036040610b080400d039510034050103080c060000706940d2041e50b000c980c0341e1400d0b4080003030003440907503940d90411101e0a220100c40c000604840c03990f0b0b803a03501406101020725030214856100d6561031250400802401c1d40c1111026114a8002508015109258090b030000800f40080d94618030410106602650041c0c0c01c644041c410038004103000301c143c2c0c1c0d0101001145135075400e1903450071900390703c83d030300306642c4203004009002d10b00342d10662420b4451415224034202104802c0c108142c0414aa01280e00565071860038076240c9840c005440702840480440342007503181e0340c1c0c2d1404528000d1180002074a100c07030030032250408002070707034020032808001c58041c10203031507081c0782c45802840180a400002404011a48264 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 111355935 1250 111354685 111354701
    0x90703021507081606060f0605120a0e030c060901020c19020307030201140c0601030303051b09030c010e060f030109050604060e01080606060327010e0606150913060f0305011e02040513050a 83
    0x4d10350904e09800307280c41002010395001e0700300d0108002501048042c090b2085402c00000e041c5240f0322642e901215501800c52928101d095020a2296003844013040087e14000e100c180c00250315414070700700716842c0401000c020481c0c140e5500302d50700543c90104042084da41c0a103046c00b14030356203440e400c0300da01c15020940c0e41c5115400000091541c9540810f000d03004400d007030100300d4180082e00e0303440e001d80d0150340c2d41a04401c040c6c0c0d0700c2c0d41c05807014104154002c1c00b810f00700401c030220990a0b820990040483e292604100000c07403a20f8480c04020f482101e144154550414441540e80c4000601990140b45c000001c42c000400d03409014401241c9600800000c801e034031080d41c0601101410504d0303074410200403c1080c9068800c1400300e0403c0d002c40c07420b00f081d46082080200040a1000325203642c1c82011603680c00020414010b180500004907000420910110444401c0003502d904144140000d00040da80c5541c0040d060040142c0401d01c0d89071450340c4c0000f40091 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 111357185 1250 111355935 111355957
    0x7060e0102190206060108060906032d010903030e06010b041505090105390613062f0403031701060801090b0102010e24010506030c0909040507030c0b04080609070302150708 76
    0xa41201c01c82c0c50340c00900640300b0704082e60b5113400d90310b070601032000f842c00560711141c1c5904400e4a01001c11a44090005aaa43c4c5000320032903c00c6c603c40c1c1c3d402c40c0c1400c3c10a90001e5240d00310f48903e6802044003038010400d42c84440c0c035080c40d01e0000062003440b403904908011000400c520799a11420980318000711a0000c40765410495401ca05a0302c420480c01080c811000400b00b624040450a50710803051481d00b00170801e101d035180c9000740101e0b68041030550018007100160004d401c0c0076000f010007010f5450380c6500314103000e003205449070b081440c0c0f11603803c010b00c40746602080c905d045402081c404200c0d01460350050703014040311154000c032445050104003900000000c2d10303070030b140c11098400072a62220309001192004130b0b4101000384040080070749030300f05202501d5200f8003450540c0c05180e120b58a89084072415030100801000214080c070406c001030203403c0e00508500000c007000b900d10707804030761000e61501c142c03409940017084e04004e10081c5001c0310303004814 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 111358435 1250 111357185 111357217
    0x1d090c09011a04081c020f0a02061e0d0204080c010809010b010f0804030201330e060f01051c0608060406050601030e0d18170102040305071e030f0206070203030a0306171207060e0102 80
    0x40d50030a00c0d003c0c0ca0000c0d068011f20070202c03a0b08044c1008501e50030f0340f0b0f03009040c680c075207020b0383d108501c00e615a2481c8038003600700700003090064a0078400b8002800c060700c040c0c81c4102190000600542020340748400c00d900d00a80000b0a80c0c00c4211044003110781c0c00c19104565443c00c042e401444051010700c10b07100d000100909180303186a03641007880417a01511101510794050b0910304004076551031f008890f044d0440d44d20f41c051406450740d5418079012941115604560134251017a81c2d000246e00c1d48848107200402400e0300406602c030b030703083c41c00b04810202c0003a5540c0d1070301141122000c2c84028000300c01c2d10074803038901401824048020b00081450303880040e000f540548001c0e41e071809110004180983d190900c030808400410b16007540710b0954440c04460001c800e002c91f807000d020480e41006840500c0948480100d03520f0015013a440d01600c210710002e00c4d80100c0032a00502e81010f50007229000b07603881c01d41c12120002d01c441c2001c0340030f0300902c503c800900140d0f003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 111359685 1250 111358435 111358453
    0x91a0403020703051c1b020402090a030305120a0207030c02040c051303080301030c14060a0e0d060603060203090706030209031b1804051c091a0a181d090c09011a0408 73
    0x41c0000d0750100b00c0b4032038000c844401c5220312000079a400c0401081d4005030344940140020305060401c082c4960000b0001850171120800140d51003c0561003100031880201d041ea43c0d10445090342035100c0360b02c0409624108071f5036001000601010b900a22807980c07003207540c0381c8610540540d40120340e54102403107110703268288400290402d1100b110001074251002c00c0c4d04030017910101c840300c0054071042c1803402d02d60013503070901c0351003001a82000700c10b101803001c1141030140c4002140941c40c01642c03030910318911802c1040d41e801c40400e043c010000c8900d03546001490a110342044d8030700b1420f030004c2000180c80c4407005407a03801320195440500003841000300703022802c2c1c5d10314042c40f2034500b074400090321070510512580011500005a50b00385200c58002444101c3c4249001e0511103c100c8001c009040560401a00c000d60108001041c84d041c010a6401010070703002489040c210070000780c0030400c14014403c0c081c0401c00002100240101a40c3c09403074040d0a13281545 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 111360935 1250 111359685 111359687
    0x9060a03021e0d092015031f0608070f020f0607052d12070e0604050603041b0b0a02120306090109090213020a23070b04031808030403080a03060506040e0703091a0403 73
    0x104e8181c000b52403c418004061161000d68043c2c850724a0700035142017503001003444014402d4100800c0c1524841018141709000c4c0344042956003d00103603140c022050800003801070010310410100002e660103002c0c03200800000080982d800b4903980317031469855018080d2103441e8400300644180c01000319a4a042d03040c40741c0007901035207400d00940320702690740c41c00455814148800c1690007c0c0c1c100002e003d141001401950b10038003800703481c44500e46240f402e492119681d03001442e126004610307112103079814400e00c212900c040d40c29504505000c400295150030602c2907040301559000321104540720901c0303018402080341c00440d22803031410006454140c001e2007140b180c51803240d414140740003007001c0c0e4000a800840280c0c0ca607a0382d0340c080c6c0d0040700b18100d00104038040c504c00142c078079042005001440c880d910850b20749500303000140c240c1e4030503000705104140c140000d01c90b81c01e10404940d0710017103501d00402c0010304c508cc0141070300c65840204104006c4001008185 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 111362185 1250 111360935 111360941
    0xd08040b0a0305090a0c0306020315030d09090f06081e0c090f0f010501110d0f020c0604180b040504080a0518090a051006051611130207050706021209060a03021e0d 72
    0x1941c60344040c88039660f91405551074100441c0010003e02c5140002d1002c034845501441d8030461032110120001880d100191512a1686040d0001120108103108076065401089031034005284140b040d030341003a00c115214101405105211005164000b0800d03030100440c404841c2c001e410081f0a00b0103864140c40344004407000350840045000014103944101c14080312919408081c1c8001100c20b072007128241100c11110046105142d03034a04a0355800c0300404c0108208804104000c4140098400756018000003520861401c0104404546e02d4011103401031402d10300259200508001c03024000011044560000c1821003049403129059204501374000c0c2100d03503080565400d41100e491060700c00192519020100c04400520b040760040c0c007940340103080410701c0d645140e100049801a0505403080c0d0701c02e2600704510354043c000d0780218000b540301035161814850220b4414800c4404210405500260b0ba1160281c0440c804024001480000ba507aaa02d002d000c405 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 111363435 1250 111362185 111362197
    0x20f0a0f020706020a08030105010804020a2114060402060304080304060f060b040e06040b01120b010c0506090606010801080604030f0e010c050f06010f0e010302030615030f0604051501120b0609060d08040b 90
    0x351190a4001c0782c001e000044201c0c2d5264003403659451f580c205001100e84d0200a4000c0b88c100014282c003207002c1a14802d56030b10400c850360015444e10041c00d00d0103004469101c1c00949030810010f100c05030302d4440450f0360094000003404d50344e855529220000f04601d800c40c82c0c0f65031403d00c000c1034140f40340004108032403484804401a440d940c4c100003c691510b2500f03400309009030004000260140c0120106003414141445880c0c901e0311003606051080b80c194400c0e4000d90f04108456801100d01ca000d000001d00619492405650103403051120346003600500c076540341041c1290b0b02c035409103000310381c0c88400d442401290800855841e8000e0245a80c0d010020901140b00d84080407070038103da40080082c859600d810030051401d850000700c0a415024062802043c0b40c4100310071402644a0782c010918a1205d600707401c1c0c0b03084103070071502c0107010540d4144c000c122a808140e03042042243c07600c0c8507494490015003038103020440200b5401c0085400070300c0f13100701405400303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 111364685 1250 111363435 111363437
    0x318090e031b0316060c0e0904060609051605030406020304060608032206020c010203040b07050a021807030b0907020d0806011803080301140105070302070b0711041a040b04020a0e0f04020f0a0f 85
    0x7001c00090b903055440e401041000095084124890300c003241103038000b18499079540c106070140d0400f40700824104c49003200c1c180c5100c0c1e22000d08004070f902c40c0c0310f00b9910110611000c2c0d401c5d8081800100548005407001d80384580120104003400b030340e540140000e246250440796201c04c1d03060800d48020351005017042d03650803080c00050741c0380003150604100c401603006d51f140c107082c800d000c40b05400c21401510540f09041400c1c0040e110b0500140b201c1e800800000390a24001c1c0000b0161800070b101540500404c100703008410390000740385103048455003022005599400012141e1081541c2d40c4680e192090320300101740080300000714143e803000000ca500051a0764015603203842401c80050040e0300103a01000141012005000c00324810f200c0b03201070080c40303000501500c1e90801690341e00103075070130200c0480c500351090002e080c1042c2c82c1542807807541e02c1e0241910820400040c010384440644120694466045078070039645008069190f21103108001d10358180004100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 111365935 1250 111364685 111364717
    0x50a0e16020c300105070c060b04090f080918070f1404030302030406110a0609080910141c0b18010e0f040803070e12061f0b040b0301030318090e03 65
    0x2159644046a0030908250182102c10340240c0c3c1400d80c0700c45a0030034403995011003809442c0720354510038040c050095805a446480c8441e90b0b0070120b0403144a02d40d2035124901d04074010340050341c3e0080024400703810440d05600c500d0150042003048070804008281c8880030010030201940140341e00000503950b41d90401d9201440503a845079200c0d030301018000d0303481800208825032182c07103004410b00ba8038080c0c81440203a503680e00c05844031000c040300c0b051004030b40403803c0d0404450581a11640d440c0c6000e8002018894104500c41c10074448000403680c3c464060701211504004070444001d03100100c00b0341500d00e424458242070040001c01c600000209161650070010f00380603030740000d9072620f19102c141c000c3e030380f0008418800c1d03040f0507000c5071405590b4091001c1e80c1315030108401c0c0c281d014004841030f4101c810b00c5e0040b0801090a000074400c1075007444c1171740d06403a85418503551007101d10f89000b60416880e0f0251105038200180c0b400605c0c0c020003e0078855511401b50707 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 111367185 1250 111365935 111365971
    0xd050a020409140f041b030503040b0d0c0c11010f05090901090b0f0907090e1e090106150c0c0306050c0412030207060807080601021f021c1a010e0604031b050a0e 71
    0x1010804a040d950314030b0300c20135400840c003c00c16503240a1680000c400710082815604d5440c0c81c103580055100f886500004201078150301d500f400762000d00d0841d4038080c64403411130340e1403840b1260700311507050401504401300c414840c020400c40380680170090560b40c4031340e520904403020f80303910a1a00d004d180c0c0c4144200450522000701c0b4011092504c03844a000d042540c202500d4600411401e608007540d0141141810356602c058010742d00c000004ca8500c0c2030107030841e10101c071544c0356410840c205803000080303101c1c90b10800640313900080c003081a44031a04c8a040f14000e43d0041128280d0860206d000c1540009580088400d240c40d00840380e5603950095810a500316581030260b000754201c640b607050401c0c01040403100382c140040c2041118216042c102503404e800c911150750b00e403004103d131050025013182518003403802c601116000004250180142d00c0001c0800d0040100200c258182d00a02405000050702c40c000e170a030750b421078945009040c0c4481903008110450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 111368435 1250 111367185 111367211
    0xc030201410606031801061505070311030301080307061a0a080304061403011809050a0804090911040e030a0c050a0501020a0305070815011b02060409050f04020a0b03130f080d050a020409 82
    0x5142c0705050081c50241140ea409500002c411a52142c10b0072556a40e20049a001e00b503464100c0c402c1c0b19681c2c1d0988841d031914000c0d00c1402d10b1103900c19654018401040250f1000084481c01c1c7d511080209486505500140180d9100148560302040d00f940c04142e4900001c0070300304586031580d070200c000112032050710440c8400e00900c04015070703410190f4142103050301310500a44c41403048540c4800301ba22180da1a401030341200c90a5910740644c001481142000030020001c110340400c0803160f594103450360703845014a41c1d800c1c03010310200b403018802d05100881e506a00203000b9580d8065508008000305800c56401c000709108001283c80c00710036080301e4128181c10307160701d020f4516010000d6000d201c031070400c0381e104404000108428210340101c1d8041c00103c6c14029076803e041c03041206d0502030340c1200b610320300103104024010080c440c5c0b25042d550048800700c112140f5082c041040e104003a21042e9050030541400340d0710303040758010303c03c07031305030420820a00c1c1501c91 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 111369685 1250 111368435 111368561
    0x140304240905031005061c1b08030c060402010804020a030b0c03060909010b0a05060306060714100e030304030f0f05040b130f05010203040b09040e030c06040605041101030b0603070c030201 83
    0x1c040e0150702001410080c0105607005d1030300020300900e51800072202100307007038006144201c00c40c3c00c00410219008005042d01c052006030038407030f000e076003080c4112112980e2500e0050005c0d040281410205041d504c0300b0711004051500070404110390b14181c100000b00d540f00b035840a001d045030b0303030015070320760410310502046810040401e000c075481c141c02c11c107080d04054003c3c1c0c0c4c04030b07041040e800056281d000701799207000b83c40040c2c0b11070b00c49020701004942154018080b180c10030810000060f5100402440600b030506000c600910381e500111064000e0760071100419100048420340850301d40b4070441100d881c01c1c2c200b40919100e01c012a224052445403600000d4140000c0c410307031400f81c210138140070b05074045a0502c071400103580c2c6450003e8a0035140156a241407105105800c003680c2030300c02084c202032020002d04000310749240f01c014400000c10450308960803c0500c00c0d0003903407a0500030b04000c81d11825808a41c2000740112440068081030303400076540340f595041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 111370935 1250 111369685 111369689
    0x105060415030c020325020312030606030f040305092e03020a0e06030606071b0303030b06041404050402040902120d090815061306080d030e0c010309080904091403042409 75
    0x16191050704900c1054000e06001c07510700055001c10700c9810401400c48a20740b02014458403c0c06462020340140360801c1c090202d0380da40103c0800410100741c440008a07134100405e0002c41e0300c0c695072418116080d00030b00c0802c607800356441c07240028104e888140c801249105d500700302c0d00556049401e60481c40f031140003c0106100502a00c400c0c500a009140d20446c0541490300d0064699100548100032030101203400b4100700c000c0c02415810b114184141c6c03802d40d533841c43d1500b030120344902c0103041805244500e032520005021506e070780d001583d4440e4081d205905114548107002e49883c100100e041c0011030740200025000b00c006807810414001d50416041c1d51580020301660840c00318107800c21948800000850103c03c110030548003110399000030306c0c2648264468100420009414101070400c4102400303d000001122100f40044a00103081d601c00d250000c482d0b407070390b20384480a00020a0000b10b09125296101590f550100413240f880c1c00700e101614000418 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 111372185 1250 111370935 111370949
    0x180506010c11040c20010606020d0302090a050f060c010908031902090a120212060703061d06010207140a05060706050a05010828030e0402070f1502040b071203060806090105090601050604 82
    0x204100100c01d0602c1d0303200c1d90480019103465005225004005c103480365240340b00c0c3d0100e80d550301c800c019495050100030140c00d9139242c1507281080c03000006100139880e005941c403490a0b41d46a107400d944180803610f00380107101c000c0c07040000c50304010b03d1540080300c0307040700c11082d59031148030b211013071080710b03d5054010017041c841820700712005044402c4c503200300e0308241c6803184d6100e2000c0810140740b0409140d98081202cac4c0c10110314083c991760b01c2d0354050790002c540003800f41d50fa0300031071542c050b111030a00180d00c000c0c0010020700c08070a41e0b0311494100d140012200f0505c012500f05603c166807100081c00a40d0b65001310541e1280c2111303810440745490b2615282c440707035520001000f240030303141488a40c601080043c00326844140101e90300031032403010070100070340c2130306a0b0480481800118180fa1818480c0d1902d40f1035814010704254024505201440c060390081c005801907001f168064076054480a000b407206036000391b9503104801c00012545406011101135800e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 111373435 1250 111372185 111372203
    0x5161a01080d0311070f2d020a060906020d03050a020d1a04050f04030903150b04050c0a02060108060603120d18080706141902160b070203130b0405010e09090a06020301180506010c 79
    0x145c4e0300c42007404ca00c048021104135022030103494004144080b104000c0f001c0701040c64481480348104040d40400740d101001707012000204104903a008100e518800b50700d0b00300420141c1d00c007400700000380b2401d010300c0811031600b0504e0700080124a4101100401990b0402c09a00c0d03900d8100310360802158020300240002f1001d10000d1140d0340b032001c0070802c0315000304403148540700040503900115441140d042c80494000c0525138100412801450a000900301d9400c00308086900c030211080b005506520000c0c49500800040e4050203049454807a4441d07403050b68608030f82c1640c40ba0102390341490400340c2207001002c00c890000d009485005600340b14031003c1c09079001a40102011060729414880c01d180803841c0320300428402e0b01ba0b9405160b40716441140b00c02a0301c9540c00802c2402d030140818070003030342c204210424860003180d080c43c1c0c82d506c1504540c907100111400804d00390020000007a003000411050f680361610a0007440190b4a800045032121102c203c00350201e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 111374685 1250 111373435 111373447
    0x31d0106120f03031103010608150a03020a0506090d060608070612050112061d070305280b04020114040810021c02071a090309090c130f0b0a05161a01080d0311 70
    0x40b034018003008240302e0705001c20307001ea05103940c0070143c10917808000825005070800003118048139441325a000200c40c10020142103401003000c00c0b0450080502130342c00040c2c1301240381c2c0c0ea210001e0032581c0c428000d000c2c0355114802941c4a085901c2543d012601e02c48141c40c03000d119005060603540707440301101030b2a007251100030281402b06040400d54071030030b04560f1415410f2007110301039805400204003501c04004550408152071460700030b101d01142c3c41400046003510b10796002502440d000070101034180a4618030306c52a03005011174800d001105c50049203907005400451610805220b50564140b1200b00b41d00c01c3c010018110120301c0c902d2401507106e901c03110b4010506504036410842001d0104101c03407030039078000b00c4540700801c08011121803c500c4201a041401c7d480c3c000a1520072907040e2405822058001c2c40300109800c0b0501c040c2c00070b0b44182d960010450001402408540d02074000d00303000f20031080c0200340c0d250f00d8040c021300136400000d00100e51640307041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 111375935 1250 111374685 111374693
    0x906010b251b060903150f02040b12060906030a05060c0702010203090a120c0b1204031107081902030601050402070b0c1e0304060c03060807061d040b06040f06092705060a0302030d031d010612 84
    0x1551407c3e000080d0b800d1001094884402014140403d80d603600b058081c2041c60801080400c02002d00c5d11952146c020a0000b500c040745054110009800c5a5100c1d503140c40180e0031406290a42500010040070000d2584805540300003811301a00ca071220068590301e8800141c801c0d010000500312000010500203032261782c5650803140d0a00980714403d403140a0681404000c2c0c0d024120022403101441c254601030140380c0c0104822142103180100b160b0701d13540d14150007003280300344102c0858101211140401d0754827000c41045801c0707640b8506440d000b0000c10f240742e03940001920300b19004c0344051001a100c02610201d80761f641c2c5c0302481c41f10420401001d801e04503005902d603085088141c4480001d00003511100300e56264550410400801c004125400504120f150503d40c110201010035520f1950841010100e40c6070b075010080703211038a6661000390503104051310002d046038143e211000d54561031582018030010340300310782e0903511103015110340a010310390440001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 111377185 1250 111375935 111375941
    0xd0b041505100201090b090106061205010e07050708040b0708030901150608011208090603010b04080d05040605160f0512030a0606090302090a020a0c0f030801050f090906010b251b06090315 83
    0xa4541d0744008600c0d1700c02a0741c0c18106000c00d55005005a440f0a014400c5a1b003100078500f03000070f802800c125661611034143c8285401a0041060103000107601052003d4407040340c0242141e04045a9524070a2525001d95881126010b80f5943b034001101400011088000c1c201c4101da0748201c030301e9080a4000d2502d256000081310350300800c01c050f0b41580c461034003560090070251682c1e61118681850f260030086140c0788071003080800c1000380907030340d040425520520808403640001e030205240090041d40100c4015000784903a4030221040c0101c04011446045000c00038401540c2d504401c0d6890350090200030351144220001500160b0a0381c054200c01410346086052241c080d252410440300004054001039802c8005008500b443c5c0186008010151144401381c0350031607000e03440702018002c88804400004980f000c0c4400382000018040c00c240340340e0880141e81c6030001c10411009105003021518030000900140619855001c80c0d81204545c070390b540003c2a11002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 111378435 1250 111377185 111377209
    0x30a1a0603010605150a030507050a0915030b030118120c02030c090405010b0603010e0103030822030305040501060f08010603120807050a030b06040e04060b0906040204120206070c0b07080d0b041505 87
    0x1d50b5848500140c40c1e030724824810f0700300c2000c01c00c140d5030741d14030100203055910080c140010302c0010429641d0507540140b109048880e410110b44004503605811000780038280203843d455801c0064001c664211840601c480621951080700051110142a2201084030201940c5904140030b0521203007090104140d0185c45030340000380350004800024100d402c203030815a03600032028014000c1503001480315401c081a0481c425240801c1480c214501c1d41c108002020940c03a00007060812809402010151490440c401200b5440e13410781e0b03008040f148400d964610348101c241500601a041d114004c2c907040c0d84051815140e07010540240000310b01458020104000002d03182d05c42e401c101303006030310484010943d9180070080286801002e44000d1040e0301c10001001040524413407040c8250b0705440746900c0301240e0a1401909203194042441c90034005591001c00c00c0440080002c0d800203c0200481c50380708081c0030440e10340080e40380201c8140305081c030691074890b5150301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 111379685 1250 111378435 111378439
    0x5030106290426060912071202070e090d0e1503010302060f07120c3f03020f0705030903190c09110903070303180605030c182106060f030a1a06 63
    0x1290941d118090792401d00d40c4010b2408901c0e24440c41e83c00c00005100882d0008034070001000c4642d1040d41825a41c0709101c00100100411806015018000e01c0702d03900501d42c1105207104c0780340020000380c40381420015000040c4191400189901d445080c000f46840c03c01c3e05617085a00703590a102d1194807005501401d88024070480d40000c7d159112140e03081d035159a0f180100b042454400c042c01c044050384084920360310385e2144050b05043c0308903003209a00e082c0c52515420248107800030700c03407840a600101c030006001024030030008000c008108083e03017100d41255902d200c2c0c403100484110001c280b07602c0710004101070080e94108200320448034060500e081c24001c0060714202685e442100801c0c1e542c040185c10909074078040000300820b003003244c614a8903045002c000d100c1c1070b541c00e10036516265040e10075204c4401c04012903180303442c0151169207980125076900300440e10b040c8030711f0342c80c403100b021401c0129101c1511035101000d0101d400c00c07045420040140113118503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 111380935 1250 111379685 111379687
    0x80a0f0804030f060912020c010c021017090109050d090b040302010c030905090f090601050111070924061701090e060f04020f040618050705070b01030809060f04090e070503010629 79
    0x1101040c41185042c05884c85203100141c400e0180c03400c0a2000d03a01039203002550001c5c03100110b01d0343c20103261070b0384c1a4100c030381d030444e00c40d641003d076862121b001d821740c0681180d80410444c1101548240301e2540540308880030124020012181c450f5903004a00c8015414001000154050080048154480e05000390600d4507840400c42d030190881d0741c1c0344030244000500984407000c0c044180074100c00e20b41a5134100000b0f0803503654030918420010b00c141e80320309282804003207829640c0070700b0241400ba03030096038520f4002c0c0741141c40324890f14662000000010000c0191180d40041052040a408140d5660451280181004000b640c000f6580d01c07151105030b596200305009403010b440304094400340758503034200300e8a000f444501803100420400c3d021541095060341140c4e072058540c0d6880340000c01140250040b03240c1d10034101400300d40400c6000450304003000301029a000c84107500c0e030390410142664902e00c1641820307941e08030811150000d0b568038a0685000b841c0c22 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 111382185 1250 111380935 111380939
    0xf1d030415030b060319060b0307092105030a0f08151e01120e0a050c09011a0c03070606120219030b07050a030902060d05041703070915172e080a0f0804 67
    0x40362003903204890b0081100300c0c01b40e650541070054401c0c035001d0100744041174214500500c01030f0030074109000e50320340001745000d80358059000410794000c0a44c05425280c4a603140030300170305951500e50241020070f07911000204602103801042580e00300041c461040142c1603009000203051806c225810409104d0351014400190700400a0b02500c05004007180142401e010742002d50070780b480740c0b2a0740240010003d41c0340d8004d0b090038464001203c60f03a120301482c10076145201d9002c00074940f0303051440000c0d406400041c00703881d05000381ca03080640d1203203400d60750f00c00e401c6c1e0000034030740c25000340071403006c9108001a0203402c410b414001505041d40e0001940c0e80c01c0354650801d155200c40800082101008144025200c40030001c2c2c114281443c1c060405180c038041e00e1100c001403102c40d010310340305036581490580c0e0302c1214007031800d040642c1070250481e030000340340e4507080780c10301c6418401c441c90000807a11804043c01c40d403545d6a07956841d0005100302039a8518041c000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 111383435 1250 111382185 111382189
    0x207060b10050a02010b0409080a0810030c03050d08010b03061e0307030503070c0609080304180908040e180d020d08040209040201020f0f03040501090501110309091801060303030f1d030415030b 85
    0x1a01d00c440d60300d6242d541d1a42d1000e8002420f480300d0b8050b03d400740f0700701550b46000032188800e0f01d502c40f020341448170305552024144908180c80f5803000d09900801000042031150118002040840541d42c1000683e00d90701c1c881d0080c813040d41d100340c0001081420300348035000a00072411211006099403121503494480515642103140d003528404050f250410003140c220030f110008092280145092914107034040400410041c06100007545441001d001c0002c02d41c1101c2c042e10b464101d10360941400184074200e803911211401181c49681e44000010b1b00008901800c65060b544000896580b6400d10030325041c05441281503100f0b19000c01c88003041480200a000c4201008645032850003000500b070301307425400181400784901c01c41c45085008800c8821102c010f4410414944400c103403401081040450300c251940b82c08404010558190460f503e08a02e05200784003400e510302c01186d450080d11045101d0794810002000101015042c3e501703420b0300d07410000352002101c40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 111384685 1250 111383435 111383449
    0x4110d0c020105160206010f0603022505300a03020f0d0e06150a030c0504020c0c030708031e03221401060e160f0503011e03020607081e16060207060b 66
    0xe40c103016035182d10030010581540d1090404084c050300c0108529454011505003481060040204058002450880328411600d207103000d0a00010300c1d812401c440d040a640381c1e014007110341c820412220701c402c10074035a0b400211000009002203450301201c048103030000d60110071490b050506c18410ba010105803031080d083c0080078a0013038041071400080c40c0055131607074001c2c1c0e80b04d150a082c050020800130107642054401c103540042e660060810113030701d010540348000341e141c0315691010a0440d40030000c0e01c2541c130b2120184405020040440d00103010464030320b041c1e5124604584010580b00c105040114091000c030105441544021429208a50003d0801d4108001030164081310006003602d10000b074031707040700f0388c0040382c40040c0035100c103100303030500c03824409240140141c80012580c000c550061405641c0d24040c58040303107940008008918200007503121010381246801220032a070588290b07051a04940d030340c1e090007500414015903402d5034a2002c070200f41ca07114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 111385935 1250 111384685 111384701
    0xf190512030406171e07020312070905030705010e0d081608040b1902240703020f0301080f15090705011d0d060911031203041203020906040909030311070308040204110d 74
    0x40d018640e5942082c40107060302e00e100314803802040c040320400514500781c80d90000003203000d402200c4683c0314081300320300d1402401c1075195822100018800c00031b801160910407100140d0945400c1c643e40c60054645000d1411b42e1131704242d41c1c1644030001145000100000710901c0d040c01e403101d40f0750b250078070150041c1d0070a103090344000072504001040d00180104040721031004040b911612003680760b50480d813420740340c48640f040000c41d0b6040c0c000c1c0c0550308040d0318000d045840c0d6035503065140c1d485540681d5090640649981600090301f05c400b040e10512081c0c00408141c0c0ca4279004580d0b00a86000700305240710501a800c41503542e80d0680100a0f010728404682810b190518180c0c240d071800c00103100780c0c8109490490756070301d030041c0e13980306030070940d0303540c44400c3c19000340d0192003040c1d1116401500004d000c03c50b403030203030f00c9204518041d80d0104032100c404448051244950900a0003140303625001800510b01500202e9100100c0c0748a2070409500d0301c0f002e81a1440c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 111387185 1250 111385935 111385969
    0xa0908030a0e041a060711010e030102070c051315120302160320060315011101060518040c0603060b04030212010b0a0906030b15060a0809011e0225020f1905 69
    0x21540c2c280646010b01960a10b8020400191144d001c5100040c0301c1d4810100010140420a10040642c0c4e0095402c8205001c016000b559210024902019581014003a141c03140c0254580151071350b90034403583d0114101182030302205820088046526044103501310218800c0300c020703583c01c0d5050144a0015441421100805034414010045184c0f88512050155806004000030007920f8982a04840c8003828010a8400b030401440e003d00340603041541c2140c105070401168644174005540314a0180c0d60404055403981400c6043e1001840b95020301c09060000340b0251415100c04105021071070700020708850040c01040e00000e2960010300d4469880a00b04240f01d103418925502c2480c0d90720f01045000544006030311405482c0e006030400503201c00080810f50254010b142c241c054416011141b010b03848001d010754070904144007a96019410307000d8403d0841c1c4100703155540117021518440c00b103018091418076490081c6030800d0780c05400926920f0780f0003911480004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 111388435 1250 111387185 111387197
    0x6120105010e011d010c020105040f030c0315090b1530070603021c02030c0d0204030813090c1e05132c01060e10030f05070327080f0a0908030a 63
    0xd040300141281450b01c2c500703070502c408441030008000c02d0721800a0540800d007840c00c0c1940881c001240c440c029604aa4071104880c4d05c0030007401031180c40181268484d00702d8040d200c040b03601d41015204421001049009200d010a1440745141c902400c88000607243c10302d2860b0300640502c0c02e00c80d110b4a001c50710101002c0c10300303081d001e001d10405000b8130b09055181484200103541c00c0c0c2e08000c1c40180c01540440410300c0c07001030104882d9403100e85602503440c0c42e181c0c01c0c014143d52191050384007810a40c50000fa468800340500d4041d00401e807144031100c01c4191036840300f0200c901e610307001c1000800c1144118401141000003503d2070400d0400c051684081445800345407000a00c007407010030004016255000c401ba8a5054081d80d44910401b190a01078000e4420803491800c410b051008011071154541d104070400810300c2250030a604000e990742000b56950b0a010341502c10800c00181c0850411005140c0320006103088840c05650705403031421504103140d2180080c0c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 111389685 1250 111388435 111388439
    0x90c0d0c0806100c170c0703020907120b150a110304050d0b06031b1e03010207150b030d0503011a07110603012603031003030807030b0415030501140c030103031d061201 74
    0xd1001218010002c1403c111040f004c0300c1e10b52032001d01200d5025100000d000507011044942030000c00004d5a025200c41080e0401e208080c00c450610209209142e16040c4040399620b4084084540201c0c4001014030b400c40310795084402d503002c00480c081e14402008000f825440ea06181070b400c0740142d0846000d810321204150400380115a024124800395007003544c0741d524074a00d04070110601d10a602c504d8501800709029010b1064040c00341001d4040c00540c04004c5e800c80c180c1d1041c118142c54060b203046c3c1094a03503010a010300b040d254152580c0c46540305160000f0560b007409086003141d09644000010000d0348244c010040c00c0105018451040d4450030001c0743e050700c44c401560452820400c15401c1d0a80c82c8005010001000b01060798203000b036101500800014000344950500d5031652207200c3d07901e00c030171901c035031810f19406036181e100340c2d55a0045070020909071031a4a19202203810111f07000141c2025103130140b202c01560b640300002c0c1210303441414140343e158 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 111390935 1250 111389685 111389689
    0x30314011409090c0306070c0f0618051c0503010902070c08120c071202060904090809090c130f0311040506060f1207032304060c090f0b03040b0c0408030306090c0d0c0806 75
    0x40015000783c3e0b59510131450880c10390b8000c101d00364040111b203066038001312a81441e015a61030380c08007074005485c001d00c1702210706420030303901e02c058003c00c1210102c50f2000307403c85210780141e841c0f0000600c02e10040c8034210b03190b0001c10b1498001c42e01c0c0c5000a0303c820a00d42843e88075500005080d000161840980d501440620010101c81c1c07404203031685c40b6004a1141d110b80d084c01c078801c0c0d0703844501d002040707803400030741d08a14409400c01217207160801211600c0d0340503081020512000b9100028910650400700090700e5011001c403222030707060003e110140402900003580080d06000c0c1c549160202c20280448010144000c0901e007030001c8083c0454000c50307441c10a01e02c29822035035880c2d00041145820903400540020a20a0707030000300e503600b82030342211003d2b03c0003c200043e8030f0801d0003c0c50080d40200b440b075401d6160151049aa03210300d10a00c0b0a5070001d0000806a181400c000b03a8880d8103508110b2601100ac2c120400b1074820100d09408165008184481c034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 111392185 1250 111390935 111390949
    0xc02160e041b030305040509220309050306090d0207050d0c0317120a050603031b190308011e0614090a0b0309060717060604050f0d12090e0a06060c020d0303140114 72
    0x485502c2c2010300d1030342c2940c5004100303104a005190007030ba40c1c1c074041180c0100b0b10b90880e242ca140c80c41c04410804140c98001c001e00c0c100c1c41100c0c8030b48030f40004a5110f640215200c42026000c1d002410b0307051400b4140400c2442554090300c00d94a12103000001c1004d800035000c58218003000966920b503900c141c200c1c031500240a0058040c42c080421189440001c00c4610442c6129031120404560310302a42c6844c01011200c20242c185a030310310205034001c0340f120b040e59981d101201c112481c0703a44c1954104414881d850026603030088401c210901d100062030f40c140080c0004401c191104800945a841514205070715031026040000590303000944d05488042d0505001d59400c0120002e0840d000320302030a4882c00801c03c12003c44e40d9408070030101c49030711070031480841c1e0003154098840d030520702c207004680904400041e0280501d1080509441098980d1404c10700d10790240441c011002e103044045c1542c40e07444504a402c02100c01e8008c1c030300c00d005000144c03c550240221 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 111393435 1250 111392185 111392213
    0x9060406060b0403030f120b10030f0e0613140102040819120e01140f3001060804020904110409020a030606091437020304051612030806040c02160e04 66
    0x1034010180f00500000780e2160316203040d240945005061001400c42e9000101100c0c0445030f402010040307504580c1d40c040d0861401012524010410307694409041c0e80c8850f01283e1203007600341030390a140d001980c40c00c000d42c20304942400050425072502c141c113184c1070722141d03d0300240300040900c604000e601900308040318078514150501c1c03001c150011700b82035260702e50620b2040b030110b085d5a544140744150340b282000180d0010011440d510b4403102808110501ca6a60090314004a032050260003030301d002da580070703280002e19030b9181c0302e00e1001d0001c02e056940c00368640d01c014025940707220400c00554090711300003425500d05001e4804a50380c060891a000c426181008208400600c2c03089880c0e4a040060103208200420020040aa140c851501c0b9101205000a120000408188141c1d8609407504003648a454100750315110b03030002000581800c00254841c1856000b0450921080c012162110501a800c01050710300c0c1c4c12a1202910744000c2100744140204810f80d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 111394685 1250 111393435 111393449
    0x20a06030c120c0c020402030a06080d0503040506070806040b0904051e0706050405040504020f1804020a050402070506060409050c0604030321140c030402180f07030b01030515010c0611030906040606 87
    0x2000845080c003070242c0c1c58224480102d43d90f9440040c50890003074000c0c41c0702d10f0740280704558902d0f000100200502c0c8a019440c0c4074814100c000d05414000c0041700e00481d042002461103580c4c08408460b080002840d480e00540c545203010900d03180c090340c0038000d6124030007406d42032002c45c0c3c003245240c0070459280401d0b07107e0b02081000581000840e1b0685605940100362960345001040e8046040317004160041d07102e8031a0104440d460300424010303882101c02c0130b45160781341c0810059003e06507000d000340c1c100c2008564036107402d40c07110180d51b11400a5070b81032482000011283d401c1a0b01c00c1d0042841040784482c100341968811030a00b41c480800c02c0106802c140015400300d006100d865034140001c0850255034480441d480c0e5500403003510840c41c43d018031211000c61082d0707401c2c004a82030240780c508030f6020340201c5210790540704551413901c45040044606030b06000e41955101d5030b406172010707024444001580300741c98010080565090030718100c0101c81241c0d00c146 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 111395935 1250 111394685 111394691
    0x3030f0601090f05060d0e0a08070302150c030c0a02071a130503030c0304170304090c030c1b112808010b09070203040303021507021608010506190f050d05031303030c020a0603 77
    0x2209940860307210205913030083d41c000da25016020340190041c02c0c5060a0089441204117030300800ca1114001d0925500c248d09840348002d5140d20fa01a0340070a5a1440c024041400040d05285000c0080c0140342d006204031b4070700c1d47c0e0b14000c5a44ca131041076844040f250b4002581059003c6140103d001032038103400031440c040003420303455100c2c010f501441030608003208030806501d00070410744002d0302c1420b03010480200e14000c060001c0859801c14000300c3c900c000c031032072074000014050342c0048d046100000030018500400400d00c2800510219200c2880c2c5005600c860041807140030300202e40000581c070740c1c49420058a01c6008000e8421540204000d200107507000c81c0d07500c0b21074403c5151001c1600c40540690030200300c14860030f03a0303841049000400403415000940201020f582203000030060b00c4951178000341d64000c592360b1481e01d91080000b800c2801281015a004a05607801e041d08080345e002640701d5940158002214100e01400754a81b080c2c11000508a07801c0030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 111397185 1250 111395935 111395939
    0x809190b031806150f01090816061202030720010f09051501080303042d05030a03150b090a120201091203020c03010b041404030c0201030e070b07050d03060602030f031902070503030f060109 83
    0x24920b81342e00d03d40042c2c019601810100b10ba40d0240880b01e02400204d0282d85a074805802c8074404a4400e115000008160340100c000d1151036200326400b03070440d0347d11403001c84e40f0080c648000741200c05079070580b99a20031a20403444510312533034609605c031350f02030003016025074929101e01c0010b0700103c40a8004009200010341ca02880441420110203081a031000c40e80a41c3c50280c00444090502c0c0000148040619810707800f00140010154040314055110860079a15010b21b180703c0390080c04411041c40020118800c2c4405d0510514100c0c11036500c2e64810180200940400c4000da4000c1d51034152502d001e0113000e1409105a070b0400500c041a100100f820340c02a00c05000d0241e080b40c16801e5900c2030300030800d50700d8048c0484164039a0303078103072800c150b00c91401510ba80c00b655001c5950740d841380c0200403c441c4298000c50401000008030301e02d55001401c10a03c144103241f0300100c01340790b40045c0040c5405140519181d00c0c0440d403240d40084000d208070304101d840780007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 111398435 1250 111397185 111397201
    0x70320011104120809040f0207050106140102031804020c0106060f090b03130b090c0319020a08030309120310030b0a05071101060b03220605040b090d08010605070809190b031806 78
    0x10341c0d00300c403000da14007042c0350440c1c2044c0d500c40c801e5400964115091500070250820705400401e0304520a00007004520340d1140614003401030784415074010381081141c562039580040180d400c03408020001444c00003031028290848a00ba440000440e0450330540040c98100c0d41034001080004c0c0a0362a52401100400700782020400050100303036403002181045004002591003500054216407140c4034002c4100d90b0b24801a0049100b0002c1e00000320351190b02000343d0b8080c103c8034000303084040c0d00a0703840100350401007041d01000c0300d82900202041e030503004a8051003184400080606101074010300301c0300d4501903401c190b0f0610000708a011000c00459034003001000b81e1200c001c00008010400c20781d0203030098802c905000900007809040400706025061590450b0041c0310481000d0b80c0d40755007407041d40301203075007072000e100812003000c000d00411000410030a4030828406000d502c0740000c4d001400c0540c004010403081da15102d0903038940200030401800b251a00186c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 111399685 1250 111398435 111398437
    0x301060504030b1e0c0d0612120e011b030807080105040902011e0c150606020f0a0c050609010504081e0c06070206030105131503050105090105070905091b0c01020703200111 76
    0x10008019035030580c0004c600702c01452466054000050507422a402c0c15108207226420003d03142001c50b00d00b80d400111850816820000c0560008603c800000e036250103881060014080a05000209071301c2e070640030310000300d283e10707a100b9140ca0290307007400b940080c80e0400c160000d074040c51610b105040035030380044450a0f1140348849002c4401100a0200d9013218030b610020404e10f0b8101d82c0d0504422070342c100900341c610702e50881b0b2001b102c0074629591094800c0000d000710800e140d0500460500c03200a1280350010b06000b8901076031034494030b2814031a019031441d1010b030740c40c561365900c000b4002450008011200941410744079000a51903200610030380d446a880f21454409004094000c2e1804151100014a03410b6036801c000b40600303000c42e5241c513a5440d1000060649014402403c1900d01c0a843c0d40881d40d202909641002e072400c03100d1b114a8424091524111424002421000e100b660380700c10041c0e1900d100c18424585014011141c0d0402440c0e001b144c00d900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 111400935 1250 111399685 111399689
    0x140607050312070201020c010f021206060313060e120d0e1507020d2a030203030f06040203040809010c0201030e0d12050c03060114250c0503150610121401030606030b0106050301060504 81
    0x702c20060b61541da0003640240310303c5050020340d50030f0801030090381440303074040c050020802e81010403c0c0d030f6140401c44a840700320780f40384074810b210b110f000104a00d5800313031b004440440300325202e503902c00e50055a65044000b00c2101c45445a0398004241c405101240604a911000d94400e08150380f02a4980311400d80c6a13003003109400c8036030f0381448004840026410314208188847c00c0701d060082d140c2d4411103140c0085070f40c030b60101d10241441d2007140d00c2a03810180050070f14a50500444d800590141c050b0b04250311384204001e201c02c1888522040d2503d40c46038910341d10b08800580c16200010034459000009108002150340c001c0c0b60f842da280204100140d5840c25081e9170103422003811080c1075070100702103440c0200290f4401c880242c0700210308860400b15800c407415489101190800d80011414030141182c90082440800303010001c3c4000c110038052614440450318240d00503554680c584104206004001c1d84e25030141002d40750840c075660410102038500e02ca07034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 111402185 1250 111400935 111400957
    0x901030e03070c0303050a200601030204020d201c05060906100207270608010504021e0409060f090c0501090b030402090c0408010203100314240907080d091406070503 73
    0xd5540c00320010301030080350b8209600c10f60f5221880e0b100d0400800681042c80c13000e020568046100781d43c41e01c5500d100702100b04110090440ba825035003404040e4001f200316030b1f0241d80710442100341e581410b00e9030009520080d0041c0d01e40300a8802007810038900040104114503050034000c568548114403940040150303007148419080240492401d184ac2e840700c451282c4000c0c0b0009140380c141c1400d80440880e5606221860b2201001c9003250003d0750000d40c440c03207180348000c05014140507020213007001800019010b0741c03a110303642903a03140c0e038080038201d55840000003000304031509a0060311080c039003520458180f41341851070b8400940042c1c407404284002074075400006081f6030152008800039502c03424039011070f0200c2c000d075020849621000c4a01d001c1264030000e081d8880d20800c50115a14001c0d200240000160241c00c600d09400345800119150000f0044410040c800c0d940c0d8100ca58a00010300030b180d003403041c0e41407007103c00b04075040101c0c800105440100001b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 111403435 1250 111402185 111402191
    0x518030904110c0a0c03020307061d090402040623120c13050606160807050105091b040b0a03020d08070501050717160207030203060a0903021018140c19080c010c08090103 75
    0x101c9034000607103015860071000b541c40b6031401300e010082201c0d414400c4078420744c00c4400307080c0c07100d900303903003034005413115081c0e103000c034901c030011850021700c8290028005000041c44544400b520590600c4d00c1c61560701c580c04004542d040703800c0003160090101d50900c050050034072854000307005040d500d06c0c43d0250b207885002003100e50791075004441079646052103850002e620740c50040c115401c0b140e402c0c0c4480d440c0800003058031340b0109072a84942290150480c0001c21401041700602c03030352558542100b01d041380400182c450004201107507005400c03003500d030303034191504500b90760004020301c080241030a5500d054407614090f003500044140b09100b04100302050407864140a5400654940301d0710003403144d94040f81e80000f1106029500362900035000b800214192a01c81603500800410181302ca1701107649051071040e1424818265982040840009550284000000c0a042d039480b2020072003101e04004051280c0700130700300103501540648542c3c140c0d0142d81185070526403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 111404685 1250 111403435 111403451
    0x30406270b0703030e01181a072001060b0f03040c0b1309230106180f0803120c0d150501170f040b090a06090f050d050f071209030203030a0201050601030518030904 72
    0x4003d401c807210004103000200015516000b00c0402e141c007802d008d80c3d2004c2a01109059810001c0005202c0c40c80f60b215400c0c260552103540814082d4103034181e906542c1c0340c4001c5000f140c2070008080c0c03440a00400d0340c99060905140c2c45100050307000008a00c2d08000c0c441d0261300c0ea01488088036103c0e400012507440000c02684401c40400000d0844412440046035954000c0b03407008140c03030300d203560000e002c1e16481c0c05d4100e03040c58041c40416500a11405401500301c404180c0d00070030a00b503a82c00c2c0075040e046901960241d01051030303010302099080c00701c0c1d44d011180d46c0b00207032501403294203410801085040b40310003031700103881c0310000340c001562148100270701008141d1190003080758602c5401c0c15000010030040c00c903614010303030f000107054a1060059800390400d0f589414584006603440e81006e4640c0742c5050180070bc072480000259a051010382041c4074560000b0401e840c0c01c0000504a4070000e2840383c440003586204c0310141c030008150764040400359000a0800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 111405935 1250 111404685 111404687
    0x31109010f121a040501050403030b0301020403050c090703090b01060207030213111905040f06080610031103070807020703080d0e0708010c090612140103150e01140610120509030406270b0703 84
    0x40c421400703030f041010040c0240003c2180542c01103108034005c1d42d0170826640080205804d03031080e444041e0441e400250503450600c0c203000820b03000181814000b40d01c3d40a03aaa10a120034240d1054015801c426410819801c1012585c3e6041001c9401000030300c11000f40c2c15420f00034110090710344054052984160f03400390302102d02a2510203840a0303c15038542006240c1c80c3e0482c0d08901858001c3c103002310050082c0107550b80e100040c0c1d1183c2c01d5558219084a650400500300011481019400400701e1141002090320040e489400f0528180c40b500c41c51400400c0e511020300740c0c1c502009034048079400805202075800910b000308005138a01d248101820400311000c1482203854000002c00003110003c0200b42d00c82041842585034002496003242c451000380048603a030080002c4451805e601000381204a07428002d41c681c43d08841101141c20898003018541e00c005418003160342c01108208144800c58807000b000215000a240d01d00d0140c401c8040140020400380201 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 111407185 1250 111405935 111405953
    0x6020f2803030e071e080105060114030a09060204090e06060a06020c04020703020f0d0c020909072301030e06070207080705030a080d050907090f0b1008151c0b0a06031109010f12 78
    0x1503c1d080d000c484800b40c5408a103e858041d1190849820740802000119918180103003845400140c5a01e5240030240d4007003030455000400d6510079035078512400000614038400b0300040c0c105020005103050404210620780140507000d5449568610410001241e0006032400460001c0e0340c00f589485261505a15051030a00b4855190155a044604465004014040890080300c980d00700d42c944140c81341d1908201d0040510070103443c1c0c0e44043d03510280c0101480518185000180006044c2c0040d04101003554602c00503000a58100106142042075a01503c002c0b03010306411030300c694a040051080d801803082064413440021190300051000800078546140c00784038004922415200814207440c042c0d03c20300c2e031491000c8050340f0804082e1311031014550230b49086040e0b80100300c0c5280780c42042149000c0c0e102494800100551759030fa004c0c440c1c00c503021a00d9411850560006080c00c002c59002d40c0600c00100304241c403064030340044800c54034150604038000d0800c02aa = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 111408435 1250 111407185 111407201
    0x30402011106060904291503300a11030a08100503030f0d05060102010902060c030a090e01030f03030902030c15040806090a0c0e070207030206070803100906051027030c06020f280303 80
    0x5402000c008110540f242c883ca400b4803200201c0540341c0022742c019620912040c44034529100e606800501400d03c0b07401c20080c9400602070502513140c551007100c1e54038560011791080002071403c400e00091802c0403503100090135007140510705040840c00c0031851400380d0040306009541b41c4000c1481c5034001c2d400140d840380c001d07118a0f51400354182c910758951000c45043d0000d29081c00010f5101207003104c0780e043e01c2d805554031001c1081c5840031000b40c401072406036414090a25408031070703610311884012200502d503131940c60b1746c9090a414208003005282007501c0d0031021201000690b0b49010b00d00392154801d50580645403076070102e00e004582d800003504404001031050502c0b40b0074000c0c51140c0740850703040c1c42c0151a01d410b038017600d4151180580089407808042d41d2540604000c03440d0105c161700f265007019a41c581d00c11030b01c001e035006413202f40110406100c00b40c0c2c14000c504014560348000c020380300520030943d048040840c0c503200140e0740000c8104c20140b0030303004442 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 111409685 1250 111408435 111408503
    0x10b12040813060c030e09011413060905090703141203010b030907030503030717060d080409020d0f061710090203070e0603100501091508061014010c05070b030402011106060904 78
    0x40b400d0b240c0401600d00844040300790042404e000c00440985008805903050b1012031501120580950003446000f0070600440b20255403100c0b004503d803485032061521940300400108010751031814004d030301a00e0020f0301591600480ea080c0c9801a8100886e0704440001a0b03e6035079035251140756060650a400040450100105101015a000e030061010000403009035640352600c9080200c0e100d107007400107003100e200740420414100f0b0b90303016218032210b07098040341442817011001c0c101c456a40290008424010000442e01001c1041899245641101300212255900080c1c4c2d04e40741032042040c0c103103030780700001c606480c18005041c01d100329030000c0c0038030350310b4200070000f41c8155851490f00c165410000110f180c5c002429134016459081c0c42c04046052054889840e4581e107200c60520078628100e500140c0c0030440d00b002032184000f0940c882c1458030005000c401440228486540100244102c5584031070b40c00c0d030001ea00070250181004901c3c00c0c1480e00f10613180032a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 111410935 1250 111409685 111409717
    0x40c0e0303030c0f37111005091504050616080709030836010e0105070f020d02030f070f0801110a1d1c0809040509010204030b0112030302040b040824010b120408 71
    0x812000c001c0c04064410300480d900305c5c00920f8103100484d0304807203848904d02158404000501c103c40780d6030180740c00c540c0040a45d00038034469040c0c07a0f0400800d480c02c03219a030068040200a02480c0135450031503000385002c1400d0304000744004c104005501003c0c0102c0b40000345860ba544c010040c1042c0032080d101a0329144104482d41d5898104141e582408210001d01088003584908200c4220a07030081c454a00d03855a5002d01c808181480400c9806103d0b54601403240341d0108000340090020355800c0f201141806803807804d4800509100c441c1440038003030f6080307883d000050151044900c0c06080d0100e880e13440001d030013400070b800c083d9a085450403142c0500864078010300101409440078031190f22020341d028200c2c030441c84050305840c4080014000e40d0307200189410304074043d180150030961201800843c0b41d002e9031214520781d001118008240e00342d4038001c2c03101c40c020800395446601d0101d6425031b6100341515500c4296480c4001400c2203508000da6081d050260903032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 111412185 1250 111410935 111410977
    0xa18110112110708090402160b070908060106270f060e0301050f010302030a170705060f070e03010c02031606020d050702010c1209030903021c050d0806040c0e0303030c0f 75
    0x802505282510a1800954000700c607010504841c058801c107645046400c5140000a844040d400d403c4041c1c0c05a000783c007009540403409510b41540300c81c074000c081c40019400c2c0880c01034040000c1d42e10000ca00d41102004120583c1c002065102e82c11104103000c0510501840c44501c038102078000b6103084007040340229410b9440302108110010590003040252640000c90b0740090382444000d42c16842182800009103e0404241c0e20710100c9803514244640b46c0d68660400004444400906c03551b00f0812030320640c4a626003a5110042c0c1c000c101d1b10f041128000c0d00e0748120040000d003200034135003500070041c0d640d040382c41000e0321103800c2286003040e03640203018000c40da40f2000040c0c03c4201070501010688615800580d02da2101c6050074916801c0c08080c04a140002d015103901e900904081402403225410410080d81d40c40c500d481d110303007004110388130000104100701c61b81d1304903200c680380003048940250320b10342056211030f0740c0c14542d145841401304100344c985441c061 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 111413435 1250 111412185 111412193
    0x5120114010e01050d0b12031308010e0705100219050606100e0f121f0c020f191b120309031209030302060f060a0b0f04050f27060f03010c0509030601060c0203030f030a18 75
    0xb274420842244220f000c016500c1003604e0903240a06040412500841c0003041a840c00c00d0020001403664019102506020340024010b0f0b0070100c4140c2340c9400100801c8114a0001c01c1c910440707001e424025503000e100e10102d80b115440c0807549001e8144079071100c0c03e5880800008880c031009207640007a0700c404000c0c40000e003040420a00142c400e0b00c00c540301c448408152002426907039600c501310f0410b10389608040d5954034a5a49004080c080042000014640740701d507194000c0c1c0b81d40140360700d98a040051402042840e00c100a00850140b0000e580841c00c40d42080c007070fa035080942d843d5500007a01c0007006510620b6442d40000302000d4100c0e0510140c802c4840846050000c07a514000b80240300c5004080325492584624401034050428940a504940042d10459800502c200401c9c01c4400600d003840104d1341c08580e440075464104442409080d071450904070080650380426640e014a110b420000440800020980c070981e0f4820194500703404c82680000c8248c1c24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 111414685 1250 111413435 111413437
    0x6021c020c0c010801030f120e04020c0a030e040b060a0309080903030313140d0503061c0618020a080f0d050a05090306070f0206091c0309060906060605120114010e01050d0b1203 78
    0x1070400154001c0740c008503015030096000c43c0c100d030782086a502c0100505e5070394510110b080c00c0d000d0107121242031000701c5600c41c0d20107050704203480c000500c00d80c20603040240c181400d0100d01445141014010b964070740f5901c1c20b40d0316601c0076003000f040f107050a1404402c02e01910000036014413002c410042ea0090b565000f02401d40500d04010340941d070070840c140c584c103c4007800e03800700c1c00800c046800c41c1006c03000c06502c3e420740c502c000300308c0f9001c0c1d0700c40c0c0c1640e814091402400da619110729066203445040340c03004001240042c4030201e1740c0d090068032880c24250307010034860017241c1c040c10076004008903021a100102600c0d20780c682018050080c20145003007400500c031314400500ca0030700000b21240c00c500f840401149002802604030080d20040e1011141e59441d80001400a51035001d044007910702a229140ca458400b0501101500141e1007440061741c04040e6108691304030142d401810001c0c60300175075070012544481c0143c14844040340d044002e240302c0079450107001c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 111415935 1250 111414685 111414697
    0x20c0a0f0c0501110d02060f090c0409060b100207051e011205010f1404140610020f060112030f08040305030a0b040b180a0c0306180906060f0801020a020c1008060d06021c02 76
    0x1803202c1803c4c0303070344241d8541c0d079400c040042d9016904c440081040660032440d4140d0048050049811400201020400356804414100d4820b03403941080c007928648621801d0024115200a04c10f1a00e0715001907154042e02d45041c00c081100b5111107240e91040508030f0845880c1c50081c0083e50790b460030b40021400c0792140074455142d01110481900c0c0034022082031340041012504c46480354020132078404020502c40e8150702c5006413200e010142031101a00034188400d5240c0313a400c0909024002802c0e4071602c0041080c80710400000903005015241c115190f1100040c4958900020038003d12480100e02d03441030101d580d0904001c3c03880001c40c802c80103544140455a1480c0054056505d1802103108060708405101c00d00c3c0e9803070380400000c902442020a07610b0340c0d0000c1e401c2419040d000034050b65000030780020340c04e1701044003986000c1d00f60746c14450190341e61402403103804050102072258007150b02c7c80c4240310b0701e901a035124601038816000c1b0b0340000141440203601c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 111417185 1250 111415935 111415937
    0x705130e0a060b0412110415030b040215070506010605030405071802031506040b07020402090d020405010602030a11030a0e060c10051005030c04060501020c0123040b04090b090403020c04020c0a0f0c0501 89
    0x540040b4841e840b103c140c0d800c8900d4110140d05441c050b640d002102d030740098600d60055914585503400340010000a03000b90f01a80c0303041264189401803001d041008282a14994010083c1400203040010030394112060b625209032251254a0a1402c1a01641c400d42c3c0c81585000400c28461241d4000d5000c1c040780d01e840040f414100042c02614040da01c40c100509006019000c05400c26070006c00b18080c2c01440e4100704400b540c006030840740b0a8000000681c4082202d40c06d0b6500482c0040311303901c180008508000203103000806a2042d100024045d100100c0d0280b101541044855800c90010750144500d18210100100050300c52040c68880d00c2001d040c0b00741d9080034440c540c191601039010b8116800940010b550782038112948005800f811035500c2c0c4845064405040030707201003803280355a2880e00a00d001641d11114150348941001024480041d40001d01054160000d540143c0ca4002d01d02d00d96040018030700c0003138410301c022451801001f800420501c2030b41c000b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 111418435 1250 111417185 111417191
    0x50a05010e070c0c1206020c0f011d03030f01060c02120601140f04020c0304092007030c06050105030f10050c09061306090f120219091407110d080f0705130e0a 70
    0x50b018220b540ca00d0aa40162452009210501c140c0c49501103011265000324005403401d0400f00521340303030886140e003544059640c0c0d49004550000b00f02c0007080d47c040c0700f0085056081050003100020010b00c541000e12482d0403603201151a901540382c44091020b0988040e582c0d1070950150302c490555005205903448825040d55113410b209503030384c89003101c00441c180750410150340010b0800d1025039201c1d500024150441c82e14050040c000c2e184641e6500b00e611a1614014040d04c0047e0000303417090700700701c0c091682002c0001300c901012402c00400f00c3d080d2107918800362507214400360107070040e40000d03904440721800625281201c2041c3d80e11504e690740c036501e500744a24240550507005108854420141c60036408580300c0700d84070100034280c156111104800c484003090346c048020a0320040040e0150070485444111403000b001d4083d404900e4002044550020035200d8494009400704201510402c19603581c041042041c00392a9121003242001b400100c407a513002e242 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 111419685 1250 111418435 111418441
    0xf100314100f15051b0d0314091c0e030a0b1006050a020601090b15120619080d05070609020306010b0705060c041503091b0902120c0f03040212030706050a05010e 71
    0x20364803200e08121250b50080380c030303450b06005984420038059120141000800c0c0206071440d035807428224500f6005c28000c0c4862103007a20041d06803a9940e001c07510300c540403000c008004801081c00080042c100305000060803d0b82401d0324a0166485a1a014403503002414100540012002c1c001d03000c0d100310081c01951507030106d0359032144200040050f00074000402903d09240c00145008000030440d442806101c0150030b0320360007040b00400302a942d032041c00402c0c1041c1c0109501540c11044100c2e000e801c0844896441500905200400800103000d030240083c40e0b01400f80141d0040c02d40e811565280701c0f00e00e154008040035a4140914404680320090520403541254034510f1003442d281103850041c0d0007400e44660903503022070450100400ca0002d620504054074100d0401615002d0400074940e504030010315180c6200801c0012140f15134028003a240c1c03081e41110f0030f82c21484005031050450085190041c401e0341030505101503002c10f504500d0596580f9000381e0380e956 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 111420935 1250 111419685 111419701
    0x1080d080f04031b05030f400501110703230d031407050307120504030909112a1009080405010e0627011b050d0e0109180504020f100314 60
    0x4a000d032802000b050b900c140076200c04c07900d8070318034250f42c1c0510f01b0303681480001d096003c0b4903400000200c3d0510007000071080c803001404c0c24080001100e50902a0803c89250800369620080c0546814440c0341d10f440d40302c0d280100440c101035a030003901c2c5030400101c0c031104ca9041d43c03d00b104180780e0140c440c00155044c428840c80c01010b0041d1003171080c3d5150150305840c40d50003d0b0181081003400c1d6403201c0c0400140c0904d078080d503c0b070341da0103c03401c0c9805203180843d01454015808003100b040107500c00316002c10410139605111301c0d048410b030307821002030b1300e0540e500101c909201e060041140501841c60040c0c0b048850a0704c0316044100f91908100b200c0c4a6030703058100c8000c4501d62036120114420002d9122001070400c0c1600c50780301c910204440d515048100c1d159401003c6814010b980480102004070b07003800c0100485060400c40d800519851601d6052181d0b508001019503468070020000000050300c411030b1411139040081c00740c020110a0b92080b0300350000320b2500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 111422185 1250 111420935 111420961
    0xd020312070c1203080a090303020c061306061a0714030405030a0f110604051305040201020124090c21201204020907082a0403051e0f0106180b0a090501080d08 70
    0x56500da5210980c1e691b0f442450002400680000c1d000c042d030a0090351074100b42044404c0c080c6001e4802e006110115251800640d00540c00011041540a00e51400d02407800c06544186501070340181c07007800341441c06443e500a582c0825450310684091806000404a09000080c001d05180042c49101c3c0240011442540314032078001c1c804002041040496a105a810610520010803005189200030300a89869414030851402680003081003420301d209040201016060404000c100090701c01600314121032034400f00c5807514100c41500d5207440d800d0100031000d40c142e645501c40d80260b00c0380d030141160100e00902e00040403407002401611618801c820411001800980c80e014a143c0d4a200d0703030b484d92501130140804800950280940052001c030048545c090f0841a100e040c50440c5240a40d005a407502c1000d008000b5014001100c0b009949004540c1c1c030010783c080f03103c4a080d0380c08440c01519160010032240b40200301420034168035135888240b42c860100c1481d070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 111423435 1250 111422185 111422219
    0x11b020c031506041d2e05040f0305030406020906070c050418080f0a0e031507020610030305030a24080105090c0f09061203070803010f030b0a1b0302090d020312070c 73
    0x942c4140000144a450283c00043c441c1c0340361240c0f110001c55503c4510314001c1e0344440c50800940d0301c8030342c03010070b40162140c00540042e260107001d03508207501c40e0030001200001c05010004000001001d2201c5501207903980500034000741d960b85801c0c140f0140c17507402400b500d403103241060010700c04580281000789415811518040c68104805024100e40e03101201341d0044c412401031400c03c2d5501400581c0c100501a0350841103450450341c000c0c100040100401b03060509000c003030012070391010542ea400b0024041c0021810f00001a90900460440009070700f5142d96070040341007003045d001345000c2c100c0701c01141e00804109013044400010b100a880d08254094002952498007040c11140f864074070064a261102e261200701d442da100744c020268000c2c1854081080144c0c80ca050303603216039174801c104036544d1102103402c4011202e180c10070800d5004203482045a0303c098041e04215401070894410100210102110750441a0305882001d000000000c035520382c4210144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 111424685 1250 111423435 111423463
    0xd0528140a09050402030112050d050c0604020d1403030a060608010b16020405060d140a03021c0e040515040905010e01050c070201080a050c0f03040308160201020406021b0d05011b020c03 82
    0x20840340e5404104150308210701440070014030200020f496112880210b000e00344042c01c0103500c02c0356003031803407409259580f8002080300c1002007005402000c5061364115904491001a10007903047c50a403032006101456001d00000007480240714065001400b02e8505454400b030580e6505c407080803d0040c6445000300b5035150b030240e001454030b44c4c000340e88110020003a8242d0030454540001c1c0d0095011510b445030300840d401002c0c0341c0c040165030310510030740c042405008000c5600900300c2d6004040c460069440d280401c000c081000b80c903900080003e00100440c2405080c45406002c0041c4c40a000b03501e00004103c00006050071225a01c2e010384410400d0f454415040b0001c0c41c005100c00c00424041c00040001d005d100020b500440c0241c0c0c1c0d000050400c024100303081e4410004c1d800640e8410001003060070b4000c2602128001c00003100c41c240340001001c00c1c91403510080041070395280480e00c034074252400d840080d16180b140d08440c6c1c2c14174401d0500d562a0401c06403030b0f0b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 111425935 1250 111424685 111424697
    0x15030a200706050405070e040c0f050d080f0c07080102030c071a0402062b020a080403020d03060e010b0d020d06030320120d0509010e06190b031203011205030c0d0528 73
    0x341c00b24415801c19600903205000b181d40403071340c0d010f8422120000395012901007469140400003c034030b040300076014103000c440328000c11700c0d00d64929240c0d00c1694610300b02c84c0400b1490314803810061180e00c00400c80403000303550740d20740010015080e900609003151f038040381345075030852100c1030080240700d03542c041c4c44c0740e1420001212040201c6901c2c644414203402d151680312030f90780303e40003501c5c42d1045500c0740d07440340c1018a00a418540580c11802c2018a07000307082209e429a00310320b41c11a6101d070201c698034040c03041c191001c0d10030008401c0326682000000020968410181a9640780d0f074074030003083c40c1c02002c4140e00ca074500740b201c00301680207000f46040000319900031a0001c03890f000000f41000118249400e240040f03508425110741e2421081c80801113003e0001540f03000ca0140440324603c0c01d81700d03080c4c00107018056064404140d600d0422004004503000c07208011f0813200d682c141460001c10725844210031800c6212445280860740b20310790281c2041840b83e844030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 111427185 1250 111425935 111425947
    0x1f1506030e15180708030a11010902030c0f0109030b09060603060106050a08070f050c151b0405150a0c0b04050d0215070815130e0c04060e07050a14070215030a20 71
    0x20680750306000d030112020341e00310f11000076600e00070803101005080c0d000255031914041400076010200c0000a29100c1e4100341d615001a0380200d400e4291a4048500006c0c1615410040b1a19071958000a2090320803806002001c600060010b1090004a007120400c0c2e884e00310840c0d16002d05461000815403d1000c1100d0034055007105484034080c0c580107042046420103a8940700c0e44c4070b14000d600c54100c0a00901d18030b11b140781d0007842d000b8400117103018504004600d42302095006001542c80210b1003031000c510900450000e2600a14040c18a0900b030401d55120040c00400c04007611404403445a88914070344c50501c43d6040307465520b62a0b4a09020410404421002a900869900c01416006014800c078050400c0000c000c00f0100381940c284070869a080e040f086980300c074081005a00d0317030302c14100d80302405a40f51a0f81c460200f030b0f4a000650191060080d0311070201482980c0700744088020314800e0740b000e08280300082c6001da1903111024010700c0101c00d88070400c22 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 111428435 1250 111427185 111427213
    0x50912070312022413020409080307080606090310050603070f03050609010c0e210c04020408150a090c05010507140d0c0201030b040507200304050a06020a15050f15031f1506030e 78
    0x11304c503407100e81c2d4040034a50014586c00101250250385040f06c990002005000c40c071544240b501d940003100307880091500c82c000c40082d985010441ea06840c2c0d6440c9c00008900c0d46050000000400e140385282c0d2040d1788902d450f584a40e000c9600748025880c20410101e41403203404d189420b0280034004800301c509030b040040f040c0c0c1f420308403000140f0505943e04419181c40c0300034002000f0140c043c201c02c4001d038000c0c440d02c0d403014204480da20305207000e00002c5190150b00400b00c502c01d091007641e4012600d0403040000348006010081d000300180b04a1241c1c12015150241d40300b40e800f00521080c880400044030400e64581c0c0024118148192094410481441e05480904222070420b0759840c00182c0a0400da044000181c02514804040040e20645d6503e501121041417169207444c0740220810031009214130054140a00362141c0da4809104440840e881c8540542e402d240440b02a0050141c3c0814044031185d042e5000601750300ca803180740a07000c010400781c5160140088 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 111429685 1250 111428435 111428503
    0x609150509120430020910050a05030c0906040c0c1b0f090e0a080a030617070311010c0f0b1009020c1b030a020d061a0303070302100606090602060f040305091207031202 74
    0x20020b501c10650b1807080140c2c3e1030000842c4a41c011f0401c14009a090100b8000f06081c41e5004a00031303407010002000640c0c40070744a0380e1160040d20001941070000c001202c004080c0000642141c107100e50401685800d90328210640b03100910349200f1990311800c00040311150807103800f41e44c00c5643d601c0002400c22009041c1079007285004a00c285d2602003540c0c07001c503210203484003940315100800c1042420100080403070341c00d0a101c1e00c80d4489440303640381c0d46580e00006004101e820001051400200b4030400a030000741401c54443c5c40c645111959451000c82078502a142c00c4840b209524000036610300302c69001e0b15901c0109004e680c1e41014141000581c0340c44516414000c020303440800240251501a45c01002e88840c400a084100c984540008081062254003401200d0300022680e4000c0500c0d40d41c0010356846003421140c40c00f6016441e94440289507079110903410000d070701d40a40303014144a1122038a4410280d0381d511680c2c4082c1d41a010f8007403002c0800505c0c00b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 111430935 1250 111429685 111429749
    0x131a070b13050a201201020d18050d050307020a0c060e010206061f080903070b041a0a0203010e010e0a06030b0c09180f061e0303070b040b060a031e06091505091204 72
    0x2014010301310008001440031034101d04030002a030b5020070741c20a940181d00400003d0160514018000340c0d00c2d4503003039291034101c66402c05014000000c40d66140c420402442c0c403e410145003088661201801020b00a480c0251401817003071002142c0241707481c3c41c042540040e0040c007030b14401200c200942d44441c0003040404140402e001400c0410303149195603100d14807440c400b040d0007400c20300d0a10680400b914400403140b040c8010b10240d0301c055500d07070540e0b00031066003102e90341d17006801c0003a11050300014148918001880044020705018000c0070343d00703c0e03c40c3c504044580d820000c600040324406407c500d80c10201e400790030a88180d03401d0351000000b484010784028003203440e40e40100e9040f11162444c2d0204405d01040a1020f40c0011017200c203000814915221903450000c507200306a980e0040c2501c80c001c11016074049884c0301c0d0f05c000303074010381e4012962960040008580e001031714040c40610b40c0810b00307000125811303070311030307400ca4070080d01c0110001c2002562a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 111432185 1250 111430935 111430973
    0x411180303131403100207050303060d0204020c1501230d0809060c031909060519030506061e09090115141c090609020301060803070f08131a070b13050a 67
    0x100010010003000d1081c02c005803910111030102c0e10080b2003070604e455030503004180c00c14410300c000ca0000d0404000c913504141e040380c205c45041e200d800090002e116950980400380715039000b0480f106c0c1500e040301d048400c1c101c00f81828100204d070305124100c81c00d00660303004940d40d045000240382d2202601141c04003509090502c1940b4480c0c520b16441207040f520300d0080c0000300510380d5445402c0324060211441e2a50428034141058994282c00041c500c05154440d0006521a219181582c3c80d143e803004101310071903c2d1707580c1d52656a102107000c42c0115a81c80001c26050201d50428002c6101036840801b40f609103c51264107802c5900e02030990810940c482112000600074008520f004850015141000340304042c00c40324560b02025030703500240652000f280e45403a4400036144c00100441d81c0d072101202410412a180d00681c3c52100c60500148441419002405140344a0052140c02d5101d2409106825003a00f500800c281e000d0301108001070303503600c2c4401c100080f0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 111433435 1250 111432185 111432187
    0x6040c0314042d06060302271803090415030b0610020322030605091c020c03070909290406061208160201090e07120b120705010f090b070c050f0411180303 68
    0x44100050300c0a81c1801c180c84458945c4018400e5250882c140350580704485d10840030725000e110180000d06004111401d038485861840105460a004590603000700901c2004034006441342202011100d02050700e0007541400041d8150030240356404103a0040c0c0c00035030600030415190042035840841e10855030340020340000008019010fa140100c0105010702454510040b1301859165104d0300b08045510902da01d64a03a14081100c40c140c4038481000700385a01c1500700381d1144036940c0d071151300001c404050b090260380d40407641809035228160502015580d070401c485006c800e510701610682042000c0380c004081960380082c0544103041c49003201c1d613103541d074403c241004c0351090082484011550030071034a510401d00c0d6a08100c42101074604a0f07110265034042d0740c060141800340e0f03409003248490040109100074501c000300c45a41d000c0914200000341610b1042c0c500400000300c034000103207041e0060f250300f01031640e90313142801d07560680450103ca401c140103801d400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 111434685 1250 111433435 111433493
    0x304080408010f0e0114010510180f060e0a08070509010509060d05010f150602121b030d111905070f0602160807080406081806040b06040b060d0506040c031404 70
    0x80280212050f1600010300052181501c046040c01d50724080f40c2c80c04911801e0b0010f014965441c4e02d0003040e900701d840d082c20708402c4851104071604035508000b40002c900310f800241d540d407010f42181a1031043d42d0400455580d040b0a5603505014002e8039030194040006001c142000d0304003070790000f40109440c1da001a03907101e042c05c443e00d104509a005440f50425000c2c2020142ca400082480f44001d00b54201100c0801005000c1d00b440050030002042c1609640324041083d20381100e0b00c0c0104000e001400001704101c0e50204858001c98150031480b03090300d6000340152540550030190200c5c1c403403126541c40000f075000c036903150040c84080f1910300c04508158041d050040c81a0442a03989080c50405020038800518075000105a031040d410030705400304c1c402d60481d038011040140c940359000000c001d01600d401c2c00f034100d0400f0030020a41449034102d0341c0615800c2e01e040180b4007810a084096402e80b02e05200349080c148040390000c1c11103a000d03041000c50014130742d0182 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 111435935 1250 111434685 111434699
    0xc180a0c0c0f060f050105061312080919030201090e06100c03050c0703060905060c04030201050a050a0306050603090a06060509101215140a0e06040f0318030606170606030d1403040804 81
    0x48904400d94620b944d628020680003c2481090302600c0c0403140541041c0c800d21442505080c640a488100c080000c9920100042003040d118848401400f0070f0300543c001880d0980ca25503444241e000074040c1c0000240d82584403080390007688040c04003503d03c60000300568842400040803000c20030104400c00c906041404501c000d140f09100106d900162070074150710340100505044011036040100304010303038100086610001042c1081740d140c02209800798020480c44d03000c1a0803000c00420844103c8010130600401e40c401d400c100080c64440c800c4c440d010400b12642c120640c004042802210080840c091016116504103460303403140c0e00c6a1001c0e589480710000d0003002100a011510045001d10b40b0320035181c0b4001d00c80340c5000d0312032542110b4141406820310070320202c2c4a00602d221000c503405142c0145050005981d00c0f84c010500700008400031800d0700600300810102d2402140b0b400700510700b991206080e1544000e0414161b002038402c413008802000001414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 111437185 1250 111435935 111435953
    0x33603030916080606030c09180a11120109080d020f09030706020a0317040b060409080702040516030621230f0604030815030a0321050f0106020c180a0c0c 68
    0x14030344140070b410808101825803402d124a60003486072a00310404112980c0c80000f00c4040b041002c03548207060b80c4450108103040004080e44601c140650050f00e410700c002002791400c00c51064a07412196074031088401d0890f020071000401c50501005080f0000c00d45401412189881c94083c9180c1503040000074036003600755100301c016800c00c1d0301180905030000e00344100b241d00520381d40c1c4589031035950007800c03030802080799100d10307034514182d070a0002130001d451401d0b60241c03041200e0f081c0081d500c0b4640c0001e85a1000090514401140340b54550414058032940190f11503407464840e80c420000102c502812000f038629200d12100c03006040081600c012110300182c60141444e0a0003062500000e0600310944107955000c03c3c0c0d621b0001c0d10442d1540c05260240000d80001d0b222145640544c8030718a0396070421003031218060700c0c201d009040b10b54030340868a42d020480140b02e11030030700240814035007038007100040700e00c004c50f00b09544103103040c6010000794506503191040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 111438435 1250 111437185 111437191
    0x8060619050318011407080c0c030304020402181c050c04020c03070b040609020603010603090b07091215020f0c030306030f0a020a030b040809060c030c0115050d03031a0607030f0305070503360303 86
    0x5d95800030080c0001150001d51040e00410700340801450100c42200281c1d0328407024200901075030303000445200346100320742c07d5030440000078040254002c202020050345003031917900b030300c06001e00b55903882d0500d0103100f140c44039500d5401841c10b0030700c20780f502441c0c1c9500810540d00c0c00d8490f440100165141002180030301003d450001d01a03146040082908034010b0246040c02880c283c107200c4070ad503d00c2503800c00c5512000000ca0300900210100190260700030301400e07030f00c1c0424035031402c486c040041d520074601682255846a00e842c40c1540c0d4500c03401005e504020307000e10620210b100c000a85a000c0d00038103005107043c880b4004114980d020448042580e04045115500500c0030b000b00c0000c088040c83c104c0c0f0301c5003020009401c0010740d031002800d1503035621181c0c001620700c40c540755154500070301044e114000307801c0250118425a1210001038500800030384028041e00507203002e00410780c00804220b505c800b010118800030402c40e120186040301e40a4400020401584 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 111439685 1250 111438435 111438461
    0x207030b090c1c030e090f0f090c09070507020306060603010b041205070b0a11010e0604080d270b010317031b0a030e010603051c0c1a040f050d0f0806061905031801 72
    0x40c110540c00c4c0200500c0e1142007903403082a2076018400002c1144028580207044007825241d541c4a01d01228984801c07003c19603040341c440020070154540040150108034000c1d01690425900c1e00d0410689100074010f203100d01c03405010a201450010101060942c428011601c07242e85403d0b08204503000000d900000800f00c2ca19013014640a00501907440308000c014000c2d4281032b500c0f9401c0d0f00900702d03400c0300540e4070000c40c041c582d04009150341540300740314840b0446c0f11500782000309480902065a0900240440c1c200d100600001c49101c0c41500301c4610140c00440340d0b007601381d8400d685400c100b68480c11400c494040070304c10400110311550081100c84100c41e2024482840440c0140c00e1110a03404000070851600340080e0b5030b03580c42d40451840d561840d20000480140da0b014115100303090091040e190401080002c041c41920b814046960710800c1015620480c03a46000210700d030803000e50070314011000396410050302011103600446011010342160601180d01e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 111440935 1250 111439685 111439729
    0x10203040b071518030c080903010b0603090a1208071205060604030605150a05060901051b0f1506010815180712020705060a0c0905011d0a170105070306080d0207030b090c 75
    0xf0b2100c1e8410b002c080e001005441d2600302c1240c4025240c9004c890010f007052000041d0304090361703020746c00880c0181004021640382d0a045034040da80700c0080c0b108035800301c5014003100501e8040e140e0184660226599401840602080000a00405072220790400814400480040c800e4024180b2402c000c03c400c0401164031020040511440e030310250084000f04609961a43e10404942d651706000400604071944180e0851512842c0900c02103540909100146085111903401e400790509076507803040c50300c40101d211401050544030562000a4181c84480c5141c1e040b00c459001c2c90500302107140031200b41610003603030710200c0c085516030450801c00124000e14404e400150000340b0b08110b0b5103007003100281c20701020000070070030b40040c8996030b0302c2503580c01d81100180a081341d40e800f0401d0391814060180c2415208540460f06000011440b410f000403031614860080e401054550b15546401741071080141c9440098051140101060380f54040c540355a00101c1c803400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 111442185 1250 111440935 111440963
    0x31214011d060613030b0c0d0c02070e07182102031207020301181a130c15021e03091003020d0c0512131208090312090f0d03020f0403030e010203040b07 67
    0x40012081c0284418070400f420b011401840340d0329980748060320750110752011940c036480000c403410b0060300a075509090510181d0f00f69154003059141c200c0795045004035140e12038000a071004c4041443d4207900c1116401e00b04890000740d0f041d041c0070812034031000c12011040e00402d05020720b040040c0350043c0000355404c01c42c2424410782002c401c3c04101040d07440c42c543e503100820041c20300301c403000514071804508882d40f40c0c0c816108060740070b000f2455840e5610940c06000c0750048ac0100980240c10700040402e46011b44042e4151099010f07600e002503800802c0400c007860900e803c10103501340850354809410b442002291245c0d62a1607890701e004083e50224040000e04070806203441130a6000055001482d100101d04d0700d007070030000380c1e581c40c001a1842c011070003980e2080c8415418050014000304442111103406819148030150000041d000c1e072044103031028240c1800c01080000c2846101c4465440c2c805105607440d03d6070764407805055421034070060f0b440d520074002c9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 111443435 1250 111442185 111442229
    0xf08370c060f1107030c031410020d0906050f041a1005060408010e120c0303040b070c05100902040506030c03060c0d09200a0603050103020f040f0b150702100801030203060403121401 80
    0x100c840c143c0b9002400d1a50665070341000300c01d61840300511034006103058400d40e403000d215400c4c040c00854021510ba1038449074500150643c40030a9803100d180c440851110301800f40740b80e105a400054408100392150f43c2c014804100030100903001c5070b00700700816195109030081009042c010004184400c6c0c0c8003480b810320006c4440c0d83c880120806c42e40c18810b4000c0700342d0780e019400c24031400307055036a02010b94058000c940028101d00410300d0868140255030300065407503000341e500304250794814084c103589403041195030740e15500c00f00000d015107220340c3c010f11300f00700415000704035020a5501c100c1904d181c840d0402c014801d500c0320599604100c400c950042c4458038050216500d180c010134107a140d01d032105030184d074aa200c2c0c2c040301032498001c400351000103070400301075461489085101c0e4000400480c80b81d50011201002948555440c4d4140e940003406001191141d64050341c4444281d112031480c01d03200c05030709042c05d03c403000050003800d01c00804404a210b0543e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 111444685 1250 111443435 111443447
    0x1020d0b01051204031215090c090f05150d0905031605060c04030803060f1503160e0406050612090a020301090b01061107060e010f050906130f08370c060f 68
    0x41801c0c104402406420005500c00c03400f190041c0d01820590481c03503d81da00400030381200d46000c51102c0710111b0015440b0000d91001000000c90b0b82c440440c551075030000f50410509110b5641c1c490f80f40009400f51031100e2000300310600c1d00120008000c501941c80d02e0945e00400c0244080780c054003e00d205000e0b0500c000c80d80b16106a1070300e403a0500b5a95110454080540190b00030202404168501d4442e64102101c0000c1c1101c80c0351640b41501c9060b801e4101e02c040d89000500d940070031082410140100002d84a0040060341040c903c09209000380000601c041c03d103100340e03a148805030700d083c803c1c00f041c0c500032581e48031150304090b80542400d0202d904000960310004080010303503803081101c0701401091a026003851003000c0c08995a0043c110007941c82000007404510380c20007940f264003181d6040d005101c0050b550881c00d915020b85041c201c850540c44c111803d012650b44c00000280c0c42079206928042c1100d455200c5c034200260031101c04204041005c2881c0c607003100d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 111445935 1250 111444685 111444701
    0x10030b040e0c120d17130c090b1302090a03060b220902041803021c05041a07060b0603040c050112060312020105061e0a0506030a11072f01081306020c030a0201020d 72
    0x80400b1000510010003c0c00c1002080114414a00106264406481e0700040701b94110803a0002d40c2d44400e5408002e00110f2461841200e0b92803074012881010b000b80e80f15444000c0c00400020320b9522920301824412000951040e2083d84120320061001d2090003190440203001a070380b400717841440203d40c0900d5140152204003001100080da000034003c50031881c842081c01c000c1c10070f54055805001c1c0350010004480700c00143c00100d000710300039220040c06100140143d140c41800d1050500c07041d5070290984007200700a01040d4000c030042640005418070008141e0b0303590305e500000e198002031440c01070351101c2c1801507e02c1c14440c095422644481156000403400f000200c0b040d415201d0680180f10120019002e000300b07074400e26805010b03140640d0f07550303018078000d04440c003e0344200c10b480280b401c0328856141040030b400e03080c00060f110541c43c0e0300d54000391009040c054800b1580c0940822822110110601c0903004600b510b400151b03c1300ca501c5091001e90f03400e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 111447185 1250 111445935 111445969
    0x122a050a080102090112020702090a0b06090a081609091e020d0f12080109061401031107020a1203030e010203220609050714030709020f09121912020c0405010501090510030b040e0c 79
    0x11f108c810007503540c6101d02030f08000d080500280e000420300100300103018400e00e01da44003140d2000003503081800b08e08141007040d024820302c403543d01c07001403204503410a58064001070032141c80900002001344041c0d20103000806103952022546e4841040c07000b401c10464120040522a85509800000160260840c59014000981040580183c004c540c001d082c0c101a110010003240c2081c8004230f8099680181c0502c01640d00c0c0c0c00a4000d14448030000c80001c1d150000b004003201040c1300780c0e8000e400e460800c84100e484245e90760020034400300251740d8290707a10000000140204132200080600030700034401c151054040500b492150340c8032140c0140100030103621641d1350030440d40c035490102c41d80b004c5194040280c9280282051000c0f00d0841f010301c1e04824411003400301c1401180c240d08881500c0c80a20500041e0723076081c4202030119016540c01e01c02840e0401061400da900b503e0002484407942c800a400d58428001d824150f802031034540300e840c00c1c40c1404c241c40309a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 111448435 1250 111447185 111447187
    0xc06010303111c020c04020a1215051519200115061404030206040506070c080a1b080a0c05060d0b0d0f030306050607030503010b070305160b060109122a050a08010209011202 76
    0x9841029461710542c0708110321569000892055031030141b240d0641c1c0034940f0f03104004410703818107040355805490203810301c241444445014152100d9044892903d1040e01c00480390f01104402e40d0350604180c469850348142e280741002041d000d100e0465090080f0442505540c41c201000e800e4011400e0586d9000f0001c2109101584070041224125402625410307640d6029051003c00003200f50001c00703890042a13144010f02c03407101d0300b090f00c06850143c000040c6a0303034410180c2d03800d9464401810009801820002842c1060181000b05815a00440c1001c0c00000040c421000b0000c00c036503200403180340e201416450301c6803d029200a80d160352a00b40240c030b014009000501c40c103d114180091010105803280054400c0b00e960480b01000c00c030032500c2d2078480401c044030040e0004008800016580123103800348008181c00c81451000181c01c0c2c1013084245c01da101c40d9030402c00c111078001400f9110f011076a0014104e5100041c0c41da61031400050090101a100000c082c1c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 111449685 1250 111448435 111448483
    0x921090510030e030f03040206090a120201031505010c03030902013e070e04140a020d03031b03052e0305062403060103080d230c130503030a08070f050c0601030311 72
    0x40c000201c6a01283d20000b0903187d5440d8400911607225031030070190800039035400080c1100c000b6003882a40c0d4400d80b410300440a0307602c0c1c880040c40c01840f0351400200345107123040210b402640540c44443c0185010341e41400a000c4400841001000001c5d41079030f0402d9001c818005481d40607101d006040250541e6441e09070909600038010b03001a10140e550020000032120400070315a0703540d4090312004074032000e0708000d001400c800788010311000100004286207072003845440e205d80f041001482d88003603c0c141c42e0a40f543c11100b0504000c05046002c004183c00f004158403540c8000c00100f08009001c0030000e00480d481c0c0303078902135403101e0014800a0003507015181440a0246c000030402403001280c1105000369020782e0007150307644240a00c03003d481c0300030448a1026020300c0c0509640744140360b52442400c41050006070102c0c0441c0da45840b0340400300c5c1040e014a4041d04024905072220f080900c280c1c0300f1004a01c0402c2c030415015805e000300410107000708000340740b0038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 111450935 1250 111449685 111449711
    0x315020a020a080a0c060f02030103060e0d050d0f020903010528180201110c1203040501020d0504030f0f150216020906010f0807030c141206090c0c0a0204092109051003 74
    0xa031642c0701c0200540300114180d01d51600c0382038800c202c940c100c04244151214410303610b000758005e0005855160428000d04100c0c8400141413400c5560359541a18141c03940400030014840a003140e01059003c1220000380c2d5000d004060262038580d4020703480c8901a24402410240c0703201e0140b8550819420142d40c00043c0a040c90094080c2001c0c003000802e0804d2a04000c9444a8940e00045050000a0320308001018200b92602130302140c543c8040701400b500c1030b024604c80180803c100e084800e000030b42e10040049003610650712a1a10250300d101d038000e0340c00c035035149403070b2840340c801070000d51400e655042d40190080c03c00d400d00113802e00d00149400d00040410042c907817982501050b55210366061343c02241008080742d1110700016410b06640c40c280d9078a480f4402032800320300e1020140040f5107500e49001e0080c4a01d048079402d10026200c81c01c8160350400a004800309480003100078480c00c100c869a4104e80a814401045507071105c0d4950b0000f01440c08140e40942 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 111452185 1250 111450935 111450943
    0xf1d030403060c0c05010e06010806011e0506070303020f181c11120708030406080f070302090105040611071a03040302070b030705180613170706030b0f06030703090204020a05040315020a02 83
    0xc1ca40101c00070071900c41101d03040c1d9542061074001800c540c60251904841c0c803010542c80d05840c0960150340a503641d514441850600039000710200c003103090710810084c90312800424107144a402c0c05030804c3c10240031000d50350805d940c01562509aa0624641d6240c1110700d14003070b080750081014202c2c4181c0384d24200c0000100d0840c016801c90750125030a500800c44140100303044401c80341e0b55900c0b28001070000e8415100d045505492001240310070f40240292205d000301a507405052074a800404c07165124554000b442a0060000c0420404202040809401e9811207004d0781c90070240340081c40c00042ea80809814070040c014000c80f950300004403001d024414465010a4411800080e00d078407985040107070000c05480c000a840102102100e80401e4000640f80902c3c0d0700d079019410b440c1804c95032a8400e19080298101e40790002c059504145245400285680f03a540031504a17400186020f0119001007010410059030380e8803030341d0000740010b040d1b080905404003c3e6507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 111453435 1250 111452185 111452189
    0x260114060603040c05060f0a0e0405010812071403040605071202210903100e011d03030106080f071b1401150e060f0d0c0312110d020d180302130f1d0304 67
    0x71404001011805000707000842e4006464014000c41d5201d4020035210156809410340d6004500c40c00038000b001c5c50980301d03040c101d51018010b880005543c0c00400c0307035984011400c43d0200f0020040e2414040100043c2019044545580e5034800c0241440c001c00058810404215032010381f861882088038403000900390703000501c0580b52050400081d00b8034900e0380d100344940c1d103004402d43d010a8150440310000004282c0c850030010100300c0d55481e40710900460b400f00d80302c40d012079450311a4141b4070f40d00ca081403801054004a0881941d0b200c0d240702c4058030a200070b440008400a800e11808401d4540c060380400503529241c04a01c068500a100364882e6031400c2c51a2040d80751405c10034420740c3c3c0103024801954a030318041070680b00c01c0d8020f0380080e051001c02d9419540c00580908105010340080c40903005210381100c00c0081081c00f02c08100403c2000001078440d02c02030106400359031340201e80ca44d8118001000c0320b1000340c126403010b040986454140f0000320403103013 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 111454685 1250 111453435 111453439
    0xb0a0501030f020702091e0c0f070206130816140604030309090905010914071a0306063405100e031c02030c04050913020102150108070b030406140126011406 69
    0x1600161034400c80009000300704d0080e401c0b00c03083c8104a280204446c18038100d00c4075044128140e2581210494a4052250143c462002c100300b2040907207040006080d0080c42500030441c11030310354501508007d01d00200341c2100700198030500004403131100b004c05041e8250781b8582043e1950300c004010300714620520020715a142c40c01003c2c01820742141c1c800640012600d42e040e84200080c580c0d400c0075100d001004100c1c003002110650100c0112405290000c3c0350078100281c02802a071110485003000ca0240141660390408980240d400e040d0b050080026102e1350305100301032416103451400c0c2030300c190810840241c00c41c80e03020341406921040c0398010703202e46e183e40c3c00291910450f044030786d106d0703221401c01030044140380d980c3c82514405c0c2d00f1303203c1d00301e403c50310b07144800c2003800f905016070010a01800542030030700286078024011800402d0414890f407a00303890a03000c0c1c000b01a40c0c42c0e8480d618549012225000c140441d0400003040070583e010300030380f240640580924 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 111455935 1250 111454685 111454691
    0x815030c060706111308010b0a14060d0912052502030d1b05030f032d06100314010f05122107030e09091e070506030a02070f0f0c180b0a050103 63
    0x9403c0c05025030015140c00c0c84400c800d50303210501000d241c1324090f40d200d044015800d101003201b49003400503001c800c55800b80c0448000e06256408c014294100c010030380c4d4038540e1b9640040200f10303840b0850301403085540740e03e0340d40d0019103220750741d103141c103003450391300300f5801400000507200000c500300035400c2841d0000c1e59018080801640814606000e00184404501034008114440066026224205699031120010319045150100c428421500b041c501c40005502d420b120b1501c0c101c1031828540015246501c1145032210700742a003082e07101018582c002d01c40350806031001000078a4034801000c8103502c030031078003000402d146d184401c802c41c08101031040501480c103003510802c4c001e110b510300d8078281e0071307003982d480310300d0746c14084980c590307410448107030010400c8002e0320009001c9500d550f4506800c5002ba42c40314108440c2c030a440300700d100200b841c5284902000c0d1051185103026450500001d1394038044400814902d498020490302c542c4d8bc013400c2d441150300a003004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 111457185 1250 111455935 111455947
    0x90d05090a0e040b0a050718090f020702040216110613060e0619020f0106121a071115091216110a080d0203040513110406030207020d0609050606010815030c06 70
    0x1c40c0d080111507011011105400d020710042102d15010346200e00d41c00302080096561f5804200c800da1000c1c001560050f94480d018013641c00c140e0000801006c400d10058038010040e4003041c220f07405000140749c24040c400e140c40c1001400b118400c408241243d0989c18009a21034092a01c41c05101c0c1009018420049107100e8441c071082e210103c0c21503071078000b540c0c8102d40c003a440b6001840d8101da1546028004100300c1004d007412074102e50020003407a556444a600225420340151030602440400350841c050007408000a54020b04049402c1c0c6044c20304060241c44e045001500c1c2d050144c007481002410441d0b49040c821064028480e0fa01d0040018013040300c02030307544c000c4800c0c0d01480c49400505a0008020300c21550242e4402180e51a400000d20489200320000c884c65407080000f0803000b40b298000d062007500041060321803014517540c04040302c2d64000c0031942d039000a000c0143c1c039031b002022039900c0540800044210102d44000940729424496947e208100c04680c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 111458435 1250 111457185 111457189
    0x70905010b043302010902030d02071d0901020408070308070c0e040b04031b020603090a020112050403021911060a1d040b060d0e07090c020304050909010e0c040b04091205041d090d0509 81
    0x10300d8040c3e100c50007804801c40308100001d02802202d0000e034082d00c01c4c140c410301241d100040340d4007203512911207076440710b00b41510000c10910140050072299024000410b079454184280f0700214480e01a031940d9074564501400106629440714141800c00c208002c042107402c8a042e0b803203503146c0f91034034455641d400000300d01c003600e6a01a421820200c1003100d40e000010f00601036034004d03260101a0407030740b04590180e4034112030040068009268803200720504418800340c09120712025101ca103101c90110300310783c001c00d50400025041a81c0d000300c9801000700304070242810f940034020078910401090b034620980c1140c5400c240d42c3c095110325220103004032000340c034411005010582c04808001e65981203030041d00d1090000d00081615001d0500c11003803180c941e0030161500b41003000c1088010204c205a19030415220105140010040141d980f2040c8442c0c0b0f03000c0d1a54100f4030010000c40381140700415003000d400c00c0c0100400000340500460205e403900030754628a00c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 111459685 1250 111458435 111458489
    0xf0c020108060d06140a0f0506060d150306050901020d06080c01080714040e040501021209150c09060f03090a1b03020307030204020c0a0203030403061b0f053403020f070905010b04 79
    0x54040c00e854907099042000d01d005c101c2c01400f541008506214201c900b940d07100c2114001c0c2ca10030741c0300b202007044240c1d1454076001000035000f20900e620140360307640c8403002580ca0031501c0100503580001c90301040d90051140101500a4500078100c50780c20200180c02e41d10042e0900080c8880007000c0005240c0d900c4c00c43d4003070190074102c034040c2d05041c6409400b0b03421000624048030b41020000e20069800140303181d0542c411105010302d5200d0b07043e40720480c1d100310300b820f401407410803c0086030015000150700030701000300241000c0100d030401c18040ca6422800c45d007032810014007040980e4000a00e1020741e034040f0340041c0c2d43c4249400d042d240940c0d01e20b000b900743c04045400404d1080307946c4600c64031400f80c0c04c1d411034107040400403100070091400c003d000c101c007804199511200c461a034929440004044410346250564a040b14a0503000c220010f074002c548001e10440140000d20080400d950148095410400860468025405400030540c050744000e114111880 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 111460935 1250 111459685 111459709
    0x30d031a0301020a0c1109160503040501090f0302060708060303130b1b01050c13090507120c09091a01090f06020a030f26090f0615040209150a0801080601060f0c02010806 75
    0x1c00031580c40b0030500010304904440501560301c0c2000701c1c00ca102a0920743c040d288190f00e8000c5c01c50a06158000989403074002410a82d050f660711070040c80000c4280074003d8246002c2e80051261785010b500042000b080140002d00982082c0100e901640710f075003d120035907400c800c00c1500d51640b048541c1800c0e07000a080b0780550700b00750900845000d181c00810400d0720681240e104143c644042c0c90a4809c00d803184c80c00250041c032008030290301940445565a0030f494040d108640d50030400d02038900d0f204a181d10042548142c441940e00b24a0150040c04c030304401492307507460190702075203034400104003a080c010080c0107010701c144035041180889800b034444148403103480170f880c09034000842d104020351099030050010320f0030009460f480b80c104507a01e41511156841404040c1d0800500d058200e900304810440c00056440035041244a41d41d980c1050362500c0102d80c5445c0040c0c0c080d40900c6682451403827480c0c2d01400d04001c4c140c0a0900302c403030761100e1004c10300130080c070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 111462185 1250 111460935 111460939
    0x3180614071e1d030a060e0d02010c0c02091e09030306040b03060103020a050d030903120f030c021b01030f110c06060109120b07210c09031104060b090904060b060c070e0c0405030d031a 81
    0x30021041081d10361048000c3c001f0402119100c21108605900f214280050080030231590840c250040c5841e2501d2644000c0301000100454000b1001c0c413074401d410f8812903810303000401001030500307142c0328042c4054012001031610354599004a060072101c0d02910b030003807059601640506d405180220015540080040360903032914800a151946a90b2040e000078100490140600d200094070000000c114040342411006600158014600d07414001c40941e201d00b6460740c0c3e190003074081c100d144c11800152000d0301e0000b000405144c0e40750098007002e8801d00d13030030b00072074541d000866020180303042c001c4080d40344000001d42030600e5a000c030109824a1102c5a205900040300002c60b0300c28820314a1401202c0e0030030040c0c0e60140100c96001500f404416050b142c16106150014001d842c00644415000e021507400ea11403014504650300120080115100301004164060500151682005d0a00001a0312411100380301e40405d40c035052000002d400c0c4480d0b03441d10180c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 111463435 1250 111462185 111462193
    0x6040e0a0b01060e0d0f110105070807050109051006031101031d0115030b06040e0604060b0604090603050a050601080304050f190b03010e010f0503010903140304050c100c0b1003020a0501080703180614071e1d03 92
    0x437841d00602809140804507014010354030b05da5203c0c44980200016a540510100004940c40004500500003010300520038a940c80c01e50120300c8080c42480880029102c001c00101c1c01c46c20702040d22507003d00558041c078641710048510b400003180c0d903a0801d512020100311540e020000032624007640d04000d1665181140002c1040000625640da0070f100d08181d80940e070341c1c3c4106540700c2c022446071a8100d004411110b40a15010404505103107201071440405500c8410011064000b43c0003426114908401840241c400d103241a00404040340280b1201d54255002030031503400c95420488001c003c400301e4200103060120a5503000080c051800603142200300070b0856444000948280480c0404240707100314860103242070b66009000490800d02e40401198200d100401000405079182050804c4003030440d20014114002c000110309902660142c7c5011380001d0107070f106000404000f050040010300607000940301608150404000c40300e0f1a4440c088052001541806 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 111464685 1250 111463435 111463447
    0x3040b0414060a0c1715101808031c0209060f030402030f1c120b090612070803030403051801020307031d040617100c052106040e0a0b01060e0d0f1101050708 69
    0x14503400b08040ca0040d40d1003000f170515030002180340c0070040e07400700c240c05038041403500d81c0c1c02d100d913103006a07051504e00350303604130303210403009901c0e0031190000d4805070000a801b405c0c101c00b00c4400c6a4210340e03d8421032401e9405030008040384640c280d100e215110101c0004c042d075406018004140d00d40d103090380c1e44da03480741034008110002c03410000b0106100d045441040729813845000c0c4d480101a00000c0c803911031104106900c1118115a242c40c440d00502049180e4140301030f5000381e1098446a4488a00104c40c0500401c0740600904640c428407090020a6100c01d01c4954040d40c452010080211000810b014003c1c58101c0080d5140020080011100c00a0400c9034055810410005410440f80494440c801d101000c040390215412400300c10030150301268200d240100000344c11281401100d081680c001c0c0d060f40d007082e610004102c03c0d50011800c0c08102401c407842000c4c1481541c5140c005102e0700400750600040802040c00359000d44215100c8941010b88141c5a00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 111465935 1250 111464685 111464701
    0x251e0f0c0503030f0703060803040e06190f0303020a05011409030913021e040f080105090d05030702160e090607031803110307021c060e06070504031209051009080105061503040b041406 81
    0x1a01900c1042c0087d242501c00120303410048251003e40d50756400a1140b601c034a03003081894449d2074000c01d141d0041c1840080d201c1b48040e000e00040d84260060f01c48401d4a0412901311034200741085018540b450400c45c400c079002c01103074040340f4119802c2c0d42c8072092060820090103075090300d016000d0903126a46500d0340c4c0c1c1c00581300b142c05040c0300c1480d03291900e415034280c45050b5841402a841094034400050044015681c0400c0705d1048412000b503404118020b2201d0343d01602c0110304400038401c8240c3c0c14809641d02c00b900341020300c00d641d440300d480c141300000c0344009001c00502a01000940030107104450038160000c001002e03446403141d407001c500010ba002105c10500e48003441070065400300c0d40606c14140d03921541e0400e0b1446e224001c0d0400600e4a0341c0401c40300c0c0d800402d290b504c0e04c5103820ba40314244d8850b5080741c24800e00c1400c60f000030388118032607418090580084030b40302c6e04496005a02c0718107611315450302d10b40440c5030000034080701d2950060500300314100c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 111467185 1250 111465935 111465961
    0xc0d0f0828020106050a0504090f0305070813090902040c030501030c170f060c1902120409050402040b041d12120a18060f021c1503060b060702030303251e0f0c050303 73
    0x140728102c81610202d507039a01004100c0710000d10040a10b501d40c034405000c85d000d4cd0180145500074207544d440c0581103c1c0c07100b0566482e4018070340c5241c1c1d800204055040503c64540d01c3d6105003000c000650543c0c8a00d91042002e10401b0394044211400c8003500105216801d0321802c07810844144e4201a1040c0381180c22030012070b8040411449a40400c03840001d4903c07040107a185038034a03082c14054001c0181c440204143d8225444070140c4245840e075210303581d5030240c1900c40080c00208100d400e42041d980c0d01c064408200c082c051007005611442d08184c00106010000072500c0d500783c0035001c803000c1d08a01420061416102d51712030083e230340003064203110000c0400d070340d20449141001203482089020102c1841044240700103000c2d81e11003958a440145812700b000100c1e4006860340e07004840c500340308100d51083d070710b214400307040b80440b008050034060f401d50b1140110101254820505c2420003108440502806025040b160b83c030603004003c1d00d5982c9001001e81d220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 111468435 1250 111467185 111467189
    0x120302090306101a040e01180e03070606080601060908060f060109080613030f11031605190606080c010809060f06180a0e06090718020304080c011d0c0d0f0828020106 73
    0x800010b101307640c45410541100c0136142c404400f040d039642091140203160b4a40c11404442541da441458413018040003e450b580d032040030041002410325076034904020041c6d001d0024011100d409120b40c010200c4c5444e445180c554840c0b81950f5160012100c00015034826003950081c83d01740003581500010201c5a540640c4902848250001c1c040b20171050040c16024681c009010768084640c034009080300040c0200304444c1d052001d852042c910792881e150031540700303a60b00400c101c1400184102c0310550002d081100750340c94503002e2991616401804074400e6042100082c510790b640c441000120684a0780c810218a0012501c0340203003d000c0340f100b0a40b240d42c000440080001802205076030502d4003008019845800820107500080e1040b100102c1c02d02880a6503078091003820000c500180c0d20328003030203813880c208d070800c6250009103008061400e40354011034111007110381c01d640d03c4542d450342c5040d00d0000c1e2100b18440381049440e240300034044001903505400c0b00341 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 111469685 1250 111468435 111468449
    0x20c031306180614030106110c0301020d06060201050901060608041226060913200406050d0302061f0302100503070c0f0b010512010603110103090c0f03080a0e0306090a12030209030610 81
    0x2005945030383c01a1000341c448100a0340ca400204018854144100b165416511106007240c07032070007000d4006400d903001940b00e0044265104d5041040540c240a0140c0204074600200012801d0800080c11700000910150000207061000c14081d4891150700c004041c911410201041c00da039280512403a040d5039192284a0041c0400d00c940050a20110850f030310010008074084501803d010a180d40c04001c2e5005685e110002126201c030311602c41c200d4070a80c0178044c585451501092000ca201840c0788640000480c14401a11112070080d80a1000d04000380c40c1e0355500d0b42100d40203200d10000b44401d2145075400200041c4a041d2416154201e5103aa41041c0b120110f81c03c031000703403002030003808500820498550103030340000000381c060082c2c070103615181d00007580c0030b21941d44115030401c4001840d2060660000c49e010300382504601400040c02c200d0701d401d0362501d140a02521403198141c013043d0b105c0c0280d04a6406200103010f40d0030350b2511400c0c0200303075409031180310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 111470935 1250 111469685 111469727
    0xf030605012102040e0a0b0103050a03030533040605040905010e210405190807230103060302030a020f04180c032a1701090c150e030c010e0103020c031306 68
    0x100d0b003803140701882c81c40e507600350021980d411019001c0202a11600f07140503054002c00c001c0d080810000c0c03100700d001c2d60158000303001c9019240340040840d0001051804140000c1e400d504580405c0300e41d440468461800d00640c0414080010f03004248540c4201d50103460300040300c08110041d001015054014800d543c121501d15240810103608c1c40202e54081200f084140060300c1c14804680741c4954a8203068951034440601e149001d0568010300d0003111203981d80d0b0100d62408244030341d004001e01e82400340502e9035000c0b0743c1ea21040f4000078400c0340c020200300ba0584440c0c0c4102032407051440c1d40301070090107080c50300b40c1690900054035103c2c18641c1074040c0c442d510300c115513a0343c112460007029600e80003c418062580342c2c0c50500729502c0c0d20044001c0741b0210030860182189070030034010030780744c031401070319180b00c462015000f0b0300842c03040c04a5a8110035020706520742800e01682c1d641d401c2140604501c100107560002403003c1d00082070081e44500354407900080043e00c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 111472185 1250 111470935 111470939
    0x5090c010e060306060405150d050702071403030f0319110d0605011404150c11030a120e04201b0609010b13020c0c01030b0315070f090b090609010507080c01060f03060501 75
    0x40b101500c421640d0542040080000704100d081c4a4180800c00489026403800c0ca24121401000c2e21070586130540168840c000601500c0c0c018140c0d804441c10481c0210715100400041142c64000286070000a00440303501002603e82c89d0001500001c1e601c5e10b441ea64400610a50010002800352a0003e41020b0780184c1740c0144000f19400d031000d140700c0302806000e00c0d0302180c0c64510110225181f50300040700d0030313041e101048050701031480b0f885170241c01c9090041c0105403002c0014880e02c10b40c203140100c070981607000c505030301d074440440400750740f41c0c0402d550183e005101d801d49010752003090b003004212181075103c0c01000707601b01d4000c0c9941406400c00740513802039102032003858120402155666010f54800f0f9494900501680e00c1c03001d2821094070a09000c44e641d0700460380210f441d0880e1940700d1b03a8007024001e008400c6050040c0d01011a4880c06009015414801e00194175001d0181120698587c008603600a21882d81ca8016407044948107100444480e4140000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 111473435 1250 111472185 111472189
    0x110708010501030f08030705070804080303010e06040203040309141909020d06121a1302030d020f0115080a0b0c071b0303020106050603070512101203200c100804031205090c010e 78
    0x5954100c13904400034084110440d1659480c590002d0301c00814481c0070050707800083c580c18094001044850080c644070343c940504d0785400400200460311962041081100180d00304101400b0760300421401c0e00040c1c0c2c0d0201144c080c1031000c2a500b20b05205840000300d00d502c94004202c0340c0c11186040c01011360f6118580040b02c1c02c2400180218030030000750010541d03100f68254032004040001c070383c02c0d15940106e03080c030881412150058104148540c0b040c0400d00840342c00c0f00300b0b1080e1702111454502c801d43c6030307091184002e1407090100041030075440b400c4142c2c0e0905800035840003007084254003024085c56a88000c40c00355003040d40010b101e180960640c0d128008076151603140c1004078140c80c072000700080440c91503070b20280002c20b00125000303031201c0075803094480818680041d4510b0070001c003070001d802060752002d0323414602a11005a4240410001c0c01c2400c0961203a1909132400000c113020110303210328100400214010000da0600c040d003080e00e401401800c020300b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 111474685 1250 111473435 111473441
    0x12060e0c030304030222020910113304050f0708070807090603030f0509120706050d0b060304111e10050d05070e0f06070501090f03090509090304080a1101031b11070801 74
    0x701c0651b004240f5050090025200c1c0003490404640c030702c00615000c015000101c1d04484000c138400000c064208120071040100500d60301c0212010104035041001031075aa00f01480d042a003580d5542c050100341004002c01c02c0300340c8181042e050303c664585400025680d801c0714070039459544500200054a82e03460302c643c4080c2c80e015607940b0503aa0500c0810b890503801030041c181c1003400c1d074103984500300302445003c010780202c0e5112507580c1c072201c2c00d80003900c4079600384922a40d000c0090000061044403e45005401a03d40b540d47c004070700c080e214014000d8000541241c851032400502030b070f10200034428a5031001342080203455802d82280c0320b50107000090b4210b2030682c618070007403a010003d003010910610011803040c905540c1c001283c0480c0508801084050006114901d49908069800f560120080d4200f91502651941d2032038410000792081b1100505140507074443c2e0803864150035078114041c0010f00c0c4aa004003141d04091141055005008000c114850180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 111475935 1250 111474685 111474689
    0x8070302060a0507081b0913020a0f020c091b0705010c08041a0402032d161d04050c060f0f031608070e0303040e0a0213030501060501080a05130605040201050412060e0c030304 77
    0x561010003039991068601076600346d40c41a190b0252041c051414180d40d880141c19000c82c890002503150303200214007070218004207000c03506640004005000b1a168008075a9101400d40130b10041c115298020720098031a101000d001542081c41c01580039401150540c05a4403e0500075064010b10131603200307804040d1030081d4140c0050052007251849420b020f010329404140c500f10040340c0700f010b07a1900c960b094100b5000c40385c0c594200002c0c0f0580408072075040e410307201690030f8a0255603581d1a0354030342e18a10710421002c200d100e0b604608400780c0340d0045441c008140e0340e0502080110b443c4000844035000118600d0000e58201e118041d00d01c4e0703e510240080d0304081c200170f007040b1621401850010b071658213110310740309061007840c0100114040d0000152680c101f400040c23040b500104440140e0381004144201d03801004800d07086103400c003e0000352a1500d100482e020700c142d40c042d00307a080c0c40c08601014002c055001004818403401141c3d0704560380d105040d1640030794 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 111477185 1250 111475935 111475937
    0x6110a020909100c08040221121c06080a15060609060305040f0c060906020f070b040510020a0210030b03010608010b010c0807031103030406091a0903040605130e0408070302060a0507 80
    0x5840040c1000c102142c2c020701c1c42e0041e60600c0481c82c50003000c0340c02084c68100010300b24030901080d820300c8011003c08a50481100706010b0201540698544c498000070744120341c006566406400c0304041048025541130f0b05100301551910859640c40c0003c4098840d1003402040c030030103041510450044840640741e000d503441c0360000541c0240001072042d1342d08140141c01d900055a11116031b405013000c0d0312008103850824100900d0075400164000b103a5002010501002110030306850484400311250001e0700014070040b803c0c15580c4400070f40082003ca100100c03d6015000102540300c1540204186652040c56600742e0310000340460200d42c40405443c00304040000419415000307062100c51034411880c0709186500c112000d582007641d1b0038500080003810101c5c462580b1102d00c55000383e0038015691034981c4035500c00c01042c00400200341f41d004050b242038074000c204100c0000520b00c1d15003081c81003540400b0f8110014091240040d010000d20310407640960702c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 111478435 1250 111477185 111477193
    0x30c021c0e010e01030e010203071e0c1e05010e0d0306050f0118030b0408120f0f0a201b120d05010509040b0606070c08010513021c02030312060a030f0303060503070611 74
    0x1c0100152482d00c940f04071541016102d984007081305c0c1003400114000c0846980b1107084040c3d030740e41646500440380d4100c040208141040c00441d405058541d860707416000d000044d45020701d421801030030000c1e11820300e40500844d008034180c05502a5045034400e448054009802c00c00446421001001c1e043d40c07400721000c01c0c004a419082d10340c0c1d2062003414007600d0013100c41070340719620000f03c81c0740c500e0117102d004100317001c0007007401603421101100d020301000026110144007001c0c10301c0b00c44200c000110740c0c0c1e07104110344400b4040c03103130150003030300c2d0710801c8540310010a40c8840300c0b420096003400000070342e5050240398544a690002030150342500c4140801c00140c1c0680d2055600c00e07403030f01001c91114400c1c880e041c0208003a01004005d00014810b010000f044140d4101e92281299403030400b50714084211643d03c800c000210361980ea0b401b000440d00b80c256000a041980c0c40b08800c030415030940c0c002001d40c0c03021030803100f0140c0d03690360448040503544050f411303d800c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 111479685 1250 111478435 111478457
    0x30c06010e0c1e0301030615150804030e040e0303040606080609070b090102030d1812030515010315261002160303020717031501091a1204030c12030c021c 68
    0x4a600e001504841419100d0f864440d5515420302d0041c04504203581c1c1c1c0d9800401081002490700c035002040e94244022500c0d645050743c03103190000c000e414103003031004680000e41007610601404041d0100180100440b0181240e5165030b90411102224050328044000c00c00e40c0000072000e105100203002081200e00f008210411a009403100b281135110900c04a5442d60041c0216103203640400c08285d04e40c0c05604240300a240c041130300805040c81e00c81405111448203007405a043e5007130a011500288288074030503520400c0e032000126169021401030666940c0c0c00b49154000380400311000d9192008440c0120b10840e00c501020000e034800b040c0c0000c2c00b0f5000741c48014082c00700c1002c44022108020b807140e01c02c40307008001802c501c2440d05590b811224502c040c043c40d601c5d0142c10b245030320302e6101920980940d003e40703042e4900080d04261044011140203a8006543c2d40480d102c0078001e4040c140180c004d1000d40615034000c1c24140c00341000004030055640d8000e0215 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 111480935 1250 111479685 111479699
    0x306031b080a080f0403080a1d040903080601270303020307032303010302040c0201020d0603110a1a0d02070203070909030305060405010605030708040809030106031e030e01090b040509070c0218090f030c0601 91
    0x41d2019280c013001034401d11000000c2903040002d00030032103c51b00c0e2050401120307070000802160455240d48518504030114002ca41e00107500795000c4020f08101c1e420b804942858800001e070000010f613031100e444401b000301170f400701c080c20020340310b40c40d52407030003140020103002e142c03a216814074102c20900041001d494640c00c122070b540740c1800014541502e45000000740c440c240c0007516884180c0380130201c581002c4116400070004106420902c04031990705203494032400141c48082c54010131184155a824480c0500400c1e04000c1002042500d28001e009054100e5145110710321742400050600e00032002c80e0f01c0b684580d034a800c81aa540e540d0081340f6000b0703030f00060301903581c0e4001000041003103030b80602517583e91464200002244c50010401c00031140c903d230404c40c0d800e900700001d034101d500340c40030b6030070817900b0040c641c1d03c0c1c070303804c1f185690f407074a01039480300c0f54814013480d06100c060350500902c50007090311004612500784a50324410260030403402d03846040100422 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 111482185 1250 111480935 111480937
    0xf0c0c0f03070602190c0806100611031c0e030c0a0c0306050a02070201020316060b120610060c12030903050d0212040201030506100509240c06070206060a060804020118150306031b080a08 82
    0x541c89000c401b928075031141d100524110086900e841151218201403000a410412000240910354000c610344454550100031040c804040030303041d25242c081c0031000300020b100761011155220301320340f80040941000c900c02500c520040d641070b0315020120b03040d04a076001b200c440c1074040c0c00071403400d040104e0319580d860320890207840c860b81da0b44074441d0a580d442d6540c9092500b00b8010401070901030ba2030050503d240c1d020009204c00e080e0f480300050f122983d0b0b86080703005070400242400d40c60038145c41d00c0c401d041007004440c0c8001070170600300e85074800d50b078010383c001c0e07808000d19560b02c014000740c0204c1c1504500411420b100c503003c0d03460640300b2482c4c8a00900941c01100406403040c2da115084040410380c107400950070418a40d40c10400150300900c1198080300d21443c0010240840102601c041d0403c229000ba122401d5152541003000b000c48503580c0c1c42c0c2400c2014024001e0905000480c3e10b2600e070491141c0c0c80d042c4451a0066a850202510070070b0b40d01d680701421 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 111483435 1250 111482185 111482233
    0x1d0d0206070f0f05030c0109060b0301050601080c0708041a0a1e0518040617030a0f080105010906030b120f01060915030804270c02060429060906060f0c0c0f03070602 73
    0x6036003c501040005001803010b0801000e010002145200c02494150181d400c035030451350107a0715007020040c0da6a0b01c445580c0c1c20401c020140b030b541d010f550400104c0c5100d241c0003500380200c13070b132219050501da4100030800712505e40d446071100300001c0440708681da0600104400510280151441c80c1d1510034428440c03c0000c00014180b55620841141c07010704401145160300041000803187e074008048200070b0b03116180c5080c0c158100720000e040c0796951f01070001056a1484008042d032103108441003100442c00880e01c6950694000760301802280c02003a03100c41c01c1020105000c21410030b2041a654043c504c076040c00d0900300c8180c1c02a150106c40c2ca600c40e04900421150181d5206180fa4443e159001d00064a001c2c100488849034a0504c02003801e5040f800500d10308000024a8209408490054081c2c5403e0000386c1c150045800d42140b000001401040070207000684043c50002a1045201201e41c1c404250300c9a540d03100d0400580c1110a4500e50750141c0da41d1043c0e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 111484685 1250 111483435 111483443
    0x312041e0f08210309060403180504140108060601050a02060a0522060606030f15030206030915040b01080d0c030203030f09030d060807090c05091302030c04030c090209030f01020a200a080a1d0d0206070f 89
    0x200c1198ac0d800060244c0d5a25410480360016240050041810a01c035460b4446000c0c20540e24154094200a5440030028900e000c00780c4e032180454201810180c001d2041002866940c82003003603420304000400030b0744580404a031030400e09813146101405030070220003180011440191540c0c00b4003580d68402001404203000300c00010000b12084061580150b015180c0403071698100b80c0300600c0c106400301410705022042c040400045e5000003141c0e4845030703001583c4480e40315500c41921b1809a1018203407410700b880000301d08203c0c0040e00300304603200a5002d000340c041201c4155864819442030980207500e04981c1400747c4040c0c1c005580001d00c0c0c81c0c1d00b520341503072030301c8a041c01415a0840c0311269000250341c0784525040004621305280390008502d440c1d40750401038014200710707101e030b6000c40701c070410000c690320140045060b4927000040d4540d9072464100060140c08800c03007581080384289000741040c182f1490f0038260302d0303001c2c107004c1c60812030740c0310341108203900d01c0215 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 111485935 1250 111484685 111484727
    0xb0405121501030507031a0f0c07030306030b130501060e0405030307050c0a0804090204090c0305010b0a0f120c031d07060905010503130c06020303060f0312041e0f08210309060403 79
    0x601001c5580308a802180180054141c4605600d00320008011240c824200d000c911005c0c00410310200100d00d1304900100009907842c100ba1806801030952035101406603e000c40c1041400301d6016112000507200b803000304002e5488610f0f04061400a03a00680315a10920015050304d00a01c0100740544004040340c010000f030f81e403030f40102d41c82904543c06103030f004a4200514000d5003c1c0d001140e0607824140200d60402d101010240100803a4008000c000c00030107140301d000d003095000c560203c580c2030207210020034002e400f418019000812414400a00c26011480810940e09445860381d8240c540c03841d00004462607000a0144080c401145080a000401c0c071298003000705880e4000d035480740751910800c84203400250f4102d0098014541342c50801d001c80c01203c081e01d6142008e0a1240c0300008541c824480b10740180607105032100d8003103025100090451855008003e0044004c03080f080c2c90303030a500080e11601c0780c59002c000403600280c003500803040c074108010615 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 111487185 1250 111485935 111485953
    0xc0a0e030f0709020a090e040203150c070206040306020405150708040e0403110f150108120904020d0b030f0309090a06120f170d060f0806010e040f05010204150203130905010b040512 80
    0x90a200c0c0b42d500401d0300f1540000d04032410340d0000701c0c18008007891500c0d40050b260a80110780c03038503440e500602c1519100d000046044442c8002c0d148000d070050070301c0f6100d54803444d05100035880303805242d2051050180741d007080d45c0c0345011241030642c00800d440c2401e1812079140d01050015200f00c05100380c441d60343e03d255008100c0c41c840414402c0081803925122030100214030810f03000b02030b441d00705083c3da8107040c01e0702e0101d401e41c0d0010b9800680e81d44080301e98800400720b41782106e60501035081400a044400030150250220440d0940c2d21900c4e5201c2503000c490240c814445d155489803900b40200d11101e00703424441d40503500c0811040410300b107108880d80100130413a8882e540d80d00034403002506c119000040c01c4040e000300465410014040a840b90007800100654a001c0c401000c1110a4050710002e01250000600e880040400603459800c00021018170741c00c0304a001810b00c0403030107064101c6400751072091500f4201000c0c8882080345c20071180640c4641080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 111488435 1250 111487185 111487213
    0x90902070201090513090311060717090c030114010603050c03010510030f0906051303080c0705060105062826040230070303090807171002090f03060403031e050c0a0e03 74
    0x5261003d81c0c117000180101c018500500f0318090022404400d51100c020025501d420103425884031020007842d0030245e44440c1254500f0b11076080c00c50b09542040114071410140c1100740b411b070740e0551011700041c0d5034030003803947ca404248600b40d0301c640c030071400c0310219000e81c0c04050201d91915007c00c3d1410700b601c0e0700f82960416104018403c11080a4000b850b6100c01c05541020008034064944000303626065503030365040c003a0500c07458000030700122190104a03040300d40c4586000103000d800c8171503400341c1040c00c10802c196280250b02c20040c0800c2c61401000d100390340c01403480c09400b004046801ea00c002c601580c038100545a0403521145204204002c01548a0780e1940300e19402e015116080c102154411560a1462000e2000034500482e800c03c0409070a00c00503141d0303a00c01d00196080c1e0440141c55014080c10080c0024541d05401405160b01041c5807000c014440040110844000f01d40c400703203c5030700340b20030b2800743e1090b010090030400003000c0703800303058039508 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 111489685 1250 111488435 111488449
    0xc0b040807020d110102101107021207030b070905090a0c2c061b01110c331305070b0c100e12040e0f06090103110d060216050124060909020702010905 66
    0x20f81e84070070303034100303c01c041d61b410401e0700703043c0701204820320085040281009003400b0344c20009104100803100b0541201042266000a640240a041d09400e22000c040c007440600d01409005900400001e02c015040f4021440500310341d1b5282800c1d0042612215110740402c400042c1c000420305413a03100769250400380400901199030412100320004546086940d0385003888410101800701c03900074000807c1035a207c4c00b8010300b5030041c2030b40341041880d9000281040d443c02c0e1f10b03082030180c00260007900d501180c1c400d0302203810321911004084514001c51400002a510110000f900a40150031038102d260301d105c115848625001d81c002c08541043e00007440452643d82042110f0504c448695000401503030391520550540d210f2034496110000303141d0190400b0396900e003c224a0f581240c90194450280c2d1141d04418039080d8068844043c40984140514000000440030710304400101c43c19900c400c0d60503803409031300c0c20182d0444101a130501c24010300014064980131 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 111490935 1250 111489685 111489709
    0x702010507150f02040806010e0f0903030705030406092307061805130b03062404051b07050a050601060207060206090102030f180a02040603150c08090309010c0f051204030c0803030402010c0b04080702 88
    0xa019207c41e41c1001c2200c0b2041c43c00a00040040c040b20090040310300012040300c1d08071041c7d00d00b2680d01e0b40d036400c2400142c8004080200000380d44040303940343e0500b0007012865006100c1c25582d00076506e140459003040d800c0601c030400c58903940c08201919040c1c00d6142041d6503004082000c2e621900007130304005040300c40741c0081002607a050784d900001a44e4484022044404104505101c041785280007120143d0020704000040d0075814402d080201d09441781c0c1c002c1c100c414030341c0c60b2400203450322810b2042c04007622409010a04030303501130080d40e01c14903544401161991314450420252404601d00d1150350140141d19000b584443c080d140c00b55001c3c60180000700008000c20088904070441141049051230131b10500e00d601000715000e000c0c1c00d192842a802040c20803640c550000a8020a544500c203441c14601d800c50000e84100ca00499240701d082da40c80d05c205843e4842242d00a0000c3c45521424000503460004517800c1030041501c6418448542e000c02c402240c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 111492185 1250 111490935 111490949
    0x18061c140906070e030a02060a180b070f060506130606020304051801081914010c02011e140403120204050a150f0f080c1e0705010603020f030c010804020402070204021e1305060702010507150f0204 86
    0x10002b00e80e040c400c00c048010080507251103c600e03201958032101c80b00010341000500304d0781c442c0702160f007658407807000c0714100c1030041c5c00304161030303960700060340d0b03940140f2401d0300948034003011540240859004074100d42c4480064074440d200b2181c424403220500500303c0e4013485034004044082c000f4411851880016000010707480303429150f0006500700000e11105842c241518564440211f180030398105905040c0740c0802640107030001d0280c050b54000d9500010014400038500c489110655011140b98840f203500c5040200d085510f4409148000041071140780828450800680141500355041c0500010701000301780c9811107500003034043d2540e82d1515402c1c001c0d450143c4804d16810012001007006109180001c1c0010038018006031103168003103605015901c6a804480d85d184800710581c7d4000880c514900075a000030420b03000711f007006800400c0c141041821100c000350143c558a06240050350391307200710005c1c002420a00354a0f00c0c010300d008111030002d84003602c20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 111493435 1250 111492185 111492197
    0x1e0801030c0e01030809010f0302090415030204050a0603081c090209040807150507020d1b0b010f0e0601020606060d0504061103010b041d04020f010518061c140906070e030a02060a 79
    0x5542007449040090750402c2c02810700c60320040000071001001c07544110030a080c0102c0d00c1000c0d00c8190028010b210360181c1040c1041114030307050342d174079000e04150f074030898041000e0340307401820008542050000070180d0034100001c01c1614501c0030b0000304c0712003003100410203031155030104010702801da80803180100007107459020801c00c490003410200e0115402c0185180c042002550f400301d4544a00500c07110201c9940340700042140014441c1c2c0141d070015081d40d64803800e8201d075203d8030801c14809a8440420340c25803000c0b45042c09500000c1c4098103000010480100819010740100c4000c0e5803103c080007008130303600c0030f10300a05080d0900e64440d841c01c2003030740d820081d600b28050400b210f00200310060b42e0f0718030740e812190310a103401902c569010082031081204201c105911031004107068401c0b90341a442c0320b4010b1403121041c803c03103000402c2e00d511601e083d00e5104550300000c0001e40100d10800c9006038606006080701c2424040340c01065050740071203160300010301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 111494685 1250 111493435 111493439
    0x207080301140f03070b0d09050f0303060a0f06050304022b061a01091d0c0c0703081306020a210210020f040e0c0c210903031c051302030c0d031e0801 66
    0x9098009094220b042d1512a01c43c03082000190b20743d01103005011a01c08041840380c01c82211764002405c056101c0d0855028620104010f903807900102ea80d240304142c0810081500e007a4a2500d00449035562201415500c43d0350801680403a002c820050045902d034a0352440102d002c0b029140d54081c07080080e0340c1440d090310f140c07800c407140e0f44e06041c401407000170892646a45a41c0c1d04122013802d078056680c4903041d0b89a40e0b40309000c5040725921590001105120046004018039000a44c2004075184d403000701742c0c0c44418001c0042c1c0038208404006076014540410750400004620659103040e100c050340da000c0307070000b240c144200c5030003080600550704014a0503410403d180c1d20107050901a4000c5565a2045400f40f000c101c0f29500185000c0c01d14800d80d0031402004041d2515006441d8038032290810001c68084103a0926000c50a10184040ca410509401401130130031541c0c20414001441c007078803401c90800c607140c2c08080042ca000855094005410340c2c0d440a194 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 111495935 1250 111494685 111494699
    0x10050c0115050a080c010207030b06011806050307030501230f0303040b1305090c04030506040f02010c0b04290106090b07051203090f01060504020901050405242a01110f070c03060207080301 83
    0xf5071500144ca51307600180340340c4901c1c1e800068610807240d002400c20703199074034100100c03207000c050400701c518429062400321303050340c2100246115189075503080145a03a1150340005002040c03041c144c403040d140d417001c0c03071030300300001d0390f09280c080602106c2c90300f551350a04a500364454843d031003001c100c080041c0120b14102d019241c00a01e410910b80c00c29003140c13522611800080c20007810f80c921100d21b41c045900915100c411540c01211460179440d140c18401020660002c0e412a002481c800000a074145540303141e040c0c80155403000c8541d400c3c100710000380da11048090f60701e40f14005003d6905030070100110302c15090100500a1100316030701980c01d41c0d426800161081c1d0050000c0985a42d01406039022134208698001d041108481d0307918038001901049100b4120000e00001c003000001c5068441c60040c3d442104400b0078881e0706401c0b94540d109500030320380c0030880031403120b140c440902820742c0100012251380350707250340e0501203900401c0101c0d51010080300420040b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 111497185 1250 111495935 111495949
    0x6170a09330204210f081c0b120d030c0504090c020f190b04020d0201050c0a0620040509010312050f0a0e100810062a0f020a06050c030910050c011505 66
    0x82407110825400c00b42089990b00705584d9900b414654402c0310581da82c14080c0d02c1d070541c10640d41041d005030340d80d5040030382807450580042c121030a8034282483c00819007000c0030407074071315010400035214950310000201c024003c0710504c0350411400740408107006000f4403c2d2052084950000c0011140d404041402e140d0700c0c0c41002450640da0130703120045076042101c2980254101c0f00c80000c00c103d4401a0340c28085c40c40b908846101c3c0000d01002c1090650020b940803242c16100032030b1000340c1012200380d10580c00780a130402000801000000d502d6290400a4a040c3c00e040e03041000303000d1a01d500e60454101d1100080d0040040400c0303062005a00c40e614410f850000c3e107501d0402400c20080e03021344502030403c2040d444085e21296401004074501490202c030f40e120401d10b0400c1c030304120301c11700c082c0d1140030482c8000540d503001c0c90440d03d0000c800000765007045008020401402c0c0d405140c003052103070420603022141400c1c0304180c0c40011460440d01c0860911080c0910 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 111498435 1250 111497185 111497273
    0x705070e011802090103020c0d03091707050c0f0a0e070201060609060509011709121204060507020a03121a1008090106060201151a09060c07030308060a06170a09 71
    0x16451000148012507610607415a01050707000b000d03a88481c0000101c00a120300307214090640242e44409010b158035410502d1818011004001c60b240c980b0328240c014480c850008010782c3c0b111602c1886410181d80f284e0006100401110760a0782ea010301d464824800c03102400140d547d03241c24403000b50400c420202810b01881c1c1030781825102c50010f40f0303540e019483d0103086101c4400150b03810400b006aaa480448454501c0d20f45d0000c00c41046107100c00e880c1115881c0c2840c001424403440000c0d106207481d007640d00c01030500d08009111004018a0301107004061441d484003110b5101c07810440608903095075242c40c185024500a401c46040350480002c6904042440a02d41d528501c0d00d02542e030310704544001f43c030008800401c544194081580c101c003010441c4003855001244050880340281c95007102903035900100032000d4002c1c0288008550351280c00002034031000125a80100e0140001640400c55180e00414650312500100c03402d0030956101c001d6005490300400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 111499685 1250 111498435 111498449
    0xe0a080c100501050a0e04060605041b03060b120c031b031005010206090c060d020a090906062319030b010c02030604140d030522020303040314101a13050903040e010b070507 76
    0x8015410580003500045c01c0d8440c0c01860b14151000c40c051200c55807260005020051040145d0f050311b041084044140964440109140840020702c2d544500102d442c042d1000b20850004e503200820b4040b940c1002e0064480301e49080c0000c01301c2c4818030f000314050728480c1900340d0002e190a00081c5401d50007021803a1507004040500110389604060f241040316080005d80c80744a290b804498440c41380d440341c08900e0030208001201c980140004092065008560300c00e4100c904c03503000c840c0301d00c4810340c0c05041e80070035004c80c99200742d0194010038814509082c3c1c02d21990006031500400352001d8135004644055a8042d01040200b61015201f03410188030511304001c02200c900a0b000d0200031510035045090308554060007203802640e4002c3c0c40d200a9080132000e10b9840300718510b010a2680740a6100c4680a42c086212101c0d5000420402080002443d01e4010344070150020030148414000414140304003195a8041c02c090038096403541c001e03050542c50f2082c15032001b0703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 111500935 1250 111499685 111499691
    0x90702010207031e030908070f0b070801180f11030906010603050115020601090b0a030506070305191a010c150f0e010b06090306011a07120c06060510020a06050603010e0a080c10 78
    0xb03001a0f0005903a404485445440b0083e0345840c40c01680070b40b202c0b5000501d04000081e0b01c6040200c503074950243d4601584c0101d0701c039520f40800790389110081c05191703521101c461402070007991a17000703139244110b1381030302081860b0180181030003034100b51035100c0309411076001400900d0307040c0b081a00600030040c80961030034003c2c901a4a512040c0230b0403803500e88034450079802d502c0340d00303140f0700455110041711614a0020002401804242c48501e211400d2044040b51001e490088051400c000c80e0b12186a4010000644200e41d03080411103140d081c20f1840c0821003070710b104031003235900030380340110342010340b100f805084503483c51403984601002d004400454400090f238505441c40742004036250303e41030640000030700035140d00420020181e00d15080d0b41da448220010600e2045600340b003615181c0e810001d884940603403280045c1d01c40c41e65100030070916008240c0111000e00001004660071031002d040640c1e158041c0c588100c00a403070050f8040c10080c20030070110400c820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 111502185 1250 111500935 111500947
    0x606010302040b0906160807080c070e281d030d150e0112030e19080f0f0606010f11033004020603040f0206161506091104050d0302030d020f090907020102 68
    0x84001400f4054140780954401b0900c540240c0c0340718803803165070740c00c41a642d40f190b0161505c04015400030b104070510f802180b00c0054964031300e504290148460a10328a4000100c1c079800207403a150b10104074006031541040300030150058645404a141c80000e1981c40341c191841c441a624142a0b1350780c81260610704001d40200c998085064440280c2400c001000500701180d43c0052071000316440b0031200840170a5044d8202e0304401c40c0c000509856040c80030754200b40c0c9868082c85040c0700c5420a4000036602d62080c100d00340300f0380d11810242a01c143d0100450318503002107003401c041c0220390002c0341c580d060905c8801034039000602c81140c10b181c40e90104826001c0030f0001801554400c504204558a11040e20310054000c0040000341e160ba0402ca4081400911540d850300d10346200071810031034a004003d0100707902c00000e45498500414401011514281642180818001050354403081c0c0024050051000d04203511129520100104131754058091070940e0f104000e4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 111503435 1250 111502185 111502199
    0x1150207050f030d05070201050403061b080a1811011103030a053c0604020720041104030201080c07060e15060406050d1a092e05060103060302150309010b06040b0705060601030204 79
    0x2040340d4456500d84151074842e47e10040e078180c061604000c9c5014200389400d0740b284a10700042161a10640c0c941c0c6250301e03041411800c844000310003d102905c02810710340031401445410412500600d032100c5044000e01d106030454005030781c1d85030016180d0061181c0b100e4141220b900d042408900c064400ea0041c0310300d00314100780c004a031005d1080c2c000207803a42c1d03255815180000d401800c80e494115003450500340c0d040c0f4031000184614074084440d40b8070302c80070040d101581d070b040c0c5405e080b90315885800301e115009010100c0d80e0546139001443d0715002480f50125014101c8100c030202e00300f40741040107883d9150002c1d8045c6c81c40b60192000306843e00724082034030f444160030010a4480c00080da0808481804030590303082c8000c0c01140d4a501c17000d10641c10380504108021980b078841c01101a6850340c030000e58030901290301c01040d40000b00040d500715034480f000142259003000400c45640007070388105800c4c44081030980900505008465203e0000d180840c90b103414480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 111504685 1250 111503435 111503443
    0x12060a1406090f0705090a06020a03080f0c070206160203070f0f05010f0e04090201021510030b10060804021011060705030604050915010909060204050406090b0312090102122101150207050f03 84
    0x2070085030f6508940030458041c001e000310340050030054100c8040b03039162003010b5a9410001d80c22400034203250b0011ba042940d80c0c0c4c0d5280920508494241360165940030000b06400080000c60f0741e440d620b44c100700580e4100800030041181090032a20b5501c5c0071351440c6042c2c120b0f4001c81c144929030180b00a41507000100c0d4007015002c1f0742c00200ba0070319000403450840c80140428800103500705006051100000300d404580c450024100359598204020a0004061058101240020001ca001884d140c5240e104000061030006044e1074030400c0c0c40d180c98020788040012841c000b06200d4142010300035268048010402842075580116440140140502c50743e0302030b80e078031a020340c100b10840d01210001c0400410521806445035191802001103a0000e40309200d900142c801030321419041d9988514140c0191504d8400c55a4000320350303000751190581600c00301c1e0304640410503407038414041d00c00452800524400107201914110180c0c1040340700306800c05041d031250741c1c001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 111505935 1250 111504685 111504691
    0x9131a0405190f06050708012108030a050c12010909030825050309070305030c03040f15121107061b02010e1b1306050310091101080606180a0512060a140609 69
    0xd54000c0d201c5026080034103800b0403079103008004c24240028418000e40c8960124141e81800c0c400c40301d0055000c80701003045801c40b10060a400c810701c0010010300d100c0c3d101c03c2d03001041b2209103203050390050800103800d409808c00da104030341d605800c40074164818481c5901004c088405012220070914a900312031500e5441000c0100c00070000d60808000e10510004580c010101e07038450032140310b481c4c1c60390002d01a4031403040d0410fa0008004c03400e0000001c000f0101c0c0c41d445070b0513035200c4484c40580f02c400324014101400b00706101c00101c00b40306282c194504482801a070b111040c00017400e5a0103440001e005a205c032180d10018162048108a001c004450041441046000c000d0180c203940c0d104c5a03040c00f0320350704162032010380d4100c0340076180706501c1d00300e031803486000556509205175110b54024606000c0034a41132000c0205c207038000c200404003840d2940e100c0000350310b807500400214094001400340715140d0941d004d10b45075800c090380c11400514003e00440d00d828001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 111507185 1250 111505935 111505963
    0x1090216060b031603050601030506060d030f121103010b030717010503100b0a1a0403030311181e030105130203010e0304030b0609040309080a140607020607021b0a0509131a0405 78
    0x3400c00d0702c40b95a02009030035a03180352410021481e60756420540c1e01c40700e09100554407806404005025071400c40b029503c07455241e100c254008001c5103007104e4800000000450142e0385000e0300d194420b540c801b460080c0803502d070095407407804010040482c1c0603101000c4440c44810014406070341c0105146000703481403000040d6180003540095141500c0303a000c100780810340780c40802d080346100c00401c2139030b02a4600344802c00341c10040c0c01d05485040390003014203845942680b00c0780b50416a1250200c00f401000c00b41219820000342100d00c1541c1c126100c110014807031045003030a015888001644078051400c1a141d900d480440c160001c040a2041000500107800c02d40160614009009800f00715000c181c000d1038840d5006d01d9240101626101715400281000e10006540703101c1c074640d50103010340b00d84900f0409d0340c500602c1d60690b80028018030110b490380701c001d042441074080d4600c4003040382107402c08203001d03180b0001d101d952044e40c8c420440401e0001031000c04840003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 111508435 1250 111507185 111507191
    0x80712020a090905030301051503060906010f030f0e0715080c09060304050307060603150f0e07090c0201060b0c0115050603040309150c06050406050f01050105040e0114030a081603080109021606 85
    0x86200041040c9030325040380030031520307055007681440400130103541a00c9083e5003800c60341840100000701c50000b180c0301d41e404a40742001074519403007888070783c0704c3d107040d400c0100d044464860349205484406520b80700315030110604014920380750404440d401401e007455107090400c94000e440324400e24041d240205e000001140c20400104101c900c4580c00400801500d501c03880c01401000324882000b4088d0309001d013100e07a030181407081d1620781e801c1d10010400b8600d130806440140290b5600d082c01e5550750380c40011603451034802803210700c40c0b030400040c240d070130b0b2a44083da4058580145006590038001c01c00025001041007043e00e00300c110340c014003140e9010486075120340d0b000007031400781840c00303000c00c00c1074a80205026811601d05005182e80b500011a22806075208021b46143d1000040061003400300006081034005400c1d0740e182002e64580703003040e0384819000419004a41146010302d980701c02e1050162404040c103625241c5040034403000e0040e02c41d0f01402c0507a07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 111509685 1250 111508435 111508469
    0x906030e03120c0c0708070e0604020903100902061b2d03030a0b04060f0605120604050702250503030708030a050c0f1821011e0506030601030b090c0301091401150807 73
    0x703065007a1054403080c5411201c0d0340b51160704a47d101e16182c45548440700d0708402240b0b1903d400e00030b8030a6904050001d16030944000d07420b01c0601a842801d1760048ad007005201601c50f8a8042c03040c02440c00700c001c01e8410200b91201178100b81c00000d01c00301801444100c1d002d41c0d404400c03290020040c400206101ea06d0340c00007402401e076a2300600001c44100400502c141d08a00078004500c101507890f902075895206000565004888080050f004034800c4046007480b0640c000603000380e00a14040b4640f1140402d255034045001990602c01c0801004861412801482d078405522007505017024806819640c00e40240c1550b202c1082d8403d00c1e03080700e62134500640400b900c403001001c041a0945410b5402015051403405004503100940e014181c01e81c010a40900c1e4003400a2802da031035034441a22a94000d054a1011300884a01203003682c2c090040344d50950140c0048604480107100c0d4a08490500c500d049691101d110100070316180480c545084420300c0200c20320100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 111510791 1106 111509685 111509701
    0x1090617010e1015080f010e0d020c06031303020c0a03080c010e0303010f03080705120304050601061707020a080309030904090606030c051e0409021201020a020a030906030e0312 78
    0x50301802c1d40c81040f20031a4400c3c444070080e190081042c030380310000d0b141400c1c2e940e00000c440d0303911100101d0106030240b10609100211340010f00300c480118000c60000d0000a0003140d805c4038000e214814180280001c42469100425031481d8903124a4488910b8025180c410025840c09000440b0700300e0000860b030580704c41c209007111a41c03070b641c3c61007040d9000c88412585800b4034480350001d0000d8101860059104401400c05981000401403266451508016112207038609006405070045900f14415410a010a540760b56964a441c5140728011040340c10514002451050000ca81d2004054034410400216031641c0c400802ca01e1500e008506080d44502d202c070b081591410386d11007135840d803014001d00f000b900c2d114110750072070f0012480800581c1049050004043d030200010000c9c240c10b050400111540c840f140c3ea482c001c605a4407002240d1001040c0c5038 = true := by decide +kernel

theorem cover : BRFrame.Cov 111330935 111510791 := by
  have h0 := BRFrame.cov_init 111330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 111330935 ≤ n) (h2 : n < 111510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
