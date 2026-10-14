-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0636
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:51:02.569446+00:00
-- url     : https://prove2.me/submissions/60172d1d-4c18-452f-a7f9-31318a333b07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 114208633 ≤ n < 114388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 114209883 1250 114208633 114208651
    0x60402030103050a12020c0d050f0601050603010608070f020a0c03150f0506030309040f0905061008010f020307050d240b0c06060d0f0b040f0203070f1e05010905010e0d1a0402010206010914 83
    0x300704045c00b0f0580c208902450000d03488a0781c8907402051003808038030100e03110010426a0701c2a07807a8030800040b400207001c0c070800125a100012000c0d0f004484080c2135003168012114050305d2035844140840340c5810854114024607904010a00c80b405601c101f507821280030f02c820329080012940e03d02801c010548169240c140707550644042d94802c140031504401074800340d00e4818907094a2441c0c03442803610543c41c000d10700441c211140b00752070207030041d9074610b49403c04680c4002c020701440200c400810700780706c08403050807000000004c0102004000c0e80c2d00c0e2040c41040c0b504083c40108003500598408808000003022211021126980f01e01c000c02980c840d07044c2070951074034003c1c0082d0144905140407407134a0290b00c0c500200d41641001c180807180403240e04100900e503100340780c00b184000509100070760040340c0540d503030381014081b520490090744071140900c012010191518558000780300030744d41d05008980c007501070b880c002d11851000c41904400060000c0c84560 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 114211133 1250 114209883 114209903
    0x30d030b0105191b030c02150a090b030a021908071101060b030f091203010b090f0102012f13090f050907140f04060b3c07060c0903020d0b010e060402030103050a 71
    0x42c1d01c50060341d26071500700300c0e203800e0b0356100c13000c4c600544000c0000380103038860b41d0f482d880d040e40c040402d4100c4101041ca641da030070700c1a181020a00458101600302900c1d1602807128641900071480145810022540c440480d400d00b14400b8280802c0c9190f0001564105072052158224170021a078110182c00108042d595030480c0441c104006080d1104069000000000e03e000780c00000e008112000c90700560034400400069081704e01c242d80c42d803c0c4070031200c0c0803502c1c1141020145528119a110b8a2030400010801001d05559070400d00035159a40071044004003684203480d401071844009102c00c1c0d081ca01c642090b0602068880c5c0b05141760030034520191a540c00c110000c261a4903e140c07207442403203000c9103002d1118559404400620322000180480c8001518919404541c46281034001d880301c10107032480340c400d40c1c1400345071000000141c48501840c400709001c3e0340343e5003071941001050010070002800840c031481c014401400812400b0a071115003d500c220421 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 114212383 1250 114211133 114211177
    0x1b07030518011e05030613051306110c120705060c030c030c1809010e040b060103060518090a05120a02060108060c0a0804030909060b04030b0609150910080106060905030d030b0105 79
    0x2a210781c202162001004240c0c08045090f60300070020b1800340b90103c46503c4804003484e0050210b4404580f1400d02070000b00680020440551000d80c802c841d50700246d00c0c1c00610000549014105194064103081c001a5202440000e002d1150031117040c0c500c2d01c4c61410603240150782c03030001521a007a64500000c41a048100f403602303010400802400daa1484d603035034812400251411078042d10010090800507601d9072207482040305070b4034000c00940f52032408107464112100010040c81d0103101d50040d01000c20000c0210000e900c0702003900d00c0e43c0307410302d40c2d00908245043e8080e0b0416400b071343c02d01030070549041c00d4030780d854690f10b80310b109941c5508003140c0202c11a4050012986040c03004200c11b4100380080007a2070060480c860345841c1e034424000d0b40c0c402111002c0c0f5100740041192210300d000d00c492a0030001e0300c0d01034903403030740c44002d00780c00c4170342c0c507441200440c06244007003006041c14892100780c400d04d42001c20110790207000203061446181443c8c80c103640e40180355 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 114213633 1250 114212383 114212387
    0x7020307050607030e01150e0c070c05030a05010222211b14040b060906030a020903070320091302030d21090609051203041a070e10081b0703051801 65
    0x2652416030410120340807030610000c05401065817221000c2e0075420403010f4048503688488940c12140c8500d1080710740d0b03680d00310140b40c58200766002c5510042d003010028050340d0821130160200c1c010000182d44d41c070459041000d070340b8a1801c03400c61000c0d03040304008080d9203c01c41d40f5081c45484901442c8041443c20003803611003600504004501d0034804202e0b4021030300c8440045100f41c40400000e131541c420407800d0300130b00f00074650141080001584010b81600a456103072009021500500d480e50f407050300101c50300d00750100542c08001e40718141c0c41d00010b01900281c1d150886240c5001c59004240c81d0b0031611224030030b0003444102d10b00c98102c1c000903d4601701e07a000007003101001502c0d1820280c00c060340181c80c02e12884030222040555101140c0c0215442010042d81c0000c0901e19098480300400180a01090b030412003007039210301c0b0502240700c140f50b41d13007d624548185000051000c031001020b00321000e2003540c0000e50404106c850031030402042c101c1c41d101e89401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 114214883 1250 114213633 114213637
    0x20304061a15030606070f0b04050d09090204050d080a0201140c0c0105130506061e0d0c0f0902040f0e04050a0f0503030a061401020307030315080106180513080f07060609060f0e1e060108070203 85
    0x4004c1c2042030234000c200c01d02c0b401041d50580c11003996903104025940300c0c0c40805074004c40c00b5050b4030050418107440001c0f400e03001401c3c5600b0074000421030740c6075403400407444c500488000039921800503565044050078032441d58008840c85000410b41002d0f240c15070703140c00080140380107040b00b40042d41480c083d0901d50034103440c020040072030002c161a1801d1001c03c140310b06551800b1a4a001c40c0e045494000e132000c2c0c2d900802011140340c038005e124460305070b018206880c076000d07080e40308000c2000b010003007801c0b501031402550350341414410380040303500503071041e101e1070f00c441030b480010781c0e010040314800c0c0e07090716003c01e4036820752560104500680c0e01c070305850342c030301100005d8080100c22003440385011030074108001d82c4c40c0950105001e0009000500140080100c0001d600d4210060404903004010010f203054039210407204491303071a0001d103c04484040204088070245035402d601c001d8940d413001c1030240950007512001c2c0302400b402d052000041c00140e4803842001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 114216133 1250 114214883 114214913
    0xc061a040c030f0e0601060806010c2a06020d0309030509120f0a0b1b04050d0605090102070c08030915041a0912030412020109090e060601080901020c01020304061a1503060607 77
    0x1008100c1d211500039006105000c0b0215140781040c11283ca0100701058050494500e6280c00c02c030b03540c0710380c01100c9048501404440003171071000740007004680e01c1221031180c0d215200301d9040c00c0c1403100180c40c152140030101c0400d4207082401000aa00c031058605041080d250203a604d040d03004800d080031198040d4682c5403088842d902c05200400010a00920365081404a00860760071556807038825400382c5508550075082e108000b4400f9230107168005411000142014000e80d22041c1c00c25040e44104030700e60011515450f245001d040400f40ca10380c074417000f854079241c82180503082d008403000944104011031503a5a40e202d0061602000d030700c032401d03a603465480d00f0144408a550f814113034000b90f0b0b001d10200b40c80080d0f1144219414100c0001c10540e5907240c0111002070f0020044083c65400b400003c150b48001d00145010380d2051308045191fa0013410304401034110b03c072203548207505d42c0036040f03489040581141c1e0020016140c03a81d548215080940c1e807140982 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 114217383 1250 114216133 114216139
    0x2702030f150109060c020d02010306170d030b0402041811070c03050304080d0e091f05060a0314070e15090a030c0608070e0a270608030a020d0e010507030c061a 70
    0x81002104a00200c050384502006444214060362260045aa0309814010000031a055840d80d90262030700c008104100c520500d008520329884040ca1700b00304085211801142c1d2003001208100b039058002c07122160002c0d10218109450080c038415152220480900492382c0d44014220401d5030b41b0444280c0741d00100090300b00c0d542c80c81c009039240e0162003100c06600170501021403041c42107200700c84280b4002c3c0076060546600f035079403021100040c508403450328071403000909a00c2e003201400c81c0407115240003030501016064403902c00350007404003040000c80c958000559890241010641351103400c9140c50740d002c180400c40c9404c607508042c010380115071001821980c4080018450101942d891654440c540e0910118800f50700031a1140e440c0c1760518020b4400b042d1540680711074404021889660b1021007500f5036014005c0200103810440a4821250304840700020f480c5003072900360b240100c23581b402061110300d02c40c002d00e0035843d403101f056100708010901e50301000007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 114218633 1250 114217383 114217387
    0x1403040f060c060f060b0306120106091d071d0f1f032a03020f04020a031413021f080105040e03070204061511030405030a0308091005040b10090203102702 68
    0x1d0080580034510400c0210703800c5061280700c5451260364007408046a0b20805860b0442d1908010413036031405490b481400d80d0758924001031010600d0003688801130a20340d00003862501004514240f800035080030300c48021765004c12800c26940c00b5501d070700402c85150b0090329184c802494001c4024403150007404601c1d0744010040c000c0c0c504503862140007111501b0744c902000e60300c80e01c00c01c00074800a5480000054041e0042c02e003600100420186c4c0d1900040c225586440000a41001e44110151240d09a0000110704101108040710300c001c8540100503c3d90820081c844001401410300440c2c03a202c09a14110041094035084e590082c824030041c0d0b164078201034030688054810300002c03404583d8104030980481110b09a80d40603000c1e2001c44829101580c0586001d0100ea4051080e0140008038446c030348600c5016900c241c4c06000d040c20500e5034030007011842c1d044024818410000d122180b0208050301d4229142c00d5181c00c180d004202c18580042c10710141d2194080c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 114219883 1250 114218633 114218639
    0x11030c0610060c050c041a090117060606030c0a0309020f030a060c0801090e07050405041e030903110a05010c0f02152215020a0312020f0c060402100315031403040f 72
    0x4041021842425440040c812a550340d0070300b2555083c0224000e41642c202c01c14018007410300b90800c44851807001d441107041c1036004e0105442000c243d00810101030401200e040e82d64007804803a030000000c0380d0403411030802c881c1801c45481540340e804203143c0e903541c800781151500303940c09907261002400c0e56045226400e04030b000d000b00c460040001900c1c40c00100b4090254840c1e012200400c0000f807a00780c0c00c11052000415010b88152040c000b2a1541401011011010741c0391511035995100c090380765140111441c012072414038407038a880791050100d030740d014806014150708400091241c400300d001089030801c2c0d002c0401690003000510303400040102c10542144449402b8510a40d581c4e01d2948502d41c0540300d1010040e0450035480780407d226816035144c0c000c2c1c416005140507050308001c811035110b0070044103070741c0013807040005524242e9602c54800c0c6140c2401c1c0002511040c0344120400280402400d1018620810201080420543d030150800000307104120b52 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 114221133 1250 114219883 114219907
    0x15020f0901080108030307050f0c07170304060909060e07031e02030703090c080a050712030509030102040f0e0906090303070c0501060f140a0b0a0e04020702010c12050306130516030902011103 84
    0x30200d4852030105650100004041c1c030004201c134402c440b0b60b95010b0400010900c400d10540c41031601d110380d07109607000071815052445100740007110060081d42d582d498900003900d0004035500c15000d01d403400d1b0042290f52050511250b0008442c540040c02e090404031581034540c000f01e443c440d041c030200800c031105030150300504080d4040c0c00c0c4282c001d0303922520780e0f07584c1c3d101c0100109180c01a040c10040015a4411056030342c0c031034140310f424142072001180c22600b05070720a413000c80140304204000300e145009540c00c4198440034008a1070440c07661540c1e48400360040b82003000242104051100a500c030f580a890360a0040c1001c0c0d0b954042144080301803561184500c1800c0b03400501103200c48215181249640c4660445a901d107007004020b411407001a410700c501940c4c2440020344a9100c0e00c8032420540740c0613102d003080020301c0041c040d0005c41e4500103180c8000e2004a0b042401100358000c03c0c2d103408100701403a8030040380c0001c140d4100314039a01c404160008000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 114222383 1250 114221133 114221137
    0x140a020405010e04050405030a0c03050d02030f0610030e0a032003280503070c03180315090c15051e07050a060207021003051603050a11160b0105010306030b1315020f 73
    0x800981e500d043e54000181000111042035900800b40e40c000c1111503039240c0117518040c5618024245141000482400402a0380c41212000440d0502d04200301152a00683c189910f26240c941081074102c110603141d640c1c1c110f60400340c2407266040071300c10000b00307030700345401340c800b60301c05503512842030b40820600a00412540311581c508407221a81240c0320748142d80c45a8017581d541d00e40c1100c103440c252a5003e00c000410100d0700b0600c0088081000002d010b01c51440e00301700060703420318070306202d042c10016801080120340001d02d42d1491079030140903158062070880c881c071a208401c0103120060710480b24000c045015000c0f060040c040d00e40c0c080c14055009031441500c42e143c54000f02d04444044600c00b4007448120b1166500c5842584100e6000b101c2401c0060440d05208080900e50071010303c182825280304a1017080154a03000c150040c0000c1c00d09000c07641c01d41c0e031445000b0500820342d400c114081c49400e4144180342e0141c018080d40601704541d03034289412050200d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 114223633 1250 114222383 114222389
    0x9060b070501140c07060c030f05090616080106091a0d050702070608090c1309020d1e210504060f0507021e090609040b0601031505060408060403020d030e0c0f0103140a0204 76
    0x6540f80040861072049949a6144120410410586414010742d6210000d1011060f09001c1540c2c0365100c651050304d500c11135010343d81140081c500362611044480c0d8080144100e0400c000d140e1004000d0550400e00f0001926420402c286022100800003002c9004150710340d070f007171800d100600c805150049081c500366100e60352446035590b01c8021091707a42000c490b900e90000118540307030700030007015440746800c0d520041c403419001220b070311400d062a0011510003c01c0031007122003406c00c82c04010030204c4c6400c24560003007245410401074040d0280744642d2040c0160301000b0011188039108513180a58001c003151018030020b16900c001d02904034509000b070100a01080151820898291140b580010802182c0d580d0900442c06003030100f00e01c158000540801040664039440604041c00d0260010600d0789030a0400030314005180070041c050618010a05081c101c3c00314645c00060025186040c8050351500101c00400002e036910f2a100c0364032041c0b0615424680007032040b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 114224883 1250 114223633 114223643
    0x2060712140705060f04030c0b0f15011e0c05031e0d11070c170f011107030207050909060c0f0d0c2012070609021c05070905150112051009060b07 64
    0xc60a140c07402407149106016002d4070707652040d0006940c1da2505110366900034420315040343c50003140e42c0c1e00e40214609642c8059141c200404001c0c00700281420301c0d20341c0c2e6091814290300850200b601c21040c0d40c0344806e02c10054000a60010300c039007002100d03488400c03141801440620f02d00400c00e16000321191042c0700b403d010f085c05007503c80200350f48800c1e0f044800003800c94904542c800c080070b98142d80e801c49009403410010700c282c00f8411020001e018a45059884000e40740080c01c14505800040c0314417140320138041034003000108582d028032445080c9d41c1c5d42c0f24060103107140d805031592a5200700d041c961841c80c0c6540c00b80c0c254145900b010994695856030502e90f41e211084205c01150305032043c032400000c0b40040d01310844032800500386a948000c2d800d0031040410701c141d015101d952085004010361441c900c0b4181e880a40f001c8440c56425040e8002000c001c62100088040b584841c0803400104003415004000c0a031150300304802c1d5940d42051866402030802aa1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 114226133 1250 114224883 114224897
    0x3070e0a0b040b09040b030f03042706080601090515040504210801060509040b0a120b090d03180f0201171303080606030408070b1f03080408010c140904110702060712 73
    0xc0d4072031035141610180ca0241d83c209040000034003d00c8000c214200c8184e5041c490700b410343c04500f00c02e01c0208082c00541400010304500d004180d07944500c03030380c54251a03130300d800c5c4100021807000c20050705658088a0101d100d0700c1d01e00301d400740704003c04000ca41c803501c0c220500040106200c6641507030541d00f14041b000e04103882023550848000d2042901140d4100700440301881c05034003940da880c80091200040c661180ca40c1e60700035407402000c4030070b0400310f020b10501c0c003020854120076011900e002d0051140c0c00d41c0c50052980620801800c0340d18110040003160300170446407000304440c604605c120714111401940ea41c184031b4082e00890b01e005c001c03ea5a04112085038812604501e1251804055075940d081e1100d0061980a403210900c80200d040101202108011805a03042c02e132a2410801c481e03003107409204048061160a1450760940b005e84070a9500d450700860f400904468407aa1491192051400081d8000c4001407000c08011408401d104040c0a0b591000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 114227383 1250 114226133 114226139
    0x306090114070e0d150209011d0a030201030b0f040e03091e03060103032d020a0311010b0904081308010e01090302010605030f0a120e12300714011103070e0a 69
    0x2508031095906021040844140000c281900450590001040c060036400074000640c07a04c101d02c00d000585a044250000741d41019982d0103007003414000000c1039058440d40c80701002501102d45480000c0c10300d03807111a044065a1410309c10219250060414001101460501905c80d4005a100b61241c2c90400c03030070507180209800f9042d48400600102354913400c5444c01c4d81c01c0501805039807002d078840460327841700108005440c034103110f0a40082a190b480c501d80a0402500309a0201107a80f62950003805a030f40c41c452a600301b42c0010320070f50303118480391b4201c0c003520064000200c25801c0c602000001c1a0550080c4d0156011794000c10070725491307404161703e540071200141d010b80e01c40f0543c100402c130004035030310420500c1e080c90308084840c2c001040345941014404c010b15080b42c520b0611050005020389843c250b0394800102030301803109989140d0156030005821400d44580d5030006c3c1c0000d600c00910a998105610784a00e00b2580080000326002445406405050000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 114228633 1250 114227383 114227401
    0xf0619120b010513060303120e030c0f0c0901230409020f15180402070b0c220b030703050a0204060215090a1b0f08011103070813020a0b1210061e1701060e0306 70
    0x1002134030380c035640c0c6034685d0104c200c02310043d00300781ca5180c10302e020410401c02c0ca00e0b8204003a58444205501402408610404002d2a604160721014880d0000041c070000c00035036000c207440450040f04d0000b8100c07041d00101d10110f0812004507004150000b002a2017402403002d0000100360440200380d030711603071050009034060182c0c001d10b82c01e22000440c111f001088040c200540c0e807004038440005241d21124209030b001d50242e4a48040002444801d640c50300981d80e00041c5030809528003407521400a550c0d03081c0840103192034041e08089084000c041c00b2500d211904606072408841d141c3e03031140010461441646200022202d0005446406000340c5481818516a084c110782d03ea0380f09560b00c0100a00070a03041c090401c0b5140140e480c081c0311005040d0111145841c0c9121011052000202404080410201d94420050640c0c4540303c020b03c0410a00107000c03000c1202003d40d0708034201401d00355901d544100204000c1d90081c1008074145040341194499141c1c1010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 114229883 1250 114228633 114228641
    0x7080c060a02060f280207031b030509060a02100c0315080c1e0d0f0309080c0d0c15050c030406020616080f010e060118030b06090108060f0619120b010513 68
    0xd000243e000a8009184042c0c210301496000702c1c2c0031100131150304032410760900002808203028400b40d012031708a0502d0b52180d4845604004040c550380072051a4902821601850f0172492144000080740d0748030720300c24090340040c960004024818001c515070060046e107a1070703000c041c298407003890008030150f00107003403085800050029001d040c0b11130820a4115a030b680c1240c1c01c00d03014482600000c50860342c007070341c0c0c90281d41d504443c503040030b80207400c001e170140c019841a8802d81215000c0b954000c403000840d4003a0b4449100344000070b500351181d00400031001c016000204001460a402207240d03071160544100d2070f450f0340e9950905881c0058180c0301c41e01da0801c02030051000011000300240c210708141000e407014104040e05403030030611034000311840302858003844a1420300210071405400580c01401c417525103003048031807100c4001c02c801c4c40f480c0c0600075103506010a120540141c229042d0914030201e0034100a446002e080c8200790148100b295440d500e448a480703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 114231133 1250 114229883 114229897
    0x10b0d0e06010b03041e081602040b010c03170a0603080a0804060605151605160801020712020a02030d0309150207050607020609160302090c0405060a1d040603030f0f1107060207080c06 81
    0x6543c500390307100c545a20103460741c80c04000606034007410080021961180c00b030042d0001c0192243d5002941d841403109031003181800b80c1c11312010300c12010006c0d0b003109101700000a0a48641d07140e82d10320034443e02900c680d520285c986d510005103901e4132b50f4401c4416100d58091401440103070784d61070511040030f4813081c42005006e42400f20768001c8401b100c850740003502400881d9150400c1036000201103000743c1c841c00385a0350000e94001000080c80c4602001821400603003400c0c0c40507004aa05c4845260a0070205a921141c0504100c4540c20602e10329680c2c0c8021500c0e88800d15105666070340a51350741c0f0241c415000012084000011244410903081524030340e83c900e15403e000c0703156006442981c40e8401848045401d441e450054800c801107503486d01034100c0e0f40409000d1407005400c40500642c1030220a0010981040110400941c1440c000e0710680301d0440840388900303450b0203084180030b04240080c0c025800114401a221004180d1791110502020802c00e0700c1200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 114232383 1250 114231133 114231149
    0x30206040308010e131214040f0f05060a0813030c08030708010e0906010303050d0f0b030319080a0902030304050d080909090619050411090402060f0705060106090512060f15030105010b0d0e0601 85
    0x17446013800201c0e420042814001c290509143e6005800c0c01d580007a0041d0f00903090840c82000f08002500c03010b0012402042c00341c0f1500d2504408503402030100c040140025082d480510340700c41014071440d06080785542020300075803070b400c1805c00108011004e204103001c40c4101004a0071100000c14000e04907035060b25100c4c0740000450656002d041005805440f2035562200341042d07450510060800000c602d4104001c010300d14000360446002402003242c2d42c0c0b814843c400141c03000001c44d8182ea4007251841d00c08032091400c080301d0b114020341ca540240d00d03001400409680062070034000c6242d40221680101c00981c03110071110225006000c04910f055010701d00d0410340000790704140040c050501d480804615140c0680c0040d80c01c4030543e101c0c90040060703590185070000902002c0380c0351300c0803d07050b0f0750031a40c07590046c0242c08080860710100f12482400e05104020745000b1380240007a44e9034a0b00810a90841d140d60601507040c011402242603010443c58144d55100f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 114233633 1250 114232383 114232411
    0x4060c050a0e0f0d0203070902040314060907030605061c0614070c0b0105040e0a0c03050d021006050d020f040e0a140c060405210129040e010e0307110d060504030206040308010e 78
    0xa01001031895100c625260000c12a411301c0c400360b2001c1c40040301401d02e5103c00b5075510b10794a454003445d40140d404c08030b541c020720140100e000020443d4402ca81d005400460251104400900b41e200710724410a4410030f03d80c00c03103007081a590807958110b1071024540051f542c032580d0a407011404120010020040d00b0014400c038541075003c44007605405040700c3c2800a05d17610100643c0c26034106503640d0388402e20840c54240d04110b4104aa02150003e004071441d101c0400e100c1c28020f98001d11400300d01c40361620302d031504d030b01064100a038001211004407450410103510b19416442c0d48050040c030718407921034200035044408488018204402c0444440e40d208840c1050442c0b2440e40c3d5251030b0000d0f1b1614546100b10301094004241e510441043c2d0b0400045038281d03074041c0100d0341801c8210710005000710030760740d003541c102c0d03104030a90480000007003805105010040070b40d443e00b07050000389940020312038411752007902c81c0f5516903241c4070588500201114070069014034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 114234883 1250 114233633 114233657
    0x160204050a09050a0c030c050f06040608070c021e040605180601110102070f2108160509030102040510050909010b070f1e021008071404050603010b0a050f0f0304060c050a 75
    0x210340c0c04168024408100090460341e9940c4a0b400c2c224940c200741c1c1c100600042c1401407160301c044072001403600310b071078200c035000c81d40125844d03005502c207900038081050002038541d4054490941840d42c001c081040e95001c641950000144909a0782e004900c3d00700301240c2070820744d4030034640713000f9076030042e056580d01d40c011240d0b0021a000001503540a0200e0f10004000100909500e4071894208036201e90010717004032540703180c441e018200f0a4101c144544a81140b450800310302641c0307045942c42120328003080c0a481141e1184d60480119065500b403150f01c580600501c4408603a9070070180d81c1c440d50f038002801500005002d050356180304100099049a50785e85845c3d0060b40d0707240000664000030420030705000300c400820000800c0228990b800103651840201c2000401d0a0034248070100e4080d0105000d40034007510002480a11907000d0415102c15071310080c2095500c0075000c0811000d50025a011501c0e54103041d9406a080e020384159468200c03155102c03450000c2d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 114236133 1250 114234883 114234889
    0x90702030a11033a0e0102300f130f1103010b010203131e1203021e03180f0103090b0a020405010e0108150409060204171b030705060307031a1201090c09021602 70
    0x40d40c002e02800c91004000d10b90a16020780a403c0c0303066000103803140c0c2120718440d0071b80c2035081c60507821040c40c40c01000e080d000b0101395070000c00b540810302c41a96003441180685012500181c0210507450b1112f0070407041124804d1280d02c00e90003400918100c0006a130349005052840344000ca40781814000c1d41104800350143c00f5a00c1c2e0400007503561800c0d4810310656010041c1c0040e041951028201000d54482180d03142000d0b000707602e4511a448181c01600c0b4a80d49148150600381094105a2103604040d0300780341c1040396407000381450034810740254003520500d4007240351024810015802245a41d20404504030100415942c0e041000001c0c0541082110259828400480d41a4041449004940142c80203109108044a03214200d2100507840d034440d50100100344000d0311032105803a008021410040b070320f4191a1600c4c6d8040e00f4401070190440752070300e511805208150440d03590103001d02c00c603100340da40b940044000d9100342d010b0944070700001508103006007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 114237383 1250 114236133 114236197
    0x70507120903021305100b0c12070203100e07140411030105060730142b0609090b01031a090316050a0c09021c090302100b01030b090702030a1103 64
    0x3955440c100741410340b01d41c00a6550900c007004c0b03d000654450402048002d001050310160151400050a20708041c450540e10601d01d0202840844086020011510100152000c90856500030b1010381042652a41d5400c0c640c415200340300320141081050713040910039000712080d041200b0346543c0c20a001d02c900f40c0d0180d0400c0f1a42c64403d0800004200304040142240442d2000402902c1c10044010250b18208056045441c0e040140090880c860900d82080080c07480c40791150712000001c3c0c40c010b2655031b0015001d0340c1440741101c01c00414484c2c01d4107072403080c58012044d550003489444003100403201c4003071035401009203a216060040388110780f240700714122a00b149040c0c1c1d43ca0484903d45c1c0c032240c1c83c0381c2c000c5290250b0070000031b0704040404000300308000e00d036019107009541d00480ca59440785640e64003501d10b00369100c0d81000301181d601610880c494200910000d560f0f40c40a11984005803260680c0b45903600c0200c1110203808907104800f41c442c0300044401091 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 114238633 1250 114237383 114237413
    0x1060c120c050a060c03020d0e120d18060e07030b09030309060f0c0c07180605030a110105091206040f03030b0109060e060d02090d05011b0903020d0b04060e0316061103070507 77
    0x68403070b109000f000107644c0e0069180d00e015583d0302580f80d120400c800010364182c3d0b450490550409580030501c4911001508d201449041c00032481d6400407401c0941c800c04100e0103065a400d021200c2800400040c0c240c0440384525161001e0b40c4d9010030480d200d01041d945110b160b044240811003500480c1c2c40c0c02d4101c56841480c0d450803d41005842c548030256100d00000f010505085810700c2441c482c00008040071360107814a03030a43d503500150400f0200100d0b05000300402e62040c19203640c1040c0c0f4042048204032a50782c10a41800c11620082c0781e01100020704003d01d1702020752062440c81c00704d44080e11440b040c5c1010004000030f1f5040301c41d408501d19401d101d00384560b41c0340800454031601810000074003269400001c0d45286020f0f07800807e00a180724100010b13104c484010400c030342c00c80d100d00d10a451300d1038041c014050040740c07465144004100c07a203280d40310141601c0100e10404c000c01c07440018030704009460004540c0c51f40030500c18040320021403600b070200190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 114239883 1250 114238633 114238643
    0x714030307031d0d140f010c0f1d040f020315040606050d050604090203010501240206160507171803010609060501050313240c0305091b100315090903020601060c120c 73
    0x24075809500490042d103010001a178148036100e204041d00c040070b100c0c18000c003000c00001d02418290304800f404030b0354610300400401c007042801c0b070b8000321420380e22100c0d0440200280054080f48a1100103900151043e406820880304d0148140c90301b0300c01c4000302d410f02e4580c0c9081242e050441300040400070030103904152104020001030703a0a10035075010b0038004040c0354446030b00810313140b04190604040815503110030103000d000c46484401041d0000f041c50059907410a625000d0842400013055410600f0b0208601d003698100907120343c09400190020000da50761408a003003650a1481038074081038040001c03d64109800b00e03a4411940070708108450341c0c1c2c80e154a6a03100e0480070301503402c01d940342c1c0b03882201c551502466420200344402004185140e41ba014003609500843c2e511414403501c41110301d078026040b040c45501d0940946502e10341e201c82040c0a008490703c1140103002e504004a0054007803260710681c140c0002d1040c3e001d8030f0008050f100952031100c00c2d12 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 114241133 1250 114239883 114239927
    0x3020102280f08030414031e030c07050106061e0302120703050405030c07060e1c020a17071a04030501060f030c0b0901050f03071805010f0221040503030c010608071403030703 77
    0x702252184054920a9201d08416603032840e0038245001002c0c10b00503007000ca03030010825400105220707001c0310180b0380002e96003543ca031030340a000c180b03901c04c01000500550a14500048194201c0c020b2803c4884640c80502c00400c4003204404900c41c0055240c0030005c41c8011400300c0d0f00c0390f44003a40c01803080c0201ca18000c80301c1c0b031039490500990321050001d00c0006211031141842c204441c2aa1421842700107000c00a13400a07100f0b00e888d00800d0074411114442c0d442d10007080200304024100070701800d0328001c00107030060640e8418041a2002c0d0300b080c000003881c0700380001d68001c403a0804a0140d206003800d00c0f100e040d501c00603072a410840700740702d040f440d500c05800650068403180c03200c0d0000740409500d0424207401e40e0001e03044c000a94512440301e43c01040c1039440041004210f00c104c002180b03208414041e981000e41c0600c004202041d104105602c401c05407a1500c0445418595840080021260070900b05806800a000c0b20380000d02492424000c042c00001000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 114242383 1250 114241133 114241213
    0x90109050615060f04080d0306090c0c030f03020d140103170301050a0311030309060a032405030a0605090a0b010e0901140613020c2e14070f0c050f0102070309050306060a03020102 79
    0xa180340e085070b001b40449030003030050b104c0500d8051194200805d0042c50510043c544003101416100300c41a0242c02c0c4001c0c080e0540b8001e2080e4101e42c944000181f00300400341c040c02e60705241c0d1a00340002c407a21445c480c4103214640002d41a00d0403104020048526507007540d9500c000f90039240084c1e5090710080c0140800d641e030300300181c800b003105a80c00040c604046a1510b00d0842c005100401d880303200314041c009520003192280c440b6030002c00105158036202403003464088850005003580701c00400100f107485003400ba00b4000c000100083c0295541e49400c0800c503502680e1255000c2d1401101040c503854540241070340014a4090721803110301815520800c0401c1292616013181078001510700b840b03184a0b1107141d03441800c3d040f0a61034525400307071042011080d100140401c540d124810004200045a60070350240d00a544a80f10352802034042203490240c0c3d8441d000e00400600d0301c0c288020b00c003003100d405900903d40c0301606604080c2e007001c01d080038500406048100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 114243633 1250 114242383 114242407
    0xa11100c120819060b0a05090a08030403030e03070f050f0904140a08090315011206090f080703020703031106070206010b0a0302040b040305030c0118150507050702030f01060302010809010905061506 87
    0x814901c51034a64001e02c0c54803190308100408040000300c42246000c0e41030065101003820f8506a44032410202ea0702c511050001d04121240d1340800c2061100003004406c0551103048210f4155040d0111014030783c036915055410030490198541004640895004910306080469001406404410304182185550904064050a00b902d158500245508450508000340340b441e40d1103041c0081c040d41091865035101c00002c0c4054080c0381c50308044818030008204500b5040d60189655690f01907a00d000f035181d443e240b0007540490584100f00040320710224144d0300c03400c4543d02512182e801c01100000d680c11545d484400c0503800e000c040343c984d040300d00420155000f13500031522074a103000c4942c25503018058060800d03005541c0d99000079590740074100b0765050860007190555941a044603140950400030750b16120320742c2415402c00c010f41c41501524002ea80340f50701944c071480c0d41c50985984904c004c1c2036620000000701100c000300080000c40074014646460012800d00d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 114244883 1250 114243633 114243653
    0x1b0f061c09140a0b010f061112180306040308090105010b12180f0f06010e1029090a090b100302030c091509060a0519031a061b1006170a11100c 63
    0x4101c69010005006104544031b14010400804951411454001141c1030300c0d61101c0000584245a89000c00c0381030034140700348100c60303051502604982580c07806041c0248809400e603421001546414001300c1d1604c40c00c41261808001c0e0310504803142c0304c00e05004034003240303014040420701076140c0c04801010180700d01501400741c28010f00c0e0550400d428181d03040740c00392503c0901d0362141d01c200a05180c500110544071382e11814940e0b0f481d00809140401e2103103c10340b1fa4454006440070850501f26072200c503181405549940100300c91420a034100d110607141c28a80010a106210540c03500038040903800d904204002d080c019101d01140143c0c01c084454030100d100070580520110b6001000c00d107822152900784000134017460a0260340051045207806032100040d03581d903007002025528a80f001000440d50302c1c80b17009103998020300d0540603144c0c001f1040c11039401603460014075070b1002500261422008141c0c6000c10a6038140201c04d0003e10003900e4502e00800c41c5066 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 114246133 1250 114244883 114244903
    0x7030506190506031914010209030105070f030c0f1209020d02030604030504030b0f0c0307030b031905070609050406050a0e072007150507031202090406081b0f061c0914 74
    0x55918688244a0080707095038001000e55000c4d92011050220b0152080350080c0d0300d64200c950000000b01c5005181c2c06441a1003010380c0542c08e03d07050201c0640d115032190303014030041c8d800304032000811808a5408083d03170b8002c0c0005071091a07050003c0b00c580d110008451004200500041440e40840c1c02c01c44102c40c10780124074013040c00c1051226034400158000070102d9001494500121807406a000103480e0100305950f4000080c1284c03820814a080c030400c101c1c120002084628055a1303c000381d00580d000501c00150004142c01c0034003c5800b56940100820910f500300780103442003000040001c03041084038261040ca480789041c40800003120040609800d6060001c581104142c80d01e030001000300400c080000f0135405110b8150703a50300d80b8405a9100400f0002401800340b0790401c084902580380c41c0b416031128414800303401c5e00c2c1600e6442040c5998400c1016501500021140e141c2d407009101c0f9031040e1661103102914400c00b100d65610341804207031445e1443c446 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 114247383 1250 114246133 114246151
    0x706050414070501020703051209040605030313140d020a0306050402041404110103110307201606021b1503010b091306060201020d0b03060615030a0603080a050a0905010813110307030506 82
    0x407907611001c04144020800b03441c0030300003002120700d135540301d03603940b19898519040c6150100d40305015a4440d080040101002400c4988400b41c203100c420510529100e080c000b403070855140d04650504200c64204242c004000c00b0b130a47c61354403444054000208121b038010343d41c01c08100c0402c41c0e900e80742e0081e4090041c15183c00b01c0d6200242c1224503402e45a55505c909004005c1110750110860142021180320307048204c50616040746000c2025401c61502d03210401d010405ca54002002108081ca803040640746800e0f030418000001c07450200c03800c1080d0200b0040c003101030b051004207500f02e4082d126018036106072404004454594000500507500091210102402030040194a090460142c5800d00340303800040c100120380c07496001060000710000746880d1442d4440c80c01103400a08040d5210150500106207900901c4400042280b1030030100b800d502c505031840c0b01d42d80f080c0700c3c5074140243c2e0b04c40142000d070402405601d8440e0610102c001101070041d503008a01d58 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 114248633 1250 114247383 114247403
    0x90309030a03050705010b0328030e04050c0a030b0d0302120c12160b0a051012080c030d060f0602010221041407091a030c03030301050d0c0906032f0a090c0507060504 73
    0x285040b9080d910341e4085d10780302e80c0c402740115964072003c0310b0030308805210302c078500c02903460b5140c240d42007034404142950242c500003c100c2d480800b075008003c0303104142d804014a16009081090710540d0400180042c4c0c80b0003c00311141680000900c4a0b03000394007120901c04c0301d032400034416807080ca0350b030400000d40c2c44071008110642c11200d80182c450340041c4045e15000064007480401d034400c00500340c000b034010f6024460a6401c4032a10072103d030640380d0310344007500c071031014003d03074400c4150f2540400c6000a10f10310610a07100f0590032154a03840d1030001810b9000d44aa01078020b440c0e01d03066681c0030720f5080c0d042042e5001032403801c0000c2001d0108075034481d20f2007980410b25004c1d070020985011f19580110480c0e054400c21200000416624107048915405640089900340d25000010041c0711780704108045014161025407030a52011000384890443c840740c860f0003441c051828400024030f50040314014545140035400e005081d12070030151041a14192010f2210b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 114249883 1250 114248633 114248647
    0x51806100905070203030402010c15020d02220b192303070f02012304022704030504031205070b1504020c03160c06020f030f0c0304180524130203090309030a0305 71
    0x10034042e85074000c03d640003a5044d81b41540000c0e009840d1144000c20645d224440e05180c462541d0642e00b07a40d201c013004545a0000300000030b50904000c1c1384140c207850304500083c64160a20468881c0b5440342a0700c6c15035900b9003415221010266940e03a061b1242e00388550100c040d8001940c81403000d83e80b5000301d80c8c41844080c1c01c5501c9e64805000d5029108032000000310300341071103504160b058400080088000842c4400130040300000c084041054080c04103142c0d112024105603809910b600300310f01a40c010a844510480b81c0061100c05268005110030401d000050308280010b0005480d000c18860380f1402e60348814085210320060000540501000000000113400c0da03000900300412054140c40e81ca00622043d075080c40c3e0000f4182a080005005a82c010a00b10840c1c80012280091500260100700d4406c030349a9950345d580700c45a1040700c45141454005400011800707000c1c44880080c0d44010443c107114402040058010b84003045140320b418004c3d60b9941e1104e803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 114251133 1250 114249883 114249899
    0xc04050403051206060a21021603081504060f030201050304030311041d0f010b1b0a080a051213110f0103060f06020c0102150903040506160b1014030105160305180610 73
    0x50084c2c4140d0064034180100750405401c0282c030460343c06000040500410070f001c0b0500a44601e40e207103045801c500c0c06407400c0540104103180144203910380341c40b8a0701c0901c1400f0880e0403d210302120140701d00410005540a1402582c0160003842c001c201140124410590395105034013000c070b1800300c884401c4c5a400e1303d4000e542c00ca1152000c41c41c1d035515080100035603010701011f01080c04494080200035540401ca40d4101d60b41c8012070907192008840c010b0700da90030031400c00440070415070006420750452020825107940c00402040c801c4050400d100c4910f620030300c1c1d2414140d40c0d040c00300b2220501c44c00c00008040035801018068185400203085c484039000303114484415400740011000040251816280f06440d948e4450000e55000f6016505988010301100840000e0103004080561940181d40b121052020b400030b001007403508035141101c0c43c000350702840700e49041c814401d030482500b1041d02003250450364440c1280c207003403041c10b840076100700d010210304000c656 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 114252383 1250 114251133 114251167
    0x11509181a0603070b0306031b01090e0f0f0610090303140f030c0406021614010507020607060203180c030313090f06030c0b122202040c020712061409060420030c0405040305 76
    0x1001820305c0506608004000c40d0383d0701c280035550004502045240c40c1164440c2c50100018070b10381104881d5400c0207044003030050000d54840c0b40185291000a00c50304001c105102080302075580e50f0b0400349980c4084450b91904001060550310810101000640c01c0d0051070242c554440f00c95507844c5441000303440c2c2020225a0502d04031000300404c400321340b095078600344010a01300203940d640d0a10008010f841810b00c000d100b2440030003401b41407401e0200140d494854a412614903604820405035640100d070a90307413425005800620120700103400010011054200124645131240e6410400000c10b40000da1040c002040b501c100035a00015250050021890704403104112200c00240551140000c0e004648070541c0400661082051030700030202914543d01c80e13011841d00e0800780c01c0320a94803142410708004136000c0f400c08140a0b0090368044011500e203401780b40450b045141909400350b250142d140700600c103445500406104a01c2542d8031a520011001110301ca1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 114253633 1250 114252383 114252389
    0x801151d01080304060804030e1c020a0906080309040905010902180703060506030708010b130e0106020708120901051e070f0b01150e090606130803041502070602011509181a060307 79
    0x500c0c210380108a02400441200e055400f18904000744e82d40e40d003415140604112040d1b0380010a441030440720003003240580c55458401c8030081000d681e110200070540d1464001c00805410800420140d80340a52020058921540000c9040d0710320340c000480040c0d6031340d074010190a01d0002c10a8495062252102810341240c1e00c0c0c1c2541032018000301101014003d400e62508005220346154000010540041000180c102815a1240030081d101d0700e152158262920071080a040ca40c0c1100040d200e0600f0180c1d034840c1006522580b001c0e16000b107903a03074004440100801e0300441c007202954130079280034030b044520551400c401600400f030303032050301400c00c03160500081450340d4080c01d06400004c1140c2154540350b11443c0b10100344540e07400305200344000100040d1200340c02040003190b40f00c40c5c09446000390b680d10141d007692501d030310014489411032414400100160301078080504808204203160a15950b51495050001132280c11401003104026451601b0882e00b009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 114254883 1250 114253633 114253679
    0x5030405101b030305040602120405030c010b060414010e061c020a0905030a050c13060504020304050f012a050318010518060a0b210a12030e06070509090a050a0204080115 75
    0x1440c910014450b0442c100c000070100743d01c0c1c201090a104558041d00e60280c2c5105290030740381041e00d043d517039a60044049003100e508000000540345091002c0d6000c80345054105da00c01d4400d0401101c159903800740c819407002c07091003034071880600b800c80c080c2c0e505001d21006070b880c07640100c090700c1e1400c16070107240b19610948070362000400120303034134007000e400f40d8001075800c2e00d900c0c08801a02c0290030180d001032011003040180100000c0f801801251800204109a0150050106101c0c0310756001d8030300c240076041d410107a01c03a0b4000c5500856002503910b45a000c0d0114600390340c3d050307580c10301c20480c140c044220911b041c0903c6411402c03941e420001c082002d000300b1141001c1d42c0d90300c1c43e0300e98021020411520305201a5603950f43c4422030701244085044090000c0a500f03403015224032a041c006601980074008580540000070603400140c0d440c0610040540001401d03107880c02c0c0c0a21000809503024000c1c01c250390800720208480c541804206074214100c6103101c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 114256133 1250 114254883 114254897
    0x102060c0307170403031b020109020a12030c150209150307031a0a260706050d060b09090a0e0f0f0d12060614031f0314010b0103110405010f0c0b040503040510 70
    0x642da030003102c200c14126240046104554503070a0a900604400207803a2904030200403000c0d90b02d03819030021140724800c545842e4600c4d10707503000d08842c000c11000100480c0b102200800490014600944c0c10100b0070009450105e8000c0419440c4804c2104150340f45408405d11512541600841c05c1e42c0b0200783d00481042c82040008031030703402030302c9016800e408014208604400071800d0300520942c030012100f40c550346040092031940403111f101e411a01e403182c003103201d808100466104210050400406840301d0385800000c0c0711291820b00603209101c4003a141c600280410b225100e00600908403024000700003808000c0390424070302489140c94011300013150456480319250600c2415640c403a50740150541042c035100396010b00c404c2c0034410010130009895103558aa0400100134000515846c0c019019580e0030303100fa45880038180400d21036544a004070521814151034442100d0000342c80d032904440b401e0380c05590642000400380060304110520500340442450444 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 114257383 1250 114256133 114256141
    0xb040c0f0206060d141204051c081b03070501063b0f040510020f0405040b01020a0b040222021b0115080d030b010915080103020a0518010302040903031d010b0102060c03 74
    0x29180c0704010075191051302496202c034203001c1d02d010340c510b2504680017140c04401211840141ca5001407241511a4000700120b18202e00d80c50003403003d05601c140c2c0c140c204800402c001c000100d1404c030646040c0700922220020542c240680801800d031181c800e50501d00c0000c0c00340d90100840c002152340746030582d02c0301125120f5001c05602c0340d07040000c3c240d42d4a9034603100c0c0c14460040c0034119403500100d032050085004100800403210211030070010354140e807006984441c0c1010004e44030650703110016001d4200140481c680c00342c1d10f00c5540e04400d103e007a60049800400c060305c80c0c0d00780109020400a002d1154194000103941a040a241303400000d5070b03520100c0c0c0d85142016103920180555034001d0798950080c1038400000b00e555200e00c3c20007843c00000b440142c3c89001d07030002c00602d1382007a500c40d961580c000041a40241c0c00c41d02400083c0606038803c40030555220322070041051440303c8038250500007000400c1c01c05031703032000914100010305603030950f4100308180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 114258633 1250 114257383 114257387
    0x8060906180103080a05070c060206060315010b030a0b03160303030905100603050a03180b0301030303020c060109050705091e18040b0609060d030804030e040204090c090b0703050304030c0c08100b040c0f 89
    0x1c1d045035801000c00755691740081d421034860040890050800c0ea048201103019170300800c0300b83c030500c01a0115207040b84e407010302c100c0c180c0c820f100c0c414a40700304001040c1c9141c0b40743c1044561003409000c0341e2407250000c03985201c030066a402a000650344040c1502008010710200002065412040c44564250340b58540c403a501d8000080500c48001d038008010304154204500030181c030300200c0d880b50394900b8013a000e0352042c150010503015007400803e24030501d1003000e020300060780c4c829090403844803d100c1d91228010034001840c00b201140d40040e910402c2483c0c65100c011015101c604061401d0b080c446000750440e44150b81c07240030840d4a855841c3c0c0b04424a405140269150700c45040545102c00d61860217a007107030000070085440c0034079402c00f5141c44440e58400700d41d141e44801603030f00c901030030320000c0000340c041000c200481d114601800b610fa006402444440d640d50703480300e2800c4040c407400340c8019150b007646030081c42c151141c09034200d040e0604e00e1600c9515100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 114259883 1250 114258633 114258679
    0x4050f01080406090b04080910030c021c050405090a0b01081b0711040209180106090b0906040308030c04090c0207050901050d02090109180b0f0114100e0d1103030a08060906 76
    0x850401c4044000201441503e0304410325498011803503d20608280c00c00070415072110305110301901007102e0b440c880d1446489160700680465000e84443d8801b0b0702ca502c460107021000d802013040a12000c2105c4d554200c40340c0c043c400e403860004110040c4000505140d80061920310214404142500080325000031101900c0d4000d403580d80607442c21002800901070800c83c0c50b00301039540f0382c00c460000c03011030003030582c2e103540c955a0700540c0e0307001c0e14500751203012080c0d90000800c0c00200001100c0c1e00c00303540c01004c1d14240c00e0070261038417010320031900c50050400040e03201342d50030881420845000d601528054035025800306064011500300741c018400d90313400076540e0b170341400c40e040e00300c1002c1d400d50b60000303030305402c2e040c4448080040c20007805961210b1140c81007003a01840c001e0b015160600d826160b1a04400c0240204043c4000714601610340b0482c804a04405079020f00080900d00501e40320b4110600f03102041c04011345008000030b000750b400301240300d00c103401c0e101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 114261133 1250 114259883 114259909
    0x7090b040b04141503130b0108010608151008030c01051006030204080c1e0414060a0605071a1009020d020a090902040810091109010e04030807020a031d1206090703030908030405 78
    0x1c040c070b0380c03c089008200c14101001c00c54148890100500c51030300b070944560000c1a008100407955a41c035000018220703891032040d1a241c3c1d01c180400160a021234803041d51085040c0c4200c1c00290f941c0a005042d540021075441503a5034800c104160740645400c80b070094601403900f14107203400c1880003680ca0030b01591081c0b1070168440c018a45081000700d81d15002005401840302d0352884c0c00e00382c442601903c41c1c0c0c0c8640e55184002c03454600c241d060301e01c0107402804180883c2602204020f020101615503501d140c801d80012074901068002881d85041d04000160b076924000c000401e01d02e1710360030460480b801000200100000020360380e280c01066200020107007001e15001c1c4200c2c40100e05207400040b0075000013224002040401d01c95806901d51101c5a921070360226200c1082d0071004001c2000c4a8a80d854688105120510120007400c030b10040c000907420320f85040402c80340c0b59060b1f0b001d8103081c410594015060f40c000e1003804001c40c00c0c03074140000500d00500c410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 114262383 1250 114261133 114261149
    0xa0909050105010e061c0606020c0103060902030f06060304031b0b011508040804270912021009080a080c070f0507060e0d120305060a0b070602030a1103070e060c0a02030f0607090b040b04 82
    0x10481501e01c040c40303448031884044006c020017200782d0320070000e51070300541e02d50f150220b480d091000424030307101c0c001c8a00c10380055140021590300c500401c00c1d540c002034800d504209020441c40d641d01c411480f992139440c040e09a00207079600d0180c82541c0b44d02105100000c02c054502070000281d0740b0000e035000e42d01da20300403034180005c41e124800280c00c0c0c0e10011031124200364005051141c484699800c5a8581c0c2c2541c80ca090310075030741800e55050100080c2a40c10400c030381e903003c41c4901d88054000e40b000d440c2524014445c2c4401c403038600d0b0700f101036449401500080122541155107030f2030481003a01d14000c0c2c0d01494480042c03002980341d8003824152030380c0c00220241e0f0369440010240c42c56a22403034841d0114209070001b504101c0300b4401c4a8a0150740303103801c55081d01502d210f107040b9074a030422a041034040c0316254020f141040e00074451259600010303503007400030300d000702403800041c420703481c3c41c6000030080501584003000b81e800410052004050250458090302d82c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 114263633 1250 114262383 114262387
    0x2010b0117130b190606020325020103141005010e151209030f040609080105070516030c060f14060405180a0308070207170609010e0304081506030a0c08030a0909050105010e06 77
    0x14800081d65a10440001c02d083d8019040108a161043c002609100880070420143e52188030681e900c2c4580140c4403007018000040e41501d6003c65150b0303100303500c10700d030109290702d50f01080907880704292004030031501140803d0142c2d5901c00c9400003403800840c1e03415502d14200484004900c05c4002c4c0150740c4402c040001c100e06410000ca0741200a5881003550b6a5039070640101003200900640c0165400c00300801e1100f0b201c0c0081c0d07030705981910780c500d054500079507040c0c8450992540899020f40c03587c41d400340f400858848d1180c00001c200d007445891034588208003c0b903400800100300c841d03086088400455000036400350150349802c205a00e40c0b541c0200780c3c41c02000740d2020003c1540d215003d54411f102186950190084000074410901007802654480c00f4500403d02503603c0701401080c44215030341d05a8001201500f9140b21185a4a941d45030303060f2070f0041056544000b525000c0306602840345030041c020140b04205650415000030028010b08500e50b22400f40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 114264883 1250 114263633 114263641
    0xf290a0c0f05030702060c0d17010e070806010c02030712020117010e011a0f0d090318141512010803070b010e07080402040b061204050607030c08090706180801150e010602010b0117 79
    0x4000f00c13101c140c0c0003884252504e07410512a66620040300e82c100001d10f410744840d0516160020a2741078600741144101c06550b409801c440300d60b4024016810800034113180005601d040c03200350013070410000c20080e284e0440c0000740404090800d04c0f40c4c4140d560300104408958190307a281552100091802c0440d6003152401c0305000d0040980503032a40001c8a032200c100f80da00a61070640300341c42e081508030b03a000001c401c001d202d1194591f5444521030748806440d0442d85000c0c44811660b040f41442000b280350003003207109070444407403035100082c048117100301031491714010105081c0f140c0045c60000001440110041d00007406a500e0700110800f40d51440d0590751880000151080c0e5464681400340d034540d030607104500441e2030700c1d460380405480303060070ba480796102000411005142c0301d0102c03041031501104280100e480c2c6c02c04100342c9002e02420b100c1e1000000c0a8507801e0401902c8041c2c0340301a8032410942e89030445a20090741c015907019070502c1c041c1010041d42c0d403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 114266133 1250 114264883 114264893
    0x8150601180902042409031212060e220309060f050c1f0b0a12020603040f0b01090204090c09140f0310020a0215060406061202030703060f290a0c0f 65
    0x80a090501d07800d114410300896165020390284c400c68070898803140741060707186100c903a07504008a58800059010340144082228607180440308640b80c9000710600c0140c00540c41118080d4210b1140301000e10305210301d45800c008610600e22218001c032000e01910742d0040c0c104040d41c400d500a000b01a910f000034240070318152403012800c0001c0d00d0342114180c0701603000200103034146c564640342c422624043c1c2004481c10050700c5142c035482c05052016000c205864100400c11603500c82504144000581186003442c001c00c250000980c55908040104003034604030348006041129a0004018a80c16855030300d40721017096032403d0060441c2c401207420038482c03c40107051640001240400c00d940040c13102c4c904010000c0f03417031041e04e8000070002590218411200041e03414410580c03004880c0d80156085801824005801c1d665101400746c610701d10b60000c00c0c1000c4036508500c010050340c000c000c0c20a500e840292608956602c082d064405d800000381c0003115141e00b030700400c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 114267383 1250 114266133 114266147
    0x60405040c03140109020c0c0d0f02060c0a050c01020105101502010f05090d08090303010f030803091504030806091503060a0207060906110301080f070503030a0c1118070e060408150601 81
    0x240c03090111140c003490103000b801d48103203080200300d40c42000040c103485510a555032171300241c026001d5200072404010300d241c0103500a03900540e52030304c0707039005075220401032031219900d501400c05031016041c00c505110703440540e00c0c15641403108002c0060000b0302404190352a96001503102500034408a0051105090040328140342c0014032180d0308002440661581d0980d0f100700581c2d5038802c1441e20b0340001e200340c040d981010f10b070038800180e90101856004020004070307020010800891319408800381c80c1940420040420300803d824580d10f03240c0c1c00b4281c94803104480f00640003195841000038a9480400ea001c103154003000300a40101c1c000c42d0708154140001030040380100202e520a1080407030a20400580c2099000c0100d18041210b0004002d50300301020140280e038203414030141143c1407006030450485640d02c80300306c1445850101c20145092801c0c1e007001d84070090034940d0b1485840c041c03108212044001500700c9150400700c110003076580315800107807074070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 114268633 1250 114267383 114267389
    0x206011a07050610180b0a060e060f0d1d01090308010635090c0132120a0519090203060c070c05030318090601092103051b011b1803030e0604 62
    0x60060f0740520050b1501400c261043c0c8424600200325550200501800c5608195495402100c18a000c1140d280203082850140c00003601d136502e0305808114400003607215016220185076540350050342a01c1000c01032420402c1000200300d042c48986014040010500c02d040c208140072900809403c40c400c4041c00d14481c40d241c1541c40001d60601c680b0b60502200c80750000d00ca850f00c2181d40d50311030008104584c0001d4039031402c40101c1c040243c01200b040380d040707407108001c00444003d0084056403a100d0052114002918107000090b10302031425003502d20703a800d007003581640240e9000305402e904100310000c41c65440a540c900200704508a0740300c0c40c0c0c14007002c01d08000c0082007582d600600c030320486200d100383d9503100042d15400890700540c000c0d5030100c41a40700304110941e1040005000c0d0500508252556243e9a40f080040047c0981079464103901c440102507480c000e1529101420507641800e00500303480c19440507444081c0400940c0c0d00010f8280e2030b440304507006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 114269883 1250 114268633 114268643
    0x10b0402070302010605120d20011103040f060608120f07022e02010e0102040f061b0203120c0c0a051012090b0f180d0207053f07150206011a07 63
    0x1100181d050190082117288030b0940034407000d103c000301818010403500d1520715281c80c5c40071507500c511604082d2401342c035402c01056581c1c01a24900d0451500030f50b11891080c5409400d00c0b041d45080010b664480e84550780e140d0080700484080c11402c4192113400400c01980741e00c1d0070280c00050086540783c2d01100e0400c05100d40c0c0302c21400317510100d044107100c41d0000d10142c481141c090f400c030302c107a00c504245200003c1050002600c1a029400b03400c412114081d500c5841d600064240f140100b645a01e900c00000c00940b428400c0c00740c100ca58000721007900c504c902e0040801c00e06d80d50010010100120041075143ca4147d035070010300d0032034000e4014990f52808072100313080e282007510140700901c2c0382e00b6040803404002600800300f995035800307040400e18041c280150801100012840704400c1c0200c0c0200c5451003051151186428440f4a42c20f111054041c0c281126504480350b4080c103640601c1c10707240c0028007503045a402002161085201c100120080d004064000380 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 114271133 1250 114269883 114269887
    0x60a09060b040e010b100c05070614070501140106030605010201050103021003051b0304030804022b1704210b0115050f031312030c020c01170f0c04050d0303090507090b21010b0402 79
    0x303d8000158800c4010010076900900130140384001036a1521012900a0107940202d00900c403552050340801c3c1c101c1040d4440360f08000b0301ea0f03211401c0d18030507690b21030907200c008010440705600d4050071004200a000800640d411900821100c03091801140300f0b240d01c5802140c01d60324030000752080381c05490b580d0344d202d00701894002d0030031109440c00e0303109421520086117002003070368246c20b04201130010501c0d440c07400d64030440d1401214441c002820020300c0002208001d610b400045015a081501d403240d50502d05848c0081d4181c00c822908400c0300c00d030b009555006012178860740302140714135469a4a540c00404507402c2d1000080c0951500514411000c0d05a0000580302041d5025108804401801100c0007141c2c0b0400320401c402040c00f05100000003001c5940018444622500d040c0e115400b040001d15840b10440000b95208410000c0c4130b03003030110703402900a824090100d0490380000881409091200d4090140b0041c2c0c045d100070300950010590b080043c0c8259 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 114272383 1250 114271133 114271151
    0x30307030207030801150806040b01021903050306030d0e0d110a0902070809041103130b0406090206030903180f1503070c02090901021e0304020109061803020d08030106120b03060a09060b04 83
    0x6010b900b107660b084000c18603081c00450a03c9600030b01c88604c6000e075440b4201c80d5102070800001e04031503444c1a040d07004800524400d1070108203220b484a01a0310b50035035904000080c10300e0b00800a002d5810080001c51420283d90307840d25543d110741d006910007040c0c2403c4c80002e800807605a212842c89840010788001304a501d00207813061007c08c560410410f0403040001303509200c11a40c004c00c26020b6601301c80011003d00300769400c94003030303800000d207028640d0211f1090361054820750081d900100b402e489000c810125030703c072840c060310fa020044ca03101c40803440c8040300820308804503a0100020300600c0c41440c01c240c6668006100b82c40908141007200d000354044841040c4008000b508024151064001c6a019980c10307598444c103036182a408845900c0a219003180e81c2640800002c0980d44595a0a0310715010751403040d0340303503d400f5000d801407c0c11080350348000d0520002c82529034011880d941c0c0400c000d10081405039071031606600805141c0480c82e40546041030b11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 114273633 1250 114272383 114272387
    0x80c012307030b010207081213090603051c09050901030b07030b10030204060219020607060c020a14060a0c0206070c0b060a080708030904150e060d150f0905060703090309090c02030c030307 83
    0x40d40920800d4600b0060101c446004907103030f0030703d8010041030b40c3c090580030034034048180041c000900782800b1500700c207846418074401d56400780d109813010b611510030302410107640508011105020300303145814515010101c1c99102d01440083d05170f1403110001172081d4001c0e04440d0001400400d0304007038482e840c4015000b50014007030700c0c00500c19504005c500158081d03015100c15002010603081c0315646d95400060b01a8001110031409850000000203400040032a420194031001d0051890b2003400034044400e810500c104550010050040d0f854118150f03040352078001100b2a030079a6901c000c03544070b03080d60703000c40050f1055400002d1010004009894180c400325828480001d0b400780d0000c81112a0081e9a112052400030841e01d15061000060b100d101d014030805507031100300ea032400c403100500c019002d140c42e44410401c01109102a55012982c0d040c01c00c071100103620010071100942c000e04646664411180712400d008009a5401d50700d40340849549161440b00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 114274883 1250 114273633 114273701
    0x6021009030509030f160f06051e040b0409060302040b06030f13020102160b04080105090f100507090e0c030f07020316030804020d08040303050414060910030c0c021207050102060a0903080103080c01 87
    0xd031086c8000b02d40c0c011980c4e5107a1041c14003110415071390b15007001c8982284c54403402240405400c0c82800b08000994444000d005c2c00003031481c868000780d03140c80d50050005440c00c03008000d03c220301c204100a01d8140c4400910b0700000486480541c0d80000c6c40142d01c1c003040c642000c0b03c40f003c1c84000040004003071f00180300362a46100280a0f035221010f2850340c03010501d280460340d8000e00050200c420032a88001c0e4840031611300903807611b60302c00105402c0c01d001d40325040d5201c400401c010f468000303200c226801607071904c015440c050541d18129484040088024104401103020900b5582d4050030340c00c002d42c0110045a585541e03190280c0703964030900c10703c078160099040440710fa140a400341c0308040c1014203034421010b4100d90440c010007070701d501c00341071110b09031011000d80c6400c010b81b0000703110400240602820440003a20b40880240361040743d0f42004581b800003039000240a046a0340400c209450300c100042103405840865501c01004032401d103034041000810b00b03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 114276133 1250 114274883 114274903
    0x4030516030201140715020328090201090608100f0f0329061306030206030a0603171903050702010f0e060a1401030210050c0f0a06051803070302070b09040f0f09021203030106021009030509030f 85
    0x42760600002c0c1c40c054030300c151200d0407000b03400300b038001804201150098882d02c0c1e01c1034005440c0440d0701d80700c404841212425030014841d0340e01c119028010806086022004111980c901d1248200407d80310103012100404d000d02509000c0700008412906030403107005107500034482d0b91030380f52099901000300058072040c0d40c40443c12507180807202c0c0303001c21540e0004646403801e140d0351046809901074480a02648215035941d000c290b401e2030944030b421035100c100b101400a81c10071800c89000d035002d01d41000c070103521003001040103a81d455620003d84446003001078031240a81c1c107503030406124000343c10700c070b016035011041082003503400350b0b1240030740d012004100300f803d02d121540c0e8000d0f134034018003581c0034200910410000c41c0c003609143d4802007020540701c40070300320841520614001c01c80400d440e500600f0440c40d10910407041200301d40015400e542c54000c0007507503080d08070704c9071118a68410394101030502c030b0380450f07140b0003010742101c1b000601c0440381c9549041c245 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 114277383 1250 114276133 114276181
    0x6050603040609170a050a0302070212030706140a0e07090f061d010306111614120a020601080111070209070507030905100c0308070f090b13090c0203040305160302011407150203 78
    0x9043c88444c0800e40f0b0035140103c110359181414804400300c00d07802940450f6090340e11086150325030540b01e10400041512510230823001c21307092064507114256442c00340a8103886802c02314000d07190318000608104451030741c980841c071038961a200200404ca16040101000700f0504040405c414518005c0e040741d100e00c80c00c0150015540d0542454010090300c9070900400c0e0300d010003c03428165045408180310070a9801d07141c49034090305a681d01c610641d40258104500420040f5030a11234402002c1141b80e80c2464040103038002010f00000500610034410302260b10300925200c1c0071404080c05019000c031324000c8410502410b0002d0041007100000c011030001a000703480ba00300b0726211440c9880f040c806500b45a1500c01a4010b011a041103a108007000503c3d500c00f80100704100026030065907607242541001801e11004504032071041101c4042000140da01941b41d5800135a42881c150300c41d50380d4035010041d00d4407056070907032084c0044140000d2010b40300351460054680 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 114278633 1250 114277383 114277403
    0x304060e01020606131508011b021603030503040b0912040b030105040b0a080c06090102120a0306080609011b080702030d05040302010606180503060402120f060103080717161506050603040609 84
    0x16800480c2d4801084507070b01c1e00040031300307818170119495030001c00d840c60600e40040e03061500d42d0030507801c49910503c80b0340342c07040c5800109440c0350144a0702a0215100c4038030000710303003941c5024000d840094070007000380c50b030304e030002e80d1805080c00140b041c03880b0242c419a54503541d2191840540007800340c544105d2a003d546003841c074120540400701c070080b2000c0c0c100002800c0070801c1d0b50b00290007603030550091b41c14ac038800d403815000801a0390003645000030100d081c000b8103882d01d41e0082a410042c0e01d80f44500030343c81320907001096041001e04d41000715560703554040b421130040304c003410300d103d09100c1403004154064200c00d003038503096031b242103040c070a2465450251300188125178042d0403110114001d41400c060710055805158120307800a620400c8041c0360103001d03070068031882004905902002003521050001007100314001d400c000d00558100d180d11a4810001d00002c039a510003605003405070003140080400925050f120715290a149000d80800c0c9011140b2401c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 114279883 1250 114278633 114278657
    0x80f100e0109021509030a02150c0c030d0e040506060d0c030507020c040603110910050a08060f0c030405060f1f06030e010f020f04060e03120309010b0108060a0605090415050909030406 81
    0x10502c50250b103290000c003401c800a5074181c00751460751007605c0b0a5014040c0c883c0000140c2c884006601480c1e11160300e017075807000400f18581c02e115428019600ca5000f9100701d08545130b00000b0901c03c883c1c105c034005085d4461b1000107606100360110b071558503003040c3c810841250150300980c441c0c5503a400351100c00905104000854819010041c20001101ea00141905005801d2640446c821455003c100d80311400140c0c0c0c003106620040341580850200328403025000c03451a08980000c0c4160305500341030340d42030344a100c024021001704040d080001c00c22110345050415030098200401705c030326100c6400401522101610b500701c0d42c01d2070f03a5000352200505c00c956960130582c50385414281051800c8030440e1030218000d5243c420062540c40c200c0c400070045005600d880b000081d200015000940140402410b0070b10461210500b0010b5580000c21a10b511008480c0000c0d14055202e9440c0a1580c641102e5000703020102048480d03e0b0003c000c10654403961241411101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 114281133 1250 114279883 114279911
    0x705210c010f090612060f030c08070902030f01030807150f060518150904030e030d050403021908100903020319020303070207090b0112020a0e040f0204051c051203060a080f10 77
    0x1001c510080000b03481043e08000e8940710300b66900d1815074000c0c1c0030824561343d100c3c4070444d1006400c00d890004030000200414401048040e0040400420950540c0b03420080b4a8445030144005441c10400094100401150001c80c203140b03020040304000f0024041d86050043c07605004181c003440c25005c0250381820820315851103414002c0303041e845800610281300511401800031014000e00741e80700003031a07a0a12030310b00031428594900b501c032480e6004010700c00900b907905102e407a0b501e036000e0015050205449901001540000c03c100e0b072245002c07482e42c4240c40007018003110040c062501640e01000030f50041c0e40c564226681d2a03118030307004040f103401c68482800306942c0303c0300d07450386104e50300503100c031301480c2c205442c0030076810b00400e007a2101d00030741554107580054240801d00d0308040702298000c1803506984e1940d4588d1302c0e1561465030300400500f1100102c00030320942d0301c44100502400d40c0c002501e101e01c4a804100b50b8550f955074122090038100798503040c18070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 114282383 1250 114281133 114281147
    0x15040501241d0d15092103020c280b0108030403140727020706050f01150c0203120c031b0d0306120201050901030906020408011a03070506040506030c0a020705210c01 73
    0x146840c0da0342c00400b00c100e81040425510580203e40b00d00440445408006541c80f529108070b0050090006402c02d0311501405072a810015606151040c8282410260000707030035003d01c4810001c90f400d00a000c104008413078030425004200d0405200042038400011026004491041e04615107842400c4142e03912050a4003409020070f8100c82c5074284920700411a00d40110b5170b8000615044298840c18191f66040f43d5680319810700703000401201c5070b031301c00b4a218214a81345c0800840c2c03540e400662510800c2000200404001c80d40c020482c1c42030088482041495280d24109500d0001c5280c69981450504ac04a03151850004014200904c0f030503042c2d5050b582e080c41d18460074019401010151000c1d90059401e01c07010403566024403d84040301d200d4001c09200c289880c0400d2301e05612908030750b010348014001041180c454a042e00e800c0b00d941e103411900c907400d0402c200c2c40c00790b01754082948080c4010401d80060387c07001032084a54000c40c251074018490000640d110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 114283633 1250 114282383 114282407
    0x40909020f0409051b0f1815010323040206040b03010305061009090b07030e010905241501020c010c0305094b10020118050105091e0304030305031504050124 69
    0xa8010305003038216160b0303014401140d00300c0108804044030302c41e00411001a442284183c494030361409025101211880c41c03508d00601b440e05001075205120035041c0d03000c01303220903003800c3c0301c803000320b011541c481c0d007a01c02030003411181e143c980da96410140e54509003a500301e0761322141200b01003407522140c06402d0000b900403410380f00a44858030202c0c0140b11040c0e02d540d140d540d0b003903900c0000303105015511a00415032800345600c0807030b0b08013a01002e8081c3c090454545030100e81d80882c0d03008141d6400032042402c00b0401c803070460400381d500703110781c070940c3c2d0740204c04074890150250030304138220a5100740301498017034141031a00c480c1c003c0b20449040e20500321540356581a49001080c54411102c039100200d81c1e8180c20200000e200c01a00701120241d442d81b0400940300002c02501900840444001041107042c3c44501c3c0c880c4181e00000c1c2c1007010001c006440d081c61005000c00051014000700043c0d07945080c40301980c4984c0d4440201e00340c242d10102c04103442030018a6807 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 114284883 1250 114283633 114283643
    0x90f0812070204090c08010c020c011b03080618010e04110306060a0b0c030403201f050a2d09030b060d03140d0b030613050118120e040b06040909020f0409 68
    0x102055049580030309801a10080381d02c55220b030044400209156001d4004140303840000c901031800000181c00d22050b0581903042100010030103500641aa03071280e40c0c40d8150070044655240c540124409501d04010301358019000b5000041103c0d0745049144560700840c690718000b40f260007019100e46040e10301a90002280000780001003550000303116440582c000c40c0e14140d503035902d141c600c2c20a088404460844240740c0c02d05401c0116140d2410b080a09007400b540340c0400028085002d0046c0c42420040c1c40135541c035080d0510a248804005030444200c0c07403034144000240a0709082c0411207000355644040303602d07801c0210b200314540703526882e90f00214103200800e01c5a5001645204d40303294031030300004da150301c0903c44a4002c64040110442d410a20300b0b00500355940c002544003102401c50169010550044164410010610348101b61310880b40001c1c003c0c7c0200c16074268060400540068094102d034094042e00d88292205201c5040b10010001256040e08000d89 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 114286133 1250 114284883 114284893
    0x10c1104020a1701030b09070f03050616030b100203130503010c020709020a0903060e0a030f020106080316050106030c061806090b07080c01061a0409060506040f030318030b0c120a270503070b07020c01090f08 91
    0x700d031010a030840d54dc02018a800030b6003005600000d80a440180031060242e0400159194404000300c642c601410307081c0c000f0300c014400c001c07000b5564401c51140c0b00d0403944c04115006001d1145203204c0055402080903c250711841c1201c1d52500701c2c080048000c104a408070118032030040c000d01c41101c0810340035508014030516030560554120710700725210b545c0e03140c001c0005048610031801409443d62035688015000380d0300f401600385030300010240418130404004c0c0d129040c7c1156401d0380c0c440b5429403605c1c2d01c4070034180075069a0b000f00000c000a51380309500340e400b400c00b038000c64018041c2030088981c4c54050104611840c09050b1496803451400c0c000b00340207810315600341150701d059011407039403621200805a0103981c2400c241c43c0000d0700100c034100c004802070b0465500641008171003030f03811910150081c0e80700c10408000d407604900d4140641030095841054000b000c100035450103d80c001d465803114412107002c40e0f0780d440c0124034684410700040a41c1c0704400100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 114287383 1250 114286133 114286141
    0xf090209061011030c0c120f0c010e0d022d090f01270507051b010b01200a1b032a060305060402071e060605010c1104020a1701030b09070f030506 64
    0x100070042109166800c0c0030140c6070912020b4010070050055035520406440c1d030f80d5000c410851075087c032240050566000084650f030041010a40a014172402d00b4002c50600012010805003000c0c10f01c007950290b2107100000b100706144009600c000c407400c0007070001110350401c1010006050380c038061404c8203400140006443c00c20f80105000e90900a4407550500d13240c0c503c01d40d1021220b1000045000c034644100054000b543d156144000d4004d00042c91408002045101c11501109a0041901c4040d03c081c10a00500701425004201180c2c1d41c9070080b050307402c16840784000c0340c4441000d03510b190412240c03070f00000d0852107456414403072032500e10f04601070032000d440703d1b074000d80c00c00100d400103151500d281e0245020606611414401c4d0800c2d4045801c644c1c0300e14148410202c1290004841d500d90400b606412500161510100e5004440140307200303011845030860701001000b03000808030441d100c0d5481d8001c40303411507283c03500022210310f9403100030015800300003c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 114288633 1250 114287383 114287389
    0xc0f110a03120b31060608091b0a05031204031406010503030d0f060e011511010b01091a040509040b0103060c0c0c0302040e1f0c11070e060915030703080903010f09020906 75
    0x102c1280340014810307a92444ca6802a440070003020160342c10b00d4203042515004211540200b60040c40c85041c000700c2d40c503041040644030403082e000d0781440c0242981c015956a180c1500c20301030500501110031491041c24010364960140c0410ba070603a00444c0104607031600011818107941000e0099402c1ca200242035070003a081040c00d040440c0d071a5800410031105240d03a06000300100039911520a5100e040035008001c0c1420319010b0340d0420a6010b55030740c100c84007004590800e4076120f03400910019581080c040d5030044d81c1d1040c12003007480180400300400d141030740d006e5501040305550407001610000503a00004015014285c0c0810140c034007a40410010001c00b000e0714100b2200d041407400d214150701595103000d646030700409103a5840100b01340311118001c010b0100604011a0000c4244018070080c401c0403400c00140030b0301c1c103802d00e4040288000d02200da460b5100d1074012003d400203a40c00f8040c2d03282c0140104200c0c1ea034064401500d4004d80304000caa2198424 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 114289883 1250 114288633 114288641
    0x1b07050904020607080325080601110606030304170c10030e190c18020d0c050c011409032a0102070b0a0b040203040b04030f0507140a02090c030106050301050415030203010c0f110a0312 81
    0x24841c0361940b10007200c0901070b940d0340841186a52940aa46442400500071800d02f501420041c3d008400308a076903100001160700751455100c20494025081045d14a0000e50003609d582200f1460b00ca0001150940c00107602c1107020700c240c40c106986c2d211040c82c41c4919040141074031040d130604008003d07006030003002c40d90501c54094a4840c100580e613041c0c84550380d201001804c0001d10580b00042842580c4601d80b54903030b83c00e05401d0446080f0780e2401107403485841d40c038842c440c4111907426241c4c000c0f030317140c06032000307546806e00f50070800341983c800c450b000811030418032102c0c07a510303091088074441ea50180d003041c180d84498808039580c2100d0781c42401402400c100031400710b24041c4c0050b050303001c014000d02d0a8442d6105000b6058406030480181180c240018880c041c4c121064030705540c02270318001682048406051000d03609640040d400d5441c2c4414010444c0d807001701017400d40b1003910b030300b00162a20f10029076a04400c000280000700a14080c2d98449004c1d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 114291133 1250 114289883 114289891
    0x8070c08090418110307030201080a0f1b051e0307050703030905190c03022107090b030307080c0f0616141309060803041509060c020112090501021b070509040206070803 74
    0xa202414626420041811100c480343c0003060840c04040c03420030860030101c03208042e00143c024201803490340d40082e000d42c00141410680c542c85081440640d5086d070f000b01c002c5410014181100a6400230143c402e500c4000401c40c3c1d41c0d03a01c415800c4082d5010120307402070307020f907603000e00e080c855890803070040a800008035002d009802c1000385108554442d10201ea01031841c0c0b510046c55441041380b40284400d5081104c03403142101c166552012034041c088403944040810024080d8000a00f94442c88034003d00c480004a03400c82041400aa45038940011604644aa403151004500111111100240003d070448504004114074030040c0442001d80d5490090b82c40d103e24103081910780c01e17045034013142c1c00441c00b0440c030031501e6600c104940c5079050941405080c81d1000b420101c1007480a814401006a941e90000c8581e024100c06034000000b10740303c0c080c12444910358850064150800d2103070110103c3c1a1520900d410700a66000f4a41d40c50020203a884008a8100034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 114292383 1250 114291133 114291143
    0x30109091103010501090e07080105060a1206060b030c09120a0203060106050d060306020d0b28030f02010e190f0812120408070f080a030621020402031009060b190203030708070c 78
    0x2070310280540c409000d141d0113000f06c024041000d1202100642ca0f1486584c45400580e040205100e8943c82c4c81c0d0b05c400641d89a80005046080242010310207040030360300c64040300c01c00008100c50503001002404c0c0c0a401200c80f001c075507800201e15903442d008584003a50540101004001c018007801c014000b1410300a0041400d56594031038104a0b000080c85011407521107c403d9000e14260b6a000903840410a40d520003030340044441c0c0072952640030040206c19440152419603000b04180c10644400518900356803955840802a0b855188030340b5003e9880c0407400301c0c60311400301e10180040c074680082e034100400d101c803900d40044080c006a801c60020484180411480c0300c4ea206080e00a942d4203070350f02d28448000b01200e1556014181d80080a0340e40280500d103005014000342e01228003603240c1e1155201c1d6034812415070300242d040f5240c040000344c0301150b00051704d031141c86541c000c00c9004401c40306036102e10040307031003400140c2100f0014018900800c0c03850041030080b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 114293633 1250 114292383 114292403
    0x4020a020a05030d020315010c1203020702010c060e0c033304021215150a06080a0903121401080f0102070203070b030405030d0614042f03040204020705070e07030b010801050603010909 81
    0x1075203542d07040d9480251004c8407a031300002042004050f185605514074400c2c42c260980c8019a03c800303901403000411602016000100740041d03a00ca4500240459003280d810041c010302d00740c8059803011100c44c0e6500a0150b0501400f046480383e44030340805103142054040c6000000700030b140706070010f0049a02500903051174800c0c450400c0a100d41c600041355010311410008507041507000c007030810900c12821442d0900071140e214008540100b031600011a444cc0d9618007602c5450000701c40018003403400048043c0301c940f03580f455040b102d0506c01d991413940003421131403d07403140c20301c080c0d0542e0022030104000340c80c6100550788240030f0420b40b8140048a82044195407140d48038010112200200c2100c03854140700c0c42d00030303802d1107242030450650300c2d43c20390b0001504801031a1801c8040001819521550100d4160b6944401a1004103072501900d009645040c1d90f003c0c0028a85a20501554015020b00341030b00d1005103806e0842e07190508244c094a614803046031041c5070307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 114294883 1250 114293633 114293653
    0xb03010e120304030332090109051c09050913030c031806030b09060414070c290403080c04060503040b150406320f010f05160f020f010806030c04020a02 67
    0x1d101c8141c0e1000c510300c000d942d0707040c24180101500c000703800c0703401944c401c0d503030400ba000c0040c810700303103e007400a80c0d02100b079981140043c0108601c1c0000303001809022030398541a0381d1004070a507165806d0b11b82c1103102e9140c90511880070000c8403c40c02c900010200080880e025403851280e60381b007880c0202d806641210b403000380c804268441c3e00030076107400c1540c0c41454600840c617440b80307050740d01b040030003088403500000c0107020304194244000c0b40900c40034410b90b030780e10380c494004106800800d402904e140c40804a412542517002403510b0020070400911801140c0444103c1e55646085032500d44409086a5000e0a20500c608402c040041a62220301881c0000d0036100340030444003003540d100300c0800038514100442c40c85042c00440792503864008496a20800380b80c8a003202100c210203a0300c41c13241140a00d03194040501c241c00f0000348180f0011928070a5460035000c12200d001500e0255040da00704d98584c00074820806d05007000c2d400307444d0a8580d44115585c00726 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 114296133 1250 114294883 114294911
    0x702102304090c031409100c0e0303040e070816050307030b060408010f090501050901060503150606070507081b01030c23160605040b06011803030522140103050a0203060a05040b0301 80
    0x401030784840c012a8654090351181e07038162040102c8107004101c2206281b50040d0450344035100d60821544166403142000401881051159030b01c80f4050212a51245c03100c042c3e0391160000c8070180c000564a80c00900160b07103207001c005480599450341421a00e0f80700702034002e008030b00d61054000109100c00a0751845c02d01660100c03440340c07000040c541d880e50500f41d081d108001c0084889030304080003080300d901c000a0300c1014030340c0302d404685a03840b50f900281480c490070802030658400c1c0780740032a00420100d664030000c5038020340103120900f0103005500750746803440e0a1000c15810000b1031010303520307a0590400f4505428000c1e181c8136140011452030100c48606035640d80c0d4071010401004160320000d504020f0909164100c2c480030800c3d256140781a0000030104040464580786000040480c02d5043c488444600e40322900c0d41e0481c1003c07250f10150600081c200008980c840c0010301c22280601e2010b4104c030952030800090001400081000c00d07010740d07840a101071085 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 114297383 1250 114296133 114296137
    0x3081c060b03161103040302060d0b060703020f24070309020102010603290c0412142a03010507030e06011a041d0610050a0206070807020a051f1107021023 68
    0x45030101c5080d03101d00308807036119035034074020258200b84840e442210303402e00c8001060b1070840b40d04965440d80c409806512602411070303040300b0303074100d000860100c0402d90045a00500c0022190440c0e03d02c04496880302ca4a0b6211041e07403030840000f101180c0c0c01072003178000d10b00340b0780113000205446550f42d1383e0601d051040d034102035505000c50911500e46c0300303058105400c030130159030785401e20341002003a0000450f50000203012030940e420b03c07031000750203103c0002c01c12600040c08200344060003030315801c810344c0038046101e5403a040026090718002c0c42501b0a00c8035420041c0060ba090841080c55840020443c8968040c00d0000042c034013402a100402c0c5444494001c040381400010f000340c81c51885d24810030f010b400c0c080480b6055000400c5980400360b89030502c265150703050300b079050400612002d050f07030095401c0d0400400c243c44100d201035410840820980d004c1e00d000c0031241c0101c00c0000d41c031030001d94a01030400d01c6a54500890b00d02c0d902c00c0c1820803031031134001c002c035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 114298633 1250 114297383 114297389
    0x5032707060302040501090515160309080118031e08150310050a02090111070b0a0804080c0307110f03120f03090f0615030c10051608040b0c010203090705030a020a03081c06 76
    0x1a400040174020765a000400c9001002c09407840303403031200080b420101a0190b1039010104100c41c0840c80c090500c2140610700800c2070740700800c40d0f07a0741c45580050400e05024213070f0208605289980c14040c8050600c0342c040442d90b0780124a444030720907080100b00b02600958503200344090300c681301c180c038841e050280c540d015006a494180c40c00151101c452a116040385411008040002d0361884084441144e250b1400f43e080380c0e29407400340841d0003011000700c100e00c4040f52940c2006041c80d903421003a0320071034840524500750b41c1050341d01c80302212081d801c3c0030284403031960313206440c0c0070310b1704080400103440805400620b107070300d000030440d18403044000490044000d07060910091301c000704150346500c404164010040d00c94891264801c5050364003514800c140312045080d24090040d070340000c2d681d0300704e900120380070750030644280e01d0600820760000b03420301c2c3c000703002e1485a50142070341c1142032440e2115059500308031100c0448100340f00201e024041144600000703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 114299883 1250 114298633 114298637
    0x50d0c211106010801020f1209010609090501051902041401110f010e0307030f0e0a03020f0d0503030a0603110d0f0b0907050a06051b0610090e0102120a09021e010503270706 76
    0x919208a40320b2902c14180c2c0080e18991042107080185103080d8202c940d9581e02924103001600d4102c442130050210743d015401152814a07040100001074010f01c2c001d000a1144140341c00d8108141001c070b1040344100a9113500d0051002840e5000d114520004031103101610071341400c5d0305446094030070b01d04a0040942001a03200100341c2c0003c010b40141c442c1d46410101a09088086251038409000280c400c2d2014107084041d60354980112401d01e070700c0740582c2e860341005d981e20000b8203440d00007200c29100b0307911904042e01746243c07040c00701e5400c0002c034000080d16890303400300f804c000342403030007140540303c40031400b41c13a116448030041156698007560fa85112440161901030800300d920380303810001c140b01c020b034015101502a103050744000652100c0507401d060092040c5803224140d00120f8041040d40b2032039a10801e8401e00a881d45009085002c0400005101f0905110301181d01440860010035040d0f200c41d140480d010080e542e950030200c0341c036203003141640c04040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 114301133 1250 114299883 114299897
    0xa03120801150c02030627010606020706110f07050f0303070c1d06010f020a0204050c13030c050405010e040804031209030803090a05071406040312210209030118050d0c21 75
    0x120300801400c210704681101d1070f000030421200e5000035140d0801410590510744103001e01c400d22903607602506901801c0320020000e05a8070760380a520f400a902c07846003c21120480c0050402d00071810100c29410240540580d5050004001540034075202079134042c48240540303c0002c08e000b210501500b01d50000c081400401444004018402840b89041042141100c8509500026100846139046801203021360341c402d0341030194000c442d000501c503404800000103000550013400c0a0398426103062107507030f8035902455a40101a200203091100800040011926401c50a480c0c00f0b4185410034842e952500c0c0c2000541003501c0441d403581182d4101420007030700f000a0402404140244141c2d641d421001480a01440c48050f01052207018030302da09511a2403074600380c170700c0c08954003041041825040c1c000d42042485030b0107986440394a0000d42141d2a0b0f2240315980200100f121071412642100c1180345140211aa00d031044400c02c00380c010075020580b415070341e958080c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 114302383 1250 114301133 114301139
    0xa0c020f06100302041b02030703080402031c050304060e06010602030717090901061710080a0201030f27031701050a090207020d0606090921050306150c0105010603020c0d0f09050d020a03120801 85
    0x100486d102c01d00b20000e1454080e24044c403680d004019a0304c240d406081c141e00a50312400800d05242040c9120080700303485588000c05260810301841c011406480100b240c0340365540d599544041c00e00a06001d0b84c002c0c030440340010b02200c403810004112000140c01c0140b6100828007000080c0c100c800481e09030704010702000d2071112100c0e8080011003000f10110b141a049580301d81188070060304064680c4000c10b68250a5000444510080c1e021410105510803d00c0b40014022070220000b401c04442c102d0000320040301181680c1004000b49003152616410b00c0c000c3d405200102c1c0c000b0a240d18580c08180c152151000a1405c89004074018035103140140800e4060023020804000840c0250740c116400317015203a11a4003903420401d2240303200c0700156513005030503290440f5802d00340049641580b42d0003801038080854111481c41d22001c0d000d07105100a082100c0c00682d40100130081480c040f03040c1400030f800600266002522034484220244071101980c001c00c860744010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 114303633 1250 114302383 114302389
    0x103030f0309110103020f2104020901080a240f05040516050105040b0f0c03040308031003030306120b0423120a08060a031106031e0403020c0a0801140a0c020f06100302 74
    0x8201100355928040014864a954024492a001e5030850404d41d012070303004100c08040d0115060003e0030f0281c00528208402c29403200f1800304e604a01a00032000005400b001c009940a00070780d005001d2a0000502d842ea518840b450346030081c2d030181c994681004c0188107100c0c3d24040c80c0120054441c80d0b8845000860341303425980598108101084100b015003160800e42e00040314441c8540d64030300b1000000b03895801282c201038480040007040c450300d59000120030741140d01c20746003803103081e030b640092004c011015030018241085610000340000d603014510050b94160115042c6a202c80d01e4240f480c000540e01d140412050010b0b0b0520384641244406030300c0703001103c520510a00319034410110302c1100412600910012000c11440310340c1a00c040e42c5070141003c11a042d203001d06000707554100804007140200302ca01000700742801c06000b450090758120124016988403443d50070000d2107a07002c44001c40c000c2c1103500d2240c10041c44160b004140c445001540e40d4118010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 114304883 1250 114303633 114303647
    0x8010b03131b17070b22050a09050a0b0d050c040b040e030d060f050f180402010507060908090a0902090d0f02030c0306101a1207051317210a02060609040c0902040b03010303 76
    0x40f03a609034441c01c0c082010107142000c45039075000b800c0841c11045485042821041c015400655000060b00d502141d8801aa03008034400c500110b03091100c202400d007407003800300c141e540140c032581013580c07404424100b54000c41e1f00c111001d00700080301130034603c032203080d0340041c020944865121207040040385c40d46040c040190404507460351042c0303060340014011600301d03100b00c0e41d07240300c40d00080c040d0b80c0200300b40c54025030040d030180120119807a04000d20b40c8001d144510544040002090002003403080d80d0901d08050720440c21500301c0d440e1084842000351007240d06101e60704001c050380d10184907481c0200d9100e600100601c0c18200700c1d118540e406010364000c100d081c85094403041c200d80d41035400c1141403d00c1d03a901c6556905681c2c3c5034005400c15400085403100745d580500c1d0004441840181302040c00e2801d0707150306500e43c1c5611640c284203006a0201011540902d0b09404040e000b41c8100640036500e0f40d50b900b03074010fa8005601c4086080c0e0080b00400615400c450 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 114306133 1250 114304883 114304919
    0x180e0402010c0c0b0c010905060f090303011503060b16200a090f18030905030607050304030f0e0111120a03290f0d060608010504020f030d0f0503060307030812010306110301030308010b03131b 84
    0x440329282c0f800140300d335038a0005204071804280d0343c4506100d00750013513100340d015040395800c00d0b0b40c54411820301010700d00d1510080b0f4082d00d44603554200d2412542c1920071a26006010010352885c0014600c0609000105030320000d554440f003640751034802407070700d0b5114400c0e251402c80900d000100f40c1440401041c0b50203001c810810000045e90042030f81c04060028107041912030066070048891800c0410401140e204400380c01c0c4000c50808060245281c0c5a5810300c00b444103612145040801004040741444d044030380200c003880c103490580c041600150442c403043c1c0858846d102a143c00e6841610642d40d15414001541030814264a4518083d0001c183c0307951000750003041000f0301c2c0008410410084080340c6141d60500c200d500a50704201500c0d21503260300c00700700c640031082c481220703141d103001c42c0c0390b88042028040d43d04880c0c15840d0f0600c1ca80c0f801e4190740140e4001000c014000c100000c14000103900507040400c0004100b10940c0e01e00d061004441c5807001c200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 114307383 1250 114306133 114306151
    0x315060501051c0203070903021c050c01110c04090813031401291005090a0801020d05070e01080c0d0213060201020a0e0102010b030703020d02040219020607180e0402010c0c0b0c01090506 82
    0x400c03030340083d405121002200b008140d0041c2e03259180c0b03504403001012030700002d600c200c14006a4803044901500c034511140110f00742e44503040d2050055030302101c80d0200c1140c541259100020924107540b011a510303004114403850030412242c28142c0700070a800407142e1180002e05072060790b40074400d0142e011010010007240c1c00248020486004c4c4007506103210784052100080c42d071b0b20a000f6100c2c02c2c0c4015060824140d00ea42800380030b50400c3c000b40c11920300d40760006039140d12408114030402d40603100c102c096125069252016031002c08200d00c0c1030740800412640c4210240c82000500d02640010f88810004100514110b0038021481c11a81001d007090030340c0d500442d5901c21240d04580541ca11140c41c07010070060f003d80c800418012420301040010316402041c002d1003040720b6540c0300c1081030140c85a03030440416026510b1741254000004d00154021614202c8243c0541e50b00020075a0b14000081140d1001c4c51400c496512280f15208202d410051513400080780 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 114308633 1250 114307383 114307387
    0x80c06100f0506030402010c0605070c1e03052d0a0e03010510030c090e1624030504030905010e04020c060c04091409031207110105011401120e07060e030f010501031506050105 77
    0x14648207062807980103281c03080400101007000c582c0100c03111b41d0f04940c0504140a58034181501800001c0c40c010f050300c0c5000c3c100510381003860100c400214095041c1c82e45810420650030008101d030401035141c0090b03800c4040e1034071158400000d080815041e643e00054500d0103c09e25003541c2019000510041280c0e0040c40019211b41036602501c4111078001040789420f00e0446c5059480150100031a5500310040303400506041c3d034601d0200c151400911140a00c0c2d0110111441200d0190020302c02c000180150342c0b003480945024031000b0005410720b00207010050402009a9032401c0555000074100074000c624001c0346018507400d850740c0f001d49000c2c0d20850f141c0c0300d40c400382c0c044440c440b00000c449500484410706100c003060f00800c02903231a214200340d9a218106c485010543c3c08503034202d142c020740224110640300b030001d010071501e0301c0e0060368204502c0c1503059046c000c482c0c581d00000c009208270360096001e02c01c0b8149807070000703e0384401c80b64284c1205040100c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 114309883 1250 114308633 114308639
    0xa1b0305060d02100201180c030302060f130320100c0305070507030203030103020607020607080a030207020f120d0c0203010e0102130302210a0b220b040204050f060a180e010207080c0610 82
    0x46000203210745030103440e030704c511006036401280140300d56120480c582030b00d4260103040c003194126000c00d45e0310940898180f610740c440d0031541444112020030442c0ea41c9000c0500107885118178801054441e0b059400d981034143e111418001d03c110320b0000596583c00b400c0000d0740c58068590080c00c0760415618201c5542c40007510b038441404040c6c000d140014840d0219210001124400c0740c00000745515030144140040203540528004e0b880703440d000b0521141480e0102c02c0e52094100d6000504008113510070a80d04041d02c5d510599041d56602d43c100c2c092403080c0010300e4600104034082e04002d007540304104481c076840342012200a4548081d101d150ba00040501000da00032882c024540d03962411041d0684083e05a0481014041d101c1400c025501c483d0310301075031007101c0c2032199540d0258480840d0307004403040c03a800314024108004440100d01c02e06150345c03d040011a491000d00109801c4e684a03840481318240001941c004203281403003220380010703181d00d0380c0101502d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 114311133 1250 114309883 114309889
    0xf0306190b040605031503010603030f0306050108010506030a090f050118140628020c0a03051803120f0904150b040609080601060206041101021c2735060a1b030506 72
    0x10b502460090100000100d20800c840001140303c22800400a014141d22440d0048c181e01e12841c0399004203040c80300100b0b080d8010b500850694a01801d000e003140e0700c1d2592400980024a000e903042c2c08001200d030045402030007001c500507a404117080900b0800c0c03070403180011600007040c9907070700f0007818400f49120017100e600c0b10244031240c0c004803580c0079940390003d12400d00e06c0700c1d42e0302c1040034160415403c4409000b501e41202c0070386040200a5040c9900c490507086600c803040c804001c60030000050001500310480003800c00126181c880003c0484441c07a900050300c506400300381040f80c0341c3e01251440142502401802880d450054007942d1224045d00040840380e0035809000305074401c1144404900450507005440c0c00c0350784020301803940142c0b00e0b6100c01803403008146185082c40ca21030450340c61610aa20110450036054081c81804007001c10105800d070202c0f0709003104100c02d40c00b42920040002d44442c0c14010182e260074040590f4080c0350802081100540d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 114312383 1250 114311133 114311137
    0x21204030f050c0109060b0a0b0a020a080a090905090a0b0c1905070f08180111030c030702040e0a150203090c0109030209160918020c0607032a090b0f0306190b 70
    0x280d050400d01c111000410341510396029854100035558a400e9640b000e00200350043d802d144000c0e1340501c3c0950700c402e000a02440740c4000c61016a000340c100800080c0394400400c407215180c501006115203a10000095039800e507a035125542c00815200d09000c3e005008580003185c29520700d00d49080c50012041420720511040c051000102d40c2c102801613546600003160351141d2200c1e6680307543c0920380d5589100c1c61a06001900070390303860107200800412200500304036402103040014075800c00c0003810074100c00040600a0b039003901d000070000d8404108034030380d0400244c1c40745004102d41c2c7c900b4145200c09070400c8003c44c005c101688440301da058008444204509a5220410040e9502ca259900c040142902c82007882050301c83c0e0b42c0a40f1800f0b5001d01507900d2500c4482c8120705a4001e010341c204128840d40070010503200c1820412900501820400d07001943d58400c000103400521040780c3d050000810001c0914200000054010a010101d00e5141c10a13400e44164 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 114313633 1250 114312383 114312391
    0x1a030a03030c0210020309150601020313050d06090507080714040506090103030f0903050607020d12020c0601170106030605040b01140a0825050d050312090706020c0411090904060501180212 83
    0x4180e48207030303180d1024800c3c13040c5880e448050b02d040d5600c1c100302c6a0180d58160303080d4034015080b1054041080d070f6101104036072548801d1403580d007600741007008101c8035000301c0c04c0482d20300d07585214030000940c003801503000408440e80908101858454201d601181c00c52441d8031451030007040083c81d90305c80c1e00c024152501440c04c60414420203d040c0e5001980d0342016000380704003401c03c5030302540083c0881c01d03424180e8031054402e0b4480742400a90044500200301a027000005101c0c4007488403880c5200303445e100000c0b0380240c1e02c0d203c000880320259003c2d1080c519071030041c403042c03050140010f8050000c0e6403880006181c620b1003030316040b44032103a01c2c01201029821900f6a0900040310103424010130280341400c8610380541d0313a41c090082c00c0045603481001030003180020840200b25000d03030300a0103c0002c600108030080c0402000b00c000004244458402c944070480080d116a1059000213100c1d4104007100030814004c1006c80300d410b004020b250104011040c8041d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 114314883 1250 114313633 114313637
    0x804060b0d060608071502011505061608190e091b0d0b0418030f080c0f03101e03020f03240603010605060705070306060611250503030c010905011a030a03 68
    0x350300340c8000207003010641280504080e00300100400d01c81d402207500300c2203030304142041c1c2401303030820b8040c0d00380c80340204c403000d600b600b00d1010400c6060000c000c1080c0444640c041c101b00b00556107604198100484113100c40c031f00421402001074000070680740781c200c111060596407030411140c109800d9140c00465030140c0105001a10000c55045000010002002485010000002c001107490514400e070001002207038010300807400303611000d00402444071803510b0565040d40c07403461940003405000500803035100000e02100c000a4a800c1c4014502c980003125103580108000022103a01c128401d8101e4110f050501c040070480c0b4000c10780240c24070b2100d0361060002801429940c0c000b90f00400006080400c001d03000c111101524405c22040020301d1316468101c84407080340c44100d00e5039010740c0352070303c614601c08600c0404003040c141542c01c49446001090454002c6100803036640c1d140d181c144100a030a010312031860781c2250318990600012000039a45544000740901 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 114316133 1250 114314883 114314891
    0xa0906021e0613081b010906050f1006050f04150503040308010803040b0d1505041d0d02010903050a08060409023a02011e020307080318060f0c030105041505030706090f0f06080406 79
    0x10400062500381c6064040f600c45c0c001c9440882c0003928080c08071030204840c211301c6c00d00003600041c0303000310481c001d4145190b21580f0509005094480750300c45808804103610501000606079407024080c003000401382c6d200e90312400c051402400c43d102c1a00306041c03a810500082c0444040c0c4000c0c0d4544400600000c603070380450383c0102400d00740316003040782c1003818064002500035010700c0504880b16682c080781c0d640384a1207400c82c00c0f6100890001d0004804002250000d4890b10b00241c010000900c00100b4940c56400141a04c04410601001500152058030f07403071a02401d00341218a141e51074a5144c605500082980880a054582c04140203048036030f2180b003003040e114a03c0c0d11444050362400c2084d0311070394202c10b00761361200c0d07403090f940003814020780b41a0040c0114150203d25045074200000c1001420b91225a400b10889050303001440d56801c225100050034140c1720526020705250031000086081e401407607219118400410841c0d9002143c01d41c01600702800003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 114317383 1250 114316133 114316171
    0xf0302040f08030a020d0305010513053303010b1c0201050c070e040309050a0b1309020d0e1515100819180b060108060f030a080c030903030a0906021e06 67
    0x5002405960041040100315034000b040008001004081107245a000c980304c40d422445e0840c00d4450034002c540e0841d001106d004072242c80d60304000c0d0800c0400c95030b00310b1242003840b983d080343d4000c5904103141c40078001c42116803c2c02c0c81040d00c1d002d01921241c0844190961034a002c03c007000d0000c1c100040000c8040206006102c01c2c40035011040940c6400c1c1000d0400030168840c1d070185074840c02821800140c5100300c1021144003500807100b0616007490606003000035000740b01084042621110807102620b401c1c48440c849104080c4c011101d4100000500300e05040d18044030300605031012071112142d0864403559001501da40400080c020344a581c0c2c001d0191881c0da8500701c024103804a00f005840d150091050302c00703030384880c1c1542d140c42c20010b48101c0d613242c094068202c56502c0d008241c00e54010003810500004803482c1c90303a1400400e02e550f2240c2c4990000580e2500140f11481d4180004c1e40d05d0000f00301e41000303103003417410143c0e05c0e0480a1329002000a0240c411 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 114318633 1250 114317383 114317387
    0x5090907030b0103030c02090a1a040906020d110c1506010c08071110051207032d0207021908010b04020a05040504050907150905040b03070605030c0f04030605010f03060e060f070f 79
    0x54001c1c50b0b21420002c400c1d40d40e858003070202920031404034400d039141400100040190b00c83c44181c95050441070002c0c1c14a0000e010080900741c2c0151a0039400b0010784901194078007654080d40305c0b94000030365400c003500701e042c200342121400e019886e10004c2880096a482900d640074035070000641a40c40310350345810040c04c000c01d45100e80100d0300821525502c0d80002c007500b484e0000103405612580c4907201181103540c0c402000a0072915000018075550b00e4010400400741415001032410b143d54000450050480442242c40802c6003c141300014081c011007450140581c0e05506201494201801078019030103103900556542002421608007009400f006000c0308090b0380080d201217600816401d4140510703800350b4280014441e0504000460318111060360f038825040da00d4500c01e540280e4801c080c80c05000c04148808008100c062181e5030090a0041814240510790310300329050383c0c80102d02c0c0440303401c25010841020046112542e00400a24101c7c045100d80a01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 114319883 1250 114318633 114318643
    0x32802090a1a09090103080a110606031e030903030403081b01060e0c0c0102090409030203130617040b09070f09051603020306030c0108190603060c0206013303020d0f0501140d020a050909 82
    0xf140c1c00861080000b0522041c3e070024203051403a45d560a80069100d41c1e61030b0b4811050715199059808039101c02021441000c80303081040c0c550041e03900c1e029050001038616080342d0410f5502c60304c0007428211101182a00d10f60054142d0000c1c01f00500d804007a10340900000d2526180300400503003402c0d40c1ca82981121a103120061082017a0603050030000d6594210740640d50510008010110b155802a505210044100030001007140c0e01c0b5176910b8007011001d0481004e5114410300402c4090f1300150b070a0103080100c01c00a0180342030086100320000750f0445000345171040051082c29200442d28401c102c40a0a11700d01c035440b0901f0310000e820640d00181e0509180c050003100f084544e4000043d0158103030308480711079807151042076041c6103008034003113180d1005070200100701142940035805c01d62420014140344000e5140f00558240120040e802035907000148024075440840ca10000d005581c03545d1111310903404034480d56410701984d841540301070001000a181006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 114321133 1250 114319883 114319897
    0x1606080106140a1205190b0a0803180103090803010b0310090b010215090304170105060909010e2802040603031106090c0102030403030e12030a09030308090325050f0102032802090a1a 80
    0x100c00c100c0c91920107031031b0700c003111010b04a03d002420321854404519090700841d065a00e00006145070220074074501d4080c241d4013040905041e00d950040c0042001c82020b903008090500c65039139286030024040b8a040c141381c000c4016039280c444050a03a0342d00261806a6902000c50718580f034035440d00207032441c092a88921600745112005001d62101904101d00a50003921a81c82c96240c02e09a0f50036142c805030a4003603603000b07a040e103008181141d1101882110511040d00c0c3c45c1141d0041010f48030b254100341c010490403649001090010404154007000c91000761240d10b001c440000d480f40304501c0060100b005d01e04040109680e0300c2c00c2d10400c4075210741200c1e556003050b00301418004842c80143d0200340c60500099040101008990a000c050031082c0c0d20761401003001c02070640403103010365082c8a810540901040c0c248001c602542c062452821018034885050000040c2c8101c00112207005003c0109992222440c51081c2c404015103c40340405014845840380541a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 114322383 1250 114321133 114321167
    0x7090f051011060709051f080c07080d020307090e070c080301060e031e010506030d05030603070302010f1b0605090c0303040b1602120102030f150d050715020c121606080106140a 78
    0x40113104065800c01200030031514142ca244005104902000d00484910b402c4800400c1701c44000885400c2c00b48000c181591141d10440e0500c0e151120303a208907007084480601203444807606000020008400c41d40c0a00140703048404000b56a40317003446800103100b61014861442124034030346d036050100300351032104140703480f0b032014501c200e65020340001d6411074000c0c003800d1540c0b0540c3d0b1151040b039114110140050039420f146900458403040034403c1002002515048010761410f10440340e01150301841c4081880d00345116a9400c0846441160b40f195001700000c10403108564280c49041694541a078481d0340389002050811030700a044c21000e520001c03c100102d007600088034044e4205420030040c1c03003003240c00e000550650f80d90141c0700754003521082080c041c6491003102852031500c103031884035000c01c0200707031b80040c442440d12480c2c20082c2800741e26101d0b8042d0800420380c62810b0301665242c00c0025144040c1c01255947c048000034010240e24080c02c90304024003421 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 114323633 1250 114322383 114322393
    0x7020a0206070f06050c0406050405100e09090a0209060316050906030a0c08010c090902070209151c1103060f01060f08340e04150b030901090803040302100507090f051011 75
    0x586400c15000800c0c0c3d800b00c90651400b00401c410b02100c0c003d46060b42c02c5900e4061515007008100142a10b1800c0c4100c1002204025840181c4031030240320b0007400b0302c1f0000c005c1c4102e43c1c03041281a0303c00400040c0a0790040e02848400e0048202c0d00040321016940244c050300d62002290404400741c5007e044281c80c0d55000a03012015406400e40e0011a5141c0020310384605019050b446125400780d03020402c00301080003640d410030211740840c0014603002c040104a80e041c0c1c044586418207550038020543c603210641403e1004d1603119036000c103e400e1940c1060340c090410307540d51035164108003400300000c034061080300b2510030404200c28000201e00700380d10f40400700182070500e4400503528400080280c00c00380035682412108440803030a103820420488400c0d04018815002c13507480c0d0301c0800108200600039400b941c0603134083c104201103c1580010f40c0c00c090650380811100b1102000001c40c0c0c0d0408000b071340d00880b40380d040080c01000803a40307001c03c14640300d014003803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 114324883 1250 114323633 114323647
    0x19020303040506090604080d0507120608010c080604021617070506160f020703150b0a12060c08010e010308030a0f0209030d090620030703030914030715052404020307020a0206 77
    0x405588554810822a00d40d1341d1400c10640d100d881c1038800500d556001c6c801c926813a0140c2c3c00c42da40c01006481d103101004c0840401c24282c554960000c0026550f8038070504410f50b01c8000f83da1302003400e40341546408000003215010300c51001001d00710706406118151034420b41c50803940d136581c01c201100d800f130601c2c4c8402c0c0b1003105254140004190608919181d890005c03c0200840b500b004000020002c0b90000001600005469607030103010000089400d24450103107161090041c6000151401c5202025040e00c2040e00708600c00100c80c001040013410a13011280d02c1300f50004080340c0e400d04a1004406070195030107a80d07060144000301500c15a0200b180c808441a9980e000d0705840c0400c890340c0c001d0079807142002c05420400041c40440c0c000e41040c000144074061100604030204510b03401c58001d0b03c0e0894035001c0103840030300c07421424000c0d0b50b0007021100c08041c1d85a550075003d034407158407a24050050340c0200004000500a00c42003000303d130054440d5a541039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 114326133 1250 114324883 114324887
    0x3061809060a0501082d150a0b09090a20010e060c01090b060406031e08070506090d02120f0a0e030f071220090a021c0e010b041b05090909010219 64
    0x4000c0320010b0b40c0610b090000030386241c00240320804c0403032101c01c11070301c5009214640c041e08604071050300c06100d290201000128914400c51081000942c0002e65904040070002c1c20400600034400740d9122002000119001c62100880b00d80e040605074980d0181000503590310500c40203580e072210011400b000707040303419000f90f4191480b42038004681d90755941000102c43c8640005000d2040c03003208000a00d09031180c42c00b0032402201018140080d59541528142048902e804183c1007584480c61460b010030101d41606241d09096003040758214000420340102d10b00c52080021101c2c4d45045a1024403000c58080300307a0381641d1110b601c0b014504c6404015820403160154070325001101000c100700002e40000004003042c000c5d444a0310319101a41000b2111030740c400000d020155501891702c40c4502c0300001800109141c54200c040100300c40100b001d010030761809510301e040d02548502150080c0400321401981510b6810702ca600901860488405812004044600342c40d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 114327383 1250 114326133 114326143
    0x1e041506080a0c03020315041116030903030e0102030708090f0a09021911030a080103030c140715030510050a090f0b0307060e030601230d03020a0c23040603021503061809 75
    0x1442c50350082c4142d4552001c110224030046440440c211600d030315800041c605a084524040d208507209420604414214a4003240c143c0c0101e0100e410b038070080041503040402444c509900b400603600f40811521070120511a22501030f00c519120b414031201a44ca103040c96015010000e4115118850444c141040001c03803400407000c40e10002800c006d145000089131b881003229501c489160f441d55400341c48440742a074007203075883c907045074520168030100908801881321070059298000b02c0c2e0005011590044e100804011f81c42d00240840d407100e80441c412241044000200c580d8a000b4a000030700c2c03140071351581070080040000341d81d540103882c08034000d8100c05407007890740e0300c1c0c0c0c031610304107001b03040c84441c0c2e02088100c01035858413450b690107050107030041c0d8192107550760b29429400d465803c1003544024030101040403c5000113032035482d030001c0e03508101c0c0310f0541d00081c4841c040c03030200050004000000642e83d848020442140b01803804010180d070500000e915212 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 114328633 1250 114327383 114327391
    0x18080304050307050607050c0d0812040809010e01030203040f080c030403050712060b0306040507030206130b27041e052707050301110f07060504030203090d05010b120c1e04150608 79
    0x43e10604001107030b1490000100e403206a4000001e0603081004000e0041a2810100c199030700c0c0c1c014403400482c22034403c1810710441c032800e541c80d942c0701600005081010726080c4541058418010400011010001e1010842d000300b855a1501d4100b03040c42d1035442250001130a0780212200081c0680024122100152040c5424001c00390500e050550319002120041c1103540f00d030300c0400150070204020444504481482246191641c030061520b50041480000013001a80a44080c601c600d10514064008903414003131240b14000052154032001104040c4c181d940c40801c0d2641184050159075407014085002003011540300c0e5a21122284910750103035080032002070380c07060682e04036545500400780742814249240c41f03080081030000d0040b020b5110401c24803029a40722004000858401e074000701b500c59000741071201280705d0544800c010f5200c281f041d2110b5a07150107100602d102c00e60352030140c80d1144001005005900005800040040404600d1544c0601c03001e1103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 114329883 1250 114328633 114328639
    0x150d0b01080c010c0314130506030f04060b1e0f0604031a09071a040603090201030b03030409150b0a0c030503040609120302190e0f010c02271905040203060f071808030405 75
    0x24001900b0040d200d9600400000300019140314064400851200140032029440c928980d0295103030000310314181c3c400d8440034051800c00b820001000720300d0081108285050b20030150055400846d1281070042d0305505101d0003940b540c5580f00d441381c009840042d50407010f40043c00d51900089400920195050003040c00307801d40220300380d5400c8420084070006110000d1a061400004800514642d0300c02c030304058541c4807441e680e980c2000944080d00403004c0c0021039100c507078507040041c42154040400c0d003100b8002c0f4011590447e041f500f440d609400e100d642c991780c52401c8001856003807070041c4441c01c040d010301d4901e903041e4090403202c140b11031400c004003202441660010b1059001381d500245007010f18a440d40310305040410b50f1710241048034240503085484c21420b0a03000280b400550141c02c009070110300406000c0400300c1e0400030486810a40c0200743c0300c07100200041400085200400e142e144120218900c04e40710110400100751100e180c03549030b43c803901c00c1c184 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 114331133 1250 114329883 114329893
    0x2040203010f03021e15030406090b0106020705010201061e0501200a03030b0a051906051305030f0309030d1d0d0821101512050702030f12040605010e010e0f150d0b0108 74
    0x410181c04081c0320040c2c05c014040d0070755690030590120190300c0280300300da10945541440d40000c80c0d03a2906800390034950007515146080ca000282101c02c01e034003d07a07601c1038003015510ba15452034005010b942080c42d045003c03410401000020074240c0001c8140c1c3e00c81c9040c890240b561541c007031482c22034122044158107680300e0821400810304098281480340e444010048640940300070003540201a032013401041da29000a400c1c6016444042155000080c091010303140c1408003c82a060750300304265010307400b00801c56800a031554203406061459403210602c00c091060300c6524000303a81d844e07050f24502c06903503008182035a085011108a40b8049600819218111502001c40c1d035006502e000c3c50074140c01400c00a002d83c801c0d03000401a04200c40b8a1034000c03c0c0180f26008070b0440c5007080d1174114202c0d0f105a01c1000b00090850042c400b0a490600c52900482980000c600e15243d00012142101c0c0c203110b6240d0008642ca0b0b40c00400400c0c001c80381c100c0d01e0101c140d0b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 114332383 1250 114331133 114331159
    0x70f02041a0315100909030e0301060b0f0f070c0b070f12020f0307031b08040f06080f10050607030201060e01080a030206060607020a061b050a080c010c03140106050d0902040203010f0302 82
    0x384400764988580d80c5a0408140794030640c551088503640449600e11940003103580e04001422180300d8030080d000295483c0200b10300d402c003406910020940b0a1485152002c5c0d0542c0c01254045d0030003070480c26074001448070038402c8540c800406000c500c000f0317030707501c0032039240612401d16007100c2114503064407030612240e18000304000e00c80d03041c1c3ca40070311314149407560100d0b8180c0c20820341100940c03901e410200441c840002800142854101c4014660f04003c0094403140d0020700740c3c504d0901803420402c004110105083c00c60780b068506c180c45400354541640501f9240d0401910078252400000e40c07034800040000c485030180c1c082d203040c0c1e01c031041800450300c5500d0300603400400d140c50801801d88141d0040b10100040080c1d118109030795520b003801c100b203082c0c003500c1014002c82c002d00028002e119a00e1812083c0c14204841040c8202c1318003031000510a0500b03000d07000c00c0780840c032143d64200c1c403210382e40180115070720341e16000c00b4103100305c040c081a401501e030071001c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 114333633 1250 114332383 114332411
    0x3031e050408011a0f10050307141303140f06010b070f050c150d2909060d0501020703051305011b030302030c070606030b04060b0604180515060c1c02010911190b070f0204 75
    0x31400351b007041c2d607415166960f41c01e4143d5105d0324414515051840822500802c100c11641c0e001c081c42c890030307a02007084400c1c52600e1908030b02d8001c03e19280c00042c01000348000d104200c8045e2644004a218a00b40600300385040c10241d0ba01c9503000b0122039540184507210400400d04e0b004c0700e000400205041720368010100252521403100d0b40d030719020300309561401d40c0c1101c4c1d01c03040050170100344a13247d6032940c5c2640c01ca5102100811008104070024042c2c001c2010040c0c1802e1909507042e500c0f941414a480104600c040c060650000c04650030b280c010b401c4075820ba80000c01440115030700d241c0307902e4412007141c0c20366085241c1100710105142c00c40444088501d150f4042e110340a00c00342500040002401d00d800408201d0070007005510380d0009800d0120b595409058081800402e00c140192202c01d0101164905823402001442122288a880800b0b4555a0340c0c00d02d103221078a804821500082502130010031120200944007407443c0702a48240c8051001b055000b0300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 114334883 1250 114333633 114333649
    0x213051f0807081b0d0503040b040509070e011209290a060801051015020c0a15030606020c01050a08040203030f03010e0106110a0f021e15070203010e030403031e050408011a0f 77
    0xc90401303420850307a0304150b0b4802401c0380e240b250024018036070b554032540d816286d07a029070301c104d40040b004203040219140541d03903030780d0069483c00c182c1901300340c20000034000346204041c013580599981c0c0031818441e050051520000d005018a0b105524924054410300e03002c039143c4107141c0c10f11401141120f0180180d42c01161598103020850f400d201481400b0703105240000e00714801c07804444900c0e80d40000701d10040001c41180545a40f8450008082d00d02030780001056500910144c0910717644042112a40d080e1803502c4c05081c2c5891000a00354464600030900c004404000443d2810b821039065049507034035200c00d0b14010885032069180d90607082c02400b942d200c007480b40702608091010a0150b400300e407a0740c5802400c0400908810208403c1e11585a00030481108609007441419a26800c40c80114203007465550000e00b03480c000058a03880100a40c030903a0164024015a0080d0103030070000c0c403100d14009151000c0d070b0b08550b8031038442c04200d022407880d41003009c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 114336133 1250 114334883 114334889
    0x907060203040326070f0b15150901050408030c01020301051008040305040b031305070f08010f0b1c1e051b09040b01090e0307060608070f0510080604090213051f0807 73
    0x80d5082c50301d1521182e440030700c02054442602d07042d0101c00c0c0d20300220001802500d01c50070000d13070f00b040541041c4801d0603000307240948103581280c00091550f0b40013100900101014070140c1da403440a401204d26016940c0440114170004ca50303440810410340265058400560b183c402c1c900ea42030b001c42e4480000e803009400304c1c00400007440b110340803000969100a2410b1050b0006000d0f039207039817034007100340c3c00b030701d032440e10117400388444042805031409107000200c00780880e01e409000180c8110311030b000341e0700800705921040e00300720b2880c002c64419082000c028281c0c49841c108991918804600c1104060840c02d81045c685400101d803402a50810354080e049da0800407008003d2802582c80b41d400d00c418460f40b80040c034540540c02c0900191406019041e10f04040c0410341d500c1d5030030451140011415400c000d960110007140e2108049030301042c031506070700100f4005820100d444802c00e0030f210811004078030201503c0304074400702141481440d590804152519500c0c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 114337383 1250 114336133 114336137
    0xa0606030b09150c13080307050601080c1002250e0405030901030b01211e09031d030c06030406021309020706020a0809010e070b0c03040b0a08150108040c0902070f0204020c030d05090706 82
    0x100c00b0400c40b0380b035a030150003416404001c150500385c450b03221b01d00d1a04080700480c0e1a038040c50041c00001010700040307401130003e80341170054100b2184003035100c0811034581d10f40c803040c41020f8050000c0280600b8000c0440450440c1282401d090860720b03680b1940343da60200e414000903030b506500c5030254541b01e00c81d521641408000710310004020700500f40c90340c06203103002d61000c2085100c034031444005902c6611506410405d540d40340c491a959822094400c0e0801040141c20388c842800320b0b0f034000c1d4010001030f91201980c110f88840c20140d0400d00d451f80c404100e11040181e142d00602c0b5044182d1100308042d078403c9851420b0b42c3c0c60f00c030078007070a402429082203140400c00203000b5040c400c500342d0f4201510b807e0000120303081001808002902003050219120042011000d0030400f031900009514180e03e0b1700c0340d8251580305080d40d1581c006041018440c0c08004240c0300b83d4020415940e17100700d002c4a0396a41c01640c1442007091030b000104145110019900c0c046075015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 114338633 1250 114337383 114337423
    0x601030305091c02060a03020d060b0705120c030d0c030c03152303010902090403030605131103010b0903030c060406020913020702030c0103020309030c071d0c090904060b030a050a0606030b09 84
    0x79414030103002410500303020581c5203c1150b42c0140c0c0c500025048000c8944d40040c1c8031408180c0007401da500303507801151a50010480c5401242000c85c0800d19074046014035581e50855880540c514811403010005543c070380585034010650581210f55074461582d814007201d00015003410a101d090b10403003822104140300000000d4503086c4145a925004000081280e00790300030900031340040740d0883c0000c3e6680030502492810105423088810541800c0040d0074011504402901c01030180301c440c1c2c4404a18148250b6040040700e003246505030a0b6551824540340c004081c2d008049001d01c6841484210308004491b4402d80715100d40040c0180723500d800c3d0070010340c029400900390074440d0000f00b040c1c0c402c900b800c100000041110a05005210742e81c80c4580080400c043d08801c0743c05410031035034a1036580c103900c443c0c0080e00158009001080780700064580a81d20710300410a01400c106d28040c0811a408441140d0085079118007a0b91003801054540c0c0007500070860700514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 114339883 1250 114338633 114338647
    0x6030b030a1104020d0f0e0d05070309032003150f09010207020901120c030f08070510331d090f0601060c170708190e0f060a030f0f051006080601020601030305 70
    0x5005801d04501001510040c60500c005801c10301b600c80108038031a066480e00c8600c17011200030001d00c07552441070300e03003103041445599000707101007113a20000d0f101007410241c58425860b160140402200014103c0c0c25038864824103050080c0f04072401849001214006141d000c010300895560aa005184003420383c2060400b401900903444181e920440c52140800040da032a0902c0e0203040c003d40e04140c0b540304c18a05546040b101292190304070b400c181003048a0b0491602c0300c80c03000400c502e82d5240c031b05071244082c629142c680c0316040802e03505402e980d801c80741e4404503003d40c699600b59540c20355482c0001c0d230394013000e100340c0d4000b58500060202081d003805060b20b442009205e41803030700c0f02c1078462078026000140140740c00e840480c00118615004a0603500000c030a40342c0d965003030007860001d803c5002c0c040c1d20f8014180c0350010240801c00541c000c0c0c1a00c800c003142000b40b03041201818a525100d4050b00010900e0f08020801640c000504141283d0b81983c4103031a00799 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 114341133 1250 114339883 114339893
    0x50c0a0f120b15041104030c0f0e0a0c180f050a090509150705090411030718060801060302160f1a090c0603010311030a060c030515040b0934170106030b030a 69
    0x1000601515145440d100011899580c41c091482a9005c003c1802d441c0c0381541046500311710a6485030703101d03181e0154100500d11612848542c400b02181c40000d40301280e0b4000d07210070050307810107132100d8561940031178107400300e8001d482541e409403007a200c0c103512f501c011b00448405a90b0004194404100040d41c0600004002e5000c0c06c0c0c3d161243c20300f0620804502940c100f40d10802d01010301104224505a0194080f40111007a00c1c031005601e19242000e020120180a040101600020f00ea041303203049004840340940c0c8001403104003409420602d0504c0d20b8602214140204200402e0894100050301d5600c0300e00180100d2039030340385a40d4154060401c0c1c01c1c454041c007850060f200466158451001b2610b80317500d0204413461300c91101d00d40441801040c600c1540f4010401a50340c50b0013180c580c0c4201ea485200032012080301ca1140c4071000056140001c000340d00400c00840d5019660b440307a02441000d00d031a9980f81d04069060300c2c100000e1175010340c800860100464 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 114342383 1250 114341133 114341153
    0x4061d09011a1308100f0c0f03050604180507030516080d050a0c080313020a06050a090b090f0a080f01050601030b0d03030903030b030d0512070207120b09030d09050c0a0f12 76
    0x3481007420b041ca007a06480d010080c640d01540951826017111101c20f280003010300813030720384502200d800c000f081c2c000f0002800045030f21404030201740e503a10000380b407911a035114000d400201d0700300f40c403007204919000c0d80e40c0c9035a000803920380c014454107069840c028201c04d42a102040b000e0240c1f004600300845654010741c00c60410404419105400724011000641c000c40300480c41008500e818014031075460074941c007100800c40c0c2009060f550640c407149801c20f4501c9450076654038140d100020b032504840700c600590280031400e0009001c40b000482008214600e40241b04c66919000150100c0d0b8100904942220750520300c040000e119500218280e4840d0400150010f002c0003c031349010300e507591a50101c0c0300010b20503809600d80b460b6942c4120144010140c031800d00a54003201560140b00400d848100c07004911261018030548000c0340344814104100f080c0b80c240f140e82c540307a807000d0380d0084d031101e0800705142c0c0104d030780c00083d1000b034407503c0d09510a5036100c1d404a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 114343633 1250 114342383 114342419
    0x7120c06080903071e0c05220e0307020306070f0914010503070c1406010b12010b091c060209040504030e12010b010509010f0c0b09061008030406020a0609050c090c04061d0901 77
    0x54003003007042c9130008107140c1e8900c01032a04801d2200c0501600e160031458504c4941001344074000d44443c0d12032243c80e2107202500e0701d18441d004191101c4070b9081c00d18600820b01c00035454010740b03040107891903105004440381016031f602e8002039070741c86203800807206080c49014006035081000906090060400c0e10815101d0381700c65100800c070f1020303141403100030303000310f010300000141c52480c0c014414002805014450145403500220000103079004080078040c0b030b00080c0d0850400140a20307907043d1801c012001d0b105001c50b1503e8030340140700000c500283ea124840c0410380e4800c40405120f242c1c00d030303001030b1a1149030046840c019030b03c02c2224038600b010040d9030381582c00000c45000c5100d00440c8000010581424503c50011021401e900041f07104e60060204101c0b0715030000307500011980002d400641010707182400d906003100313024902c0d0050540f00a0000b11171403940200101c5000da61224038440105030100104018107103000d40c0604040014401d0390240e507841c40c48 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 114344883 1250 114343633 114343651
    0x70306140f06120f15120a12050c0d03020d0e0303040c0902030a09290601080708010b071536031227080304020102011116030806011101020f0c07120c0608 68
    0x103240e40103001c41c8042c0e2040b11402c204c26013240900038801c0491003905035503035040301c003903903450190250030751340e03108081b8060070250a807125035030594010000c9a640903411010303a203034008407180c0500694043d00c0c603414000e01e0414200911080403094900440d4030903c410320052505d607146d0041d40010b0302c141d0750240d690714000c0000c0c1428040d60a00c85070906a28401009041d0018a800004202c01c0c14440d10a00300b00010b5030180009040d01c4c88008041d40390006400c0c14100c0982c64130211007405c0c035100c0342c41240c403080348806401e10364944054000380d20ba100303441c0c08400f0914000b0086482c985c4240380307501d60790f0084103000f000c5c40b140e0071218603651903074011920023400c1510080c60000030301046d07590a0180482c00050465000c4c5080d41441151042c00c10204001d010040b2920200b54030360300c0707100048030342032110000b0b54581d84201c1c10500d46a00006030010544240c21000803a0a00c907101210001e0300a0b4251260b1841c000081c0e8914a0042034048 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 114346133 1250 114344883 114344887
    0x70309060b04021201090501080f06041b050a1d070908030a11011407080411040b0d020904020f030706030228020a29040c03030f020105060303090f01020c04050c12070306140f06 78
    0x8920340b240d1001e07240003803002a84080d00c1d450020814101c40d0103801001060700440c101034101140019080c0e00710f40d0281c00e09031044a800c10f0a03102d100190091075000e8208100024000242103c0c141480103140d840c45240d1220502a2040045849030700c00d42d0b04280000c030381c01c1c0e01441120b042c500210740080f442c12684561010300d00c6044642d10040303072000060105101d0441840003400300b081c2c0c0c0c10840010194001112403003c000002e1040110900040c11503c0e9080866030014019085074480c0751964400750281d003011413a50a0034490524460520164005180139442d05401418000b0b0b617549445800b072080084000e0602e13010f0042689c41041d04c006203201e00e00412071001000e0842c9001404142800220700440e8104800d220036903030080219480d802c000c444110391901c0e000c00603420600059a0917911615290810590110140c0100034100e8060501ba5107550f910030b042d4200caa180c050489101c4508140c04264200050240d89175080240024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 114347383 1250 114346133 114346151
    0x6010e0109170a2a060810050402030c0c01050106020c0f0d0f0602030c0c070f0f080102070c051309060f09030306050108040503120a0209130b040f0204053312010501080709080607030906 82
    0x2132508403500b84284513445108401d0b079031343c020b060a500c01400c000d03c3c12028600b0311821601c2a035201d0b00031144519030010106502d10755800441e070441c2c2a100003445950307036508002e034688040c00c00007406005081d003000241d00d0a001c11020641d40451702680102c143d44912000b03410092140410b40d0007007080112100d800c000c44c50003070002410240e0138500f00809481c84421507440244540c1c010300c410000a00c0300591709082c1c0e1030a903003682c1020100703500d41000c2c00310388501410481c5084e40c1c0351411452500050700741c0d030007903e05014130f507a203000448411404031030140541d0010700004030100c403441041c5401c519814005410003881100140d0a03281c21216500f21302d6076241c00c1e8a40d401e050080c2140c0c40d50404c002c6081520b02030209201218000302d10380300e801c03101c1e140300d420f00d5038000d41a002c1826298103520340019080c00300c0030f41020701809001c00e07900400606034510800f0000250740d0800f02070415501d42c200c0c19009480000011108280c50368044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 114348633 1250 114347383 114347393
    0x2030106050d15060905070c030c0602040b1606050f04020904030804020d0c08150f0709050d0501111209061303050904180501050702030d051003050303010608150603010f03030806010e0109170a 85
    0x2e000d08034003c1c40300c400c0e80c907500d0311003500b10b421981c020104a401e21040014003900021481209500f50421070703405449460068003d02c11500000c2007950040740c4400e400c414952138224903031140c8420004c40c1c9820b494000150710480b4002c3d440a803d80000f80080e20070000d564000384094104841501940d842c25030042060700120900d900502d00000c0903030714400c6254001c00e500716040d03c0d0707040c0903c00905c60485406481c0c051180e8400c9081000402d502054000c60600882e03a00c6801c1c003500519986400e540302c1c001441100301152540b4013003101c900f105545a21080e01d0855420180006015540002c0450000030100e20380824028000c49219600b40c1e405507071307100221004c0404440014256007049880000140001000041101d042d103403030f1b00f0500d5070341e07891068140ca6444420281c98222101000000d425121091a0340c1500e100380c8035000c0c159030301c00044915031502310030ba40c0041c0c00384004200700802c0481d6000c07001c0648090300d004004545038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 114349883 1250 114348633 114348649
    0xa12050c01111605010b0103050106022d0102040821180f040b0907020f0d080405030a031512080310061b030e0102010e0604050a05060115091401111b0901120312090203010605 77
    0x1010f038003103600c1c00140c41000310a228115a882090034104825410698029501c0c6801e1604c170300c10403c50413400c0c4490100e006000c001d101c2503002550742d1500c2e00900c5482e40309120012100d24030f09550181a0313407120050b81d1040b00801e0328005000138200c01c00030000080d10b0f21726041503603510b095043c0e40780d0151040c17260300395400800080040c21155403601c0d4071042c0000400c01c90800340400100040100d500d45181440c01043e0707202703031000d1809030b0310481d40f20032000ca05000301c00c0e0410a8030300186111346821740d05081c803250f5400003522007510f4a0352100308401c00000d4680040d00803040f6a1030300d84184000105c10403400520342c901141510300b5a880d0784038030408410030000b003160034007400c411201515503040f1443c1c00f0341000250300038500e200824421581d0700e47d00c983c9200c003a81320000700322804601c0b400350a092490700070b103185018000440010842400084240c405650b0594078110340890511640000380742410301282d03d55242ca600107220b6444c140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 114351133 1250 114349883 114349897
    0x406060312020111181c0f0b01060305090c01030f021309090c0b070503070308040512040303030509010c0212180d050102030711100507080c0d060306051006020f0a12050c0111 77
    0x4000122a81182000c1c0706007405030180380c0031a03041134004120140c418090310400c05c1c000356103100b020800c5000a403810740c5800342c41000c1c03d04c403a61800b0300641d080c41c0060340b40142000e0070340382d8032510304406581088030000350aa001440120265101b98026030a1741c440b000010305000c501c060701444001d4942c41032201c0c0d5103c03081794050001e0090100c004000c0810983e00d440a40da503082c0d280d0242c42005410301601000040500c4803d2101081064951094955894403442d01500800e800c2d110200c066207400045030405000003045080d081c0f081c00310b40d0800450100c6041800300108000b500710210428100005000b400603501801c1940c942903c81d42c0910300c0b640c42c0002d41c0ca03010035034500307200c103100c0c10030703040311038075421040080603180d86050748648c1ca80070705269800103094918200800031b4440381450354000344c1c0d50302e60984043c041c04007030381543c0c2d23084000c3c042e103081403000c00201c405000718014014000c070703100085440e1b1702011503030799980c00002d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 114352383 1250 114351133 114351143
    0x20105060d0f1b090603031d0d0803040507050904031101051006090b0d110406350106080406090f03030507110a0c1202032806110c060619080715031b050306060708040e04 75
    0x45c070901c205908554070b05000d26a092074061600d00084c0040d0710302000c00006802040f0010205050101c00d100200c050706020300460003504003032074000d00c14901c0100c90391095107058007160a804543c100030007180d401d952000d2403a410020719051b1035000b40200c1c6141076994481e0400d43c80303040050002031808e500c88501c00c007040c909021b502a110b2001d144107070400c0d0316007803030407001c4a40ca9054802c40c0c07500e0103065646243c448010a08550054185100c00151204143e130540050340325034116607428420305d130785018865841c21500c10040003814608824050b5001000022040a000030700b2100c244841604075207200d0b41c13042c0440e99074100411424140300040c052864664103003503001c0e01c4c0c5221106855211103028000500c105044483e14100214141400c00540460f000341c98040b6130360040c100c00c1c607840e00003000220381040a07190701040d07058500c140c801519201c0e28039540e1018104800c551108201b10740680c0c00748004291451b15080d90fa1083e4459 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 114353633 1250 114352383 114352391
    0x1080c0f06090d0506040c090c020601030302030d0507030902040905060405010612150b0a0b030405030a03150b07030f0306150809060a091a06010210020a0806031005060607020d060b03010e0d03060501020105060d0f1b09 96
    0x4c002340c4e2040d1442c1403c0b21080d54808001000081d5001045890b4014440710014a83d03d0324501200901004030000e940141050104000d02001081090103a40300b18000c02660383d6a00c00d9880181070001d000e842200c01721488d840040603a08041c61305440140551074894451203092007a0304265000d491039131000c2440002c540d0188641e4800741c50310f0100c18001e51620500780401d00c2120401010010707003074080b0051078042c0d00a6809802c0400001103100b081e2a402440c18104454503c0c06210f440b008c202100a6486001d030341c1070300140000c0c002481036000d07159010026046604500c60f0300310110426295201074001403209036240b2030242082801c0501d4200a003400b07007105854801488440c1c4c0c1c2d2802110840303070381500d40c43c1c103d46c01800c1550052000d1600e1a406500342844807492242c00b1440d000d041045460801c07100351200012822074a046078041d4101445200f20000308030816034000006119201c1d0101e6010760315001d0000700720507400f0520050315 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 114354883 1250 114353633 114353639
    0x1506030c02060105101d040c0518040e03041716030308060108060108090309010c050109080a090f1d070804020d020a1806061d1207030602030c1201080c0f06090d0506040c 75
    0x814000e4045006091000300210350601e00040c0391030b003048510100380100010710b85c03008064882090b42c1d0200090082020304103241010344141e03c0340f9007050f100f08040c1304210503490284502400c0d201202c006500301402c022000485044a03400020b0f103203d0104505000f0100301203410113548240c1e603410721801c000d80050808040500001d06009180e010080e0000000082d2041400246885c400e10015800c100c5e004100201016121400c00110014030f507070010340380230850b2041d500c9a900e6a42d03a071440014043d030f080401c0413200c0c500022901540c45035103001d42180c0010203140c09116954005400ca00e1640d10420109459095070f480200c2103101e50002044142006010703a00843c00260410001618103441071210703494040070b0540401820000c2d6911040840d40c03400e00c1d51000b101038200d1100c00020030000c80010500000125410722034450150010080b01c074007004011998012488542d005550304c0c4005010403410060306006e10300404400301c245003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 114356133 1250 114354883 114354887
    0x40501090201140a02060a0c090b040f2d0b030a060b03190c0c020a05100207080609030403051911090a020c0a08070c0e0412030f020f0a0509101b1e061506 68
    0xf0741c4100f03444060030038042610840d4000c00c00c0c6505c200c1c000741c005480c851443e4207940c881e52503000b4040d107c80204022a2810014003400d05503204c0b0510782480e102100c0002c6420100301c08140c20600c0713080c50401c83c82c112080616084000c2140203d00d81e91601e81528440e042120002080300c4610030300701c1c0c0410140300d10340c0300061900c5c010690358a1900400d00c1170116114560180086840641304c20344240b01c5070000d01140016210035092801e02969aa00540019160f134024104100b2a143c9011035400305d6690007440f21004123824010000d40710300003004040d8294080000840803041404460940b40c4143c405d10384802141c10072b03035031014081d0410704840200a0601c4040b800300107900b00090884d1501003132060b070611030040a4021400c1d460300d1005c1c04561204181d411034050981200306a031003058854038040106d505000070040c0751403030107080c2d070300c0c10110342d0b440340320050032000e0b41c00032803021101e0791114100e41d20000c110286669810081c40416 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 114357383 1250 114356133 114356147
    0xc0304031e0c08070b07091e0b03040f210e100909021e210f0c031819080d1505010504090b0f030d031b020a020108190b09071e110d0e01050d05040501090201 69
    0x796400b50f454080080441c00d0540c404035000e80300d51340c52701000103000c0005c20005540c0c03059020f24104202d4584105810740500403200603c0841c080750f120341961304244149002041c015610411468074040400c80294016440208410395860301c0803c0c121401c002007004000b4a03c0781408100c0d8800100c003240000781680c0f04030314801c0103000d46807a050042d2904041c8807a25440c020201e0b00016280003c80d2005100c0b00c82520841e106202c3d81c070340a080302450030001400b000041c0c114901f2080c800c0e0141a010030b45c140018025503580c0e5102c484501c0c00a01140701c4201160b00013854805081c0c0c0d034500081d21010340b55040000215134904540050008103a00c90b0f00c0c0c1e00182100c0c100401303801c14251010003101c101c2003a5040454002d1011b400b0701070754104400001d00c4240350380701506ca24019060000c45552144860710000300000d8041c2502500b07401e41240d107105558107160400001340031007102c00101c0d105260180d417007440005003414642c030001d0080c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 114358633 1250 114357383 114357389
    0xa050714030102130e100e01060c060b030a02090711030f03090f010615050d0506060d05040f0b13050303061504050310020c01060501090303050702040b0a12030806090c0304031e0c08070b0709 84
    0x199005020007100c3c2c0900040142c184c948105d50130b081581c079070100050310100d41c1c0c0a0264004890b0000405035000074035880c0381da001c6e80c41800001d0220040c1a542e84070118000c0d00f04040e100003c4145208205440740d800303070300c0262440c020701500d280f221504261400240d5400400000d04421400d10810000b80709003e024016160103450151090250400480b90551201b0002e611a0349400840b0f1444c20f03958010055401d19007826074203012514008c40d10b40800c80c010802c41420b44070034210b9250300070019451b581e1034500b40b201e00c180045c550500003900340000b284a0303800f8440201500400140140c407052500040360075280305510075414010302c8130080c40420740c071408541209405407004100c0d1801803021484208483e03102003264203000039035504143d0f100100b14001e003021079003407620351526090440725100030341d80103012800800b407040c6012090a00d1004004103400c2011890030300303865000b10360380170b5041100c00800d054100140c0c0c0307410141c11009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 114359883 1250 114358633 114358639
    0xf0106020105191a0d0602070201120509030703030e0115120b070509010f0e0a03020a1202030c04051612060b040303030507180302010e01030f18050705031203070f030507110a050714 80
    0x102e420045154034280e0702c030303841c401c0701d441c0c8400c2002183c1c00c050340303400c01c41900600428290140b070308183c8000c0d00164400c900048100d54115486c101500a1034054140a1301452508856a80560050440076036006036952150708600c00720503112a40d1004040d543c04c0382460118918029401d50b0008029406012040c4246500c07a42d0001807011098070b10f0400001e40442500001d91040380c030741c0001e40c00b0044280105034150740005820781c10b032007070b0101c4101103000c0e402c1100f07849044810111008041d280e5041c8a40710b41004218103107040000110b568881560004560150b001980403c0d2128180501140d0101c1890703565420700d400e10180a04560008100a042010305810152543d141e0505110282d10001d640200c122045c43c4048403482c041c0d4030768949110340f42c800d015600c082c80d03c210700a0110781c0b08082c29651200e1001600714250010003000c0c0c04001040036114425a00503001c02020241a01a070300800030035142c03c07000000f60f0642614540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 114361133 1250 114359883 114359891
    0x100203070c03080414060a0c0201060902090f04090c0e01082b08010e070e04151a04141009082a01050a0504090c21020301080c12030702130b03010c080f01060201 71
    0x1a03640d010084005040d894a840c0d00c582d00c0b1801e0625030680c0c40e160050481c000c1d401400803841c46c42d40144c201402c990024842940d503070908a040340250560b854000d40c100d00c10285518096120030b455038421518001f04903100c1c080c4200e07151090700140030650010b40c000c40c0343d01d9541042e050404900c0ca04600a030600d560052000c0e0041c072400c1c40c1d221041c804503010130300a8001d901c4c0160090001c01c41c24462100030f80700d220b524445c0806d4011440d92100303841c0e04440447d804c0d00c04100220300d8400307240d001c0c810201031010210003007001494003c038800c0700500c6003000d6801d00c4150421000c0000b0350840e29001865402810b000d01048990446504941610119a481040091803044c1550140e4507010304c00300350b9140100b40101203800500f290302850580d45110308640450b4464010702c1034182100c8550740040d44180704107401481c000304900100b90a02e01c1c082500a403010102c3d00750307070389505140085892401000380c035054045a80340184103520082c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 114362383 1250 114361133 114361141
    0x70317070906082202040e070503011e05010608071e0e040c080906060604060e0f031203011d0a02040b121308040f05011e080f090c031002041e03030e010c110301060303020f100203 79
    0x41e061100b000c4d0b00034052034a07201e903019000b01c28003200c0020325003c0c0c0244641c02081c0c0aa11025001000c0c66402904c0c043c004102244500300a52054505854a09845800c11003040300303013054100c1082048428202c1d8003040e103d0b805140d041c4485500c0b19600703814459101403e042000705024002e01e010b200030414140c1c0070120000d41c2074252044103090106c00042400c11094854003103045000000000c0d0441014a01000031903104401c0c00650302c0f1052400300340e214610455a0001e0b0501031451200741c940701c243c0d000400030700000d4494500fa59242d07000c0d040741c0d0180280c40b9000e241040720b542c1100c51044010900d10329003503040b4035413602074807140c006811580000d4031080001c007000f108026040d0345c542c00400321400102c003440204042d5100b40501c00c019103800c2e0184861101c8030f2005400c1c1ca40c143c90760200d101c0e0079001110260400380040e180b04c1030b5200b90320130380d88082c45140302860181d4090108001e8114043c2e1410300041e00340c003401c5104000304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 114363633 1250 114362383 114362431
    0x20304060e0c130f1103090307260d020a050c0105010b09030c03120d0b12060f01060906020c010c030503060a0b19171005090c2205090915060607031707090608 70
    0x1c030516024071200013940800201039000141503401a0785042c00300007091010001000014009076841030210302c1c000320300c0700c45203030071102c052441d4041e8040500c090032100440340c000d44440d000307a03d00356040410070b1418170709440c4207a1129803078120000d048020340c14113110100340782e0426402420551070800405105104807400308010381d40d101010191591028103440030703050141c040354480d04203803002c1811a1800c0c42040082000c030140045d10600109140b403850405840740341d10b800311602d003130700c03540d20003811030317070700a40154011a14401c0000545000c118042114040c0e00b00380001806203100070384112080e40807941006129a00f40007020700b954025500018030351a03804c500c0f0170b00c0c006d01c02003c881000d4040d07183d40000c000070f862011900300322440045c0b0f80f1803954681d243c110701c01400c00440c50880000b034444c00d06400600300c4511910308a012081415070880c000300c02580c501c2d00182265608200496101d0303029500083c061030b0720000b800c001614 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 114364883 1250 114363633 114363649
    0x30610090f060f12020a030813050406090e03030f070201152904030c090c050403021807140306010504061b06090302030a03050a0b090402010c02040f0e010209041407020a081b01020409020304060e0c 87
    0x2032a103082c1d08130640e40b000c6403111440400215802084103071141058200000000214010305000d40d16040c80060000a40d028805041d2040c0000c0d500d075883d0384010300e4451100038040002d42d0f40b01c40c29045412245070601008182c21280b0601060f042400443c0498a4000380610490f0a04c01440851740754120304084841007a0700003019548038400380c41c02d00469002a5001d26815000c05200544e094071034400c1525a50b05400d103021020148035501003601c0080c0024000d01040c41602d020b040b0000e90800c0103010706080d0119560307a04181c840220b0200c0041c1c002141c0c00f803556405000d02508010080d00c01c1c45403070420310200c0d5080e540104047c0c10402082c58540c20754036694840140320492800520104038405400d43c080e500c55000c06009034608050504084080403406000380400c2d8003400395000030f611002000c1c0c210f5121a4440f0b0010481c0c617000550910042004000103440035031249800c1c10318204a03002c0d0150620107401400140d00c10342e45981c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 114366133 1250 114364883 114364889
    0x70204051e060d060f02041203030b0901030b180a05030c0c03060f070c0803060d060614011805030d03052701051b2110030f1b080d0c0f020f030610090f060f 69
    0x25041c0f142c6100d410410041c01508030148001840003402040305a10081500e022a000351400d000c0036000c0c034180714402c082484060046100d00d008500b06880c070086001075072554a04803182c06885840303a600710780c02000144140c3c1e101c104a4415400c00b0b1211662102080514844038641103401a010100d040d00c028520800000020083ea54002d0418400b940104c810030905448614503081d018100e55010301103051083c500c920140c245014000f504c4002d070190a0019103234409a0180c980075000d0b03002400307250340d1903c2c0d1550204a59060342c0441e00046070500f0400300f000362a00d050035900c100507070304209100782e04035841c050403055824001c80c4415030340d5201c0b03c03416041403a04014030060b1100c030b140050111007110744032a43e01071030310300c20415510b0403074594424840e00b2880c040381c1610700003004120f8444403070040c20b00141000c0d60440304035000030b0401001320b9600056525001c41800341221070706c1840d4440380e01d9034007001610f003010400e140c02d00c0144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 114367383 1250 114366133 114366139
    0x5070305091c1505040b0916090b04020708070503130905150d020f060c031b190b0c090607050a0b06010305090a080c1c050a1b0213020304020a050a0b070204051e06 72
    0x60780d00b03544502151100503401d41c001c150840424920f0a00601405080d07030151000e02e90440460703004200071070001c10716821119840351191070200c20700090440c840f072032688141d0a001180105503080003d0240c5d038480c0c13000c4d69480001c90659144d528940d0015540315242808200f00f10001901041c1d040600720341080300788160788000384d200c2c1c100c038908940040c80440c2c070074200540080501040c652043c2d620103142a05000390b6542e074449030482220342050454403012a814002036900040001a03051815800c640840c3e45030307011010807200303a48124168000d10000c0c04015401460900c1c0074811402c180642070798440c88080d028101800025110310180030420031000301d02400b850040c8041200e44c40a01030f60020210280401c01d45041038064015660062102550061001500040d0242410025000240304a030030090502e40816640d840000305001006103442e0155140d20b148107120036650b000c4c10305e403424004501e0181c1000c0f041e112141e4040015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 114368633 1250 114367383 114367399
    0x81b04050f03010905030d0e061302010917101509140f2404060e040c0f0806010b0a030b030a0c06120b060d0c090f030c0f0b03070206071d0301050a0501030b01060507030509 76
    0x2180002c2d0040c0f03070110f4000d145200c00103205111a2440e040080010b00c03510a42d04140e40300b0400d5060010318603070003800900c030b141040c001000b0800401400c0c000d2102101c0d0804101300c020700840e10821192190490354141c01c000300c59040c050700c0b09101ca201c02d082d2050510800304000014054120303046160b80c407841580c240f40314010764803408001041031103100e95804200d0000b4000f59800d0300c40e03022103480070803200d40d1031080e1811a441c180050007aa842c1c44032140203500b11051200c00c2640701c8040314040c2e40c3c10080741d0443d0f40a1b402d034619032440e14102808014008032107203525070900c0c804460540d2400c00380d40c6034003010000403030301081100c1b0072a4000c901e07401014500c102481d010040c032451900040a469100041d07404842c0c50309080c038040d020490300d500042c0e02000016200c14811686806c403652440c500c1d02103540c2da5030009003560800c0325101800c60b541d00041046c802400c014074014040c40c20090710b0001c01d628010305a00c22a10010b01072014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 114369883 1250 114368633 114368659
    0x403060e0109120806130908070614100509190e071415120c070f03020604060b01050c0c010e03070807080102030a2a0c050c0d0305090a090b010c022206080d081b0405 73
    0x2920b1b0b150b030078068122400c010314600307403074030008039080600180ea46510300100340420074491641c00c1c4c011005040351036030741031070001004101d8100400b680da6503880301d1101149403005001c0c060f4405000000340c40400d040c400c0c402d98000482c044141326408801c0004280c2c0c1e07000046942c01003210105c800c813943c440050f10410312891800a2a185501212900303060740814480d0180f440b0701800c0c481c081e00710b4011900c501a1003a0a5110340107544400543c1d0b004410f04d92000c8000707410746110559855100e42804451307413140031240d40010410034200e196208000e5501c4c081e440c0c80e000d41c03401006501e02c403c03030490f207042489805615903042c8541000001d03144200209041400c8540d4175004100d40c1100741c009000c0c24a072800442c0440403070017103181c0d001c8181c0d1036041c0309220b80c08100304016102c0c1c884501801000b003c141071800e60081e200900036120007402020002c490043c01444010640c0715201e049400300700400c02a0000c640031241c00715021011450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 114371133 1250 114369883 114369889
    0x605120603030c0f2503080a03020912030a17010807030804150302070b1017010e030f0706021207020f120903030d020702011806030e071d0406050702120703050403060e0109120806 79
    0x1040903c00000b611461304071003401140041c2640b030801240034403c00c101314000040b9004041400000d10064041c08029080c034400e6000d81003140d4024813200c081c4000c0300d021801c50b172050744050000f0703404c02c58414035405001021401004001c0061001c140f640c0c40f0401d650007280207810401400600b000802c500c40d4041e40c030b10741c0c2c0041460340c0c281841281039604900e10b10a6141c2c0c81c7e4542d42c0e0800303204040c4241400c030a8140007440c6031050b460514076450780f01c00301c110b4034140e09002104103030b003600003030f544948480d400406840308540d11071484d0800300a01c0d001a403404000c90100c41d00c010081d1000c18459100244c0c1340c02040c070059840c07064240e540189980d00c280c4c0019500d5054008100e415285002d881210340c0b41c2584031b156045043c50162403140c688041b400050711640019480b90051060364144109402880907e6204150640c00128085814411f01141c2d10928101d0801a00208041240c0b07a4407201100902e01c00c107002d0048810004d2002c0e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 114372383 1250 114371133 114371137
    0x180b010e0921030610110a060b12010218040b090112080d29010908010b031f090203060108010b01120c02151b0408070906050f150f040e09030a0806030304060512060303 74
    0x1c9801180302c1d98a4850000301c0695030002c9900703901c21001540303411103290048001017502e01c400c1000c2e01c54401145c6520b80500411134a1301d80114840c0990b404d000030a1028210766660000143d0708451454104410780c4c003240303076451080003a9001002071822034510341c903880350300901d20340c2c86040422503000240324820400d6000c40f0040000c01d4490100138038840d0700b80c000d80301c0c240c0b4251110340c0c1c2404ca81d00000c000740c25512881110124a4a114071300811140846001c240c0c8012540828103040f000c1c0d0014000e42c1d10f0310022186580c00030368500c80d01e030800300c08000340a84150002d45c4e41a002d50500c0b92442741d180401d02400c03c061034030350511604140e469440f940c81000179910384103482460b00603840e015000ca110724107884404207128000303190801aa0080010722015442400b0410f61130508010000b82e603134804101c40e1042014002030342d140c110069000d0085140101034900c84d4004000c288412500321007a15044110051010754540c0c640c1c020034618 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 114373633 1250 114372383 114372403
    0x60b090612071206031a0901060f1707080d020303070e22020a020a0506011e09020a0801030210090503010f0f050a0603081602011107080601060f0c020a090203060d060e06060301180b010e09 83
    0x100e007001ea012090181c800c4040d5241b1b801003030107645540e52083c0d04c078225202030190881e0300b8003d070010040c042420403c148846008400e81b003185980d00c1c61549001e1040801e03a02607000802041922900a0341e4900498000e58015090103500c9405607444800c0340602d0704065408603010610500c200440403100d5440811134006586810f01d010720f082816403501e14503000d43d0004a2280b05500966010000545405003145d00f16401c0003030311100155500100b2505640c0003600382c1d030034000c1540f10014071100084200c552419801501c00040004e00c0d240d061400c00c2000640010440e4020aa04585021203007900d02c012130b6170582a0a00324a1841414004076030038102090050407070b5080d807a080807900c0c0c0c07500287c6a814644501030f50141c99050308014812050f001160b105c170005182c0c1040c880141e0b0358208407025500c1c16030a540c010310401007182403d11402a00e0820452250010032940e41d4051807110140900c1508031a50720100c0c100300d60812000c2c04c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 114374883 1250 114373633 114373667
    0x6051c0305090405181f0b040e0c090921040312030b0312160503120702060106090807090504150e0f0105061c060c091a0a090b030c031501050c030c0a020301060b09061207 75
    0x61074019000306c108498000e007804056280072400080e511b0207205a10a000e030450140908070300e004100710302c1c010300402004442c010020350607010640220104404a098a0002d0301c1d0307821420070345032441580066105051a0100c841602e03a03000408244c0742031040c01705545e0f0f050400700c4030b141c1c0d0b00b0002c0041c0316110114039524954003107006240300300b0155003184c00036a070f50bc504981484551107041c0b2a40c019400510441100341c0055502a004030f060140c10b1284240c01400c403101c002100d49907800003680d401c00020203009090f082403003169902420000f02070140c0c424011030360020141d980e190b151419290140700244010401d8200034200b00004580100ec3e40d03110305a05030025043c404049150000041aa8000c1840507881c90460399426034584a048940040a05001c01408541900c5001f00020413640380301d50003429241c0450310615081d50455001039500203400c1c86480c4841d00c0d0710003507070b034082c0011031602ea50352113050007a034404040c0110480c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 114376133 1250 114374883 114374893
    0xb0a270206190203041e052416081201090e0c060d1808130902031302010c03170108010e1c050f0a032304030206090a030801050409031707020106051c030509040518 72
    0x103002c2c0c1c010018004503082204c014100c0d00e5070751101d00ca2517a05024031076200c4072050120080002c460f95140f403841d14a04030390720382800411070300003884604004039155540007801448140c1c03003498090045c204100148400070300d1643d600c3d2110030070048140240d1010807400e8141966402c05091031001c0c0c03082c04c400c04641c0c01d284642e54800032004524140584000411070b60328070860f4807030120101024411012030b401160661710041e03040d01085006661040341a0400034018000c00000c03000089203120040314608181107a4a00e40803644841a074440c4980c00c5421200035070026480a55200c4500c40258000d00f002840300d81500c1280321074012210704940341b1809103000c2e40071030706983e8444c040265030310f80b074084c02000628004010800341c00d2a4201078203075442414407034800c25002d2200840950112030038001030391540801c1003941460003000302031030b82001106828200503140a40b5a1041c0080b550203141d0701c00000d0412010801c0b615400e6102e1070540d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 114377383 1250 114376133 114376177
    0x61209081b19050c01080a0b040f050907091e1d0d0c020406051c0b06030307080316270b0a031805060609070918050c090d030305040b0a270206 63
    0xc038007848040380c508060311a540d103118030702d182510031121080d8003600400040c00781200455030040041c208005035034071462043e4041c0e88500a0010728125914009400e14203000d0b0585442c00c517901038140907141024480388140d104003805120036405501140001d030f19101000c0c08820221401c105008035140d6407034142d84004075001e9280211001c1c458942c0758010072140d11221031003051480c60320031000c00000c44090200d80d008100505890a142230b545a078150f59100b10342055010b054500708482c25908101001428840c4045400c417444400c2e1800c00f2141d5140207450340120f02091511045200e900184580c900074000200c00f14090315105680e5241070f281e492060012400003a50755115200a030704407210380b040004614234003140d04005050203040440e40c84030401c010001500d580780c54a525520a680c009464030b02814044034021000e0f1988450a0401e80d0003017007249418407517400300301108080350754841c0701c0c03000400038413900c211030f807803640c200d0b00314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 114378633 1250 114377383 114377407
    0x80429010b09100503060609010c03020f0304030f1a09030d0b0307051203070b2a0c120c07080106080d0f0809070816051903080406080a09060510030311070e0106120908 74
    0x6020b104105a80c940b05880b8203901c240c9030780c0411510240c0080c000c0c4001e490307940c8920401c00c281d0b400390042e5124008160509801c0d0b500c41e0b007081da004601d408000c820030a09820150000103403011060080c18130404a0740c480c850381400329100703a1640074660f010b0350b081c85813400603c4000d01e05072403c0740041d071f560b850ba001144144ca10340300c10800107468020425103019007001c00180c8a1101d94200340c40b008680280b000701401d44540907075081e0f840c4141008010490311f1100602d18985801409400c1d81d80b5034200107900c5e08030b0713500540c1c40c68228170380d00030441307107401c0032400c5a9030410560f241c0300081d03120050034802c01002240810a455048041d00c1003500c0303540740400403c00f481d407100070a06c001000350304100300030050288554045900300d0869840481c5120b410f456010580b1015107860f40900c0c0307848010410150090082d10482010001070403c4624204110261150520a000038482405106107118280d40d020707821031035002200c961603203496100307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 114379883 1250 114378633 114378637
    0x1f0510030b10030c051611040504080903251404090b0406050711120d0203060a030611090418110609011106010e07020601060203030c030105060d29041b080429010b 72
    0x480740100d500301c5100d0542c0d4070070700440d0103000c050303110b00d40380142d1a550445600642c0e03405450f004144540d000d52070341e45020329402079001e003011a07150b060260030181001540e4659482000031010481c101c003203000ca42804558254211071040e1032a2404079000d820418801005442400100810482e0543c819070044d042c65660000110b80c441140da0b84000c0c881c01031681940500c00a011115650021540210040c054100d80f681d2075882005a810030702c46009801004921030146081c14403480c103d0020309580c1d0a140e0f4055114140e605400d00310850268000140d40711050f401042c5c0701c8510395100e8102c40007981c1d80d0042ca100c42400f03407030410050140c3c0e000000c0441c8000151b07030140b20480220340c81d603481d050400245621103d283d01085448100806c03039110105030022404880e100100344030a1f1240c02c01c021208000c3c1102040c0b03840e111ba2201455010701d06940c030070360002080d001503a07a2802d480304a50144c4924000d01103a0001203020003c1d500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 114381133 1250 114379883 114379901
    0xc060606030b0102120c120a0f1b150b0303040b0414030105070804020604090902031603150c110c01030506060d0207030c05160501080f18010c2106030302061f051003 73
    0x1006425280d2208400380c4654075801070050f07201104012411500100401c0700340044012201e50040410000b2202c1d00901c1d100f60100760200f02440c4916080074400a035141c0322413000030b00144590314041c1420304489091552030381c0d11703003429440e201082124041c5c01c2d10402c0c0c42e2038543d51342c00e036243c0e0070300000c2c168000d500f424040350590b4060b070481405a9401403640c7d080508000d03407407004049120051b40c5c035210709910111038030079009200d40914050070284400c070580c000d99030165100800d8000402c6482d00301c2000e161000b0a15580c1c860091a0204090315040f000032510701031500b1b10b0080910000d00501019004400031502c244144150342d1031103007000c1000740504072071050b180403c00ba5000134040040c254125a403143d40848407598181c0340300160303402c580303081030000003141210f803002c841d0001000754002486c601c40001c1c0503041c21950001d494540c013038044203a00d0b0300880581983d550107122400a0000500756440d40740301e0060060203406858 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 114382383 1250 114381133 114381143
    0x3040b0703020c0303090604052716021b030303071103040902040b0702010807030608060f06010c0b10050f060c10020a05040905070c0311010203061809150f0106020f06012916030c 79
    0x3e040040c1c0750030007109444e083c003002080f60f401c140c680001c6c04941c483d500351512020200360560002d800300061002d00801404103500e10080724107101130f14020307043d0026210700240c2c84104a05550000c12250b01c2020703440e20301c0391104c5884901d0714501803600f281d4a42d5001143c00729040e00400b010b0310341c0324002d0b615800180c688030390980407120203005054158000038002004150b02c4c80066030401c5042c9000000b203207483d2114170320302c0c1c4103450900d00303601456000c03c59480d046c0701c0c1d4200b220080310368074a440b40000c1420340c1c400d21820b0403a5042d030041807450105004a080e28020040c1480a2000785003059009019840030b180480c04039030b00e0068608820014400d491241e900600360480c44000c03101c00384040540244690b1003482540981144003441a40070b5010b0b50b11402e00c0c078a15410300f00040d05282c8202c1d0904001d51141004010b840000016080441c4020189000c040150544416a8400c2d82c8520400780403a900b090704055200d80c0d001c40190080c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 114383633 1250 114382383 114382393
    0x12010203070810031505070507060e010c0201050703140a0b03070e0a32070e04060803040905090c01020a0c14180702030d0b010e0a210507260109030f080a060803040b070302 76
    0x2a0300c041c3d2040307100d02026104000040380c0c841c4501956100765080105420702c0745c10080030740c1d40e0b601520303012140e484240e51180c07c1e0003e003a0f0240291504550b0f1800c0500940c4c4100c0800e0b01900700c018081403030f40342c0720800b0304001d80b000d2292001070086440a1340441c5031070030400e00a0324030032005c0301e603100c4081d504a5040c000e44002c14401c403603400d00c00c4071031f88a01c50211010000243e00c554415620040007981c0042080104010030328900d0200303030b600d0000805414800b82e0b90040781950884120701d0009515010301d0802d4888800c00d4000c81c8a201d0701140305a000300c0b1150701c22803020b070148800940c00101409075200303004030a00042c0c00210045403d8030b0f44084442e08003040d50018003404007a2443ea09140c155200300c7c1004103c19100ea515203045980807031856800351141140309944940074020403854200284286d058039580141a1344002030503008100c100800304a0f501c407260404001406040c0031241c90355119406109107074014501107016110f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 114384883 1250 114383633 114383641
    0x80301060e0d0b0106050d1b1706060325020c1905090a09200102010b040501060906080108030301060f05030402010203090901031514090a02040e101401090e060f0a1505120102030708 80
    0x2c04500000c0003940080b01e41401d91030110141c6c2e0303075007088007207014075500d4a10b905c200d0785070580002c50301070030740d9245034416242e00c0d0321108070400581110301a181c00c00070440c08050185054440d0b10303403800080441500000e0403824049820055075101000380070045034190b24a462906455048070100403e4a170511828201e40304100010031454150918065102c0c020b00112307000e541c180000300d107410051000400302c03202600a100410b22289050000c1e0358400c1c1000d02400011004524550401d100074140015844400082000010008045910a10645005481c05051300401c2e507120b2411004045007215501001460039849040c034044461b000b501074191080589400b00300d42c1c09000240c12a481303141268030440401040303100c4103104041d801d03c00318040080c00d50404140205840c4208449036540c0c0c000d00a001c0340980b4400c49075080848030324000750f000c4c00b0602c541c45d0b207001a40103e9020b10500c44268028a064004500c154419500d082c003e82d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 114386133 1250 114384883 114384889
    0xa09060305040506060f0109050406081606020f0c0f01030e0109050106031205090f150f03090f0c041b0c0507090906091a0708010b0f0d050702011e05061815030a080301060e 76
    0x701c0d805420f030b03070004001c513415080c02e907409000000c0626091028646810200742a0b03032156010341c08590120740350444150401402401800b582d2003d425402c20046059a489400143c02d51040044807003001e43c40c0e000e54002440208810000d10188606040090003055a4481038855007000c207203410307030310b0702c00c508480c00044010054114000780a00388620f000d0842c044598403001006010401c80410019502c02c283d204010302050064250703260818411100503409142002000a401d00351011a2028040f4601e40216101d42a00f401468038110358400c01840c2d181040503001c1c05015081000c0c024010ba401840c2c03601d812140920902c000c45001e4006801400184051110103005060110000e548141401842c41d04481121401d817540750150703540301c228034600105554603404182c1060000c0203d450300c0c034045582c400300114a40d105c0510072001400a00451245501000000d0b04550040c58030b480c28544a602c00c1c010000403a07102040406546 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 114387383 1250 114386133 114386141
    0x3030403080a110d09080c071e0b1908131506140603070206011a12130203010c030b0109140402271c02011205071b031211040302030a080304030210110a090603 70
    0x80c1d140c0e1901484c08031014400c8004025001c42103520f00c0c010000c0030742144c0c00708417100103469130b202c507282240c10106040071004000d40c815013010400b480f201034858860710355008642ca50703003040d203884e5446a000e404461569100104803001028803500c1f0256142d0040d4140d49034107800b00740c4000050b0410070203000031982540181d12080046c4104071254000d205d0340c0d01401449800c20000c2c040108241908840342102d014942d409501075240901440b0003152284c101081899200d1000810044007400b41d20088501003031003130400d8656904032541408045007074004070080e101c00d030340750104410780940b15030500d4520900300726045040119665058460040c001c4103a500304016080c000c1416050001d194482c60840741c2c1c0708840769440d07100b5a03901e01c0d9121141a1001101c441d038203025241c00040c4020320068400142010300207400050642c0c42c0e5460303160407403230800140c03141004d05d0704006503030114a900802901030448240c0780d1200c050b4036100c0c200c0c101c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 114388489 1106 114387383 114387401
    0x20a02060615090d02010e12010f020405030705090c0a18031505060109090b03210c070902070303050109022506061703070b070905030a081c060803030403080a 70
    0x1502c0d1105542c440010300048880c00c1c541000003284282d409000c00906104154214841550302e101c0300c0742010352080300a02000015180c0d4001a412a100da980207204526020800b445c1c0034120364410f4807540382d29410030803401012602d09250501c013682850101a011003c604502521000e007980401c0105050a1200006040400940c0301d23a036418540403000380156004144009202020004c10b100500640d402080c03a108000e05211144903030301000581d00c1c0140c024240d6a4000d8030700300705680e65583c10000380e2258170f200c0101a001c00400d0f8554100e43c094003014640107510009040380c58048000700c520503852905100c0c1e0003c00d1030030810281d012201d40c480c00d18a8007050f080c1c60840441c1d65016040401416181c0104500c001c4080c5040003082c07c0119450a0225581e22554513850354020740d01a4001103200c000519541000d000c0e101e01e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 114208633 114388489 := by
  have h0 := BRFrame.cov_init 114208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 114208633 ≤ n) (h2 : n < 114388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
