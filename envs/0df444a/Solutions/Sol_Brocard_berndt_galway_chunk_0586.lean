-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0586
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:35:46.516014+00:00
-- url     : https://prove2.me/submissions/5b0e363e-3b39-47dc-8041-dfb09cb1c426

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 105215827 ≤ n < 105395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 105217077 1250 105215827 105215833
    0x807060c1505061c030c0b061f08100510080f16090b1c020a08010810061206020a02070b04080109030305100501020a140a080d050603011b050a0c03020c040e010204060207060f02 78
    0x5008940c0c002e1400421080c3c102e002542c0710220144e06140542c151442511765501d50003003030070151035050005100501507400b45405644e42d000e500000011030344145061035460f920400d4400da1200c25a211076008010f141a0085c0c050708012003510039841000f2540ca190764a1400c60b020340d0700301c00740d000401c500c2c0f00e041c8864448440200341c54905401085248c1c5074600d40e1404076800701561f0000680c00c5001401a003034140004105940c06050074810b9a043c2041400d8509102304001d19050740041d0b20101a4020710904000300164a001a180c035510a10302d130280103112411400245050700081050002400352016500e040e40240728001d041c0e659100c0c0815152401c0b0340074030030f1540350800a2210402080144038010000c101c0c1e00709070b014542540c1c0454643e0300e414150b0b480c002e241c1540503040d102815140d1170440c403114254241a030801da551543c564015041080c62400554150020000c5031030b1942110500c45d40c598045923294070118049005030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 105218327 1250 105217077 105217103
    0x2041a0d0c230a110601090915050402060d1d060f100503010e100504050709020f190c020904021509190f08210f09061b010b041107021c0b0906010807060c 68
    0x70b9580009001224050706107031005070900e42c2e600d85866000d030702014407030343c88561160170090604920380260100500902c1203040c2a400107200c3d000c0c2c010b020506643c0c8006580d4002c56200b0840c084188080c141c40d0369003030003401c148821a00b114811074401c510500060035040500c103081182500401800440c00c46002000140c40050802e03100c5218141e00400c503440c0c00d00c0100f92101d0b01000643e03440d06001c1154405020442c241402c0c0151084540003603124081c01c0365100ba0f0451707801498000c500c0380440300d4051010301c1a00103241c0d40b203030f000c4204205060001d6620800400304025a5a010555995505903c00720030a40c04900111a44892000380040100302950a0304081102000c10203c1d0400b03150050025140e0740c48c1c810041c000e128441019030252803d001901c40a4544280c43c840d03000700a00400050212000e02c081600c20b031028258040d1210441d820020b443c96500c490038050050b40c0d02610030700007481d030302500c200c80d511540300c6c0003c40f80c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 105219577 1250 105218327 105218387
    0x30e0304031707030309120807030f0501080604060c020709090305040801110403081b1c18080706020c13020f03010f031103010b0108060f0d02060307032903190602041a0d0c 76
    0x15040004200e09051b01c4607440f2000800207940990801100d503924403161520b150300078203803401d05407207402491070640107001400012034510362290b0010700108080d02c208904a1802c0d000e68800e441c1545840c21b840d00300350b8840020002c90301110003d000e0803000751321402c2c113440395120042c1407800c20071456224a00702c0408640b05170f074000a0300c00f4102e409080180c0c49218410b0b00000400e49451807004804a40c02c0344003400e080c60003441480c0c00e01801968078804046454400c4e211a03000304480c0c1020707011141f82402154a01c2d0b00da5960300781082003000f00303010071101c1c060f01003c4101d485c201481540c0c00300700b0503034401002d51204801c0c4044030308a01c0240b90000c440070b60050140e201c10000f14019001540d00041c0c201110f0302065454103c03070b103100480c2c0100140d040d10b17590006800300f043c0ca1201c1c0c010f00e2500e2603143c510300074411030740300309140d420700310b5117110210010000d0400c0a00e048428420b68072102c508039241038104028140d020445d10010b0382c2c2c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 105220827 1250 105219577 105219623
    0x9051c0f080409090303020d0e0601030804090213080714090a02030c070b04050c0315160c05150c0c0106030308040c06030203100b092101151e1503020d0912030e030403 74
    0x203081c0c09440310034034140d210b031403403c10f032440c4c41c07404d030042600094081c10707070f0040d40310741040c0341da141010f4101e40d41160b452840c20704c143c0c4a5050341603000f20780c00261144541c690b00041a0007002c0b162080e5030780403503101d0043c110307000d184a15003c500003244003055001301e0303200700c0d81500024544007080c0c0d00c03c40200d030080c0c000c2c0c0301ca1280071050a0300d9201082080b042200140d98503a8902e000c86248104c0202c0031205010080300b418180d002540005006400c01d650040c40000c603a1000c020702464020176603030001543c20004000145500800c8a9014034010854812400c1d21404e09030f06a21041e50350840c10f0a844504001d140710000243c1180c0400826524550010b00d40d28160411201e00940003a5500e10036180f420282a008900809080340b5004c1c40074980040004004014443d082c1012102d0300d600c070312070f440303541100e800f00c803800d0081100e40c5583c241221406512400800403d1030b010b200710040200100b40d400301c1e83c1c40443c0c1039004a08421841d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 105222077 1250 105220827 105220853
    0x618150d0c09091a1003031d1203040b120a060303020a0f060213080105060a1202090f040816050c0102100209060d02090d0204050c0703030c08060108041101020a0803011509051c 78
    0x40d16224409010071024090300891a180f0300840103c103100588103000d260303135a0058035200300000506002c1001980007101d03d60031154403d155021111401c010854041d244e000c10b040c14080080c0200d1080c0d0050090041246030750b032455801e648400d49141160038070700010300982c1c02464152300241507440e00825480c4100b0b005420701000f0a003407542441e29410408a594580042140500309014030100030800107101c40700404258020520078800074004880c88920f42c400035040c00104811508001014205001003040070f040c110b440310810702202c0e00502031400c14920041e1140262801000010b2080f443c00c0c4160f10000c000750300140b101500202040140030250f40d42d84101781c4038400446005580b003059150080440b0340c000001d1050040300c00a02c5481d907030014205a000e48d0181c5000300c0b07200440c00603441c1c80111040104024800800800c01c90300c2d004043c2e481d01020f40302d00090359201c03410090020030790f0400c110813410760042c103000b0a00c6461284 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 105223327 1250 105222077 105222083
    0x1701030b0f1b03070e0102010f050f0f09030702031002071e03020607030e0c0a080601030b0703140a020f0706050a0b01090b0414091b030405030a09170c0603091e060618150d 76
    0xc4540007400c01c242c4140c1084807001c01140403800e903e80d2a5070217005020031b401032444100241e15210002401c4510b0103090520604020300000c1c100503010004c450007560010201e401d01700d0004401c601035801803d00701c40c2040040c0d200a54031440080041038941e1680207401c1c2c80d50390860880040c560443c06007024458401d070100d250b12514500005080304d06c004c3d0609604604242c002007401030410300401d45410b40705406443d01a40d226000081c140000d42d40d007207221543c60380d5004010014245a140c001404001550342d031000e28000c00070f07220802069952000f0351840c0c0168454045612481f8050184a24000c1c80f4548c1c4683d42590f4403c1d03151040c410424182c2086800b224594000508035404680143c9100d0003400850030403025007001e40e80755510b030468151114003400e0f000c80401c09004040c00390038002c0302210742000d00c10001d910a665584d40985555004100740903140c1002c40c40c40c4150382c4150003503021203d502d9160300a12078540741804040d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 105224577 1250 105223327 105223351
    0x2032701032301031202030c030a080601030603020402030a0903020c0d050304030b040302070305120901230d050a1d0105040618120806040204150e0a0501050a0c110a090c0f1701030b0f 81
    0x11800c0c00c050940c40070004034000350342000b99815482d0801c200c110030152042994002c0c040000301c4a4000200c4414a4480c940100309458110040c1c1c003500320340d000294010f00110400124803070f10383c0012466401399080f150003c10f18418040407080c0c014015000d50000c00c400d001040c910079186030420701c28811034403450760703d80340c2e141400380310005001040c134002910a102d41e80074090104900c0440000800804080c14a031070602c0b0350200005003c1c4c8403000585408425840713000780320072410014090115202006008050440d4102d0300985040800c1c10200c629482444060b030f4002c0002c008444800740c10307903100400500070b0750b21035020040131482850008415180c0501c030b0300c0d682c451051050030000071184a41082d810010107000c801c0d135282d4000003100d105901b10603240400c012000100d01d080a9503040320b200c0d1810101d40d0b440040c1d00140401103d1036640e40d40301909100d0605564410084c400a0000d0141d0804120711003200301c03200e50040c44a0400c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 105225827 1250 105224577 105224591
    0x1031b1e0b030903041a0d1b080103030e01020f01060603150f050306040305030a0e030412020906010c08090d0c05060c0717010911121c02030a090b040b030723041e060203270103 78
    0x50704c1b824041d480c954250801c400311b02c40003d80d40c1d501640400d10000c4202c80c0400b602514020083c000c14032000c0c0800015447e0a9003a9000b804445240301074640203201340340d111711018010348010404400300c280c03620b000180d49986240c1d08819035000074050801c40c1c4613501e003120f45400140400318560303510341040d11f0594081000303000130424081001000c003064010803c4003c001060b19042c031100203010720000f0070040441c2c0300e4400880d910091a21642008800110749130009904548000f07041c9107203840c00500c0c00d044032180c08070090040000c4400a01f40c407a000002015181984c84000d07c502d4000c204d000d040212008a846101409110703280301d05180001e80d002d40c1002035a4020b055004403003101500003211014a4280b52180d588050301c0300900000401960b900403403035801d405510070400a58000742d03075403525212068041c04110121840410880400002907140c3c004000d451030b0100f414110304410819130b120f81c0c182c8a244540c1e0341056601c0358 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 105227077 1250 105225827 105225839
    0x1005070c0905090c0f06090d02041a03120c121602010e040209030109030e0301050c070515060d14010203090d0c080904050901150e040c06020109020d1401021201031b1e0b03090304 79
    0x700b0b240c42191040c00500701c90314000107000c00400301031805401450304202c0740103581c44c0c0d40480b85145506607000103d00850000070300c00b0b00c15192007554540140c1c0e0030102192000b41c00303083d002494209440c80400c1041c0c0d1450380d0311a01c60010000038011010001560082c013072032083c000058000361401c6413280c00a0f0031148804021404507840d00707804001800e00340f180c0c65003d00e41041062800c0102e40362a0344e0b558a0702c1c4200008120800014101d85034084410245a8024000300c03e807131a814170709000c1e4004441d002603c0c8141001c4018082c41111500810383d00088214034003081701040c04041e01000340540f88a40d2a0b60008041103000300c0c5580040a041e064038208d4206460104010983d5034001c1c8216810814200050790310704800610305584034190042c0b80c11358010041c003a000d07486043d030500c00301500001c2801804070b414651010382031122030000340c40703107410490511640e50040c80c800d0040014000b0080c075030021900725600004132410030b545c5107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 105228327 1250 105227077 105227081
    0x901051606090b181b0f041404030e01090b1b01110d021201050a030203030306060705150c0403020108161b0201020307020a1d07030c0c020607020121051807051005070c09 75
    0xc0c404440d03455445a2107400d0144410b08190081c074131290122084001d06541a95031381d040da03245902000e00801c240c0c06954a0300f54500140c4080c1041c000f204106e0071890450f0411501078002c21002c51004186600c5612100190303400c42c610941800c0d6040491003120440394040405590380349520052510100301500c09400351000150b82d94200c4050714014141c181c1c803860040030442d074240016640030003540d030b1101c01942e480344c80b46942d086c10b43c5040c050300766a0301147e802d40284107009004400901c25a4002e8940704110b484201d200840c01c4480c010320300c000789900200c41c2d99212100c005001480c014411a401c080140d0001406115181c0c4001c0110342c0328000d111403403440441d4642e02480c1c1d402d013000940031944024200000c0c03014001d2107801d0002d0300c0d0045a004071840400c1003040300207044100c0c2b107150300708010142a1902100388001c032202c05030300080014200140c4a001e00361030303003240d42044155180d40000c1400caa842c007641c6000f16241c0324078 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 105229577 1250 105228327 105228367
    0x103030e0d17030709090e100230062805240d0506041506020c091e090105040b060d03020307260706060f06030504020f13060b0705060402030f0303010812090105 71
    0x60a4555524208001302500011a0350f022108a41c00c1c100340b03540f004d4007c00d908002600a03400540d40324800080307682e046003041041e005041c001c2d0502401d6034004110a4450f090940c0d41c9807c0c0c511490b40441070713951184036813034417074000346040c0864280072031440242c1500c500b15905c00c0040c0e80b401c0100303070010708015402a61710030030065240f41034000c419107040c14810810b50340e418040000e4031014001c4486014461200108210600c0c41c0159a045003030b482c025981424843e180030301a0a060310195902080340001c5942403030b045415182159041d00194030780012030b9584000b600c0003001c4a0002591070302c05000c00c41d0908020710f4158481ca400103892400e0007a640082d500c0c0390030850406140a08110060711880c04505100c03200700c0b52001c402c59082140d0003d0030081d0050943c0000114042040041c0002d1490183c1d02c00ca00f41c80003442992241c90740ca00003403248000c01d920506000c0e1061280ea0002c0a0900703041c035041c0d2a00c0301e010704911742c50b619 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 105230827 1250 105229577 105229613
    0xe01020d0911010c0302030d0915060305060f01081603170c06040f0605310204060315020d1b0503072a0309140307030c05060c07031407030b1506030103030e0d 70
    0x11114000d0400010040001040b002403e1034100c254031920000c0d564021000003076906940c809441e414080d01c41e03600005034002900a00c42952246407007034442d001550f00d4a03008510034000324841202080074003080d8041003d07011350610315200c1c1103050391030107000c5038100c8013001500d12030b147c00e001207803181c0d0055103025403208141c0b6050b02120f00043c8120424420203a42070416880c4201c1da002c142d0a465011004140c2400050010081503000520211320700904002100050300540b10030721100348104200019414402401011021041c0002d0820000550031500500f0341009064039040b01007200c031081c00c0c030030807031500c410400e03404500c80034000c000141c0754881300d60050200b64080d02c2c6d20b6140d6914a0b601c0348044c010544241ea0101d1820148a8100800b400441d0850300301c00c850000c3c0100c283c1c07200d201e800150f80c00c64055001440144882500300705132040500086d14580c6140c40494440001e8101107600c515490400d50110318045841c2e0f10a0031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 105232077 1250 105230827 105230831
    0x20c07030c051008071707020f2b0302040b030105010c050f0d020604140a0b0402040509010e01020f0a02070815010302060306060d2306120601140f061b07050915040f0e01020d 77
    0xc02d001c00c004004443e0521402040108002c0084d140e0388064110704030a15429a64184e4031650011307400d003400e20182c10300502c5180310080340b90030029000807100700211100301c01200421022010b03441140141c2848200800040040d94070640c40d40071350b58002d80940b041c08400740d036210304111807908500300682c0300106100070300c600c00300c1e510384c2000ca1500800005a40da515210400c5c801040644074a507200b00080860b8400e400020003402030000842d916000c62000b1305440d046a80c501d0014070075a4000f01e0910030018407002220308148500209a28550070032040f948001c00d0150884400e10a14070104047e0040b418000d140c01d071281c0590710540d0442a5608005040c0c600c6829148d00c05038078110302152a82c1500d2140c81c4882c440b1a29101054a000d1b0030381500f50400000079013689008100d0184e107490f0010740003940c0d0425542c0c802c02400350015194506403c0c0c0c010f0b4002c00d03524140c3e0000d417064104213008240000c17415007041c2244c0080c408200419 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 105233327 1250 105232077 105232079
    0x80d060609120f020103050601050c070b1908060306040602090303120112060c03290307030b070203031b0304080f0c010609020d1d0303151011010f061401020c061c020c07030c 77
    0x80c1c0040d92038010704421000503001d1569501c42030480301110782d0203818107944001003071141c0d100d5021515506121030403100542d69414501025502c516896018500c0e0345001c4d4015a2041000324054840240184050741303c83c6c40c0d820003075002c521082e500d444200b1071044a0101e4000b42402010003c000c2c40c150389007400e0500c103580c0005180d0003010f10704144000d42c291820485080c41420010701d980080800f800b1a1a1508a4102a020420340010800f406034000011481202e010708502a0410403000d0790440c1d0205035001881c4040c05c0c0b0421403084155001742c401d00400000105085507a080501e04030383c0007403140130240337072190360306400c42c5d00b40c0b42d580080d0541038004602d0752500403940100c081191180922031001103007a12525441003040072460071605008019007034009100e20003c0c2100c0c0318043c41d02c0c0350a49900c07410741c00840d20004911014011038500020a072900e94143c007100002007045c0d6081c44030040808082001c02c003d1807040c00d0680240b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 105234577 1250 105233327 105233339
    0xa15060905041a0a180b03070b07210207090f150602010b0307060e0f040b180f0103020a140121020d060807030203060105090405030909040f1b0311060c1e0307080d06 73
    0x525506003c002d00c040050707007a254241c4a40c8400d50403148003124002d045082c803c3d0340000f83c1180c160180e49803040920100c0d1a150b17440003403005502c07488080201c2290400b1101c1c54a9840d40c0c81400750700100410060003102d80c00c03038000b01c0e0408100156100e030000c4d071340042981c42c1d0441d00040c5c0d56130b42030710300605007084910041d0009040600e24840e03d8000184d0110325141c042d4002d58840031103000c96140c00c0d640000d249072114a000b1280340889500c900c3c020301744026442040c2480d070001c0c000445014100702c8100c10382d18002c3e01c1440c680d000d00c504079001d0411803c182c0c2004901c030360100601c40d5001070030740d41d00601710041c61401010318152040e00440c1c030030307039000701800005000003048540d2900151266a001d507100d04141c1c00644458078080c0240802481e0304e021503006040c04010b4a01c00d400f0103283d086404d042c0407d44c05004203685e201c0d40400041881c00315500f00380e800021071281100d00d0f002c01907030345044a070481d0585480c115150b80080c044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 105235827 1250 105234577 105234581
    0xa0b13140a02283308060a0b0c100c020c060c07170313060f0c0c0b0d06081c1b05120a1202090a06050a090510050a1106070801030b0a1506090504 64
    0xc0c443c0b44440d059501032001d0310b103608030f0005200f01070102044403107440c80040c1e80c0e40401c0a558000305022005019490050450b80c000c81e038483c4204401580420305002a2050b00d110300300c103c00402005226440843c000c09028030a80c00303501ca0700150042d295145c200409a2000107000f50181c0e0746400714814400300c0d224540301c0340e500305100c002e004100c40407030141200c4e03141c917010f2143e1138522402c4e52503504144010308007014012011482c14000c400418203490041800c000c0b4070703a41d40a03140c0b41c2d41c0d1035500c050f24410303041c0841041e52140c0d03001e4148603072444140c1000c1299560356072409038003e00c0782406550120310407000b1500300d280f8180d10b03140508190b02e015130280001300365000602808040c0f04004c100e6003200d52265400d607003c1c000140241d03440e40780c1f225019003960400d500501c0092000b080c0060f0340e035004101c0900a01e030b5a00d40a80d6642183d4400b01550001002008000e87e03a40d00401e03450007aa528800078903450711034408440c1041c045c401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 105237077 1250 105235827 105235849
    0x120105070e0f0307030512031902190e030114010b0a0504080105070305040b01060918020a0e10020c1c0b0403050a0c0b01150906080403091809020306090d030e0f0a0b13140a02 77
    0x112035080134070200042000420096201d161305403030140e8039954003c00e48000006402000505440807406000715502c0c0e044c0d6500c500426151200080d52000070542038666862107602114845001002074580403030103040f5800550604e941415110300545003118821140703140065103950501051200c0714464038058a480e1801e1017855003402c041400001c41e440b41c611503282c3c001a001d001030300c1000382c0200f10200809620a895542c05d00070340d181081c1500364454020410401801002c140118150581c019180885a03545072400e445a410121515041c86508561880011005c40d06a0302810740480341d44003400004500401c41c0941b5000079007404170580502000c61b81003842d24046812001112103c4004a90a40b002e0083c281009406100f4042804440b41004c68907091001c030f00e582c20400002c1c1806110f6440320bc405020000e5000f450b080c0c00030441c920391140d0b200004403001c0c60440d825941d080400b180340c01c201c08807600308020000451802e044602c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 105238327 1250 105237077 105237079
    0x203131e1e170f03070f090503060901050f070e010c02090417040f0812070f060b1504030501020c0c01050901091211060a03020d0b031605010c05120a0801080c1503040809120105070e0f 81
    0x3070b0600015a404082904c0702408030b005220140911850242c413503009a4050100035043c4d035241d0800c1002c19005e040240c0b11501d21181140c001001e16104045074490400165140d00400301c0b036070244402d03e14094401d84091201e00c44100e002030000008000604128000185151514124606007442000d20344001d0804004402c0030840c181c1e25440d8031a0004c0c40011003154a4001944840c0140d00e40307001c03500085070000602c5410b41c00f40c407011000c02c050b646101d13000c9004445a10900c0d49070381c0442d0548106100c5055280b00103000380e8410111900708400000c0050802d401c40c03400d000000f074000800b00b400c40001c2c0039074110000c065004012007c0d030200c1c0790700201941c0c01742c40d0400850110311002c0c040104940010341c400c0f00c007110754540107844002c000758024003504045110b00c000503080d0381803414010f45180700d10b21145095032034640da400b486070b012900b0590b0020301b00d18256032008081c0315140c0a103109488004c0308940b140c060003180d02900d0119 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 105239577 1250 105238327 105238373
    0x12060c020a020901030813080f010b04060f030302061b0409021215010305060319020f09040f17070b01090e011b020706110102030402030303040204050606070b0403080f0a0203131e1e 80
    0x2940183c84020302941501d9200c4c151030f40f599000002060444050f80c010003a030b204a4950320800c075019448507840d030405032024001180c42c1c0c401c075801d414081c44020b006900000000d2003503001c40c0318682200e4101d1004600c1c256698080d40d050341c102c502260310030046d41c0c05000d0205030200c1400c05407842803c082c41686000c50000380c460014102c11001c0c4c040310314000045649500c40101c0d211802032140807103081508165204100d900c034102d1703c0c1c01c41c1080301910710000d5425690480d83c80340e4151203580c02d00440e503005c0d0920301c0c5400030350340d22072041001581303644149080320705256000b0b011803441c3c2140148240d56150310301c03499920400c140710245e1408004c8035486501500c002c0303103030f40310380010407601d1050050141a07080640148020150f100c3c101501440350207001c0785007504c580e80a40100c0c8000e0340d000e8440c40c007242c00440020340014070b100e01907070303807a030040e203500b042d1342b00d40c0380030502551400e000c0c22241603000d080180c5551100d02c40484a40a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 105240827 1250 105239577 105239593
    0x140f040f05010305070c0b0601050d090602040302040c0219170f030403020d02190312020307050c060a02040815010602060613061d1609060503190b0d03030f0c030c0905060304150612060c02 83
    0x409406c54001c1d01e00945a10000701c00941180d001d14111003d0202c0090204004c1da41c03400d04400942040c0000ca224505100307010070710500c00901785201300e5000d035500030300f11a941e40e610402d2100186a00c4007140900c4256a40ca00035801b642c4100d0103500681840b07040202c0003818a1001440010b04600c0b4a880e07001207a8031180645003491640c03030060352a15458400c1d50a03010786500030700c540c8112020001409001e80160040300c031560210b032013055403940c4820300c00000740240c1c001607002e200040c0243c9041c844e0200c1c0700c100048005040b035161201003400c00709660701480410190f400344007003020340d034040008520f010b00e811a00c00d424020000c1ca2840054035880c5c18001480c00c1c03104062107644408030a031001008084000400c1c9000740203040c1030780004c0503c03481c01c110309808174040e0290314008041541e40d00c0c46a41004200a0141c1001e001a60707252540a0006030607481c900c41d11002c2c0075415a0031000c80041e150480c240d400d01500e000442d0071881c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 105242077 1250 105240827 105240841
    0x10e0a0b07031d120a05070e0f04030e150309010e2a010c0302151005090a0c0e0607030306080d020307120219060b1201050c040f0e0105180601140f040f05010305 71
    0x825103203982d5041c42d080c071400420a001228422007071250300e501080d00c0036000111540014950203062040c01510b00490351035074036800866086071012606191280001e0002e03100d40c5025402d15001000107001501100011006400854100226030b6440c10030313080b10070040142c0502c2401c1d504499201c04c4005061842014140070075906000c6000c03030342d41c00c040c0284000300b4080f0048040e55203601d0b01904241d0440000c1c840c441c00707a01c4203004160010514081c42e45201c150380c40b6900c5800c5411705010540d03012940a404040d52070201050341c480c14040c0203100c10983c0d0007036490f00d44500b407440869144078620402d40d441500b00c610300c101c00c0028800641d801000004c1c0b480c0800010a01140404c400d15541b03500c0d040800c03041700c00400151040c0d07145690000c80d0107860f8034010403040004c0c040d55500800c8140051000c0c00c0c4000d080e40e001c18189800180d0745001c03034010843e2b41201c83d2040d940b40010a041c0040070940818000500092030248503e0030a06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 105243327 1250 105242077 105242099
    0x200a12050a12021c03020d05011203090e19060b1e0a0f0f1205251b1b030b0411240304032f10050105060406120506010903020d030e010e0a 61
    0x85004180700c8060b01041c039503500034400c030404d102d80146110405224084014001e60080d500c81d800180350400100b900d044440f103491341d5950540b9507102040c2450304100303c07000c0080001884581c801414036642606000c0c445c02086075076010b039101c1c504101104580d280006207911084000d000c1180040d521600c0b43c030701003c6509082c50101c00c0554111544841d00e9104484607041c0b5062104402c9050440d40c001030850b40d000380b007440c40718030854541078a00d03228100f640054184101040c95001c2244201c203d15180011641c0d0b2950b40a010300c2c0104c0c2c055032034000c0842c0750f60960030700e69034125000013031400c4500350103081c10602030140006031000c3d040003024401c41100040004032160205080f28007100c0c0c4004462200303542d02d50400b8542c6e505405c0c600000b8080c01c10b141a24155261925204d05c500c0c4108010302c002d02d8010030b194100100e18400001503200e200024071203500a5585280d4218480f00240005031b4291079113006100a040400000c4046 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 105244577 1250 105243327 105243343
    0x612041a131104090f0f051c050d0221040b0f0c030412030207020328170c060c0c01090f0b011d01051e0307080d080f0f010501020705060901030207200a1205 69
    0x115003002025544004200200303800340c8003c245c0030364440e102c0c040c01841208850910b1040d8104d443ca04e40c42c40c0c0800590029070b1644011447c180010f002080e61070300a003200c4444224100c6084d0485414000001030a80b0300703403039030b042d00001d00072071a43c0e81194680c44203040c0e0203e451820f05950b6905da000d1441401030415a012909108659003032118403410728004c4c2c1d4500e21044146007042030301034825021540040c140945d222050030190a032403844a40d60050422555036064089481d804040b0f080d2955580c0e020140019007001d4003000c0d10360040740a22450341c10101041810013180c00c0c511b9405000c040104030b079690390011145040780c10300c05071204085410200c1c0c540b01c0c0781c0e08130358038034001c40d101c4100842c1c1c0101c40710b00c192016159501a511040f120788411242801410b005800c900b90030300407803c0050090520305810b01d40149030190903121040c80300d10041d661501d1031850410701030b8030b02e010180c51000c0c041c001025244030b03031543c0e2426559940 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 105245827 1250 105244577 105244583
    0x31b0f03011202130c030c0e04050411120f0d0c02010905090609070534021c05060103060903050418140a06120b09010605060316031104080d120b0612041a13 69
    0x1070001c040c0d00b1500d82c6654103134072040400e4103000d2031100c0540500507003550f08034040041d026030030303c140328505030107018051604503030383d19040d185000920072400304003104c41c141485541100000a80c04116403034840946960310000051184001031811a0a0b0300161040629000340001581c030b000d45140c12076203604140d640c40644d145405000401170601c103010140d1130506100041c0c4075804a585507100311030f03001025800a0105840b884210300241c02d99200c1001400000e0b4541d000b9600c00380641441814140d49076001045801c0300003000b058140c403852868120000000440d40089400c20305100d0581400740480c400301c80c10701c021700241c14420220305024400c0d4841c0e400f0b4a0003509143d86d0740351508105203240c1e090003001c0000380c1340c6048101080c504405a0b4181c8141c54080e04840200c0c000495900104584180040303030f944011303038465525000105103a000c0000c40d007d0b00d1801e402c1c004801a0540c04408860400f1010400550604502e407401e448c1c6c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 105247077 1250 105245827 105245849
    0x5160201110a0303061805071b020a0e090a050f03030601020c0d061803050301081203070e120705091e090a051c0c020a030f060e01090308180307120302031b0f0301 72
    0x1415000480d0340d9000c1100c0348400d4065410400e080c15459084202a81c0c5860a80241c00011498000c05c0710320455440c4001a1400105040741c12481c80b03001c0c8403400203200750011911107151140039142528401c0d1194804c4010504108080c04001030a17804d03003001d10b0039882c010300080e444113030301107016124a0074210b02208100d150f40c480c03450f4405d10060040e001c8003601c2e002d011a442030040740f107140300780c019001e00360102008480c4200056036074907440341d84160071f0101503808908400c0c1580260540401d40c0c0c0c55140032140309518644d0350003000f01900c4015900d118000d02140c0c500e402809004c408030b100051005a0500740b001c80c0c0c1d4000e4504c0208481e845400c0b44e00035031015820761700005003e01200c00c4017445000d036030b0070031001c2d4035010001d088031b2a03c02c004010170555000600c2d100e04a040c3c510320440c0302c00560385071044039928850b1000c02c01d211038001c00d6010050240c04000608040050006076a1503450b00c000c0308608100360005200b031581180e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 105248327 1250 105247077 105247117
    0x10c170703030e030307200d05090103091e05010506040f0608030a050a021c020c01030507052a190f0b060123030a020403150b01081e06040207060207020a0306060e01120305 76
    0x94401d0f03104074a10900141a00d440e4201100020541c032600407164003c030841002d0f000c0b1480300401c500f01c240da419207030245003400c0980194040c00701c00105413403944070103c002100f060041400d83c6600d115000006452401c0c038104403c4a4035004103040541c601a0305001e030001c000b0403242000d26038103000fa21004c240341d08914200c0242c088090302c02c0b0780841c80742100c1d00000c08003401d0384240c078207124030b03503402030b0450f440d0107081e03400c00c03195403a5603001c001544c0e080ca40c1e2102000d00001e80b0040ca035115590204100209000c0b148100e580c01100141300360b5402c55500310b9002d02e490103200e1000591807000041141400c1d00d0301400001140035014584c1c1202c00640d448030500306a000000710100003007031281c2c00079002c201b403100000ca91031b030241e94034043e8030f4109000c0d4041d500c510f01400001e41007540c08644c010307402c008500140e40d0790340d81c61001390300c03030200443d0840c00d140d9070b4040030106030306c900e0050809041102c000317a004400c0d0b5220310b0914400d81140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 105249577 1250 105248327 105248333
    0xa06060b0403050601181d060a200a030908041a030402040b01020601080a11030c130e0106090e0d0806062101030302070815060f01170723070812070504050a15020c010c1707 76
    0x404102c1c000c0316050091040d49180c7c50804211503100d4400d444041001d040b00c1100d001006602c401c204030501701c10031660031142e010b54442e040f0a03000d40421030401c3d4562100c12090090b800e0009520800402048118607041c0255005020300b0f01c00fa0415500d00540641c1c0c1e000300c150010401d0510030307580800d6440400001c0c00c070b02d00007000041c181800b0840c410003403043e40391603c810350800c0c0010691600038011082c0300c40703000e0000d24603020f0f46001101c8980c0082d018540c42030041118603142c0040300401805165205a00041c6516525020b0b03e0144168070a03081500009070014101903c2940ca07588480d041e00c0190440e10b070400100c0303460305401c001001140603031042c040c100d0761107480f0f042d0444001641d594402c1e00d55100101c04d000341100241030400c200b129446a815620305140c00c81020b0a00c54240764841000400340141600110380c0c180140f45607a5000e80d0420607403085100a00381200700f01e890361115259054503440040303000034001100410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 105250827 1250 105249577 105249581
    0xd0f05010f020d090515060604150908010504060c1b0206070b0402032406031209061801111207020a06080f010608130515060906061c090f05030c0a06060b040305060118 74
    0x100d085208011941c0f902081484002030181e4001a140c52182c0b15030040c40000ca160340300c0c061400240800c1c109450080a0900e0003039840003c41000030412001030101c40900074103014620580c40490303c0008002e0060048100c5010307200890b00c1c82c182c5c0c4015031200000ca6000e10b420019100103641c071380c00032a10304003207040700c0c1c2001c0900d00d03034104500760305c00e5030306024540c11002e564002d81e1a4410441a0180d1032045901442c1002502c942e11032991010b07034400d4041c10455800d031400318810342031113041000c00c0c0b034000c0700060410071407801001a201620440c10800000d00b000e1a050301603400502501d0284074402010a00f89054101c4000041e0341c00011100c6001d031054500034000015246130380a02041c1d8041991483c0c030109480e2618025207884400c040c502d8220f070040c4c408240f040c2c070707513a196103200404a802400103143c092071500c001c0c011102d90785002c1007103480c07541c8550761881045c801440081c4d00030071400d0442e43d859440111540c0c6241070500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 105252077 1250 105250827 105250841
    0x30906020c0303042105040503100c02120a020d02010f0203070c1205040b040810050a0e21070609110325030b1b19021605010801062102030703020403140a020d0f0501 73
    0x41180300c00b004020403c401d5188940e078001c3c407081d240c0121100e01754142d6842c000c2d4090700390315810440591002c61056404110006d08510441e805040d80d0902a0300c40c1e80065280740040e0800707142090201e409000ba0f503483c1421060840c03841c43c0c44540201829440d03200285000c2484211803405441101030741c0c003602c548580301366590740d03c00b003155403545030390580101c03942450002000c01a6a1290006414842c00940310401000c1a040450b26411181c00703162001840401c000c40c210b03108450035640b0946841490400b48001c0620701821728922444c400000d08121400c0006096204d04880d071140d00b28000e5110301c9404000794544540b0f0309603010002c0340881e005208070071000d40c148490780a58000000b08090110b510035a40201400309404c900100700b01441140c0003420041071600079000782040301c042d0000e0380d2090310440b00086d0041024424032421030410300f5803220682c020103100000c1d5000c10052100c200000c2c1400d035100d81142c043c802e080d04415 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 105253327 1250 105252077 105252097
    0x7050307021501080102091305101505190c0302010b0a290d09030206010f170a02210a030e132a0c080301030606032901030b060301060e040c0e091204030303090602 72
    0x546907131079020030740c002d400000205200d50030002880d40161400e00c2094000e82018121020766410002d0044034156450031442c03c001041251544451117aa40c40f50060719560710021b09500c07605009081d01c0300d90007058480c200f0008208070405a1000140400000c00103500850612880324800da016082414000307500f4a0340f0072080690115001c0d0503201c010050400054417004400e0581c4c034408801071403540228095005460940b81102003e143e00460348580c81c8061412820f00d4a20001100465135560764094946007401c07032065030030a00b0381d013046405e5000c601018180000d092458180e107444150000803403141c06407458664101c0b9030b8a5603035940b882e103a80181902e00c401e44074000c8508800040c01800401c02c05c03022440380c000322080e400d44c2c8402c0d0f5806005010359600d596140800500240061549031049000d0038070200c0032481d0000305580081e00070b0440481d50400c41545d4050340b801d009a50a072905454005481e1043c0e00d800300c0213128000b054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 105254577 1250 105253327 105253363
    0x10f120e0f03040602070608010605040b03060f130b030705100801090e0f06180d0507020904031812060b030609010e070b030a02040e0a0905150c04061d040504150605010c020105030705030702 84
    0x2110703046000000f0800c44600340c1c201e07008160350341130840300d60000780164000030f60100010048404684091900808000c00d080e410448101c0007d0310030703124003850101c8035150600d02080e0310b020b020007001843d05a03402c075111362081c040140280310501508002c01c1ea1008082803551003081081907009d18041101c0d05400c0900224400a945074040f6401d032040d2801412050701c240c00b81e902e61075020380040d030305441e55030342036541160044400c81c101c0c0180a00003401e05829440502c554040c0000050f28280e10b004e040c03c064004105010300e0b810001d9480300003800007400340c1200c03a20441c0607165225809400d010788602e41c404144a032803d001c0c400e0403a02c5902c003a40d5288a20211400704048401540c418030086a541c0c0c1480c034140420801c040c01207403280d64200f13000c86154185e030801000039080700c10070f99054a1b03041c0c2c441c412060721101d510649001c1c0a003400d06905403000c0760b00082c8503100c014040010884003201045046000704034905000e030441d00d00b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 105255827 1250 105254577 105254593
    0x50d0f0b040804090501050d02011706040f060f050f0a031a09120a09080c0a140105180d030f090f030b01030f0f02040501060206060102100e1002090a0e04030c0606080c010f120e 78
    0x101c05801d400c42e0003135080f05441c080c000202c500c0c0c00303200d101680354180c540d0b003c49149100f058003038000c01089a6041070320f85004c1c50314401d0728441d54000d802c424031620b12403418002400800c10200c3d180740c0c0034a0000000344086404421100700c030305002d6210717910079030b00d60700c143c0e041c50201403c84000240114803004240d0300081c180b01607903001c108440442e0700700b07400c00504042a100e082c80001e0010b01c85500d40d40304000803c10071160074000d2801c11006000b244d01c03000401025400030f440c44401c484482e034001100c000074014101034219450079138a422007050303c1031000038040580408000304002c1c40405815071550020130400c01503035900303c00380d2682c0f0300703c5a140c0140201002c051101a861051302c0f400c074807450003803140e107c0100340c8100030b500425030304c0d604c1085c60000203000740f2401a5180300d01d110703580710560100e4514003075055414a030040b00498104001202040e6071040e10031102c6036051a10b240800f140c03402c050018495909a0f070060300601c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 105257077 1250 105255827 105255833
    0x1020c071e030816030e09060d03030b1801030c150203070c05011206080d0c050c010528030207080d09020315060904020103050a02040512160501090510080405010617010e0d02010c09050d0f0b04 85
    0xa0100c1340f09001e900ca11002002100c01c020031401c0440740d8550080103556803001091103540800260380b0701400d100c1441310a601504200e140c02d90088030022503c610520a00c944039024220300b10003800203600f8400603503142d00488101c1c1c001d450400c0307129103030300c141c000300c81d0001c0004005000a8920701020b00794024400c40350002c1c1a2054072030301c2c00c00d81507540714400300c03412851820518582c810140f140c146800e00b100401d501050380038090400807440d00d50041c030000c2c54807903002505000c14030500d820040c2d5900504008595801000042d841c0e0300f104551280e82441c00194a540e04031006000780500d400ca650400312100c0d05860038000028010707400e241c1040c481c40d9840d0b480004542800d1140961900040c070740462200d21ba010b000d999030002d108000104200d0740f588140100e41c50114400310950391160400500314000380b01400841c0141c0c4000d114048040d000600504030317605c9140e014612220702c500030302080c14114460b06901c04024035550070241 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 105258327 1250 105257077 105257107
    0x160602070210050405101b05010c08180d050d18060e07030b060f0303040501050c0703021e01080916122d02090a090b060427050f0f01020c071e0308 65
    0x101089000d019400c40b040c140500800a136421100020715104651016407000c5654210403050000046c04110134540012004c0c09148500036070740c0d44e1003900f4030341298000000d810701c40040419800c0000f4074142c007940b103000c4440e1704183c0d9001003040020480c01111045083c20003030200b9285c00b06002d160b00780841c4003c1102c1c040c030001007145d00c50004100644100c48111075155008100420640d40510040d00002c048481903403480c5580b9004184044a0101605144030184602d10102c0d030304a000340d03810191403070013002480001220500d4221450182c00c0110300b201e040d060801c100031400d980d1306058803202d4012541d03a800080a118004d0500704d01c9481000006811160035118080d00c09802c1001481640c41b0f02003803000800102c13025482c00405900b245106129034408461214402d4008114040c955601e5905200500280710b40c0e5034010003040c500c103000024135000340d41202e814800c0804510b5520202c2c00500d900c010412000813800e078103880404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 105259577 1250 105258327 105258337
    0x916110d020c01020c12150402010c06150e0702010c0f081b04090c02010605030607080c0906160506040212010c050403020411091509091b071101210b120a020123160602 74
    0xc0c0c080700d05115005c07040201c000210850500c00fa405151291406d04c229126a60007600604114086007015107682e81581c6c1090502070000341801070410210050054140e400546071000308100300032090014a1110b08440800810005201050f13100d11400e01e410020540d030310b503440d91282d6424a120107400140724500255282080000365070a020600c40e102d9142c0e90384080a40da140720002c00ca03500241803880c1c02000c103000e4104c0300110a4001d1440c940034030020600384c501441044105100c0d4400c0007400d9040411b940541500b00e001c1c0c1c0d0aa035411100403034400320011084426004007018603a004614142c1030810840d503c1c000e203240c45058442403003540d154800c20003507540360800c442c2010300c20405603010490507000040580d805240c000520311001d403201c1040d550310315844102d20f1341c410040c012032030460080c0c517120300ca09000d01843c0c4a00d40000e015114003519081500071400002d100000c100000c80705800455215003510f0b001c41d003040e000a4000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 105260827 1250 105259577 105259579
    0x21303030221030108031605030403060903080a05060a050f0f0303090415181401060309020111030d06090516020a03120902060f040305010c0207050a06121805010b1e0916110d020c 79
    0x442261a0b400d010700412641a41e00c400b00a5103800b041ca00d5000c05441c4e500c80c2940c81c0d010a00021000070514020031080e940a641e801c1550f0810b00708841c11141d015142610507140103d0030421307611852660161144100c40c0c1c00105035021000c02d0440c466000301c02d44c0540f41070220740030b50f000c6030f06c160144c80103008403e00c0e2a031740001080445554680210b441402d02d4010090580b00b60000562988103140400c000f4220101d060f2450704102d000f40c20751525800244810050341c0b00c0c0e0380c2e01000421f2500000d414100300030b501c0e01ca1f03a00000d010441c0c6003c0100d03400300380c2d400a1035400c2c1e02502d01543d6200c1003060a10a4209020454855081050740b103881c40c0700240c5681665001048201c3c0e2925000c01580c40030394180b00c201107161100d542d04031014000707488941040c0100b001141c402014403c0005035507030f4015841201403014143c60154841038042035103d290541001000c4000d03400503514607984c00030820785031182c84000250341d5404905000e403040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 105262077 1250 105260827 105260863
    0x503070f0309020d150906051005011413050105090d080c0102070c05100806040c1206091410060903020904110d030f0206010b0403080f090103090515060f041406040c030213030302 79
    0x3590504070195070006001a51104540c03410a010505042c514010f001108000240400c65940e0300000e481080b1036203500040d9144081180d0b5170000030500e1011035004089141110208620340c81001c1c5028480c104100458084943d4654600586e06583c001c1401c03038440e0380c0149481d000c0d611540e82143d0381010760000041500f4003411442e07810032291074134401940d034402840000e20381590380c88100039030080340f00039640c11489608042c00c0b09040105060200322100d03030000034041d003210410303032421408100c1c4942c80401c003070540b80d044420155030340390350805025040f1040da4490380b01406031488410140c100403200c40440c6680c00342c8000341c0ea6900b26646600403440050255241000040e5500a0000040c40f01d42014100000c04190b55100d032480d10300360070100d20a1108050601c001031034101c0e807224030314078216018010310b0000f8482e202c07682c101401550040e511030100c2c0301000d009406403141c10310142269405d447c0c1c0c0c3d081c025611031410304100c038152 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 105263327 1250 105262077 105262097
    0x50a090f0b100f1103090a0608060307060509010804140c1c0506060a050d02190806010b03090601080a0c090c0e060f040603050c090a030209100f0b030f06030703030906200d050307 79
    0x100b088070b58a82e1400b03082c0c44694092101c0d01c07058980300c290304c0c500c1807a07000030804903c1a503100b14a61015014a55603c1010b280440616140c49019040001445414040740305541e910903e20342e84140d2280d8190b40060464075054502061583c0503035100e202100900c00c00251a00c407804941e002e60300310380c102c0e2140c0051000402070350003480c0c0c004081c202d035000982018400740d03840700c0c00c045204400b55a14181c00341030801c280c21000301508004288400c0c81d0080042c54050300e04900030b003180655640d102e8504040c00c2c410fa0140c90744070305440284d02e0103041c0390141c21714060800c9a5890b1a0211130516510034047c10001c41c1c5040040f450004a840507030303c00c1000500b604d10b1103070440d002c010403810700030315000c1f91604002d4003003500d10346400801c0091a001d808540c0b80c0c10310400ca4030307802e08001e01550296014441c1040400e500400746011207070a820008840e402401e41e103050403081c00d10380c6070544038005010180c1c80d40100110300c60a5240c0d034081c004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 105264577 1250 105263327 105263329
    0x3020d0f0608070b18090114010f1404060323040305040602010c0206042d14070609050f0306040311010603170c19050c10050c01141f1d040804050a090f0b 68
    0x341c036540035007401a40300d0841400182c10319001440c402456034140c4c030030440b0260009414020076008112190000c6944010300e58100550140c429020708101c1d590044040c40121280118800c2404058451400c601a40414090140300004015a0624a1515090140840e032083c8034030b00040d1728010200c0d0880d4030100c3c0560245a0080800c880e22240c160645102d043d807610072407a0b10343c40b0b04400001505900041d951071809400781040601d0490040c242070300302da0040303003d0303d0741034600400c130303a008650240e2083d4181041ca00c0000b200425600512076500010414031408003c01070142c1090090075a10241100312410341d2002591800c0180380901c0082c001e500041900d0480e01e03124009800b000c0c860f00c0c0c03071810710702c2e9502c4a50031f5036098004008115860130610000c0d0180d0104491960401e00c235a440007450104522080c11000c101103800030b10f054081010080040c0c2264014140241031010894466034542c0c0244100b94001c904d007458840c4803401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 105265827 1250 105264577 105264581
    0xa0210020f0a170c06012d050303070b0912070b04060c03090804090203072307200a05091009020c0f0601050f01050d05190c0201021e040f03080d091203020d0f 70
    0x10005401c06051030880643d940201c58080241500180a05004d0f00e2821482001014000e081c1c1e1820142141001c0c0c3c031115031a0382003400341444041c007080911068800000b2504510340c050011400d42d5604102681441401c100310342d455803002070b0a00501038400d003401c1c013a0740106010021082d060200784c1c11901e2004000b40149070501c005c2203120150340c06103502608505041c100f400080b0890442c40765901c6070454203090200d001701c140403107031460000c40d02260000314400302040f0001600c10f0b26503c1100c4c0301d12060f0780000e4510744010100c0b80148410081076488080614415842c0c0100702510002c0e8460301d0300004441c03420a0006004a0040c0c46807880d220300304038400e0152000400301c05104000c4403008944ca49644948070805007982d00050b221880000c1d581c4440008049101001c41e0500c402d100307002d0241200c10440c0d40c00403003541c1e11041c00c1c00300005854074400180281800456075194a50182c00a104464004008011070501e02281100f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 105267077 1250 105265827 105265843
    0x90e010503070605031e10031407051f0e0603090705030d140d0c0509130618020715020a0210091109060621130c12030306050a0b0d09060e0a050a021002 67
    0x54075510108003080818002e10003560840209803089410402c4c0c0d4407050324410b001c0d1040a540f04609400b041404802d0300c103880e2010040740602943c3c1e180c107001840101d0b0306441844141c4201ea40e0f0312500b4003030724103a4400765000d85060f44915044c0e090540324851446414068010110254161445484099921458115a103091925100585004102c00b03076440701882002c1018881541d220043c0d41c003c1c3d85030040c04107400d41006400b44507440c2c1c103480061614014014000081c880303041c0c8540d114083d000060321004081400c030f2810440c5c616142a042c41c2228190500c64100038540300c0440640d0300300d0303030fa07107440050242910820724210110100348440c070040e1071010b250190002c81c0c0890401850711103843e07450161060703034040d0404602c004c8005c41096014084c80700103200807150584914500090001c4900c00c014103400829a50b071900c40400000c0d50115080103121720454000781c1035840d2041c1e64040910050744a241c812901d00101840003503114 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 105268327 1250 105267077 105267079
    0x20d23161e03090f12031503020f040506040612110307060e091602070518091c050a0f12020c030a120b0f0d050f16140306010608060d020a0302040f0903090e0105 71
    0x1140309000c0c0c200380c01010141c02900c04054465030508041456400c4c1c1001c6180114180800c1404c011809400c40311031110101e0207800103082080541d0717130100e40c03114888094034042800c1d40da1000003401010280c102c0c0f0b2000f940450080306201c3c40c3c0382448020305041d021a12600d8030741006850001d8003100ca00e500000400000d605074484120516003012103004460700b85460350002000c0d9042d081c400c074940c0003400200091780000704a59144960032240302c200889070b44000418912503004071000b8062a186000301040c840e40d2036031a540b03294030045440b0061800043e840340e00450b000710002e090190272011824182c881d902c9104801080080a100c074601407241c00204007900780e403a402000d6104a1107441800560709940301010300568803070400380c2e21080c6419a80d00c03280254417103c010301050b5005144e09403c90404c9880a91031255840050350150302e6400c025002810039045000c5005d042c1c000d0001c0034400e4880c8994075480341b20f5070740104000d20802e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 105269577 1250 105268327 105268337
    0x902040e0105040c02011d01090c0b0325020a02180108060a14070c02030a060e0c090a0908090f13141024050703090911030103021e0d0204020904020d2316 68
    0x100030328030f810381c400c4081c400507000106d4004441000c406020343d01030b15019860f51121240030070402c04a152801404022807003905508141c5191201ca820389000c40e91180d98940384404114000c011035540168018400440c1201c40d1403c071001c1c850030310604500c0c1c41044d0205580140e1790290155605906240260766500c2c00005c4425004c0d80c0ca003030b130b05401a061140040b071800c0c0280b43c04051000010001381d00702030203001000f00c005001d001b038a403a0a01144c0001e4086040305e480d070300111400c61001d0040d00c0000d03100c42e2001c3c19407240918184a11004040140205201d880c2444100b4071080da1010022020903643c1c0008a1000340d2203010344149000301d0241041c94000c6c9030407005c1c0f0340c0390b6280031300310303180b08140b105040c0e004001002186041c2c0d80d100303003201b5a05050725041001070041140114041c17402841543c001c191548244c9455040e192410f00c8046c007072280244526107904031180141040c2d0340c1c00d0904001039003c1c291000d000000c02010341d43d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 105270827 1250 105269577 105269579
    0x604020901020a1106090d0b090c330f0c07060305010f080a08030a060305060f040203010b0f180702030c12030907090b0618240a020601050909070501030207061b180902040e01 77
    0x100b4041300c8544105540c410b0f014080780f4126254029207507c064440e01c15101c241c00c080c042c507440c00044a01c0c440c400c504030500d01155010040203146140855107100308600060b00e078041284c0512620f00b4094080415151100480043d0b032204507510340d14200481c2e600d80d01c1400b07030100b045c0100b86a99115070340500c00120030340000c5a00030078418001424503180d684140c00c151782500c494010b0250340050105503d8284210803039948111800701c888a58807021521895800310142010623404002a81140c02401220b003240440b000383c0314008801c402c0080f280d00180c0c6e501c0381c03901c030303200d401701d5105414401c452300d0b0940140310310300307150392680042c400701066024641c000c40882007604000c418003196030050580d82d8076807034994051180c02498884168005c912403503080092000c980340100d181c20580c0c02c2840d0260342c850341c40c00c1800180c507400c0d0700150a000e00320710600358150300801e91030b84451110301600c0f05a50b204000c000782c2c0105c0c0544c010705500440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 105272077 1250 105270827 105270833
    0x50109050a06110304080102040f090c080f0c0318061e10030c0510030f0c080a153c06080105130203060f0402071a150a050108010b0304080a090803040810050604020901020a 76
    0x10025950f02203c0c03c9910705074443c1561783c2660000e6100c13041440e00700c00288100f003454003403145a039480b4945007a00c4c1c604020100380c000c0014010080c03000000001c07410b1102c50201c3c17101c040401500712142410310b002007124100382c0d0040b091078090458003290621031035035201ca080701c2d040031059030b0903401c0404110948002442c02c009142d60307030b0ba0314052000103006504c103540c6562101d91840c03800c110180306440780b4103c400150090b2200c14850120282806100a0701c0b661001c506180b01c20500400d03a8064115203800041260b00000e0039584120881e06844082c1c031200c42500342c45800a05a00060341d49507400701882505110f2414140d0140540500030300d01446030200f000c182d048140d000761400c0c00c0d030703440c1e02200a01d1814031610020040c1400c0c82c01020f15071515a1a03461804080c1009024010010318585003074464201a4051b01000301070703c1e03030340d0b9807141c4d440c0d91021000390700e5a8044c01d040004d4501d1800c1c0c801da42000c103042e00170700089100d0755 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 105273327 1250 105272077 105272087
    0xc040b06031005150c070303020c12150406050c0702060f030a1506080f06130c020106080d090617041718031006060e04050c1603020f0f06041703070c020405070c0c050109050a06 78
    0x4132501d0341840c0c06110001104030100101c04c000c600079009080c008400c40c007480f51112920030350150756440100ca01c40c10820103465160301c5600b041d4001600d0301c8000d201030311480303506001313544200c010920740406080507004600505140104120509112103a00103c204c07610648000ca000000002c4240001e0f150803030b40500010a000d414103003803d20781c4111440400b4500c0140c1d543c850502001000300304481204d01c583c101004400e24003a0300a2440c0840d140070510082c4d028041010404000d040c7c00385c01c0410392580382c4031480340b004940241f0302d01221510900c1080c2c05814504611300c20203050b144144d03070740c1062010300c00c01d10020740782c041e12061040004000d510b1129821807007070b9101d28070079405054641010f1500d00c0c42c051341e44a010b40d99410550500c0005600400441d00320800d18880944964412070161500101da01010b0b4000b41014108054581e22061080849215003111084280c50740011960040d842c0107454000902d1081070255600070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 105274577 1250 105273327 105273349
    0x150b0103020f0a022d0c0f0f15070c0906030c05010c02120f0307020109080d09060f090b070b06090a1b05180a120302100203100e0a0f06080c040b06031005 68
    0x60401500d401800d8403407800395440340c0300c00001030304400c0c5e0001e049542c884140030000c03241c2c00b0a031030750100d5000c00d9890f81e402d0401c071442030740e1503400309500b500c0e0300007000b00d400c01c006c4c00d6102c4148003802e0310b10b00c2d40c4407401c121607541607404003244d1304003107101e40b90603030390031510405159040c4001903514105051059030b0128404040104001c0208104086d504815000d113407204a180300141c004806034100d080ea03a0009042c0c1940654000b0303d003011034015107404c403003011003c0c03000d907840b060680140d0216000050b00c14140440b503000f150058005480908d86a40d07290341d140704441c040c8094904000803070040000091045002d0204440211403540c0310741c000d01c0005c3c144a01d01e9211070303c1c240d9155010300505406001102d454541442c0c103502e1490141c07a01000392080f07011300c803882c041d4480032841c20340c2c69502030880001e11181c1040859101c1c0c5c61181d03108095030b822480b0390b00346400c001107400c0c0a42901c3c0518403942a4961450901c0e00f00f003141e45003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 105275827 1250 105274577 105274579
    0x402040b0907020f0c090105100f050d051614030f0411150705010b0118120602030c120a0603050c03070302090a0c05090603100812030115140f040801060f090504150b 73
    0xd4109100e80e0756981d01585020711566001094001098103005007450400b0504a21450111004100da0b0f15241001007400055242c0100c0d80d010580e0242d0b10790140e0300440403010719010400c10b2007904000446030b111003585514141d030341c03c04085a084e00c01207407000c1c1d0b0b0b09424004940020740500b104c039102c10b00140207009000c1080d00c5aa05a0040582900c96a4451083d5055540c0240740b0700c0c11501007060380d000c1541040c071010107180ca5004002c0150394004001003200c60b00c00295010050b403039a008a0750b041640415018042d00e010580c1c1c1400780240c0500c217442e00142410489901400310501565120b81180c001c080346a2000c0c24040200481c20141e992000210311850342c00d10b0310340c40e0500700707050b5519007415810f11010b80d14081005014002c81460f6845082030035141c44500c00510b8000714244d8081c2816103181e000300803d001c500c6900c1900030900b580c5503c40207085030b5a89882620a407241681c01400040309040347c40c0c00f200e80c94100101000d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 105277077 1250 105275827 105275831
    0x501020421060510060f0c1a04050303060108010801050106140c0a020604060503040b06010503010b07020603060a030b01090c030515061e210a0b0d050705011803050a06020310091404030503040204 86
    0x5903504071280464076040c001c0750a041410550000c00c11075100c2d03d508101e00c0c244825680d8104680a45500e010400c441c0c14401441c402d0001c01c002840c11140c5c00030099508050b038106854925982d80090b20080d010413954000404d00c1e000503c902d90481e015941e84100c5a202100c1e04c50541c0d200103503c00d101d0196850f048096101c0c80024002000b0a507210303a17a914240c20074424601c0003505040c10020704100420079031040340c0955980a80490316696039880c0c101c0041c240c003142c0c0e8001005000c1c8940009000ca80540c0091084090380d00c0038006a0745140b1040c00c00010100b40660117030083c0030b0400304802c411100700a400c8801d0304546000c2d16079540c0f10000075101c03403d2001d01c1c4c0d071104000340c1150314003800040d00400c0c0ea52840e070030160340c0e13442e84424107401000d041010310240f40b400c0c40c40250103c03006580200a90b02440d0b10ba04081e4003039841162110498410450001850302c203510030b0040c1c4818081c1b80405545035564112002d500141090364096 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 105278327 1250 105277077 105277079
    0x30e15070c1202011209080a111501170d020a12030914011107031101021c0506040b06070c080c090702060103030f0e19050103050c0c030702060c03210132010c05010204 74
    0x8585800a40c050908480c1e0440c0b140042d100040c9400042d140d03040d401e07402c0c0210080003412810980340d0074070041c1010241c01503054543c80c58560502a00d10502400c0e0000041e60707000d104410740140b080340c0942c0d040d10121203050307a40e031001d42d10040c2190502428101c1151103548022030707652180c0500c2000600315102203007501e100c000002d208450009030b0000b01500403c1803e207a0105030001c2d0700f8080b001000048030038242090f05c007569120300019000d81e59950100d500444c001b001c058880c016824803c084034418011343c000e41c49042c180c1a014075010080c10301ca106075900410280e82075a0701115000085d559039001d1200b244681d000960710324203418801031415450131026490000010b080d0341015100341c406000400450040030f13004421650355640603144955200010822545540305eaa080450390b02c58031a100da016500c0c081c1c041e4100c410030340685260b02801d400c3da194a04c1e0000700c080c641001100400700c02c0d40580c809084050081c00014209 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 105279577 1250 105278327 105278333
    0x180f07030e0703050c090703061215020c0109060e1b0d0303021809010e0a050f011d060d020d0b0a05010510050426030d02041802210a060503070314010f09030e1507 72
    0x1280b40c5800488003900207140300905402e2550003103920800c00d15041c40240c0c5484820306d61000c4074200540509600d418400740ca2a054044a500410382c60013004104914142036000f0074810b148143c1c14011071400080082403940740920420f0000c00e810100d8000f650203800960001c0746405591045202c0d141030f0b5a00c0c0e031a401c1c024001d43d010f4030b00c140303000100c07136003140c00c01442c050850268900500a011441021100038600c602110400c0c0d250140018420003014000a5010221168000030880d660a515001e0143c1a109000d80c1c0d80364400c108483c1d100b00d07540310000314103000422505503000d103c80d076003003015080700f0b450b071112010107411079010340c54006180c0c1d0001820029444801058048406020301c2141058504184100d0007000340c00301e803c2585050011500d54115980203500500d4002e00320390701d8aa4034503201c0078008a07a0543c45940d46002c1944801c9075240c01809001a8107648198044400e00104004100690a00c00c01510148440000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 105280827 1250 105279577 105279583
    0x905040b060f032a090415080715170403050c0d0801120206030a021c1a0916350406110c061605090301050103061a030f07061b081c0605180f07030e 65
    0x1301c61400e92116036101121002d00007a2200c0c2d032000f01e0b0811520b4020815002c1c041240030507030741c2d044005c240d040021241180c52880980d41050000301b12400d010415400600900d50a0b0a1a00761110403072644130a64000d00300740b042402c0809860883e000616015000316130141b80100c0060403c542482e128600154a0b00c14240b01c684c3e1701008201c0340495007680c070b07001c0d4048540034514503040a4640480442c40300038010b00440c0c0d100380070320301c0c0300189006d014400103500161403400c95500341d08913001070f14103030f5000307103020051501100c05100702d881d203440c600020086030b280d2810303030304d1220044104081040828882c035180f030360b0700380110350003140180030100c0d007900307002034080001c074100c440356219a00046110401d43c0d000b00700c4e44120389413424125028a018000e1101521441000170028080001c010101c041444120501030301041c408004a07900c481c14002c82d110b07010444c0160320411b0000483e01d80c555070f00d26600040c6490082682140701d69207601d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 105282077 1250 105280827 105280891
    0xc030307031107120c02040e0a0f0b090c06070b10090605010507170d11070c0905071d0102030d0203070201050f06010207050321040e010605070302012304030c0f080307020c010905040b060f03 84
    0x9a048200c038419464072303000d00700382500d091028250f00f262581d00c4001700c20f290f640c02080c02c58900d001550441c004e2161000414001e06555540c010340c0c1783c031803807e40c412502e407081c0001200010070000c81c0e070300c00e00c410307203c060711842e15002c0a070321008174910088140302c2d05203208001041c1e003000e1601803e00300d01090200c460715500d2030720b08490320709810b810080f0080d24010400070380300da10010b80f00d03003420a85549940383d40d003900100d040d441043e180d0500c40c2d00010070310100aa05510043c030401c0c800100c5805912081d004a0700d8900501c1610b074594401c7e109071072111980c40301a055230207400a100c5c039040d51f515000d580b0500981c84040801d03000b2070800c00707060702070080101d100101c011300c4120305182c140c210000d95010b00090200040c000124007005540601d126602d90230202c030030348038940004004e40d030b20820300c4450b0000c0c410680000300b6050a0042c0c40b00400001d21403428000083c4082e000c51b00300509881e85002e00400c1185200d6a56500e02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 105283327 1250 105282077 105282113
    0x71b08070e0105040b010e12030403050114070f0c05030d1d010f09051623220c0906020f0601062a050d091202010210021b1501080f030c030307031107 66
    0x200d00d02109610740c50310507400280600e040c2400c2640e1680d014400c01c1050b001120100404003e48041130700e0740c001e980004149610b0900501d046e060102e140601c0b0b908240e07180842000720754011280c903071440300000d1a03540309102e40d19292001c0d400071801c3d010344101c6c07a008040003803801030964a05140740c010155039020f50f4018800d003803203401211801c0701c01002d10203250410150400300440c64609610940c0c02900c02a5901c8030720300e000003841c404c60035203a60225900000142414441400814000d140004900c0c0c004a01d884507605854040c10b100e030300c0c145c0c2c00d40380301c00302548041c02c89400241c0d4044990340c4c50242c802d542d01910007040718090440f0003a180c048039401500a082512480720f0050f03900080d000028440e12601688851111418104803080f0402440c0350303000300d4540e0700849001d0f6041da4101c919500407204043d990a50b0340340c980c40f440003601001d80081000400e400d0190b0001e10100402102c2c0740e240510ba41c541e004e41440d803584403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 105284577 1250 105283327 105283333
    0x6030103150605030d02070b090406090f0b0f0d05031209150f0a0b06070b07030c11070801020c011a090f0907180c020d030c0909112505100c1202071b08 67
    0x10200c00c0616100d55800b03041c00750002d1401e421780940184d901d91440c4581ca540b0140040c1c5044180c656800601c014515600207000494096520300050642440c100d809040a194006028078054080d24486500440a986003405207aa040d059500040845540e4464152111a40c00c405a015407080300b44405000d01410052810300541d40148640342c4500010b00001d0045404e90b28000d070001024100000d101c0e0941d8800c0c0c6070104130000300d90150096010006001078103400a003a41c810b0b1a008000550405611102d0040c15910040d044034005000814803000c40080701d0f0070403181000c80700095550031000310404081c4c404039000ca17444840030100d1b50380401042c01b41001905003030080e031005400c010051551482400340d0247c440313146010f4180c296080300c1e503030105010841403240b803103007030854104000c0030300701c800e48129001002200014031450560392140d40d56484400b40c204000400794200200c2504c2c1c2800030008002c1040c61701d102140105406000703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 105285827 1250 105284577 105284603
    0x7020303090c010504031a310611040308070209090c0d060b0f03070311060a03020f0309010606090902070210030b0103020d140105130b060f0705031603090306060b120c0a0c0206030103 81
    0x8580c02d0000000c41181440b4040c041400090190300c00d0700c40012031030304d1500c21360352404c0b0719503841c013810316180b0602c1212501c190079441c01031500c50200c44c0500002d2003840200e002580040c400c61101616400e0240200001442c00c072a80b2a0803540e0702080b2400b50b070700b007c00110f000640840c07c5540e01da07106041183d5080000c0842d00441e02100a41842881c548689048850a00b00980701c0d80000411101950099040e51084c0101041704d60300c902c1d00345101030085c1180d005a60224001c0100052001c1c214000c840c2c1459020f040d01001c02c2c10107009502400361490460b06240d000d0003440343c004414031912821080070b1061644c81e514100c01c2c000200c0c05010310100440c101107151000362541402c450710b1881c144000c5940c0d081c5401e106007140200c0702c0304c4030300e002240610300900d5400201c0800303603806030308200102c940d2059144074611941c031103d601d1007800c400150145076080086e0109040c10300305804418201da00240050340240c1088826801900d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 105287077 1250 105285827 105285841
    0x140d0f060e060d0201091403100e010507030509030a09060509120f011407030c08040f2604031502090d02040e0f01020408161505270a0b09030c060414040209120607020303 75
    0x20440b070b00711005850903550503040da000200303030105c180a03103000e1071100c3d0000c1c4800d40301000318581c2c510682808000c0325581d108418060035040d24100c0000f401e04003c41e101841c00302c11105006083d0301ca42d1001460f02e0802d4500c3d40004520382d0748401e4185c015402c80501703024102005407164000030b0000106a0351900b5801d000e0580000c162070074054000f05034100001e02d07081030f00100200e0680841d0700d00082a418000400900000900704151801c00d20801a00949104040300c008114000300084120301030300301c0403a840081600300102606260380701900c6c10100b10b050f07076503028008001d9402c0e41e06c01d5210310090f40c007072211510201c81980441000e44443c03901004c0d61040d9020082072806481d2420b500c6c8001d14141c070796110081d000700c902c4400090b0005000310f42c2c0e0200d070110790700f260710864040e0280078174061113441c1000440c0e05a914a5807404007030030314442403000940145181c0f5800440ca10720340408600100401d81c8980c140c1d60045a03a031500704 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 105288327 1250 105287077 105287099
    0x140a03090b18120702060c030703020a030e031b010c140106141f05221505041d0106080c09030102070602180a1202090f04060b0a03051605060c0706140d0f06 69
    0x10500c6004004008900400c0703080841c9081c1c4241c0c1c2422044d44541042c0005003841c41550489815440300040ca601055008150f1840050080e02c501820324042802e154031648040d1240c00840c0703da5541d0b0746a0b40c001c001a000c190f0060700034400c0b03010001c21541c212080d980005000340c40840038440c181c60017600381c0b200400c0440c2080c2c1300b130504100140060003070790348100c288074012610081e005103000240000780800c840d4030b5014244014081c2c410f170b000c1c5c0503106c01c00d03940803c1c0350000025401902d04039081940e5142880d034817550407080380c0c0c21951240d40e15540800c084004031b42280054030b0a012000703040391a4001e000200325a101140e07202026580b8020302040141e5101c000d065030107000041000328035601c51510b20020801d1350f0340c480e4460817103400032003485000940302860410340c0704400300d919112001c1003028007031040c641d050741d40000f505000c164400d4446410112454a000382042c1d4070695100a45200c2049041200d540d054200a00c500350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 105289577 1250 105288327 105288331
    0x103060219020f0709050601180609051806010207060f02031b030307030b0d080703030906020403060e010b04050601170402040c0302090a060c1506120f110402160c05030328140a03090b 81
    0x81d0000300810083d00480b00c0d100c00d02442070404881e60394000030256405590040341411800302150201c584511014245104a00495001c0d01d4124120300b0b005644141081c00780c04142c0081070224a0200c0449155113084584011800207000300c1c802000341c00f4400007104d003024081d42d105d140c505001000c0380c82a00c11103129040100c40715003c200d1a40403200d103140c00d450042081409810a42c000c0d10840d40000d002600e4150200707020300040d8040788003040d0894042c080d540750800115203100c291003111030412294404240103180c075038807051020840c1e0502504007407039140000e8200382c007a406a00803642c100b420f9020400700b40d221000059200f0010403c550a1042881d1002208034005200c0c102820020041c0810b0140616981c00c1c020404e65895042a440503006031441e041150001b0042030b01050502d4048141d1b582c40040141d00e2608a00f8042c80100044402040310213002c4022001c4140401032002444801500c0c4c401042d20601c138600540c4d00400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 105290827 1250 105289577 105289627
    0x61701050f0a020c0313090506040b09090c09040c05090405070602060702070b0307030f1e02070b101d0a0603050703140d090302060405040902030718060602060f10061d040501030602 80
    0x5410304211000d5030002070325410100740040162207031040d00181e45103106401c4a9440b190034000c00041aa00d5504028401c14060740e040c8000009001400b0300b426003965517200581080b030132101c03141072000c800780c2e000780a0765884600760f40d81c10119003c4001035500784ca85030044d45003031122640410410ba0410307103a2000f80032036880c10b88400050b02001d44500109616140f0a1540c600c054003c40140c031f2060020003000b0340e89080e090029032020b102110440d000200203004450310040240480d0419065480030310031000c041e400485004100f1807080d92f5a40c40480810000c010000c081c3d8840c0d94000700c205c0c51140460700d40081d1340626030412000c50404d0005885400c19601110400d0b02d02084621107440020701b0980c203a0808107075a032601c02c030400010360f69040001112001d03000d94045868608040c0c5141100b03c410301106885032130100100381c806c00c8402101840f9070315460005800b00005002c4e6a0203900c01d50307215401052044460b410700c42141e0315104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 105292077 1250 105290827 105290831
    0x4050f060c03090a03210c030b030c0306010f030807021f0c0201080a05100603020a030e061312090b0405060a0e0d0c06080c090a031101020a12080108010605040504081812010906061701 81
    0xf610310b221564035010a1001810400c1c40320300a0741c3d2400c1c120714a41a082c00e12000e02c8220381e8110000d008180c0340400070700c01d210b040f140210f01d007400300b02036041c0c44802001c41c61030f0381942c0701c1d9001c40e480344108a8002c0016080240c2c03440308440248400c0c07101c1d65528101c440c050000402d908000303400328511034500380c14041184205000758007114082c2c01d0140c0c459041d80015002042c05404585450140004000c1e40d500d44c07404a2413214070811492901d04200e14040321100828044c80c04403c030208400c2c440c9180034005455004010310b083d00b500c541c84c50118228070341c00c003012a41507100500a1081d01c3d08500380d2a400004860301d1070034000e8aa0014480d003405220244c12909095040019a4030038820031a10341d030440e02403441052003d5009080410034460340417207502e40b00021a8510b00740c040e030782c0500d4010510a0030045c881c0745881c041c68400c2e458581c854034049612843c00c600780900182d5602402c3c00080c1c640c5482601d00014250f801c010295074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 105293327 1250 105292077 105292081
    0x9011709030703080a0e0f06100f0509011202060409140402130b01050f0c070f0305070306050601050708190306030c0902040314010e031911151f06020715090302040504050f060c03 79
    0x3620020503200d0540d01032402c0f6038103840d00c460000080c02c3d0024013611a0281c00058810740301c00207207940c09001655001d0405640d00c003d5075402d07024500509038444861001088a54070b0340c54212082400140403a18095446034404101c0e201004c0500707551002c54100700540c036000081c901c02c018180d1051062601020000b4401d02c50a070310266249404600382401110410040000d420040741220b280ca403039040c01c0f0f640341c040303200c1100e41034201320002e2171551286003074451070740c2d22201c01e60407e00340454000c3c40041011158080582e640c2001000c24041c02801c0014401120700582c0c1d0380c2141000c50401200901c4840941e0520201c0007030103000208a501680d00c40400000b07000340024100c070740f000101f008080c1c2d4032441c80f18402c680c40a61030741d80940031811141c43c8403e5031402a4030a103034244079000140e04800d4080002400700c6c0100a0004414546520034075100e40c00601200d405490503103142d8440600301c0340d949002c110b042d82050310300c2c0d4941e041d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 105294577 1250 105293327 105293341
    0x402010e03280f050a08070506070f05300c04230901170307120203250f0605090703060207060203090c09040503090f12010518060a020406023403050102090117 70
    0x140d1414044100100c907024400040c0800b02841c43d00155100c01596040f000904024499400c9a4000e903981d0141b1004111986e0240c2c0c070554941844e9228030f4141a01100401d000000241030032080c841072010a5818510740e011846c8640c581700c07400c60f11242807603240491800001101560010165a003941c2582c4d00444281110b003060002400030041054070b60540c017030a14000e0441003210040b041c0150080094512100411100c100d4031084004200c01d26901d610b0150042100814040104460760421079024110350119030f0750540c0ca58401e0102c0c0d00c10300043d151240d000c024840413440600c4400d030050300c200c5840b803a070b05040c0c850949038400c002c1c0751072107886103801c41c410321349454103107954840d000e0000300490b241c00380390141414100155210030b03003d2100000c00c0c044c2e0300d1007505c098403c1a4010b1602d480e0b035141d0740d880d001601d020711020355001c40b4560307031400c01d140c81007002d1445400056100c40820001614601c03084105846001c280801c202032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 105295827 1250 105294577 105294613
    0x6020d020d022805100e0c06070209040209040204150303050d110a021c02120d0506100201020313030c020d020901030311010b0a0510031a06190e0a0f05011101140f0402010e03 77
    0xa54021204501e000f4002d110310783c46000b0200000a240b8000e210540b5681081a0b0040100030009000c0c1c44a00160380c4c20040c2a102e8050002e501c003811074041009814142400c5a201d407001c1c000152590800d1201c3c141c00190303500440c0000c90005082803000514000d60740a1100e50000c5424444540700203525034140346000c40402480f1110039280070f2080010384070700341116600569600b18144a50085e0000f00c41584c01040500312168011748144200d92244401c41c007240c14080d40c641c2e084070f40840e00c0b1803d0780d1200d1204100800743e56002001030082d0320a0316401e4408042d030b40c6580c29103410340146440fa03005c4980400c500c9d224020b078855020f0380d03442c1c000785256140e41c0c4408000380c1010107a400003404202840790211129a03c49524a280c450348141c40c00d49041003249032050181e00303066100c0150800165000d0071b83c1c038842d400721348004619503440c12440c07107500344210f600d0790040d0a40001c0c002503580004645003018402d40103440c90644021007025 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 105297077 1250 105295827 105295843
    0x1090b0c0919080a0f050709110a0f020601050f10020703140c0a0807060207032d0302031c0603050304050616050105090a11181506040810020d050105030a11040c120507080106020d020d02 82
    0x100e40851759041d04200001800700f02d02401c2003040070000c10151200241c0f0641000e492180815048602404201d0000549038100e400040c50301da034285140081c040f600960300030050551092040103c0041e580f0a94a9034000600b0010700030f07400d0003810070203820b03029886660143c120030020300004d50301003140c030280c03900190030031a808841080182181119103100b01000034444010b410154084000d21021160344c000c5115400504a840b04540c502d200c000c1040e40100000c104508002002e0261014004080c802040075512401e0940b80121100c01640d0040c00094042000201c050000030409480881c40002d002c858001314038005480b0705040c3c0c0038000103000e80c0d602c00c021600904a40c0f000d0b1542c00e4440304044010790080c0544c095207030305210021038241400244001d103a9002080d03200c003105c903034007400f000b0020b180200e01000004000c5c0d096030600ca00406004000360380c0c1d00c000c150314104000307003055400c00b040000c540003041c035140081d138000b4040c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 105298327 1250 105297077 105297083
    0xe0a060902030706111504030e060c01060305060a062405130915231210060b120703090b07080c0403060524061303020f0d060608030304110d021503040501090b0c0919080a 75
    0x4445403a035040c191552100030260032b500000c0001c0e6229000010740000d42100d00c0351045a074143c03a51000c0c441698814002d00c554002d826086c42450702503103e00141c0b011060400924141c907000c2602e040c000030b0b800c040503054407942d0488001000da0385c80c0b001080c007039440395241040300e455050034006e01078400e03100d0301500c0c030742d000a00001e1260305001c03420030f2030030403640390f0310a0001c0180e01310046d0583c4480b004000240f805000c1e02a036007059074010780010b051342d1019003d4603594005801804095010702c4044001940b5103e802d000b00658036040c0382040100510030309da6203120384146d0051500740915507051440960000035039a04459054414466802040c04424100b801401203802c08500084420700400218001c80c0101c000100d019800c50900c0404c10075080025000142380640140d900f0200c2d0195412622a500106211b245501e81d445941020780e50340d901c20302e000070740d100340340f40c20045100c2c9000a0700e600f00000740380100d040d4813030418031005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 105299577 1250 105298327 105298363
    0x30b060f07022e0207120506011701090203010c03060810090b011211030303010306140702120307050c031201030b2d04111903240b130b040e0a06090203070611 70
    0x88021542d4a400ca01c1d001200d041c01c45521602c0c40c01203e0b14081816100710150260b25800300d003030102c621a0b4084590450700034485a481c011031424066104070010209540e02d500c10401a41c00380501500f0450568012503c1400d00d0b4099041010001c4070503105881c000f04200018840501141110170602c8030700712200684c00d041c4c3c402d0030b2010103180c2c940000000801000302303941c44484090382444460013035940300f100c140e0366401403403003038a14941e00740001900e0510410050107403003510020b490401104881c1072510f02c00a03082100c003d564402041114810742c0c400504400c40d40042410303031104079038488030152000d400900041032010030f840b0ba64480741c4d01d0414a02254003266025640d90610040503070341c43e0a4090524682003001c451862503014041190600030007480b2365010080c148401060301d00c030555005500c503220070181c1c0c003044c0b000412160098801040700e000c0c0c0e1041508001c01c5822940c180002e01c00b074601c401da80010386000540c804000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 105300827 1250 105299577 105299587
    0xa0b010c020f060409090602040e06060304051b0a050d0b160201020702013203090d030c0305042001120c0809070e0103050d0309080904050c1308010519051005040525030b060f 77
    0x4592940306a40110003034071b051889a9041264a030300030821a082000c181d1650780b549400c20000b44800c0e07902900075031010349081c070f10802d01d10a40205000c0141511b15059035403001c42c4108407440001d039000524401000200050103485103d0542c0a2000314541840c560010b00781003216580f10818401c41001e14881c440010034880390050040381c05601c0b86010110f0503a00e0708981c088000007410070302c9030b518a034003034010700d070140707501108404070302040103250392500072902c1c11f0303604020104090391040c52692280520301e03105070b0356070440c502e014043c00d0324040c0141e200c03130040012200104080b41d004512000c12003600d14000c501115203007840c1701c1030f00075408015405440c00f41849048503044008107040740740100d20290855030740d4500c41c00c895080701e01c0e6101005002c444c00c0c50301d12941c0400c0e800f060380d1981401c110303111030201d001c869080f1002600c101c841010720405024003034801041c800396190910104503408013043c001c1c0503e0101c0c642c060400b040d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 105302077 1250 105300827 105300829
    0x5060a091a04050a2408040c06050306031218090105060f1204050a060f140f010f06030b1903050a021e0f130b0904060501150e060304080a0c0506010e0f0a0b010c020f 73
    0x2003250000c207002018400400d8844406805e0b218078034103018058030010100c91101c9020f58561031040e90003a81c189605441c1c100152070a5100404595041c0103400e4040c000382000e001a20300c000410001d0b003001a890740501800034410381102d8480c900c1809590f4034014a101143c2c990400040c3d07009c036680721f0749442d6142c00c2000348000e007803d080100105030070241c1c2e40402d0a6090103c101015919548400000094280030300c040d0402e250105002d401d0081d0850b8101c1c5a000c0e040380f00c0c00304000300352800d80b221500121401d4014101c0e410035031600080c5000015159517803038903030019060004110548036182c480c080d14003e100d901003081c0c00d5121441603440034000c05403d1900b444c00700c0c0244800d000d0300e041700181c1c001c40c1c0e05803881022019602000500f4481c510f031156250300120790040360414041100030740540d80010000d10400703000b00282c001e607079900d042ca0105440740c148008e10a051a9252109205090b0f901c00d41016011340c06484524450301890 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 105303327 1250 105302077 105302129
    0xb0303041802030f01050f09070e06040308030c03090124030f0201050c0319140f041701110706150501110307120306270e030a05030c1c051602060105060a09 69
    0x540300703800d4400000100c1c103480d0740d5500103500c41c00070182030f07541da42c0c0c035101045141303c4400300c980d811110b00c01c00280118010544a9441ea00c024421f0303041641d6644e4102a5038001c0390107000c0d1080100c140620314000b401050501d070340210389240f51282070702c075600c0d483d00d1910000d080d00c1ea0768100b50080d640108200c9420f5000b00b400d80391b890294140b4a40851040c1c0720080010315403c40d11300c56004410705455a07514030300e4104e4074181c9401e4039001590118424291155614881c02040000d030308028807101c0e2107824046040c442e180c504100303894040d88801d0500203540240c519080c07020085032070203a80410103a13a14640781108600605640d084031414113502003102a07400c00c49002510485400030090001c171300100045600c07806403000e0a40440d00500105401801d0b141c003814440000740e003600740f44040321001d54107a03402a50a800070038241800f04811580c144030460260400b900d586103020416100184070b01c12a105148215048042c2804458012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 105304577 1250 105303327 105303329
    0x110318041103090114280b060c0601030c031b0b0d09030e10110f0705150a0309080d09060b0103050702060a09140d05190804020a0902030703090f080903010b060702030307060b030304 80
    0x5425030307910b034581034000764028540d000070118031041e48000500c06564521442e1195a050361040e40380c8400921900042d0640701084c80d4040340911480e10810820001c09000714002c0e11038050603032031400c1c00741102c1c10070f120740240940d140740c061015100d030000312410300d00300b2400050f0100603030508a6251014000307550b40301c80824002c411080d030210b000a0012420380c10b46940c011000c8034180c2d51102449803d03000441c00800396500410200a884420414100841c1d24507044c0d86060302c0303600c8203200303490b03203540c480400c02841000c1c81880184071080c00c00700440d08080901a581e84d40061600340000e131155030302004c04c000075440d01d80c42c50280f003c80d481002e160901038400d030401e58080d004501d441510000d040e1050500c40d01842e00078144059407824a61340001030f61005110100b45501c404e890000944041d2111750041d005a44864a5400010415013514050032041d8030801040c855280960340c0401190740c42a88034000148110040000c06e04500407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 105305827 1250 105304577 105304601
    0x80a050c010504030504060f020109050a02010509190603090606060e0a2601050a020721050301052413030512040b041203110d0305041a04150b04110a050702030c0111031804 76
    0x2c180a1004050f01704000d0415140207403940703070360300301501c5040382201d0200d407010700650310901050025500800051611540141000c10084a50800c000c200c007030551100c2d0000e660368041c5424841c641c0700300e40c040d0200346040d40010300c1900015803003440e68041c0e03d0343c0d40130000c0d100394031184000922000d021100000d02c414030b002c01c0020700940203001c1c141c40c0d450d800541703500050310b1001002c003640b0190b00d1700f40c20b513400e11052001d500d803151054a05040c140003849060401d00700034141d0128101444180582985081d5091040311022800c1080c0280301c00d01c0071810401c25034050312001202100074120070f00f002c44100b100d2180c0511240141c8010090555168001901c128040d0800e40710007010900c1e1070940310f80845000c1c001d243c2420703040d04a00004e401a0510310401407011901c8c086001d000384403039000c4190f01021483c0040d201c030440c14244610700d1580340034208451100d90114000c1e441e803107000c14501d10000089612070b455660780e4410026105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 105307077 1250 105305827 105305831
    0x604050a061a0306090604050603340305060601030f02040501050d0f06090212010306060501021504020d030e0306090307030809010504110913080412051b06041403070510210b010804080a050c01 85
    0x7070b00d18a9515683d00694036540542d0241001601c10b080c02c4c00b94502840380030380244085008602c98441c03a5a81030811900030000b00888041482a020400c003c0c40c0034101800c01d500b017910000d0119000364400d91021401440104600c1e078000c802c0e41c4d042d0360034840124110381100c000307100400044e0050780c030781031022440710104038600c58032034140e91041004010b981d403a6001079035542004440c400c003107a2400009401070505040d9150840d2203401c4c603035000f07070724440000c2c10403401b00c4601c00d09900c0881ca590034968014546500718900c40003c200e5814141c032610b000000007020740d8090b80b52000410a1030700ca81d0283c042c03040d009400151125114a03560b01c208030480340a035028800c400540420848040703031404142001485585409e00d07207020011003211601825606003e0383d40002a07070f8660304141e00c01c1c450156104211903803c140184803145021201c860251300d841c1290010366084100c064001d508041c003d629006001c1044a6a115a0148003400c0d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 105308327 1250 105307077 105307109
    0xf1101110c0f0f010204030c0b0d0f06060203030709061b0201030905070f03060213050f0a05040507020703050a0b070207060f0203030f22030807121a0f010302210106020c0405010303080604050a06 86
    0x65004140300350880118815540f10744101d001950913400b4901001d800d00541741410418070703030f901004182140306940c01051510f0781c0c3c44450115100d5500031400750b04004100502a640803152001510b035500b02207914404941d0180c80040a128009040c541d46010a0301846010000e0100602c20305540071700e65074a03498200040d4024003201d00f404c001d1214041220314203480000d0785100050446800c00d4504030070000500780181501003076000301c94021020900522010011501501da880120700b48108000d1420850354002c4040026040e10000171680c00b000f201c0e0403400a46000001d070301d03180c51401c41c0710100c411845510895030f10a408040d0401c1400c5c0c8600700b03a80301d540729028038650240544a4010f8004181409043c0f41206490704101e640c0d01c0107010726005040441c42a031042c100d00b01c162120800f540100010000513604004003103440e401540c3c248441c0d45141c0c0c000d403095070007400b441e1240e602d07400040c1d00d03c007141d8403120003000c4000003042c0350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 105309577 1250 105308327 105308347
    0xc08030a150312020105150306041106090604090b09070921060b0d12030e0304080a15020d05010e01141509010e030a0210120b0307030803040f0326090d020109030f110111 75
    0x1040a043c005003d94240300006131000c07409072444800140203405451160342d00e680c0c110000c4d031011720184d0300c00e07000d2186d1407076078480d80080c102400002100042c036181030310400c0b15280c0010441000c020050506000041d103c0c0500c810140040ca03004500c04650701c1d0020280c009065155005008102444244802502003d0740c2120b01c0d1000c10124008800c216103034490b5029916540c0e01c0b2068240000d010030900c801d8100b1080c600509001450341d142c0c0035590280e20020034429200014004480e0368000051699412036401d00d04245400724400c060085c5039000d4140f10110900c40720984041c420600520340c01040080b034010441c1000e450415007104444c64980380c9070002c01513003800070320b00c003d82c0c4e0001042030966840b0b988811058506a0b070840412050010340c040340b412504042d44061025220a49249440300495160140441c001011a07060000c07580209401c0300d0b05078068405071030b040000071030a00004c1d024110269042040100c000742400300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 105310827 1250 105309577 105309593
    0x1003080a0f1d03030a0c14030a09030201090b03041a06040f0e061f03080d020c03041802030115050924070b04110f0105031b130302030a0507140a060c08030a1503 71
    0x2800c1c5040d112200d0214181c84144400800910040d400d40d004008041844d4010058021464842d0444210000e0a040c20500710341004164102007500d1200600c00c568002c1006001f41602602d09800e44c9000e44903030300444a4040040c002e020403c0c0866010340b1150451b42094540aa05005184081c0161a6a45800c9031817500e803c11810342c07500e07144414000d100c110384d00001d0050624560301402c038000d501c60050b80c5070301d100402000410315440c180584084001030401070302d81d80340c215a01200300c3d4044448040100820850441d84d8880000400d0740502282d039282054800101d2003c5100c0c1c03640140c0190f122404220401031018a088100107081d1049542204090300542d660f010603034400031141c2c2000891464004090043c002c2d42074a603035006d00003170340c1c0d401181c24101d130b0b420709941c690003201c01030050090310805010615000c0c0c4000200e10300d410002130104c555050010011a00040401e042401b250230030310900400d00844054a940d81c039001c0c0e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 105312077 1250 105310827 105310847
    0x904091a0f090606030705011706041e051005010e0d1b090207050c100e01051b1509030909070516020418021f0201050705030105010e101416050708071208031003080a 73
    0x3180d0b03c075070b0000912604021805074100c03401a1109030342510310001d0079000100040c41d45800980e10001704040441c0c020f0000030003401c055001079a405c05440001a001180c0c0046062000b0030f8110643e079104d201c645081c4540010040700050382e82c2054518000f5251308c001500c41c004920030082c040e000c568028411411112140c82c4841054160740d0784031210784140c08604140100c1c89002a0b1224911610015606590084194011100340104140c451130020b9102140102c41803c0402c0360301c0d0805500d040807424000c0c888a016042c2a12a000034010b03038071417009054500d0024240724038554014154407150f510080800c84034000104000c2c015801c00c0c01182040d030040c030480e030680d503043c0c0d1107600340c8030640700740822001c1c010b10100800804094041000e0074040107001801041c403110001d00d100c9007040c0e850308000b070708400203e40040078200301041c05140d141603190340c072696a42e142c0da03e02d800f03030808602551000c0c0c410800080c1d410301c640d5021203006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 105313327 1250 105312077 105312091
    0xf020904060504052203110307060506090f0c0423060d02071b0b300403030b3f030d090305090405011202010f03050c0903070f0602210904091a0f 64
    0x841c69580d60100420780e1000d40358803040c205900301030b04c2c10b060046181e01c510b50007814101c0d894902c046510303145601c0840706585c865603400c140002860300300c103c541c110800303841c03501007801c1c441407825651251388900c0649002c4c40b401907140c60095582244038000c02801ea944520074001098041d501681c1c040342d11051610f030f0b0741d000900e240c0b410403d80f040300d11200d0425140f40c1c50501c4001410301c84490701064a0035514865240010851103148281c1c1d011402c101c128080c800c80b10146076025250481040d4004504010307a003885503050100c640701103c01e1010b144441c00d5120740d100b600c02c01030130705544006141d00040200500074060303808001980c0d03120000b800010741d10f00000d000900c0716003510b00d480c0c4250006d540110942c2d500d1868000010700007898075540e039006041e50019660100714158050101850103030711001c2c0b01c4844c4070b99209098017440380080c4c03103200d690303140650000d0081840c5108024810b01079001c4480c00e103021511010201140c0603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 105314577 1250 105313327 105313331
    0x31b01060b0a0e0d0c090f0b01031b05030604091b0b09010e0109050f0411041206091203050709170109080c1608010606021f0f1107030809060c0406120e010f020904 72
    0x1501c1c800800071034651041aa40341058114001c04101520b20b940f0000d03241160040c1c400b0076180168880d60b80040e000040c0000e00544440000d0f00343d41154444641181525050601040e08070040f03981c056400c07500090100c1e2189000c0501c405080400240d680c0c034000045119134500006145016003600c8420301901510011551805d0b03034040d460f000601c1407a6030702103080c00c0e0000c0d45840640748405003000c1e15508a000e0b2170341e92420030780300c194035a0400010300420003d0480420058a400d2100f45042000500030fa042c6210f1448401390b103c21400031901c00307510002c0380c281d100b2070f1143d842001e40c0302c941d507442d20308004148241c42040300241c1c0c10414403c40d4102c91140e00a0214034241141c1c8040c2e00784513180c44060941c848a10b92032000a41c8104041d00307032040c7c03060f901c485003030800400c802d0004054104660152060015080000040d6411102e0910741156078083c503500040103080d130b00c0140f07000c40d0309004c030070420b042c0284c000d0851304400b48d81c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 105315827 1250 105314577 105314579
    0x1704030512040b0d0b240a1709030304080c0102130e0601020c0a081c031b02030a120b0a030209180a1511030c070f0305120118110304170c010e031b0106 67
    0xa9407501c075510900301c0300e4108000102d8801c0068104204458000308105040c03404a0f01040014807200000c1080c2880000c07105100c0342c202a01400241c1015601e8502d841c040900e03139964400948050420b00300810790140b107101c25011030340189a40e4100c1c0344016500e10711240d813420240d550354054014503200402d60b00304002d030b0008030fa18010041142806440075030079220303406100c0008240e15408082200e00c41c1381134084c42c104159004642d980200791004168010b070241031a1000d05184400c000740d590780c04000306981d011201580703207403514182c01c0c07802602c508000c0316034040c0c41440b070140b20000c03854a0801c0880b1106210361005910742e902140301c00c5030050001d1a003800340c0c0e000b180074500050746891003410401d25100508040020141090740401a14a0071600c80b8040d510580100c080024100ba607107800c5040598415148043c112a0842110000b1440c20052842500000c803d00b11b284252036230781c00b1001e4180d40347c440c0100c0d010202c1d820400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 105317077 1250 105315827 105315853
    0x1050106030b0103330f0f090e0708120a0912030207140111060c030c070803010f080d050a0c02040509010615020a0219030b040f050c0a0b0d200904020705030717040305 74
    0x10b10542000c2a0700360404241c4e0319001d20717401000c1c0f10450301c083c9289080c00304006404520840c0074103411510030444500d001100c40545900300340c002801c4d040804c0810a4040000b9040040000d80d0341c601c1d11400702140454060b07003950301c034028520b010700b80d2205041d00421000250340705d601d03802580d00e0a0b1001500c2605440000b00303d0f90f80182c0003d41c0c44141d0602a5411400c482c401d40e1900000d91100c90094000381c0103001c108004180400c000c6504004d0000b55400c1401d001e414070010181c098600358011034041d0040d52160000707480300c3c0080d445000940b01e50209196102100c683c0207540d052549402ca004020201c04003c503490112a68411254013046001c0503643d02c0c1d4030038850131034140c4112607602c0348404c0e841c0c00d40d13a014559005042c680312096264034600c4a104241c40e8441c0702d02441c0d0380c41059080368240700204440d4104015200580d0720101441c1032890362068070b030040c00d250f80b007600c00b4060046c04402801124007400c215222130795800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 105318327 1250 105317077 105317081
    0x50904060b031605030a090f0b0f0115080a1e05010816080c0609060c030705070b0304050d080603031e0c16031704060503040f0614010b0d060605070206090103090c1701050106030b0103 81
    0xb903543c10076680a40300112400f4465401982e1100031514080707062030030f55a41e0b51104450690841e043c09081082101d0b0103814006540100200c005c1031403c60b18404010704008000781c03103c1d81f0302e5220300e40030601041c0300300d00c0440d81d400b82d8003c105561351508050344130030380444004584c0704401c000081140c000544140740500080200f4508903603841040f201c0d900094108105000600c082400315001b845150024640d82928640c2c03882c09107425801e02c00404c03100000d0100b03034002e02500ba18008103035203800c019a1000a9003080d0080d01d44035601685007620154415550584441c00e02d10b15046e0403a031140040780b034034a443c2d0b00c1b10204c902640c0613250000308144005000308584001100220340241c000051145c200c42c114030b00000c0981040d01900f40002e20201035412500c2054000c03d0f507840c1183c241482075000a0007841146001410140c40d0f031444401d005161914000a00c1d1070342c042c20034140780c0740009028020911450012a14208203c1420b501138 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 105319577 1250 105318327 105318331
    0x1a10111207080d05040201090b120f0a05040f17040f0f051503040308040b04020a050409060c080106020d020312180d0903020108062b0503090411030a0b0607020108010303030b0103150303050904060b03 88
    0x10685041c4800a0b003424000c11340100140c1c10081a1840010381032a80b4005041020300c5440e0341c500740c940004150302107640a400c09200c680741c5810440800c0000c038020130030f5580103004101072480d28003c070310b250059804c15032000180300700002e12100c64001c1e50b011100280d407204038480c04151529914003040b075028020404090010300024040f030b40083c0e200b0f02c010b0440b0022900c5138045012114010012a0305a80c0c65140440e00c91700070000ca801450303144002d25200b481424003e4880c042c400a8805590503840840c00e800064180541903810a0044800710744d500305004001420602c01070b40862652004142e03982084c20610701d0840900f0704030828031201181c1d6103c0050181c109031801d01050001c6003241e0380c0c1d0b01451900c2d07820843c4807516402d03c108905d08039500d03d40c1180c40342600b0003210b030046c0d801c00410750440e901810002003540f10000140c0140c104000340c2010030b0311400c404010180c100000d482079500c00d0b102080b4580c4c81e102000113034441 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 105320827 1250 105319577 105319583
    0x40308090f150406031a010212030a0e1f020d1401080a0b060a05030f0a060f180809010905061b010e03090d031d06030708010608090604080910091703030612160501031a10111207 78
    0x9c100000740d00e050040d080400b5681c035050895a0504000d000c003c801c0300061078003140e03d0380004e4108100c101c203000f4460050a540c107200c026500d04400d280c0d2340d61902e1401480b803000c040c00142e266848904210040002030103030b403032a180192059031038114094048070146c0c0361011300400000c1c28819103c080d41034400c1c0880152654031881d0b1190449441c1c24100810103001040c00d4551b0305c06840440ca03242c10301c0b00c010780400607050940d41751554a100642c41070042e07032003556450321000d240720b80604104a40d17914040f03002c1c190f06555030304141c000348000140420b0603031008416040f14041c0e50f820fa881c1d00c40300b8416803141010b9901401c200e5082c0309504080c688030341c1c40c01e440051401c00140c00b41d81c034461994490904041030f80150804810001c0f2070500725a1502020b1040c000703440024090440001410100c1c0100c03810140d0321869001a0208443d44a0690318001c3c0018081c0f1400440148004044c010300f41050149100310002031442c02c041d07901e82a8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 105322077 1250 105320827 105320863
    0x40e010611010e01110a1b020d0308040c0914070905040b010210021b1c090f06090e0406020d0228090501051b0106120b100b040308090f150406031a0102 67
    0x440c18004441c12122803000450350355072400407800c030340001d200d00ea40c0344100c00c0303000e0344400c6000b001400c101410503108402842c0824920010383d00c131130300d1600c4551b15007021019501c490601d5088100d181d0043c0350031510b006451546031082506081c807440307542e40e46244003501e4200b44000c0e03c1501c15a02c0c007580c440d01203004808501e401400c1c000d0345083c44001c201c4561030110340740404180110120020b402401c1c103015038442e81c1c40c0302500d00c400450003a00e00d4000010100d0b41507100301954485010085010460039070101c4111303c214140c2503440d104a610f05d41c2d0000e14a1300b00a2000d410f100561800c0c501a000c444c1c00c0f120161a000d04040089404149804c4241d042800035581ca16021445180d40329440f1070740750241122003a02d00d002408207990591340c2d04601010341090100700005004c4030201e8506010a0312418074884006010403aa181c00c001d103c409990007150210f021070341a4070800c0c41c480280c0d580d0b810045d4000040e030f2580311001001e18400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 105323327 1250 105322077 105322079
    0x1a0403020f090402040b180f09011b05070303061802030901050a050c0f0c0703050a05070617040f0f0c05040501080a02150c0322080601060e03100e0c0114090603040c030b0a02040e01 80
    0xc90400302c401da00500152020814480210014844100c0070050f0038511380c03c4018841e111004003503540d03214000000800c00c000b80041d9045403800200750217810450006405070805119800c04402132000308070a0b483d016202da100c1d03029400803100b10300103601c5d0400040e00c0e4180340c000d290080303107520b1b4014604070400304006180d9002e900020b505100d010400000960104045600103010354080c01d503541c2041c8000b400000c01c0c01504407003510100c2480041000c10340b0014036250b01400e220252142440d02811903070840d4489503015190500015018070007095401e1518803c0b110200300341e030718000a0119000720700c0c40c1070b1641d0003030184030044005851510000c45c101c201c60001e00d583c4401c5280340c0b01c8243c2100e00001d081403c07000041c141007040f40030b202d50191051000d4030750703034441d550b44111141c1d035981000031030b44448001210709011110240e0b0040d040c1d82d50391400c2d090854000b1024070040303a1405002c0e001600c620030f130740b09072015900c0300d109840c216 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 105324577 1250 105323327 105323329
    0x10617040b01141224070f02030405012d020f010e010203130b180f15010b0c060406020a0c050318010e1c0b04031103030a0905071e0b030a241a0403020f 67
    0x40001c0000705801070815802480e01c480100b007030520000d4102820319171110b820281091000000d020030b001d1054429060941c55000f105450641d04286003500c480703100c640c04c42220300300d40b094940500d004003d400c0411039011070150040300c241c2000b405001714211145081b48001c492100c0140309120003070b400203e120601c950488070001c07140201007081c0480d141050702c100e10b035040c190710200a0421207403a80c0c142e680100b15440b021824010054102616180000d00042c9810340c0000c00b204031600a1000100f6142c008027141d4607030150309640107490040c900390601048140c41e0603c90f80c40c1c501840d400320a00d4081400b8105081e6a540c0c0c1c1402000d40200d00380800c54001c50113900041010b103100d01d00a0358081240706040c1443c900f824556081010ac0d00c91402e0005040b2075018944401c0b220074110b429a81d50365100d10341300421440d02c07251a11000c060340030942141303050405040d1150005083d8600c85640003110307071071059100003034110741807001100c1c0f1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 105325827 1250 105324577 105324599
    0x506070203010207020307090501031104090503090909012c0f010509150901110c01090201030617151e07080106020712020f04051b0c0a060f0507080c07030302040306050f010617040b01 81
    0x1040c4003500141c10700c2d00f03a600080c207001042c0c01403e44a542c4000400a10070307450650300d05d0391001d40301004610010b0b00e90b40c5d1607114980845005104030404a503408000758840e102c080c00c1c0400c19190310303075101941c8103d0340025019810034450aa0040c01c0300006118a9000e00104801000c3c05072200c8184492100c0003800b00c0155541d0b454440781803080f21005100e90f2811100019411503144000350407189a40c005000500752900010404400000d0030614078103296091f07140c540c2c81d45040c40b08540c1861075050f0345081c01c000d001103e50010300c5079044e01c0b42d940075031300115150010241b80341c41824010754040311042c034404545c181a800700c3c0d084600c00d007211074a0f09000d024201c3d103034049420000c903a0b124402001c1804414440c464443d82803100910480c200440c0040401074040c0c0640521000080c00d8010140241d044500a43e84a14140004c4c0303040100364589110034170602001c81c8507070742c0b9010081e41009a030740c0314070b81c00003c00304c0070390070714405541c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 105327077 1250 105325827 105325837
    0xc120a0b071202030a0902040507091a0c03070f0503030105031b060301030809031c0509030705061c0209180a140f04050601060509030a0f0804030303060f030c0905070302040905071e17010506 84
    0xa0012078003070340a0364200c41c0011807040d117040d0b201107040780c142c1c0f040c04200c0318014640d41c00c1012520051103e001c3c070180d101c43c2c12101c1400349454118501d64941107105480340102401e40d143c80304030410502002540c100c0358201d043d50002c100c1240340e0340070400c41c40340c0590303c000104010700010740c000c0b01401c02e0200250403102114900740f0302400d0302030642660b0001c03810200e100c0d4820719042206101400069408505041c0d1b80b6030000203c0405600d55588240c0108544400d07031201c500c40c0140360086038440c000d60a1000c410401008031081098a0500560000e903500078880120380c0119804402001c075a864103c0c11920794000b42c00b4243d060055210312008141c981e80700303501d4540601c0c446c55aa0b4503600d0050222503040d408410070300343c8001c0820110301400362203c01c0700c9001c04003107050307640c540c0b048009100d0b035080b40b11014a02000d210704191701082c50b1000c5088035611000001d02003406840c3c5c01103d240715140c18001100601c824200000542 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 105328327 1250 105327077 105327091
    0x90603130209040606090b030a080412030c1a040308010b0702060306010c02010e040c0207090608190308070e040509030a17060d03140f0307020609151b03060d061a030c120a0b 77
    0x501021030350350014555440545080d43c1c03042e10b906040c81800318034420000c1407034045004202d0541e40f540d039103000c0d0144e0700c00c56066414000d280814503024088907800340380c0c002d4aa51980c2078052444040c2c29095809900050b0204008540790550104440e00035400901603400c5580b03070303001100c990360190400c80c1002940b01c40191952158000c4240c420b0303064018010060801d1142d40c12109507522202159000080c14424082e130140403200c0701c2e4040ca081c190130b9850718401c0c1d03250f09070055001c1d0064500380800612884c0400039050b542060750729011043c5558048011500c0156045075105000c80000300009001d01c0301da1215a051b519480d00708218032903d8002a00100c0b440710143e040001045850034051002d00b00750402502035412038149a07040003c04402c244d2045901400000030a0095a85440c090351070340e48000103000724441103804488812526007098003078417468030741ca5410315040000c02c0101c0d5521004040d07580080e01c4405840001812103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 105329577 1250 105328327 105328351
    0x4031104020309011e0902030f0c0a0e070201020c0706031b080402031903021c02010b030f0a051e0a240e0a1104090f12020a291b0c031201030203010c050a05090603 72
    0xd900c210545c5220007029451030720b0015116146006240c00c0c18041e4250500da900b04000d809044e554085e031440640d11820002e041583e142003003a4028420441004502d201780d034400070f0720075130541280b410814580c4a50070b0640003170009503001007090b10000d51542161446810800d0b003035400610084c02881251b900045009c48001c4401c400e0840d100143d441e0022145039003400c0243e08180003102008201100c45611099200d50307c000c081008010151124803502104220f481c034503a4000003003001082400c01c0000346a8400c5001c030034400d0034100400c3e10480003041455000d42c0100c11100c02504c010b08010081000500c11070312404800c00342000310720a501d05950001c1c441d0020044406141004500c281b4090301441080c0000c200003040704810b505010b401507660004460144021000c10800e80188400d000702c0384400b240402c0b0120138610b00b079040340d000380c3c002c1101c0403001d402200c692140c0c0c0700c48404a002001040894100301008683c0300d000e803581 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 105330827 1250 105329577 105329591
    0x1020a030f02031219240603110c0f0627330907090f05061e01030e0114040204060f06080708040f0c170607020601050d14030d02210108030403110402030901 69
    0x5070b00140000303803010f90301449419401d02c40c40da010700c500c10040342440c0e0803d41c0c0300211140480d44207054047c8100305600e071110b0510b503251f404152810005134a040e1040c4088130f03054965555801c4952122025004c00c4002c900400e94007403501441c1020050035907031044c07240c5544048000f40180180c102901e200d40b550202280c241802000d1210207000580e241580500580380c10000d02c22641c0c0c81c000034015280c1e98074034180d03d4039a44a0b001d80300482e07840010b0b001000041030854642d4240000c011401e0a901c00c5580f140780f01702c40030040c43e51101886000c02106004500c049505180498851801a004160b001c0d00c40c6800301c1002100b0343e0f0342c0b40021b405034030680642500002d8a00600c90a12000c2d600550510050000e985440001122001c0d650406040c40c80c022200c110280d80910454010212030711080d51f5a20780092031586001c9022182c14150544034000b00e0840c00100440742120b800208070108002030b101080001e44c0b002c1e100389015980c84507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 105332077 1250 105330827 105330847
    0x9050612091c0c03030b01050f0706050402010e300d022a041503061b02030301050d0c0806040503070c0902030c0414040b0301110d0b0f18180304300201020a030f0203 73
    0x1207002d440b594242e55007440b44555280c05002c0d503040d82c55140c103115080c0100560fa03807040c410b540d00507411a0b0041010f403501c1c0010380b1411051802541c02c032042019040c80a82c0702c1030207080582400c4403040c0b00e0b0024102542e1240211012000180c106420030b1048006648803183e00c0600c207648204410500f04c00a411107a440c102c000022500c50030420a00805209a90490354070a1003402038181d4800000d4980c841400380d5440390480c00010300500944421b002c1c0030703001180450b050b07800c0c00e080980d56500081c0d0110340700ad00b001c0020400241c00c1c0241c81c010441c94010703504160034a001c1e4030350110040e945075003180d60b40e1400031060b52300f405858290501014065a9482d0110a00054030621641d842c024441b6014500490311482810070340d02c00c80d84140119615000b11420391000d141d100c4101c584400f142c0482d032000032180199508201c22103804034802c00303000781c84040048541c082d01580201e4039150110380581c846100007512803044d40d02d0220b05903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 105333327 1250 105332077 105332113
    0xa0320030406150b0909070807031103010f030506060a0f0302010f0c060216020f0a05030606040b04110c1006120b04150f0207060209090601210213120308160905061209 74
    0x41d000d88071180c5030840c011060491410120140c0180940680340483e4040443d40d03080c0054090000c000c2c0c10f07000509407070310a5000304d80d0340a0700700280e0760700c1d40d4504c0c040303c1400803400290b0320b902134940450f21610b00310220000700c1e0744501002880711b155800641d041a185242c04003807010359414100003584610040c002900310300c0c0d0501e540407850041c0114010303074000c003138019001d0100a2106503800240c0d5903010b2002c03600460380c44007200c0806c014218500d0018140e04004c104440d1034800401c1c1a0b8130010001420440ca0b551030003040349200201001920840029010902145c0d00c018030010501c0c0c480d00100d114018802c15038100d9003d80b109032084c650100d0121801c0c5041510b01d60495000d00e46859140800440c4802c44001e0910054803e0340c0026100042d05a00f100381c00201208845844d00014904000d001c0442c201c5100b50280c400b0381d5010311f4180905109801d88902800d03150138424407120f40c06140c075001d418035031769201d600d101c030840711074078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 105334577 1250 105333327 105333331
    0x70c0206090a060206090d03050907050607081e120c1606021308120c011a010905010c210c021305010b032a070804060f080103051504260a140f0a032003 67
    0x150340100b041b07140801c4c0715030500c00030b04910307420181401c06019840c40d00007562020303650111034280d034406080c07030078080340d1283c0752911900c00068100081c10015903400351841e48007003095000ca42d034034811080075a00c1885040c00c2c1e01103110901d000881c0b12a4040c041d02c0e80d604507003864642c2c5442c20103207042800301100040d80000200301c040303440c080c020a00940341c64010050444020000644002d0603809854100714000c41414181f00104940c3c0c03108605800d03074950b101803a0080144442c03001e90069015000300031b034412581c0914426103040b00d10241d41503086480724400030460071264028007015548000c8001d5404242d41d004143c41d0b0b1181640b1542e86181c40c01c0900041321440405050101110041012070304c0030507841200d0f071109601075070542e101d1401c144403540c071050415041d0000d5091140c50b054a10081c0740c0002303140c5a0201c403500441c000d000c0340c41040780466032040244004400c141c002c1d0400f0308019242c041081c01d582c108560905140c02c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 105335827 1250 105334577 105334589
    0x5060405010506010e041b08070c0b0907030c1203080408090a091e050601020a080904020f0c010c0f0305090102130509041406070305150105070206031b0c0106080708060f0f070c0206090a 82
    0x7441041c02140d6805c0350110041074010345042c8080300d01110006100c0510354482410b02080200040c242417148003e21400355203d10741050740c0c20a1011603550b0746072400122680c00b81c030784000ca810004500404038882d49a90f6202c1c0d290360726984c0c00c0343d5800c0714078490b401807604980421041c101340242c4a20500d00b807954280b00519948840580e0006081c041c1076401403d00f10f404074030080b04465024500b52000360780c6a030681820700080c450907800070125441c1400c51905558080082060030415941c06e102540720010010b080780300e0540703010138050b9039034020881420b244180c0f070751050248800400b0001620180d40c1085822a94000000d550f403080118144001c089541d294500386401f81c140b40d21030740030590b18030000e0502010b8a040401008250031001b080f1004944003500070f000c000e513100300c0c590b910105030003110043c2c05408000340400c030071800541e201c0c00c10816804140c0d00c035a031090350b5400030031800b0b98000ca01000900480d031a021040e00003171403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 105337077 1250 105335827 105335831
    0x80a0302061902030402090117101b0f0306080a02150409060608090709050c030606180a0b0408010b0603040309060807020a0c03140105090a020303091215010b1306020d02150408070506040501 84
    0x20704035102e04040d220544000d14040d10503c00e000c0542c07aa440d0440c19a10045102c00c6c6034164228400c0c41e14424070040c0031111b0030a24034020314480c60004400d4041d454495500550300107000780d06450042c00307405a65444030b18180d01524000041c03208005040c92036a10342511441c034501541c0044d00844089900305003070000500040191000030304a80208220b5428a11542880f030711014116a1042d40b01098041c0742000044c020038a49400a1030f401c442c0d9502c03d01c50019400501c11040c0c203500c0c0c612001c06a0421100700c0388110b40c555280c8600324104982900c8008001c1e003600110312480740170324006002800d101010b14004c00c0182c00c0c100401415500791040104181c4d00340c0c101d44180d80041c0c40c004280c51942404807621060032624407091441c0150301140031020a15500c000681403480c0300c028000c9203030021104158a45846050341d170b8000308045540164000a90300804c800200750007078105200741402c524258003511072600d410703000d45d025681c0b65 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 105338327 1250 105337077 105337081
    0xe010c150603020a08010506010206040b06180f061003140601030518010c030911061e0a03020c030f03040b010f0303090612020c030d06050a0f14040509190b150d150c0207080a030206 80
    0x8035042000f94003c08603d170080c450b80c80c244000031f440f50405003004042641300b402040c125074645200c55800c90001d00740c0d010624290b102d043c11500c06031003c0d130041803076544280d0b0451103130041804c03410081003c180b1071349524004400820b0018035402810510201d940b50001d0280030f4441d001c44540e6000c15840800e061101001c20060009031003004c08002e05c5151843c04400888220b901c0201d15880f000c1b48042a0080e21441c00301c0c1c20540030000d0007012001d2104051406140146078000742d40e0f0b240c00c004e00c0814182d01000c0d01180d80c0707680820405101d22203003032030003c17816409030511030301c020b006155400c0421445078664444000748272504040718060300900318206003903107291901c1a070113100344c45100c1c6540500d449000003440c0c3d0b00100604442e8008040078011418400c8c01e001c0c0307503d442a02d80d020001c00e4284070700480e01c4c00c10184c000c22600b042c4104415501c0c94804002041090f2180302540104100060805420701c0b00c10703c0396020f900640f10074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 105339577 1250 105338327 105338329
    0x603060109050d0b0709061b06090c080106120c0501050301052d0607030210050907180905240118020a09060e030a021201020a02060a0204060203071205090d03091701050402030d0e010c15060302 85
    0x1003130147c21200c00c00042d004102c6d40350716120221420141c00182c0060a0009801d001c4400c480a80280c9450f609000d0300064841d8110380d0054014010400f0b200b40320344400044819110a2068542c4030b01000080481448020070420400c1c2036040c605d02100c02c0346002c0390003034200c004290096040080c600f00082d40d1401100da00002c8500601041e500f058841c3d50054170116440d51001e582d01e440ca410040c08010806115114a202071a0940000d04482d8510341c2402444041588410041508401c070b0081d01d16100c65034880710700c0c04e400d11100700d4090607a045616898803c0c2188800075885281001010140d1040050380d035428140c0043c1c82e122019154040e020700c10802008056804810380b5030580c0d1000c0042c0c1a00d6036220221a54025846c0703107503100b80c044000b0010140c0203880c0b2402c9912140c1900850b6074183c10f21406c8810898010b5056080910300d602d0561148003521103010b41418048400026501d9030b101070010380b40f5244510740c1d91072060041d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 105340827 1250 105339577 105339587
    0x11b0c090207050c0a0303050a0f09090e010603020312040e0411030307060e0f0705030a120305090a061404150b090c0904020c1509160f06050f0c030705010506040f060506090603060109050d0b07 85
    0x10210096072044001480d5a070010064818031501c00100700404e11549c107a5882f03480070b00020a00758a003800819503003d10240204260300c4103e100b881495502e12000c0d40c900d0960382140c81c5540c0b060903035696519100e01680140b5076035581804100040d01c0015014424401d8041c02d4500401d8007c14411101e0300d4411f60340c000394400d07409501d00034006803c82c18007806d6940145004141500e03910307070681c94900088002400c160400d08100c0140400018072071041d4007640c66444503a0601d41c0383c1c82292010501c003a0402d419070001140084044010b14180f80f000e0401460f1240312404141080900e4400102c0107a00c0003e100341603c04203c2e4000d05554080c8804410385801d40d03040a141942c070994003071000c081015100c88494100ba2007540d002c131419a6510011850658000c020803036440d48182d02c1c0c03107103201075031206205443c251032001e031007a0314228036542003041e2504000e01c1c4a041102007000441d20b074565000d0701c56550f1003500d1500745800c000402400b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 105342077 1250 105340827 105340843
    0x4050d0c0302120a0b0a0f060e040303020c0d030c170402030309060c1509030309060703150f03150501060e010509010804080903070b0301060305060603040c0b0c120f09010e0a0e06011b0c09020705 86
    0xf007a400a000707040840c118404585d001903c411001030b00c850741c16a10070140100754810022020740c0320401042c5909a00203040c981d400c01c054907012506400706404582c42c10058100083c0303140b010f00b00c0a41001c10168001e800201101e040800d004001070050744294440c2029400c16180080910040191030350410844c0010b11b0442c03074030312141c43d568600282a102055200c034002040302e500d20b907480d4058801d80354029051078a0341066800c245a560000c02e43d545000c000080301340c415500fa144202050351040d01e00801200115544040500142da646000300081042035404209400017014038400d026121340c58004082d0484900400050049000300100700020300242480c4069849001c4010b44541000c5031070362a0480d405020005e00c4000183c2c3c802500090003e406040e609a0321500d01c02460028440f801c40c8901c189100070705003001083c480c0d800b800c0d11494081c0e400404c0300c8908550780b41c0c44c00e43c2440c0c0c1e0054200503800030300c403010b012060020320 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 105343327 1250 105342077 105342109
    0x1b0602030d060b030f1306381801090209010e0607060b100e300a03020c0a050d0803131b090501031509020d031409090108061e1501030c0504050d0c0302 67
    0x3d044d460210181003866800170804005604102da04004010a55000c8284189185c0840d051707450301c03a40d0840310070140c405400248075103076001c0307034285020210303100100d44c03102003986103900c0c004441000e13400028050741440700c5060180155180d65000c0c000380e40c028000800e1007094030f02030203240701c0c0c46541c003010094448040001030b1500c0d54002c0c0351030031645940f0030b828618041c3d600310181584030070340c46000c1c2c02d02000a1640c0000c20080129080f40c440d80f0071a81d940c00c200300710a44060080c8aa1401d000082c2c4000903030685141035401610007040c0c02040008444001070b19802c22481d80f41e40e03000600038010810009920000354160400050410f90001007160550038002030801803074005800014601e20140c1d01d0591016041408950316041d009444030300484426501e182e1145c4810410009084424043c411080500000c034505000440261007450112030620100704030018140d01c42704d00914100380500c80468050341944100325078018548044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 105344577 1250 105343327 105343349
    0x309050a15050901050d1806050a0c090905060d051c030f0c0c020f0613060309050f03091e0105070b07030b01090503061009050604090b04290f010e041b0602030d06 72
    0x34060601d00e407036903804400d41d07800c00c03c1e20b460800c0c1c01250144a080951103429040a40120800d45105513290307074030703100b45424040c983c4d4502e0050201d03601041341c80b00040c04c0d074204020310703620b0390f1107181c004c1400381003000c07600d60989030141b9101c0010612301a040c690980600440d03410310035140312040e150400d01150300c80f0b00d002440c0d0410580003900c03a040c8084190328903511030045a140000502c0e00d9404140d8440000e402440c44160580d55070007856030a1100702800b104441160000800c011002c01122002020030f501881382a41801310401001000c510710080c4075100e01d00300ea6010403640040b00004003200c1e21a0302c5240a5409142403100c0541d41580c01400c1d240d02250005807503440b00001f6014010440313010b0466030b0303248140802c1c4400d0352280d02c00d003489041d25080c1405003507000c8000000c2150250406540f0034014095120401d0082e500036000702101799200601ca02c52078680303000741d4800e00140c2e00001d400d210507140e501a1100400d845411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 105345827 1250 105344577 105344579
    0x51003080403060c0306080d090303140c03040b0711040f0c021006060207141c0c0e0f04020d02010809031e0a0908190809030f01020d02070209090a050a020418140105040309050a 78
    0x140c90158061400014405a00c2d58081d04649100790700000091041500300c0314240d2031b03201c2c0906018041d0206400080300e4002504560041200321078844c2042001103241500d0312454241c250001a81100c40c0c5c0850054481c3d16a942e0213881244801c039000050050b2001074080d2401521040c400c40035410210304004298000c2941000c4039400d441c0007480c11040c40c0014264000c216400e81c9645140201200740080080803000751000781c40c4003602921081251640700030f0468009500008010a10700154440e600158000800310200c2e0304050840b59a5148600c0031034400c0c0000740c0101c4c0e01000107070302242c46001856240040c1a0400030800540150701407500301502c074040014106620341c0f000c0006400055121000319115a2803c40c002c000c4c0d4400740081e0300c101140404110750780c81c08661425815840801085060001d90034800030304007513541181e00c5102500d00c4030220b500c441b0b440d0800d00510000064a28042c0b03000380000e46650801c03405420341500c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 105347077 1250 105345827 105345833
    0x9070807080601200a060e010c0c05250801020a031a0a2301051b0f070e06091311041d01050a0e0d1d12011a03280f02090702030c01051003 61
    0x800306401c50002c0c60b04e032086111183c0b45001d10524000c041074180f203140f5114041c00707985d6001c140c803004458024000c10b204034104642c4603090310000703400b9411007140c200b218102e8180306c1d4501c4183d0903076078413075565900714542203070441808407000c281c44801a42d2409260380781013010200845030920218103204440349499a0007410401310040c540601c01aa03004406448400306030400c080c80e6100e049920a4466030195030800b25071140c04030210b54884141556441150080d01d089107a0341c6403542282409000d14040d10f81c3c0044a8094040e40c40c2c60042e0380c2400c82c03095114034130030030301440142192401400108001d240898581d185640850112042c0c10380f845d225003c6010042604040a800302505a114441100008413440c064004c0c10704010841200006d03400c0010606440300d0010400080c0c40101e40300300f08012040c440f0b0603040074042d4100c2c10321030840b0340c00314800700410b458020143e440402d8000c08640e00340286940510019804954945165 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 105348327 1250 105347077 105347087
    0x100606020319091a09030a05010207030207080c030102040b0d0b0f030d0309170414190518010306140603030f13050d06050603060703110703110a320a0c1202030a170909070807 77
    0xa585200c13603400c0081c2d00016940c0411080007503031703000f030001c40d5a002c0c10302c0c0c043d50792400ca106403103040c094640880c00303615040c03081c0c4084405980c00c0b03900d0402c1d6550520000c00700e1000c11030388852200111185618104821030151900d07032000511104103080506a0142c48c0212070707040b0500b000300703016003020200302581295081d5034074201c440c540f032004140e0b8991a000141c016100c00ca1101ca40d00b00c00190342d048a010350010003504440610240840c10110f44c0c0030b40682c070811244018040000090042c508004044a40c00751903030006840a07145100980306503071a02c00f88451403030180407850300a07140f8203040128a660351300020585c000c0103005010f10103001c61401c0c0c102003d0044850180c1d016644925030400008020703039003460700d0b00500c101c1900c04200e1038504000a00f5130082e0388c0121294030383c07506d0480013081881207140b040341c0500034000010700040400a501c00341410002c109601d40424105018070201c000341a20100980031040c007000d00d03000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 105349577 1250 105348327 105348359
    0x1d0303070222020a020a030f05030f070e0103090b09060a060501080f0402010c081b010c030c020705130908090913060b01082818060204151103040e0910060602031909 73
    0x603140c102c1c11460b4562481212000d00c100584481c1c0006051548158042884450345102c1c1d2903a101700c003903041d02100c0c940405c480c1c0500c0c0017000000300d0071444c00342e0301400d42d0b80c01c145800b040407149965040040340d015507001c0407692040c42480401c00c080c1c082c3c2d00c0981420b1070904800d1400002041c982c00c40540064140003241c5901002d104028040300c0d00710a449610003540f40c0f100e142c00380209074079044040064504102c6010326880030841500300d8170010b11503221503240070f1188000700103415003181c541c141008045079540707848141c01c2c40380108086040c0710078030900700301040d503202244c658108981072041209410309840008840114101090851175501380c0350001010302051b003001004c6c04c0c103501001c000e45600240150f40c1030400b004421650100103881d5002e0075075802c2080e8000340418072000050704070442d800120b100407280f055191040c0c0c14101d40c00d5800581c0103030400078030201c0102e800c0310004001c0317140b4580080500e15041000440f8494 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 105350827 1250 105349577 105349579
    0x50304090c0507080418110901050406031a040606080901050a27021306090902031011090907170c0705010c02070501091211040533010c0b060d050a0605071d03030702 73
    0x18a2505504281c402c00954014a41c0b19902d035503202e03111545500c0c0551000e114008441c2441c0818400c203604400b51480c2c21411303101c41d41800c0c189401a80031b0060005007445034028038001901d5551640207110040c039294403240c2c25402d02124032030035034074000c00369410f1600f051000890340d84011815a901068004800d01d0401c60784002200780000c60844c04075142440c1d40801d080d0116404080124070803411140f40c0988150b981d400c0d079941e40e01103a8130070801e0004400d5410040ca41c03543c484c00701d2401c030481d03605040f18001400002d40d403d80140e0804521041008800d10510708800d81600041038950324040000300028540c3c0164030324160144594010802240481c5015440090040c0824030308000c2c001182010002000403070158401c822030322089450f0000c6c030404041e500c0d145141d0307050f00d44141710240501695001140c180030040801c1c4148483e186d11031042c0b6010400c2e00740440001c1070384040440c482c24941d42c9000a440c0d0395000003c4030f410740d40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 105352077 1250 105350827 105350831
    0x10503120306130c020d0e190302011b05061914060d12120216110607030801031e060c0905030d02030903060f130c08030901030c05040302030604031116030b06120a05030409 76
    0x14801002c240c030000f0030f407029496141401d026030021034001c1080e4400c2401c6607610344003d0102002c000d1081e114151680440c0b030250b90038809544500e1002c02c1c801002c3e10b040308101003d0399072a161110031203400c00c481d00115482c81d40150603009041615000b1115500242055000644298480240103042405864030340706d400d03000300700280c0c40e24108001191254400a008204080180c00c1116042d00074065103c00d454030038107454020b42c15a5840c001a070840e03944900000d50741d0407004152080214050010701c0301c0c011080c02031400d81c0d0381c02c0d402d841e00c1c0c1030519144200ca4400103542003809100120340300002c01c0c03a802480c002240260340c803103141940318031441420103445030b1001c0001240b4000000010100c1827400c1c2e13400c0040c0085004115a14051404000d5040c2c0042012401207031080e19804074510004041c0c030710714940203140241c0005280d0084412a011508110152401d442100e104854020140035410a40d5450f0f640381e100d640a8011001e03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 105353327 1250 105352077 105352081
    0x20c090403030b0315011508010b0d0e010204210c0b03090c130b09130c08070302130f0b1207030b0c030f04031115041109060102010903050405060d0b030d0806120102030105031203 79
    0x10310036004807801181c0542540c449038440f85031001300407002d0107a0f58207c0031070070109098038441c451007412140c251710403c0c1044005258040602403410700318070559008d00020421290084151000d20f03456040d1030380701c40e181c0c07800d089504402c0c0c0c4103008a036424810006030304408a0003101c418402c452602070025804013520013002075481440d00550604100000b03180345415103041c241c02074038100505c2c0d42d1600c9013992180b42d0300000b500039220140d18600860980c0000802148440011502d1011078001c01c3c24011101c02c40c0e640c96101031004c00c21300c55480c0c00c25400145100d001071a5243c0901e21000030900540020200440181c051507681018400b04140c071640c07110b0003c035030801e8203003440c041e410106450701c03030303140013021a106600500c6414440b5502d5213071541050702e04003c00416402800c2d0707030708189460308a0b0714029074041c0700100e00ba0016440e07070b404030705008081c0049130f0041c4140c20821b038410030040c02035640010b0402300300f500309071621380d480d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 105354577 1250 105353327 105353333
    0xa08180f10020d0608030307030b18040201021207060f0507030b13181101050412050102030609070c0b0c0307090305011b090e0408030c030403140a0906141e03180f070504050f0601020c0904 83
    0x10203845e070084296010110034082c04170341c181c0004514206c100c0b242d14a0344824803140102000a450007409a44200c2c040305058603400081d0002c81e01440d40021001128403105041c0c5400f1031340c0c500020340d0f60350b0615191411258400c0307800d00300e500c10849010200c44010007111601c8001e01010390900140813a68455400c881c0070340b9042450011003201d071302e001e038044d400075904c0c2c501c01d038894400204441d1282070001200c0b034200715541c6860312415511005644050800010088844000320110b2004d019154201d4072042d05602e50810700c21008002503500d401c5180701000440030320004c180c1040950750420005140344d56a92100d02e01515145030040329141c0514003c0b40d4003c1064000c140441107a4054071160740041c13003a80b03c00b9440c8641c0d00c040416942c809032200580302e01d42c010f50340c407116890707644068100c110b14040c540f8041d07642c4509182d000d0b01c001d0000781054015103800482c03000c0ca83c901c60600e240040d40b2501c403540024040e002500c000340034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 105355827 1250 105354577 105354581
    0x14070602090303040b09040606030b0f131808030406050609011802210117011b12090206070501110406030e0102122e0f05010212070c0608040510020a08180f10020d 72
    0xc00c00101204d954503610b000c3c0704441d805c90030600d07110b1450003e00107181c60081c050030a18240040c4090401c4114000f002301c000e2440e59181c03036080d900c010502c60401041c1011085600508103161246400d29041040c0c50004140314082d00c4c01d030f030042118842c004841d0208007203901003d80c50b0b0f400301c511001f00040e810200e80d8201042400015401c400b0b4913884085485400240441258114071284411140d2040310014680800562400381c5590001224500c02001c0d28980602d0742c0ba441d00795494034442d000326a10000781040301a406104030022601044000c1d402c000c500c03603000d5128000102061203003142d500021140960f1040350700d001d001120148003801d6280d4103110840102409114094030400e8502c00c1844180d20035190b000f0781c0710b00c484240c2810401c0c100c50414000d40203d0f510f2107a60303c0409a204280003428050344150358204071440e088844005140071048410a05c0d045822060b141351b401080018500164840250b55070811216080c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 105357077 1250 105355827 105355837
    0xb120a021201060f080702010b06090d080706150e0f0106050d0218040c031e0501030c12050f0105040303090c091b050a09030b090106090e030a0f0311070f0c2414070602 74
    0x70350040d20700049803041d0003104240115081d55900c004550b00c2940a900302d500e11818254040f100340448405450501301c1c2003411442a02c100e414026141d9902044e2180c1e0078442c9415a4810000d004c848214100035900000500b62002c072940347c260003800512489102c29000c0e0780000b0b48006600152082c0041080c0180041040d0800307450010001e00b1029041900c0341506420a146c0b1175103401800d068a23080114864014640b602c1d000e440b40301202c003100d050241d101004200d400c02e1145900c141d000c0d8902003550481031030000c4000e030290f00b0440b2410b00d0501d62400c3d81d00801206401400d19081c65070b660b600c002030a031180d07505030f80000d0003902c0040420485038019042501180d0480d907045c020b940309490410b481e4010301140d08000380032500908240c6101c0e8000390459174000e55818908450368031148140b81d00c1d01c0003a03400442403181044035611012440340c1440080c141243d4225402c48018642d158503c00181011000301d070a0090140d158102c071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 105358327 1250 105357077 105357097
    0x90607021c030c0506010f05061206012007140409030f03050601021e0f0106052b020402040f0602060601110303010f030f05070924080a0804180f0c021b04060b120a02 73
    0x41c280101c0e1800a20010403000704481e28040e40c400059008800344020060340c400405031814107900740c103c041c403801c000700142c1c100951103844426402014080a01c5400c0d407078050010142807031454090449198941c0c0d006600e45490000481ea20050003200310314245008285c40c0c076580300403031401c00b010320baa0001e02e100144c0d50343d0002c40000c259040844010084c04210750351010028403400c07140340c61320302004030400070150050341610491901d02c01040142466107511000d86150980c0d001500560300c0031040c40515071f0481c5818003000d00307500040d86198104280b403070301c8514610000b41a024609968800c201e014814400901f90f8000108070f0b409000004600c14001480448600d8504040106000102003440c406952708255010315084c40e04203170868040003209e40c820ba07d540c40340c0009281c040785c050700c85d500721070707600801c1c0c036990400c241d1a01d111079403c0503214500d440f50810040c0c211a041d90030f6103004081c0c0705a10369500c43e86a000e48035981c410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 105359577 1250 105358327 105358369
    0x30905090130080a0207030501060b13170106031b03020301140402130207170705070512030403030f08060f0907030b0f040203040209011203050706091203050109020c0601031b080a06050402041107030509060702 92
    0x1504e0380b59800145d41c42124014402400450f50b180000c8525108041805482c55420f40e0180103402122910441b45c42c1e2210000540c03d5498803858070b1158440c0c0c10700e02c1000024030410551a090040100c95407200e40016402c0c10554000385a9804030f0a5001c0c0c0e40c2c1c5c0102d4580c00340000e4041541080c404c0b40c3c0650f0391149a4030b0003903110101e0340070740e91091319090b0880c2c001c2500041078400703403a0f0544418080d006040701c26508036070014403842d8080b104100100064490481040c041c007220746000c40c09c96101d804104e507007031910201c14025841402007001613520848542c2c1101c1544031034048255130f03805c0031a041d10a00202614542c240a401c000300f08400402180070300541c0d804010b141d0301c44c00790109901ca60401c4000039132003a40180003188240d54440c60940b0b082028121003a5102030300b0b4104040d40505980840c0d45400708019414039000d02c2c10062403407200c851034032003a03a40c05484c90150120345801140040764420454440c0d0002c0100508007000f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 105360827 1250 105359577 105359587
    0x100f060509160306080d02101127030106060507050c060f0f030108061603050601020a110a093206090403030b0a170610060908070b0f090a0305030703090509013008 72
    0x50700c03155240c080154400030f480c0c02d0000075842c0d40400c048411b6074056002e0000c05101000c44d0b4090644031540c003803400010020584041e110040110b2504040f0002c04000d421020400d402c4542139402a028040208000e4001460100e20103114810481c0c01e00e0f240c0c1c0da0748511042c207008000201e2510400040040347d0648009003991041d00b1303140c84943c940000e42401c038141c0b181a500c0a0159001581080c005145090ba000003008080c1070100200e42e13401c9054150340f07035211401449480c03515401007181100b69044807986100028055909104000c40d061040051001c0c0405d0380c4d40c41004440d50711010120000c161189540901115501d5125200d0b0001e44036046180241c0000007007441c05408688116107651002d0b240062a2410060343c55010001502d80094104081c60590761141c1d00480603600a6004544540445c5070251280300640c01807480b4425050040101c44244648424181c01e03600c0400c0030340c0d131848041d102c0140803c4000b00b1184001c90 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 105362077 1250 105360827 105360841
    0x90c030111040e0a09020609040203060d02100c0b09150106080c0c07030606061e080606070602091e03070905090606131401091e0203060904020108180a030c030f0e03100f060509 78
    0x1c050710684149038110141e6840e615980011500101c100941104003801121b042e071a00d07901442d44944007a14103003407800e1940c0004c01540802c208440402d0000c1e09540074007045904140c1e02550440c010310301c0550345441415a004140309100030000c03100300141d00180700400342d958001250007141c4c1c1039526454030f2005440107000c0c00700003d038011400fa01007019280000c0090005884080d01501d40d20705221441c2d102c580240c4131a80c003040b0401c0c0e00c4e12203086021003161004841d4a00000031010141006100d0344542d00203800c2c0014000c01c24004940300d45c00071011242c106180c0211b994903030180a10100e40e12202d568400001a40f19040d0042c80e005200843d84081026903040d524040340801d0342c000d90420600c0c4002401540510100d5030007034020700591051060743c0348401d150104a030310032000640307040101010103410004000407611103080000c4200e2034400401e03981c8003294040010039403500d5691854001c151f1280c0c01415000d0480307581c41c50000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 105363327 1250 105362077 105362111
    0x1c0c0b24040216170d020f090f04020a0804080d02040b1804052410090b0310090605030a0305071b05060414032e09031101020d09021513140a0504021801030c02120703030203090c0301 80
    0x100341c0601558409c44881d074146440d108461101d038850b15332092076103c036151841d80e0b07044030311002c011582c20800818198880406880000118140105139070703800e00c00d10007554400f81914411138103581d4080c5445144e0384c28a06500c4090325050070410310000c00b261210102d501803c04441c0000511180c40c0c03845000c0c03000e0700c0040005000308e42c1e50b0414550344010111001d030000300103100303d000144030a52140c01603502c1c4074145400f1501c0304006500390344241e0081c0d000300807411a07090a41000d0059444c11003001006424040d81c0c041d1442c602c00f254441d4000f030546d1207102030205401444070441c214000402103440380c1d42c50121304c0061034400000d0340b142c4c0b03040001c403004400040486204000c3c40e41400d00f05480d00a000e00c41e4480c01c0d010503840b84410f100494152110300c054860309200d65066510030341d01c0b00001d030403039000c154808115081000750b08401004682160a0741d0780c503103401642c84e50303282400c81c20000500d00c8240c0c10350034100c05103100c510003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 105364577 1250 105363327 105363337
    0x3130605040320060717041505010609031109040c0608090106030605010f061d10050a02010e0604060218010f020c010e04150608040302070b0c1c0c0b24040216170d020f 74
    0x1950344445074040f0000f416941c200498101000820801d040106c000c1c0311038842d17401a00c1810744c9101d9803c6446c82c0c00a550f026000781001540019007001800452621241f50800c19a2681c1c064100f40e280c8064088003030040700103102c0c10401082d500002548950001d5800c11000c102c03950b118010800004d210348207450001d014001480402c01119a03034010200d0000c0841c1c49218480800340c80d181c00c031503001d809556031412508401c403418802184154030903c001640c0b0070100c0030300c05105d0803071050541089010700200c1a00c540029402c0000002420312148003004500014040c150000d01c180d441c05d61044001900c0d900441080d0245110b80c00b910302c02501c44011892601910340d003021181d100410341c00a884185642158502c00b40c9070040030000d840d2601564148141ca1125440c40c00d40c0c1307420325101111900e200030000803202940741209c884c0220303054620030f940c09803503041081c0004480075490700880b440009400400d544405020881124030303049 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 105365827 1250 105364577 105364607
    0x2120703050c132306011808010507120507090e0a0b0406081b0d11101205040317090a080403060c02010b10030204050a1208120a020903010e0304150c0512031306050403 74
    0x10800f98901c1e540c1d02c90083c2401c00b650446100401008056280040d0f500a440b05050141d48030300d1400c0500d218007101c0182540070004215410013920043c070392441c20300c2d08940d044c80c11060140007035003d024001142c40340f00c0440410348482e01400e008004883c0f2280e8018944000010001008161808580410412507000b690780c1070522921003d0304100a0940d206c001c4112858509080a01600c111615007441c00d40d0b45641500d007144d030156815070225030828080c0c41004004101e03e0f5101d0013090280102010f140c1e0340500500079400010425030310b81c1c1d02001005d01c00d600c002c14400f0f000f0030f0b4903981011040d0280c000c1d4045e000d2240540c0304244041035000c0348500f52031070b203548008090314140e6440141702c03852030040e01d4441c005800304040071072a03509004107064010600007a5170360350320b06071400055444400611041c0310400a500d00454000b00381d185000c502c900e089a580e507102291050601c10680c00289000e2400d0140400c0c1a8058254692545 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 105367077 1250 105365827 105365839
    0x1201020c01240e010f030b0a1b0c0b09030c1e15070c05210306060901020c0604060f020601120201020309090406110313052407030c020a0501020d0e10020a050a050702120703050c 78
    0x285420f00340d462620309009001c03030005844c40810010700340000c182c0e48000c14060004a195043c60b80400402d008030102c030009076250960710a10940c85043c6030403415030402185800d00030941d46482d510713107407200078030020341e8404040c94140511500d50300d007000410000c082c0c40e003040c0240028040c801c09485031312070070f0b1500c0c9031344000214010500da1400c4440e4210356501e01080340300d9000d80b031002d0450180c1e85082003280c494002420180100d40c4500c014030744008030003450440140d010729515010032580c03a01507600441150070454044d82c4034031040e40e4a08114001c4e000e54052111020000801c0107816030110441009040c42802950003d4244ac0c08040220940f02070140f0100d074044085902c450203940101c000b80c9240c015a800da6125881c0c1c142249c00081c00b20710fa09440381d0551046800074080d0301c840d807508a0f021420032881c150010649c2c001c411011003032047c0020080103541c0e41103440d8400071044c4049888190301c920b015500e0300c080c0411107024103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 105368327 1250 105367077 105367079
    0x301080d0302040302012109050609100c02070506030a150f030309031406100504050a060503030f03011502063102190311060f0304020d06020c150108070e070e1201020c0124 76
    0x54864000c80f01120b405070354404400d124000c021480c900b03242c9006082c1c5a64406000003c0d1013440030380c0c4524540005030003c80c41540420094030b0003032115104541004206000580c0c0741d0003500d4001c0c20180c00000e042c0440307110b00b0040b129a030002c81c2e114408000c00010594000f0000d01500c0c440c41e4041c11150100b07015556880d02550b1503501c480000340c0034002400c06900c050b5102c1041d80000c1142980c6030080b0381568014428141c08902c0040107110030b02c00d85007100049039840c40204031502e080070640181b03001c4816103189050075803031404c01e90050020820b0b40d46070020300507080d80010300c070040c2c10784461344400c44407816000210b110919016043c0d0340711212030380402e0f145940e5582000b00109110b5800c0b02c1c2031780c0c240080017052030100b100424028074100c0a0202e541005040c510380601a404002c10112700c4040103421544280e21401c0c400c0255140b80b03407040c1442e840b07400390140d401416041d40c070701031b1400c100c20801452500808103e0846065a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 105369577 1250 105368327 105368353
    0x503070203100501050d02042d15051c060504030c0b01060c03030506030f0a080d020f07120e15041e0306020a170a200706060b040b12060a0e0705070c03051002030108 73
    0x83c070424400d81d9803000011421201500302500a041800b0480c2c84810414140c0d0410506c5200d031040d036403038240d5440d40f039030742907814490148000d04402c4172a800d249a04c0803211203d00c0d0020b07001852561203002040406005040114440f940140d1062a030f41c2c507984002d0a81030703514030590001c2d00741008600203040102c4c1200b540710958001c2d0030340418680724034205a002d0120b06c05159420802c0708503c5a82401600c0618400d030302d0001400b044d114024250b00c20070f00540d1180c052203103480181d000c44411103007100c21404d80d01100120b042c00140e07c0e407102c1d0344068006400080c1005d00f8550000e010070b01036885030401407207900e410316450203d076100b071401107118140300741e5908106640c20142c11854840e50011410584903001074a50360019405000c0440d0042681402c000070240d10592001040d600503a1003171400c03140c440c000801600d01d4050000014501040c02351401100d0301454201e82101d00785440407520f9002507200f4800c0e05018080e600382c20f503103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 105370827 1250 105369577 105369581
    0x30f03050403050406031104080a0c0f0806010e01031502120406020405030f060c1e07050d020d0807110c0103181b0f1212050901120e0a0201090503030901091406090a03050307020310 80
    0x182d405907101c80c20a400c020003603004140e0745a01c1c135110a020f10001131101400c203c1c00700040e10502111081e94640020b0a4940d08c42c2c0c3c2005030300d0f80040d801804000720016940d0304680d0001081200b482e0701082d807400070f03c03400d400020000a518104414080c59800901c110751054003164000da880041003501c1f07420545092000440c03c00909200460300f41e0060314054424590f946000b1b181e03a2220310700030750400107501513000040381005060708000c1140c2d022040b0b08048008420b8625203545940c41d03c07003020b06140d640d80014a181c9a401090121a0781c4020164121800d8215684400026200301c2060181c0000c000c5406a0200036040d0b038554081c1b40c800050100210a850f01d03007016000c41e0412050001d14001001070b8025000891f200c400600010350580c00018030040301500003c4c00baa004000300034181c0d9100382400111030120360003045541d080400604030307101d0b5800c0701c1e500c00440c5801000303008003c0000c0000620840444080708011400101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 105372077 1250 105370827 105370831
    0x4090206030f06091003110906030c0303030108061f080a030f0212070b0405010b0612040b15092a0a02070501031806050702030414010c031b050f16060e0306150111010b0306010b07030f0305 83
    0x28001c7c88209000b00c03070400e219066007088008054403980070101d40131a1854009920248940c0d1000e0140b0070341e107408a08500584407120320b8020010f081c900c0c241d569208640d0024100301c4203003605060f862007480750001104081c03000556460a40c1408200d001042d1002d0b54a540780014060701490024202c03101200e140755181d4aa5131541c0b01c0381159100206895400c020001040c800359592200507446400342c680780c40c0c0345111040c9003a404074411240c44103805410003c0b000066000a501000c40e0b009107008a001003074045d4050310409510402001103091206100006030044003620503101100d001204150391238004603400018400d001e00441e0400045007114040105140c48003400b4000b03e03110003035003000251422480d8003041c00f4012900d8401c1c015283c0c041c403e051030031000c0340186405c0c101b00110f4040181c803400e41d5070504c00301d0325007403694840a4000a0000b071006040c0c40c0d8642e500c0100d541300da400340313501702c00007409811001141c078064445c2c18 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 105373327 1250 105372077 105372083
    0x1c0e070503010b2b030507021005070303050f060105041a0405060a031407030908030604020306061306020f190803062211030a110a020a140a0f05070503070e01060e0f04090206030f06091003 83
    0x1481d8800031140040d108130044080d020008104480c9025032142210f40daa2080300d0760780c0c2035039502d982c1001022118081c09034010780008905111850781e0001c15101581d40484006003404d0034000410360a208540c49a50405c0020541046481e095071100c40c83d407401ea41d84c2c00e529503c280e422001c403022034000401616040c4041540da040940c095503200e400680f2040c68550008010803000025500032001a8860500b00180c83c000740b01904103081e140c00070220740e590700e542d502c40c5404024071881c00707040b05c3c0503000342000312a0315000740a030340484104441d1802900e00209603208031a41101e0b80c0c1014807000d83c41180c08100c07074103400c459000d0416034240d0303a20b184243c892000e82d082c0600c00c103120305000c2400c1e00c080302100c2c0d20920040c82694648010705007008a40c0c0e1015060780c64003401007042940010381b40c141207000b111148502082c0c000081c0003044180000fa40040c808420008680c1d1406410f074040d040440e00c0201c1355680c255000307140d4980e80402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 105374577 1250 105373327 105373369
    0x6080907061209080d050a1a0114190e12060106020105010609051018181a0604150e03150f06040b030d05040b03040f1e0c05030109020d081c0e070503010b 68
    0x42903440c41540c4907035034880c0304c0c2420510301a4003980e001c2c01e9403c182c503280802a90b4444c000c1c201e001c480b6117401c0c2c0342000e0030198804000203a03045202d0041707402c2540303540c0c0395003505801d02c0c3c81425141c0103444020040c1a05c0009174607400c1d03641e64240100400b56203420000306605014a4050302100c5004060b04028000c481d412200c0c5264901042d285a400c50404542403403c010203150802480e4000030b031100703914002400c000a5040001d004c1d0000300001d11480d07240a06030051480d42c4e0a0074240c01601301d0110340b800080281e5543e400342a401801150404100003034082c1c8002c950910060051908151b11519980500340100e04204003c102c04011603010710b6000d4024490341c01010f9041d15003841c00c3d0000c01e400c05115002c0181d440800c103030104001c000e00010b81c0200040c24055000c0b0780d9085101c40c000c0c01e00b84001c24685042c1e1203000400140c1c1c0c204d50804c0c041099a110b5807540e548040c003549101307500b4640d25880d41d003482621010200500c20314 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 105375827 1250 105374577 105374597
    0x51804060e0906041a010f150c020a06120b1e10110307061b0801060e010c02030703060903050a1103070201050301090216020a0308030603070611100207050304030503030c1801020c0102060a0e0a0c03050105010608090706 96
    0x18401100400040200a1249e80040c440143c2d94501d2150700600b1181c0300e03c0001c6500d00e440c4411951002512803148454410441820004002048040d54281c1c0c40d1205e010001c9000d88117400740755460f02e02840002107030b400700011500050051035106990044612070110700340c0f081f08090048100146600000c5621584189003d000e1940040c01f82d07440c0765160707100d21040d00c1c0319200a50101e54000b030a40300d1658001d01d810100e0300c90318040d5040c0101c2e580000d03c0c40c1300611900e400560041a0109090515103c503180c440e402441c1c41c031526640d00d0140c416400c1103402520a0050391400184940100d60549241c103152000d40501d0340c07060325000080d0800340c419178803072105103c0880001c40800045005154001c12592145042e180b081120000444440d0454000300f441c0d822598001424542100230b59001003407044a129650345070009102c4041c1c02103520a400009000041d8003460682e82c09076240c00c5a40d0702d90411540c2e0748058807920001450401d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 105377077 1250 105375827 105375839
    0x60e090109031733030d0c0507090506040209040e0c03011a01170703020f160606090207120e130903030209040b09060121021c0f1b051804060e0906041a010f 69
    0xa0402c0c0d01c0004d0583c0400610842c035035103504058003940c107003040800300c003200c10340e450108194400d400b520300c0d101003c02d6042e40c0700d6441c0c40341e5100d0040b00030f8696001c22000da6951301903441c102000b078410031410403070030b0465603100030720030700305020b9441c102d2111941b01d1803110504406006842d8582e15003000300b111500c002d0002d046508259080c00039041000c08500104090000c0d590041e1005409090800c100d030000d90298542900c10410400007403880400107071030840500b07004141119100c0801c640413203000440c25041c3c0b61280030010103030143d025213490481a10200f0155000d002400101c1d4010b03241c0b5800703e9100700822080c801c0d04246903494200d540e0700542040310b0041402d83c10860481c20ba00e50070b468202d50440c4440600c51401e81d13603941d1800801e5180c00b944c02070417600c03803080c4c40704c000e20130042520800c3c0c489400c014010944140e8030f860f68036241c500c0c580c0302c08098030704070b40450400074021120600071a034541a100d21701c03200d240d440d24107a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 105378327 1250 105377077 105377117
    0x50c07020f120115060f05070c0501030207060e0601090606030b0303042106090f08090310060b03160306030206040303091505030c030c0711210d020105101401140d060e09010903 78
    0x11030200e0b4081d01000007240d1041c82070190500000d5880c05404540b810f01d40054070a0b001407032908104181809510301264803600c0907402c8030420300f00182e40d014a400c043c030141070610a159002c2c450361000054680b09a400320003100c0840d64100042c2c03086030105a247e100700d11a0f00200f18445502c2d00311b18820301489183c01b40b040b54006040c0210341d4071240c514a0758681640e07541004580040d1505051007049841c809170041004010304000300d8a0490001400e202c1d440381c000c0421001c0c050081e408032002e503800801403034070345070b4a01e0020040080c0b13000c1c003c0b001d202110380075021030141041c2e90003224003102d0141583d507440609182d80d0230030042603a80d1444122000075945903d00c1005e030350203180e01001c948402c1801c40900d8040380021030401c6a26080c100808440120340000c01e0300c07460040d050400152000480e00844511008041d125001030720340000031213544141c0c2280e141c02d90b13606450703039840c002c5400c0341c880c1d09018021843d100c4c2c04c01c022103450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 105379577 1250 105378327 105378349
    0x909070509011b081903090b07080a020408010e030c0c06030f06061c021902070602070f0e09150106030902041104050d0b0709120528021f020c04090305070209010504050c0702 77
    0x61400842d031100c0240480300301c03101d1043c282e40d180340000b41c0c0c0310b41003412640c14069442d203003410711400e2107603a50b01907074000003070224080050b400c01017411409260100c40007000c16000a00c510302c250082961a030740898214070440c882c514219005040c007006076481030a81c45580c4c521603840700d0501c00c01e42c0c40944802d403c1c1d010100c41180383c100710302c003408000f4991000410786805041c8040e04c3c140e1103821140c11755000e21000c010240465100300e0a5403156610340b6000e88030400d005240031004e584101c00b07401c1c5c040001c61460380c50352103803811500031141400349102c075200720305113841a4040c0710b80200c052101c81001c5200000e07000e03000790403031915a04113680e0b411096140c660004046881c0d4202c1ca807c000d900c0341040040140718000d1608401050709940000c0c12901a4030755040700c0350795031580c1d1050780d000b4050f4011960001d0300a01499486180c000d004e9804118124800e00c00b5038008030700c6003820301c58035229068201c0504d15001180d000c011130003041d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 105380827 1250 105379577 105379579
    0x4030207030b0c030f06040b062209050106050d050f1005010c050a02040c17010503060705070b07140409050a1d0304050105070206040306060806070f0203090303121906061e050909070509 82
    0x14038600040012240e1031018407a603c0c41d558503480f4140612404038a03080500740d40e101318140420700400756a200c0407a002e103038002c1102014801d20300c40c0000301c1441343d84072005040c90300e0000a503190300b100041c4183d60004008000650b181fa000c00005001070320b01082d050080142401954010b00748142894003d00c225821044994001400e0b12596944100000c9480300c10b54008882c040f2a03902524003200500480c0c900000028070b60301501001034215059180403c15841c01410f000c001d4103260110169035a844070038900c090f1000740d07065061b240c5403a00d00e007610b001401c1c003041400d10001c05035141c28540b00044407079070001e000990303200b0f000300400400120385105410040c0048009030040d03246c070703804c041e0400310780b0200c8909541003040980c0007983c2c0030088903107013643c5400c8108035448084a00000302d81c20069050b80301c2c98042c1c00b20307206411649000006a40d00c00d038200303504158404940c0341c0a280345803070304403401c00c01140400d0b020303102070401144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 105382077 1250 105380827 105380833
    0xf0d050a020f070f050f0102071d1e090d0806030105040b0106030c17090a050610142709010f11070203070e13020307030f0201033e1306030506090601020f0304090203040302 76
    0x21a200d819080c07440f03540c004200700c104031104120300d09041e50003141c102030900181480b980b50524503810300d0a54000342031041c060300d000841b0100b0b98540207454001c95520705425150001100ea0703520752407503049010400050010f031561605006240c0705a42c48414450319920f8500c1c150040d201c40540202800301d9541c80300444d0580c80010343c4034024820080c8030700d0550341070041c1021409080600c4100d8011024068030485c00744d030748501402560805102e0780c18991800d10082d5003050304900c072801005002081030b054201c04480080b8036400c01c040c00c2e07401680312040c0700e1520000d402d034101c41c008208000c0d2101c149603000c00c22018030781512405138002410841030341c000b03d880036006001d803c25035074144102d443c04079912100b40304194059101444a8100c0c003003422510301d18035000e040c81101041a01c142c810b0702a035a45801e07803100c0000e00903010407511a40298dd440340010902e43c400109040401001006585802d091000400195000071f02c19000e41c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 105383327 1250 105382077 105382093
    0xf05150f040f0c05070210090b071202031611090603010b130902190605030a0f0612082a150f040803011e050303040303120507020a02010815010c02030609060105030f0f0d050a02 78
    0xc142c0d40a5040a40d600f80c0e2015a108240d1040090800d4102d0400040180050042c040a1403842c2290780c00740e04000003030303c400c4c6c00c180128071307510999221102c400380c0c0c41141c004220442815108828089944090540e02c0b03101b85400c841e820000f07282e00c0241c0d541c41305803070160b070360000b0915800900154070344404034020305201501c680c00b001c000780300002004442c10040c820078250245d850b4040c4041c520340030520704039860341c001c041c0018500055003000b018075022005254a280381c00e4503c41640c0c00700841e11106404d40c07409446040d1000105133980e14038846218aa00c0f0b030240e4256403c0101c2c2c0c21034a06220038410700c4482502c004101395030100b019000443c420364817504600d0303004d002801990000781c40c01c030a540c00b00090000503a00030315595400413845c400c0e400000d0314000100e92400c030148000c1c1d054002d06007445409c03103001c1251416103c054084030445202001c1007a600c03c0182001c0c0b03026001610364040541c49080100700c0100c0c10302c1211418 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 105384577 1250 105383327 105383351
    0x1b020c150d0b04020f04030f0c06031103010501050c010f060f0503191a1b0c060103020f030303040209071b020a030c030c210605070c080c071a040602060c0703110d02060402040f05150f04 82
    0x1b07070f0203038106913041d02820f040141081440000e00b809000245801c1c0b10420280c0e440505030300040c001c0505210f40030aa413280202d0940c0101070300f040c4440300b409015621140e0300c150754428007515009010381d542c1c400c0707410602181501c46070f41c4810300c0d518444201808159000000d446e290039507403041d10400d01da210610151040b0102080a4001d42d4514070420550f19211402d150094009008000c0580e0300c11a049501c00c080d03042180740c0103141d0384200c0c44400c04500007548050340c1e00c0c2c040f09001c0d80c1c90080040d00d02c02c0d0341408801d0744503020052200500c07900c42c91440110342c0d400f00000e84a0f0040e981001d80c3e4208085440415625003280790801414020580e2142030700300016680201070b40e4030f040008060314900350900030f0094550070003c06c590229040010f001e420540b007543c16107024400a0180c9411124000c002511b0340d01c142e605a12a504100e00c0c18502c00e51441614019101200c00349000c011600a0009002e1844082a4040c1d038589000050f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 105385827 1250 105384577 105384607
    0x41214060703050a0f0b06160501060503070803040f060302161e0b040f03080a050606070201110a08280207060801180921080903070b060d14011b020c150d0b0402 71
    0x1441c03942d01c0104840c030304441c8001c11100c0510481c420701e402d0820109164941c002180d020544030f41d440810500310b0301300b0501404e225804281c16210301c0c2c20004801e81d000c00a48155000e10765000c007842d681e201c04505a024403182d0002203a00055614001a14801650448038400200c1e4030480500d1319403c000d040120781c00c0d501c00c2940100d070010150301540c0340d54002d2161a0801aa04001001c200540101d003c0281800791110000444000c10020346917010b50010381550b440401910295154000801e00400002c00e4060349003030703600201700740d0150380959840ba607032a0f10b4000814215040703403902085299440d03034284041008400501c2c01000c441885070f08400558100800b00d100042021800341c005000762000610312001e11500b00760300f1140e403040100e0ba4284000e4440b07002e001e188140d0710700203409c17110b02c104a80c25242d01c42103801783c5d044010701d0803c0c8221b4100d9006018211402007000a41034000c940c06184c00c8803003d0001411310200c1c150a540c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 105387077 1250 105385827 105385831
    0x305151801110903011506090504110418061a0406020a030305191a03150108030702012015041208040302100c05040506132d0308090d06090b09060a0e0304121406 71
    0x140c0c0e20b00000d40e00b0110f050900900385604c03c0d0392000114689041030040c10641d040c094503100726128031444550000e00b0090302c001d802962085407590080d140080010700d82807060180c400c2640c401441d100c1018000d4a04a50040e00503002c800180c0e0390071001032200408440350700ca1003c1c1c0c00010010303940700302948000c0d0300c050b20038100040da0800d0301c0c00140d47c1c0c3c0c082c81c1000280050003219408070a0303070f4000364203003406030403024284880401c1ea144081e402d06680b040504031550005915100e50069008480340c403003800220310100e80300c40c0d0031140a000f582c080c203a149440411030344000510300903890a0f034140b42e25880011200e50000c441c00d881981440d501340148440521038404190652aa0512144440030b004851030745a20014207140004030b11441962107480050008580c0103c003008000c0d0f103441d0030400c1c400151980070380b501c200400103400200520454600a480e40001d504044c03402c1c9007100702080c1e480d4100c0b80340703030780112201c625407080191038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 105388327 1250 105387077 105387101
    0x30c07030c050f011a0303090607140304180606120e03030f1b040308030f0117100f0b090103050a11012309030a08190212040509070315031403070308060a0305151801 73
    0x41080030708501c1905080845c00c000b28401d400c2000b0700c152a0740c0d80c408445080741c2c01100021080f20800d1254254041c56111007001034403e060051001c4c566888003064400944032142c1441040c1a460f0480b85110411001c0354403c00100c0c81c04805807040d55070095410303003100d600d40080050076a41c1c4d0003591003140c41d20000320034080d020300e03a40d41c0c0314003503d4a65614120040080441d60352012400f10401c0c03d556142c120700c0354052103410141c0e10f0080503101e07070001d5079245003983d40c58189000030344400441c610300c4d80d0558882c0f4404c1100060348081405079260000700783e52030381c2c4521401b0b81c0c54030400d041c0701e00007812403000c0d1801d228810a668004502d00e04041e08120500e0b841c150361407400c20043c030481d038074201840c3d002251482d001030000c040c1100f03411030b4040c07500060b000090042c80304141000010003860224801d5982072502d0b15844103015540589000040140d0415080e142044c90310141c1198865240b620480a144042c0c0f16075084401c644102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 105389577 1250 105388327 105388331
    0xc0302070b0f0403140f071e051006031110030905070f050a08070b030a0e0102131503140405030706020703050706050f0117060f0a0e01061d0603010b060c03030c07030c050f01 77
    0x200a100e90210090341c400041c1e05840d00e20702c1c00340d400400c256078603c41482c1c4250f0114038600c10100701b80c103030381496620038843c2040c089801c00700c04142c0303440c540860f4284141e002044000e0307813600845044940c0211400040f0184008200803017840c1400282015543c0341d40d1004200100040002841d03042c0c108183e80d4100000d022560209800000171580910804c024240c140c1e41104e9025100311070010346401e0020b941030291140803806c01912210f4000400c4100002d020085e403640d254070104440c501440113905082802c032800740c52900103101c0840460400d800500c4424800e2814914240a070b565aa00b01ea200b40c4041d4500d40d40c0f03c0051003034440030005222024100f4008004900e06110440051400201400050b80c4c0340c001d00d03a4045c000f5040600600700c0e0420820b610480940c078040040e001300e0354170344250700b04540310700142010780444901d04d80840c0511300e1540c95449803c007030703400300070124100111014408080f80d81400311000d44220701c000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 105390827 1250 105389577 105389587
    0x201305040b0717040f140a050105060f03010b0109030602090a0b030c07030815090417040f080105271506030a080c010905010606030e190c08070b0a030e0303061c150c0302 75
    0x441e80705850010b01402c00c2c0050b50035068000b500d60340016a000754040181c5002448030311301054004d00381c46002c4803d00c00c0080d003004116064000c14482d00c004c0d03404019500101081509a50510214a004c01c1c4480c03424400300320603400030125241f02600b001071282e41d0b0030700a800341d170084030306400401000c0365000405038011460f035005020500c0c105c40005040b800510b00a1000d040100145504829012039203035041c00c0d1b90080a00d0010f5001890740d994950380601402ca0350075081c0040a031580c904291041c1510808985450042c140740d0412200383c5000d05010703007015407520401042d08009000c1100030035100c030b0841d0002c03440c41d40604c0c000703003074030340b9500841c0c00e040c141021400f2503c000110b00407140324803007000700d01d00c084c1c1c02e05143c18040c0ea000350025015040c4c003c40e10141640003444000413a80d001c00010b1281c142482d1280000d4078201e9008010f41c00d01002075600725451440f0354091152950b0300e14410200c4811a40103030ba103d40401e40102e9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 105392077 1250 105390827 105390833
    0x17070f03081e06100c030c020303041d090d080c0d09020603010f14220b01030b0405040b0402031203160e1206040b10060224091608030d062120130504 66
    0x1201a030001220750b04244681461070015241100b40690301003040042c45002060610a001c2e400b5026005025a580c40d611524001d06170300010540034010303d103d502248400c1d0001400d40c6482c543d60340c0f6805141c035840031a10056112079843c84603917480ba4400310143e82c500008600030151035244004c1113150040b007055861a000006115014110b504a8200f942c9402c2d141d540d80007480001d030420f5000010380080c4040c170015a0000c2c500820071080042d00c9541c140190b000314211a0020b140105100f0b05100171200f0414010045446100640c000c4080d0220707024020310110464050900783ca01e8040115415900240100305200207040e4003802c00300a4146480681078100c0c4100c0b4408400a880411003e0080300c0d90001d10294024400c00b400c100b2400404023205a8540d511a03881d00031140b01c540c42803071301000107409120b502a034050320750802d5480041803595100c90b110425100807072158002484465001582d07544802e54403000c0150002032a03041c0340c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 105393327 1250 105392077 105392101
    0x30a0507080c09150306060918101d0f070317070b1501030f020906040b070f05030406020a06050a0501150305071206081b0a0f1502150f04060c05090d17070f0308 71
    0x103030060310041001300c03280c030007518041000c640c4600f003691080a07580b078004c0714000701000580c8002030350081d14120030600703825801400585190a45414110020410385921042da11030034007000d5114140400c00a2070010400d506030078556103071824240c15448184c1c144e2422510000608100041464150780510461b001450b0140d0114104064003000c43c689124a002c0c000081d100070a40004221382c103090840d00c50740c40000d40741c030b030303540d6a4003e9511600d80c4411107815003041c0010711040b809200b01ca04a801511803003aa070f000441d003c2e401480094a0182042242070302c142c03004606014840c0140900c03001084d107000700e0400c0103010303a04603c141d8401c2000702c50402404101e0050003003918080c400d1592000d0b4903890903803805190303141e0b0b006840500700c03c001e9505d080c501e01c180310300c0c000e40c0140301c62014800211070601c2030f0811980e0000011446101140901c254005860325280c4160704d40b0016850f0490000d204600450000340020108901c4203656 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 105394577 1250 105393327 105393331
    0x1a04050f091203070f0e041112221a060a0510020a0203160803030403050d0902210c0a05060a050c1509060403020d080103020f040504050a021302031006170a0b030a0507080c09 77
    0x10100d03103086042101e0002d00303201c03011780c1c420b082009501651520350703103a51044240344006242c032075850080c03444542c00150700300c4820900741c040c1c0000504001c5400440104541d200451b12130300071041040c8844240003601e0280c205604075008101500c500c030001070b103c40310783c008080151462041618207081c0e0054040c2031030003120200a200c10010503660031a50609145454040940507030700102100180170f98880003003404a603c0c504001c0b108c16608800c1002c1d07034100301d1003500b4010301d50310910502e034200400700044511188118040c010800440003503c0390000510007200740040b0603240903065401c03000503c0304043c0c0401c04078910203041d0070a588258503580000341c0250b0800c03102806a030325200045e00f04002800106803084e0300600c1c0000490a0804817030003500100e80c40d0301d2004017043d0205403240603000c209003514807001119150344c1c0f45114040502003500711039401d0b00c03c012003640000c4040c4400b0b40908210320081044036205001c0110704000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 105395683 1106 105394577 105394603
    0x140f06130204060608090606040e010f021824040308030c27010f030b060403020d0f051203060306060109060210050c04051005031005060309060103061a04050f09 71
    0x4034182005099000342c600f004000d031181c8060b03036101c90948030403500354040070004240e450140c00c00d9103c0307610b8200210364454803c2d007410a03038000d585c0112a900004c003800c00703241029140e085040c404458007540c0c00c0c4c001c04c8040110300c40d60101500006002002070f189000c440c1c112074402501c0305403410015580c12000c402050003551881c00190b095031a400c507039110707000e85180c04100078401480c0520b95400c005a01c843d4540440f44240c903141000080794080c400008001031704110581d03a0b04e001030806040507002400541400908901400705903070015841c07030440c03a151400951522a108603210501869209a501c0320406088100155101014600030201c210000307201c0b503282d90810455000446003400941d100e04010004218190060604d802c000010b0440246a1001203401d8134402c0300c0c83c6152511040c18400d0f201d004010021802503 = true := by decide +kernel

theorem cover : BRFrame.Cov 105215827 105395683 := by
  have h0 := BRFrame.cov_init 105215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 105215827 ≤ n) (h2 : n < 105395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
