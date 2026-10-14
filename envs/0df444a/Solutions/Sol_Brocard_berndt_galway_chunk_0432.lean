-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0432
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:46:55.339186+00:00
-- url     : https://prove2.me/submissions/9a0465dc-59a4-4230-8495-cd54a146eb53

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 77517987 ≤ n < 77697843 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 77519237 1250 77517987 77518009
    0x309030f0a0c020f090c04120311061005180601140a020f150a1113030308040201170109090c0801090b150d020d0501050a11040303080112060e06070c1202030a020c04020c0c 76
    0x8001802940720740151300c0d0400c8644242e040031a000c01042c1000e2040005922840c46204050130031811b207502814016107040010b40c68800551302c8a2920084a0010340c1150240d140305416140041c0409a00054503070f00c1500181c540325515480400c00b2516600040700c500304601c40c21126004045c0103200101e2000c280c441c095025041c581228400c3d41d2521550b18203016080c4003585503920f4880000085a415090000c201d0f10b803800101d8500c00c91400c81c2130b04070355040c000503039262651700140840c2d015901c3d4a01d8240c4580d50182a1260160007500240d80c17203002c1402e000086565081031040281060382e200c0c1543e000c80d0003500e11a1040e516650348904000941c002802064202d0803540201c619050555602400544041c01248000c1c164112400b08101c400d42c000030001c00c0a0084031001d00d020300005081404180040300c1450041481c206514000030591b6003026540d0042c00d40d40c5400c10502c40290800480418503206804a0b001943c0b00d03401100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 77520487 1250 77519237 77519257
    0x4020a03050312010609171009030302040b0c070503070e0601021c12090c0e0c04150311040306020c010506040e0304140906030a0b0903071101091505130f0603090309051203030c0309030f 82
    0xc0e450b50b2412070080c16149140c0d1149504c00107d2a01030380002010034070000c111600390300060b40c00e0181c00d08900030700640e00b00c03c42c01400006d440368900f000041a030200d60044044404035a02c4003c80403500c03405458050240e40000099200c002d0031800c0c121840c400e6103000c103d00718084200c0d5003a540c0714031060307034880346901c03040c40034040489180360b2180700d001c0341038505403400c841c4020f104080e04240e001c0507035410700c01ca049008601290b00447d0000c00079507c1c0c2010307015140c02040251100b6200300d00d4104900c00702d81c004002d40342128100e020011240d00104c1c28403282c100700401455042c01042c10131000280d00d03005c07990040002c1001151600311514090071140d1409652a0620503001002c21078041101c011040c070800d01d00c3d05035114410052103038207031b0506400c10443c010307582c8800b00d0403560580c000071419000baa02c08000540c0e03101070080800c01040d40c1c840316081080021013440d51480210380002003241160b15041e480b05010a1701d030400b507080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 77521737 1250 77520487 77520517
    0x504020732060c040b070803090a0c0b030601031a090601050a030e0d0906080f0108071a070f050d091a03010b030403050d060305150c1204031103070b1f0602030705031204020a030503 80
    0x3904020420802c140e840441900b0b0a490141480c960300c80e54011600700a201845c0000002c2c501c01044c030248407603e5120001200440d2944c10032000c0340c10403102240024030b40140071880301c4500c4400c03c50340c3e0018000c03040340d48490780112002e52280b2049001d1584030600c0051040c1304019a1075002c103a591041a26801c00c0d43c010500a0040c0000e0b642c546980d0050181c0807000c14468100d88000c03440076005900400e03890413a0081b0300004d400321060030f02000c1403210104d0308510640495035403081e0b113a280c80b00348001644400000072401c10901c01400a42c40e000c000b5074100e8064105141000b80c0e0704081001e54a581c3c108981075000000c88481c0c03600b0782c00ca82600019211b0444e81001a100d24000384c20600a2010f02002404d0f00c1d00c1060810900449250780d4210300003020700e00d070005049038444d0a02030462190081d00000044480c03001c000c0d1403007280e201c0d0155117044450802d5061a07000504240e0344a401d6000000025008200a0980150710004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 77522987 1250 77521737 77521823
    0x1e090601090615050306010f21050106020f1203160e0603010906081b0d0308040606150201020405030d03110f09040612061d010c0c022b050f0111040501050405040207 73
    0xc405a501c80d0f4840d4140c10203854485400e03a0b00075007660740c05107081ca060300d4801c0688000b114207243c1d080001c4c08180500d04c41c5200c40d1103a070062416611550202d82a800c10940107913a0f44501d00112441d905040c00443e02400d1400d02c50100c02d1141d107800d4880e00c16110001c1c0c1654007c0c0d00c6170740c90300d60f641c40400c00302c1424418002d8885503200b800300781443c3e02000c5080c2231600300e0b0060811591500181c00c010465104d000500901046814072400c6500060b0003076103e8001d0500c04d124249070b8500c2c04d4400d0042c0c0d440c07041030740001d50400e212124003880d190801d0520550050311643c01140201141c41507102e564002d201c041035510140c6101044820b03c1500c001169041a00c2800d20b50b400c04070484c0794a905980b401040ca200303c48248054035200c0401c082c806965030300070180040010b902410703c41c048020000c91066000b01800d5200714464280400d00c14402003006103095409030140c18081c0b049007600d002c103529140440ba4600f10108140000001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 77524237 1250 77522987 77522999
    0xf03030a2c060f07021207090b0306010b13120501060504050a02090108130b01050f01030209030f060f1612020706020d090303020c0f0109081b07030b0108030406030c0e0112051e090601 81
    0x79625241d80d151001401000341407401080c03462148200515620034001090421034035640044075605840c0000c0d20340160300c0f401d0f044c1c0601640f000e0144240309130000826001d4420040341c152890501140c2185442c5c0081da40540c080c0840581e200e5681e1200015580c680f40103040c403035080c481c401a0707a264034000141141001800b04490314440021100c000b030489401d05056a200302d40f40040c4003071020048000e44505c02c01e0070f03090f00505d006070310003100001b081c500482c01d4000c03024080d540c021381441c0309400400242c0015520400301c0d010034580354028481b00d40218809440c03c1c5005a030f5105aa514050490020781c5c0040c03500e000000c107103d40c15040d04100000d02007000c2d1611402454090440056034807443c0c10742e0030802c008100001001194064600102c41d84d54003000c40e160f80240c410700d0042814070043d0140c1e03d21881c1900f0341174005031a40c01e4004100c14030724005020040c945540c5000403090296150424000244140945401047c407581415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 77525487 1250 77524237 77524277
    0x50601171609051506070804060212120609070306030b13060b01020309090402151b10051312030504110d0609052116030903080703051b06010f030305090f03030a 71
    0x800c4900e070304021001902000d951000c041100d15154000c42c0c0350310b806000c13000070820340c4601c40d80140005610000c0000d50405001101c0300f580a5031800c1c0140b20081c4404d2040c100d803c940c5444240000d03c00d0b150600c58a07400288034503000405940b02d03620200c101c8010398049581749180d1001c101044442c0c01040c00122083c0302030346c2454086d5020443c07041740500024440c54100d1950041c0741202d0090350421040009040311030010792440766203800d02c450032124524240300002d9007101c80191000302155000d0385c0600b094294100442c01024098403ca41044c481c0c1d0074402030383c0d20300d5055054503019290000f2110303031900d0f10394904810300b01d5603244050070b9001081d225080d90300399400c68100c3e9655440000305c501d012a410740251300000c1013090085988800d02d0b078000d02605152918142030304442e96802512a6924001d02c0781c415418500340040c000a0701c1100900040c200c00307000c2c8005910110f00007403c5030000301c44640008c0c030f012000e5140c0001d072 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 77526737 1250 77525487 77525519
    0x170606060c03040608042109170106030201050708030a06090617060f0f0402060f090402040b0301091406150c0a0c030501140a09050a11010e040609020a02240a0b0a0306020403050601 80
    0x11038000d0714081c80c051200303440340201d210714003e100202001a09100d92000f240015008100740d4003140302d1200b0001e40040c101e030041c1150550a00e06524521905208510a0740e405843d8203081c075a0300d588002e0345503c01890031494644031040003ca001c1e050140c0005485a11040c2c40a01d800000d0380e4949000202034069100880061142c12000e170030350720390081e4046c0c8480d03540d45007031040707001c0c20b10801e40d542c0c2d0090b00c0040c00089203042d280182d03060b140f0b030141c00d000456402c0c180900c1c003841940d000e41e1100081002d400300301042c1c0010201200c2d03590540e4401081030710ba101d40076140750b0003650541d4540e15080b01d10032080c1003065010313034070316801c005003580c64030740558501c50840002c00241c44c0c500c0d24034050380508410662200000c00500561303442d41c44000c065001803000002503c01c01840014011001d000303010850006c1e800d8103e541d50340c010408c06012100e0b41d481d04002860f02c0440800c21500091010b503028500a0400307524200c54030b201c1d1660 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 77527987 1250 77526737 77526739
    0x405060418050f160515030c070503160210020d0e120a06050c0a020106080d09060804060b03030d140601020c010e13021605030405180103022d0301060609030611040b03010905091501170606 83
    0x2c0e04c01e00740025030b01d40d040d80c40f2080030040410b80301d9403600305400c65440341110180c00391001003403040b848002808600d4074148240c80340e0080c0071502e241a039440070760811400100380507400160303540c10301020030702d007140600c2d08403182c50480740c44010031503000707558500c5240380016801c426160240142001044240c0044c2403000d9130740801480c21000340100c08c10810244007040a20409030030800404c100102540c1d07440c80c070303030740024020040c1c494030b14100c224020004101d9800821003030035401060711804047e20340c1004100b0403083c00180003142c90780c01e10224108494a128002d20548124001d540d198100010445602c2032280f00d400c0c03c1400500500040e12000d004c441000a0880350010041c031290500504581d24048140c06620701400000c4080d0703c600c81104480c01030302c082101a40c0c0040b80d11061195014a440c042c000b040100144540c0d540965801520401a15100c1903640c02182d0716070002c1e840b8940c82089181015410041444030b07c7e00404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 77529237 1250 77527987 77528023
    0x5031e03010b03040f0c17060a060e01050f0d05010f1d06060a061b0309080319090e06030d180e0f0118050609180c04020a030501080706050c07050405060418050f 71
    0x715000c007082c1203100041004100c0102c8849400401065040941c082d004807882c00c08a46407418100340d0b6807a088940d030040301e00b08100001c03520711848074507040c1e031000b5112044c80200c6905000ca034112040040ba02c41d980d4400050a0100700c0c42030f0703445190f07402c160150013014900c01c2d40c582200640000e00c10004040104043e0750000340d4441102030000c4000300c2c6c03042c07e050941d090180e070381c480001c90100160f52814680103904400060b502500c070100c0494030b803040c80c01c02c8401100c029802d940810203030079902e4000e0740c6145581c80c01c458081c0010341c855410841400c400d5070b8082017294075400503c03008100031240e1103c0054030703000704003624100000401100c0d014225511040c070004008081410034000410140000f81040d583c8040b502d070000c0081c1001d20859000b80190381021a0283c425400c0307408600e2100010000c0d41d0800c0e00700802040f014255540c0250b48066290b203554070400c000e003034140510058440d0542d02c4040070f0400120320040003040c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 77530487 1250 77529237 77529239
    0x318080303040b0408130b0319050c040b0310090c0314090a0312020a020a0501022808070903120c060c0c0605060a0812090118080105100b0a020303190f0905031e0301 73
    0x440000140d03a403094001043e000c294482c2d0518040e24495020a00f000015241000c20001041c0004600521000c44081040c41410391000e0481e4402d8035000c40200b800c020401200041c00d01554000244040040b003550381c1d00c06840c03c50724072580c69000b20b0b4941c000940c2500d90074981c1c0c2da10880020213020140701ca541e00420901c0e8840382c411f0b12607030200d05060050710800845c0c0f403c0350b02000840d503c800d011014500a01d0484030b5083c2161240d040c5406a8407602441d0701800d595101c071200c00d815543c40400001d018030503a8200901d03928600c1c0401e04500400f1415140c6031102500000725040000a81e0002048640071b050300c00340422861200182c14001c01100c8540c4903110f810220040307c0c21421003000c080d0180c45508003003034921066009501a2a034401c0c101e891070307501c00c0804100d006140d401c10160b00180009902c080c4200c41d01d070003c10415500042001180d402c901c100c0e0700304101134685910115818101003140e14402e201c0d031411000c80c500755 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 77531737 1250 77530487 77530499
    0x7030605030303060d0c050a0b09030d020102120406020702010216060804050c03030c0703060b032d0c01020105060a0905090c06041824050d0303090203060a0c0315030b0619030515040318 82
    0x1a00c005482030740036140002c404406d02c4031100209003e4000100120fa40c165a014591501c0e040525038500c00c1c060025005038450051003150307044094000710b44001d5032142c442c44001c0d0064041a410342c003401a00460b82d200b00d0354032002400700d0341c40b00e040504003410a40e00c0d100d1b100070380d9400ad80c010086010110340005241040302da011a000c1102400346000c07900b0039011203924090f0000003040c0e1000c1107081140001640e510700115629020004012400d960b0143c400d241c00544103001801010819044503a00c144140100d070002e4a45d000450745503407150744440d058190f42069103000c05000e010310400808625140d0b10b560380c4044000840801d0b81c03203554800c1c203040b0704030340805000f030300840c0b640364006098034030720b1600e40b010801400c200e440303810004e0301c3d103450f10f400840030b0110502500e812501107002c0b40d0f0b0312002c1c0b041c80f2040041d80289500d914500000040080142c1c2080c29a07440c48940d8a040c40d280140c610003000c0c000c4020440181c0b014004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 77532987 1250 77531737 77531743
    0xa03050a0c080115020c040207060b010809030412060c0302090d0c090b0303070b0a0c020f010204030b040b0a092f06070f030809060c030c0711100306210b011203030e06090609060703060503 83
    0x10744c0c1e00d02d828104203005035038007039140091030542280c0042c0049880c500b880700990080650800c01c1c0c8440c01c07156660506140c503449079018161340303130130250300301d502184442d40504404080ca040040c94110300e400007400011a600040b1b507840c0c1c0c81c15083c0800c031240e00074140340076410b5004600f09401030307485800c581c02c021300d2145030f6035072400403001c014801c01c02411103c8011b002196519240c0c10912149041203906441859820b80400c800d107500d4800c01c1102900042001c06051460030002d03103203c0b881c2a003194081e6501c40303480d0550782e100020011288998564506286545806441310b41d005181040d141c108004000185040001302d0b98003031418881103541d107141c1e00c1c020140c0c000c07450f0391941007020120381001503a0594008400c0d2000501003a2980b407040c03c9509050410890090440305030130010001804d090901d000c1c4588203041c046140648480100c0c5040c0d002c44602c1020b900000900c03c00300c40c24002030f0380011451505204050500c000710b95 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 77534237 1250 77532987 77532989
    0x503040b040f020d03020a0b01050607031205330301050703051614070b0106020303090c0f0d020f040212090714040513020108190c030603020a0f050307061b0b0403050a03050a0c0801 80
    0xc04000090104400b1594101d4010750080c0320703040030702c0c0c2414000c1d42d80c42e5640302150302d4000d020010450b894031800395050281d066944403a0083c041503c00302130500500014240f0380100d89104500709811280074184951000c03443e81541c035407080500351140078000e0307414146000148000f034864030800320b5241c2c6050411344055469042411118030410201800e0340c000d00c0004100203502000075030103403030b00f01d0490302d4040d000b008000d0803100c1000003d502014803c0600c005042c020440c0c100100010001410000090100d01c080c60b403c8139200016004101d05110400d40c3d072100c900d01c408181d808200f54601011007004032040c42c2d4019042c000524005440903900b03a201021403960414140100501044050060640f03070108a00c05d030710402001c00c070003284040c204100c3d01c4c010000c000492a01c14140c2d00000400035460b40c0300d181d003409501185002c1c0c1814002ca219945684d5681d030304000040482d1b40c00781013032101c1c6050a003454181c0798800c02c554 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 77535487 1250 77534237 77534243
    0x612030c0b090c060f04081b061b0a02060c030406170c07060e0109021002060105120319051e18010314130201081e0c04030b0f01081c030f1802030709020a050304 71
    0x442920b6405145142404400c582d50b0b11031390000e103400c40c000ca0030b006441295800000c58002d0031004442c05d60380103042c4000707070b04407500f40b01b502071511200400c018601019400c0d100c180c03901c0c0e00420220340c8080400500e550001a041201c9640310340c0c502480c10003e101003a45d400c002d09002620300c2090409805a500d5984880d808031080d8080c02110360b008007580a036582c0b024029468072002d1207500e10540010200c0200d45801108a0304820042445c191810140705030582d81900000a2044e4421844100103441c0c242500241560301d541540c0c10800c118490004054a1030f2034a62620300a403c400e22100e5012200c0d007140c1d003542401c103012207035140014020000141c079840110202001c09012141484200410035a80101c0606407903a0350a580070344031400a22584002e0b074000900c208414081c44c2c82014091403a01d00407a0041c211074500d030986801808203906000648801d00452030f080048900500a4074030542c123003000e081c0058500c0c04020806 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 77536737 1250 77535487 77535503
    0x60e0402030c0f030f070f020a03021e070302031005100906140d02120d0804060c0216120c03120816020f0c060d0b06040e150a0b0406110c04061502010612030c 70
    0x86507800074190143d070081c11041c0c0c0c10341c2c0c0702e00d0410441404250300f5503c40004c500c05010105096201250340906160150000c00e1451400c00405844c180701010f4480c1c0d60281400110050f0740c14440d2007c2c80340703040000300f52170504404036944e0420030f51001c0515880c00c3c0d8104070800340401d1a21303114800301c4180301461418004107502070407012840e407003401240307100c50100381c21907481350180b40251810446821003102c00e990302d000380c980d0003494010446040086040101d2000c002601c80d0300e00c40c0100d5541e0b903a035450100650192400305000d1410071900c140c8500e0aa645070400c0d2004146085100c0f09168403018110031090040c03400050440e954941e640101c0c9100e0b501904284d5525500c03051002c01c0001078683c0652840d915401403118602981c0c0041a17404003500580381a26010f000d9601350100c3c103c0403441d008100040c11203980751700c2010002e0200040071944844014402801c6480580200860004038400c1c00c011030f07444140c0816559102c940 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 77537987 1250 77536737 77536741
    0x1308010c1b08090409060c1215030f02090c09060a091d0c0a0f0c0f0c032006030a0207020301090f0804091104150f0504090603080403020f04051e0601090305030c061f060e040203 78
    0x224015149020028160780c1c1401561f008541d4820f0710001c0e4800105002c20480007801c1c000711035040b0520000d02044801100340000d0300d8840d081c2c2d0b07002100d1494452402d444a00840e541d03400040c40c40000c039000490800400c404241a82058400360a20314101d1600c420742c0003060250184075800c0000341480310004900070b0400502081d0032004008151002e894144002001c50100b01c43c0400803031000c10460030300000780c61404400600e8182960341d00c180103070003500312500907a855900c40800401080001c03807a0143c82c2e001d828840c3e510343c140849102603c04602d000c0481c00410001001540101c480c3c0041d000700d249020342c0c0c0301c0d840550807500c41c000d075046002e416141500010810400f600100100c900c26070b140c0d84030321040710400045030411540c01d260000c8070001001c104030310001c80c59100c0d005040091043d6101d44850b49550809120810198400001d102806520030903003042e0310b40c40b8101540580c20400014280341801240500880e00440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 77539237 1250 77537987 77537989
    0x10306180206031f0f03030801090c050d020a0215060f0d0f0302011d0a020411031311060c03120f0906090d1107050d0609030e01030203010f03080f040b1308010c1b0809 74
    0x600c1529002881c440e240d081c0080030101c44c5001c065400340070015040c00141000d00483c4800480303405480d480e03a10ba1820980c840601450f20300b2808210080103d031503090a2403000c1e001d9010306078010b10500d8504d85813030503540005400c0502c14201745200740e00c030780d0340d20900c14009a888620128800400c0c60264050005810403c66540303c440e8040141c2000080340f03445c141c001ca40a001001101d1080f80d03151101340c0340011802880249a0040f9100c1902001c00000103030100b894000c6600506040d074100929a0718582c00010500000e0940050542d4004050034058402c900b0700e0310701c03181c0d5031141c4854042408142200c43d5008403052051200400c400b8180b56070b044014903044009207884403084011540c3d046414209520034130a69059070b81c0040100d10207400c40d102c2c8000d9070410005141d440800300400705a400d407542c0580500300006445201c0103051180381401d6801d00e0340c4800400c948519000c141d6020003007860209a00126125905e4a00f94 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 77540487 1250 77539237 77539271
    0x19030e0601052209080f07030c05060c0301030c05040c020708030307021e0d0e1306050a0b070b090114190209041104050307091a10020109051c020d0203040308070605130b01030804030c0e0708010306 87
    0x3d1101c06d840d110224600c024180c002c520051039621403000d0b02d4050b65440c0440303203240020b00024190f010717080003d21407410281d01016030403450f801100d506a644650f01840d5910072191100140c01035852110071103a403a442080c24601c04019180342c0100c0500207065038500004184140d2125101c503c0c1c3c007174030b60310103409000c019142501c3c5548903842c0182650040c2c1c41150300d180920f0010b41000c5061107100452200c1481d80b94680d112100d2009600d07011520200b081542080f00003420356070f03485089000061240d00548503071030302c010541490201d601c21a00e45003015284010790596180d05280000201d03000e50044020034800c9004103e11f140c01481d900c5070030046591580c03141780d034402c02c0815600315004241e910701c04907202d008134840203158030340a100000c0064110f0308110790002c2036108803c2611125151030109410030f90064480503000601403050080d40450340001d4070b82c4200140c40790416100040807060144000b5080c039660f11407404a2451403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 77541737 1250 77540487 77540497
    0xd0b010303110c0a030819110105070801150507170a030e15010501020c0307060f0305040c080d0809010507030c1b1406010609050123162906030d020d020703080306040219030e060105220908 83
    0x320007000ac40c580910007921010084c00350000d4160207515416101e44541704407009035900a101b032144645200d0b030040950840c403254402d064444405070850002080012031500d88865600f1130b0394546400a400e00305060940b5010750440340b003d0061070340000308504a03140342d03e000038690f070741e03030610723400810507900507034640c0c010205000501a4407200c16030281e001c41c00200815260414198102e501c44994040421182c801d07482055441600c82400903000d0701d030a491483c2d2aa1565090410907000303070340803d101601c207000d296400045c4000c851030002c819523500b0f071601b007407000e01d008501219261000e42c1103048100211030002d6010303201141d54000c049090300348441d500d03020480f0400d01a2241c144010351543c40051400c03815145a0081c0c0205820741c1c279400d0003035000030308858101e0b800300403152011880c0d481c02c0e40c100c8590b50f40002c240550030310300e038100501a403085102d003100074820000300300e8084556654003c8140d00285040d56481c2c400c00758007407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 77542987 1250 77541737 77541767
    0xa080910020c061504180303020c03040f06091d060d0f0f0b190b030105010e1305070513060306050a200a030b061303020a08010c0903030e0d0b010303110c0a030819 72
    0x4200b111000c02c00040a03406100100411890601128203010440d08210303034588894015081c18008a4042d40c01043c104513490240e0b45001e484a03008010300708a07130f000700d0005044071000c02600d20407100d050810f0910540d105e05504020001440040c42e4000c043e040e02d02062400e010000100980c905082c1e101c00c0401861406008801d01024000c544c0c40c3c130342d81044603110080c5410722070740c2d040c2c528406407690a03840d02010a0407080d400c0d0b0084a140c4207281011482c1d50300c00510b11040d6004c1c40c00400c071541146020703400c0d100c0140031441240e06002101c44180e05482d40d00384250700c0340c01401d80340c0701e00c0f81c0c04401400003c05440d0b0095800101a41281c841c002280c0580e8000da4804040da6550348102d0b080700d649612150020301e0101c41400000d1203403802c0f41600e81d0007481034010055a840e51030036141c00380c4c000c4010079440304140321080b506101d02c03003181004403140d03c3d00070318503203a03c12244182003000c1d010090751700c1c081050900504281e045a50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 77544237 1250 77542987 77542991
    0x601050f1201140f030604080a0503041407031b060c0c1e0e04060e01050c041a1602040f0e06100513050a0608030a0503060312091804080c030c070e070f050a080910 72
    0x40c1d50f500d248002c00c102046a8016a248110541503017000615240244e0340100c120b0702e8200d00341d1080f0340a0b00080d204580041160101d204451130070000c81000c0c5002e044208070b0840b11040300c081c650786947c0103d060105c064840c02c0490841c002d0003084030105d0b0340c0711001040110b0b8841c0c1200c96908000d00c0d00403c0340601c800d010a9034400f034203081c1000002c108075100e0410f44241400781f403160f0301ca20b000102910368142c210101030701c010a000c83c1005c07045c0b0116030005043d2805804031b0f064055031441c0044c3c90b40c20030000c4d60303000107500180e400c4e07280c244008903c140d070040c0105813400d038842012071007552440d4485401040c2c91000e503521071014a10080c031961003581c000b4840d2141c0c045650104000900712022014001c0034052002d04004d51442c84800c001c2c02551a04403c0c0f1900304800818030040c000807007410090440241080f418101b01e450151514007000702aa00700705c201904a41150420301c1c9509201410340d807031031242858040101d540905880c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 77545487 1250 77544237 77544239
    0x201030e010612051002040807060f2303060411160b0402030f1608060603030a120504060914070501110a030206070c11100806010e040c020601120206070804030506040212030c060601050f1201 84
    0x803c102407801e060510420681e018005040f0a101c01c0e40180d01580c1041d401c418000c1060783d000d4940211500c0340c41c2003487d01283c0702017264018202d00002400582c5000081103114501889003284078840c580342d10741803101042a0340c00c1c80c40702000060011044001040a65600f00010200700c210002128610790f000c14100703083c42d040d40316280c800e115035001704100307241c080141c4100d008140d80f882c0409491000c034102910740504183e03a0190781745c0600002c2014880103152183d03103640180a11841d100c0010484040410707102101d80000c010741c400a540840c18035080080c0f4601002a1911400e1100566680798a5560f008429400480c0e405402454180c07044000f42c0390400b6a0700e90f24140000d07107201c940e00c0001a000f860060040c0c1c000075090480b00c2d400644503504201c410303901c00c0220780c45900150707a140d00110400045251900b0440b446802e10070142d414100301c0c0c10340c10307518100509040e05002010820100c0c1400c4201580c0c884c074001d0201c2a059 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 77546737 1250 77545487 77545499
    0x405100f020f0f09030f07080312072003190801030206070210090b13030303050106020f0d110c03010e010b040c0c1212020f0a030b13060b0412020102010b06030a0f0506090712090201030e0106 84
    0xa83e2110a00302d00074012046ca00340012004207200c001c036802480035524021010340c8204d800940141442c0034089140710071804400e600c0c000d440c14028903802180c0c2c030040d404c0404d11480d2090020313800c10005000510040c0c881d4829107041650545030855540c104010907640d030081504000b48448000c030702c00120fa101c0504c01011a802501d0411042e600d83c5c3c0d04980f581c4800005807007503071210104180280c0300344014450311300f0041c1610f4241c4032141c0080d0a4034505203401e02243e441e004085d52a192a00c10000c8003001d03401d150301d00d1000c940d0b56040880c5a11000801d2201c03078510342c05038183c6501191050410880110781c1d1703d50000014004043e4140c0f240c0c05810245400701e250b6000e480b40d00160386042c1960750030189005002c02d0114400c08003281155215511600700752241c002650140d142c107080402c0c0d11059000c0002100d10040070184565500c1e010b0004182e00450440c629002c85000420703881a94001680070b41012123010310207600e003860000302 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 77547987 1250 77546737 77546767
    0x702090c04090c0507021f020f030c0f0d111506040609050c07150203061c0507080109080a0807021b09040204060803040801140a05220f08040b0901170405100f020f 72
    0x10b0350003541080010032000d800484081c000d000c002500500800702030f01031210031280040c0c03000d9240c412210707913800340c81002c0c0c00d42d00103941404155000201000080e00184000341c80c1c00010310303040e001c1c01070342c00c0b4541c1e84000544080c0c2690071814081407940d00c4680110010f02100802401141094044c0b6040c641c4206030a0b1a403085000d0f0182c3e1042007402120b016a00040407a200103036915040300e040b1304030640444491244480c0003030380600a020b02d074003460060b02040d44500c00c01030058140c100080240b01107400c066155040d0008030101a25012001e5415a0043d512480854028480c0b504550352a2002040024003400c05404c022610020994100300540700d51901d81e0a17541c040c2c408440e18070807001143c500b40e414001c0f0350440750046a0300c01c182a403d44400f100c1d80c0c815042000c09520003da02d104c5560406078040985000000c1c6000500d00764803913584607510a16403c414a442d00c7e1000c4001000350103440e005281f0448551b614400d940030589 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 77549237 1250 77547987 77547989
    0x6070f0503041a071d0f1e0a030f030f021c021509012004050103060b0301050f04051b04150809060f010e19020f04030218150409150e07090e01020c1209060702090c04 73
    0x220f10390743d4170380036109040c011480250502c1c06480e442500304040c80d0442d0201500c00a50f42102c59000000f012415220a1004a40c0207490329400d5051601009040170351b00c02c00c8103903030802000d54400c1b5582c0090041ba1070751950100041da5140d50780ba03a405814520020301c0c0c0303460541c504a000f101c2030801001210b1090720f0070481c0d01d50361480d68201c1d010034032825a0010702076010880030b08183d08126445840340303a40d644608880c0c1100d041581180c0c100740c1d820600040c1c059a11a00510b005820007900c4006003094030f001c480d501d0004505000d06900c804c0038001203480782130301d5030070602c09031108103045d0746520344001e60020703c0c0c02921099104d0100b00c10440b030164030100701d02d406030312840c90320b03900b480c02001030001411481100b00c880f4100e1071031500b50310303640e44500c0700003039141c4001d000a98030301440700c170986003c040781c1030003a4030402041b00004070024420080f03044508406071120039807800511240201e0300c1c040e400001420402045541c2a40100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 77550487 1250 77549237 77549267
    0xa0e0906010819080f070507120f030905090f04030e010521100504020403021005130e090f01110a0e091003080a0c17120c0702030106030804060309020f0306070f0503041a07 76
    0x141d50040b0394020107010110f07041c0013514140081126452403e103d000608038240904115080e40c0c0c0e0b10f01e20640c2e801800182515802c5d010f0316104101076014081c1ca005100441e042082d506110329900c80d03a04000d0001028040e00c0e4006450a034010400e581640d420681c103480780c4412440e60b0003030300504841d000e207004d10802c00840c2526052007514181c94018003441c0580380010300903201907001d4804007102d524001d50004404e0300c00d0703000340e05c204c0b5448040e08041c19505030041c2561000506c8100303904040c0085a6a65440ba00c0e034080b04008880c1510152540030445a200703c10340c00c00f40c03032808001030001c5619003008036021200e101d008100c80068141c800503200e4012518121000100c0d040410a00051840605419400107000080403507490780c3c1c203001548680d012001013034031004c1010552070a00f0308442e40903011380250115140000c80108000b1821804409000b0040003080a000210001c503410307450078280d142280c28000303400b0340064100186d203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 77551737 1250 77550487 77550493
    0x1020a0611091207030b1f03020a031a0709030b280203040b070210050103050304061d0a180f0e0604030c0302030d090503090423061002010b0303040315060f030503090f0a0e09060108 80
    0x5411800c0001000000c403501b000c61540b842c0c46403a050481c08411080d40502c41c9541e04010015980781603124000f5031144030300d4001203407921a0301440070801001441408881c1d04204042307400e0540555101003c007191021200000000c9842960075211060b5110f101004000800c61443e03000790151985400316102011005890b03019107500340801400c64006101c00c2181600405004900e08190184c00302c00c62600400304031010015448103080d104642030500d00525544545241084011810701c40f021091084680e00c00000d400182000107c854110505109105984000070b080000740003c40b10341c100b02c1c1d526082841d045104a10b003901c400306400c11101c400c0c0c071143d0b880c0e00e51500f07661010104210070102021100965494819107074040d40d081c0001c0c0b01940c4a1000d6480740502d05800d4000ca40482c1c01401d10200200410310200b41c0000030f80b02c0222003140d50000c084280701c0400c400380582d0780402a541060f6060003280369000c20342e54140c500804c12 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 77552987 1250 77551737 77551759
    0xc030209090609030d0903090503031801032405060d090c0308070201020c0402090d11010909061e0f0e011202040f05090a060b1509011419020703120c1a0601020a061109 74
    0x1410b80c840800380c0d0b040c1c0d140d6004220240249010b03030045d02c4480e019051030207941d580d1b80086802c46d8810301140700001e000084040303844d030b00f61040b060b19281002da0b0385140807204200b1901c49060f030003a64403426011039501e90130103d64118902156100342041050380d500c2c0b6151009402061040b4058044e402c0d004078241024401d4844803c3c1c001c10005400820381c88881100a90381d2809040010000020902d000310b40a154000d1120400380c42c20704004846002852110307400c40110b42100a0040002c1c84813501c03100d056441420000e1516034442c0300140040130f56540e10311442e41804108458a072000c0380320761083e40a00c1042c004182c0d1141040070b0a82500140e40039644184080c0000d548a8600080200c003c0a0b581e45000c401e8401030044030807201d1500c0060740162428410024000d402000b19034442c24082904d951036034591803101008101c003d0081d6000e000034205038400c0002c00c45454010764200720210f8902c602ca4450343c040300d04940923050044d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 77554237 1250 77552987 77553001
    0x7080d0b1002061506130b0d090206030702071404060602070512030403050715030b030a050607050a050d05010f03030f08090604080702010e1305090c01020304080d0e0a03080c03030412031a040507031401030c030209 94
    0x400c40703840030745011b0010802800c101520119410104000000310b50b0303451104011f07115440214051030680c0c0080080615100039490032540d130004044c099810300104002141c2c00181101c107842048420040d030030285070004d03185002d543d1000c0c0152040c0000080e60740c4480c40c04041c0400642d4040c060301d81d800d418543c1d540c912040c010990350202000401042c8500060000c58400e0b103001c41c9090762541191003511402c1c1c00c00950b85054900c100101a0032065010944480d400c00401502e80444034603100e140040001d051001b00141d1081161721801c081e03598114020104415951a0210b03440200340c112050034941c4035000540c0130641c0000309070780031100044004c1c409911010001c4449002001003550016034404000c00003c1c820009015010000c000550322460035040070007900411018100c14585088c004210f840d00c0f0a4003900c6c420001c3d240031540d40c03500312084005210701a41e1001c03417031000d40080100700c651144001128000c49801c006034455035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 77555487 1250 77554237 77554249
    0xe0a0624061e18120602031501230702060706053c0103060b03031c0b0108010504051e1510030e010606080f0a0e1c020d02060f060607080d0b10020615 66
    0x50940081100388582c8500e600380f16401c030300140c10045502c01580e42e91402c21030307a8400075980454901e5004800c11001d07130180c44030001442800d103041c2d01c0d400c1c40c1300d03142c10015800000c01c09185c1c100007214010340d15440700f01d40c400ea07480741c010012464601480b0b034079414802c881180500c4154260309081074102c091508c1c41924500d0f00c1c1340743c8d18613600c001c0100503030f02e04aa0107000a100c0d121004001c0300f030384004c507550942c0c0451000d0400f80010500003050b040b00e071242d03140c18140a406514010404c032014240000210b99482e010506414100c14503110307940002190a002e02c09641900983c4040f03031480c00030300c20252520400c0e0b400c500111007403402c12403008005548509503030000c00001d2040c4050350307081103420088540c0503191b440d243c800340c0d00c8404a1240c05a0401105611200c010000486030038640d0000f081480f48903070180c020500426101d0609201e40e03c1503030300000c018036102098110032406074542504443c001103160506032092202e08040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 77556737 1250 77555487 77555507
    0x12080601020f061b0904090c0303091a0f0307030903090e19050108010c0e0105071407120b0a0e19020f0a080604050601080601030317042405061c0c090e0a062406 71
    0x30703418000741d1528a4081d43d5a90000ca00d0703264825110034404008c00d000542401c05503000c3e9031881012403c1407121485c00003106880ca60313896042040d00b60701410941503d42260080c900412801064101128500e02a8018100c1550070741c007031000964248803200e1200404880a1120f6070340d44040c0c0342214a41e900d208049059280f1110566100d070009200702446044510444034a0b02041c2d86082c800703820600301803e090039000c0521000d02142e983c4504418414840d1400e01c2c0e00e5241c40b80800400200c1404124031044110358410500341004100a4082d03024259a00c0c80d180e41c40070207803401da800307001e0140045100007000c10000e0580340c140d1110b40d2400d0b10850b03200c2e0814801882551011a2000e41c89110141503025141c81074002e81c1c08101403d250301004100c0c0d0341401520b45807000302c098080002c1682007d070b81258609040041e40d0109401014109005000000d00c1246400c524132a00c4070804542a088e030b03c4169400074450700c0d44d0094541c0004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 77557987 1250 77556737 77556751
    0x6050415030515090a0b0a0c110d0c080306040902030a12090e0403020d080a06080303090c041109010c08030603011103040606140105070203060a0b040f020f031509010b0d0905030712080601020f06 86
    0x4045071040104146410307008002d0000305c0382c81c040c0035160302d11681000d80310b0748081c40d00c40404c0b00c81d85501c142c203e50b00d5030062003e002c1c400c100c910090186c40d50b464004114190200005904d96501e9004040294010b0b040d911103a5991803c003004840c034a50b20004616041c5000c5100064220050720171740c2d1580040002e24602c3d6026a030f880300062211f00d01549640d800f10716484188040d40c01082c1c48401000005010400c000c02d4a0b142c0310381544d0403000b48100100c0760383c00050b8403a820b070042601c40d40c030348a184c00f103030250200c02c507210740c070080020620081000d81d0b40702d20101e1f102004800c003001000030044405119081010754035500400118410045039441052804001003001a101a9004682d01030f6003103480440c1d1401d070b0200401c01440c401c4c080c040000101250111510340c1008891201e44c048c0e081c134404410743c0e4079600004c000e0200100c070001508240d1034a44050f40d02001032825404035030150040c010b01c0400740183d04005170090040310 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 77559237 1250 77557987 77557993
    0x1b070605040303030926091206070903031d0301090b04060c1b06051f0b070b01050402040b0f0d140a0506030d0f120c0c12030209150703090b07031e0201060504150305 73
    0x102d5514100d02401400740196801c14450311071043c0d00c0e42003d0042c0120320564902501c401c034001c02c01910201e54844145e06400040070071002c2030b03101d1030b0030050740c1c3c3c142400301c606035290161481d83c10803a00c5845e050340ca0f04040c903003400703403070503503e440381d4441ca50a0001920a0404854402045224070311701034801c00b01d240002c45680013143e00a0022107803420b0700000040202560081d9400090301c40c03030001d60041030041108030180034110a940c2540b0f41072074841e4040c01403040c401c50365000c0c80003040100c9101d810b43c121118542040c0b917204442d04049242500800f41550113910a02c114011103000030f0040c4000c004140030342d195003814540c80c01009000d00640c1030000c04014480d07804400003069600c001c004107441c0d6400588452402043c0641e600d07506000c004bd000091008000190b4005081802e58a41842c15500c68501c0d180c144d48005202075180d441100c2101a201030680c154440710484a0844080c000071118060000c004002800041c3c0190 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 77560487 1250 77559237 77559239
    0xb070503040311060c01090b0603011503020a03140709051608010915090209060417060417030c030103080f0c03180a05150d050c0c0d02160501081e090f010c051b07060504 75
    0x2802c0310f010681100001d0442071401c031044da019400c44d025503404a0311680f081c8144845414244140064181000c40b5a004141180c00089194040703100c014403040200e901a812070300140040802071070100b4050145041040e54008110455850f0300c3c0000d444500000d40c81391f40b4022118410300311b150340c0d954181000c1c83c0c031008c1c0d4440e18955400c40801c200001c0d000303039903100380ac5a00004401419050400707181c0159450112401030105c6101030080c80000030801045a0460b030b8050384c0941d4070440030400045a01909a441040d0b000c00705419003408503220250b60b00080403221515000e441d40c04001345640b2031040190304820a1103880000000c0f60300c07882e0015071450125041886919201d071601c00c07030225010040e048540460100f54111388828041d00003420070010a2a2603003004985c4c1c074280540540c100d8151000c01c841c0b074003e009480040c264000240022642d82070094190761040aa100d44010030107104c5c1d40c640c01c003055403c156013450b41c4951800d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 77561737 1250 77560487 77560493
    0x905060d0b06040b04030c08011a060a2d02011b0503070203070b04060f091b05010c0308061c0803090312060f01080f0c040504090c140d032010060e0405070b0705030403 74
    0x400001c0c5041c0d070440420040801c0e400420009800250301c034003c0e44082906013038074142911144505815081003210f1200c902d80d58900c243c90f62269075190110340c000c2400711045015000300c80707045071320fa0150000820030f541908044680c0c09207169214480d440ca18046410b8407085a1880042e0014000c4e5000107070002c400540050080002007019814501114111201544100c410342441d0400c498520015903051000309806d081071a003c014a45000e020b4800c004c240d05d10030641d0b64400401026032501000c0390940100c000c07516803925031300c000d903aa8844041d40000c440c64200103915490811041644800181d407082c4113038940002a003031100b405490001d03101010301c030100c0c03640c1b81c03803080b200568014510300d003800b8034101150010003c0e8405550013601c3c101031600211750418882c803418800040d00c100001407401c0210b08008029280981e46410705000051142070000054003541c001c0064030365195aa520450071449200801845608140000c0001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 77562987 1250 77561737 77561741
    0xd06020a1805130f0e0102030106020a0201080108010b0105040b070501241a0309030409051317300601140918090c01090303080f070302071a27030d11041d0a0c0905060d 74
    0x80c05407140049210345c0c80640c001d0990f0026002540180c1c40b43d120403003950b038003402c21070060160740000c001100310000001d00d544a180108070701910b00107070302000c00409501480c48202403411403080c032480303c5e22030108000f40d441206d0300c3c0288010548111140c142c1101d005685480086191038581000c14000c0c100040c9001c510802080403140031520f004800f4480c0211001c0840c1d664100d009842022140c5a0800d20000460780c60112040016010b0f07941106007420030340701c03e04140348402054450f40c0715154201c10143c0e003c00043d49044e20b042d01440e00d140c151904103020b0801114410843d02c0b0140c0010505800301e0711054840403895006081c1d850003500c0c0c481c3c5500e0300140c444150202058100b0f0035010081c0f051008040d080e20b01200104a1150700101016541d030390103200781600c030042d41e41012000c1605000220b4004085206809012890b05a4180b284040880e40210130a0901d150040c1c036038480c1ca003d13404d40310000c08890502800e4440880 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 77564237 1250 77562987 77563001
    0x3090409020f06040603020301030606321c06060503010c140a080702070302040e030d06050301060515031f030b040311010203060901060e03070306050a0c0905030601060e010c0503090d06020a180513 87
    0x60010000d00407580982c6030f482c010009095a070300c0c05030f6654518600034007240e0144d848420b0034002c0c850040f400036280305a800000e076541c0d000620300b500143c00120342c000000034507182051508541c2c4104032558000c201201c20850082049101414003610205401064210344a004000d0100440e0064129542210080c811183c3c1c1076101d50102d0b0444900055030f04642d440415279101070080380c0142400f40800794024040a4900000b0541d070744050074078280400d10102c0081e041101c042615080700e141c14080841459603030174040d44002d4141d50035000105030030500394041d541402100d00400000d4202c403e16071034888100c2d800c4c501701040550600804500002042c07050141c240200e40500c40040d451501c030401810721a0300742c0c062802a00307c1d03001001081c1d04401f00e414669002c0c02c14000c0780d03c0601e42581980300f6446219030049001d5400c80a0154650140290900c0c070f40301d800c90003400010070240200d05200342d69000c440701d08003688100b82e50f00860b03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 77565487 1250 77564237 77564239
    0x1e011509030b0403090305160b03010b090f0303071b0603050103050d05031e250201050118021308010e0102030a110903070501050d06050a0b030f0f0702190f060f05010905010503030a020309040902 86
    0x40c0c40d01d07207035030301e103608a10292001d400140710200140140441030222005002a1403108042c07241f612124900d5400140304003219950041401000340d00d480c00200303240400141a00d548040500d04610f000000003192202928900f00104e030f1140a4850340f07050340e40200052151014446080b1060f900080024500344258100354001c500d200b04841c1c01191509046960502c2040010780c0c0d080c0400f281d070045a050100410030040554504106051030b004003503940ea030100c0251008050a80c4035031b40540c03801c40c40344041c3d0419805103025120080c403d0285030280340c55a10076000303041d43c1c580c0c113030410300b020850740d800380000740081040d16201244030f0f665400001e010301c0055011a40780c10001040011106288a105910440c200300012060800b184001e41d120403c4410b0701801d41186560710620410b0904c8041c119030002c0248030301405101e001d0301401081c0f150407101170906002144914001c02a1148150140d00035400c2c00c0e0349604001c05000f05041c16 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 77566737 1250 77565487 77565497
    0xc060f040b0d060302011d0a121a010602010b010e0406182c030c0607081003030e0d0c06020a051203061e0d02120f0f010903050702010809120a02010e061e0115 70
    0xc1c0c1c8151000540034a0074442e400040691450001401c6070003061850101a2440b090100c019600c08803040107076040071034600200c0c103c6180c039541c1007990303080d100020001940001451981508035022109080e600d4440d03446001c410700080d201c0c00d000713201c2004500d000c3c4660310b01181d40228140b003400340301580c100c62200115207101400300b82e0800715070400039401c1001542000314541024117480e0420261034680108000f02d0340c00d000040c1000802415141d4a90321059214402034004101c0003040f80ea42d40041d6503922085030480d400d0284c05c8415682c1d041c49800d0328481d590103001001144490346096084040440201c0e0780301c20420078241c00743c1c99451002901c120318000038401b091000c941103107411440c04601310207038140308002c40065400303000c0c0c0301c40680c2805d01440c030f92941d8000c24188208010341420110000c80c10601d026415048100b0381107544040d03481d10345684d1080580d00f41d1031660350405024207c01084060a001481501c00180b4501 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 77567987 1250 77566737 77566739
    0x606080c10180519031a060f100201150909030807090803030a090203010603050604081c021606110c0109241404110a0f090902040c0c0201020607110a020307030b07110601080c060f04 80
    0xd0300c001c41004c000d060b01004004107004000700800d40700a100407541c5d980d9094946480018502601281c00c940100e04408100500600035081458104a03e14801c1c40c560b4640340303000001e25040909500264602021920003400b5040460540303400030042d5140d070351400403901c090910300c00700b00d8043d96202800070105005224080c0900c1c403e054040c2e8458401940504100004001c03014041c0304110a40d00c0341040541c4010442d4018408202c90112001c1110940500080e106c5c695080c070300c0c404200901c000c98221001003105a0131030b0500020100401c650188100740980c0400c40c1c00b2501140340d00308003444800340100391418039a12400c00750110b24031a40039508003030b12400110110b00c2d00b40a06245a101403404025803c0790380c00003075458002504807024004400c60030640741d0300601030b11507015009021507602c0e90b5245031010280270211503110000d00308410800c0e60361000308981d412030300c00c1001000030340046410400d580c7d000b00c402c01e00103001000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 77569237 1250 77567987 77567989
    0x1509140901091e020c01060f05100f030b010c06091401050c071106030603160605040f0905060904031121250503030a1509060306090507080309210106090e03070606080c101805 77
    0x284103010100700046005072601c0d9248d1006032058100d944a6801d82c2103240b41c0e940c1c4100515010041c03490080340c080c103000010307114130703681401c0a80500e0070040c1050034420325210344e08505038003000800580d0f0711300c01c040c022805036200041040880c6400b800c0c9502e0300300091908144000c09031084003210b41f000e00182e911a900040110700045420080c2e078004450550041101a0741800381c1d107890000074425020080c401400c0c00029605494100803c00100f80c2c0c29005a0402d2205a0441205080e80e00150405004d600b0503002030b2074070022121030540c003180e0000040d07044d80c03a14910342d80600301e60a5182401c1d5016600082c0c0c000c2135000340802035003e040000303542e590303d0034010704143c3c0c26084107056134402c010094264075452082d41c512501c0b4105c0d0801c415585004034050200e41e807107442020f09200e00f0b49203120010000b0041c2520400d020480c0943e1260301e55142c03030840340403d5110000c01103a0401c03600810a04000b004507d9018000640f110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 77570487 1250 77569237 77569241
    0x90c0301050f040b090a03050a05030a0f02030129070b0106080403050c120c06090c060a0516020a170f0604050307020904030c0b04030503070e03160902130b041509140901091e 77
    0x44035107042c0c1d4203a00501c01031051503d545a008100c41c1c002d092006a640c40c090210303c01ca4102c08100003000000400707480d9580c4c041c19075001000015560f0f965140302c090040f0410744841400719108101c03c85003810020100c45003d80d01c822020400d0386000800e940c0b10100034415024000b04010100c8034002c14070445045440d032401c02c0d510b802680540710720b4000001c0002103d940242440d4401c0e42c2c880d0300361004e1800d5850180d540b10070426444210040300e07400250403104980e400b02e02c4503034000c0340300c03090440038084a050b00c004503070750b903a03840c01547d000e405600704102000250401002680d40316000781010000b07103585940d0004000700172103058001410200c103010541398020400e00040c070b8200c3c010300004c2d111910800103c00300340b1a0312206035001804241510038420000300030001d070462680c8039030b6100001014880b1034031190700080d10046000c00e41d02001b142801044501408000c0a031b07081039150300042100f4401b06404601300440000703071580ea8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 77571737 1250 77570487 77570491
    0xa020f04080a050d0e01020a2003030705070e1e070507060b0a1d0405060a0b0a12060e0a03030b03011104030b040b07021f090c0f060f081b0c0c28050405090c030105 72
    0x194010200340a5030b0343c008001340801d0302024119003000c10000e000c18041414070795610301c1022141120700840000ac1c1c03961040d20802401030003281170018030030400d0100756200b0003414180440d82c041c80d003400601200c1c116022000720b803047c080d01000c03032201ea2101103522005800b12a14a8646020380f080c42203507006c1710668800c3c2130810080107824010b0a800601c020024006040c0074030006480b42054000c00a59080344020f00080c01001e80248684809050507520000582d0800a01034031406220a00035802c1c00385e151940b400600c00c5404072038105015203002c0d00e965851a40315500a4110001c41c81200340c0280350901240f0703020610b00101c00b0000c0c0e92080c0d032425003080d07100d83e4880340032501c1c4480100300302a04501c002c0e001d80080c3c5010880340d66104000c14903018007140c0c02c00d44500224500728074500c00119801407207030413103c890303048110207115088400f6408400c4458840d580b000c01c028286600882d80007100d401c1500c0078010018007081c00c4840c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 77572987 1250 77571737 77571743
    0xd0608031b030405060d0e030d0e060f010806100909060e0303070c05060a0606080412180f09050f04020604051210023402010503060915040903030204050a060e090a020f04080a 77
    0xa11280a080228000001c02415070140d410980b41900051075030140640312074513151900d510740e110050a20440b46148602c0d6001c0102000d5203031002d6513108211075800031090b4a00010800c8180000c00a1041c6105c9440303001d90303400c1505540c00b8002003481164445d4507910342c0030284505102452084883d03584e0b00d8034040c0745040442c80c002c0c025120050551425406119140d4030400c0700358015000b10442600342200c0c00c0c210b801030345010b150000d181c000f440120340d50258200440885045a0342801140c503044002c442c1c102007030710000d61005040004101d281440d00c00d0503904040d5030296038151802c1d00c0e28000366881046d1071410f010480312402000030035030b02020381c481644558a00703000d42c42d0380060014030025120900c02c03440da000180301c060900015100f00e240207081400101c0c030514014001c2d4016018992050001030008204180300d0f40180402e80001801110740351100440704d402540714460b00140c07070404200101e04003404018400c14544 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 77574237 1250 77572987 77572993
    0xf050a0b0708090709050c04030f02130504030c0b010501110a0b090708010e0d11190b06120a0302010903230714030408070b0301080706030e0a030e010e030d2a030f0806060d0608 78
    0x80c01994031404c0070030030b0708440c161a14140500000780c0710f040a50b07083d85e903c4042107011001ea4000654003288034036000842d50300b4501040200350340300c000415030507c00c1b40d4511042c0d0f200c100640301045145800030307685e07000c0c00b01c000221b03840361010b98104644c00b090b5070031035484441040c2035460049020702d165115014a1080c51707400128280120403c0014041e01c41c101059a0841014a10060102c3c40800c0100e1255503072035084015004100d012101225120b2070003074060081c0350000e0300440c0485171500303010b55900001c080300070102d041d00340c54000746070750301d0202d031701d040f91000705e05d04c410f002c082030b414000c000c0600a060740d004203588942c03420038000d10348500354000d0b904040c202000c1d400b400b0000925411000d90606040150082000c01202d05508030044a503240c030440106050306900a025458145200041c084040800303006407560200c5050300200090703d41c500b514101ca114030a059045036004051501c4d184044c1158406e5507503039001000307039170 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 77575487 1250 77574237 77574241
    0x121a040e031b030306060f0a0203040504020a0e1002071404020d1512140109020f0f030114101703160b090a05030f030106020606040908030c0f07060612050610120f050a0b0708 77
    0xa80449800d0b0b1a2030308080103528510380840860000d0042c04091241c000b400701d080510b450003407040e11f01400380680110b455081c3d410000384044c05072000300f4041c0d0f0b002c0f06814510384c404140d40e0148e4001c2d24503440c100d0319000512000354030001c3c0601041d5034940194840d43d20705c07184d0300003d000c0e000300300d54525043e040140d40c180001c250300f29568580240c0f0401038890407004410703410221002d60080ba80c0749e002c01e014280c000300446d0000308000401030075502440401c070996041d2031080100080506401f5900e2180d086501903c3c00304c003034404005203008107240e600002c88800d5408021050f80c2c1c40745103810040044410080100050003010380c1007201e20350103401180d00b400307a50300e01d444003601e43c80302610100000c034000901e0140c3c0350300b00c812140000d601c05020030269035a00c144000d203020b0a03a00311994040d10002c00e024159030300c84e460988003c00308041c1a540242c0d106103d07810042e204803403038050070640e0008110303990301d15441440580c903092883c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 77576737 1250 77575487 77575507
    0x31e020d120f1b0b190b0409060e07050301180b07020703060507031425030e0f0f1b0603090c0904031b03030b03071706010e070e130911060a121a040e03 67
    0x40b0500c40d0841d0b0705030183d224060110b6582011541c01070401010f41d42900b0039050910054001200740c29045030030300d000705e403c1200540c8283d0301d01030340c18161070640340c0b154105400d0b26041880c0300c0100031900d0300ca4001c03135600110513800c00020300489602c507035295a81c1041d128111600004641e40b040200b03040ea810f50340950b8003040302003004000112440851500c505113072503210030151b952464030120344080201101c15051501207031810f134030681096544801302d20131101c8040c0d0b019061803040c1002e03020b0b40c0c041c00120020340803100141041c03000502004100b035080003c541034000c111a000220300e07000034026900401e0080040082c1454201d40d98401a9000c0024041c0e07500780318041504c40c1502e030381c2c10f1401700030389450000716401c07030350f0a0b0144d5101705541c061102240d602c0d4094680144100b0903010001030010400510340207010f40740307021440780b0342051a203000c260300844011070764801e0501380d08c0103000071030121807800d04e203c1e6103980b000622040e8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 77577987 1250 77576737 77576747
    0x140f030a0b04030909050a0209010c030807020708030d050103050c01030e0a1203020909010b1206010219020114040506121008031c0b01140c0d1416080a050c150105011206031e020d120f 81
    0x4c00f47c114071003545412015800240a040c042d40040c04100317154000c29841c920a0000300010007240d8201d81d04c55034412188001010300784411105d41c032418039100724a50282c002c1d003203603444440251038403445c140c8a209030002101a0340c01010303800c211024032a901c01e4810741c00781c016a03030159100d9000030038444009401904c19810356121200c0c08104850710852065265420b2130148807850100b040b4070020b0145420855100501162810b4500c4003401028800c0c240000742c400507030354406220307440b0f10034040a158581a5080004e0280d0850340000d103420006140c207014884d1240d03030403081c1b504051100c1c245038200300f10b1100309a81c45070020b01d803c40d2959459184c0240c140c00d0f041e01a4032001c00920900011807a50707840ca004030283d61001420300240e5102d90190141c06582074024042c03540401d244e800c40440d035010502c50750382500c0d030015411028000d05803107040030100380f1504aa010825103140c800189140000c40c18082d215254043c84140b0031742c0c00781c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 77579237 1250 77577987 77577991
    0xd1503081801080103020604050409020d0b070c0201091502031e0c0708102019020a051c08070507050c0111070902040b070326040f06020403061814010204140f030a0b0403090905 78
    0x8100f00c10b00f001440581da403101110105c03401103d0000d90840bc510104416440040c4041e00660341c03030040007031180e0060340b4206654400d980e441306564840302c191007502040c071045e40043e0b0041c4100421a60758a98500c1e1600d040c030f00079402c040305100418680103040e04500c3e81c54000c8c40f40411280c1c8140243c01003103016022030301500788085054055400b903040003001480242c1c1410125500911090f0050740d0018240c50030b02c482e9481541e1030a505403181c0c40041c440c0c10000e44414496400d545e24190f100001d059901145401141d00d08440c000c0030f40c8501501400140c0d40e140c2d48004c0c0000d000c044021a142c0c105410054041480051840c2e00700d050b030001040368880c0e05640c540d00c95840340e40400700148508106000b4011a00010807942c0b80c4041070f650004218000210340d445404907120f521003090031a420b0340254440c40d01030040b000c1c2a0105450b00b00c04280c82d43c4000b404807201c0181c0740d00c0f04584510151816030204d49000804c2c400a0854040d0300d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 77580487 1250 77579237 77579239
    0x70f05100603030c0b0c13030501050603060a05130f02060d0f06090605040902090c030a020712020303060915010e060306040207050102030c041a0703120513020405150a0807050a0302060d15030818 86
    0x54580b454801a002c5007044000900042a504c0050f94070400700e010f507149183c21a6401c2600740e100c4c60001c2c0244401c0d41c0c0144a84900d00c002100c2020901034548560210608502d071900207a03070703581c10350726075683c120391095040c0300409800b20a445042c0500c42c51900c0402c0461034130700007000310349142e0401c41c081c609180c0b0200c0540c5030031410b03e4010703480b07442181e501e681c0d50081200030300810f0002018210810703640480b459000000d9405003000b21010911070326581031640c10443c0788181d05021407505001c800032854030402841c0c1c070000c042d2001d450580f40e41c0d111400ca0b03200b103d5100c50350700045018400c07038800c0d654141d132034001c030100780e490000b00d500c010f009071000041402900e0740304c00c00580100c0721074450300c0d00550301a0080c0030070700780080114104d02c898000f030350080c00000e40000f0307803a0f0000750740310443c0c1b80585008500b900f107400344081d030361102040140103500d075800c2035070b10407484142400850040b690981c0380c1c3e42000e407054040c0d50301303943c0c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 77581737 1250 77580487 77580491
    0x60d120c11030c180c19110d08010e1303110a060914030c071202180a06090f0207081206011803120f020c0307091802030102040902030f0105031504030c02040b06070f0510 75
    0x5500d16407914003100c04c142d91280192400d50313442e510150864440d20360304081d2084241d0a020035142c000d40b0b580607885010003510a0f04c03040420441d0003072001d2060b0028802d500001c10500810203080a044600034540448a41d4074404107a180c507203100030844881741c0d5038030120207000958180040c00c4d190100034500e0503000395080c40e65034000340120044201a20500d104554a040c894250926081d1355050b4034a4410240c1c0700502092181245050400300e040d2648989803080310b088bc2d5004070200d0401400940c4500c0000004194506201801c042d540c0e80000c1e0300c010340300462040c070f28440c1d0035448410051003210008080380075513101d04101c4500390303408030310402552848480010900c1450352114002980303441d0294140d40300041c0841c6c00c40058000358400c640101c121490344c2d99079410301d9a01c402042c1030584054504003ca4006031299801220f00c030300003400492640c20550003e08254422401129040c12544401e4100407040c020002800e82030326013 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 77582987 1250 77581737 77581753
    0x20411040e0c030f0f0601112b02030909040b0414070f05270613020f0a080a06060f020d05090607020916030606020105010f031704081905060109050606040e060d120c1103 75
    0x445105000e07240040b250801303400101c02ea4070030070a10361088c0d0030000300e40c0d281d0ba014200044c42c1c0d9003100245112158440c05aa0003800042101c0c440720f005014503295036034507118002d001402070310448001d00d0034408116a0203007002000c000d03085820300480b00514107004c00c50403002c605401042880e040c1c5000703045040e05010a940204182d451506100c0764540480080c803e03130704003001d030303030300103d20318046a9000c0300311807040d040343c0c03010400140c03600c10035920304594152950050380075071b000c4048580310704040c0281c410050011418581d160b8000b0b8070300b55003141c803144d0403412964100d00441c2c0c1801084000d0000d40020002541404051000c19401d03000180c0a5281a041003e540f0b002108940c0284500c00c1034455140c01d10300b4488a4150f0514103a5683c800d030000800c01103c540b040b00e000300c100402c910300c0e140c941101003000d0705005003110741c494980e02d50100410b91300614249114455070321211440da56103855068040381000040c040d03840102c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 77584237 1250 77582987 77583001
    0xf0d0807260c0a0e06040602010c0e040e030a0c0c0503070b0715050105010503011a0412080403030f050415030b0637140f0912070603050103120503070906110a020411040e0c03 77
    0x680582c00c582c00e89840d5a540c00245401e0301d101e03205025641d001100003400080e12a030643c0447d0b4420701a03503907800d40100b41010801940c2143c5032912a64008124400a42d0f000c0d59207040b640c0c0c40744950203101559900000c1c1440e45503444010711030400201602007140c0720280e24645018080100802e50404000800c0c5000500605602d0905088404801d602241c151070003440c0802c80c43c0c0c2404120b18100900d40c000d8070003200441c0018020681d00d038010020380d01550003101c4580c680d00d1010000304c000d4045002c2d8103030000410002048020341400c0b220003824241a81c2901c0c6241003500889040440c40030f8008011403440342e002080602022500f0011020995945a42006001601c00018600000024458140c0c0015902c0d09504520304a85c000d000540121066800507201440116604400903030401414040c0d140501002d55401180d081140c00040d51980803d0403038142500707001d01c60b84040f40800409185601c11544040c40e4110ba42c2035080c105 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 77585487 1250 77584237 77584307
    0x30118060510020c0112090b1302011107080a030503060411031521030f0d020c03031602011a1f050d022b020403030c060203040203010f0504120305070809070b03090f0d0807 76
    0x4111810414211840186d04003c2e030050030215401c00700950ba241000c070105110349041101c101d01080707862201050849001c1101c0c021280038602810b0200c0880c3e03000c450b29400204469403040e51030710074110b4100b059010710310070a40c54035aa01c0000324042084003040300294020007052282c076009a03041e102006907900d101c0c480d4175107515050554280d8029025071488050203120201c10418800c10005640c424007d50b50001c0101d161195039503664100c420f20142d0f0091305551000030013564054060b10108841d140190421110360214400e80e400001c1810b142c40a61060703404074207441d0b00310701402d0b6480c0f400314540f40c6982e40140ca5000d00080140059501000050941d2801c1d04000b94410369208104030b02d10340352500301c140c52013501d00900000e16100000c0e10749402105d0060103004400010801d0a14150359001c0581c00141196400d02a5004040c00d0003820440045009415110000c1510702680d0007099802d40e4980e00c6500c0d4a5441c074522544011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 77586737 1250 77585487 77585503
    0x204060509060c1207050d080a060506090d0302070801050c090102011a031c0c02060d061403012d090503072102030307050711032406040b0303030402030705100908010203011806051002 81
    0x140c51541d240c050001109013021114030b1020385607480003812001300722001c07520700d400801c1a01e901d00c0680351b09554008681d86801250741143d4200200b0b501890030312110358000d446481181d0400380c450000900f55201540c140c2030034030000c00c46201540e028091b03900c2c0c07042c80035102501d41c0f48000000343c0e5401c640320194000010300c0915203d013480b6046c0100300c40d40191038165146103254158000300b040d0320440158005065510356945410301407501c1e8548001c80c910504014140044e481141922250070b40a9a58910b0800500b091018280c5580110312950307158000240d03803a0a60450301090085410400400201039081341c00d8400181d000041c21900b9521240070034030b040c0c8000c61086450700c0ca10030003403a2050742810303544960416241480170b030300701c1014181e507400203550007907051b00249006c3c021410450503540e02c148c460f15290301801c1d9100d0a80c0c1c00ca90007a00000c2c00c524100c2140100c17070105014a100500b826114011080f600d00d8000703480d2994 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 77587987 1250 77586737 77586739
    0x10c050306090f07050c0105070903021f0804031206080f0d020606030d020d08280e0d0c030c0609020301061509030209130f0311070b0a020106080714030703060f1d1f0204060509 78
    0x1102081300c0078800d2080d500808600b0008100034145188040d12031905807001301d12805a40b1041d801c8003118500e01031f50302c1d10f0307501d4818858465076416200304011301d84011007030b40c0d251000624000200f010441140140c0040c0001b0109240000e092110081000d80694001c0d8035641000740c0c0000c0030013800240d860b01400c1d90300c0f00d84401341440e00350800c0711200d07542180000c4107410994480c903c8018803604403221b2003c0d940307080c1c3d11010b0f55000540030582c907411000c0418900d80201408078401000003900b240c4458401414182c8842d03244006406410103108606000c48025040051105040c10016040e5109100403003001802030800002107070b0b1900d19070f030400001000c0c100c9640000d8840142c018028002d040074414407450344568480010700480b41100080004000b6020b4412942961103540141c98098032a1030042d43d900780c030318034411005a01c1464403c20a001d400d10140039131401e0410700901401030765592041108001c07150300f1034211814044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 77589237 1250 77587987 77588011
    0xf03061b0801090209030703120f0807030b0d020d020d0803070503090105010602071202040f0b0a0803180603010812031003021c14010507081501140d0b03060a060b04060507060f0f020309010c05030609 88
    0x445c0030040781c10104554802026024411841031180b5004581099a00f0107661341403500e9803170791401c6003030342c00d000011034001c501079400034054103156100c2001c2c03e0029151303951405255540d1481a0300844043d00003900c0030040c052000c07801e0003a240113160901c0180841c504100081d402c80381080b070001d01c1030341e8030103201304000925002042d6103000103190840d2103584502a9840e07a0040710140e00030000815914a039203003c2064a0580f00d1140050020413252070b0074586541c405881d80c820050701d20000401030b650501c02861888001041c6084000ac0340380090481d00340300004a40c42e4140001c108025a01044050303021000200002040d0903d10050354800c080e00a400302180001800004210f16508151a014000d800310f810a5480160750012542d090180c010403000c100010007400c0d10400240c40c940b4090480000e950038441c00040485550a605040043e00881005410071003803207040d403516290b080031851481d054001481100700100310844440c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 77590487 1250 77589237 77589247
    0xe0c0c0f0f010213060908120c120c0706090602010c1d0a03050102070f02030601050105070807170408010906050402030d03022a030906040e04170c0c04090611040f03061b08010902 79
    0x14020400d00c03100800032000e952841c0700c6186514080d5110140d11980109144e00028907030f4400c6044404603070004004d001221140c5e81802029441541440f440b841818a00360140074100002d01c200d4060340002d040c003503d4440b01501303219595102d101507900d17001c820400c1c0c0d80c011281440d40c02241841c00589079240340064501d48464002500c991310110f41c000401400d40400c6609034004c1b411180c0d2030703a8a40c011640ba1060300001082c4a405016410014000c40700008002190044690078580c4480b219821592a0881511825103039010300c815400c01303001c0c1c40d48111140ca015858140c03810025514400350081c145059001e0701c8202e205c40b2418415074092450080c4119550780e07030381e040c000c01071006031010307505280001e00307440181102d103040b10404500c9501900d501c1001008010060040c2c80c0d0948445072500c1c42d50f0283c2039840014805080742c20b100d200e600d411810a00210b60072528507103018400c194020b000da80d00518010f0455000010160703440c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 77591737 1250 77590487 77590507
    0x30105010e0d240501051e030d0f170f0709090501050105040b0706020904020403050604030e03010203070e0405060d02040606020d02010b040b0604050d0f0807030f0807020703022404080d05090102070603060e0c 92
    0x542040034490b00480f015051041c603154280c00050407a04100d52003036031800e04001404142c80c945c000d45525038003510030744144074001d074a105100003182c1040d910081100c040203848000c00c98070101c40d08520000c1040340e541101503040502000ca02c00c0005604000020b0054403660140c4000c10a02041103000c00800e82c04803600c40c0740140c000e540b10340e07907480d0182d96403109031011000301e2802007031802ca605051003904d21a901a59030201d00c0000032090000900d4081e1900e5009414a24440b02581302e0b03010712401020194002c02032032100060003400c403060000034601c03560914827420165a9a03e00f88c0301031740c1d000c0b1113071100021a450a030902c0c0004120041440070f0100340d050602d40c1100e28044903000684644160343d441c148101d80355481400025441080e402481c070060400340c603051784148030600103c1c5440c0c0c075000428508034450310910009100041c1100c00e0f5681440003800030280b904060002c1801d200c0d1b02011031000a04149650002084035082 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 77592987 1250 77591737 77591753
    0x301050709053a0f0c0e06010e10032a030b0607330903030618050402031b030f07090e0c12070902070204060e04030e011d01050304020f0117070504030201030c05030105010e0d 77
    0x5050b581d00d4903000f6006092402807900c00344400181d51102071444001002c01c450b00ca080c0c403d2505a6403c41ca1190303a0341080f01c1c44030030003180d20415a840b83d210341036a442d8011682c0350141c040c2405100c00d21401c0c0142035450091005001e0107044c000c59002a801d600b03c986024502c0d0441410070f40e5031103800c807540c082c1d0b03250242054240f00c0c0503414140c06501140540c0d005580300e0361910400003540c015100c090300c0081d015031020509000800c40a01c600b001d154000301a1189000b000500341d180c03414a41120b1034066650010514040080100c00201d1030299044014144580e5042d5201d03502440b9030f20700103800281c010110b60ba1580824050031140a4006250525040c01011103903000c0000f400700300004448104a5030303101d0b94403226401652030901d540d95030b42c00c0c0603924101c1d4807038506200d045a02c245060081c2244240700c1c558554949803907a2540c0001820340d82900c040d1170070300ca000c000600c503590740319041d205a600181c0f007a000c240114604128 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 77594237 1250 77592987 77593069
    0x901150c0b131e030806040c0f1d04090506060901090e0307061505040e010b03010509030c0d120603050109030f0315050906061b010e07050102010b040507090e0a0b100c02030105070905 81
    0x80b070340c003414444a002d042072840d42803c40380a03a0310f0001540c0d500c0c3c1400102c42c6413420183c04610a1325464600a21481c0e0020300e01c1c15040f0101c0d040c803c000042005da0700024411561a00030000300001424826030490042404003024890408030310301080d201c1c45100d1000d418140c690123402c1d02c581014044000400001c0c2040100403416441a030003441c3c08071403d07210f942814042104c107240003040c0c45201c0c0320380c1c01801081d44140c809686810b02c41102030185915500e000011039428070039088424080d8071104a003100319000101244c89080d00d8a03c2501e91070f4041c000b0340c5071900700c00e070301c61010303509a9981c550300b03003150450340404c0341080565800d2843d4010501740c08074080088500c2a0028000e822140080009580e01200c202d00007030040c01d02002103109540c0400d40040c0c540d400003d80855a40101d50a01081010f0001243c1143c40c1801142803d20440d03600c4480c078a0b00c80741080c1010005400c4603031164110001c182007600104e54000b50501e00741d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 77595487 1250 77594237 77594243
    0x90218040c0e15091003080a030c09090f0507080c0309060106080603010b091602190b1b07050106030605040c050904050c0103020a0e0915190b0a0c0809040203070c020901150c0b13 79
    0x220083c50562012002107004481150040c100f203000310700f8900c074840d504e0b03080d242d02920150918800e10000c5008002c42d10020080100519000803040954424209200140135010a0b00d1601c40b501030b10301e0380c01400500c0303009820020000010800b05906064500910b4882078688a200009014124518105510502c030b402031184014030141880e12616458082c0e401103251007225045103c0100b401400551340d40b40080c100d008020003044984082402c100e00b040c20a0325554211040e9400454041c3d64403400d00060004030f1b03240000074102140c90031684d20745552901e80f0741e10714200450600d0303004544994128002c050300e203001b02d4098004c9900e440c12694034840300c40004802707405506042402071505806400c840151044886800d203000300300d0704115030040e540681170f54011800d0004001c1c5544a0000f1400780d841ba030f95031801d01ca003900401181410690180c00c40c1c0f130605031700102d100d42111105030055002501101c0719030341c01d40440e41c0801c42080c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 77596737 1250 77595487 77595509
    0x140c19080702180105030c0612041103030f03010e0f011502030d0c050405120a0b0a290109170a05010b12150c040308040b0c0d02070513050403090e0a0608010f090218040c 75
    0x4580d0380c080c6030035500d040758411002c13180c7c8040c180041c8991072045014124410345050001000b01d00803403e021041c40c80035045a18180030120000159017083c2c000860340900c18080c030820034106440d19000d040314080003050583c9014029680744240d890800c00252196005005180180182d0b402020080c0c800039000e07251880c8103480b40f40c400022281c82101c90f000c0b50044030701c1d21808552020094143e00100c40055103c0b80c0716031200c00a0b4108441440086040c09051400c1103031100c0003401002410300e145021420740300034200c82401040704c0034106010706c1b00004c500445001000c1940520b48400818031040e00c542d0300082c0c800e20f0009800110442968001c0410001d00c0080c1d0341c03800c40c4a0002c980f0382c445840760a0340900d0400140e90110141d0f071185400c580300f0300b4081c031161358544804c025030f20125180b0340103e0380c8060801c5806001c3c001c00c0c1c0e016031441010040424264006140e0748640d25051000080b0103000600b0050760038400d40142c0345c02d200c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 77597987 1250 77596737 77596759
    0xd050a0e030109170409051518130807060b010f02060411010302070c1707360203130203070b1b0309100f020f060f10050414041e0b0412140c19080702 66
    0x8104913541c800d2190307800f641d10b880c001910704811005102d0703000000070030011505003e56446600c0600c007a14003011411900c0440700024016802010098031400b8042004030103c000507081e014415000415500b100040100140f40d50030341c00000402400c1c016100d18440c00c001c2604102c542194406d2640000340711006003000441e0401c4401c0612400205504064a19045a600c7c030398561610904100d01c03802e007407140c02441d406011038210f401800103a4000134503041840d40710b0220700400007618114043d03420700b03101c0c0040052005601d81075803900800c0441000f0003903001001900044030b00781620074411414040c5080c003c541c0c0c1400c0028500c0443e41b400c0d81e2031507a90340c2a600014544c10310780510b05182c1d110002a81d06035845480c0d08034020051001c0124a0103c070588000056542100f1070185004045c005480c9005640241c420043c036000060302071018040e00b0b000e01800513032207002d1084807100c08a9a00e0514010a4a00800f00e000b903010512800c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 77599237 1250 77597987 77598023
    0x7080c01200c070b030a02090d03030b040e010606091404140901020d18030e01030f020c030f03040209060a180c020c0a14130513021c0b040507170d050a0e030109 71
    0xc45901c01c0300301d0004010401c01285900c0940c891018082015041070904110304061040915401142d001c000341c64140c0301c0000400d031600d4a03c0460100350340d046902c00b142002d00c150400c1c101c1070b5008002a90901d20060942c00c0c461240580c403441c00c501742030450b105e64100031148040024010080c0c10105400c6020b9080b04500066440c83d044a240e41e42184028842d05690507440f807034103d15001004401400e052001d94800d50b070208112504448100010180d40c1640c05400d41c480c1883d204101b5415800317050a84203c100c008103000d00403140e1040708640008810008001403400826030800c0d8544c4402c50713000c21402c0d400a11000070180c410100c0e40115544030f000b80c80024100112002034818005820613248410018184081400c113141460801c14215490a07990030034174540c216803c039a00e8020305401c00084610940c54201c8164101c081c00c000c5610341c2c4011310f140035000140742001301110300390900340c0b02075122040040e008100201c030040212 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 77600487 1250 77599237 77599241
    0xf030412020c01050f030a1802030706020304031110081603061d01051206071b110a1e090e0c090402220e0c0a030c06050a05040909060903030b0f0d120507080c01 71
    0x3035101015000702d0002200d00e40c0709104030307000c03102210002410360300d91110541c02840307584650905800115405005039800708000320003042e446d4000c41c1d40358258903001a075002c60260090080e01641000076a99400540c642e07401320b0303e28445640c0c00c000a00440c00713000c25074010a074401d10780c8410201072400d00740040c142c030002e884030090622a0341803280d0328541200c001000625600030302018101c2c102881804a00400c00444443c2c041000110100b440c2e81c09001e031125400f40c0d02840455901c2043d00400c5080c02c20020500c02c04810b90f10707114a003144500c5240c11400040442d41d55803400102200c0d880c1d441086600810461b5005004500903100c682c42410785214503480d1024460081c0c0f9480b00d03142100900c1d01005807020b030007041c0790b401401014040403404024074401c1c007032014002c10b4049500707880f5003405800c650400c1000c600070001c21402c0c4c02207032243d40d003960b24154407454200e41c204d6204800c4603140640d0740000e10520300040d41703015500c815 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 77601737 1250 77600487 77600513
    0x5010303110a0c06050c0304170d020d0c080301060534030207050f010212130b16020f09150d0602190801090606050a020723060a0f171005150f0304 65
    0x1e880d0000ea52601c100100d540300c40e0b0034001449042c0d07100c4107010b0707a44500050400c00201c035003102d003081d07116000011080e00c0e4013040b540d42c1e032241e481243c00d1a410080030154101c0f03030400c03a1a0216541f20920948014003400e001d0000008641903213112840c2076000d00c01c15161448103a8031076601c086941d16469006500500c00c0c003401088030302e44115010b203ea50140c0082114440000000300e41e5045003034800d200c040c2c040750010310340110740d00401c801c2c2c102c40e041c0000504036204010007454003202060080c010881000010302c10b690300320341340c2d460840d50b0001c0100546001070280c07003403101280308820100e0034003c000c0d0b0041d0405041e2038420200b48001a240d4608840a004010030800164440b603001c000d00b0181d0741c0f907616160742c5c2c03d1a081503012214007185040d485641902c001840c50405074002a81c418040f10341c1c01e88100c00444681042240d000c0301e000383e40501c4c0d10440031074081a8944030b0f0304088640382114050b160b5240d10f841d081542c205290 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 77602987 1250 77601737 77601743
    0x21c0603081c0c020a030c020607020a030c0f0617060d060b03240108030306030c060a02011b050417060405100209180112020306130803040311030c0f0606190b1806120a050103 77
    0x1c0c1031161074410643e00a20224203500d80c018110301180b52805c50342c1c096030401c02c0c1d030007040800007000540c4524866030f01840c05803445000103403034401146900d54407139000004108403100c181605100b0001c032903400c28000c0701c84c1908004142443c41c010907102c0b0300c1c240d062041002e07030403213440d10b0b60b102448090815600840c5c0d0703036a03420389500c03840201c4d0b01560680120900c00e207245440c0d8041d1040f011244000202d00304d1a407803105114032504050130105002007010814143c100d00ca40c00b0401800780680000e00345542c50036542c00c03d8400341c0b20f200c7e4010441016039111107410011070490070036409101e580d00e0780403100c02100741200f039009002e500001824140c407609500121544101c030070785142e03580e88045500c000140305d01d20490008011200c0e946034204041a00c0d121720001a0025003009803c2001607103d401d00c040c0e4501e2030340020400c1d07401c000c059618030f054401c060000c0e501c1c0440002c00324821070820903000ea60003c00d101c6c0394246a0b104505881c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 77604237 1250 77602987 77603017
    0x3041506080607180b1608040e0103030c060b100905010807050906040f1715040602070201030204080a0b060a06020703032f07090507020705010503010312030902010219050f06011d0a021c060308 85
    0x113046000607408003118090201688400c100b80d22603a8040708000032024028018039041c6926031564860f08542030b801540000d00840717210050041e04d118060642e401121040701c03c18560344042c1c101c00103441054107000c550760000300c20a000e181100d445010040810b66a580c44801c00e034058002801403030a01014850b00e585064800140c90609a0614204c03e140742c0d6503654820203940b2260049040607000c1c00300244414040215140a42c0b15020b501000d207040c009101442d00558030000c115841030b501080402d070000700800704a000c548914052060544118100e07000880031504944030322200001c202da51544568001c0b92203600761031950381d035200115a540070a001c040c00d0310184c0000c92841c28025030000031454418016140b038542c0080035840700c0c0300703a400c0075901e5170040100891f0b0110280009405030860701500a500b6402017202c400c40703100180030800480e800103400c5206008440903a07616084104107002c0140c49150101e11904104002d1644d50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 77605487 1250 77604237 77604257
    0x72007120611040f030f030507060f09060b1e0d170a050c07090605060909070c06050112020a090e0307170702060d0b130b0f010f050706140601080c03040b010b03041506080607 77
    0x150b424007194221629401d14000c1242151240c0da1280c14068003101071104c10849640020118050740b00c28a000c05c0c40058140c60760b0404009a8118500d4280305440d01c15845103962100141c04140d4071041e10a040c101c5003a19084107a00c241c880301c0032903204003054140c55039610200601e8549440c1c0305450b4446d42d9080040c1c1070b92558000d0384c0d0310840610042c21b45081515905074440010325058030040070649858040310300a802070300d061410090780f2415030904803900e10050110780c80c20007286d046401d070785c0d45030b0144200c0146035103d19407084002e0001c5070f040d2880d89d9001845107580d00d1040010000500e0603040f1540503461400d0340242811076032040c82e8860202030305403407640b100c40004440c0c04404501c40420701c1420310007200403400c0c3d03200b034100a4504180a02c41410200000340c558400101000441b800810802000941100c1300a0441d121003004549940326440c00e4504c0740c0c1104800c0406a02e0030000081c10000000d80314020000e5072a048010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 77606737 1250 77605487 77605511
    0x607090614041203051204050313050108060a0b030c04150206060a05100210051f091505091b09120d020114011e050609030102070b091b10080720071206 67
    0x5680c0400007421210148001c11035403003d60005004244207103003c034500070480d10074404049050305e0a481d5503001041c0500ca1400002d9000050310007424420124074102c0005142c40b0018002c07401001400b0020916010841080d10041c01e5981c0390f80000d15a0901d000f0f603180000c550080c0b0443c0c10b5100090b25003010b0010140c820420382c080c0003100d00e4100c00401074031015040110130b10080f02c550140c4110581d201000d020800c0c1c1c041081405034404201c0400b050b00b005105400303500034419000f107407e0048001100030711106440c0c0078900b00203110741035040496003144c01812201407400d581944882d078845041c0c1550307081640c81d82d46100700e00c0d204c22545882d481c03484000303105918043c0081c0c40d2140004001510300919a50340240790301003501c0000300c1d5400420000585146030389001c51210f010303140f0180320443c80038020100720010741030109025040c1039a501c110303030308429030b10441000001c0b07a44c0c00e6a150803284250308050019140341c4d2502d81c0045038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 77607987 1250 77606737 77606747
    0x3030117070603140601080402011103040305010e1501060c0b0601120203010305030c0d0201020a020d0c05031306050d0506040c050702190302120d080603070302030703021207090606200706020615030c030f06070906 94
    0x8184125072031320300e95038400005541401010384280e062010780702d601c02484204200800166115a002141024144000525000c0700b4120200e61084030401482202c0c0e00100441c0c074960400c1d10145240c8503207005882c00c4410b0302c0d08600641c0008004803c0c484000001d0161030410f00c12212031100f6088101d08074001c01108400582008104d000b815115004c240e080c0c40c0a8420750f8a481c17506903000c1036402d481e80c45100411804030300d83c00703040c51a200301c41d80301e00e003924240030365080800c004100d0300c10f000c402032240400080d0007294826070201c03640950b60181ca1010346020540a840d955040b0f0541500091000b000046c2c10342000300b1507500b102d81c09030091500a08540c00c1010895040399480141d208080001420540c04e01500c030050016440d0104540c028070070030700303c0fa220716050007201d502400080050383c3d4001461540410f9400c080c0300c50240e168006801d000d0000c0820744d2520660705c460241040120b0124040d00d41607c031440480c2e074940e002e8803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 77609237 1250 77607987 77608001
    0x702011e05040b0d0b03031201060f09030f14030d091103010b06070c03020405060303072108010506120a05060a0914060f120303131505090708101e09031103030117070603 75
    0x71801d2108101c030040580c0039124444901d032020815511500101c0d1542e0040004121351a180200400c101504011440e080101c2844d06402442c29501d40c00c0303414840c4480200351410400070107042c130307000b4800e5640d1000042c01c148000e02807403e11055003e81000424869446d108000281d860f05404840e150303079000d501d40c078401e0326540812000f41401041642c05001c10040d11000515202c000034440480100081c41309000d139000030300e100c2058010a0007254100324542100c1c2d076000c1c02e581c0c04070b401c5401103060795810b808210300b0319030307540141072681c1001202684020200d04c054403400c02565504890036008041019501c1c001c00c0402140d0010001f2443c058840030401340c07164000d98844043c0e11090005900b1610111090b003c150070042050002040901002c400104179030b000f4007544010071502c6e50610000e144070000f10750780b03076010303c00c01d0f0094050b99030515841e020b42c1d03103e40c0d42e1405100540302070b40403040140a040b80100e03034240a8402c1407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 77610487 1250 77609237 77609297
    0x2060a09260c06070f0b0702032505012d1104150905040b0301110418060b07110f040e071e030503040609060e040603030c03050306030c030609010f06080d0e0d0602120705070201 78
    0x28040c1c01703c075106d01c00341d03003006801901180000c00041d10b82410315407030081c0d8a1003070070700d0980000320b90034200c1c00c4a501c0010707014401c0c100c3c5060b20060350200e40c07540010070300e0640021a6104811040c41d2485076a200030410184035140400316504040440111541600c0034800041a08101803c13500a07000e43e110000c810302c001c0c08007820300c000c1d0a45250703072101b00040c5541c0f1801e00000c1600b0462040b41c001c44c050300d00e804076083c00c049100e000e031800d44090145900c0c60041d5034807000c50340078044408a4480309040c0780c0165223000c07030080d40c0041c1644e0347c80342c49180091031011b0301c2c0135100c04500c100c0008a03c900302403080c14110b13a0569218241c0f0f6400740e0b000c554a51024044e294184207000007000700d80d809000c0c25000e10b201e800000345408483c02ea4909031074895000000340d4000c0c0541d0100c082c3c102c4100ca038180011a119000400c891500c03030000c2c010500305410040313003a020806c0c1160000001c001c114000d80700e2602d41300500c0f2180421030042c01ca10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 77611737 1250 77610487 77610503
    0xc05250203070b0d060308070b01150903020a120614010801050403081b0f0a0507050607020303060f0312030109180b07020d1d1e04090f08030a051602030702060a09260c0607 76
    0x80100009003c003819142e002c001000c540f440d0380383c80c2c00d1400c0d004603d0507149030b02200010810079100c80c002052162441c1044111036180d0b8000a014850a00c6400480c2000b80400c3e010071807540c5c4460a51001c075800080c881d611405141e0003008126004c801150030301c008901030381d46070050340031480e15440303060f03141c0008100301480079004640c9582c207002003031000c07200052003031018610500880d40110307101c1c40c00d00100a0b8064401c10340c60301a8100c080c5494542e49a40c0403241901d2200b00b001c01d0601009500308a41340000340050300c050080400c0c0b2202c10760100300302c00440f920f682e880c1d41844c40070b80170300404400c200d116588048102d038281c0c4503925a8907920311040300104009000c0c070581e12418000500307800100c41d0303400004200a1055610700c20603400202400070000c4003114014040d40d84e203e9807a000c4d1281c98042100310005108000f80e0000c3e040b8903060040008441d010300108041e402c8071a06140a1249110811b040980990704001c1d005246 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 77612987 1250 77611737 77611739
    0x4051311010f050f030f3102090c1303290106020a030807180f0315060810091b080d02010b030d020307061d0609030a020601090902010801050f130c0525020307 70
    0x1500d22501050000e0180f1200780902c076200c03400784016511a002c1708401c1d43d0305140426456082080410b2038a084058080c90480c96003140c2c800c162000d58141c41410460311082500c8255002e030400000307103045148404004c110b540601802b94910003406050f0444034007428500c400e1090040400683c8950b181d080420321071902e054001e4481c3c141190303032001550003441c0020076034001c010030b591141d00800030490700d41724014900c607040004000481c180610a41c840d2150a101b8400d141c54402c00c030103211707030b006c125966128901e820140300c680d111181911061544545005540703811851820790502060041c4400c0e800d40c0a14a003652a56860000344401c1c2c40305681c03141d0b0790b00c800782d0024003000000e01840080c0001c589508034024000d00e0801c0503003100c00260306003ea03210060741c000f030105064420484030b485032000da950206005402282d0204800d44c2040d10f6141c0e85604640245800200b0b0f02005000e4240c000c4004158118410001e41561103424 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 77614237 1250 77612987 77612989
    0xb01140706090201030f020301080d0e04050c090d0302030405040f06030615050f04020d150609030219061b1b1707080f030d02160803070801260703060b0f04020706020904051311 78
    0x44031030b0505205040002e1040b9220214034200c0e0426000040107601405030b040a494101002e0702c209602104c1c1441146029a55010075001d00a621400f83c0320301c601690406009005880160030094410000c2242903860580941414842540d42c41d12b012034048900d15040480d0f403e4840c00b07041c3c8616441e400050000940c0275120b000f00c3c644d07440c2c091801600405041000418040d0740d100941410b5004210400ea80d01b022460203030390b1040100304007904030398010b00090032950f01c14201051814802e915800106054100302e249503400300d00380450340c2c18040c604013a0b0382241d105584030541d19681d000303002580c1e007250340144841000c140840e002401e840c0f80400c5405416800e960f5010050780040c0d41c020702190906005001c880c21090310000002043c3d101e0350341c5812062003203616600c071400701074106600d0f40003581003611415807520211070040d008550399150381c10309500a4000f0041f081c4200d050001050303280c84d24900351080a0b40040d160400114290 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 77615487 1250 77614237 77614241
    0x10050307050909010909021f090b0d020712020105160f020a020d02030712110315060603040b1f06030f060902040b040b0a021504230304152001110406030b01140706 72
    0xc19000400c6000c00030301d001510765103401030092854050100724aa551f104115407040405035501460b0480101200b01c07560102440e03049030f2070403a5040c1d90300c044071403043c06445040405406103014103014a01c0c00e81c15404907210781300f032000d010b00903030403100110f600c031401d0341008006900411040300949000402c10807030520007012161610b40c1c030084422015060807065603000040d000f0203034030b03080501c164945006801c0703c0101038a404c4000907914080a08003400075244000094050034444003510f001c0314004030030700809592018028040d0041305501c0307807020305240c0c0010700b01c4498020380b8151100752024a0501703040c10082c1d41c0c00c6d000645030104520485014034801c5aa190846000e28029080030004525101c00401140200c2012030f190354003c0008110601a4282e0308803029140d162441d58901601d540000b8110b8001c0314007502d510b061082e003204200d1500420486115840510822480310011f4079000125240401c40c0503041001000040701c51b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 77616737 1250 77615487 77615491
    0x602071707050a0b0a03061d040b0403230403021302040b07030c0c030f03030518070312050702010e1206040308071e050d150905062d1c060510060809010902100503 72
    0x1000854014903682c0c0001104030314260b00954911000142c5130001039414011000602050009494018002800c107008940c0082028102004510210341050b108048402c0c45070a040c8041c0d1070b000b405003a042e0241d1192001700d2080c1403620061300d00da40c10b4001e0ba01113a202c11a0f043c02e0214546007601d0136800144100d6a0030051807010000582ca003003c000d409000b03035400900351a00354000e40303a054001c800401039a215000810000d500041c001d1044c21962070030688074000c074030040c0c0700c0704062408140e005001507d00e0000140c0000e40920a45c004d40c2c58005644072500c01340c03a009a20b020980e20721601609a5400074040c4004044c204480040000c7c9580c40c4032002201e040d42d500b101c55503c0c2c40320140308c0c071071404090080840007983c190800c08a0030500161403003041059a82c00395000c400001c1c0c180603554032101580740c2003182804140380c10040d9607022081401810046503540b8003180354102c0520078a03e00640c003810a01c2e20f1200d50320103071603503000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 77617987 1250 77616737 77616779
    0x402060403051912080402030c130e0303090615010c111e04050702070e1e041509050604060c09060509060d0e0106080d02060a0605150d02030c0d02040e0402030610060207 75
    0x208200c0000042d1040010107168180141c54080100d01440e120100d098401102c404001c05130b82840007695020656901044040303c03900090307242ca421440103490034005286003400b012042001c64840410840d2103108003014000c1495007010043d12500d400c424080c3c4501d40b10702002d01d9a040c003180c902400d13840098511480030684002805441c41280e050303005802120b401c102c40d61030301c01865004101c5100d101a41d0000040d00030910800410103440082d80c0d0841800a50340c5d03900c10fa02d4990010155000d0749000d00344103010b08180c14000c0e00282d64103a00044051040081e11440c0a00411241c07810841400002c003502e00c00390076034465540c507400018a40c0007044101c905d21441e8001c2c001c0e5192803840c0c0811141079a2099004035981181c141e404015601143c8503040c40b62030040e100d894826661042c0d00480c0680c0b500742d0b20004010456000c0e50035214459072003101200c44c1035541c0360501c000b02c401480f0304400b59005e4035042c000309810085500f04241 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 77619237 1250 77617987 77617999
    0x220e0a061503080307030e150c130f08030a050d0204090c09030c0b09060304111504060f08010803030705160302010902090a0506030105060411090f12100209031608030a0c0f020409050d020c010206010e0601080402 93
    0x190814520b089823030560302e0518070400042e03141c0201610408100c0202003d402400513a4941065035482c0d21030034141c001000400104404401a980d050728054011500e0400c58503182803000f44c07110200340020390b02e8581900000440003841400ca624649020f400b041c01c54807965100d8107582c44e000311543e407080e10345501c140400d031a900030b00000c1810f076a0b0440810200b07040a03002a01c1078100e4a05500204200400690807000700d800111404616281e14011800d04030f0040859000003540210342109120304035403280c100d05d0255008400801582e11a42d0070403007107a1001100300b02048040c4902c0d2070915060703102d00034050001d401d04184c00d002020303550808001112800ca416800709c1d00d0440c5e8103082107181e01251008800600c40c9040070348207660380c0211a12102001007112001d02006580c060304411503501502c1440082550301d402500c80720500308410041c401c900f02030503e50b10000311340f07049640c84100c00b011511010011142810b00a0060703800c20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 77620487 1250 77619237 77619253
    0x303061804060b04050403050a09050102070803120c0d150e0c13051e04020c0d0809030a0c0b190e060609070302070b2202030a11030606040603030509220e0a061503080307030e 77
    0xe25117026061060744243e8845666848100d0040d10240e40d0760441811940805d5050200030800000ca0385100e00484880105030b40e205e450b00303260b20903240a08610390501d101651600fa501010800742c5002c803603542001d545510400d492030255003410301008914850030402420f010041400c0001e0340f078400c034032409182c000300301030381d000d4240341d8501e6200d015500c12096110b0700361604024214095403815032065070081c02103480043c0605802818004a15222100200f40d40c0c5051106418001e1900316107480f0b03120101114110b000e60b94604c0000c8a880c4648221100d983d445402400301d070311400d6580500d0488002043c100c0c00040e403103640541d5040045c0d07000d40d48a6a80b00b40028003c0c001d0600b015030140c1454005d80c100708007400041c2c0c024041d03941188054130341048082400c081c0030421350580030303d4290140b515040a0203082d0100f40d4903200350140400b88488241c0d240400c95800091101070b0020b0024008a85414440e030002c03032880b5801401c9030030030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 77621737 1250 77620487 77620489
    0xd021008100b430f020f0105030910020a09030c0306091a09210702061308070e0601170702070e100503160b03010501081f060908010b04050105011d030a051510080303061804060b 78
    0x80300d2002400d40e5070980340c0c54a0021450050320486101b03400707180c12030450601c0e41541e40d6580c91200308002c865008644640c6403031180701c60710300841e004945041429a80e050000041c03260031001d650b140c2c0d00c0c51080b980c2d5801500024000c2070901c0040c0084050360030001c1d080e0803118032605105c0e1080003154096510b4070090222015034001c0c0c541003910b0041c1607483d10030164480d43e0010381440400400f81c1e0815291a090445a188490259a2401c0c100c2c148035254021a40304000e00c01840b0080c001d4004000940304243d0032a144d5501161400d40c10f2030304c1c0e10030380030078000800040c40039500c20004c0540008411011142d40d0340981d40000550086402c144000b58101e802048034042c2401400c500004c00d032420001541041c000030990f413116080d8140743da00700008099251001c0010321080c50304542540c01c0703001048485a880202030350401d075103095a0a01142618010086a004400092284041c00b511103aa085c0107071000300300b034a00c1a0785449403142 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 77622987 1250 77621737 77621857
    0x110f0c01090b0d020d0207060b0108090a26190f182d0f06050306090a020c06010e061203041d0907210201031e051f08030f090d021008100b 61
    0x14411000270444280c04000100b28900080c082181503004500c61008106001c400c09107082c46040f00624030340c24080300869a1042030410070180e013008801004e0a50f0041c1e44240b000b0144d6100b402c1010022020402c044080c05150340c0c00c1300700109000980c504150042c04008031442c1c8003034156407098014030300d0309558408000f00380000300b049030510b491264254800c1c56200c0460038446450000c95860005008201840740740c0d1b008116660b4039103019072a4100703418110f95640c0c2d00c1d01c940c07004c905104030450101400c181c0115080306800300e0800e064501c40301800f0702504400207a1440c100100318280c0c14980c1d01c107044004400491105200081d5140780450340d8105a51101d01005500c07000c0340c4203090310107003401a0744011045810090038421110b440b625020005120f03c9082c80700250b11044090703001d400c0c180c100c08002c2c0302d00b4502180c80701c01a658a40c51103d845411a00384c4108c0060a590703840c1c0280b44240941580000051404c0480540306444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 77624237 1250 77622987 77622997
    0x18020a11060106080a05010b030c180f06070f0c09050402010203070f0201050405090103053403020d110405040b010806130c0510030f0e010f1119080c120403110f0c01090b0d020d02 79
    0x90070080800540b0407171400356034010105070324020710b9031406a0845909014445481c082e00b5018043e00d80d130b55a400c11000c1010340c1c02040c2c60f980300c1035032800e240003541440c421110f170140d21000052300c24103846818881c580603000f0390f10b02034083c0d4600003800920310080317060110611001c611a26031710009070207184540010580e8811071a03040c0d00c1c403045009134170030b1300007c024a2246640038580d18400c1300d034165214a0301310250701c2c00c000d502c01d01d80d0059403c1860041008240080341000e54103c486a0f410b4400549540590400c1400380080c041c3c441e60381001c04000905080303e00c400c000c106172030001034541d070b900f4001041c0c2d805041200017984d121500c40c11142003d2141d50300719038050210710b00c1e141c0700034421542100c115189030103008445001070ba00784040320407a48850300748040c7d00000e01d02442c01511407155485000304504c50220480c143c5c0b00001220b841c101c00584909204510b0066580b120b50303c190081c0c11199024895030101a12030700240c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 77625487 1250 77624237 77624249
    0x321190311070807111915020f010207030915030e03030c07020102010b0301050a0c09060507050607050c1002030c07060605040513020f011b08030106030c05120103020f0105120703090c050a18020a110601 89
    0x195130b800b85414404851961051164421601c1c440340c0c0000301c1d50420000111846031076211030604c41404142d04124031080641030355400011000704141e4840e4000b419104c152000508500082c04124100d84444004919075401000414140142c0341c004c0c3c220a0304c1440041000380741000800d00b520710903200c50180549442510b80029002450740001d84036900e081c07800c1000644075155910005012082404000200b800b601074092002d00303d0318005c414259503900785061810707240ea01c00c03141903c41381e15188002c500e40c078003401154024400c910150189c0900c40d02001042c0c03e00c0e40c0028103001140d5040c10319280d030b610061003264000c108581d100e40c5442405402c1c0c4d40c1380d83d2030030100f001c200101040d12111000090544e60191120349150041c003005984a01c0b07500100b00461000008000c800c940c03503003010000c40d12440a0903035556039001402084d01c442d00803012040e03c2201100301c224450f80c081d140294461805202c140c2c0244032140c100301e8217811070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 77626737 1250 77625487 77625503
    0x5060403080603012c0a020a0303022802030604110a0801060b03090c032a130216060f0608030406080a06090c11010e0d05070209090705060408010b032119031107 71
    0x8418150010360050384242c0035002407007040c1d858000285030000307501d494030038980c0444403042507001c01c0001018081e409418618510b4490030040d641d40141c11040642035920007002d40e440300620a01d2070807942c0030b0014035071602e6642c0c445411510002e0b07429000403803a000022048000d010b040d0080115040d07690780d0b41040483d15007840025084a0300903032041505c00c1c2802c90310502e8227140002000038400b4003034030400040c200b0740d2440c2c0d5030503014000310f095441040c07649005180c00744149003c10501d180071962000355030603446240120741041c40308000c0360f4054820194030602c1d121002903070640300e01e1003200311008400e00a00003165038400c40341501c0c1c24850039181c114420024034801414000003060341c410b290b4020b02030030001e00480c1c4a031004105040c0900b20090000d41c88989492a0500809000c41e02c244a8813443d14203030054454180c0d020803410210a1961a25003110480d00c01c0008522500c401c060369240381344190070a50020301703011442180e030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 77627987 1250 77626737 77626741
    0x91501060f2c090a0510030f0f0803010f0e1f0b070f050a0b190209100c150507020303061e090703090510180c0509070f0305061203160605010608130201031e090506 72
    0x500c464628001d01808101c1c0c908800d01240e61086d17500a0100c90b40042c94070f4004000b0300c1d0411403088420401445800c003c4004a480761501120105485000004000030707a18414a4411104c1404400d040c00c000420709000400140000f840002d00803030354024036840341e171355282c90200481c2050f90508007001c184000e098181e50071900000102a040d410480398400040032841c1a040000a0040c80b6054001300101d6110520480e40c11800070002464a41c202946079031089504602c40c001400402500a4900510b0741e28544041c140050079622a1019030041002000030340385840340852004902240f03014246150200c511500400001407134240700320005504024454044402008081c41d80310b08102400e000601e00030070241c5400300821841c654030509600c541c040020010000101c000000701c01d81d11a5008001c5a0790302c1c00115003e01050b291140801c2919211001562190304070f4000424044440000074034030303501800403105260812242600202c0c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 77629237 1250 77627987 77627989
    0x1504080a0f050a0207090510172b092606010b0405031c230d02040801021809250302090a12030206060a0b1b0a020306040c080105091501060f2c 63
    0x8a01d45681142c100141000306925020703450704010f014482440b80c0d602c00299400c580d1001c02c1000f0300c00c1c4925a1250030003100800c0e02c445404103030a0721112003940c019615901700e07007881715000403590707208621030815800b900101880762500306140303800c42c003d50a070705007449124001e041c54030400d56214038000c14181041e20b10005c100075098010661100181c0001c0505021a640140c040740500124404c00386800b8400061800900c00f04001c80d18107015030040051444020310fa0054942c0482000245a0704844103d400002c005804064501d601184200310256080140c1803152807004030303079140700503400903c028441d00c0b24241415014403105400500641d04031250750700b403a80c00c401900c00c007c4264584000c441e003040c2000740c28420340780c0466009007941c031107041900340303508148000d0049840303552810340466500c01d800955015540c1c0300804c11220f41c0c1ca00340043d20f60400e031002ea0800d01c070003494800450340351110590180b0303e440c49180c4207444240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 77630487 1250 77629237 77629247
    0x22020f040e180105040b13030c12030b010305060306061c0c0e040b071107080c01050c01060902040609030b092d0c0a06091e050d0206030705040905040c06031107020a0312021504080a 80
    0x2840102c4a41d00d49010b02c030120700700c1c008466020421042201c0907401601d81140e80d00d20f802400f611241c00d04c2c25013840c165050308081c0c0044006d903001c0c001a1282c108254490703009882c0c0c0f5070f00c194242e070810080c101034400c00d113409000d6100d050744180d445884c1509c918044400300da5181c00b0008100d00190001c07140300c5c094000c2e100600324a41441250307035642242d6a645414414003003428015908250809000707010060010b40d29550f03100c0000d4070405050000311800320100c030003d1003840000540f402c18001000c40e859590340d0128201032180c07400842c0341418001c6514640d1582ca84859074401003045030303a01c000c5103260004419036001d440f80e48001c5240303500d104002a642c5e100c09038104d150100c40c013a0f52030312403c1c02a41c032031103903070f020100702802c0c01d00300000e0282c4619620204c4003142c4091040c540c2c800d491628a00c5001c40003940b005228a062011541038a001c80303200350a8011501040300418140120300401c9500f1142c18000090911030940c1c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 77631737 1250 77630487 77630521
    0xa0209130c03030e0a0b0c010e0d021203010b0d0212090c030120040504020a17010b090312040b070605060609060d0204050f01020601080d0f02031e0703180522020f040e 74
    0x80c4003003000395600000650984806010811103058440295035440108001404015000c4d0303a00c403451080f03540030385001000d070741a5002d03100c601c0c0b40450003c5000140e00210703012307051650b800d0045078a00c0e42c0ac04030040039000e07403c3c0002c40561170300ea88102d0099100400403c2e140450800300360950308a15030b03080050000d00c5210038085a41d40a85060340d07030032a0b0240e2584a40181207a040061051082c15041c0080000851945110040951010542c280e4160454001000320944614424030115034410032101000ca13907164095074129000518403494801d4a900050980d00100c007000310103940050108054070b0300000c07d0382500000c0c00a480c5641c903001500c4d031a1940e8680e000c0501c4040312440e0040340c800d100300c8400c845030b03505040820102e4100900c485d00b1002d000c5000c590001c0d000e010600b0b0b0010950112103000303201240f0100c1180000041103101d104500c8801d400740194581a844c0c103000d840a0400c0102c100325030700c0c0c81d26003040c001c006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 77632987 1250 77631737 77631751
    0x3031602330a060b040b09031006120302010c05041202060d0e030a03020405041503030e0d17161101020604200f060c0102090109170a02010f11060106020105010807050303090609010f09170a0209 85
    0x54600100051068101030324100d4400340c03c210307202c0c00408082400c09c01001c02c5810040d1a0032030215500c60701c503920001941c0a035001300142c0c0604d00099400f4840c6000d03c030142c100041481c0010301d040720080821a0075018081103410980400c2c5103190000641400401c3d004503040c0000d04081c451201c642c00c07a401c2580340c0600c0c0d500c0141085c1007a40740c0c24002c1c101c5040c100180180f100710342001c0c51140010360b6450343c1580c0c00c4100c10703516410881e80c0c61610054002190301c0011000e0190f60045001d24501c19814482c42840e014044251340207044043c0254841d0f4944002c0d100e5000390074000350b07030f8440c034600040012180350000c1020340c0840031810205000014032402040c3c0c2802c1c02c000d80400c80d9402d4820f0745c611072240d40503102d03800010400070b5040d0000350480d400a411281c0494440c810540c50713018080c14079411130300c18410081c0c60b40c0b00b84540c0b08000700c0c1d810400301c125149c0c01c1074541c50003104502d0015900c10303d00d10f070450620080c1a07500ca85 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 77634237 1250 77632987 77632991
    0x1406030127080c0307081c05010e071710050a030804030605131106030c070b0403021b0114030a0f0207080408010207050607080609060904050c030106030308010305070506030903031602330a 83
    0x401452012020020001819082d404640b02c1c3d1000c0f000c00480d0100c54114001c00d8891042410032180c500b000000400d42c18144000050381c519500720311801045691509101d50307600940c1c1d10b0005200a20240743c01440160005982c0c4a20302c00b90302843c0180a17282d9030300c2c214205a810740d00e01034450034200d000c02c0300d0391020615581808245c0c90341200c5032a82d03038540400c0071020b0301a18801800ea00101c00901003095000910b145c4000501c034087c604144800c4010758040700c2c600030160740b8420410000307030130301840c3d80082410444100014100141070300e5241198000f80c1107140c09039400103807082030010412449034040c01502d000c0005142070001700d0000e0001801039400791961b81c011030300700141808441c1100b58094020400e40d580d034100109101001e1100b51030700e00540402107001c0c185142207d01c1608000002c61642d11584642c410203503c44200c0c1c402c44c000d085400b0113100c0c0c024030b043c0200701d00c2c89583c48007201002030b0021030f500150007425094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 77635487 1250 77634237 77634281
    0x60c1107060311040306051e010f1a03060a030506010b07141c0c020f13150e04030804170c060c031503070524040f0303020105070809030414060a03020c0114060301 72
    0x5000051028156041c0b4940451074030711070034903400207000b00e4000400d958241b60820500502ea250102d140314245242d82c181070341c0e520f044100c3c0d0903550040046c40c00d1040400d1110702d4803e401560840000b03880c0007051a07480d20b81e141000402e0300085880b8100107640001d000d400214100040c10200140c0500da488190b05408580611550303002d0007a40300e030701c6003999140c03070364900c0c0044050f00d0a03400031500d145400041a0540ea030490741c001195000c10301181c96500e1728890765040d2110040d80e125529000c07144007409610020780c1000300100e50700c03030506012007801201103e551036180e0611081d4040c2002c20301c481c2d680a82e000703400400480d542c002c502c4420716041650b1210000035000c3c40c412911403500984d074081d0f1410740c00001c03d64158072140c800c24071a91901c0481d21090380207070b220720544c810f00d410904452040081460310303c0040429205a050040c40c026811440c9800d4424072001c084040c0041000c000f0107040030701400200540e0318a0058001e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 77636737 1250 77635487 77635517
    0x1207030b09040b0a02090307030309061202031003140a0503070b071b031409150c0606010201061211060d020d15060801050d050316020a0b0309100f02030402030d030f2007060c 77
    0x5540700810140c02c0210040c042010710f04158100d4030000f4011f801e992003143c0302d04024100200c103210b500001101c0c0c5242040300b418510035240030701d100d036034100f014920755100c4601c0801c000714100901c1c041e83e24903a0002e4001c200501000d440390304254554600607001400001e01754808240d00808510840e0009910080075480304040030359281d250307017414001c0756900303040202d03501800c04005048005910005981b92003035000368001e012103621030780c0d1030885c841c07041030080604d13050b468441064a090005800442078a440c014106142a45408195a490203031800c60071000310f800c0c4011544101a64050302060f6a80c220262140c1c6d00c02d0343c1c9100f01940136019001140d0900115925540140020300404001617200e00b40f0070040f030f071030302034101d407103481549041d200700901003e41c02503a1040360000c001d0311131140021416005041d24003403403040d056460880800b21b080071407100710010302900c1c1c4203840e1b0140d444c0042c1181d00524450741401114010700c540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 77637987 1250 77636737 77636749
    0x4030c0501060f0e1621060f08030a090e070309020418020315090d0305040c05090103150b010f050a030b0f06040602010f0e0316080d0f0c030903180b040b0912060103081207030b 78
    0xc45030f00380101c00b41480f4010112001c0c14203081400440e40e01d070b50250001e1a41e13800c1f20041e0f030107042c2c044140503a50080da03075aa100c1d0540d6038001c05d84801c000c01c0090100e480140e40b003805410042900540f42e400203007183c076840202d04950050010460560904001307039080c40c00704c0c0703806294506080c504070b07984841a42d806801c01d0b0701c500c0094208907040e0110801010060310032403030395171285800c504e0f004070800d003050700ea8546013140c401c1c0c0d03102d0400c5400c48000c0307071a628030306100c4410480142064484d01e40e0040c620035520101521000002c0c8000c1249038000140811100009400c2d64000640d8118591041c04851090b03442a9507480c10150711080099584d01c01100407405070010701c2c0101c10480c68a1405d001846d01904400d40d41ba01c07a070344000082c10205014111803500780254110b03000140801d100b0869224020032500304010300500074000401503191512209800840780904003081c110030701489060f005400210070300741488030050b04004555 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 77639237 1250 77637987 77637991
    0x31a0105030a020d02070204020a03141303080403030e0c030a030207081e0c0103180c06030605010e0405090616020c09040c1703031513022a07090c020c0411040e04030c0501060f0e 79
    0xb01e10f60014a124881025504603034800ea0f020700255201d84004001400503c0c810141200c2d45110070002242880e94401905007a81d00da16100f0721600e80307407400c070020011160130782c06038480d542c80864503031360420000408030f2107507000b4041359040402e41410070300d07c0260841d107901031100c0c0d610f03d0306011901c00c201e00d074286400260740714907894201c00f1b2148020060161908450003041c234903819080b13002642d01c2038944450036800c480502048a0080f00d02070916004500415610643c05014011107499481121024603254002468109003514101c4202e038000004000100300040041c40926680340603500390300c3c0400f405602546403034a00c6104102d000c074600040c500546c10785a441c514900b03269907001c90301c41d808940020030b80200c0f04074820108006084242c034000d41d9002c10f015805401101c0c0040140006440c0c08a50201d145400340004030f03a500707058420384e00c107a00990b600071a0301c0041c101142140c00790b400036544580b01c0c0e1018811040c855055036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 77640487 1250 77639237 77639251
    0x1b06110c0a2108030c121602060411030304230415030f03050d14010b0306120102090f0f0402040e0c031015050406120f0513030e10140c011416031a010503 68
    0x341e28050030701d1010100b15020b05005103000c602100340200c24a00d040034001c05101c400c1c0004050b1126040714400ca6500005a801603202100060014400840610391490090120b81c1015107560140341003108404510410816940c41141a468a809405041148140681d0180342951203100d5142d00130706018060000000e404140741510b68000c2881c040035400f0041c103540c4030702e81c2c6a45a40150740e4184105e1401000103007030881071003100d100000041950b143c80c281001400340384d00464680d994019820703c000118259038010142c42100da02c00107030b940307103080c0d1403c101c0490f0b0340d001320084401160400440302d8009085038140c502e141400710a001d0162041000380005840a00125007440e090200080400050b089814804c0d184e8000740b413090400d101c06003c020800000140e008150580b9400007103004007100e0741124008900b5126184070f08075007560076983c178241c004209140360074203076043c0724190250a0041542d804903080600080c160301001d4425 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 77641737 1250 77640487 77640509
    0x705090405120c030c0d12050609090c010c050102070501020a08090f070b0307050c160303180e0903090d02010c0501090b0412030507020615030102042303010501050a08150709031b06110c0a 83
    0x660004040042e07817003213201e21045401c91003039504001d18614030110600001030815022400c2c3c0d180145030329216002040c0107240040c103c03030045401018810064034155405c0100f180842c80a000900c0384114036200c041840c20f0000c10f07e40350a08024100300c050704107501c00d120301510039003141e420808518000c0e80364240b007175580f1f08100e0103810600b148100c1c88400802c16811045000b0b050755800b2608114903a505000181c40c1c804840007149170b041080a0315581ca45503440e849030700d0040c90324a010007047d50300c0d9400c5400e40f0405a03000c044170000c22017001010300030081141028a024402401d000c10041c0d51b4001c042c290070349000000e880416182c1302541682d00034060120054084540c40c86240411403603143e00d280a542000004103c0d81400840c171000c030340302d5a00519900c4030705118610030b010003810880070090241000001710f6960111040e90802d0b092280c0300e1140341040150111044000c04200382c0c11003003180400e540c0b40300c2040c045407004002c0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 77642987 1250 77641737 77641747
    0x705031c3e010b040b0a03020a2105030a030f050604020702011e05210a14010302090403030203060d02121605100c031404050a030f0303050702031204020d050109080d090203070509040512 82
    0x9500c1007801c4440d02200100d180c801d0404031003815004601d00690580c0d00304641c288440c00c0c40a204614040a500040e502500b006400080303a810981041d03250440070340b4070403c1c2e44150075540800c00c2e080000b80c403180802001e000d903200d0b55400a0003110110700d0041d055001030500006180400104a10750010306040da010354101e40a80c0c507201884c00c8401c0d210600784c562640c090360700a45180c41e01580c0c4030480075501c5c0c240d060300d0300280740c01c2e01e030b648540d811070103035000070800ea4111010000200042e00c8102c05404e51036040805403450060781030072160b5826a035071000384102c041a1000f06404c0e0400d00d030a40c06030700351800c0c0c2101d405ca046502003500c1107512054001a41040010a01c00c850889040c00b40c0300f540d040c00652910902207903240100036038a24184052008140140b0b031420101407070501c40c00000c50b4210b0142c59009a981000f800c21138000c0d2592081c00444c0b5040c05110b014140407107005201d821b180d21081e070b842d241000b000c0c419041c0019 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 77644237 1250 77642987 77643047
    0x130209011101020c0d0207120b13080c03040906230604060509010c0212030901081806070f12050a0b03010c020a0b06091e0a2003160311070204020c0705031c 69
    0x41c08480c00060800035541c0c1d41d528020b1950710320403600c40d140180124076000c11845424120b21f01899040204802c1b1030311a105992980380c4881812180500100400500b820302840074000510608100150301850195031408404038007501c0b80601a01e082002e0301c590390501035900351503140c5071454883c03a00c40010780d4445048100039500403d115148020040008002c0c00c00000a990b078500d1600c419814000c00308110361050104e42010f00082ca607a44111028641904507181490281403060202000c6030b00c20b80d40d0307000c01c07500d80d0515403050030240034100a0520920040003d0081a169108100c0e070140c409886a100b520114081d06c001d048070f20701e0312120b02074910b002d00b408c800c060010802010300100d050203443d03d5118042c00c00302600c6c4103202100048185500d40b00c3c044000b0109802e0301158041d05000003030151b02c0354070140039454004802000194103110406103825000e544428920248182c40c17170000f40d01804500c9101c0c1580d42081211004103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 77645487 1250 77644237 77644247
    0x1a0f0d0308070e0301050414010b060c0a020105131706010906050105090f06031515030a1b0503061005040807030305070c09180b070e040e0d1d0a0308091306030b0109060603060513020901 82
    0x6425036140d1b09000912040c007903900e000c005c0e10307042e481c003c1112502d60002d0161a00070300301208202e400420003d07000d075020f800100091f9040c4400c4849860716034a881c001c03c60304501d085c0d0030b03a00c00320046c842003550f07200d200c01900f02420694108102c00b40041c3c030381b045c1d46491600413200400800c4c115000d41880c092103c0c8001c00c3c4443c0346010030080041034204582e0803005504110310f045c0b0f4400000f05010a0a20540d62549550380e002c040c04285c000c00d03208202040420040010180d00a00900f0041c43c480e503141551002c0c0d0782020010b03c40c540e0130a00c0e01c2454041c0441d01480441c0702d52400075801420080b00c0c3e9500c08056607540700c0c030324410f0b0700a41090340e0070040d0324012402000c01c0c8501c1d01c0714040300d072010f100003000d040d4000010341c000710102000e01c00714102e44040d00200c0700050140c81134030720001c01c2c98181c6006134011940140024010b0020b00303107034041e54000c2c000500c0e040042d90702d070400081c0030341f002011030101c0035800221201d032a4460 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 77646737 1250 77645487 77645507
    0xa0608280e03040b1e0307050901080405070509010b0a1710030f0804030c0b1c0b010f18180203071101050c090d02040f090c050f0906060a0f0203040305101a0f0d030807 74
    0x7101940d4441c1c3d5a003140400c00e6124075002103c2e6240c0001064a0030090b80c02d8074085c60030b95a51604164090380150b0700041d000d00282c2c3d070b5100300d600c00603213581d40c85441070190100d44041900c4584106c005090200c00c2c01101c00c2e0001c10740d0802855407000020306040701d801c09500c0b6003915917030429000d9840b07250406403041c2200140454028405401040c450405c005940000f46034403030006d0403105141d001b42c0c001038580e20325104c0d45100310984030321500085486c1c0f43c420350721894201c81124520396a50002d0300070040102e9190403825442d00361803482c000340051703d49058240424410724950601c079024032107005041d91a1075111042d00021032030100082c1c00e1a060016502c04c05101d51407080b0300ca012a0541e50500b040d445d4003171f010181145041410300b10040c0c0301d60400310f00c030790210b1205000010101c3c1040012160408401c03500080a10103a1a10002c400400255900481903100b580c45181c940d0240799407050703054a014001074841a90803502003100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 77647987 1250 77646737 77646761
    0x6080d0c08211005010203070f0b0a061706060a0f08060103060f1d010902031b011b060207021806010201112701022419060308070816061a0a060828 65
    0x200e82da40c6908045040703409100d1004140c00016565401260385e03104400c001014505240e40c48000204044d02060300071801100104000e621400e90724402e10f60f00840206581c40341003800602e080000e80140504aa402070758407040c00d200c036159a919040c030005100c15520b503102500e00d8601d40c846c010040d56142c01641034040c1d415424003818030000141d01c0790051044680400081618075404000103840340d050b0b84540c4070641112008440040d203c5a40804c03036903005a4808140142811081c5034040840c01e10070002401c5913075010062100040030400001c00701d00b1050801444141c1c400060340780589540102d0074290303800084110490b290001c42440b0094511441c401e020b645040582c5965041941707060701c00d20320000c3c103603200c1040742d02c3c08034600c031004100201500c844101d10111580e90b02c401c495284030135010421460003010840d00d0002048002000c43e85002040f508103001800c2400c200d48907181c58400303204040524031030190300a4a41c0e608 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 77649237 1250 77647987 77648017
    0x10207020909100c0e100302070f02040513050115031106070c1502030403030305060609010c0b0a1118040b041401050118030f11010f03060b030106031e05070914030106080d0c08 78
    0x61501800d80d44000f01441d940c041400c1c007007050107a500c10b421250039240c0040a41440d0b2110304030a034000c0d44114020b41d0107242032403445c0096110750003814043c042d014211040600142001403c548581c02204224160b031030b000c00c04030710b0401d5201540e40302186c15956981252805440c800e4243d44008010a541002d021070389030080043c00450307020341c030280140c0d074504c020080c0e1071003a15807042c0070404406450300070607440c0007415427203451144000703100e048000c032540c1d0035084500f683c1da030b01140c980c0742d0708242000c1c09100410b15080d03405012401d050b8030a00c80008050140d90f040200102d0040ea0a000e0205070200568100304540301044050611804103076586500d05d011a07180085000101d2084c420740c000c455144030403a04503403c4c404228081c0100d104455400040ea40c94907035100c800e1b105d041d010300036176200c150005140011480c49900b980c0c840b14800c2e454090100030106021a01280c510369901c0d02c1402e85d00a854660014021aa0b103c91082 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 77650487 1250 77649237 77649241
    0x240b030a060f0c02060108210f0309072c15130f0501050103060b0301030807120c141c090b09040507020a150504150e10090c08010e1b0f0307060509030102070209 71
    0x9010350042d400450640300a21070505029030076680c0d103a085c86039000a0348424551040c140a1100117901c810309200c030325141c0380303000c410b154564000f1b4403407a2003034104041c00c00100081071105150250021031000400880b0302043c440d843c0002e012000c2448020b041401558410080d0141448c4200f420094104c0031581107004003800d0152501103407502e480445c405c144035081e68103c903440200603207401e0181e540d03070160f032010441c2c000030b005065000e84001180d002c0d000c0080e24010004143d035a11440850741c03d8180501d400c3c05008031a01c0901c08040000112544644159800315207070311034610481c174102801c0c2c40900000c40160707440030242e00c160441401103010b202c09946030750078001580201d40501c040c401a55101083d904d902243c140c00c14028180a0750310404203d0341d4065190a49071070140348452074001c9410b00c3d03071b2401d180c0c2560034042d60541e0101070021159000c42e41d140011f000f0001403140200d0b580300190340940480d02c00c590f01400345a154 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 77651737 1250 77650487 77650493
    0xb120109060905010f05011a07171b010c0302090102030d050603190813050405060901062102040803130b0405090708040804030503040b04090c0305040b01260303011202120a240b030a 80
    0x20100b05000300c4882d401d1000302c14107a00c150107018142c804845c030140c00e15480842036180396002040880f2540c006522881080003020040d10101c0800803200000c400c54020080c211242054500b090500c14441c840469a0010179150024642000015507440e00390010b0314040750000400400126a0300d0101002100b102410780c1031544034900402d40d40340c0d030400080d10011a0b1581d00710b104000108201072040d02d20245540c14085a40705220381c9852402c2640c0c425040b000c016031000a00d03c00d0155801403607402846242201ca0806040c02c0c001120640c0182c81d6404000403400400c042c00211000c581c0116405012030b0703a01d6564186007500368100c7c1c4201005a8034000004007018024040d445c8070300d510580da2075541c7c0c203005060b5108e0005040a0b50540d211900c1494052000c0001718040d2400c03030048000c0f08940e104120441d0704841071000a0741050040d040080d6840d0003080310f124076000c41100d41c007600100340300105004e40c28a507040c403031070030a2424 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 77652987 1250 77651737 77651741
    0x801050408090916120203040201051b060117030304050a0b1f0312080a0509070b361002070608070e1f0e0109080c060d0c11070e190c120b12010906 65
    0x9801810748810449503920041c07003405402e40e00080c408030307074882e005e641c2410080d03000b950321501c141406401c2c140015040d161461003443e41c01071035400a801805400380c078501c513a10810140c0300071403039454a5550540c4407100d0b81d0f0010001000d86010401d2502401c01410902442d4a039112031140c0c0d07402d0103415001603070828408036220401141d00034a050142500c60240344c0018194103150641039901c03513002c0c400c4031030024a031040c43c08401d15414404941c001002044401e19078080c0200840110303101a51015507201040c00c11580340c0041076582d112840c2c0c10140901001c800c04103104421240d02407251540d54142000090b41082c410320030000e00303a0305da804035525107002c0e90fa95030000701580d902c1001070000712100c0f40c1035000850000042c0c0350102001d0b408000c03140c9410380540206e240c2080000c00c0011103601088203041075a81f50000b0302121502440251000d21100403240010b41c81d81483c070100e03201d40ca26452f0890850008001510b07441c209100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 77654237 1250 77652987 77652997
    0x30210020604150c05091306091107061107051527030d05010510020a15020409050f0f0601020304030f020f0d1407030606050907050405092a0702010f1d04020705070801050408 77
    0x1da84410f1220380b54003180074400c0204d5800c01c0d4032820700e409403900030014203103829107000046035200d410220317000d40180505980041085812610740b000c61a2510a42e2001104403450001c1440140e010910001e03005440341c0c0e0300000310383e42e0344a60249400c9625a482400d4041d880901c60720040e4400200520845686000401059032100204095032140ca400000180d0141c0c1d0031802003003d40c1c01090f0404180500149810350310301d000804d40340119080e000f20200c0c04208043c1101113684a035120009201031031419086503134174a028500d941020340280c02c21080881c45440f24030a0700d0310190031002203003824030702d481d14030307914011030000f224010f04020001880f803d1003048940900e54644509082a080105120f00035074004e01d0380002060800f169070100451070030000c0000300c0b0720112603a90312180005402034079004066010440740c5d2002d803101d038044503108004d03840c00702d4001d603850915040042c0303041e101e03400142d0654030300418403080205142c0207007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 77655487 1250 77654237 77654243
    0x504091d01150b040b2802010b18010f030b1905040b1012080f2d1201170601090c03020904051e07181509030506040b060406080f1f06030210020604 65
    0x1101651207041e96055200b15846444114801070000340160501c0b88040c24251a03c00522020101180090550820b6020424000d41d5461200084509081c104400e01036601005548954509010490242c0fa14480504161049000300e541c4601c500e180c8100044054024440d600307180c24007100d0010156205420882d5840c4002140700c0c0041d5142d080582040340f660030461404400701c0a9803020081a083c10400e154480720600e8071400b07502d0030707003c0d80d900d2502c602038a56500e03003d49068001d02c8601c0b603064420021080000385403815218182c501103007920a0300c40c02d80c0640151144150f00500f04010000320042840c02200381002c011005900d40d1030385001074484805503040141030340102002400546100c10650310364a200d0300e400b0403000c0e500d40340c060401409480c00c40d40c0500b50020301032145058000d06002e0602d2a002c1c000c100b900c1c01060b41d6401c007403035501d40d5000c070410000384600401e5012400440d00a80042105444a04001d440310000c540403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 77656737 1250 77655487 77655491
    0x1403040b01060801050114031803041e0e01090204082a030312041203050f010e04152c030c0307060e011107030203190f0c0609060f020a02010f05010e10050607030504091d01 76
    0x64950b22401c149640c40d1f00703c548440c60b54590301c40043c07a551044200114600c81004002801d8160408883d00c580344485001030880c100f001c1310b00340f0001030340030070030803801800140109071000c54504c0380314202e0b4200080d88580005202c250310803100f1020b9150202041c000e13107a000e07004025200b1845a10500c0082c00d00400c29000c40308140c402c1c80107041c4000060110070310340c102194110b401010705a400030300014641050b038440940d104c0081c400c200c0305507504c5640e142c00c00215560034010b142003a1100e02c50300d543e8082d401d00a44200d03141c001c4516108400e500c4000600350000401d40c0d55411824040d513070744d100111000d40e40c500700c1c61044d02284207003618990001c89a60343e00407038005454450140c1440c80040d904141c2c5c071032503009443c800340700803c150741c0c06c1d40022441400d040000750840300140d0000c203070000b070340d420040e040040821400948030b003126107030345410460504803102d000e50340040c0071042c6003c12203600c070b00380343e41124005401e030320003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 77657987 1250 77656737 77656739
    0xa09020a1701090513230a030e0f0915060d090501050f1b03010303020712080c0601030b09070b0c03030c0f0c1b10020c0f040b01020c03030d0606031b050d0902011403040b01060801 79
    0x40841100d00445d0700c04201c5d5800d01c00345000503040c0041c1d01440c08a410b600015a1000b43c105041c420740042c00c6000ca6141581c0c10760a0800c42c64401c0c040300111500b0920345803081d20100450041c00002d4424500015a0324070a92a82d206c02c100360341040003009589002540340303c64003c151250b8072020031b40d15142c00070480c800b049a05072035040c0e01400c000c518110540300c0a000c6000100d40c51101480042d55207201000214000c6020b101c07000c8203410401303105030600b101500712012042c020000b0710085400041241d4103c1d100c06e140320b50314a00b0518100310340c0101b980e4040c4900542c00200440400c0c0d01d04084034010480e000d10020701140401e0741d886810340d890981001c10b074480c0d24040d10303180d44544203448040c0103031099103130007000090856114080041090382d582c1414840345070700d0f00c1131109013410b64139032600c1032040032005051401603916280240c0d495180c45421a48200d020702c54015820700341a0b100d003003915161090440c24041c1000007018240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 77659237 1250 77657987 77657999
    0x904050105060a0c080306010917010b0108071706120f06070e0102010f05131103190f0b10080307080f0f0412020108070201050c120a0e03031905010509010506030f060a09020a1701 79
    0x411984440f5094072522801d0b441503031100070b26040108000e040c0041c14000080018002d17809520300400b40700001852240040058807200000d0540c5080140716280143c42c0c4260f40c8049801000032500304120362420780c001c0d46402c0d200e1510034003074040c000c240240b0350381080c10320400030401d030001d00c02c03100c00c0381d001c00880c1c40440d000303030354100004010740105080c008940700354400903082c0c1c0d06480d40c01004162030190044121081540640c00006005140c01c110f40c0111000c013420141d00e1410301510b5903800740c1507010f04034000000340345040ea05042c0480c0c5460726200c00403a00da41d6184039080314540751800990200710b26600080e840b91045c802d05124084180626040800400e046074190b5801810303020b415a5542d10900101c4041024602c40e03c140000c2205205454801c2412707120b040e84030038020b100722001400b15a40b00c206880d4401c0c4068030f5a4160b64445c0d00003003045645a000f40c0900f840050407080c926481414a40d07007080c068141507060341e13685 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 77660487 1250 77659237 77659249
    0xb132a110c091018060506130501110102030c0f030903040302041503050114010506041a09090a090515070c02010804110904030329061603121b03050601050a0f2709020904050105 78
    0x15242c0b0742c65443c4500510084118180b180741060245000154071600c4802149850340034507a80310f030300308240204209035a8440703021040301c54100025400d50034081140c05140c0181c0800032006640400040c03006502081611700130340c0c0082040c42039803240d075038600148025000640c0c81d0b509020955603025a5207040c0c90481e2800b40009103004d280080309004440750724420320b50b81104100c100300e165034160b11180142c1001c00c001582a40a14146140a881c010742d02c20010070101002102c5070000840c404a03a02800c0001483d512480e1001841c4203000c0001e502c8401401800141541944481d01c0328410242d404404500c0b83c02c66403c2c0d918488030594030500402ca4003a5103101100c1d8052618400c0c10b0240e10700916003040400c3d0fa840400c0c100b50400283d040b040b0342541401100c0c0c0001003030a003c3e151903038002d0003c000a82d8050340c107041c45240c50500c00c00a0380340c100e0381c1c0e01c03003106607e400825480e41020006980801a998861420540040303014a411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 77661737 1250 77660487 77660491
    0x42a05040c0c0f1101020a0c09240b0307050702040b040c0c05060112080405060d06050d03020d02010c030506060d1a0d0b0103020405100803120702030d0608031201090b132a110c09 79
    0x70070040c0341016542d180c1130200200481c850460090080203000030b00e1580b81c90020300010701d000b103003800100c4070220806c80440312050310b00c200743c042000040141c404a03904140c080c07811a0780d841c02800071801409180c003125810514000301e01c141598801c1e04008054880c4064a078140d0b0380307203001110400d000341d002e0100781d01000104034030702d055401804807491022002c5646a41d8800091907108450701c19005070300032090b40c0003c103074280b09181240c1800e007420441c41c04c080001c956180902e00d00c420180380d031424086406c0c10101e01225481000030400440754815140c0700084640030310003240250b04048c082038095002c49103aa0075544400c000758140055800943c413400c0c0040e2071602540810010801c1e00c503020300414000d00340c0300000319a2052200c0d800884910140d0008001e1403401346070500340e43c1d612100c2c419546a059000c83c0c1c05010100207181c000724002d44144611aa02c0308007807054010b100084013113200000d0b1250a003215003403041e00707441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 77662987 1250 77661737 77661743
    0x501020c0909010e060403051b060106050304030f11071202040608150402010807110a0b010e0601020c03030f0c07090204082803020c011b0b0108070807051e09042a05040c0c 76
    0x90402041581014030066034006030b248004aa1084103560080c20b0007030640c1c1c1a4000380e8001401480014410120410300d0301c2d00d40200711643c9040710042c0240800b500043c00c01c0380003100082d540e4400c1c40020081d035140c00a0b111103590b100040c00d299201254104c2c010780c100f00c400986d1078004107010f143e00900303504100c41540c42e039004540b000401040d03401400b44200c03440c07003001804c0000715a1103110354080c010f15410180340e0514404005d0142d411507214130000c44007500c020042d0b58080c0c0d48019060b4035008031b043c5560030124250060303000301d480814005186100092840e0404035403450203580304e420000411606901c103600078015030b008070444c000e95403141102a42100c408054076007940740700d170786a100c030078001e038403941d4994000e2100303000c440000e0181c1402400201c3e8282c0000924039011041c454240c014544600703580c0c0d001509010541d03000480c071611003a0707504a0001c2803034a11000000c280243c41c001ca10300414030b0384160140304002d809a030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 77664237 1250 77662987 77662993
    0x11205040b070c080f0313030306050405070e041508061003020a0b12041b050d1202071d0f06120a0506040312020c100b010e0310051503060c0d1a0a0308130e01050102 73
    0xb540c01029500c10b400440308482061040051014150030305000e14041c005242c2101a40c54041c10010180c42c030320781046114514010034000030b00c0d0130000380540244151004140008500040d0b540700d0401c0c0c1c401c19040c059034081001442c8840c000d0400d031780c400c03540c136820b00e503c50030754003824003566013420070201c031540214010072561841041c4542082e161843c0b02c1d5240c502142d00345594040444541c41180201c0c1009038040c00070401070081000d0112503a080400d60006620b07008c4c016900414802c00400d00540355001d81170007031601f0030200c0f00e1028031841c00503a2620119400e400180c8048031425040c6894021141e900004030014068201482d070700c20010715600804038103200c4001e0030081e003078405020001c0c158802c0c08000070a440c5c08000004441211b96245200390020410011000711207000d86407864040000060014100e80c4000c0342040d0007401c0b00d40c000080304001081050220007445081d110b40308981e022580e8012005240320300b80982405a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 77665487 1250 77664237 77664241
    0x609070c020f0d030503090c012c030109051f240302100201061701020c061f031e0512040602011a03070506070804120803070f050a0e0603060301090b1005011205040b 73
    0x191086458024050004148200c0d0b40c0e00b110000b046001c0280045000c104e01001700440030505011f584d607102020f00780403030180040c062000401c1e904141d545440403030100b0391141b54409500046001d9071200c1140c60342c103800c0038969031422950780c02c06801c40c01c00c07450304090266035119041e103100b105003428600d81158200202030380300740d01000c11903588d004c0010700c11030240b0b03c0401d000c102e07a000503035070703454032024600b4600002c0014580d510540c1425418004107010501280d412068500f04859000c2184420303188852003e07000c0c1c0318a074132114540665030000c2c411610365800810203025680700c07201c00d46015102456151b00921010400c80c100207000b840214407500a40f031600b6198a00044034060110040d105400044100000c0c00c1c0c01400703101a11055081884c1000f0005200520060a04c08018000c103c0800401e00036103013500490343c1ca961040807075400c0d1808500045d0780316002d104042c00030b40c07602003c1545840340d118140c021904224082c80e26 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 77666737 1250 77665487 77665501
    0x80706030e010f0c050a03060807050904060c0c0f050607030e0610150302040f0b0307030b0a031e0f0f060504020907050a02060606030408070803040503090f0a05010507020919090308010e0703050609 87
    0x901040c00241240c2d500c9188454101d01c00344226010949603880340e40e00c50b10855030003002c42e90650051040344e440044140b00d5640c0d070300c0b910f0354855480040030032500918201201e036032001d05070052182005000300c0b000c10501140e1144544a2076400b00054400c0c4054941d0307490b025030312a80c5400e0000400e011040d90380f10078010040660034054030b019500c0c4c000e140d00c4402c691001003c100088248039140703501d0302600c100440c0440b8202c00395411621381c99032403c04c0c106018507601d110080082000318900c176105146401200c2e81c00b203400542085070103460b04031808c903c1801c1750741c00900c4250003074090f1240d402c4d40350700170311042d03071b030901807160307950007d4000d43d0090400d102040008000380c1c0254440d522410103941c4488541040c8101c075000e8034a800d1090b15803000500560f40d000341030301c0105804584c0c9140c0c40e01d40f2100d8000700d4154121002045091440070800e00d5008080d4034102c480f40381402d0000d54401030114207c070030559250ba80401c80750013003104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 77667987 1250 77666737 77666741
    0x13080306010e0103060803040801050a0c1815090e090319050c070303030b030a0206130603050106020c1302160b01060507020108060603130b0a06181a031c0c06020c01240f08070603 79
    0xb810041c18000f800586402406243d07821039031000c0d616039111000c1143c01d4150380603564408416040200c1007401a100d56500305101e4010040141c01001c040d41040b0701c41c2d510b0b080186058501c1d140c0c00d0511808803503d81c0e101c40242400d90b101d6440051801d44982c080303072058003900c005080d90394119503007103010740001030049a162040031850740250b6242c000030400b1105e000441c1050324a850405003e80c3c105a00c410295000304101c00f06a8070703900d640203404800b0400041c0e80390100308800b07130101d40c0090064030b004141000419001d0b00000107202e098001d0b02c0c0c030840b50361801c0c108501e500c000c072420300502d41010541c00004031051000c07600106001d0010810a40b20781c04026801402820151819154002c501c00114030446007030401c0804e0f40500002d80580a19494034002085150100041d2100c0c00301031005035410394190429850080c07201c800182620450324140009807016100c1102d4005850669012035000700c482020281c050780e40707000300c1a40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 77669237 1250 77667987 77668007
    0xf070b09210c01060306052e0503060f060d060e0714190603020319020c070f080a0b0c0a03060b070501050601090e040308061005040510080405070801060f090e0705030d0504030b1308030601 83
    0x1070b959203505001c030004910f40540303845401504050754100c9603402c8036a003151450b0400a804100040c03003404a510045012648030003007652454980c2c940078082000380c3c101c444080c040502d0041c10f1101640e001c158141160011240410b010000b5010441003240749a4003d01600c140702c010462140030b81c01841c1d010201c0c10300b09081807428042d12040e07034029405441030b9000348501f07201307030010b000405c006000c04030000c11140039260b903400c907894005800103c140402103001da03d05440f0340c1006000c0e280c00380b162515500c981c50214080c1c0703030996615000c5268040041480c2020300c0c0d41d079100b181c05660740c61450f00c50f241400012062800d0540401c40f0401010401c0d44440007400c0a5a40c29591030340185050301307055003014001d401070f2103140d04101d420060034885800c020152765420a0020788403240c41d108610700811644825054040d4503080074855404c0009801100c1c0101e02c2a000e659401c0400c003021000314000034184482440442c07069485034081c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 77670487 1250 77669237 77669257
    0xc1103010c020c0d0c120606030501050a051504051005040e030d1d06070318080a0503090622240c0504081501030309030b0619121e08090909010209060f070b0921 71
    0x4500b25885100b40c2405400c206da05550072500d409003001003007002d2040590002400104100c1410251003150600004101262141c0d84070408175941800b0f0956600c020304005000b0400340000b55905030700d03600007410411075949080d4804a03070264031b0038006580d10000c005801203980384802500241031700c080310f01d02c5419076904c500008080304002c040454143e101c981c0c5a280c0b0140c41c40c0351220090400100440d403156591210b080b000000c0348599010054042903030458982c0f640036902803103203c07c80c3c2d082c20307101503807160080c00410a0310031a00a442c010048500c102c681e0701000c5c0720003000200d05001c2000400c032060030050300904010103201269003007848481c19010319030045d004000044100000700015200001d8810085240c1c0f000c02c05085e84401003c0c1c024a1081030143d11000001613a09000b90304851038000e000300819254171400c0d000210a400840781280c600810300f020408003600000d21242d514170340c40022a000403142120019a00800100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 77671737 1250 77670487 77670503
    0x2010503160e030d05030103020913080a2a0605040b070c0308010506090d05010c03020a0e0f0f0d031e02030403030807022d01060e1306060e09030a030b1f0c1103010c020c0d 76
    0x111100f50380600c24010006060391760f5680365410750041000380507020745110300c60008001d2107000100744500350390144010b400d108810108155140901950441c490a040c24403481760208000303150740600e004502413040cbc0300642c1c1c0d40e82c0041da1403040000c0d014021541c41c0300100060f1500320024020070a0151140c601a22255035050030342709810101c001003500441c03100e80e02680600200700381001100c203620038000c41c40104810100354001c46004920841800c0207140c042c03468101c2d5240c0b240b8260880d8810942c00a449801500003100000c041d5008181c3d01407002410400041a00c2103262141c1c59400091102c0802d8001d0303034045540321040060101c80c1e1240d281c0c42410b104950300001c2c612454003d003111a2500103d0035511040107115115400000361240783d170312801e00007003203200710300054007020086601c41c0908000071000080d6a52200843d086c0c54880c10450342d00d00c2e2140700b018244c03034501c0c510000681c002d4860012a103801d11804034218001ca0f4a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 77672987 1250 77671737 77671757
    0x607030e03160b060f090703050f070c03051909080a0f05100506090f0402031c02060901061d01170106090f020a02062508040c090e030a090902030403081512100917070201050316 78
    0x70442c0101b007205c0481c046a1b0714000c00c1450754100000d00d600440e035261054107070303002c0d55000e8618001e45001a0380b0210700c80c40b40d00b03981e001d4242c5801030120b04007143e2901513149804000c41042c500111040d00508110030344800d028040c5c18040e181c01803a4030207658034040e44450b581c1e0700030310990307241c420101608d4100051088482950400da80038120783c0c44d001c000d0078251299035022031880391403648081c9040804c0b00c015419160380d500c41110240c2c8009500d40503200ca82c0003800340300d191450f410135540141d80100502c03411350b020ba503040d550b0804450300c1c040d0401c9000c15001c6440b07200c15002c074481c62085900610910080020a4464001008564020340380d440c856000081c64482140c000502100410034000150701d0f40c6050f41c2c0042550354007503c0034004043c5094500e402c1e6440715030003c502040541102c03403201e8401c160381c001c5c0c15500819196061445100b49072003503414200c0e10016010b03194149161205000e81402c20600303031544041200c0162 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 77674237 1250 77672987 77672989
    0x109080301060f02071205150714030a02070224040506070c0f080a141609020a020f0129060f070308040f0c080d08010605130614090904050607030e03160b060f 70
    0x1035400303000165a9a4a20782c0000d80203803038100c4030f40050b641205e0340e041c6840094000103c0c041c1031800039400001075220414240c0fa010b0454111560311003000c41003040000c4554081c00c2203c4c02242c150a04072156910403602201060300017408410030001032140e800c02d40000e2043c1c0748034004c0d4401c480d5583e002100e1224883c0c0005005400c450720302d4060180611408429070ba40742c001c1c150800c0301d41040c00303811080c2d2040008181e00416211516402030248007104416000280300f02030b0826107042610b0701d4181c07841c0c40b052403545100c15a0130f000050700c407281d00c2500c0e150301d000c04d2502c060315000c1004104540c0180135415840005120703241d90002021250010480350002000140c48918140c00040805c80c0c2804900e640124004c01c80c0200c2c2d40381c1c101111342d500e1351440c0716030fa4424000d030940c0021a20080c00708114001030300d54070507055075504021403030324400030b261644034200a0584810f98120f4520100e68007110054005800403c06544035403018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 77675487 1250 77674237 77674253
    0x415080304030f060b01110607080c040e070f02010e011109040905010b1203090906100c0201030f02040b13090509151501020316061505010905060418020c07080d0f030204050a170109 80
    0x10304100c032980c001c050240f0030468240503001d481c0d030090030700d144032421040503180c1d5114002c02c00420800d42101107103620902c041114007418184000c186a480c1c002005845442400c0d1840c0041d0b1034024100e082003818070541038031002e1000401d103000c11740c00400028210752002a2199540c5400c4202a55500c494105423034880c04051903e81305034030108175200350010403a034003030340042400c000d865602c00d0b9415050769090800007000c0e840c8401800003400342d504103008070000068000041031514025a0803030703400c040d0601950f070b6005560b50311034800315a202d0007001a05e011401204851656680340c040600c1180e0810240741c80158409145817416a4610f69550f1180307650115050004080c0c0303000c0c2010b0003440c2c40c0802143e454070551244941074134080003200100610764045403044001903040340e100e1611805120703114001142030401065540a226010602900a03071701181c03c01094175907840c0c0340020003140004640c0b014001950f990b00c00300005940d00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 77676737 1250 77675487 77675489
    0xf1205061906020d03140601080a09052a0307090e0c10050d14011403010b03060a020a0905060a0503010819020a050f011709071d04050c0121091203060918020415080304 74
    0x158000d144a580c00134001c0d088030205804c880048000801700655640c00051503074000e0658030b8000758200f010b0070014180000c944424072a02c5101020700b6480c0401e807400d41c40e0200450130780d8841a507500e550811980952040b9420b9003040324280054508081130310040c15603410003919104a41c0c0c20321048882e0079114044030903a440051202c0c04c0841025540b80c801035008200482c24800000d9540ca0020114644260001855850103104070031820080c00041c00c440d40354a0714003c09003098009000d001c1d114071a8902c8076451f41111002c2e80d1604d03401509030015030703040c10180000c0c14540070440381442101e0a500c048401190201849002044044c011440c1400000003501e8035105034006084400d01c1404049074000c201443c02041c01d0800d18201243c0450030301080070441c40342031800345440c00301020300110302d400c2d072188201c9590800840e40c481400c43c085070b080f450544c1041c2400d4201d480141403d07401080f462a03480904420299510040c524607409 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 77677987 1250 77676737 77676749
    0xd05210a0e01030213031103010b090901050f07081023030303160f02070f0905060103060b030a091a1314120a05040306150b070602070f1406040507060f12050619 71
    0x140422003503510418011a1040c2480d044d07140060302804800d003040740c0e010181684000380780c40c044581c0c003580301440803100648420b41c14034010f0205402001c0c02c07660b900e9800d00000000c0c1e20180f1581c1040d05c00c04943d40e00031207c4d0704040c0152051901c401c018010030541d84014800c959040018600c43c4100b0b940308101d204011078014406007817000a8405d41d40030b032205000c0c0d003002c1c00d8801c06480d281080058540c2c2c40f00c004802a060b56071015080540c004103200f0f0740c500c55048000d405000b90b00300074403a00541c17002d0580040c1200d25481c01e003806d180030700002d40704082800c03203040c0ca070f81101e0103100804107017601175000741015030115500040c00c20420589024410300c582c1c50080d10384000d0714109014195102d04200200303407581c0040c01d8420040c144000c018001e8001c4030302081c5c1030142075160394030340003681c3c1038a4501c41c85400040f0b02e4852554624444086c3c0c2c0c640103110311601428016000190915034072805030440802074440d40d204503802004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 77679237 1250 77677987 77678053
    0x40503030406060801020a050715060902040b03090c0603161112031003060e0304080d0c0314120f090105040302071e030b0901050f090c06030115030e0f0d0f1106060d05 74
    0xc0500c2c00e00c0480e28250b011500b02d07401401801000c5030024241c4101e0b541020300504039002401c0500d0051420380c01c01e0100601c08a0301240c8146190061403080c500f0008580d031181905003000702e140001c565200c840701c4802030100301b41703220344948240601c00340c00711a02e1041005c07140380190070444089403c00710220040003809580d00822406d4010400a5071816003000075040d1690303c1c481c90141849540030603501014440c0e414010907103401c02e009a00c5500807413103140c003010305882e1034007126860800700c0c28103a41031042d1805641d068000f80311107803611060001844440e8184105000100c10001c049200c022000d0301c03c0c440c5c0740002601c1d20785011110248500588946c440d41d1040c1e00941d61602c0310310031203054819075101a12000c04591048025100e500c40404860155800d161003020000482c461070a11079103c02c10a040141d400702e83d0782440c04d090105c1c6502c1000840e0b00e86c1004100d8848060090007500c14240c50b43c6202c04407601501c6600103111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 77680487 1250 77679237 77679241
    0x190905010b031c030b0d0c0501030903091503020d0509150f1515090306180d032d0902010f0c0b04080f070209100e0f0f07030b0102030d090c09051b0a18030b04050303 73
    0x1603414401da1000c5041106c1d50303030000b000c640710321540c81054000d8030706144c0c0c1c03460303820181400b80407500010490040c04910b0f080d2f51140007000303900810f4200000d01e082c6400f0070320700d035404261584c1e82041e861001c0d1955030b600e414461100000341806040c10002c4803690362a80721161080100310a99010580d01c80c1d5900915180420003000c0e04040c1c1d8418060101791503021a4400901180d4030b4046410440100400d203003019a00b5070181902e40700f00b051b06103007420b80000010358002d032214000d054000388180c030300c404103074001881a4102c0300003e000404442c003400c0c0e05900c0280d00b030300741001ca901080300d140c0142d401141040585c802040900d84c0000255400300110030000c4190901c1ca850701c40c2c0300030117041082456103681c0000c0259100700140c03100026000e00178021720249003001c0820441c9030040d0300340706007820300040300c204001241c4042002104d100034946660618110703010a0311500c110003980c0821800000710b42103000440c000d600441c01b855481c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 77681737 1250 77680487 77680543
    0xc03030e0a031d01030209030a06051f030609120206070f05030c1201030c030b010b070c0909050c03070b04050307150c030507030e030318030114070801050d050f0601060810080303190905010b03 85
    0x140c58a0f441050401d401009014010345010500711071080d400000072580362503068480e00c9507030b0f403507011449244154100000348180f40d00048526405a2401e040048101c80101c1c0c0b903c50445100c00441c0d85100c41e641c2c03d520480040d90b100301482034039410084280c0d001ca0b20b0310f100307030320684401103124424424061582945401800310141035882c29402d5981c054401c0c20912810040a0f5501c2c429028010300380700e03d1603a520003d040c3c50030b464035522400180d40085c0101030283c031560b0f0010405900d103451050800020f900e0310001000240e40480f0907900584080342040f9116002e0750142d14100302500e0400403804410480300c580304180741c2100e1150b400d0140890104040c058080d805c00038550640711b060302c084000203804d00b4541c0c509100c4642c0350b94144545400060115440818a40645504112a503003940c1c0d03084219a030b8081130b10098284400c0c103940194141441c0e00c4032481c14030900022404140794800242020749d020303103245a9100134040440c2c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 77682987 1250 77681737 77681777
    0x303031e05011a03180607031a0108060607060506190603050402040c03050f0c030a020708120103020907020307050606010309030c051006090b120606040f1506020304080d050301150c03030e0a03 85
    0x855a84842005a0b40c5012100a2000304a80500d0040d840c000041400802071200302a20380000070125002411b0000c402002080b10382140c0703982c07030601100c540f03066108040c154081d00000f0000c5092450a44446000b001d0291106500074494a91501c4860b880c80032403000702a0342e240010149070500610040d00e0084850742d0825142c0400c01c448082c40321011a04070203c158000d031660368601b0810000e1080308000b0b80180c03c081801c3c14800c4030124090b069034403d0724021819213401000740c0c0d5074040c540005000b030b0070900000c1c040e540b007944464a01406440c110456a2081c1c8500f0300b42510b0090071000310383c40d0303a020b02180180d801010a200000d60b01815104c5510001d10385400c0041d00861040741c4a0242c000c210019402c207000c0e2011040890314081e6840e64041d640c2d41c01440740e03038214040e0748207410702140940d040e64100c07040f280403921480941c00c821140348010410807401c0c541d42d291010b005000402c11042400d01c00d4460f02c020b413441c68940380d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 77684237 1250 77682987 77683031
    0x307020c0405040201050a0e0102030d020c0a060605030f101e09051c0e0607060b19060504080f03070c03020f030a05010204080102091905010f1409040515040b0405041220010501030303 81
    0x20241c1d081ca0280320050368000101c0300316244504d040300d000407480004034190300c248889862024004101c40d02d61100225269034040d110352000c0140541d12010705484080c5560412010b42103502001d120824030b03084103c98001680303032001040e0b445010002115808103054810740d00c001303001844440c225030b5001e03101c90582007005000902e600004d0441c4580800200740c29144d281c0040507843e071507460188001c404a20140c5140c44e5107006200e90014841c00c04c0b07503c920b2086010790300340442161401604890800c1e502c17130440d000e00051070075424240d40c03d441119412008241e082c0b028001400c1854000f40c3d40701d00c1e6004200544542c2e000c00c0b0f40c80500324608100c03c4ea081614849007000c80c1c00c1405000282c08824640d9001c1c2e440c80640241c2000304000d115582c0000e03103103004100b00c500700980110b0405000032207400300d50003000c82c2100c084621105000c0d8910290340800f03484e40c9150360070f03400949030075907400383e0045020076180c0c0e184c81e00000801802c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 77685487 1250 77684237 77684239
    0x8100e0f0c0a140402040503030c150f06060708030603030909071d012a0201111b130b03060402040e01060306090b060307080303100302060702010e0d0308010833091609020307020c 79
    0x20810401d684001407400701140300c0c18280c000602c9080c0c2007900c860301030b1801030a004041c1d13601e40088507062601c4244a000e29944814550300240540b00e01c1d044d2280501e4000c3c0000c2e041161960751186140c0c406001a94140710a10000c4e009646404002d03220b010280d85400f4041d01202c00e074803084200c5410181400b08100101e8440318010840c0d01c2070f5180040c1c04142d501e10703800181c0b8903202030760342042140507950002d440010345403001aa004400e503000400781c0d50f00f180804c1150144104541d0682201c00801c000d840d00d500002014144038000003010743c0d907999460308407401e21504448150f4501c0c01c000440c5418003a40e8000c299000c0510300c2c5241035076110700c05d4101400028810038012490302c1c15a4811941d8210380c800c0540402c10008060602804d101c0007403042603501e00c00c0f50601e01d4000c3c94034078500c05000c1d10180e041c900c82d0710345d040040700c0c00d002020948144601d900c00c640c00400a400b60005041840006075a030809410080c2401c00b044003807 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 77686737 1250 77685487 77685493
    0x10902092d0a080c01120b01050a080406060b16020306060303030f160311030c0325140c0c06040b0a03050105030114060607110613140904020619020708100e0f 70
    0x31186526264140034440810410214a0012250428244a2451003180e42100c4003440105042d54005941d4014103026201c000001d207095031800e040e0340c4900007250004006002c02003001c0e0080f0000e64025108070300c01301c0d41c10f0b01c07021034150980100503070440c1629590b002c001542070500040c0c1d0008000e4018500d145000042d040303800034003030280102619603441081c8180d101c0c1e40b06800407100d00000c3c641c1c9080003c2c959480b60000c3e1404021603698500000707488401c254216252840e076240d80c4d401156200c0c0d08132064110510f1001b81d4001d030401070314503965580040c030242c43e1007210780c1e881d07000c0d5a030300400b02d4074140c002900030380c50500e2211a1035404481540c0c001c60861300c0c1c1d1341d1f8007224a048240201c2c144605500200c01081405264a10003001801c1d912003440d10403070006404100480910152000b030740110301004040c110244502c03900b02400d10301e004030b0310302c569110101c5280a04d201701c204540c55076085000041d150902011078215210030003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 77687987 1250 77686737 77686747
    0x909180b010f03120c060e06070306031401050403120c0507050102040608040c150c11030c04060806011a090901120c211202011a0105091203070602070c0e01060e040b040605120a0b010902 82
    0x500a0241c513050088010301486a89080400505030044107010700217009880d504d050013800500503044901007101c412404044003100460305108891007070781c0680d1012140e4082500304001080b40e80c0c8039001300041001240003280003400241b008003a240c3e40c41c410341c50541825810180241c1115101c030456480018003958407803030910649420244401502c0c0c0e07140002441c106072450300f180c003d400c1142c006049180401e10a04031603012145c0102c41a00c0802580e9074840c0d00722040d404000403005024102310b0280c91410032b031250380e500d59a940c44000d8035800d15419041e0381803012064a20b401003042c45c1c0d4000c4030400031400213201c2025585a005070044550102030304001020842d22144e550354200c80c40780601c44001c5e00e0340c0d280c01d810500007035481000f0a9030040c64071100062503a0000c01007504a07030299a0700f00030501d1030300421001d4036480200f240d001da2a5207011440e541c034940e0303481c103010b03010703005040244030b51406108041d0140d10400e800c51050107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 77689237 1250 77687987 77687993
    0x70b1501051c0f0207060f0501090e0d0206040b040606030b13020f091302011218050a0b070807020601170705100e12010b0a1701110703090608010b03010302150a0909180b010f03 78
    0x180d564600c2d0402800441d01c103220340c088000078007410001814040c209074601f1181b0249501c041c1c180c84001c02c060000303070500c5810316502c4c10442120001a400300300000c0c045212543c41c103070818030403500400c9c402c0e503d40b80c280316581c080d6860002d16a01d8104401145011942c0207000041a500b2142c0380ca05a0796202004881001c0a414040f481603615200841d41d4000e81c40e400000a800c1c000608506119580b0350592504039080b85d03400703000c101218080c3c0b590500c100002c0d8000c2c4034580c280020f02c552041d01e00e042150611640d4008038075036480501c1910425440d07501c943d1390700800010080700c04000c10002105901d0415501d0a940715101480c068034251924080c18011607920540103112001a61a070311902049050030190702262807021242690350ba60845c3c1d88503550217001d80701c2071200a501028074404840281f1640001d40882c02e441c5c10201e82c4103603280d85000c00da42901c0000214240c114681c6010010405611405003181000c0c140310182107a03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 77690487 1250 77689237 77689267
    0x10f050a0b0904050a090c09060302150712050d02040e1806181902031005010e0615120f150a061206060203070525091b0f0503090c0f0114070b150105 66
    0x3101e0081d42c4980011700005819040300244d0f44c2c1c0003a003040c1050b81c0d920980c0084c205400100c1c42050494000c00c4940303c42d00c2a15401c1350416420340c80c140c814442943c090340003208503071401c0d40034400001e014030303c1200c151084d0003c1c00c060308507404c160041750518000410f41c20052400b25645245804001040c140b00365008051022146103400002e10b0000311604118260b0300340b500114204544600e4207000c0c54060303422548280c45032209000b2800303180004950b42607080d0016104249400102d5004140032101d1101010828045689080260002e402288120007403d5448806100d807600a22691024504288a43e40e03159120750500510600041ca8401407842c090042034048004160001d01000012800e0512241c0b200d08102c0f0301000c568002036604101c0d004004985c81014528080c0862100d0700d010040d03d0246850391504004002e0b06401e6a45030000040c143c803801520109134519141130360030301c0e01001c02d1140c0d0411109003d074100d040030394 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 77691737 1250 77690487 77690497
    0xd020703080c0c21040e0a09020a150e0d020d060203130c080a03140c012a081303080604050907090c270608010b090303090a12050c0f0604050111030d05040b010f050a0b 74
    0x612007403a8811802d0080240c6001d81e82200d92489404d0b024403000f6801c0d6231195a1851003521400c41c1305640341040c0c2401c006881244020a15207140c403145480c05480500305184001c021381440c0c60251600c0c0201d80080700d1002e621a400b90000060144e20314805008001030343c010480050b16580c014541d401a680e0807190203404034000f030b0111001c1d08a00300c1c0e01c5200c064500310b0780e090410211074091001c2e0100101d40140d0204182c0644242082d0071160076889030501516031400340700003028024120480341c041c4e2200803490b21054001d0310f04903211951600d24003103d14108040a103038079418030010300903801080000d5034011401c41c5c1140c0e0a0304a007600d403076104d80070070b00f0340c030401400070b0380100c0824011810643c00c28074111110b018008840035206d03010207110403581142c1d0701d10744c44841803008001561150303840c42c40105542040d00e040c05c4100034001c0503a4406d4070115452428078005000e13001c200e00c090b0004260884991134071506d040c4000340c0d40c2c401c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 77692987 1250 77691737 77691763
    0x5031b0607050a1d04140a050a0b150706090501020406050409060803040302010c1e020d0303020d0b01210e03040b03151201020313060507180f06020c1801050d02011101020d020703080c0c 82
    0x20316000b0002000180701c013403100c15000d0000d1080c0c1c02d100900c0c070100f602c2201c044500381e1620000c15a01501445134010407034020b08004501d004840030000d4030b070880c200c1141c3ca56190010200040c801b0f0001d000109101c0c3c03103d60301c0390308016180741690115006005c2c076a105100820143c2c0e4481d02c501c180540000b010750001e00c003881556180101706c20041e401c00803500445041550650051624070741e4518100103018041e0011680000c80c7c02220000e60386040042c18607141c80d0340440403001c0766804503498913954400c004403582048820360903900c442800ea409a04040040581414084000b1460751400d400e503a070506201c024040d091907540c40c00500454001c40c2b409000405032201d100b04280e96000ea034511b4080f5010b040018001c20712100142e061891004005407a04030050385160300340300c00e0100c00112500140c2c1009141c2c034522140b09828070042100302c120341c50160382d41c2d041d41000340000101605400c1c030820200b2180d21003107008280c4c2182a44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 77694237 1250 77692987 77692997
    0xa0503010905060a0b030f1207030818100c02010204050d050f010605151e1b061008030c1e01060b0412050c0105070b2410020f0c150307080a0204030f05031b0607050a 73
    0x80703217020a01e42a1501d90116403403059103449030380c008000780034109446c465911008955101401039488404da4118a0760700c0d80302c440d1030000c161180d04a1781900c062071000500303141c1c1d034000040c03c00d01d2017141945c035170f0400342441c20280c20038010342d4007402040d070b0b0f44502c0703010f0008011214410710b0440301440c2c0d0041d088010000310041242d061015840e00380c0015902082841c2c0c4980c820303204400e00b4410918006042503011082c1d0380080c00450183c41c408294050000541c000160151015566071001040415034000680041c1c15440300d01c282d040e8182c64038615000d400c00742581440fa06102c44000503101160f199401659240620245038001428101c0d0010080441c0c0e41f0961008003450f2099000a803010540316070000c46a28541e40810700800200701006401c080303030201b0000303c0550161030070710b4010b0a28039006140031355039181d0429040408008940e90380002074140c0c031401065008160740c2051703401400d1b01e03040c60b0b07001801c82c0c03180d100c00c041400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 77695487 1250 77694237 77694251
    0xf090714030a020604260c060a0804020f18070329010e010c020a12030e04180b0405030403080406050414010306060801060c030c051204051309020a05060708130e060a0503010905060a 80
    0x1440070711403460542c0d800f42c80c0035100c0386c58078115251644595880003005680820744400f200000406158010300036003110710742841e8500c110f41500e80200180d07048002264071212a44a06c122810007074411032400606c0c3c284030600405031590811100b030701e07503043d0070400082403003425000c3c0780e60424202407848015200c01070f43c9a030050300d400380d80100c221a00240160070300c049a0340946c0b2903603841c4418100c010070002295010303000d5084c0703284a41d10307004c0005c50800820b0b4020740120f0449042a90300d40d00c2d40c0c020780c0302d6001880007440101d0f041118940107003603032002541c242420300105007003035401050010144201c8013000280c5644a050502480002040c150002c05442c0020210901246640c2c02440341a0140300c00f07007000706068101e07210f04c0000542c0101040784103450401040300603005444207844400341040386556001040103080d000b00900084003916280100802052000680c0312034001d03410000001300107800451066031018601c500020f0700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 77696737 1250 77695487 77695489
    0x5090c0603220503041805010e0f0702031c0b090105060702010c060b01140f250b04030806010e0306070c0c0504020708040909051c05040906090209010206270a0b040204050f090714 79
    0xb044031480c00d4070080628806001482008030040c404d42e46008560411400e40280c1442128024868003041400450211b505804154020b5811040c1c41c412a0300f070801000c10348841d019841c0900c810380d41d54a03136040c06418812a070600400d000c4030301e036003031500c5900040c00d90b805007c00240b8803175550610640d00da02a0381100003040f0080803154035480c8820092055a10003200080b111a06002007178100311400c40041d40e0561240c8401c1d1681c40c0d642e015690381c1c08c090316040c144080d440f40c030401a00c0421009200e0450713035564440c4010141040d40c440219504103a00a500411102012840d45000c850442da000700000a4004490400070300b0048042e001030036000b5035010244405034040007401c1625200442007103069503071202130049104100840d03001d43c0280000803150444800c494800183c005880099400ca001750b03d82000100a4111052901e00040c07200b5420103200d030b80d03804000c0322000c4440c0d0428020f17040e59404a07101c0c18440d08002d078070080103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 77697843 1106 77696737 77696761
    0x601050a060903110a090509031c11090f060405030102120901050a090f030c060902040c050c0115030c05060a0c050303070309060b090c370e01020d0305090c0603 71
    0x7456143d0713030350041c12000300030542e82c0c8030900001c00150401c4d0340c00740034418440c1c18055551000020300c48401d1007141415450035524011041140c03400200c100d83d0712071401c641c10b0030030703541200c0001c0b00740c801d03900540d4140d4004560351401c0c001c0c1d00c011500800d20715000340f00640c0c07803601004c105c4001c0c10028146200708006000424010300d014440c480c011000800d224176590040b8003500c050540d42c0c000144000ba655000703210a104001c039810340411224111403541d2940c00852265010329445620005041001240180941e84184d640303c425240c6a25080c4030103402004e42d494103840c0c15003402e04804052070200207061089030304800c0c240c200000c1080801c00300e0039952414084401c03032005140401042e100745080f01740c860307036041094070200c03000a0030445080504000d0501300010300c88030450225a41092400980d85a81caa0755074140c1c0c002 = true := by decide +kernel

theorem cover : BRFrame.Cov 77517987 77697843 := by
  have h0 := BRFrame.cov_init 77517987
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77517987 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 77517987 ≤ n) (h2 : n < 77697843) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
