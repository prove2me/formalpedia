-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0598
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:39:40.971993+00:00
-- url     : https://prove2.me/submissions/0a8c3ac4-8b73-4c27-8e34-041bac0253f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 107374100 ≤ n < 107553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 107375350 1250 107374100 107374103
    0x1b14030d060b0c0c011b080304050d0e030706020a0f03050f1b07121a0a09021302030a06170606120c0409032102090108011a04091e0b03070501140f0c0703 68
    0x1080012110800002885140d02420388001401d05124500e10001e95802803d18494140500d0380c025040c10b01010501c86004d55000d00380594900d89890100e44450142c0b41501c00b14095580040040c43d02003008401c1d14525401080180e070140c5550800030308000301038003400000c0103201401d9812600409480003004005054082200354240c130340b0180b031744068003084500842c1000110600358494000c0100c08000585895100004005002d00d80b4000d5002c0c2803407810701400b090b6900607611130b203110541088103943e5010391929902450800f180f00750031400006101c0e03e0300914024000642c40c0441c0c4003e24040c0104044603c402e0090f07002c60800e10000c426511018640300c801081080c0541c2008000c4001a20b0703802d0600446441c00c04080c1e4403030700d00045105130b400070030441070140001081c0500d06520256852400400503041407814103903400c1c0001e410044401c11381d10040000048030001809401603a95004044810131500402c4d002c100001e00107507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 107376600 1250 107375350 107375353
    0x70519020a0302210f090f0405070909060b0f07230712020a08070608070c06090c0906030b15090601050a030b0a091506030501150c08210612030f0403031b14 69
    0x8485042c0a49002d144590141c1e5130306410700510001d8625100340c51041041c0b0041a80301c0d25224000f5040c0c0c0076410300150014904420460320b65030000c1d91500f16201c100c0100100c0d0341710080904140f10301072452407808003c100320800603041c3c0132805500d807a1a9800c4514000c031060b0a420403151741e2142ea42070f0161034000040d85049200c400082919400400e1010316086024104d100f008007280107000d01c0c11411024443e841e08030400d070f0b80e4004d50b0060b00c2501d074503118000307000c42e0005440c0c46c1540c10014000b10011411500d03040340017480010680d449100440b05640490504802c042c0c90303864082c107544038181c3c4100038015212010038100406401e1540e4801540d021100301428100104000012021240c03041400303440e00c41c0500d426070500040d28840c854080d240340ea40350180c01c1c0d9880300c4000081c0206011903515000c41ca4501c8090317501d00510b103182440d581d003003104100280c000d02030380001d11074240c4d010026500e01e840700d0f0041d00301d0a200b1700c0c40c0e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 107377850 1250 107376600 107376613
    0x3040602070c2309010503060c13030c06092c0414070b0c010b18041203020a03060e071701092a030605060304050303040606050a0e07030b060412050307061103010b0f0307051902 78
    0xb030703507501c031003250114400d6401400d1340d85001c0000381c1d41c1d2000792111851013000619001c000710f592003424082c6401040518400750389000091070620b4512502d00c1d101c19505522002d544902d0315000c0403462241c14910342e881f42d4030b90180b484051075401c012445200130000d420480b01000d40005005900009038035400d80081c4000c01d0790710300114800108901c10003002604406841101488900d40144c403100192001e40003800381e50404c102c4401c4041c01c2200056009130f8141010620a04001203a640d80c10f0001c07e5982099122180c60108601240150070540c0c803000c0f00341c40b603c0d0218500d680c0f140400c0e007030391095505540b03a400000401003403003214040ea400510301900c1d440c24003441c0666078005184e001e46100c00709500c9034100000d40e0340b00d5060350040c007a0001c40c4007100e81913103445a07480c0e101d0a003c5490a040c4a111742c026400101901d040b1010303134040c10302d40f10161203695a154002000c01c001d00a0903c220003403c5107040c0d185508901c0f54008040b07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 107379100 1250 107377850 107377889
    0x309010311210105120c01050d09050307061409011b0e0103020d0906060e090706020601050f040c0212030a140604020a140a090b03010e0105130b061909031203050f07030902031203040602070c 84
    0x416400c1c1a0030130500c0d1b020140c99845039034000e040f82c0d1505007061000030701c1030081c503007503003188540038010f03144900f400d4404004040018180b4080c6490344002c0002c0380110120404150420389903d0105103410185a400d5000fa00202821007540e5000154404a0b680d0402103800c02e400015261108108000c078481080100d1400790205000400300c66241c8400a9541181071380600d008a40340c0d101441c13101d0007040140c009210140903d03482e4030303084184000400140405500c41d251138000700d6442e091500c01c0355460b003059610140d020380d50350002d5490743d2003d908030f000c0144c25040014800121005180a00b10321414070038254034010820600704416091181c01e64a8501d210038213a607a44111002460041c20040e001d001350003040d103051085920186c8210600c0210b80c841540c10b0744241e104072031561040744540c450400032003c881000200940603448407180c041030345081006981c0c014481d180142c544101903460460075a05503000e00410030007002c000c00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 107380350 1250 107379100 107379109
    0x1e030106030b010803040617090622050703050d200709050c0408060c04180218040b0103020d05090303060102010c0f0c0818060c010c02060105040213140303160506091e0309010311210105 82
    0x104000341d44162300189041c40000c0750780707174203014000080c8011404545880b2900d01c40403103050a4004041c0d42c011550390928079202c00c0b40311400e0b000940c6081d600c0a112408240c00e615200154006004187c1040f0182e402040302030408251a03509210008404d0320800000780704500305003409031142d01e08a0040d0341c1c044004c0d449a4081c0c0140681e00003994041d0345a001104c0480d0085420208080140c009203c0e4624075580c442c00d01003003005400340080114014082a802004803480201d003c41c1e03020703490301d00900001d28010704440441c6c10311016150003007440c10300b031018408500000301c444d80003d4840c41d071030b512150403a40b00d6406201c01170051000341c500390725240c02c500c0048840c001c00d008510424400e109004100e0702c0c01c1040d5902d05010200d00b8220400508109603a804102c1e88900588601c02c403140000070002c9500c1a10342d00346c00194140a56240190003900306940242d116000030700a0307040c5101000e46800c08076502150080195040000382b2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 107381600 1250 107380350 107380367
    0x21912020709020306061806090409060614010302030603060c0a0311031f0608060d0222022116080601210c2007051f03020d0f0e1006051e030106030b0108030406 71
    0x2006031503c18800c02045444280440c0c18000c095030184211024040c001002c5020781c100e402d8205240551545c1001000d07804038081d40d01d812101078400703016070011400d80c84210b805c1901074200a01084110150102801020440d82400b240c5003109940e1014940c0044501115481010510000710b801d500040006031500e85401c920510f402c1d00420031035000c1440082c05001c1c1c00041c036001d440346200352144852034410555590356101109401c42c5554191040d900f8806d0002c41d44420940101c82020611511511410760352a0019101d03540781d00141c11000403502d243d035517411441d21422100e0485500c0399410b0300050b814004801151024014040c0d0000500344940e6540304081950a05120015004c0700c0d04680100c3c0a03024049101c24003d00303000300d000c5d5007c002d812826040b8035a4003100c0e003c4080d62402421365026114864001c010f42a165040c001c3c98001000c0f040c6014002141c5140d0341c0d580c0032107507402640090840c0c3c20100d070500403580d0042c01e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 107382850 1250 107381600 107381609
    0x1b20190b0403081b0f2203050d0216050a090b042004060e150f0a0507050d0504050108060405060a0e0903210105030c090709050108040f2009010b0403051b010219120207 74
    0x400c2000003c1000e610315205812002c000c0003008a42c0088217070580b074100d40d40702010203600c21b000f40d0360b28200c0ea4070300c40796003142c0150242000e00c2072802c0c00300403188211000103052400f01032402211500614600920b99042a1100036814013401541ca081c44010100e400081d5200e1403e4001026644800103441c851a00300e0039114104c00400c0a030b03008051003d0203d584c451741c40380250342e503104401c0300900c0c600035504004c900b1a0041c1c094400c40d0001e0700c03080100c0d0364040811045810031242da40d44600e15102c2801021440c043c5070340d00c042818202e030302c1c0c0f051400000901c030741010f06022162065038010301103820301348a034400d030180682da00b103598180200042d069147c5402198100400040080c00740246010072031300203a00182140c070808020841302d0040380c500103440340143c2c28900000780340b6401204840031030740c0010241144900c42c58541c078802040400131360440c4102500520381d49101c2d0440240e5a00c0303580c0c0d140207a000707198083e0a110b9a60312 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 107384100 1250 107382850 107382871
    0x209060301061202061303020901080d030501090615030b010302041d0412030c0206070c020307150503070e010f09050f1f020304030b070203090a180e01020d0903031b20190b040308 79
    0x381040f240c40d10a00f4022200d13411174080d500c1d1070081c4003000b0f0010303040d840607602401c01030000030700c64400300307200030320b0500c030b03036050100e46c0e2a01140001e855403485600c1d81d071480c0c21000008113100754401150788005140161070159500c2d4003201d807035003c0c103d07080300008010070300c420019081000300c040c2da49418284844040c6d0032001c0e440c0e03040141200b00348030030b085c000c004560781480743ca40600349030341003082d90f82d03c40724008040350000c0f00c0b450042060b02007100070541c0515036046040c070181d41d40055107401c01d02448045034490000c0d40e00251988020b04030391000441c2d0344081909580190307100c5155003445503601c40b000e403401c401d54200304580b901c50344403840120280c80202030000c400e10130f41c40d078260003494041424000c6520108921240b00d086400400760302e03020750313000e000794034940788200380e1551410540404514070651100c8400d208401c65604100f40500342c51220b100300441070168a030301d91045807411340381020081010380100300250855152030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 107385350 1250 107384100 107384111
    0x6030509010b1c0303060b03070507120207051302160501021b0706030603020306010b03151f0e03032805040e040b060a0e060906060f0706060b0403032d200312040209060301 76
    0x401d00d50803052400801ca00300400c6083d05060182d000f40d00200fa902c05403650708d10780140000c0c5240c04c03400d4222141410040411040c0c0e1000416070262030008290607215007015449a0003940484501160080c0e420142000300d8000e2000c0d1454449210044110142d0f20422034104030036904444241840c012080c40541c60014810303054680c248407159986e02e03030340354000780c2e440d641704417580c0014100041c6900010030700d1042d0007074519403a0041500d020400301600c03400b4141c01c094005400c4804070b6503003000b500704a5910000390904624168a881410444d400101d0b0240c0e81040315206000d02c80c140114403178000e00304180703040032a0600704001400c00002401e124810325012034001d0300d40740148210390685500902c10058659180c840c0121078000d4841134001c601000d501c20070391500c6c290812130040c00c5050105820f0a2070b0f405441c541000300703501c1c2000d2000c40c0180b102c10320400061007030580841d584881480c180c810404036000081c4064000e90521 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 107386600 1250 107385350 107385371
    0x7060903020409061e0c020613030804230706050301050f0a1d04150c0221040e0c0307020307060c0c050c150a0309080c030301030b0421090302060a020c0405010f0603050901 76
    0x20641a254101c4010543c50224203200d0b002d48010300554080d14040c291240d0060307415485051019059000d84910755901c03002c078041118401c80103004500c0c4400001c0000b441801d6440740d0030348803510342d40b400f01410300c41ca2038001d9940005001c01c0c0b0000060000d0701d0320302e0304800c0d0401c1c22a4444c0600e81000b03000740041140e154855542c0200001040c00c100003c0c40b4518841c003618020020003084000085d603d01c02964800702499211a4030395540d41568200e505886069200003c82e443c1c8c40d84822440c0c0c0020060000c5020a000c0340d80021854001d0580f00d1301d255480300303400c000f00d0500f141010a08039180f13100ba07604000603100d100c60401640d444142d6400c00107110021420111038511503000304008a000000000c4204070b08003403882c3c0201c7c0103440b11000e120400048180203552041d2103400b051a042c02000140380c42001403040584920541741104040000306d41600c5080e00b20000f484c06d070322001d103c81a07161060310340c0700031410024031542c2c007003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 107387850 1250 107386600 107386607
    0x90e1006180b0a050d050f0103170a0c060204090606110106081c0c050a0303090c140604030b0903070c0f05040e12181503070914010509010e1201090c0803070c080706 73
    0x284600c0d014400d100310340c0c0c0c04040860040000401d500900b941c0da4404a0b0002800f943c0840700d101103e0386000d002c501c91421030080503040c2c0f64000c8200c1036102070401e200b011034000e45166800c01044510070400142140060310041c050741c0320104580d800c02c10003624442c2c0c80c00400c0020380c074240c401c1140d907800003000058680920001b40d42a10890341c12240d2801d400d001410b1441010552010942d2590203006c286003c5d10882c054141c49080005092603030201440d807280f4140b00c244081070034924029000582c0ea07044034907100940e91501c0c41003200e940882650300303440070100802d003030a020341000c0d400f51001602e0190040c01080c0001e01074000c0201c800110a01c0400b1142c50300d488117141d401c804803882e9100c1c9803d110050103500b85004048100518410011517540141c00361040301105860380c418000d600704c2400f41d2884003034080c14880d9218181003000c00c18601c0c02d00042d180d039101840d5203000604101d95218403907400440181d100c2102000f0480c1c1c07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 107389100 1250 107387850 107387881
    0x209030601140105090a0308040501020d0f081f03050f0616020703200406030503040906031101090302030c040510090c050702040c0206070503040b090c0604150906030b06041809050303090a03090e 86
    0xb011541c0851403800c0c2401216180500d0f41c490b9001024590080248103c807000313801142d130309908684034000444001c440d603801c146a1310010400050100d070401180d144a440c0000045280e80c00b442d540b40c50741c514040d0400c50041c0290000070034409a01d071000045503c9070000d0004140c06840c5a403030b03281708040d40c850700c9a14403030701d4000181da41e21038011200642e00141100e407140c0e05ea101100040080c1d2108071243ea04440e507030402c80d40681205011030742c00902400d042c140440c01c0c0400340c0742c000c184004010031210040b038030764124402e401504159030340d102d840ba0803d1051004480d00b500d601000e5600140800c00e9640e4400100d903401507104004442c40d4070f0314117106203480c0c0b4100501c0c2d4400c0011038003040c0c880c6480710001d4441540d940701c550b2195a43c03030a03011590f030140c43c650403100410052201780360a41d201c100003030301c00d00300213040101d98890a040d6001910714031615008402841c0905038808a01005860481030002c200d040492000c2400b14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 107390350 1250 107389100 107389109
    0x20d0927020d0c090e060f0f1504030c1403060106051b0a08190801051e150702100c15050105060d021305060406050319020a0834020f1b03031813060e04060501090209030601 76
    0x142340250820150300c1d00c4c0240203220020040807600d40d41c070303884c103207988060703600079074100d020104660303845440c001407428100c840c1c035141c1614210043c04440201d100843d04103000348151401c1000044401d401071020444c0c0c010180e2540c0880f1400500401041e0300c01445540d4043c200d040042140e4070707407055640210380e4512514021140d598140c06146006503001d04d8130421840c8454100140020382072203000c410803a01800e01c0c071007044510a001d44c40d0403100c24003c0b20901d407602c1d0300401c0031111361000b10925560311000a00140e2098010000140001c4284007540c1e01c030004850b84c40b214203030305500302030b070140c002081190028880c8410b5110014038104041c1c00072440002d8094100030300d045264001f05c06550380040c1140a4402e11030080059262014070281090b01c903c014069458000e0018900078004c0740c9048859101e40c03110021050b800c110300ca044000e20240e07030059503a181c40d0405038100e81c416403086503141c2c0108801400c50360b021a425040d00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 107391600 1250 107390350 107390359
    0x2b020f0613020d14030a0305070512070f02070b2d031e13051b010809120d050901060b0d09030e0603041e0c18021306020d0927020d0c090e060f 63
    0x2800319000240f03500801ca00090440c0c441038800c00c400c00030100c01440043c116407402d103c161694075003142c40707128000da01c00c1c2c00001c2c4804200d0591048003440298803c602c1260820ba40f01c104c051403640c00b98200c0c01c4917640b0030507060085038041030421552400c0c0b0140c98110f281990503010340005d00c40c09506403034400000500f00c1c900c569201c8100075001012600c6104854842c8150700c1c0c001c1c00e00760301007044e813170000b1030001c00051504074080454181c1401d00e2240a2801c000c5d040241005059540312074004c51548600c00c05400170880c0c4c050013041c2c90300b0505010301380d51450100540148070800402012405203a45d0300620302042d102000820581c0c14603d01844154001600f46210003058245800071500a000501c4400300e01c40358a0f9502c6d0801c0e40c0e6900305108600c08600030090400103a6000000440002c405078030b9072210750385491440c1d04980c07016048403541a41c82110284c0a40e0200b1030b00060200780904040609100d00040c1035005c031942c080b8840c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 107392850 1250 107391600 107391631
    0x1060e030a06060914011a0708070221060f01060302030f13020a03050706031e0504050a12110703031d09070504090e011d0304080d0203071e02122b020f06 68
    0x65202000a0711829811400800c0026120024034015000c030b01c001c2c000c601890800171400741407000022540c007480901ca00d1404c1080c2d9244401908206416a4001d950f0100c402c648807d0720041440340225401030603081c50140140e90f07030010b068000904040c03050041101c0200070035240c5410076500310b10020740807114400950401030782e41000f400e60180031800155103030590030400f0b082c200b04410051150036032009008403003040320060110703132240b03142d4000704480d01d480c224101c00503c1d007c16000321014049292116580c0101d000803144140401100300b9000c9c0d641e044402141e040005050141d00103105009a01404520903540c40b50084110f00941c81035048440042a05150308e00c8040d0417a01c0360400d21603034620740505e101c181050340c404800c03985103d91003a0345100c0031140224140114a0800d412030f000400400903a0306501c00300807069010070480c1242010030900d8011452901e06240200c0c159485402d41e101648004100c0035449641100c64440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 107394100 1250 107392850 107392877
    0xd0305041e081b030306040c1d04020304050f0102030403080403090909020d030305150406090605010212030106050301090207150e07090e030a140f0403020a03060204030c0b0f030601080a020c030d0b0306010801060e0106 96
    0x440e2083c07084000003020400030550b08200040080d510800c801c54080050540b050029100440640e500c0c1000f032203e4004d8145520f096405141c100380620126186071840046860032640180c0701a0045200c5d40100400c040e441020702e0058080d0000074081080c6c90381c00308481c2400c1040013400d144d1a04001001c0c00b0f8031b500b02c003800d590700800c14013817655654058401405c090141c5801405034804000c1e4034213844040720704031091130343d517245180c0c40c0014010094005107000c035640500020103c203802d42d14040e2054145041c4080c00c2e00ea031a1a044608031021500540c3c2240c00601c03120a01c0d80e00003060b0070191401c04092a61206138600106a0b4070031900025072200760004080b06102e0554050416640305009403a4255110b0100c410382d400b0710f0303114540004c03007040011040d5204086260304004425000360516065074455411034104491540d91690780d06400391080c98200812401046800020443d160414024004103001402003100b840442010040b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 107395350 1250 107394100 107394113
    0xb0a09120c0204022b0c020609100c090308120a05060a05010c03080a060302031501060206060d020d060b01090b0f0901030b0405092a0607030905100e03061603110406050a020d0305041e 81
    0xd0710009020302d00c0000306200c5d054521a1041d010899500d02d103454100320003103000103580c1d030241c1c418000620891945500100c050000e015440007042048200040020400c9002c0c001c81080b400c188505032034507041913422120000e264030b1040c0c10b0b44800b0402c50340c015000d40d4030705405142555243c3d8581726400060501d80d0b00c0290580f0030203101540c980c262982c500c2c1a10740a41c00e83e01d00d91210320402c540c042e017904d030207548103148100010028480b0f80c06840c2812060403c2d05078103a0300c0100f120141c0084200e00c40040c0001001c507080e41e4144105044100111000c00990078164003e5036116005400210140c0c000c544000700070840c80b902004400700181450780d60350f410303d40204080300c0780c440c3c10b01a200101421400d14054110b80c0140c002c05001810103a458032458400340c48040f07061414159950182ca402650860060000d0816500ca19940d038408410003403400030000d52480800d0714040c18400050565440300115100e446810074000c0010704105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 107396600 1250 107395350 107395357
    0x9230106080a050d17010503030d02070629130501180b0312030a0b01080106020d080c0318031603080105010c0f02150d050a05040309050111030f030c0915070b0a09120c020402 77
    0x101d5803403203181001010428000350008140140da51504000c801e0901e6140d4246000e0080c0c1d5070540041c455038a1a400c80d41c0500003070b03406200003007140486118007140c0751a8075500481d40740160310401c515814481050100300190354402c211030361609415400100c1c2d91062244040c3d00d0301848280342e54200140700c108a05403140326521708241d55003200520303601c441a80070508100000a100d40046558442c03c503554444480c240e4a040c20500d041d48010f0a0f400002c4204c1401d0640301010000381c680e103401000c0b800d2800c8200e08010f030100005030f001504124000c021200010741489640c800c0e2907042e00c10b64441958200da980c030f24002e0028407001185410b00308a0052800d0300003078059030107074032216151134441d001168800e1320101d5440f01607104102e6400c00005842c0110303441210f00074028100038010001440700c0e04922000d410b0460080350040c103011411140c186c10101841007000009a0390317481a002400c00c0d8110000d202c00b41599000b55203854044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 107397850 1250 107396600 107396609
    0x2070305030301060305091902060a08040c170102071b2402120c0109110306151e03010207030f0f17060d020f030609151005090c130f0b09120109230106 67
    0x1c1d01d803a507841301002402032400300c42079a018441c0303200302035240041c2c2c030601003180d4026009500e444510481038906040203441164003042d01071303001408820441c000141d110101001503030386c0c002810f090610110300159601c4400542c0802c2204204607188011954082001846603007a210b100303078141110321001100a82001442d14401c40d019804510224810b4001d0310300c0c200c0c01001c0c1691040115038060303103603108541106a510742020403020408211728801d403169582d8000c2426a008000120003085014a007162150b41001c0c01705001d007d50b203040c2d4540520510040b00501018021030300850340180c1490541d11403000060050300050200c50150815510b010307036600d00085166524041c6001149003d14981f000a0132240020100390b095110120200d4480e80503440c0782030392640a5a002030141d10b00816103008141d459481c548419209040c0001c8480d00400768130507901d00301030344000610004905411105032903440141c000c0300485c890041c440f0342c12 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 107399100 1250 107397850 107397853
    0x304050406170f01051b0c030f070501061706040b01060e0f150307030b010e060403061d060f061804170a0c0803010b180306090712031e080604060602030901140a02070305 75
    0x4241c1c144544820181d0400ca4012140843d81a040b030030300300ca10507103040c034000403144c44800060140740302030581120903005403407070220f213420f50040c41d03440204126580d07511481c0030040312101400741c2043d0102280070340081d151558582c0540b0780705000307002c14040640c03208100c3e80c6034142d006103a404094900e40944040e500004803940044030745800080c1010f04402165104460f24801c0708030113040c6d2402c01e0700719641d0002825100c1c42c113040c10144004103264040e03042000724002e6000f1500310a0f20b04011090181080612284444190304041030000003018041c0180c104220728400030749401d81305e44120780c94051060041c06100000c030000c43c603400d101d002003081e107802c0d141101442000405054983e44212216181c17a04804401c01400190701400f8144512901d0013855190141c40c1900c00c000c5a001050001070410781000a0f6040c5480b40300c0140c0203500086040000c2c1d036000800502c4800c0d01414421404181d5402441c000c002000181d0790010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 107400350 1250 107399100 107399111
    0x308070303090c0b130504111303060504031209080702010c030207080a03020709051005060403060203070c060608030901080709050f06070c0b0406020a03030b011b020d1104050a0b0a1e05011103040504 88
    0x100203029007844042030300e000c41040e10002e0100306030012507000009039000c81718010320300b1081100905c4000704d02010b45900b00300081002c8103506c402070107984110300008481c1054203004020071404000101d1040c07907c0106c0000c10100c0702903500c0a94246040341c0c00700342600d0100c0c1094051352200352148a50f0040d0800c0540104625099078421002080075070f40781019000c00d51b00b02c0c85001c0e000403042000b0b1001c40e034035400440d40440b09042400001040b0b03604d510840d4015804050180c00101d5001d109607484842c03203030001c2e42450720341411410240026070b00b1181400f068400c0350005420300401c104071105000034440102015121662010069200c10b0800b2085000a10b400f4014215602441c44000120901d885c2e2800c818142d6080c02166018140706852008008040c1c00d401d03038440c02010301c01d200312100400c81442e603809001005100303402c0001801d071140d0240b07450301401e5610004a82d02480d1030000404424a601d0a512030340d0025a0000e0825 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 107401600 1250 107400350 107400353
    0xe06010903050610051203030c0316030b030a030503010e0a0e07090f15030b01030203060f01060219021207032303070803060103051306061e060201021623010501121209080606040f06030807 83
    0x101240b004035081642c4041b080c403202c61031280c0320321044808003900d0a092020649a00000040c0e651601490400045010306100000c2c070f01003070054124006840000180100c41500c80e00340e4004250350380c14801c14103680301580c0c5450441c050150f46658400b079404040380c850300540741000b000741030030300c1d0381d500d81c1418001e130103090009901a11502001c105405880070004d070403950b0070b502401e014403241c0c0c2032840f415051001681c0c44040c03c0fa042d103147c0d80c14440d210081d0302c2a0701044c0701040784d070a001981c034584800b0140c0c64000b07018140202e23000e001100d5100f282440c00040a036941d0100311200610660040c2400780740920200e9090b44541880d03103e40404644110010b655040c04c03400e034030880c0c40312b00d0030030306140409000a01070101d07440c417000c12032540724081d900f044c40642140c070b00f40c0c0004007c400403501d40041c04940c4004e040318401c06d00c4c0c07102c4104e0070005c0c504c2d6114070181c40c07280580d40d00e213685095084103600440107140d01200b00c90707942485 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 107402850 1250 107401600 107401621
    0x1512050f04060c14120403050d050910060503070b0d0f090803090303010303170106020a1101090b1c06060c020603010e0a110a02030a0801290c0c0d0f061b05040e060109030506 77
    0x11039003150b415240004100025000d010603801c9520707103801551800403400904a02540301070402c405200c2c09000703d00c1d5008490103854840d00840004080d000910740481007035420952106000c3d402c07180b000d00c15054080101d6040301d00c83c2801042d0800c5661910300202116007000d8010040070082c0964107602000450480e40a0b0ba1030101084c5022490000101c00781700760000359004520120004124041d07400103484141000c0d00860b40e03c44130940b81d0747c072a00c0c442c04485031b0300341180c240314110320074076000e422a4546503028401c01d6010509501c01070044d0b800f400207c400055941c0d00a411102c540c4204c8680c0c00d84039101d0800203540c0b60041548140810b035040d0002c5810310325907220310005901100605c82030b000b0003100b1006030784081602000d5000b10100d404041d11640030000c3c2203032050010088010203402d1400c00c13074000011420b070810000c01031310b5841ea80042a2010340340d294440c8619500c0302001a40c0103242d90b4401001da00036541080100700c0b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 107404100 1250 107402850 107402881
    0x1140714240a0b0f0f0405090a020603150a0f031a0c0f040603050105090f0c0a0f0203160807020315010609031103150c0c070605091509010c0b012c04030207151205 72
    0x51407000f4080f0201d16002c025035440310394106a0401c180500128140ca004d821180e00660842c00341c500441054012a1a580c07080b82c64141d40d02c0406c592166600700444500c004111000b07045e0102400c6545410302c0170300040c0000801e00d156004603c50764035440484070990f800940c92565a944e4150250103132800f403040700c0c0300e0409880041e280100c0346829520440b5000300302d85c41c11480b15410346403142c070f850320b0004500c02400030052001076650b40800705800366003011348030040c82c410107140c010728220880071204440c0040000b40d400c100301001b0740b40e00102100c494110740021920784070000c007610001e080808180030700c04082e80028225240b00c60f00750744003c4d480740010b0f03e1610a0102c2181c1011981f018810200c0411000c0c02c00c545052501111600c51901c61001029081c1c0102200101d0580d45020304040c42c1c8507006100d40340f101c814a1807410340c8001e5110710700c501c6509034044000715080c2c9181d21a40064114824085041100c1d040101c00242c402c1e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 107405350 1250 107404100 107404111
    0x60f04030c0e0601260a021c09020301111603050304020103140a0603030e03010605030717150a05070801050a060c06090303150b090a080c0a03061806020c0115050114071424 76
    0x45a000416a0743d4030030356100f0002c0d6111402d010340007984003074045c1034010007081e2061050342489030307284080402142c034860510510020411625500400d421103019070b01d000c000c008204180000341142a07a04052150541041905d07542c5034001a00900390020018089040b074504100c841c0c1c41550200b07090740d000e45e03a500032000611050500f241c0181c000e0b030390300d0f03400b9400400c2414401c545c0080c1000c644010343c3c2c0c0d02c544e20103802061308401c1d501c90041c41c1c0c0300c0e002c1014840e80720420750700505046038501d084e2840c0c000054901a070054014280c1c40d120701004042c94000d40003c410078407404d02c003494456403580303a0111a00204482032188003100b2000410000002d00c66210560040c04d41010901e9950b9150040107980700c2d42c40d4080c038040f84100454400e1014007030040d44c480c00400c140c0b0a42c04c0f2945443c501d90042d50500c450040c10388603085204055030070b0740781c1c440104072006030407000335407416400307500d04006140700e50078284140043d5085a130084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 107406600 1250 107405350 107405369
    0x140f040506071215091e27020a1521060e18070e01080d080c12181f020415020d020607050c0109050304060306290703030b13050a0204080c120615060f04030c 69
    0x4840c6c014890585070315035081100301c10075442e00700e0340c8071401c0300d459003c61008211100241c0c1ea41d0400e40e500803a4007248c408241c03600e41c0c050503410f42540034602c060b9100300811080341031120303da03145030b0060082d9140c80303410030204138240800c00c04003002c4c11050580c034101d50307074070b40d0703800d540c1c05401203800005003c1f040400c0300741612809071a02d03448603010794002030f0b8400074030345c2c03e9924040100e8418811014000383c1010342040030f84904040351005a0380300d080c10504821200d050b4591821036015001044c0d919a001c02e1040d0060001e00c0c2c52652100c40b881d15501600308140042d01a0000141c0080c1260300343d4016000c842400d20b4009040610060703c05000082c50304500b05901c0402c40a00001c1c440e9004070090a03008064140703401800c2501001c803002111920312880e40040c050180f003008200141c00c440c01201d011000000c10b6002035202c060140c0340a190782501d0a044000b992194192048081c20b240100d0702e071b81d60390404100d600e0062040c003082 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 107407850 1250 107406600 107406641
    0x210507080705040b0301060806010e100e0a020703030c08060f1203070b09010b0102070602070305060106081801020703111c050d02030604090813030b1501020d080603031c140f04050607121509 84
    0x113604042c0070b00030498115101900d0240c0c641041c004038250001c0088401010b403d001059010035008045c0c0a401942c50040e05c0703182510700502150490303241c076020301000310200b0841c3d544071141101c40d0382c0c042d9182c841000981c11802e140d0700602d07200a000001003820070406500c1540280c210050990890b8600c1c4d40c0c07224260703102c01003800050641c1d085a801400090300401409400c500144801c0c82c00304000c015107401c98101900031400100c141c0a07500420000b00302e001d07014106000000c84101d8aa00d01a00520601000c01c802c04e401000149155032958408941103420014066071109003024240107060b19010841e441c174802004100c42d02000804902d1520068000702010448400c0644113410010030b89c0394540710400000d02c402d82d801400501061407601d0200c0c1d5114552b1041f90040d0001b04010540c0555030301300004500c0c001182d940051907401c10880c00c0c1041c40581c005428160411060003002400001d400002da5001040e58290885080796 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 107409100 1250 107407850 107407871
    0x4060906081504020d06090809040c09051e12060f090f150601030e1f09142805010f06030c081902010e04180b0a0b0916080121050708070504 62
    0xc603429806405a10b82c441204000c01495801c16281c10500007800c4248568140da920015508080e00440b18008040358405040c02c0a00805000311400d081101e03981b8144004103020404543c40040450346034003e07950140c0302c01020038070504142055400c24540750303d014218920a5520b103045120704032800405501c0403424600a4582609400040c3c58a0b80114080d0203040051000350041e0300ca000488020000d050040841c00800442c40182074280003100515166500005800c0007010003d030002ca1050016541245541e40d01c0124903410401d00501164000c1d04000746800c50120600801d0030208040300c1e042004c980981c0072259080044021450000f0f0208039940e141200f50714007500644c03500441405000c420018540300c050780c4510940c0c41443c0603176188590b80030b500703004020980c089804242c0c1c003000072492500800d4401f0510070240075000790045400b0a00c2c0b490034006106800c00211000107440316869030700c800c1c00c0e1142a20507480c0000305c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 107410350 1250 107409100 107409119
    0x7090603020303031512011a10021506040c05040b270d020f0603070c06091101140708070615090e1b0d05120703020111030702010c020c0607052a030f0604020406 71
    0x20103a03903001e0061411074480c005480902038120b03507016840b10741c10242800118091040740a900708500080d170f81d1400040910641d03e2022009038115002400307641c08100a081ca1150805800d5a00240030b0440c0da1040300e02c1e01554000d07000e00e002c002500b00e050050741580c100143c2c1200d10710302551680500301b080508403803100940000c0400b03900c80151400310080c5900a141c0c1c01c00640c0d032400c44c0d484038101c03007004038201c5402c09003205052083d40d204800c004182d44060b400362402200740c6501d0540d00604030f00808813611498040d10001d1404c20b0b00004040280c000d120f070700580704000d52200c0c00050b10180d0310f000140480d400c2d02c0c2100a407841a5082000b400320f0860303000181c81c16034402c29081c0c0541d901d4070741c4d400704c0880c0140114491a6664000107c3c80c000c914000d00345040403692070b119920078030850010600110f9804a1070540920600312124050b01c1529100b91021510303600d0f004e2040f28034503292010071001c0c07049100305c40400c02c00b40c4400340c15 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 107411600 1250 107410350 107410361
    0x70905180105010c11010203090a03080d0b010201060e04080a0c0b0a020c1216030503150910150c080a080612010e0d09080a1e21050409500c04080709 66
    0x140000c08130220840800c41e2400d0808a0038018810b03a0302d40070500c0c0104030b100ca0103600849002400082d9804802c11a00c42c000074900700344007d0244031300e040071020b080a40a13101601042c0001060035081e0300402010303d119601a4540303c144c07231f007180c213a00250020703c2d419049029030284a8017010b54501100d680074000c103241386240005403400c031101e41000740883d081c040101c110041d036544040d4410322480d03132450a681d000c0c0c1015140c15491100700c0c1c0030010302c111109480d001582c15816030b409882a4a0300721016030b10750b000142e083c1030114502100354600703c003001c131244000c2010552803000740c4510386016070300e01002c6c2e9103001c040300250400d6116161500698076498003004114095400030701ca500200400510300c0e510140440d003c0313803000030104810030482c000d4180b000803480d01201c120b20100b00ca02488010707000d40300c00301e00400b07006507110200d030801188000e045a40c2c840007841c010b1030120b8254800e004d1400caa22234428006251105800340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 107412850 1250 107411600 107411609
    0x170904060b030f060328080c01180510110301120809210c01020601151b080c07050103062c0703020c1005010f050a060f0807030605060d05010f0f051c11090709051801 73
    0x81034100106c0c1d201e156a0002c82640840700808100441c5024030001d0003908103414600d21003000c82c01700c920b0300030b180140440003021441c0c04c0c80010701c0d030701c02c0d50420350341150601003c0c1004c1c0a1140b4244041f44110300c40c05034400d043c202103600600781082c0008002c0058402c850b03156100500580c0d0707480d0248951072a60b41102c030301485170341c41107820b5007007000f0764411000640d50664400015030080241d06010380d00c541420419580e050040100034038507034201d045a0090f41a14101c8a00030307011440c4a00c20302d0011900e40f52007a0704444a038140542610b03c0103600395140c4010b02400e1040254100c1100e0003c0713183c1c6050102c1c681100d800c3c1d141c403001d1400d4007401355031040004100f0b1050594074100022241c4588004100303e841d0184002125170628041145014280e00194800c8840b210300f480b080d02c50760401c100702401001e1030500c0c0c589918000d0300014054408030b8000344654240100d40d0f800c01109402d41e00103c811010780c00c021002c188071100240306 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 107414100 1250 107412850 107412883
    0xf01080c130908070b150f1507020d050a05010e0106062615041406040609020307050304061a060c0606011d03071206020409020403050d08060103051513060f1215140103170904060b030f0603 83
    0x281000c07404d0756400511509c2c1c07016010344444206034a8840c1040b11110064070140d46a6030300d100308440a100300809485203041000d200c07041d2800307100101b01008800a400b000d0030001c0355910f0f0350307046d03000d4903002d00800c2804000f40c1447d40c82c9083c4030950b8200c1c01142030280128021020340241ca10610301075131600c0c15070b074640e250400500000d0f00c543c2c00b110010028484241ca44d40d000700b0710001c454000f020541050310004224002c003154162042802d1800040f02d5074001c01c907401110703468036080180e030116003085002031245a21041003948001030000400801181022914900da110428140e640c0c1c030042d02030340c2c011101c2c0f1714200e10314640e002c06450700364039800c0a12016074000500c661100200b541030f80154101001026203131442c2c40421814008003800e85940003c103028003080203034031070301210040c00014003001040c0c0c1420500e036408400e0705c0500070b00510a00c90a507492020404a510980340c4084407140d03040014581d003000130307246190704036501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 107415350 1250 107414100 107414119
    0xc06070b061003090203030711091006050d0b0a09020d0b01080a090503040504020309030d06030b0138031b0406030207110301020a09060302030a14100e0f01080c130908070b150f 78
    0x1d04000e1101c800d1040e54041c1a951096900541c40400160081c10301c250811000c4036400010402525401020a01e01d0f0302000c8040c04290780c40300950340d0701d6402503c0821440308180020b00c0042c5c050308034040040c40481ca00501081582007440240001c0e00c5000058880c0000d21041c0c40403400301800e964401c00080101d070070b2960085a02403210380c1540e00300003c0b048500181c408a5005492143c0c6520040c8002d040c1040c40c04125401d0000f4412140d40d0660b070100d1582194002c403110500100000d1000c400380c07022071660411400119550b151904406002500040f0f0195002040c3e62802c40301424148225003051000d91900c03101e05151400c210040d500003400d000c0c40c0d64440c18003034280c07d03c500700c1c24000e03410820341809060810101510b500e100901402e50341036280010811542c01141459010070182c508400a409118009020b000794000040c01c800340000d200c000e02844620150040400030240b0442c540c8010401040d00c0c2da01d00040d900c40c0d40f44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 107416600 1250 107415350 107415361
    0x31103030121020105071b060207080d0206010e1e04030f0e040911090402011404180e0d081303090b030a090302070608060609060304050c03031209010b0406031101050d0605060d0b01020c06070b 85
    0xa5264400a80f052504501c3e201003541d440e0401240840b44400c0a03600d0b03e402c2c01b401d81c05220300c4c0098607044000301030600316804001d40d25901172154100ba0310381c60000c150b008403036136019080c009a1405000c80b03810035181c0240042d585006060015600014411652605015010341c1c9030304141d07240340c001e02120401c4514540900700f00d05001c60031041500d460b0003100544020190050b0140307240d0048410182a1040d0600b140c0190b00100d0086a00981042e40c41b80c00c4502619103002a803182d25094654a0240e00882c481601c084104581510030f90000ca44a501c26429a02c48a82c6e52000b40da03000f500b501d442c0d900203030610404a42d400c0c0800a03682c054000d00846401d40e0141307010a0869204d01684c04c1d104113000d04000580c002402224032142080ea01042014990740303c4d03031035070400c00301c455041200c00200071150f2091900a1400351000901840c1e540701c0711071264008040890420303015004006041980c2c0c5084001d0319a0b40d43c00c00801255507844 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 107417850 1250 107416600 107416649
    0x210050306010309021c110d02061603050f0d1d06070f0c060f0203130c0b0a080c03060612150a06080c03010506071406040c09060b180f0103060503060c070311030301 73
    0x9241c24101950f4200310000350b40c0740300d6074408110080843c1e11042c084c40c02d01e030040602038014103016200c52412000143c4a4600700ca10034540b0181c01c0040b008645030407625441141006c050a02c00402c0c1d03000c0c0341155a0064003818082c41083d000b65051003809070321520200d480c8400705001d00844076080b130056003804061880b605d80002c40034280b40e4118100d81064078150820070803041e0850400c4042c0c1441d00207407110007a05414220500c4001344600d80060a030b040c0c8060210100e080c50b1260000e0310707202d12543d0452022490a40d8800f150a42100f102901c1804100400607500d40220f01042c09407195441091641c0c0c01c01c400e00c6050380c0b109108541d01d0f10741318955150400244000350291b80b1905034080d4a0385800c00398029200c0a030000c6000c6101004030351040c15110a501c200d000042c0c2e140403002c1c20b0140160014002c4c5d52059400d801207600b0403110604642c0102417680c841d464100b641003080c03500e199280024043e84101048008141201484 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 107419100 1250 107417850 107417857
    0x150501060c2a0807080601080105180c01032307351b0708040b04060207060816082a0c011508070306021309110d0c050906041703041a03010608090604021005 69
    0x10a4400d40049a9604103c0d1070185203900248551700004014802001b0a001c0c0c81d402114403c10000100d204921441d01d0b0080c03121014107050341c4400c10810010140c110240b0070301d08100c0d4010f9032500300d070040d0a0281182c40d460044c820b002120101480140c508030112404440000d580da540c1d561428a80d40c48501e81c001c203202c02d00981001a41d5031008001610215003032903141c0303203400d001134580382007900240b06010400b0200081940302e03007521490f503419480d04001e50307141c0f4800c4410b82400b00203007100b0044000b02c9101661801c000902a032000c00000300034a0b804020001218420742c0502c107040d0300221410000b04800341c01908144039000e03c074000040d41d904280040310031858201c080d00001003480d409600c0607101d00340c2007141a0412500d011003940005445109901a0b0184080d16070042c4800c0343c41003007600d001d402010800c0084941004810f4460b030024420400090400c40019455840c0481d1b007900a59000d0040c43c5a002a0b0b80241c40340d03003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 107420350 1250 107419100 107419163
    0x30d1d01030209030115080a0b010828060f0501060306061202040303020303070807050c150601080a05061c030c061505130b090c0702011b0b0115050c030f030c070b04150501060c 78
    0x41d00e8001260686d140c5494520040102400a10003600e080c503201d1580e65050b0310455050f00a85941c0808131f483c3c00350500070440400b040c2500101c03070700e8100001c0c003001c8045d069081c40e200000c102190540e0010003a5603054594140344902c50f00e40c1c1080e80320354000200160414404610b21a01070b1243d150841010304215081210300407400749040c4a00304a8070700881001e09024495801901c140d40050100b80244904d287c40c10208840910180013034440c1140d1102d05070074503105030311384414039038400f5040c0101c84a00c40c42d166081c19070700400d031080401810740e075195282071096880202d4003030651401580c2d201c0c22040c654100c110281d0510a154040741e42c0d01c00803680345104d5921580301c2c0700c01541000c801c12030a1000121100501000700102030310300d40000140e0b02009841041156170340d9a011f40022640110880100001c412006000c10080d05441c2d100c030b400e420a01c00c02c882d032b9039940102d03054054450040c11150280a14003040e40c900c800001056 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 107421600 1250 107420350 107420353
    0x90301060906083f07030e030c030a0311150a0203010503190507050409140102120f090703030801182c010507140d0903110a0f050f03090a09020c0109060911030d1d0103020903 77
    0x55504540d4554a282c000c034904d0b46041c0008140b0205600402180c1e0f00002c158010310450b98000042a80c13500c07804800340c20b1008115940c484240108008200c1841c01440341601d42850230b4410081d40007070007180e10034040e496079100c0401c201075100030031581260040039118601400d100c0103186d41182510454081c8404805840c0240008c180d50101700741158400c1c5801070000030303045805041014207800c504000c0000c00d5100031402e054404103821498800c0d032110191005006048002d48203456602c00d038584001208080c9110b0300b4800000c1c030460b5600c86c0c3c2110b1f504a070054840d100001484000700340e104a0340400c0c50240f29080260502c031003040500c3ca000407012086901c3d80200d012041041000c1c0040440b8040741c000a609141c44900003c00c00011401075902d0341c0d6000c5402c015400e800d40210b41d8580d00404100b0500707003a824144d000641d5460a28001d108034840000c8162046040c81e62802020300c45008020201c40110080e601801081354107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 107422850 1250 107421600 107421673
    0x6140409050717090d020714030f0d021006060e0a06030b040b03030d0e07050901050904020108040507120308040302010b0307081b03030730030b0d020d05030706050a0209030106090608 81
    0x204030030721030369018468039210108440001160a01441c1d402001c00304150019000d1031000754000030f250381555190700302580d50419403004246807000600c0140a5440b544202d8801d807500802d20484070044c075402031010a4840c40e0546400e074181c002c1d513400056810041201130b00c02c0d40109000d0700b00600c042880340e0702c80f00203403454002070749491080359103051800c050349042140c0401054192403a03d555890100003d929110040000e414030081304001020001d0034801c1001030800c440c0c50145201d402e0600402c8102c2c00c41c0c0071005580b0700014641c20b842e0000b50311046960101c0100b240881c1e4004503000382e074034180d01c02c2d05403106001250018400e0081324401100031426006030f61442c4071840704c550600103008050518000b4107070301e26144c441501000a40558140402d641c09290882c03442c8a103481c050040361402c0d00344000c00441e900100941f02044009210b607503110741802085600790b104214103544134128100561002100f1507074119039039141e4404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 107424100 1250 107422850 107422859
    0x10806010c05010905010c0509100206090d05130b04030501090b06030c0d061113081507210c0e061201030203010c02030c0318030307020312120a0506030a0b09010e0d02010911030a03050301061404 86
    0x25521f9102c40c840200344040395005c410f0510f41d00c104041a5148014413150812100783c5454145070303060f61b01008400107650083d15950a0032100816141505564450384e03410014001c103c1c40204035200c100407001b0034450302c2c0004081c20750007001130102040c1c04255480070b0007401c94614400040c94140304506265141302120790050a82801800001659001680012600410907818448580c14402e2000c0341703540400785114203c0380004402c040c2903000e40300b080007030361056806603000603021a00c0714000c01d810f040360b20981c0240f2440003c0300c01030303840b8003820103c80e410b54400d105c0404080c0d80c4403000400302c131000d41624a48081500424102500c000714030400920004003055800a01c207010ba50000020070100000c0c100f50b00020f4860390f40034030150100030f4800210b50301800a40c030500e203030b0607100c0494900c29039032403002c0e010b480a01001e84260b02c6038042007801e4100851490740043e0701d595043e156a0804800ba11807285040c07029405c00310504c030106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 107425350 1250 107424100 107424103
    0x50906011d042c0d050307030f090b011202090108010c0e01030b180123010c08160507050406090c021b0d02100207030204050c0c06090703020102030d0207080903010504030c030f050306010806010c05010905 90
    0x3c480e040c101014070084050300c03c0e04440f900c07494100d07107280e44070103012000268001c2c2a2500a8050316000c03c0c0000801006405007507180070103016100008000a650541000898021482610308a91a0380c0e194502800c0b10012120100410b600b000e64850070745c4254008150800001c00e07181503c40d0000e00144100d01c2604010142c080c0a40c5400d44400201c41a6281300e500b46410020740c002c0d82c0d00e02c0601c1c0141d040807034103062400c0c042c50411000340b01070707005403401600401940d039807001c01d0005010b841e0408809402081e20f01ea41c600380d96a200c0718200005486455140c640e81d00303000c0340a140c40d018500b103014808002c001650f0f140500c1c1c0c00355480ca24020f0700d80c05040360f40c50500344058218070285d400350b00d0410050360040192038908101150040c7c58400c2400c04280c144508100c00c1d03415480c2808120403d078012145a0302140030b592408010000010305403040e00c0305032903550101c0c6d1100c00142d80c641c42521300c00350441c800d500108200d070310341d9200e5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 107426600 1250 107425350 107425361
    0x9140604080a0f02130c0c030c1a150103060902030402210f01090c09050606090112020903010b030f070806060603040b1603090203030d0b010809032104050a02180718050906011d04 79
    0x84a40303407a240c41140c04d51900400a80014204510811031a000e481c40a0080482d21100400340b00820709a481403104a0700003400307800000054186030300c0c00800c1c00716004034840a01d03020918241010543c00c141e442664411903000d800c8041e040101101074507a10500c1012444a04c01c0241c5a143c2d8082030141d11075141c0700b5030101510a0a00700d20105584005245c1c9010b14030600c030210240c0e034040b50181400b4101c02005aa9402070404207014203140a079840d01032003503000660708008001504000c4440b824180c0d107682c0c88a07001c00070b45100682d006446820703003001040041c8035811020149020300d04000422801642c0401c0c11174200440e031640342603940f50000c4465800280090740003081c44c018510b0502d004000c0e9004541400001401c455000001401c2203010003006400680042c03070300506048200f003c000c042400c0380c0220002e038103203440480200354000101e0546000070b140c50311556610004403080d80044141c0c410340c6800780c80c0c00440da15540b184 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 107427850 1250 107426600 107426603
    0x61b0703080301080111030405061303032d0507030605010212030c040504090503090a050402131a1e0c010c02030f090906010c240b09090703031101061e03031107050109140604080a 79
    0x48540b00d40c903010b4903500b12a20300c1140000c6240c02c000700000504049481c0d0b030301c041c880842100319002410b080b0000d141c86000c0c100d0f050940060f0203800042021103482d00b01c50100c2c1407109135034840e011000e4647e0b61050501613404a0103903d510810b56028550010340c00c0040c1d800d00341c0c1d440c00502074410802c0143c44a400c00151280503087c1045550041c00061703c0561800f05035807c0c049940076980f08104159040d52403a02412541001700c503682c4595005110340182c1c0000806030039404080d20240940c82c0c0031220715024004001d48100e40a2407034514141019507003072182c240c02c020b1800b0f04100c1054409070010b00c03540314244121341040c10a95860217003940d200c081b61411002d0034800d080c0e94007040500c210001b940029680d052074203010780d46031000a54090695900442c01c114018101169a0000d0803150f40881e0b010f503980c411984030b40200305e40c58803058001c0c1400100d803c0424421840402c01c10540e04001401041c9002d44c2c8040b010b0130030100040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 107429100 1250 107427850 107427863
    0x3040e22081209010c0504050f0d0609050705010912050303070e3c091504200705060613151a0c060405150c03010b0403150b041a0103050106020f070302061b0703 71
    0x88030b0300c0150401e00740c00e42c0001c00900811101005400141c1a4001c61190f80e104030051481a003c40d11140c22081d04658031600c184400b540030304c0e0035911441a402a1800121940c000160240000702280c19807034000020318074603207800000b03c0d8040c009010183d00605840080808080e00b0240301404c2d11040c0800d030602d1900c1403200315402a4003031881d202e00340b600140121007241881d003900070a011980020107400b0818007408031000a08507103941e00c1c002c58800140400410765074403958084804010031141091404202c0303c071085025014806c41000717010703101c40c0b110403014900216070500d0030001c0c030421281c6060710490381150550091200c0c0f07003104641c000e136650402003442c0d0302410b40d070410624402a020701c0c44098418403106401c4031001c0c1e41a4030007140540064024040405001c40b07240c000e200401c055400246050b000069062002c40c07880d03540341009000d001c0b0380349107808201640d00b081d030000103e52405040502c11020030001c60004610920 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 107430350 1250 107429100 107429107
    0xf03070306182901090e060319050604060507030c080a09020a05100e03070f030f03030f0605042306010f1409060d0e07030302070b13030609230a02030c040c0203040e2208 75
    0x200e07561841c050b0320540b400d2443c4240705001d1680c210603404261004001070b1134042e40c0e08400070b407030200342d062030350082c039022010302d8144640483d9451150380030301c3c03041c0810b84035450224101c45080030351600148440c030100d070a82c0c000741c015005090004010f4000f1344e46480018811140d00d4400e04040703424440c10150b1030400b0b0200ca0020448500c00b48001441c0d40c4441519452071840202015950b846060060715183c0c0305101800d8044d00420405101000c003c1068102d0b900aa464140100001b04250711a0442d03a82d1101c080d95601442c44d181e100e203000300e40101081942c02042070284426a07480f602c168012807031920000c00c500b41c5541000303814186160810003500790100500c550303010300145000c04490303004800060000c054100003001103a900018002c0401510103040b2b1901d000801029090084081e214030035010010001219040910341c3d0140c7c00900c03003081040302c07907404103038001068039075440b8150100d00051460300c02d03440100d03110360011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 107431600 1250 107430350 107430371
    0x1205070902030c1314061c110d0203091006030c27090c05090f0106170603010207020301090b010617040f1106071205031014130b030a05031c0c050f0f0307030618 71
    0x1443d818000c202507215080d0301500754011520b28442c10201070040c0c4110354030300322400c0c02a400020108c074403a1034a5250302c000510000039520644649a40d44a52090704500700a18030500c005c0342d030b2020105400710700d000741109103613003002001911514407400c1c04030064618092210124450030703908e05000e05000c100300041c0c1c0701810610340405c050340140312458000c00742c1e20500200040c003240c0c55441a0009000e403044420094055081585103410405602a214142d400c0d9443d1410b0043c25007200030000d400441300030f07000c11b80109145020410780440721291360f1001d01140d1a002c002e44502c1c070342114000ea01d6001440000401007104540020740001c0c01d10304004084082010b0300203400902850782d4070030810b584151103e640c0e60200152408036034090160780d120844500465500d05a03294040d80b92410644000f03051803040048400812949013103504140e2034500c80440341d04014046070505950305404100303541c001c0710800034940c00c020003180d124102c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 107432850 1250 107431600 107431627
    0x504050105070c030e0108040f0f0605060f03011404060506040212040503090f0d02030604031808010e0a02030c0306190506040207080d02070c0501081506180604060908070b040e011205070902030c 86
    0x30060b004004801e0a90707000a51700c01050301c40e440c800d10b8082076989a41c10302c1c00500d84440c030020041c10058000c2c1040041c281c1040c3c7c803400f41251f0580d00540c040741814280e42404021240b84000d40002400094003544600d8004101030710050410b50315559015006034180d0b015a4954800f103130110f103a1800ea0f000200c407403070541c1c0d1141d070140264046a950303075003e0700080034004603030440d5403000b00240360b1000500c000d81c0240401410300d502e441e190343c0444000d900a0141d51642d21940c10001003440c0602c5100c640304c24040111003401001b010080d01403903029800304009004500d1103009001d6903482403100692f01d41e51840c00640740400e0358003082c1404814420005116646814100b08400c1518515900c1e0b1145c1c102424002101007000d80c46940403402081e01d9501c84006410b492892045440d519211610740000b40964481c40c039240c00f6103001440360401d904194a12a44164100c4100c281c0320407241050341c01c126500d600c0640d01040c2c49244100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 107434100 1250 107432850 107432861
    0xc03050d030204050a050d0f02041a090603030c070608040302120711010806031216050a0209010608040201170903041413090311121e09010c0b16110303190e030706020403050105040501 81
    0x9181411441c007860311000c170f4000c1d034141c45003511030070081c0804c4051106509034610826802042040290707244007a00305102d180e8449a406800751400003002420000116108800c0141c014143d1500d0150100d6805074010401c504501403000035019001d521809000e03502e1003040c0d4180b148409100041c07055030010700d11486540711024a801010303039102160b8400124000401c8801d83d0340c109030b0f00c2c008411070020b410032041d000014542c0c3d481140e1900441c403da0f02c1c660000c008000417034040c54195084213068008200420080450007124051240701034260818003071143c1d600012518034650541c0840d0400480c5a1058018011a100c446a800d112030400f000c0703600b001d20404401005c400100f40c00101007a5a0713003e4600e4a400030b40c403600c00704071860842042d48205143c100c03c0c1c00441e0b072600440303480c00b90110135030303200d16800301510601060002d803102c050310341c840d4204c07a18041041184042205800140040d40c0602d0002c100e40c10709103400e03801c556 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 107435350 1250 107434100 107434123
    0x20309100f02120402012f010b03010c02240a061e030302010f06031703040f050304080f07050a030b1b1621140301030809030c131b050307051209190c0305 68
    0x620401c004000b07071243c641030980090702131030000c041800286100c01d01e061046007001c3c20132100185143d0f0b000054100d541c3c60b40058000348030300c2320410016030342d41aa45548182e00b241c009aa070f2030745012107508641c044a050408111503076030700f0003e001c80c40c80c00c0402007040c0c0500f800340241502409200c468001c44441086024a1610394a200045a0308034545007440000841e0078008003011244002d5048030560b55507659608145648103a100b032001403502420400003031034644040004212600550310321210755078080075180c08044201050101310f010320038a01e0404413811060810351041d080041c03120b0500d5241c0c02000010081d0390301b040030b2400001a01c84080c1c05890440341e00c0040b46481c0c480860009090030080041940c0003051990344c1000e003121a080041100c040c040c814001780180321044405103c1100c2803070104908001300070100c074541d40ba46503c140c08038280c40140d0030140058080c00400481560b407018003003402e20a0110074001d800000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 107436600 1250 107435350 107435381
    0x5040f032709020319110301060e040507050d05040c03061d06090105070f11250e090d0f0f02011104060215010e011a07020102010902040e030c012d0c020a0602030910 73
    0x1c081c02061075500121500407001000d07000300100e070003d814105030303142c103100e000742c1440b00c4150728100c1101604240b00308800101418000710123803c25109450081d04036580fa40d1810300458044000f070480580112158a04580c2c00000304103244250034600c80003100f041d0000301600005807904001a1507401540d03d0300c0284140190405200188201c0508102d0030b5080305044085c1001d085402103682c02c821000d003001c0100303481405034291043d0b9260150551541058035035110149203004000c070340c0528800d00d81600a10811207201610b100101f11110140308002c0701e50001d50080015134044e10058135954400f48581d4003529410103048280d40c9024120400032042404424003020002038400c29a4400c0d00082400d82c2c01070000c2c00040300010007140d0340d80c065803261031503502e00052040ca10300c800081e40c0000140c1030041401c04d081c04400402841480020020345c824500202c001400d039002462040c0407210161410460070321052040c0c2d42e5041c04403016 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 107437850 1250 107436600 107436647
    0x20d0201050603060105150f03070e10110709020309030c011b0206091c120e030304050f0c030109030c0215040e0c040602010c0503010501050a0810080115050a050a0f0b0a021005040f03 81
    0x110f40780040c443e4110f41d0111002c0e0001d0300b0300031f103144880c4680e18108010b403d0010800c9400703038221407005180799043c3c03420f2181100c84001180d900d1120301e620521900040c0c410020004940c000d503410114a00540b403070304d40403214560849011030a44070020048001075001f00380c0510101d0f500944c0c620160449480315115021420fa20b80340c5c4070280071401406c10765104056000c400035800345401c0b280c1e241414240103a5418070b280041c0c0880c860000e65482900701030242c1c2907103d41c0341c2c8034140340508503420080c06400542044a4600050200103284c46a00f50841e014070b4410262030750703884c100314000b400e6070200d81d126024442e08100400035a60b2101c02c0300c4545080707107801440c0703844030f5076445401c210940c820032841d0f08204602034100c0d4090b106130110303001194285440d96956041c0006002e081c0b113400084005107404104100e492001041c100c291071055800c50041210030004030340d0182c50668500003800c0e01c10040681001191209c55286c04d140c106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 107439100 1250 107437850 107437861
    0x4050606030c04090f02040302090708090d030b03030a051b03070b0f06010c080f13050907020313081b090405010b060f040302031908090d030210060b0307080c0a022d120406020d020105 81
    0x44511552046038411591403464aa00145d154103840286074000d02040a5040110008118040554964019004d0811030900ca02d004c0d110f0103900315009005582864025070003690940c00108039422032481d002010f01c1a030000380002c0001610412403440345051817249001180e500900702e0381844503424440c00454005015100c000d14410101a07030b4242003991400c4c6c55696604c2941c01404003000e0003000c0742c0100107803480d5a00c007a00108600e5031896000e5039110340ca0036150245021540406460414410781603005000310700118001c5540b2001c12015401207090480c82c100114040c02145002d03c4860f0070460005040d119240803500c4100003481040f10701407090502e040039004041c021f0019410840501d00c0400c0181d9940c0b5409030300c0d50084440c00002004400015000c04e0007500740ca1941130640c0c001c0401c01d45041107070408503c05c61055580000420601d03045000400600c1c00c0d11b01c05012040c1c9443c46c2200c0680740c100098140c90030359040404115 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 107440350 1250 107439100 107439121
    0x70f090303020a02130b10030b0117040807031419020c010f0f0e060a1115220c1a0f0d090b01090e060a181b150c0302150916080c0405060603 62
    0x20f0380d072501215502c0100b5000b102c41401000a03400075504404c503003140c00a41c503019802010003180030f89507103000d0781c00849014002002200d00402d07004007841410003107803142185030064405c1984961400080800d40c00046245030340c0c1d80c005a00c41e0f1401040ca50313001a040c2100d80890410121600901c3d1026100151844015004403408103640880c0c80c0f00314810600406d1941c1aa04800000140602421000c440042d803140c100d23810340c61a0400d0401501d1225000440386e42040d0514001c080e60a080300200f55144c40c0034032051941051810080020105520000444400c00d15100e50b00c00307016480750f40014500114040b1554000c0f803542d601524030000000e00c1c402c0007030b01000802c0895005001c1d40744826130000400e10914049080c0c460784080000c0e10f40080c101100d000e0040000100140c01200c4851014500d412000b034101803901c041e24442066003010f810125481d81c08005a6030001c0f010507401d003428030856400c40001d43d0070624500e0f1486104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 107441600 1250 107440350 107440363
    0x3060c08010b0324060a090e060909030a12060e09060406050c0c070902071b08030c060f10060c020d05030315040506030109050d080a020d09060504110409020a050d0303140708070f09030302 83
    0x5013041e2440c1110341c0c0140c00e0f05070090b0404000301001d44483e40280018136081d07481c062890000880c10109009143c4520b100d0311800644005529001001100310340740011841c0c80842e19486d20700c00300722030040510300c91055580c0700c014140c505d4a410400c080e504083c00341d0002510400c80003240d03010106420040d6555143d003da82c980d400c0c0f6100d406452154507041c443c010b010303004208800013000a0010b044480100c0e03c2540310b4081c56156001c00703443703805104c00c0c0c0e100200055400307003070441c9800d40010145c030010f20032a01c075a41540e0084417002c213260401c404031801441c141c4202504040e040c1d0082210b0725440d40d45a55032400c3d944500309000308040001c1d0014401d03012115007482d40b900c18020700100b440d00c1c002600c01a2001c5846540c04000c0c4010f5003018030403032500d80d8005001d4405070340b811003803100b5880110015000c00d500e4590141c1010188801d15020b14002c1c0c2c0d0318800d038600082c0042c100d40306254010100142c1c490100042a1b000524 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 107442850 1250 107441600 107441611
    0x111c050d0903180b04030506071d0907020c040f050129030411150703020a02090f0603070302061e0426030304080904020a03020910090519120b0711070e0103060c08010b03 75
    0x81c07003016508040d034020700780d450b034480d0640b82000c001c1050807240000e03004031b0b84138100702c440b1500c60010079101d00340f801e8a00c8464400003136510303000e80342404c0c54542090703440c010741e081c4101050104058608083c0080041c0d0340325001003100c3e1031603494580d184516896011003080b91003d2036286440050005407450602c0310000c00203940710b8034807155042664000d99650703207252070040e495880002c1c00342d00c54842000001c4a20341c40100701c2c2d21421004001d0f1808a04540c02c002c901c0d000103030600c0c1000854071070103d13140305440c0204040c1c8a440d0090010031109540015194203118050155400070300a200c0007406107015520180800c40300542c4030036035200218028091658803d50040344d81200080301a0040c012401746c85081e522540101180c01d00400e040d541d038456009041c0d204081600441c00c0c3c80000c0e600898285010314981c444d20a031103140c490550812844256a8001002007094a03c01e008100c5154104100c0c658501b550a683c1030000800c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 107444100 1250 107442850 107442877
    0x4022107020a032c190905150d02011d0a0e0f061507030305040f020a060f030b01112107020d12030b030714060715050c07020f0a15110708030307111c05 67
    0x1440c1000c110000310f1404c00c94014041030425009a100d10011501c0c0d0703c90046100d280034045007840b01200b8000020540207007400032904a26801101c69521101d149241450032820204190741d80c0e5a1000040c84801d07609541d5040c00205200c0100001d0900c600ca24a4a6101c20a00301d43c10700b6590740640500300061180d031281000c00c811882d2040c002d601c2090503002041040e04600780700080100f80d6004c00210301c40000550346000b80564000a542c804c48130301420340c08003203190050541c0c0c03510040c2400c1042c0e0105407132524554084481d00b03810114200c5c1c9a134075120764021124120000d1142c1860142107a0001d02141d0701c031400b8201c00144401407148502000d4440809136808100c50b1519100409854218580807803084100c000c81241c140783c185051810f0354506080342807203600d0000706a4401c2c40002d130885090242c0c180001d40034400b0b1001d50b1080302a92140c66400c60300c184010b0400d040000c081038040455480c1124540d8807030705603401007aa20342c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 107445350 1250 107444100 107444147
    0xa020c0a030b0c0d06180207290c090f03030d06060206070302030103020d0303050403020a1527110103050601020a0b0406021b0319030203060f030a0507030309081b01050d090204022107020a03 84
    0x4c07410103040c141e00703c3c0c800000150040d0880900d540c1c02082058080d81031120410001c1d05081203031440d00d43c585034084031420100d14101d140000400503a180180316542d864954404070b41190000c0220b0004e813552802c1c00c01c5074540600003941c0c08045454110318542c1103a000070740d030031010400074080569030300c000b40400d4000c004015003260003180c61030501191200c180c5c00350919040c000300b81c020481c100c5030007400c0e90f8203080321568040750030f4140509620046009100007490301381184070b02849000170480704a40540201d00820015a40c0c1c11407564a60411076506220011030344200b00100c0100d14040100d20904200d103800341c1e403a02c1d03650000d4080850504215454001c01242c2c600f040400901142203a109445600d01107549000c0f15407607904440c041038201d00c1e200381026456104c0d900500d0340890025000445141ca60049800c81e0400744462070794040c1050043c00d0508504204d48d807008061005001000c899070340240740c1c81103a95544c04071803c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 107446600 1250 107445350 107445367
    0x304030c0e0a180501050402130e060f070c02221109030c21010212011502010c02070b071b080c01020115050d020904112e0c080406050304110a0b0a020c0a030b0c 71
    0x42c2c01941d005040301d02c0d85030b00c0e0340213820054002c050644089104d4075124440c2c581d44030003801210403c004107000b40240765154090328000a8000f0200c00401c001044c1000050790342c0281c00d0504000440d00c403509102c2c00102504035075078540c0640e010311703090048103041d0343c00143c1e0180014050780c0d2104032001c1e00601070000c0392401004c1007594000b15418402005071801241240c4d403050103407114050226080e8221038100d59401c2c01038001c51014482c0c400d4040040080c1d40c80b9092507441904845010305450000d03421904041d003120011142540c0e0901600700355008a440b5003001510b810f00085000c0300d5506c000b1b000301c0c2d120001409100c00002e1700002c000c070140c440001191204c80702640d03606405801188019402e034403201003031107850302d0340b0402d600c0141c2c189000d003800400da40316000180226a058071441c00e880356525040010300080807906101c035100c16401030041d06008101940c02c2c020b070f100360b00c20008101164000c541142d05034012030394402e43d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 107447850 1250 107446600 107446621
    0x10c08030c2d0a030501050f060702090c09060a030b03060f0708060d05010b1906080a020403080301030830090106080316060c09120308160f170a06032a080304030c0e 73
    0x1048400080d4a040041c0b949048859001003880c45041c1d5410005680c98004111003240001006c982240041c0034450050400144654001c0404002541042030714400243c2c3e550294081000180d26054039000a0904200303140e0000902c008210061410141c000d01c01c140c010300340c3e40300d200c100c000c50040c040300798420085868003420030b801d03200d002005903007000642c0c80b0b02d0001078003005c00955100014400d40302560347c403004092070f59282da140d0360f19031341000011603510301140d42d801c070243d04004030280f0b02e005800041c1459191104410342165401d61010507203400400042d01012000e00e0042502039101070005200039030208101c8120754150041404129120200c60905422243c000e02c00c9140c1103a120940d106003500b03c9200700c85480c1c010106280c003609141140000b40320030351120541400240403680d035207a01e402104605040042d140390583d6142208407100722910180042500440c5040d21f07554404240c400e60f4172504a102100d01d000c01d12200c0d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 107449100 1250 107447850 107447887
    0x50304061e170c04050303030906010614040e0a0f0f0510051002010c02062d0702010e070603060e07030e01020c01020d05060f0103050402030304060c0501060b0403080903010501050a120b040501090210090311010c08030c 96
    0x170b015040702c0d140d1034407c903550307501e110070300400011840304030340d034801c44130031104541c00d903086800000707029103454129402410b001014120341e00d40310160010050500d1180a1160500a03a4410003a15001c2840200690b0300e20319411a41030000903401c080c6c00040003600084034090a100c43c2e01d404c0c50604c01c014001060304448602d0609001d0002d0381500f00040621100d401d52b00c2d000d0f500c3c00150200c07462403284019229603078000409860203a4001c0016000c0b410000d403811502090340c5007284d000856079001542e5a03402d0101c5404c10040c1581100b60a00b002c110904064001941d01e01a030711800c030070418034007641c01c1000b000390000402040428013460300c0c0c40d22842d107c1995080500d50a0081d03280800005082c07a0249040085409c40c040e51241400310351030705019240010400c0d6540e40d203500c0e010006840380d49040b802000740e50795440c8024294a000002c0c80e90a400380e40c1040617004442010554540803640c22103045c0541070354503451184087d10071709 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 107450350 1250 107449100 107449109
    0xb04050904051c0c0b01150f0e04060801020a02150f01051c0519150c030501060f0f21020c1603120e01021609050a0e01061206091509050304061e170c04 67
    0xa2802d8032500f111a04410744000c9030388201c0a0318076980c0c070740408882c2a00b0303246840700028407200030202c07c81e00840d04c0e510a000044c1000c0f43c2c2c580c440310041e0983e4000155580144e000000075004408810646034000041071105841545001b00148105c8072108403100105141088482081810050103c0e0030b03110313021021183d2a54180b40340da00c0c550b464100c0700300741003210301000d540c8280300c0c2906903100c84c0c441c00f032503031307441c2e5407c40d00036103010841000c1c01040b092090740c071a0020340800114440351009640c0783e0740c601402e820940c1d1001c003801345540309041407000a242c481c2e220240c044624045490ba110780c00100c0c41c2c010f1a920035240750420401c0032a01ca0180d40082d03200700d0341500d0a005414407000d006080311100c1c81081110328400e1060380018039241c0103015079500400107076011403071984160080301c0800c1c0c030444455100041c00c01565400000e03801c03880540070b0100d01c41c0200010064406d41000301600e1540000ca0300140c6d03101c03010701c103070380161 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 107451600 1250 107450350 107450383
    0x6030b06040f091b0201090302060c1e040906090b03120a05030408041701090b07020a0c260712110a050d0209040201110312040606051c060b0a090c030519060b0405090405 75
    0x42e503980e01c02c1030003040c00c001c90301080c0c00914180d4014030300501031510655031540c014801c40c2d50700d00c0070040383e4120200320107001c0d040c4888080800b80980180c0050300c40103000007041ca207400071001c111048040a140240c1081502c444a06002403e5400c0c0c81c0050800755600e58551034408d290b44076503000a2900700310a051605040d00c150302c60000b042c41100300180342e89851b9002e90f9900b941400060070810307118410f029500400d801c1040c8144c0b401c07200c40300d8001d41840d40781405025044072003500c403000d07040820b00a4041040c15400019604401010b04080210f0019001001c2c0640940c00740000314045920800b11078000995200a07680c581102d8520384801500558007a2442070a144011503185402428100442c91801c800340c0d0280b959611503000e0a41d003103400358040c5110100041c330300754502640004545030741d80020146005048000800c64050048400c03a00c4c0c40d1081c8058000380c02180d00361141101d040c1d2440e600c0346030040c540428690022400b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 107452850 1250 107451600 107451629
    0x3020706090b042a1703040801140406050c18010f02070306150f0806060306070c0c08071512060501020304051507060207050102031801020f0a0c1b080309040e03120106030b0604 78
    0x1e102101841501440c07081035000c0f02607413016041e071000038640d540300440e0700d181e91007048000d5644180301c203003400210540341816541d0748110308442030084090311040e00382003000108009845000d520401d00c4203a07074203040601e550039140403009005a41400034442c02d21107a94020810030004652100086c002c0f22481540d1000c1000301d0b00c035403441c0912580d804640b6006c00308810b44a1030000d40207204554448034200e80c44035040005943d071100f1103001081440c4140116000f40c018400304110b20451444010070030040d4809545025182c41810b002c2682e01008490441e00c04540d030415000b07001c64004200c0c4566440100341c2c2e0710000321803003000710640203140708120b06640900030003071038480b5034240d1043d400b4800207210b040000440003801150215400380c05000c034402800761000300640f084145400c514019403011801048031320b0903014503003401900002031410000c1e07802d40c075004e60134180560b005040e107440e07490b1810b40303c440c142e40040030038021000d103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 107454100 1250 107452850 107452853
    0x512010501141225020307170304170406020303060907021c0302030703151205070501080f0a0519050403020c031b010804150e07060509011706061603030e030c010b10080705190302070609 82
    0x4c400100d90880804ca0750800701c21520b5a002005071407145070031003070346c079080c0743e14031600c485c0741c1e10081040300c1840e4403880045042c01560098809402e040e00215582d0a02404001d19808002c001c10b003154000380d4030312840300240c101404a01d419040c05030b225114141c058010305400e0706121040014100001140e1510482203102d044c0124151030400391900011584c20030100c8140003a5044000811440b0185a0081d54030001080b04c0c070040d0304480c481041a628181c8090b001030707020016809031860184542c002c10030381301015988400c0b1450000c4c100c550001c101401c1013080c1c12004003410a1908401002e41d00759054910007a100c1c43d010340150040e2902034002a5901c0c08841a003182d070303007420f015007002890281040d82d00100311260702d0801c0701c11010107440d5051114001c0007000035080040703030800086410050340e400d0000811408040c141002412024449010303001811500071540140d101d00c20780ca4004410b034082d2045074002400ea40c03900f00c1140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 107455350 1250 107454100 107454121
    0x40c05040e0c0a0c15060302060301120c0602031e0d090813061413090f060906091d15010e09030c03120106030f0b01050f07020406050315061005120105011412 70
    0x603030340c8894981030242c0761010101d6550040c0780749007010078100d060003c0481c0390741110404922100901155060316580801c0711034001b0781c09500c1c1c00314401c00000030010301c4010000500413901c01181040d0b8242a840d4110011010700c0303103140700008001c002e1822035048844800e401c80c1d542640c0f86c0380c115017100780d246c4174031445000644201076840100922030840c0c002410105482885d141090000e078000c00601c0c1c0011041541c80750009034100107406070400070080c03000300003801903240c0818800c1c0304040e080003202d604000e0085400b4501042c0883c15203513084210714850341c4181605145104454a01c1824070010501c0b407900c40341c405010341a0746542c0d0b028402720036040c1221083d40c0c04040080c2c00f1400900c04160b4112215000e00f02c1e1030700040001c20442ea0341d0021074288580b5840c40140803084008008090410060840c1d2221480c5070442c40c2c411070311102600d1160601a40741004103500c2d1140d00d0001c0d8206442101240e4514078031a400e0034903450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 107456600 1250 107455350 107455357
    0x1150e090d030b0108010e07050c06041103070506091c050304030b041b050306040201020a060b01140c0a03030b01111009031709151806161103030702010203010906050d0807020103050a0b040c05 85
    0x1800c152080c0303003258650500c00d001d2080404010384030140e0366400c010450260003401401c24080010500144000050030801c541c019405961540014a101030a26040407115008580a03c40800081404d40c86881c000d1131083e14640c0088524911407a0182c1103225a61001d0600f400d00414002030101910302c001d4554071400c880c3c8902c035543c0090503180c5504030340207070241c0c0258960301c01040c40b80d085003005840525052401d0581490515030b180c0181c03042c07040c95030008640c8410941c042c81a0140340d50242069812181442500c80e6941e56002c0451440d07610b480b00441054017a1010a650b42c8484071007120368604003003039503903910314900e000c080081c010001ca1a84038100f61482a928521000303800309640d00511200c81c10908510b06082002d6407011392a40ca10620103917000c0c1407103900250743d07545095100800d44089404c43c910a0f10201c0441c00010f030301108840340640d080c00d001c10b1075910b2450076002010384501558001c0d041500d41c580e07440c1d01c08003d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 107457850 1250 107456600 107456611
    0x10801060e060f01090b071505060a080a410105090a170c1615030605040e07032301020304080406022b03053610090f030c0507030804180e0d1b0501150e 67
    0x1c111940e50402003041e11051442a40010b40140301d0003000300d81c8000c1651550101e40c0020030980d90700c1d10807520000800006004013b01c0c58071401c2d602142030085941001301400100036180c4141c80f1400c00203401d1941401443c00050760040d00001070242001d091604035084901315070795800880c101207039001c6840040d1805401260030f04e8a44161461040740340300404520342199200c08456049401140d40c140d100b404036049090240010340c880d51051104c01d880e0f500c5d1240181c9040a503481041c0210b45658880d0300440d160012080c4969440c580481d50741c0302d0031548090f038884042104840c0c400700784c1e000c8026240d00c2d0b14049480259045601c610f0003511240300315400094002d003107014400390080800d01c02c0310440013050140302600c0515640c1d98070a00c040e805540494200044d406880000c00c042c0c0c404c0307113203041c1d070007015000100006800518000b000c0b125131040710340d619185018420309500645040b03101c031402d85c079400c0d02c51201070002c072001c070b85 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 107459100 1250 107457850 107457893
    0x51207021005073209190801020c0a23030706050a0e070e2703030612030d050f060f0306090c04020c010b0d05151003030f05071e0b04050105010801060e060f01090b07 73
    0x51a126030742098031048900c100c2c1c0810500307041a4030f080011b200f20208038401d82c81c04040000c50555000e10042116540d81c60081c138803850306180201096001e501e200401041d1f9602c1800f005801004036a103407644502c0000b42039490b1840702c0020410514540090312600d00086032a1014003189801102c08000132080b01e5421544030031102074a6107866803030340052001c02c0070740c140800c8034511001507005480c18500801400c81c2220740841d03202c0c021004902c01d02a59041015800038040b1040e0302506035031504460381561226007007016406268000f60400258101703503ca0703544454014280c0080d00c40c0d03802c0860352050b5890b00320401c8503940340841e50541640494408903907264407003c45032100700705c041da032540019000365068079100f05280101c43d030115181c4601d0b0700c05d07a078685481c1090306040e4211139050700020103580c9040320510540f030449040d0380e03011a04641050802c1e00c41c0004a0310f0f10b60940c002003511101243d40d10403c009111000c0c0c40349030500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 107460350 1250 107459100 107459147
    0x5060f01080c010c0b094207020c1e0301020c03032410030c031b02030d0f0501080c13020c16180605060702011b1e0605090a0305120702100507 63
    0x51510b4480c0b2480d401c10303002c00d9041d101540003030210030607194480040d0055650b107900e1203203c1c21024070740704800f99094500c1c0700c0c184444149014410f41c00564072180000c2842c01e20300295549200301031991064440d25030100305150340e4030325012454000b6000395118441c2070f20540d5039800c160760119104000b4100c074500320909410118814600614052000411460903001014104040c208154441800d581142040b40c0501001200380e030042d60348410411081048078954200c00c05c00c2420240100542d4030f00140e078024100c402c40c0c0300041c07034076071a000c03c0c000d200d0741e8421b215034004c2c041d04901d00080321142c1001c644400019209240036002c074101265500d01400d588034a040c001c08016502ca0100f0003c0303804440302c4030786e981015485520381c007000c40039558038100e0803e030b0f00410032000740510380e001418080142106505a9030103031290213030006d4400209010000120454401c10512240320fa224100304124105400020708540301000300465000c0c105 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 107461600 1250 107460350 107460359
    0x2404030c0e040308160e0303070305040311090103050c010e01020309090a0b0108070c0c09020304060207240f0b09010501050319110703090618050f030f120c060f13020103091e05060f01 81
    0x707484144a281c0c541c1d603080099a814642d1564038040f1000c034001c0004070300030b000c0d440e103040009150140c02a1034041d220ae1440c80c100988956402441d80141c1c030306401040050000204000d5018090900010703005200b80101d185014181c00c243d0310100040501c0540340803036018220303064086c1c1e10510f0650368454180d4030032805850003016040450001c021040300740e805150007a01c10703100940381590548510082c400d042202c3d101c0b50782004204030500c43c8610480c414a8407203841441400c0212000680c4e9000501c17515051250000c0000e4181042c0b00691a0184030b004c005c012644202040c000c060300031303070001c90118000c0240491054044c4512010009807500c504861034140b2050100c50b50007030303070600d03010300c50808406507080d004d0045407695020b640c41d694a4205a004241c940300002c0e20900c4400031042c20f02032503041480041a03400d0702030801050741e048519040002c82110012107829141d2203015108001c80030551a0240901c010300c05480d0345c94 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 107462850 1250 107461600 107461619
    0xf142a03031003030e0a0302060a021c180e06120703060902180906150a1701051504050f04080708070f03050a17070e040e210a0801061704060b2404030c 67
    0x161281030b080c0001c41030400009100d50303100d180d160005003891007280ea8907400f2886503007017184081b003d030704000000c00c40700d2090110013440761058030380450352038200e11010308403003103e01405130880c44240002e8080c1c3c0f10b16400302d580d8900c403001c45015958034100000185001c00d412881044030418010700440c400040d81c0c05425054050405074481e0480b03803513808100b0140d59003003140b0140006d0324440403020421a840e0700300002c0f40c1841c0c40c0c0c484149240781c04102906c264905800d1080407560800c801e54017582c4503c0c415551111400c20340d06600643d0002000e404001d013150701050f0f4000003034030385156544c07221040518004a080010300301260740341c00003000701c19002c01d9480c1640040602c00403140540e000300108042413006102c1c51021800341c84000155620b41e10742c80528507004001600e4188170308000c00004088062028202804686e01e800d550b1819941d00b0450003c01102102c2c80c03104c2c1000881c90804682003440146e8090081040c00900b1116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 107464100 1250 107462850 107462857
    0x5120f120f040603050a11040617010b0f0306010c03020703050a03050a0e031506060904020409060803040f06030506010503060d05010b04060303120c0206010803220b0f0d0c030e0d0f142a03 83
    0x45251400b420241010011002024000d000c400102d8540b0b9074401e4000308880100f000d0101c035030311050a84500d20701901441c4043c0e02c07560288404110300390600d0f00304010f617904080e003443e00300941c0140e814124601561608094624013803010840209500400140500c404540354403552103100401c168940c40c0b505240314602a4020004425241010080c900c11200820050400d500e170050141186d4039600300a0082e0300000b414022600100e0b030307000080c40145800d11061400ca00028503900028081c50b0041600740a04810030500f0f40214410483c054070401c02c4a6072800c00038094041402283d040c14503040f007501b400fa00c089106416912020000c51410510010f440702d00800c01e41c803041c8603496914042107100c480401802c2400c0d1070301c0d40d592a00380a0301080d040b5414400030714241854043e0001c6542e1010914502030107243c10646804081d080060300c00980f0501900300032080080d4401d4121000100d1442c910000e500700d41081810400207541c912 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 107465350 1250 107464100 107464117
    0x12030a09060f0513030803090c1c150f0c090510020307030516050f0a06051609051804051f020d11040e1801020d140718050d03031505120f12 62
    0x40c0540014000e050080000100b20360051030100c0c42c200c1804901c0c0d503080d082c1d41040350b45a50000900c5a140820801008059800c6420302d800352100044020341010040c001410074600d0340c40c020780400e40e6844843c02d117825038824058520b85440081c8940c4140c000e007445241a4114003481b2440002640c40c1a40d05880b01413600c070b494442d2581b021480801210300348104501d0496a08ac00c0c86040b100501c2868042050b01340340a402011018090804082080640c0100700320b1b950254010030317010100d07280064030f807a1030034042c1c1003101c902420744200c0340850b00540744440e55030041036101684081007200440c10444d0407160701c11031040a480c83c000102156001180150805800300703524001450511100c2c002000d1b15803040c2c0c010341072030629081010440c0c002180c80300300640d600c1c0310b94505040100227009405007010203010580c0e1021061400007240b03100e58080d01c402491400c81500a0500307a0b51240c4e5044245900c1c01141c01020300300c4103810940d240707207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 107466600 1250 107465350 107465357
    0x2b290c03010b0f090d020a060206040c080d0806100e030d0207030512030108030403140f0610051306050312160510060f1203090306050a0b0d0c050117060a0303030924060512030a 78
    0x4520f404407001180c12851100e5480701c0c15007140300069482c9124100107080301d4000d45060300d031905010034001c020ba4040c40007a001414a03454107540807880300d902c040d04880c401030410602e00100c7d0f01a4403202400d4140c0b040c109000c002a40004100007204d00ca08110b640340c83e4140e24009450000388528031480d48180414000681e60003000005545d141e021070354a6414180c4091529800f9210480c8a0304d242c0e0081c0007604107aa002d9070038082d14042801a1132401010940e03409082000c0c2821913008104407024a6422481d040390070f40105c1220000d03001101c01d14014012845520b0750f82506000000f85150100c124004140d0540c58054409180d521400060712005111400c8980d9444000a45544e1500100c3c4c0c140e00814011032401d00384800900f11358140040c414848c44514100003070307555016006802d03640d15248c0812940240e15000e003101451030444100b82c1e01400034448a1002d59004100712401115041c044440120125490388210500a4000b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 107467850 1250 107466600 107466607
    0x160309050604121106010b030114090f04060e0a08040902121003050c0d11060d0b01021002070b01030206070f02060f070c0b0703021e2401030209070e2b290c03010b 72
    0x400c8003e1201c005501c42e81c03c0440b501040c004003d070401c84240c00c584140c013000b000612099081c06c1c1d2540c00c3c048143c0c1c40400034140b0f0040a1884000144001c0c42c054a070854420100824401a4013680d407020f422030301d50361504840760203900503107240c1d50025403000c0007031816424420404100d1390090040e04805e51800f00380807a00e040d000041e80c006000682c00c80c3c01d51644001400280c854460005000794988002410900c0f541c84615050340140800300104400146090440398101d0b21942e6910072440c080c0d0f0990a800b50180d032065021840c1d40280390307030200610303449108507510b404440e1907030f02d00100c6018402c80640107901120081021aa03005039041003203000c031041b1100750411100c5190045d2100c0010420020141e0040045041c1294025000720160404808030051040031a9120300c0703158550300300c581800c80c10200c1502442114034501e4000c00d401354442600c1c0c818506084004440a40807010b02d000144614040000d40b81601c07851080c5614 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 107469100 1250 107467850 107467853
    0xf0301380d060f2402030306010f05090d02030618060a06060503060415080d050c061303050f070305070c0b030402010f030b03060105041a06040303020c01080109020405030a150e0f0303160309050604 87
    0x16030040588800d03015940c075004540d00c1c12280c5800010420010715043c2401c844c401078100401d0031a8440a544c0b09005005043e038018981c1601c01c1c41c04d24006860301c8200300000c40c0b1945105002c0d400d4000c490510952901c080441d0f43c02c560b88000f01c400b19110400d10800700c411a2203542c0008100b0300c0440d09524050300034562134042407070703c0c19400303031100f485c0c0d414604040d0f1070201107540014902200d6400780002507201e04009481c40d03001030b05803009851445004951a039281002600500701806941510f610913002400c90000503140d440c5c0d45010f5000f40c80c181d012030580320040f03103c180329005502e81035030701a019103034a92030314040c44080d150400140c4190103211281c1142a00c80001610040d1300036030040220300780c030380c0014101e0030041c2c1041030f00d00e004000c248015100010f10300c031907590000c810794109074001c40503002440e03424580b810b1401200e0200c03211040000285018205103401d00c040042204000c0c3c0c101c800d03040b8000c1c403503041100000c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 107470350 1250 107469100 107469209
    0x7080f10050402041e0209040c0c08090103090503040906080706030e06270708120306010318170901050c010f0e010c0302130902180306070305091c1d01020309060f0301 74
    0x3500a440680003240c00d070115031240c03030390a07070a0b04017a880c10390220340491a464240507034003c1d40f4190500640e0740c0b409441d0401240b02c1c14580c6410316490350008400c004040044078020411140704200281e2034210306901c80c6078a01c90000040d08000c050041e10b880482c505001e0b1140342c0400e100a038003400084e00703c01c851a2404e8a40c055401d0000300458244a046005000b0070743e02c03540c0707150000024044a52900400d640740c0401103200c00010454a60079090f410b4940d40c0035141e070340e0b48004030740500c02c0041c912060b50130b000185100f0030507600401d80d0103900100038011008522011003c0703010710300303d40c3c5032200201406c0180002c2d581c0104130b28602c020400c52450608404203180207015201e1303100003035032102044542c01080c4048001c2c100300c502c103100e540a43d404010620803e80d040244485429903501c0b1550303008008580100d03e02514a9440e81210a44c0300400d42003446100d070300c81031407005454000301001c1501c0304000200c401000c84219141c042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 107471600 1250 107470350 107470361
    0x4170c0c040b060f131d0105060f0327011a0103231003140610140109060f0c02040f1a04091a07030f061502010c0216061407060c0903030207080f10 65
    0x10360010f03c100b01c501100036500005292003c040014901d645140500810030f0202410ba20b0070460407440040c000c86d5038140c200c40c450070000c4601380d140d44444e980b01103454400d070301100a803204134000b00445107042d0420b20105012501d5422280850f10041d41682d0702e644410b107110441c526042c00e00b080840500e5004003801c0d0313494015a480350f903141645585040c10142c00e50091041100104038084100060070f88081c19482000b080c0001030110441d0380203850034072501c0d5020340350091043d12001d00041e0014000d03c400e0050f4460000104040e0a1503401d07000410300200290505d8003810b84040e80c4240c050100d1032850424446403440900350408041e2030700e20b010307079041560050740040c0007105800103018615440190854403c1c0f0ba80000b903410507104246241c0302210300340f048402d54200000b98100303948500e0031034400d0620003445140361415100080d64002d54001c180ca10076000c80d0102e6032a090360b42d80e20115080ca4003a180d0200b080114500d1198010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 107472850 1250 107471600 107471621
    0x302090301060906030212030702060d0506040e010c0e0102151003060509240f280203060f190e0105060304050c0f0f270a02041202042408030304170c0c04 68
    0x5081424000000382075410b940d000c03918403515540c0c10b10030b510380188040724010b9242c00862402a540e80414140d025858006503900d03640c00000380d0f140c0751a08802c2403c2c102000030408a040f8040c040d10400724200031500510404070540201d810820300c260140d01071103006003045145594050207040024036084040c0200034420b8030590545082c2154140300580000e00d515015500d02038000008200c02034800007021503c080711000341e204090040058009030340c0e80d030b802002c04d06004a0a951a0704144600c511a03110141c5210080030f0380d011400c8600540d80e60000c001d4140400d81d0003074101d412000c0c0740f04182c43e00801801030a4005403110000c188801c0c0054104220041c403140c00c552a12102d440da46004ea041307550150343c848086003424103007017102c002440f0080c0022702071a5100091811100203407402801c1c05142e0716500700e1a0b440310106a22500160b400312a060340380c0000e92820110701c01610a404190b0004004c4030310688100005088150403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 107474100 1250 107472850 107472857
    0x40c0f2304090f0c030308010305010f0c05090f04060b0c100509010207030210090201090b040b0a0201050106021f1112042301090f0326010b04050307150503040326130201030c0f0905010f 82
    0x10100c0001e254131502001140a0386a8604543c0f550400500395205200450440d524103024160310b03030381060681d05140d030140e031104400b6880001040c01007a05d83c000c002043c1020500c28004800000c903030500412403081406035031110340c1c14900341d002d290350040240c3c01c000d00d1034400817541d50180310024014500034103e641d8030f049581c150b40c041e410a00d540d4a000072004141c40e02401018010101c1c0d00c02400c42d440c524000d42c60740d400e12030b40b00d0589529040e40702c1840c007110080d941000c10915414005041624010324210034018103030000d540706c1e0a854100305410b110b4810704030380000c01c1191100c070b0351751300700e9842c0b43e00c0c201410940700703101903180c885040185a03400380600300a05a625818401054900b2180d13038010311000e4175440300b00c001d2541c00760503290010352505001c020b070480c4100c44ca095401c040300580c6028420002c100061002c2024800d8440c004c3c0c0302044051034448c0110341c10080d40250700c000c01d240039020051540b28540c0e01201b00e03100c0c034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 107475350 1250 107474100 107474123
    0x120f0706020d0212010303020c030f071a0c16051804020604050609031501030303050105150408030a0c231005090c010807050a11060405030304050106150801052403040c0f230409 78
    0x10b20031400c9800c020000a1100c4585005004164040054003020141100145005880d00300b00310359032501070082412606041c0c120101c0a100d40c001c3d5103001032580252900821129107030349e49411a442024414402050780d8094501180c00c05809240c020b07200a01c0d0904210601071a5401540081d40512400d064102c50a20320030007240079610940e408141da516002c10460140003104181c4000d210810003000b15200c00070440d07200303841a09022400c4100b90078214841887d420001a0a40b10444c0c0c0129102001c40c0b00300590641c0c0c0000c01c0107803034415007150344042d0300312460f000c00c1c5550b000c613803110b000e0303406490018058607102e880002e802c40b5040c140001594210b60643c804414801005801e00030900501030030002241c8034601214010100706042c8030f0740c0d02030380c052400040040c0100c040b42c44440214403800399641081e1410300741c40800d80c4111000e2085214010800030b4001401800b410082c10100366031520344420440204003445049030a0300401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 107476600 1250 107475350 107475367
    0x60b01051c2c0606041b0504140a03021e03100207020607020d020f03120408120c1c120c08041506061205101203020d03140f070f09050307080d11120f070602 69
    0x700d41964451695003e0034103418040140400c1c0ca1151b002885204810120041d070641d10500381e0f070444442d00b280c3c51110180e2004903907409040d402c084e4010013000d84259040410880000b00c1400c2a0f08a940040b484401c0004a0007070810081d8801c0041100401600c0c02c070008444180c00180091440d07400000000e285c21544950b400548202107170800c0250003e10142d1414408800301500d401e4840c1401c903240c804002d04060949401d0303800315207003441904915042c0040300f204129014000c54058100d0408541c11901e03e41c2d07100c080102d40d03000d07000d070a08a4ac0f00342c42d40c0703004140c140411005820300038030180369000e640300c0c001021181a4030600d40640290050104029925030080030b0340c100208101d8400519004c0c8001c40c0c032800c0450fa440f100600d0142d64030b0444500480d0300501c40c0e80b0450b8584640784001c549400003103000f400940071034072113021612803109071545032050220b03c3c1410000500c150300d2000c10b00001800540e03c104ca0040c0740c40d0f0030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 107477850 1250 107476600 107476661
    0xd0507031d07050a0f1a031f030c0311040903080a020901050705030d05010608010b0909060d11030d08010f091109010c0c0b070303050103140a0f11011b0f060b01051c 73
    0x32030441c002540c440c1e4000c02050410407100310240510085059000c1d00f458400e03680c51031150030a5121040010000340b10031102201102010346030000d810406507281001d1403421001c1c0001d41d0107030303c411010542031070948640e00180354107895003e2207584201c12a00290400c2c0c0d0303400c1c1440400c000140014030280700500d02800030302d0b0700244650400c00b0080c64280140c010201e915020000c004032941d0301f00e281c5031301980464107480c404040d46000e40031304000721890fa4040c49604030303001c0a80d130060001410380d40f146140001180da1501e4180565a80520101703244004011009540d40310303540441150740a0503074a42c000d6920030040e140d1380c0c030066040d00007960340d200500800c03060b9100c0e07807000484000180310a00303842c0c440c2102c003a04648000c06411a21a000d1400d9000d882154035011008120903542100ad0030108000701d04003c00702d0f821807805140c8100f540c022016510100705400030030403500b2500c050400146a082e041414408078814030700030300b071030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 107479100 1250 107477850 107477891
    0x5160b09031c060e09030705120906090402070614100509010b03070201060f0b03011d0702030913060b0a031b0816030903030605100f03050c03060f060d0e0109050f0c010c02060d050703 81
    0x1800b4400030703425182107032800002201a140d001d46400420201d40440d40003d082103c1040f80c000c001e50b120340303041c0059400d2140050707a80d0058000320b0700b1000d205070340d403003900d5003110b901c410711960b901c004801c0c00d54a49401201d50000340f140043c8148000e92028640c8403800f800001046d0382c03a901c0c448060b044543c40101c0e091320010060225042c00d000c0c0b000c261080c0880d51050f03040c48200691203000340c408160103802d03054401403201070180c2020340288094620243c4d5051190b0001b0042c005144154140400e014151a000c912480c4824031070b8089001031010207210b501c0860141c110315005408041e19000d0200c0d040d982d9800101301c204c550b868240002c0d105001c05010388200421420546805004000c801d4442d940d000140e404e0881303900c0d60710782a90110400904851582c0c0286610b44001c510801c000015420070b901900c0f01225107040807103004445a45804900a402260610a00c414034580e0b41256410000398200810b028020703101e504404e41 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 107480350 1250 107479100 107479147
    0xf0303070c0303170106081801060b0c150609070903020907030f05010b0307080708070f03091407060507020a0b090d02012d081009050c090d020a0f030605100605160b0903 75
    0x3501c11404008043d00200361102c4c01c2280c014107444ea40c94404090841c5074000c1c201e6107001200305000c0480300081d031040010b010a25040340c1c54010104085640d5804151031000303140c007640100301c440c64002002440360707100340d82e0515040c2c11942030194038240074120310b06140d1540d00c0307410f2140301c9000b60790180c00540d540a84030300d450200189066009400346003400410010700040c5035020211032400340c61400d0200300107000d860001d1250051081c1070780140034060001c100ca6a20000070601e00380205d441518864503040d8444540c450804503aa000c82070302c4070940154014000c0445101c8158041511a0721800142907000d40e200b41d45400101080200000841d44400ca94003501e80c400c010003480c41c2012600240b445501b40651084505400310011560741000802c050035000c1702c0c0002242e900e1420030081c0c60144c442503020003030450042049881041030f2060000c01c444490103180c2d051700c1d2811003d8001d00000100e020030444041d0b00b0405240046000c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 107481600 1250 107480350 107480363
    0x1202040f050d030c050d0c170705150c1c02040f05150307030f0b030303040f02010f020a020616140f03091008040b1501050d0e210c0304180219020a020a060305060d030c020f030307 79
    0x81250311f49a601c20081e20742c0710395100ea090102c080481d02c005404032050341d4251102c651030700c50003451090390146151201c581543700c101d482040300c01d500600229035041c60fa01c0d0a0a4490081056454102c980c144c20b0700e0090002038104c0c0d01c2500b04000078a05001c00082041c210701c082801d40d03004480c00d56120260b955070030115603209440400541161010b4230600c4a0307940007a0440c81303103c10b6103142c188224100c0c018882c00c0600001444054000c45d10b140140b503540c2c540344d400100520384103024020070b0842440c010b804039489954040c980202d103650b4140e4240c10007030211500e0f81000418083c20002c44000d110341c0300307582c107802c00404aa031900000411f01d20420342603c0e4000500b032101880003a4000b00b501c0940703400c802642943d030728101c2954000e0040d0007030009407420001e6417031715458000c200000441d001344c40c0b2401d8251500750540584000f6a085600900305040640110344a0410442c8142c07009000f121064610f500081c41d41c0c0100800f41d0f041d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 107482850 1250 107481600 107481617
    0x40e01050708090f030d05041a100303020609030f070305070f080409090c050a0e040b0714120103050d0305040201020d03090f08040b03160c0503090907020a050109050c011202040f050d030c050d 85
    0x3542100005a00820403c02014980c99800c806601d0f4003c15800c2c40190f0380301d0011400f0402959007440000030300703808000462620030b00741c400c5042603102c168058000e910200c1c08560003c8202c61014200d02d0f00545061040d41c3c0803039450307104a50507621108811414400605004010002020b6030480032840b41e20074109204600c25a81c000d61103840c0c1107008000d06000e503420241d04c00d0300408002c0b415500c9070f40a551300761703548101c0000040001803411039a068034004606803070140c0200c0d03084840e60a400d90803940c003a607000c0d001da0300595540c15010f1080d0030882800340308003144803480016540d200c01c590001d812010742040088108840f9005005460518000c42d20b040d20011034283c492035102d1044003101c40c043e07400341001483d15402000311620259000008128088450508944844001041900241c808410307114a0309040c004c0c1ca09a41c00496403030511850841001048100030408403f448100c00b1054041001482920f0030322809485189a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 107484100 1250 107482850 107482861
    0x90506160207140306180a0506010b070b06010e090a110c03030108070e0906041a0403090b0a09080c0109050310020a02070506070809010e0913020108040501180c03020909070b0f0f0702040e0105 85
    0x3402d030310380c106800d0f202d140003114880da540040c0d00354002d01c0d08a0044a1541c10421b00740c107004103400081d14038402c14000181c2d14000e1001072040c0341c004c0042d8012611040c0044404441082140f03600002c004041288801c207640320b101c6081c18129150301c0c0c00d1030b443c2000d0a58000342e000702d0003034005080030013a406103030600b580d00241c0749000c1c014501d416a214043c24144910307020f414080e9130001800c060140d01040080c1080b0030b2041c1c3c94904038000200304400d80d000f51a240d00540f20040d189501a240500c292500107010300040403520750350300d0094201e406143d08601c81c0304c2d0b0008a54860070000c0032900d0042c51030300c0d42c0c0c0344000c0002d446031010802d01ca00840c0e01c203081009410a01441c0d228890342440c040c0ca181d100da08090740505420200398000109000c20781082110400400b81101e1003524240055030b540e951098a4140c03c1c498900040c1c0704014003614402200b004210003800c3e0111581803030301503000704040750b0b401062b2030100d130f640f0000e124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 107485350 1250 107484100 107484103
    0x5030c01110903071503060e0c07060e01020f0d05060a03230f07030320250801050603030c151905010e0604050a0908040b0a170903030412020303060d0b06040905061602 74
    0x9140341c0c00c50700200d00d0800c0c090003181da5184140700c0c2039800a10760003800c1c0441d210b40c011400a001e41283c030300050900c0f404040d002ea20000045440900d0102d030381038441d83c180241e40024450b100f206040c0581a0101809000c0040c0010340c40800f03100c000c0300143c00d0042a40d01c0c01d5001d10400c843c031200340e610900d070015214400c5a103520401040000950101d02c510307611507501c0d894107032800c1480c2e14619000c03002400088985007141c00294840b03076120084225001c01c0000c0c010b0f511980203050f101e05c00d070740480c615174120344981c0200c00385148056402c01c07504850001032690301e50080c030072210203800c0719820440d40c42c00d1042620b803500415030000305203001048680d00d17070342c0c400056100b0380c031400d00810008100d50030000e02580303d0001c5045000c110500e03500d407502c4181d84a900c212411078104007112510380303199100009032842a240980009a040a01e40350b00f010400020007a6034499200c0e2800c500040301400600e0050204d402c003981035034100345000e07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 107486600 1250 107485350 107485361
    0x3030903070b0f0f0612030903010c35010e0405150403030609050f0f0103031b0f0c080d050c030d0b060d02130503060a2a050c030a0509180105010c1b05040905030c01 73
    0xc003c2d056400d018803130000c144032541140049403603400c24a1407070822800c0d4000c0b92440d0750706500c6d02040c200d0840c4c100351001c41001003441c0e00c0c1c04105098000c1c1105412083e544006c10f4100750043c49803010305402c079a0041e01031000c8414003030071a0307804541c1d040112422000640c80b01c2c0c0c20072010240e409507a80008455004c802d4900e000c16955070444014407001d010000800400704405031b85991108450340c204c20210111101070422900d1003415109851140c030401c0c040d43c0030a41325a064030004c03800e00300594a04046955444003500701ea110f10355021070f04120164071040c03d803004118603110441408162440c100c10103003012070050020b400141400160b68800d202441e005519000d44424004e500f103d04c8011640c0b4003546022804074800082c0e01d5511541100181450031021189031980760400b641286154101307100c0d403404100c40310b6071140015540100980059030451807068020b982d40300140c00e0b42d204050a813003541000a103418026000e010b030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 107487850 1250 107486600 107486611
    0x303200711040b0d0201080709151e030b030d0509151801030c02010e0d08100e010303080a0608030a08010b0306040e0102030106030608010b0a0305121c0c08071d01090605091203030903070b 83
    0x100442403070f5034041410318101c00b90090411a0b4a000104542e00070082d02c800703400d20001245031103102510103840d41ca440c0c0703186110384000e1074844503507070302c01d00071041b1560001e8090003000c56900400d40789a001000e41c541e100740030b405422800072855000d07104410300d1807141422400700d540050304032a8031040e84000c40e4105491141640d4001410203810b0605180150340c9546103520200a034900d50081d401c140d28071000081031651100916000365072280e000c101d0740d039407003050981c0c07441022070304008600c520703004002140c01704024541c808000341000c14041e4002904508a038000d03000900460b80d1130740c06200c004024410703550b6840040c0e40f828100350540e2901959080a5620f080c3e000308000390002045e0b0010061803a071580580c0c05100a0b20348443c09800c141d03040b41c003000020213030f16500c3c51080104000e250000f0040e1a940642408c05000b2a4254400d0302da180d084102003001c03176075100080000b14460030303500c1d001d951981003a242410340458094107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 107489100 1250 107487850 107487859
    0xf0c090311041419020409051f1d07200703080307020c010c111507060603121202071a07020312090a14031e160204090c0303180608130303200711 64
    0x4001c8805281c0010f4150010661a00d03040790484628200000e840740303411500c1841d0401307041c001c400f0191144001846d1041ca20001d0f216100c40012000c441c0c000520002c8406400100d08180c0c00340901c11140c6450214148600581060342407400c811a80200c1e888503000080002440d4103000e0031500076401d28124000c00800e4517100d00980049020500c141c48118010409265407401c42e80344581c80302052001d2642c81c100300e03015080e0203a60001040d60300e60400c10700210380c400c55500c258840202d13640d103810002c8005801e13000034951425480100800d807440e0000b24030161054084078001c1c01418040d140c14990402c20a9040c20954420b103c54940001c1c425400c0c591a40d0000e20f182d01c0c2c1402c00011540344018440194000e40340c040400c0903c6a80c185c1c1509481c02600c0700344590100d0b00390036019802a100703501c00107240b1408070304a10010b40c240ca8030715009107400310316180d91004c0c84503002845540f003102c848001890608205a9051303620101204a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 107490350 1250 107489100 107489111
    0x41110020609010c05090307051002011d01060302010210020901080a090302070f0806090c06040e040605071803031706030705030a0f0f0c150f0c02090a0209031002030705090118060509060d0f0c09031104 89
    0x6c0400ea50360b460b8003840b4841e40800b02d1807200303d8800d51200b1003d043c5071441041c885a80d5039664000c1805010aa005008841d0804241401c0c2d001316100082d06a640080c142c4d00c5400b000002d1402000441c214003074000e002400c81c05a45194002c1c1c41d0f05400707000141000c0301e042c3c2c60101070003800c0380520010b22082000411040010390300503040300002c60f02c0e540e845c8044490782209103181d107921400320400720905a1080d040c251980e421110404141c40785030405569250384d10440d54035a0201003444002180441942c098502c26420450b82901070340c0c0d403044101642d0880200070011410f1308510755405440a04640814103001442d860540c0100d40f050b90000c0c0007800c020b40001d01543c142c1c400300980003003000311400840d202d0a0802009000340d0000d490640002e04100340b031505e0303c1e19405188102c9281d5143d062606201405000b05a000603203090784d41a41c800d502440110f07103000b0030b6058402e56561058140c294a0046415824560f58a029034500b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 107491600 1250 107490350 107490367
    0x6040222090614071701080c04091707052d03120903070f110a0806010f090c020712110108093408120c1203070c0308041110020609010c05 61
    0x5004a080200403680803408440400d04010003404a1103001058140350031804106403486000c01d41c010081580d030380f03c01494050300b000c2c00c0c540a00030194243c00104417040d961510b58080d0b80014441e005100168914051502450b00119816074281d004000342d910004100042400ea07031040492060070102141807183d62400350b000410500d01c0260082000f0f068200152100c0d140d0216070319441c80341c50302c0c000c01c81006d5130700594055409290086411680400c8581c142d55000041c1d4241310302d441081409403003021003400640c0120003000c6034041c101c82c0d90060301c5025110300034203405080001003031924000c10811594000300e00254001100c00e00c5501c0c440c41001503551503009058a0940030a099440268103210f4680c9550022309100050000004600251030280d203500c0000301142c80304640020004c0e28144001c1f0029020301d0350300350400e01402100c0c124922282c0802c282c09940b074410f00240c2d0102041108100d0300b406400c66100d66841c00600f400001d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 107492850 1250 107491600 107491609
    0x20307080a05070302010c020a0305010203101404090b060d0303060f0b0c06251808010c020609070b0a0c0b0a020f0705010b04061a0912030d020a0f03060b040b03040f030201090803090c0f03060402 86
    0x18007000f810005000041c7c0203542e04d058942c0040c5401c80021913490034412114150403416224480c2d4012070050702000d00d140c07a11030740301010742201d0340c40b802da40c625040281c8411166011010300d952580e011881e2141080c000d0013402d542250369036140100c40f0b80e44c0c0b174000000d0007014403071010340300003901c1d600e0701e011b1802c410014180620084110113803913143e503019030000001503180005100d002940000d2040c0111950740541d00e9864584428110600c680c04070100481e1611000000250001840c04d074003100c0c500780182060040c0c254115140c1c40890287d4060303454440d45441d52902e44203100041038003149060b01e0f1f100500702c80da05409070201d0a48203954001207440707000d42c03c2c812648940740300c410031941e451440d8805000015034840107400645041000300fa85050b5404403002e69002c03040150030359440396642050b101a01804030210b5482e1002c603800100000d01442c0601c2081026011100b0a00c080c4803246803492400c2d842548030209020241c1c42c2c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 107494100 1250 107492850 107492863
    0x40902060d090320071409150607030509040204090606030f0501030323090301060608010e011d160c0507180f020415180f030c030606050f0a0510090f08010504020307080a05 76
    0x1090741012400700a43e007010b458054401450020110b42a01030110380390021503001d043d0b80030b030064000340c01c0100051080c600740886030f900d0000c0005c03101020f103140100c050054103100b4070b0514501004100450244d03002940300b603180a03100c800070301065401d801505c5110b29403a104101542c510f40b401402d1407001ca01e1400030403120701010b1181c20701c80084400c0010301400a00c412070382e50800a28111091051044010b08100042001c1d001c1e150b18a500180c90b000d00002501d42c00d0f1150f500820701d608010900205640c000b000800c2440f400f001860060a242e40b4070b044003151405803031404d5020402c1520410042c002c00300f044407058901f0915180031090094030f8401005c2204c45074001c0084215000000000c10012040c0c007015280308c0c050521210741e660b010310100f2a07070800c003280e001c0c50240c0284124141035030108407199251070160002030f0369480135814a08141c11481c21651284100019800c08005140051907850010001c5200c42c0d22001e441c1d06 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 107495350 1250 107494100 107494117
    0x20d080406050712092306070806100306090c02010603060605010516060e0312040605090d0801140d050c300c06160303020417010903110d090608060d06090f06050604090206 76
    0x9a542003c120000e02c1524035038650340950340300700320311451400d2520480c0650b0340000380d01072005807141000080480c0c190300500c1d10743c0701c04005489060801101841d01c0b48040304255640c1e0002620300868001c4075900880341e00000755042c21428034406071001ca23007009050100800602c66031048110700c15a6294010744001401c0b00c165000324118070035150907101034a0b50f041400140072450344132a001d034091408a03005500c4141c42a140488244240c1400061480a00242d03040c4540c1c5103284074400c0003a50141841d101c0011003094901101c1c0d8901c482210354406007620321000c0a40c02c0d042480240080800c580000c1c1c001c4c4541204120064840e1100030304260107901900e016040444080d0038100c01490792034001d080d1403000b50002090f400e0003400b12070010400f41c202200d583e46481e8003600304030050f206013002400b0795030030000b114010b9021a14620034031089070700c511180b4404c00c00c582050b0301614409491a031049140505040040e901d0208961510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 107496600 1250 107495350 107495363
    0x302360f01090b0a03321503010501050a051017010605040815100b0c030d05071e030603050316030c0209041212020a02030d0504060207232b0305130516050103060501020d0804 77
    0x4030480b040d90b02e00d007140c0d1710003100e41008405031000c0c2202e22161b06100340791035070340743c0c1d004e080c0c400c00c15080e07400a20a00303030000028041400786042401454007088414101150400403007500b0f0340031000c00b68000700c0001c01c04101840700c0e00c8240306120302c82c9100c4032802070500f4600180b441d043e25501c69011500e20008005504400620544041040002003007250b490b05403c081c1094598171021100303075020031241b00c02640a0320070003050360b0b00702c0011800c05210301c02011600f21403860607000c1c0f2403c40f805070016624000600c0c8201c1c0724041d40020800d0810026104200152204c110680144990f041866001040c0c4d0150401801d000ca07042d201c5061040081c0300c2d03080d001c0c141440c03004c00322030110424010844032041400c01c032507045060404011401c1020203a1030310f072080021a107801240b080d04000d07002050740141c141c1d500456640c080c074100019841e07107032400f01d46d84100706070360b05449003c008001c2800903090b00403c0e2600141084002030000f81903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 107497850 1250 107496600 107496611
    0x120c071502100f05070e030303101a090d080d140702150c0f0d06030215180f04020f07050105060315090a0b070e13020304120c050a030302360f01090b0a03 68
    0x80c14800c0110304584940403400300900141024220054442200c68a000c07034031141c1600b10a0500000b100c0c4140321500032400c2144c10680d0000342440391803004042008240030200b51640c13180c411070721107441000903a0fa85ca29a018a40c151184002944800a010790801401e6600403486022101e1401600d0074144e80703002d8010b58901450307240728094140840e42140e003090540c84001546e0085840d070003071b0403402400003038074414512a441030038100074601e682070030824044401070380b000b04007506000c4003c1d4804030507000310328142d40c207030b44480501856003014008036842c0280c0ba40e44203c18602040c0480d03803101806c1009141c40b00c190000b0b10319602c035400d0301c501c0040040440606644c0c203030a1101940048d50b0030388040c260320f08454000c50040340381054103680a8050720b4a09c9182e10150000d400415018000340b0189400d00c0511100214255841c0c800342e00380c980d00f880d110b0903c240c440703a45240b50b0520140010500c5407440200075525181c80b1032030701245 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 107499100 1250 107497850 107497889
    0x2250215070b1603090b09032701020307061a06270a05010e0607110603010807031a010303091a0418091a0c03011e03060e0114160507030c1e030206060102120c07 71
    0x10840f000d03001e006c4e010008180b181c07d5030048001e1500c2199841d180d100b40042c44102c0d56040c12050469001d41e10070000200046c126404c0600c400700c050040710b03401c8030400c001c1103180d8048a1280030301c03201d840f0003840350102d402d02e24010a205440c490022810070f00040d101c020078031348841c400c1c2c0f00407412104110181c00e12030780303100d005080985c895030340c2c01c20f81d5561201c902040300d4548030f44050700c03004010a90004d0480e901a03850300e040d071f0b2a00e042c1d030100d042101000c1c0c00651082001003020f00c04081c0c0801c41a018034400211032005040c203031603140070010103614501854007403008600d011070030b4a040d142d0380201203020000711482e110508100340c1c0000c100321304001c00082c0d103100650000e1000c04103600044095901d5a00101074030700d08a0000e400300310240010000b09114410300d0740e07854883d09245070000c0d151000c0340b020f40c444150440069110070f0070009207582c18801d50b440078446c0812903040031940b450a940311a036a0041c20340030306a8603c90300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 107500350 1250 107499100 107499107
    0x5040b03030d0920010315030b0c0c0105010b040617070c0212030705060901020d110309030a050d090f050106080d1404170115141011030d050a02250215070b16 70
    0x181030000c0b10b0000c000700075551a0060060b0700100b030070700802e1401140c2d64079650103401100901c8607090904d07226141550364141a126018003110407100f000e1101c46201c00b024490540a066803102007038640e45000300c020030410101c104500140503a01c24810344a810001c6801c295904684207c050307440501c5180c41d5004814014000b84500c000380b00d4a020198004c0189480e0f04605000d0030b1428503440103144429540c0d4006075204004003404070b4418030180c9180d2200403001700c0d00c6a007603103c054516098800696080e507440000300001401003048682003407541c102040070003555105840729000e00c0c131a503041c29402c80390b0031003415800c1d4000e4641e81d0b4868000108070b61100700010a0550440c03085000b1001e07044611a00340c040c5070b40c0045000801d000b1480c003480d4681c4c0c5000f41501804620040350280482585185e50f40074014a2030f00c0c01d45016500f00703090040010b81c1d1960f0702032026041c400c20114000c1840d185034541d1100c0700f90a80035800c040094101c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 107501600 1250 107500350 107500357
    0x9020301020c151801020a0804061503020603180f010509030a121104030b010602070b090d1e020402030106020115090c05030123030318040507030c02062d07030902180c030105040b0303 81
    0x105026220f40340d1288941600c250b8059005604590b00c0d044080301814200c2c1b00e1000d500000c181080b00041c0010350982001411803000309c50480400d03980d5000c0307195a0030507aa1750f10105003050710007107107250801100005520345030090005081120005071a48603c40c624010450300700c4081d40000c05c103030081150b44c46410152961159682066024403400380100401030040560020307083e01034006552040b00c0050400c40000313003980d42c000c000d40c140403011000b04070302c0c030040c0050795942c8040c43c000c1240350004070303418a15900d0520381c1000303a0406c1c603105203000790700c1c80500d0748401a641994184401100d504e0500c00c01e1004e02450b04003030b0f56140c4000075030802c2c0180306c2c001c0088074030300942d0140859114480280c090716100200040180e116100064800c0483c500340d41c18444000c9070300317088951904040e0380020003181d0180103c1e444000c3c0a045052001040d445034040e541200311504040785040e9562106202e11441303240c640c1c864414aa07828001c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 107502850 1250 107501600 107501617
    0x904020a05041a030303070306031412030a051305010c050a0e090108030712020a06090609031202091e010e1f0221030f0402061213060f091e0305040302030706050903060109140a0902030102 83
    0x881b5180e25007100300901500c003a000456003890220740034069040c0016000e0302417901040610b05507500ea503803680060100034000300c0490820150340000c60800e101d62055108190384055465000c044041d1610b800c10300c0c80d1b8002c0c0900e000400040801000b9500c000c2c0d4807204100d840703ca4174004900e00002c08402408403860000703140200311450788234104261107034440c001d850602d608102d080b4001d052076a43c01550762440c40801b4541100340070304401050410401c0d07044000046240c0c84610301c101c003c00001d085000c030002d030701004805202d55203c610340c0d000c00314044080301540000342243ca003082400c0041821581d9650540d040c000b04181511180d20f003480e041e00700480c03042801d580f03d61401c01c03050b12a030110700030881c0c12508030010507019490741144603143c020742607040c1d08101c0c0a000100c01a03400b846032000078800c0c2c2d555183c0b0380400b2400c160030188180e118210703441c50b01441602003126030000340e07417065800e00d0004500c2c1030b03400400e02a1041c03405 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 107504100 1250 107502850 107502853
    0x30e06090d0c15080c0708070f05011112010e06042f0f0708090a060201150501180b0309060103060b040614060703021c0203040f15081f030605040b150904020a05041a03 74
    0x1000c50026092405111058003c0c4c1d540d0520361241d40c2041130501c0342d06c101601f4207004002031008260064100e40215200d1800000d0000803103540d4003840d0000e80010300b01d0740d00c0800410400d158640c419400031000c0710104218440c200344003500d801800207079503c407111480810810003400c4140c0d010b90500e180815a5150b56141c10f40303c42d880f022155124100451020584500c144224000500310b0103c200d41c070341c1002c0c010f40e40070701c01c84680d01c001c020911001c070720003120744041c50040c26590000d01d510f5040d494000281c8081019507801140b82200822809221640c8042e00e00c0f4190b644c1c6640d00c3d201d0404906021f580b425041c030182550000940c055400030041003140c56440c08aa00340c0e442d55904220741900d4103407280003e00203404902490380c080344203055650700f03484c40490640e03030743e4400b000e0f0754046030144c1da0118484104124503c1300161010500e800b00c85000341442c03d030f800550b091410b4090b46004903075400c0031f8101103881401603548604000e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 107505350 1250 107504100 107504123
    0x20402070305120f06130b03032a1b0a030602090609040c0f020d08010305070b0901050c070803091f090603021b1c2604020f0d02041811010c030e06090d 67
    0x1c02400e164010042c0c6a1524050b000044480300320320349060048100406055072500005082c0e405000d100c0f03a040d501d408100006907600181e50354840a2840c5807400e000c03104040585241000c1150800303816600454401c82d0199942011007415641c0c041c00060b21542c40c800803c8141c0134200302d29810070b180c540c001d80d9080e0000e0241040e000198222407045981d4681118205002e01c00200190b0180c0070a100d400710708009800c248406140c5030f410101780300416890003050754010889a04005090001030426418002c0c286c03210000365410400d4a4500810640b12445807408141d13010400c943d408040c2405103103505028411182c0300042194809400000042000d011071560a40300e400303603032952100c00c04500604d92072161640d40340c00740415a07108002480e44082035204100060342d0350700c945200391551034010001080d080c40c003142e245503080a4581441041482040000d41c049104035105d001510150307291400d0f40e020800203400140c00900454000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 107506600 1250 107505350 107505353
    0x13050607050f0c01050708090d02061908090d050c1504060e0d020309130b01021f02041d06010e010809070311060c010c111501050a060305070e360609011a0702040207 73
    0x2040500c100c1024160f503000c0c0c40d400e00544140c859900c00400c000c20900c02406076103080e031a802e80f95400507200700c0c608007454019261215822104001144069082c400200c508101603400100c082c1030040c90b03c030380c00703100f50340d2051a40d41500201305241c001a003042000d41184101d0035400c1d085400c5e00301d0a9030040c0d00c80e00810802c90040c00302e4212010f802030140615040b040d410380181c817103109601d40544182104001c410752242d002c100008844c40340c840b031811700340380340e842c00821030500100040c4015100b180c080d0400c41046c09101c500200420403800310b95001c541e1001004440c004110140030790721010405500c0c1080581045411003032142d5501207035000d6a111940340d40002c2400c44081c007440390040c0005100b4007407a8003075486903070000030340d08142059010364800210143c2c3c096480050809440e024a106003c0390a2051490031440c0d4510b1482c0c50450042281351505209804c2142c0100c504040d01c51020b404860060f074000d082555101000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 107507850 1250 107506600 107506603
    0x307020d230d05090112060b090607050a020d030804031b17070f1401090b01120b191508031c06080604080a050408060a0504200112051e0a05090607020a030509061305060705 76
    0x407000280400c2001606d044000174a1142405440b15002101e0801320744505001c41c54001820403034980c4200b4020f00050f81e50312082d9588240b0030368890030545894074000740042a181038040850802c0202d000021303401c1c80030034018800c00ba0015880e0301351414811180c402c0d1102c041c00c1106114002c8a1801041d00501c03152801049014040d90380c07a00002584043c0040251090706420301003811400e2503c803d818445140c0c00124411029000141f00d0307440315400a1066400020b074091285088420801c601c00c2100c002c100451406040d56114075000740001c0002d80000703450846a8090025107000e0b0104000303c03140c6180c80b42c810b000070241944c007543e0302e4101c02d181044074505c0040700b440001d01a0b503034031248007a0040142c042d20000c1c040b88040d01304070045c0c0c10035400200030540700d00e05040c0c0200e20740c00c0181c440340c185000900440e0440d0040f8110f5004290020201d4650703007420345c3d04c1540c428031041405a94644d981083c1d501120001d03605090150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 107509100 1250 107507850 107507857
    0xe0f010504050106050f0d09020406090c03090212010c02150a060b030a05090c040903051e31090c1b050316050109020a0501081027020705070807080307020d230d05 72
    0x305440812060b622514169558060700b007120003c0081000718448040b6260407030881c0500c06000820100d8880d0750f80e100791040c148454002940d5a1124015403402054150210704604000c00c07055502c10703002502c0d0f0b042014210484600c900c007003403041d0740c150f0141c2c0c000c0c900341d411b04c0d4590802810540103440d041c1c612080c188074055140d6003d150904c40c800d0000d615481d0f0390301d04002003c0851094407a61030102400d2014861020400310041c889803900c0d14130300b440900410740e00440c01400d035082e000864064a01094050440e4124a01785121069004026070300c002c0d1b40741c4149903200710740b04d500d280441803403100b0401c201500b00304403ca208541e0340c00c05549640c0111205074080701c0407501080c0c40c0008120300f030014040740c001002d282070780750402000c00301004142da02c8a03200f2120307540401001c101c0c1c0c2009001580103424440701452404038103800003030003456041c001030641001c90000c0c040079081d11313111500c02401c14080e180018050000544180c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 107510350 1250 107509100 107509109
    0x303051e070c060f03140f0709051003020703030f020301080c13020c01060b1b12090d050c04090c05030f0307051509010b031002040f080109020a140a0b120703060e04110f01090e0f01 80
    0x1000e030000403c1150003401422844103c036000707011b541d514130212540048000c2c10040038022034180201d2143c592000442c401151520b026a0300c074410300c0c0050803140003424449641d40305000501003000082000303080300100f1540c00804c2002103003100028410f102d1000425031816200140501aa0003d4882015044191045c0d00451401c1d02d1300c0f0314000c3e040c1c800c80b071000c1003051f20303d1810301c9010507083d00603400c5800c08400400400c0895228040603129070591480030442890304100ca1241d000450001d14200840c503a9010f0703413501015404162440c2c01d4001803401d86003540032a96001000b42200c1a501d11079a8200003540140200b1424146051010800c0c02050050b0641640d01a040401c1146001c1d00424890100004030f580710040080000300c5001c043e02402d01310003220503200c0a42000003000c0d00301d640d40d81c02601000c55802c06c000100726006000001e0074001d807000d481c001010401212407003120b0300040c041802420910080443d820304003410780c0d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 107511600 1250 107510350 107510357
    0xf030109050f061c1502070c08060612150609040f02090a090b090f0604021e0603010f08061524270f010908060103030f1b0303020c07050604050a0303051e070c06 71
    0x1501c3d4003003800029140200030301030115001e107600c00010030032012040314942201c001410000d850f80c40340301400f0107a22416583d480007007488110725001034a5043d0000a030002d0881a01d6401c110291603001400f10340f00e040d00100090510400c0c0e1103803460558010030410007841c1c02c00521008104900090b20011000000622031200c0080ea0104403000103004080700c0e82c0d541d0070014100544082134003103840040200b0401e0b00c41030080c40c0a071142000e031107841420506502c3c0342c500000c040904041141039203d40540710251391380e0812040c03c0c2c0f103481c021015a66419a407040e210140c2c041c42d401c8403204020360121030040c40c0441c044031001d892075050001101d40e0040c500840e101c0360080d800410001303008803d0108800d0582c10065202151110f29010305490a28180c0220740c000038142d910a00c14850340d405000304a41d001e0809042c1000700c1e589041c01e001c01000c0c448000f03008400900040c580001c442e02043c42166200d90924208028610920600020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 107512850 1250 107511600 107511631
    0xa030614010203040306231602010f021812070f060c0204140615030a1b081905160c0807080301120209091b040903170702010c1d0307030303050c0f03010905 69
    0x21194030315480408004140d0046090508503125100200b0f6040400200034040c0700c81c0801a40c42d4031049440342c1350417461807000e8201000c0c080d00f516a091504d0764241e204020b12044e404c603084542451010942d1507455801c040740c41d030b62a08500760080c40002039070f080f00107482640850502d000d04d200ba10207104440101221180006040d54140c0c0d2101031100b840c400440300c0d04c00355900001d0440f01051140c921482e41c02d00244414150b0009901102040b000080903e20103400d151f00c0f00e01003009141011540a83d0344003c49400200400c041d50882804507040079540b5081d00004415501d5940b003014050400c50b032030b01240079003105000141c0d11070012804840381c0d103080306034208081d001c0d0100402416402012014000380441080f14000e40d110818418074141c0c00004455100c0c0344050400b41b4805408140b9010311445800030352404910402201e82c5801e0101d000c0d166001d08507484d015184004140b070318040000030700403507503400c400c2c01980d02c2ca100048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 107514100 1250 107512850 107512859
    0x617092820040b060c030403170d0608161d0c0a2115050102030403030801050402090a09050411030c240307090b0c060a0b0402031317090315040c0b0304031e0e040501060201020a0306 80
    0x13110302501101c00c41eaa00240400c01c04a9100742c07050302c0c10350511421502d803112074101507045502c01e030810320b555484005e010701d860514a03800005805511078210034400c264a5000200c400200042d0b0a00340200b08132910394020109189003004114290403541030703104d649030040a07600d1103001c0300b50300e0100008295002200321002d8075059a240c1003980c0c02e00d030500c0069440028070399000f08070301d400058000d0803842068041c0f0b101d50f081c20510300b07014041514103818400359512502d084072030700e065030354401c111405036109034465540781e98401c6e03000d40b4148915840000103040002e00034a101c40041610761003200080f4041100b0003886e000e200c1280000c641e00100103100f11007035800710b81e8007424003682414881f00c0c90719200a603000301c0c0c10700f901c8c030118594130070302c0c08103100030809409070301c101501c016200b09085140c01d17200106159262000c18403802400b00c4003480c00740c030405140d003e0f58005082845103503502d040003070003075001251200002e898031f00c0206 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 107515350 1250 107514100 107514109
    0xe07060c020915010c0303020a0c060519110f070f0203010905030408150702010908090909160f0302130c0f1b0c0f090b1203030601050a1b050102040617092820040b 72
    0x210111010384d2504017110050750103074000d41c0060000f0050040c113007915400a401400344500c50b8091051200c1d00203100050003054070248110007030340001c14002802da0900203000e9602884d0080001c05036000c60b400800c1c01000003000180460000140101d0550b100084000e202115514902134540c3c2d5120100e00300c400588d070062220104006c2004e07980b5089038480d0b00301c440d0f4403c4d40c04400d01c0d600c00c8040214260702001c000e4030b158078108154605106420b000390394480381800300d00ca441100919034402c000ca00750034041080e90b00a0006a40e05c41c00700d036194000130f003407100d54403a00714560b44074551056030f107420304210056540b800c2c40000c00e4a4211018015070a6489040c010b55454100c0d0a50a04004205007010f260340040d009210071a0702a03000140d50f03900b4200010700713800440040d031040200480500c046d8840c000380c4d10818191910010341c0440541d8401d41e8041007400c030203040307010700a4142c082507980e4804070500b460111010030641d4071540501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 107516600 1250 107515350 107515381
    0xc0e16090608161106180706050f1603020f0303040605060f030c130f021c020a080618040b0403030915050f1609090906020903190b010b04080c0d03030e07060c0209 72
    0x40041d244002041115001e40300c030034990116418160b49507100c4280c198500f06040700c00c9603c0511b0840709660100301888214003500380741c03900d18a041c40c0d6002402c180d114109520305c20300c11102c16541414800e000c0046402c2144040c0e0799681010b0524401601e02900c0091150b00c08e048000b01924000600e2080040d0140014400e8443e0000500040100030340003032100342c080003207100c1e034100f1002d4a126004041001038588035021401840380e60700500441c010954480d6400641c1103102006a00c180d005480700066603427071400311302910460304010003000340aa410000d22505030003441c41002e50704401000b5544002121075800c0e901c0b07901c580458503412050240309055003041c40c54500583e405480c040544e000301c2d1400600702901d003c0c03581030341d02103010411142925030051030f0100c25903082270704102d5a2501c8001800c1403510039100003a039581010f0290300b0203080c000c0c2c010700751030f4840d559410160240340ba15004a200310488000030b242e4660407600c1303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 107517850 1250 107516600 107516609
    0x3060a050405101a06070602030a0c0c0c120204020d0207120210050c0a081512031b1605040209040b0a061d060705060105010804030302121503211c02070c0e1609 71
    0x102103860151440303c004250500d0318100c404154100150075403603042c020300003c1d200d01c00040c1d5a1034182410421100e031101c010701041102c41c0c101000c5030302190180c0942e070a5122500c04100d152001400901c60000310480c03040c008a40081440b07604005e44021074171a0702070322842103040c5103d80480b04101c071015001481403018048440c400c02120764058140882001801c0c000c0c00000c101049000420119500004104d0360140c01075a8000c140d1084900800100c803910040c0f03501c481050040c00d00603580450110107a5455810502e9860006048407003101e484060045c40b00145041f030841c1220807415150741030420001701c49805030094093f04007139082c00f0044030b2003040038005808060b001d000c03110041024442441c0903078185155502a8030036003041c11304020310750141e20001d0084690050b102491030080700c0000c40034082107005260040c4402009014840010b03106d0540c10401040e0084c03500c10050240b052540404030541c0c00726011512071101d80503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 107519100 1250 107517850 107517853
    0x3080a020f0604030917010204080105090a2117220b06031506090402150c0102041d0105030d0806101101090c0302040b030f0a03030b0d0605070915110c0609010519050903060a050405 80
    0x5e0801444007444400c0f504c1001c240005032500303689043d4203081d61000c1e5802c40090700420708182c200803252034546080c5185800c00c52210382d01d4400544400e486000caa05602007c10002c0c0a08916416a072518105071300100c15504190400c254081d4085070030601078440c040701d80200c80b94080744148500030080c03551b000e5550741d03400d128102150301d403001c9404200380040c5901402c00c0c00900701a1a03c100c182240e84401700c0100d50207141a030100740203030031440c6658030066010002e50362000040e26440a8102d2903107089800c524440008020b039480d20503900104461250070004882c000c88051007802201001c0645500714882440c400c2c0e03010744400b100203070003034000041d2040000c100720402072003619900e0030744004070780080003d5a40001800612114919031100c0c2c00c481c03a0899410300b4003d1900d03590034044003114801c49020412071040da00c910111624084010340c2036815a20305040a40160440070341284a4000d440000304031035079512500b44120740150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 107520350 1250 107519100 107519117
    0x222901080304030f12030603020d0609020a0e040b04030311040503010c030e12040501090303140f07030e011419050c03070c0609030501060608101e170f06150607030503091603080a020f060403 84
    0x1d0700c103003999030040b1700c031400e058850310b0000240c3d0b95600e02c1098540101000302d070b8894548108100400c440d0081c50f00c0404d500240404501040105644294181400688480c0c0c00b0300441c1640150307405a5419802e01410120544d4190400442502d00700c0440d00d400c02d8480c031802d0b40e4041d500415000034456041040400d20a1070401c1c07d038081035005034a804d81154518505600c0600e040d804114a190071030042d580c44950700d806081400000c0d400c1c2840944900b15083c4814a000f04000e00032403003810425090045030441640b20840841403507031101c0152416460748000c1c7e0b065460000d0018481c0c0c0142d828911800c1c280c80e05e1554281000c0d125219000001200c0101d0b00350f11801152040c0c10366003004046110000504105035202403861419000400c9402e0401800b8400d0406844501c141d5502940c107041058aa543c0d51014520340080100c40207143d48071490300000f0700002000914005c0d0181c0d00b5550003612160106680b031809440c0100000c50701c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 107521600 1250 107520350 107520353
    0x170a050904050108151b0f0a0e010e090105100f020c06040303030b1f02060a1a030601180e15070c03180e0a06140102280b0c0c07150503222901080304030f 68
    0x40c881900000201b444403414007000b100b00381d8081d0000c55290010800050541d10290381011081d0482c1d001110ba0122560602000c5a06420720761404400c0c03010380c03c4800049170003806081900d04015002544856503424014050280c01c7c0416009000010422280a6800010704100c200d01c1c1c004098580320705160000400030303000d000300094542c0842041c944c0e02408814020f04d00141207a074121152511181283c1e100784101e1443c1d80b20155401414440c6022554002d0f01401c0070016070b01c1500303095503090f0b48041c804100c40145078002ca50702207045507142c06051800010407010340c988081c640441c0c1c030317242d849000d0b13844001c0303c0d00d00f403040c54042c240c59009003a01c44d220400540d1508400341c800d5454140c0f880c000300f041e8030303c07502c1081301000605103860390302420400040701400511018002904000c98030112002400482c4c0703a0350740d00c0d50b003c444007500f4100c2e0841036803101044a181c4190f410440000a08800000192801d4070340151001d12060540e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 107522850 1250 107521600 107521621
    0x180906060a05010c0507060f05040e0a1406010309020f041d07080102070314160b18070902041403060f040308130f03020c0f0114090910090504050a06050c0f0301050d170a05090405010815 82
    0x18070b00c03072300e0421004000110b00119a42c000303c0c040c0d401c4070780c08902c551a00c100d45503076881c02498581014640f41101016030b441004200c000300d020b503000121032a04035450080e20601c110000c216100748a03000039000070560040c41c2d054002c0d82c410700b10b09480c0160b01041d01c20800c90b058100c2c03a0203001c0c1c5c041006d5048a64001780e420401e0400100064030003810030000d54080d01580358046410000c9501c40100100c5048040b00640720a1900b030222410600d800fa2000d42045078038400200d18a2050248642103030700000315401200c464a070095a0f51710f02d01c000c0340100858040c0c0c0005500031300394014401004890316007441e140714103000c8803910090400c1305400c02c5880000b103402d00c0d44101307400356007e0409400312141c6410900207940019011a00c440d000304000c0c149020b403c4240ca040d0388007240c002050b12518103000202196040441e022a0800283c0109554202008000c40328099405004036a46c0c0c4034026200d14000141350484084203000035510b055 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 107524100 1250 107522850 107522867
    0x110d020a051c050601140307090c3204030c0501030e0a0305030105010c050307020a080607020601080c091602030d050a0203161103030a020c280b010504051b09180906060a05010c050706 81
    0x8000141c152820860f0b1200c030326000080c0e000ca0400c0040160030303011410b00703010b054041d203d2600b090000d14200a4010b0010040c60220b0100103d81d140e81000c00828541ca0b1070058520149152616140e0408400100d014412180464038204142440d08004529a0003541d050744503e03045a2802c0b0064502c4030200404031450301041002c800182c0d80c03203007950090452039008001601d03100901a150090680002110394417684903a8017590700c1c3d40c4003c0c0d00c040d015071081850030076100264038601880300c060010504090030420422003550107540310301160041010b200006000548000304ca851281000382c10803c00202d410085400403e01403130352408599000c40800c480740c0480d80462098800d8002c40b10b01c0b80c05200d40712000030b016100c202d808200d83e00300058100070403203030498a6111440041402e051030740d106071a100f003a240c2c4014190700c034905520010b0715010304450003442001c140c400429554851114420b1142e44031009181075410820181c1d640300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 107525350 1250 107524100 107524129
    0x10c1a0406020316021c05160c0306050f0903070c060e010306080102160201020709090807061802090a0905010c090503030d05190f0f0608070b03010e0604180803060a0602160e0a0615050403110d020a05 88
    0x8c05200071000110f228004c2c2000318000c50300001c1d80e04020614143c0c0f00c0029011003651340c81401000c6c045001d400c12103040341c40314288905018000801a400341501d07a11a5903594030106111111044070004070300c8641c400da0990b49a80e07100c2109000f156998040909210800d0004200141c010b07445841d281c00701c50131030030360b20501c4d41c001401000115a0880b400307480301844801c000f02405200302c170141e1410b00f821200d08100c007180c4d51380140d1030403144903034541e000314481005a4202d81090000108148290514104504007815150034400d004c1490500c0000b401c05001c80e03c5001c6e41d0540a095156910340301e2924500d82d0041e14490740207641c1c942100030407560b00c0011103000e1040780b5080e1240b6101040040c003016683c40341e01550018900901842c0006120000765002d01880290645803003042c4401480641c00001d00c1e01940d23803181140703507048405442200d04c20194958042c404905000203ca10014001d4001501c0d0b40117010b18a480e016448911 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 107526600 1250 107525350 107525377
    0x30f0c0102040e0709031a070807030203040201030609110715020a1b0c090212060f0d21020a1b080f0304050f06090105090a030c14030a0b0105010c1a0406020316021c05 74
    0xb0b9114115401d11050039200040800d5003030008100700602d2445500c55050300b10b0302600700c1c0c1340c400c0d80a00004401004101050f074004001001c41e03010340d0040b0041c128403082000601910107140301e1644c80600240d42210f0800d0140c80d12070b0f854000c8510a0015685880c458004083c80140b14070038280308640c3c90080c10f0010600b030f05c4510190021043c4619580d1141c203240c0144042e182c08410b445000780d400d030001d88040b0b00301c0062a820100800c0c1111244811060100c1c103000c20064024082c419524000c813030041d610040c201502c91840644501010242c9080d9485c0304a12800d43c0151804603401ca09160035409807070403040605140d0b29001000001520100e440d400484514611140a1000c6061120050101d1500b41e005040701802520307040f094130814030959040003044503a00e0304000c1d075003850a01014203d641d15040303040601d0800040c0d003080b40c10310004007174541c02d460360b07900c002602000034200d070008009111220b501140c1c540c1c03002e140b4047e803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 107527850 1250 107526600 107526607
    0x41529090712020f030a1803091a1b030307261314061f06020d0c06090f080a02010504050105250e01030605060d021801050301050a060e01021203090a150e030f0c0102 73
    0x121040d03800202055680110304d140d417860408a86400c490300f18140350303100b03200d00c1d082e1000a6003181c030010959100c400d00405d80014140924418414040202c16240044090f5512050004040c41c0140303002e403a581400c1c890900c0c202c000c1d00800003000c0d581030a50303012841d41e4100680044855001d25074904401025100061404000751015200c031002502a111700900d40004c00e0081d11040c0302600211000501c010180c01040d503024041943da994a6010084503001c18a24980e200701c1481e00c0f150a8100680245001c40b403d0b10079509141c00203102155000e240354040060941030034625003000022514054002003a0b4181a5200008909542c0b05005040241c900d01009640e07288100e25140300013441d40798440c18030109100611080d42c40180d00d0094032001c9c03170304412440f24071004078a4103500b9980d54003214130000920500d400302060309036009002d40c080740c00c1d96000111604c1121104e1640e84003030f400c140725012a41900780c00400d2085a04e8001604 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 107529100 1250 107527850 107527877
    0x902180a060809010c080903041802120708040c0f0302010f051b16030318050102030a0f0507020409080903011b1e0e1003020a0810030b0408030a0e060415290907 71
    0x11040c0e822550220702c2d29010440034031003d024850f000d42c10362503d5207083c105246801e03503c0c01907025600503041c0b02020300e031090629506032441c0604083d50b0b070110303040c1900040d01b00001070301c051b80c0780303419184085043c3c18000041000c40c0d03410380d510302e00c0c0c4201c0581142c139a001286500c0d0401e405841c0fa80c0044070801801c014503090345d040101c044c5c44c42c07401a15640c01c0910412012411240070841d6a0700403041d5a1884414103040c000c0c161a214221214802c21100940c0b207407030018203a050000c000040c02121005800030411100c400d05074442c081c21000352040040c0014101116005903040d8120300c85006080c8082c480000d400000d540049088503040080c0c2d01155408106a000e882c840d04890b44246569583d07041d500d540440c42c20080024040c0240000411800e130490b82c0180010650641640c260782014a0201c01e242c1206000741c1c4003508040007010072032504c000c030329043c13041c1030090851060303100184140000001c02c1c0c5130038010b4091403040e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 107530350 1250 107529100 107529109
    0x906040509090f0a0302030901030b27070207080303150108011d0a0e030c1911010f142a0d080606040e01050d060e03041e2414090a09050105040e011401090218 70
    0xc84c920303ca80c000d10b44498555000408a07010781c0c0e00a44150701d034082036199a11451041c0c049140342c90329030788035983d450200380d18100c1c040d8829025403000000b040034456004096005120091341c404100341d130390300c9c0817080130704982400d040810a003d005c207004124a900c070940d480c04c5c98060341c1c1004010446242440000300154040e000c2031170001c1c040201802007244002c5007420901c900b0500c9150050038080303030101e060364006001610f280c03003151000103003900c034182420b1220000f440c0000503498131028050003000c04c40001c04100d8510707194003518251454280882e45a0707180104104202c0761160041e01c00e0303641c449103c441590140020001b42c1010844450312040780b20703c3da691241307075a008030700d580b100300b2070002000c003030810006841c01203250500e00d41c41c18039007868540c46414107440d444816081d0001e84101c60b60000b034100ea508880c10410160080d108500f628841c003254207038452100014410405180d029040c40c00601c2c04502d48500e00b5030104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 107531600 1250 107530350 107530363
    0x60f0c0c3007080711010201020f12100506030a0c03060807052d040203040f030210020f07110a080709060504060b0702030a170706020a2109020109050f01051c050405070b0906040509090f 82
    0x255040703c400074490b0180039464065981c140c2c0284002c5107002503061131001c2a00a440e04a02c581420303402184211381c22140941c0909401410265a4140816403600502085800350086410a900080e850b907000c2180c004031280034000d20444d0800017401c030009038a41d032000c06003d100d40348503078081d03c40784051407049100305000032482d001e508000e45807442044051030314600402c501428904000127940c1c2c01a0701420394502c00c5140400110304c400550031503a40d17032140483c0050500440e8000500300d034070a8404008050701c4080fa012144510400a509548101c02d2400003030114080000c5100003014018100800ba5856000383d900004520001501103d4a002c000c40004c804111507030050b002000712000070390029002c000140301e424441d600b002050702050b40600c1c1280c400c052500e85003801d404000d82181c0050405407010b44981c400d42d03101040d4604500101c5035802070080c0301c0350400d880d2104100f00c0c2c03a4001c1a1045500a000540c2c02000c41006031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 107532850 1250 107531600 107531603
    0xc08010504021b010207030e01020f030403170705030c0105040605070f170718120b0601030f020702090a1e0e01060f050108090c090c04050d0606180606050405040902010302130305060f0c0c3007 85
    0x7030428088d8503600081c130b0032128608211003500308200400001e0100c040c4420403940844c03e0035203454160601509602418440c4a041d509040c10001006101e0303018a1140365a611480316607081003008440151140e4044200381c1e001c0004902d18a000d01e1130300d02c2d6040030180d51040703181c4400014402c00d00130801160021101d500740101583c05008150000904280c00c508081198001a0301a480a4402c000302c90341d9202c1c601010714456210880c9001c844805c1c00a54442c0515a0003049588038004a041c0c01c40e502041541c0f0a1410b140100d040c14010025004c5000170000c1e040400703800e402c100d1004000004541d2522401c50101c54040c083c00a40c1c1498503c4074070301325075100c04508001c0d1410310180701594104c002e48040d200280c07000a0002050700c0168000c0c42040403032001e0f031910410000810100141152103840304078a02078440c2c403a022110351030f007d0344018481e682c1081d4041c00c070540c40e010170600c40c0000982c000e11941800b06103070316103620400c0c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 107534100 1250 107532850 107532857
    0xe040b040b061b12030c0904050604060f0b04031202030a0507060c0c0c030b15030d120902040f05250903031709120a0c020415030b040201110c060d090b0a0c08010504021b01020703 79
    0x2070680c0d518006200c1c0d82c07101134180807801d18601e494401d200c66403040380152407180f540c0303078003040d00c580700c42e840f4102900940c0018030701c25032146e1444d24690040c1c41304540300690303180501800d03840807055031401006a00c0f200d00b4804141d84d140e01400d010600102000080301a03407010400c0c542c0e07904000c601495004002d4200740240880280170709000a010344d10600000716015840b00350386c0110401040002509000d40c80005d010340304002c0101c0318142080140b01c000d16000c50200b05680205d140c010b442d110003441903074840407074440270707012402402085e01c03803c0c95000d085501c401480152048214421400d2841c1c0d00324199410002d00004c0d0b080c6c2c21402c040c440c808101e440004402e0440d455a90395072140d02008000a04000392120144042c45007000032020083c0001d00040e01c1e90910314100c0028030036000c0540e4070701c1160303002c03403100070380f030322400c1480c00c2640d48940c02a82420244006940128646041000305001c2c3ca03415030020b202410407203100b6075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 107535350 1250 107534100 107534137
    0x30a0506040c0206060907050a020109020d080901090f240509030a0b10050405091011046504090e070f0f0b0703030c141201081605010e040b040b06 65
    0x9041c0411514060403207820f41d881541406000c1c1e680380c956a91080d26413900307980d0b860f11000c0482c09000c810100a40003481c41d40801c08100300240540000034080e40c40c1403241e0761f41d120ba001c0490841c418030000c40300900c5a8040c0c0344020558038103114040c00d0030f41c60302c00b07060301103458507000240a030344c0c1d403003080140a500c1252078013503002010103c40c148282d003490f4102c030751a9104002d2804c0d0b01c2d5911003032081000c0c10340c0c0c181d40c000c04c0407800c07004096803041c8030f282e0590110720f01654031061044103203100d0422804403200500301000a1400740160158a509041e507045005180e01c0d024000091000e80300e0058070001c5550744003402c0018904a41c180000115810500420003844014040303a250035080c1c8004582601e00418022604a070540e940e140c0398003404800000000d0340161080ba404000d8100c840c41c03402c0300d04500401c1aa40d03025a07403401b4090014045a080182c6450142c21140501800a0000800311210400103c050b4810380f60041c180c1000c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 107536600 1250 107535350 107535361
    0x110c010b01020106080d12090309030c030b0f0705071e03230408100902011b0204060b0c011506020c030a15022503080a050c030c0d06080607030e060a0b0603010b070305070206030a05 80
    0x21300807030004060501c0245250046240003501c010901c45c61700386070580c0e4000c00384c10b040c03040740300d08025a08407540308640da8032801e021400d001c08940b42403502006c100400c500920035401c480ca0190410038182d010b0070100c0d0800b4100703190742e400b94100680c3c0e02d2583c6c0b061848030981400000600c2c0003680c0ca038a44079a8a04103040154105501d40c500755401d001f50343c000b524030450210041c00d40c400c0040904c0010300400345604005480780e40800c0c0c88658150540c0280d02c03e036424901c480980755280e0b4200e80d16a4031080c140c0d01a0020300c0600001100380c2c66030b04c4ca40c607440001500340000e61800c01c1d00e0140c0007000b500c02007041042041450340000342c458020301c1115080c0000e103881d201041683c0b1010b025032015800c0000c5a40e06891342d86d0002014250718419101942042341004014209001683e20180650400f0035028110741c444d81c07101e01c201074002d508603032804061030390b0303600151810740512600300071110042c1d80d4507005601c03560703040c140000c460030324 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 107537850 1250 107536600 107536603
    0x10e0d0f080c040815040501021c0b0111060103050709020a050904092a0501090e22030221120a11040e10150e0102120a090506070c03030807050310050d0303110c010b0102 75
    0x50300d5000b10314001c02c810302c09442c0100301c0d4002c2a07050140240c01e506e461070907031300a12a252084200101140b00000803144540180c030301ca40090780c444d6080c01e500030b0341d1600c038030003807100400c0c1e13030301c120010441405a900035000800c1641007650404c13840801103029121010802c80d6052040c01c01100441c80c8440c10403030000b116803940d1007517030078070001800f01c0322a402004015045c0800041c00600007002c90f0100d50310100d00d20178090004d29000e0350381c40700c1d0000209241b503100d00031100e8440c0a01500d06540c9420000d000384e40300d000044005044000910114075400c001c0070400c50b100c00c050600030107150201000d01490700b03091100c1034070130440642c200030307801500b000180c5c0e0001d03058000801140c4001c1c0d40c1d4130f6074202668944a02d030301c1550090408500101440005002d907404c407030007516441500d0ba00c0d150100c84520007240d1801008020b02c3c0140714504100a1f44502d0612a0400040d44080d003040034000ba040340e04094507580d151110b00929503030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 107539100 1250 107537850 107537867
    0x30c040509060105101106060d14370317062b171206151b01091a0412030903020709021c060b0301050f04092a0306150303120e010e0d0f 60
    0x560340342c960030401e011b21003140c1f1303802d0141001e0f00c1140e50703080351000d03c18440f4541d50704000d800112124015213001007003002c18506000a04851509042d0031070403240d502202d4100d60580d980030a0078072200d01c81c40c80050103403000ea0002402e1b0090801c0805081d0940202080c0326800b81040700f152030422400c01008519882000c2d05005c1ca6010102040700745070814003c5858180721501c55140e500c45001c0c8550070484110048120301d00c002c0e0651004c90518090019255290000e091a28400d04103507401400794185402050a480c031903131020071914030a20584d07240c255200080c00598208a60484e0350700f82180e901011040d207407051200500094121501750b615143c0014001d454400240340115298042981080300304180540b400781e100c11580615000b641c0003074940d00c0c45001c03c4801c41c7c44c100d04020031000740c1d1881022a070781942c4010040d41d51100c40d10282c0700f1242001072541d242c4502400d20381d82400081841141551078100310418100d00410400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 107540350 1250 107539100 107539129
    0x405030c01090b0412021605090405010b0a2601060b040b070606150905030f0607051921050103150506030604030c111002010c1404030c0302010e03030d0e010204050a060f0c02010e030c040509060105 87
    0x40c00003e0f07007ca009080311844044520450f1611819511800c00d2405401044041c650000749042c010450707201380e80030364012084090894400c54108159a402ca8030740e0b0240b0312469070305000421003c40b54800410060348220400700c0d610399618162102925042c443c6004106041c0007400030341410001c0f008010346031801003005080c1980c01901901c80c0e620b00840d80b00528a4040059001c0c820140410100b034421800045055402c035005081c02e0200f21207035100c6100c880c90701c04140c014030340035440060281c1107035150307503800340c03003840d20b040301120954920000382c4810b80e554001c89401d100c00360004581c0703c204400040c5020211180c005001c0400d0000780013183c070312621881600e50a08040c004148144001303455801128400c0102600703100301c0c02031910064001d442250029211000301c543c0f1000c3c246d4100d0302c91444c42c0c00003412100c50601540c0300b11202c5203020700c0038068403412040d807000708003034030b1084032010180d90000d401007025080401d1350780c8068 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 107541600 1250 107540350 107540353
    0x6091a091504020114120a020c071d0703230f09250909060b0901060f14031e0c0c0a03080402030d1403040605070513030f03090b1801080405030c01090b041202 70
    0x42a003021a0501d111001d84060b040102c40d20100e9884a417400441c4c0e8040c030810503140f441d1501d0440c00010394000c0300f04802da80138883c8005060700030f45161039468110a07081264a90b590f40301240102481446c51440307000c144400111582e121071407a00070641c00e0000d072418079089800d0382c5060f0b48012504040c0703560103513a0407d00017207040e16003500c80201d004605601c49e07041040c0a0045426000c0d40405203c00010700c407a04440100c1645000e502c51b440c01040701e140381c0c40180011905c2c2c1e0b00051207480b100841100208080d60b00404902046040075124040c1604c2c11b980c0480450100703175520240815482c04000f4003d41024500c3c140c0c1d5103041a0b980a402400301802c0109043d4866003c544030360f0140c400e440f02030b10300d501180b2200350ba03410a2000440c1080054000c180c03440e001007181c1c036a01c1c040703680c0f40d40310341c1d0f120b891002802d004403208640140180c0d40f50005010200e40f01c54280160384000b4043c2010303094a05281c10f1004c8400804503151066 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 107542850 1250 107541600 107541613
    0xe01050102030405060c0f16080d030204060906030903140d061a071a07020f060c030a1505010918110c0303160c020f04090f0501110a03150506090906010c06091a09 72
    0x240daa00000b1036056480958000e500c072940342c11140d15208030607461403081e000c0d90b90f0035040d0070780b00d002200440d8034070002c50380002003000b41034049108900030f40d0b002071145442800600d01a0f041040042e00c68604011420106280703190260840105000e450307032180d5041010350403000407511885240c0c460a407800d03070156075000041c0b03e01d0610410784d0f407002c40003a1035980280003103261105d4403001d07110300b41b41801030300441d90300454404004c0e5181846103900840f81032420b909403041a118104124200903114aa40702c01000886056880d005940d00c8054001c016040c044005001903440307041000303060052a2601c0c0714001001400c0c007901015946000d00100c0115042ea80001d4a03202803e208003e00d19000001c2e2844d070828045410f901c80100050200851650707003001340c0040d207095080700c1031182c480c181e8003d8050002080b10318083d000b9941041c0c05062100b502c800350f41e174800c181c90404c032098540401400128200c0b0200da0611544104007602400b403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 107544100 1250 107542850 107542859
    0x10905030303061003200a0e0a06020c211002071b0b0f0403020603040303021b0c01030c0c0803010b030c0702120303090c01030e06070309080906071b0902070c0e0910060902070c0e01 80
    0x1a500c10300482402c00d03882c0c9a100000b491b41c1c001d80c02904900248440d5100034660f005843c4180e01120b040c0100808c540c0003604510101d42200e502034000e10b00394580d41245688821141c411800005d140980d40600c09296400d00c01015600c0c402d1a0492a204c03070700e4416001c4010b554000c0e03804500030441241c078120003104540030349604840881c0c0326111410228001e00880c2d0b6100c0b03143d542600f00041d01100050b948484101c01d0b0b0b420f101201d1510412920042601402441c6c54000d00c01400380040e4440910760010200c1c21080c01d0851903000210002d0f038040c0311241d0b40e0000418070220b60003c7c40040c1d0f8081e003e08061190303c00700300c40c496840310020700d90b41c20150385401c0700c01002540b0044444440008200d01c0d140d141c03030b0804014240525040d42800e2100000006500c0c1980c0241c035501500907160b44601031401d19100b030356103801001d840c0700d80101400451403100358420080641810f880042e100c0700d4625014440b841075030004025212110b00421 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 107545350 1250 107544100 107544109
    0x30709140414030403080d02120a0b060a0e030f1c1205040201050702010c0201091802040f090513020108040c0e2e0f1a04150305070f0305040f030c02030a2001090503030306 76
    0x103400c194002c000c2003103405180720341c5046026a400c000c252540001704880ca01c030b1940c000d04440c04d07620003c010f05484a20035002158880103241c0d0700944140305425403d400b070f6010060304040903013074410020300109101d04146028801e03c008003a440701d040c0850ba8015020000b40e12040401c01480c1007540019040d4010648000c2c1048454a14a4216403045620070001d0101e459085c41030040f0b05030f140047d40040c050b1200c2a0f285850000300c0348018050f1703900800e010400c00e2a0504545c004440c90040240181c901740040c82000034004d500200e0349204200c43c8022030989049004010050a8840001a044d42c001c5005129641660f002401243e01071a240007101400b035502d0000350084e43d110f0108040480704600025406030001403060005a0b49c080218035003075020340071140107031805443c071030154100c4000240540601e840381c134001400c841320f810b00c540ea040400542a01803042c00501c00340b402d001d5507040749100d0003030703c6c00310091400c5103418400728 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 107546600 1250 107545350 107545391
    0x10603050304031419290402060702060702010c0f060f0606050a08150109050d08040e1e01030b180a050a050c030f1504060905030f0307090b09030d08040302010e010606090302030709 80
    0x640100401c1c01052000d4404200c00510340c1c10111600e00c09a825003003100342d20224081d004500c8050491800c100c260281000c1d102d554024039480c0ac1101035001d2001d80c2e0040c540403070511100d0108400460400204901c02520491020a5400d45526045c080d00c42550100342800410712203504040d40040107542d1102042c401c04441d22aa00012101301d88140e0040390000f04980884041c4540f130001001942c1079140e0302110b40e2140b415801d81c5a1203200001b0341402c06038010f0002036480004560070003850f04d017203203060311301c0c00b9038070300b4001308980c100c0d980d901840d100c004100060004c1360103806e048025220b03445141400b0b9440798400310141d420045150001810071429502c1072480580040440707459001d2030100c1c001591080e14404003203204d20a001071825803203803c4441d02d080140151030106000c107029903d8060150046055540310345200303080e51002d00c108801440c096913132840c010300c1c50050605196943e0018009141440300b04c25442e070200700d88 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 107547850 1250 107546600 107546603
    0x10804030f0806032401090501050909030a0f0201060506030f0405070b03100302040905120f0c07050409170306041d0d12051312020f0d09090c020105090d0302090303040b0d0c1101060305030403 85
    0x3180c10382e40d82000080c00c1c9107440b946400d1180c0d0003d401d0343c841d030345d0710042030503070700070210810907647c0303c2040160300c0c001100d0010b03c80c1e00420156101c41e1064542100700c1815000105055403214005031094104855a03441ea01c0103200300b00501030f08204407001032003648103641c650f091600c000700c0100e42501000e401fa42d12042d00c80700b000004c000b00b41c80d4440c02407038079480700002c0c2100b15160b4011009d130b00503841000404502e500d014400e101070306520404100c1c3c0c00c007102c003243c1e00b1a0401800281d009907101500c01c4410807502038400300011440240c0043c071400d80b0054001110001c0452200c4d203003000300000358158000310340b4013a401c111403130000081020120b00d4010041499115070141842c202c2206400202c070000b51150781f034090114801003803080342203400032079031042d096203c00c4040303022601960042c0190740015094919207500c41081025540c0110411600c0340e5aa05980450551043c0c0b80d00050421500a104151940d16900c4e40c90059020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 107549100 1250 107547850 107547857
    0x5100c09050409140a1101090b0a0503041101030e01060830030c09131407110a0507052106041101080609010e0601120e0a03091502070503030f090609030613050c010804030f 76
    0x1c0f442408840100040300506180c126440600c1c0d91408103d00c2451240090100c0e0140e0307c08107103c140182035548180303543e60b45604603540d03511008107035080c00240d5414555665103140d5814800c0c0202c4015050007002001068840280e910b40c1a0782030803a400c0101c207903443c10402c00801001c4a401c04902600b0701e44a05e05c01000405186107090f00507070251a0400390741c0c01446c020481c13407141341e050b103a040e42201c1300a10503407102005c08000f0201d81111100344210f2810941c503011580020303c9000c01005458030b60ba00d81081902c003610faa521005000c801980d0000c0f40c44e03400b400981d0821619450b00707007110004440a03210905001010303440782c13100080d41e8000c040c03074224001140d565400e47d05001d0308070304241c0170b0810388420298414401d28000030310b507001c880700640250304c2c101c0380d42154841a0080720031140c4c8518100b204c81003d07035003082180d01400307142100703807010513203403404926050750b0150b4981486240400c10002c20781002250028850078103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 107550350 1250 107549100 107549111
    0x7060203100b0d0501031101110c1207090f06050306070f080c070f061d1501050a0b07080403060e060709060315031e050102030a090c1202030303041b0e07050705100c090504 76
    0x1c40202a480c016001914005400700e5080645012500f01504880c014040c41c00c84042640045400100005000c0388580c000d0b4410745250800030041c03090920414151220b0075264a28507084d560300e42c0042c51210380b145410320181c5000d2000a40080050500d041600c0e03100c0c20162038624014039584806101144010030700c0b005011728560b25900120400400e010400c520600d01294403001e2010f01c2008041404a80070200c0581643d0000700210000c40c41e0462a905540c003c0d030003200d03520b40910000001a506004a4411043d4440030f010640b524000050a035080c1e40e11200c100750a14071031445043d4440303da1015650050901c43e480105011440002c2d4403041d0014820340c400420071614410961094040f54800d000910040d6a039484240644005150280d8181c104002042c000348116030034506c8034540501162510ba40c03444154640042112030f1008104000b8140082100611402420441116040144049031000200306440c03034041d2501569864 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 107551600 1250 107550350 107550361
    0x30c03210403120c060f140604020702010302120106090305060901110f0306010512010b130b07110d021314061302031501030c03020d060306060306151a090d140105011e06020307060203 81
    0xd089030091500098000f03002c00d441d20000341440c4420310180e4600b46420440030264925010b41988650704c1c0442d840c06880364002c0000070341c01000c003281810743c20405486c009032090349403802802191101c1088519600f07200e82095001805170000307034500b40110425004502c29a100b05000c41e03142a2a0703940d10b001030b1010b04c03c841030880c40006c40c1c3c0000032038581102c000e1040740758149004155036a1200d566226000d0410014184c808000c40c5956605164000080b8280020401d41500f0300c4901441d00315410b078201046000c120204108860800c0a0f0000c040000400c046103189400500c1071070001820001d1410192036207207010b403152194068400654007600100a001d6a916105004010b10301c0b04546090a0a8800c1e1000c69910421000ca50044148113258404a00b2490880d0b01103086640d000e00711442c154085009411101503544060000107071550410402d176001285600b00c9801c5028030b10700a0026680c0841139804403a48054050303200d072140e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 107552850 1250 107551600 107551663
    0x607050a021c09092c0c2b0f0b04020910061e0216090b040f14010308070510060b1c0606020703020d06020c0111040e090601030b13020310020309030a030b030c03 71
    0x455100c41d484078242881d5024071455100c044d210302da0440034400000c0d80b142810f541b1a605142c200c0c1c1e10013410390440c4c0b4205241007040b441119585071000200102d61307030325034101c99507480680b06c040700b4104020071070402268198028040c01c600624181c5052001000d5151810000e1440003448101112950080003264182c030601501c91301642c2e120917500c00108441502c1601c00ca0074000d01e004011107900c00ca0b4514180f0510840300c50303085450b840640e81c089001200c441c8203102d003404805000e4882c1801030240c00f1000c0341c0d02c558520301e6240d28a44641e07406011072400e4000c000054002507c102260b07410f841c1d988e80380040d0f041080081c050300c610741c5801c2d428030130260350501e4148003d00654039914841b0200340c8074000d500e940d0b1242400f0040040c8465008104400350301800c52851071300c01801ca40f28001030007007910036a00283c480000c0d513403000c240e11409907058019600c0307031401074004100304090700d00081d69489101400c41c0d0003019488000800b041d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 107553956 1106 107552850 107552867
    0x3020610030c1e09020304080304060f0c021e0f07060207060908150a020c01090219050a0902090607060b0a080a08120114030703082a0d020607050a021c 67
    0xc0510400070b002810106a0f094540ca8000107594200f44c001180314500c6803200e43d8503400c0601d0050288e0306200740c00003a07142405e18041c5150b500003001044810040900d454060b14041254140100d211900f8210300a207203000c80c0003900003a01500f01e82550ba5486429035480440e0383c0c8400003604010f0b208a104c00200d01c3d044c1d070303980141023030500c810000500c0c4803243d80042d5041e510140c030b0740801030080d4001c002624000f529a8018054207034190f14106a141c00610a44a6013200a22890390b4188001854a0720010034010303084800c1103c0307034507000d810a000c0682142d5944030913101820000308156140c14982504843c0240c0200107103410b641d1a2146604408a45083e0300c088151300110485031075000d03031807440e0400190000b0800d9403002810124000c200c1011320a0400c4440300b86e07a400240503411a0100650310401d0040b070208442410 = true := by decide +kernel

theorem cover : BRFrame.Cov 107374100 107553956 := by
  have h0 := BRFrame.cov_init 107374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 107374100 ≤ n) (h2 : n < 107553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
