-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4583
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:05:21.795705+00:00
-- url     : https://prove2.me/submissions/687d8078-f204-4a80-b8e2-745328c842c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 824100719 ≤ n < 824280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 824101969 1250 824100719 824100727
    0x7030f0515041a060a031e020406080f01241d07020114040b01050a05180703150906081b040b09041b0b120405010b01050a081308190c150905031602030120 68
    0x480001c6034100c0d0480003c484c461a0785246d951156000c681112245c50042c0c0050405030555070741d5488040207007610b40c02d0b070302610003040c4100d000b401c40c6510044030007210080502d031520105128425240034901503241030035190241e15032003400900c20f4045649803444010411301560307100d409644901e003540460750404040000b0000700f5006a030003000c201000c0888482d0745506aa0044003d0074006021020002d000c0440822a00000102420000300091843c000528004a0980d080e401400740083c00200030a8600b4041c030254050745100c08100840c02080c607040c040c100780c81524522a5540c0c00c0888240c000d8495012241c401da070802041c07040030301a6001105007441c4c0113180c0900c401c8040c01c0d04102400303041e17880b4492103141c4100700f0136500711a41000006030010031030784440c030000e12100162004a540707a0002e4284d03010049a40248008298000c02441c100074101c00c0002003010340030f9003680e1541d01c0c0ea500c0c4040b0310040291076090000ca01a440c0c0d6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 824103219 1250 824101969 824102003
    0x71502071a0604142421060f01150e2701080c04090b0c0a050f04080a03090609080706081302040213140a0b03040201050d091205091905010207030f051504 68
    0x3401c500a110034000c0e03041942c90b040c480d01001007541e01064041e000c804843c1414407181da040d400700300458000401c048000c07411883c141842c08400c20310b4048804130b6075901000fa030760341028400e9800c001103030700203140710314060f0180407080c09002d4040c080c110b641c00c04000760002d6110b60452a6116180107000313040050181900c411310684060140c0b905584e2589800310008080d0f08070040301107141004c05204800b00c2d140c0c40190a80315440781c0d15100050744485071024101c0229551000c005800b6010f410b9500440d16503c1c09800d46900e8402d0503503400c0b00052424580e45108000d4500698031440034110603102d00322545021820314080720304041a9490702803040d20749071030401c030582d030380c00442c3d07446036080c40c048e502e840c502c6011601500707020380014a030b881140c28144010341c0c800094007107402c0850ba9901061110490000c0040440c05081d0050308034031014004281e0034003101c0501c41c40340c2c080352103022224400c94800329027034800325240d10f01d502588030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 824104469 1250 824103219 824103263
    0x305280903030506063f0a020a0f020105090d0c1403031509070c0203100c030e0703080a17010f0302010f090b0c0102130b121506070503030c09011704150207150207 72
    0x13500100a442d554604421480e480000c0c03611406844880411040d0b403000501e1075049400120341c00b0820003019043c11a51030001e900300800f1003001a148080d8020854414018540944a108050207408110090440d165040c0031000d56402400da01802040e14040000314880e070f005000807000c41d1480c5080101141024041004004820a00c80c0242c1c0e00454800110081e802c00007032121507d0038160003514048074070307032014081c141001050200a00040500f100c1650302c00f018240c03a082d0304a00300070b081c052005070b48000242440107500454a0985969690401101c6c03141c0d560501403182c0e00604800c44241d40100769003502807a010b0080f000381c501c0c00f603e0383c2800101070700c0c1503540c00c00401d915248454450920071a446144c00c9a031a80d0304240be0303035524a030180d28899a50b000350f032000d0010342507203001106070f034800d601d0324081e950081e000308441c500104a4000303900b1981c070541d90015030340743c2e40d02e0103441403000300385d4107210301c00003005101c19020800e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 824105719 1250 824104469 824104471
    0x9040603051605211b011b0f03081b032a0a02010e19110103090c0902070b01030b010b03160f0314040b18010612030c0f0803100f0902120703052809030305 68
    0x14078010ba4500c4054041d80c000c20018101c91124003280c0c183e10050700100c1d1014140402c407080703044c00400360408e101800e2814800c0c18060b4a0b9200da0392101040702c003d200f104081841b0114081c800301750802d914208084403502c0700500880f0000c02c6130350060079a0b110340c2c80702025070741d40c2d014207000744010b210b102c0680950020200c841d2050b9110351031300c01e0704030001e00d04050341c40c0712600400c154213a403807015210b08001192641220314023410480020f00098804402071400004d04903601411030b80702d2140ba409050107090056000d82e01040d0040b2718070185510340341822290f040541c0703124810750060b140c0c08840e052410240740341c85d4000001400a90401c4020b0202d5240707442c0c114011581844c080002407a1418214600b200159009000301c0000003806841401c00b040a400d4030710020959840540d01e2032000220710442c4800a40080000006240c8902903409154040c1c042480d0b00c0d1036490b0180301d03203d22102000c0c290641c0f641c5041d00014164944226 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 824106969 1250 824105719 824105749
    0x80408030301030b0646060f03050a1b0818120d0c0804030f0e0310050f01030507060306080703060f090b0c0322171c05010305240402090402040209040603051605 71
    0x2628103007001c8080e020101b203c005106414003e021440d03107242ca007a0308480880c00c00408400b05040c1c80303c40c0284410000c1030900700003800e0a01040e40240203100e01680d80100400014183c1883c0000342e450140084c0740300b050610001c030003414a0300600801c0145480014025075500078081601c0884500880400801010108200010350040c2041ea904146410f00b0110190341800017071038069010046203900d41020180700c8020820301a0340c0c1030341d01c5481540c50782c0c2c0d12840110203e0b2490310508800b6488a0810004548150b004460060b20000c01140404a80e142e100b8552001c1d14581c2e111b000020270841c45031310900c3c1e003079980d072589104100312800e60345440b0a0501030303034055006900005004141c28001038000c1510541d101c1040c00707590394904109440e04440c031040d06840c1d40207246843c2605604040701d108507030044c400c017444e449a4081c00004d40025510a4120759a0100400425010490313214200256134201500358105418022070341255030f10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 824108219 1250 824106969 824106979
    0xb0a0807081e070818100c081312030b04020f070c03200d1202070e040c06261311131b0e01020a0b070311030a020c01050105102307080408030301030b06 67
    0x502c00342c03944010506600080949042c2002c3e4a48131807050f9440b0201d04c081150740b00703000c003c070f58025658000101c07a0f031480c0c85910b400e030b841c1c58070f0400f141c246110080004008074040c0e00864000d0344414000c100c068030040c2000c14010211000d03034000740741560f4282005108000f0452b007401000c800c408400740d01c032240750044010600000c0d14010050400703004c9101034440600c20401c4000801c013100c071866441c01d00d410b00d45042c01641c003442000032070400004212052003010f0104928540300a404181d9600701d00302030248101d00111030340303151030950714156a00c0d03a40350310001043c02c0c40051450308017507080324a4904c040c40031060140943c0d4101e400c3c0c1e000b24034400c1464011001c20665034a06130120000c00d40a0441e2460507400310074003000d0f04103540074041c10114040200540d0b601e40b001c100c03421140c050381c640007445840001c080b4180003100b000040c0100e40b60181454066a00d52046400903000084c480c5d00120040052021105a5581001c01551 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 824109469 1250 824108219 824108251
    0x9040605151009060302090d020307030b22030e120f010204090c1d01020a0b0c090607032705030c060c010b0402190224062709030901030c020705061905040b0a080708 73
    0x40b025108125500c0b9900501d503000c245101540c0300d03031050104180c1d0041c29503034080c1d00c902d0008904401580e4100350821650140c010310280003c136004801d4141d241e40081c0c000500800101595100c0c50209034014212203c2c03600e0000d0016101502204202084220030308000070013a2043c41040141458609254140c1d42d0b00482c041c0d00c81c5030040b4429655030355a00814032035103d00c50b070040d0088400210300c8141a0b001c0c00c5240200d80c580d40071003013250780c03501058844540b80100c5030b15403c04080066a4904840241074008a8070700101d00350341c000001500700e811241201d00c0404140700c00e14070a960501080c0c0c84c0c0003d40001001d02081783d0705041c540c003401401117014034200c108151140c05103c0303440c1e00303c008150745001c4600d0101c161a8603508415000390100b810a18030543c1203001042c00005c0d1807018007411309044600061036030b000c0128002d0310a2000c00c110108404480d2002041344020b561034808403810f1410004042c0c0e03a00401106a0010740c0d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 824110719 1250 824109469 824109499
    0x71a2a010903031b02210901020f150106031b08010905060307080f030307140a0e04091109180105060406120f0c031407030b01050a050102151b210708040c0608040804050904060515 79
    0x30911031000d10081031b142d84030100c580060349000c0209102c00d80b00d101c3c2d1800303201205681e40026050b01c00a40e024800114941500b0071904036046d040c8000c901140010b2000b0f000340d170700c0b00c0d5000b00001e0445811a030f40754026410031523003181140850300300104100d445600041202c4484042c0d1113140e1800c4e03c1e4190051184a10340f2100340301da601e611134002400315041c0420380da00d00040c40242d440c2840e042c4040710214420078a6560b500f050009102d0f46080e105200484841003081030345170441740d450242c90704960740304850040350a0004008104031150301c28000103110000e0548900f542040e06013080143d010324420b46141c58240101d990204248120055449031240c20351101c8280c20a000303110810300e10b4050001c10300182c00070201112100000c4407240440c041c1d1034442045500b82000c41c0c0240030b10108281c208a1540b0a50f203d07030b885809000000d0603d5201c800050000382d055500395041502c68090081130002c01c1c0080030100303412030328405914864 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 824111969 1250 824110719 824110753
    0x8030d050c030921190302190509012316050a0b090a0f0f05014122050c0d0311061e1b040302150309071a2a010903031b02 54
    0x148035456484c0b84c03401c000301410302280b0709441c1100c031081c500000e441c5a20314010000d4105041e041700051040105080c502d00400c101c07106004103940710300c890311881c8203e1840380f803400d0841c04e054008129210704440700c284240300c0076126102030002c0e260030307050030f001c80d04002d459003410350460040d81000500c0c02152050841c0e100d103202c55040403e0601340e00400b038440c1c0d009502440b540c240625004d8080c401c00f80a260a00c2e010701c842d800100706461842c00700c400201e03050304a40050441191484079100052040c8100c0d599981004d02082280d41f0345a0100c2c0800c0540c912444001d2040c04401c0c2d01261842400b208010300d101c21204104018281c400c00030310209401941070102421034014503006400500b401203443c00b04100365104481d20040c5010700360021030820010301c4a01d103503000c44040503040c4401100300c1d0050707600e03d105a800c013901410107646801028000c8090560094a0018031440500380070000b624401110b0021504089a01c1d400c1c081e007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 824113219 1250 824111969 824111983
    0x8011d070f0509091810020f0d110f0f03060405090c090f0a09020901031b06050f120a06090509010f0b0f060409050c0c0303010314100902280f08030d050c0309 70
    0x103518024808101c802815a520301c41e01e402c058000d2603039020802030030b292220381d2a25030b82d06400c880d503020312007003a07208a00603104070159034001080550b0030a0304541103c000c5c0c11281c2c005c0b0f4540210310b003000126a20103003048100050202c2000b680c0d260030f01c1081c1c0d0100241003e445050290400600f0200b0000d0106440c005005e001c0b803900401c3e580500403569000d03080284958680c00d080c41b400c0c24511b004030000c25501c01c0480c03440d20840a0b500d1220a110070182003070010034140703a255600034009419550782d50800140d651660207402d02410f503110000501041105291040c0d80d80e0003003080c0150440041908191540700c100c1d011200045c800007682d440f540e4042e40144100d4142c82400d21001c0f0000c03050000a80041c0c0800c5160030480e0308245010760f00c0c0c6e040e02d494004c083e500807900d942c101d500307511501c00054010050100c9221043d10383c04003505000c03594000d145913a001080c804e00b4171f200d92040c581c0001c041c03030116081d490f10300d1004d991418 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 824114469 1250 824113219 824113231
    0x19031803030f110f011d0c0f030d1112031602071406041719080a171915050406090209011403060d02060c03071a0405061e161106070903020108011d 65
    0x11400040c180c07608014020484c4590655009000140d411400005103141e101c1d50522a03008989000c901c61902036020240c0b040054064104075104080698200c448080c2c1c40655008444862164000040065101d4520041c0100c40f2140d0307000024070b020040d400c0241024491442e03030752203075110000c0d0380c11070311041c423040703805280300707101038202898040003801c04003440c4908000c10036000051b03e43d4510a54504a0005100c0d41c0d540c62043c013900e1b49201240034ac1e50310001035480380c00007a44112603128113400d09a9620105086407055407081100c01da0215400c2415a0302c840d00302003441c0c4913020b050460505030000348401ca0791280003407150070001103030318802c2014410745840035000040c4c0d50314903a070286021411601100e00705d9a0b40103101c0060440d042641182c06142d40c040000700460b52001c001c0c001c005102500d1000f4041c512500303c5c0d00000c00c2107035911884c0e0f16544c00003101e181d44005070a401040c1c21030440a040480d102104030303a0302034443e078004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 824115719 1250 824114469 824114477
    0xc0503130602090d08070b07050f09040207050109150203091b060d0c09120501090b0a14010e060f0301060810060f06020a03050a0e06131809030e09061219031803030f 73
    0x50007403415500a10540d014580c00608018440b810b00071028040d18090b401148042c140d0380c4c8041d0121002c0c0300b00c3e941607400c4d26007400041c220313081c0f0780d025100303181c4103c0000405034143e4440504981100c640000c40c2500001000950388040c001201c81510300e4030390500020306240025014000d1000c0d5820a070707903501e8001540e51240380840001c120350004509a5134003410080d0180560304c01c1507511a50364404601450310510980388803550301b1540f00641d90070071500f045281006000c0643c050310014825680313030f41c284a03010050100340014800031007110030000585940da0301c07540542200840c20060709402051604510f54145849541c4001c0b140082d42c00503654901d0580140c804a20803600e114500381c0315080d142c2000301100013818021403001a2950600c00070300040c03400da803400c0340d82460b0300038a8104000800c08a044401e00e90381e070703161004010715450458271840c80a0145038101200766100480800410b803403500b5500c0c040d040441c0081020300304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 824116969 1250 824115719 824115751
    0x11100e0109090c0512040f0c1406090d03050d18020f0d0503120a061a090307091b051809130b0a090812131401092009010e041110050714010c0503 64
    0x240784510b0842d207860441700d2242140b03040500b88903960030030707009049862082d5580c000c501e013015a034204890541c0100554505510349080c400c0c3c1c507400550480c1841414080d840000f0941e00404000c8111582e800b0301404c4103004002c6845080c41019006102e104800e10100c0c2c1c011086841d0350034403950000707298440c101c0c0840109402e030b10240c4241d0800c01c03003110001494005002c1e0840841c12228072a4039070001c082141c0490300c2c0c1003403000d5040c501001d624007803800b6285100700034003000710720030b8420f0101c0c0403000d048a00700140c0041200c20b03410000a40a0b15800896501c02003102400c140e80d00c0002d8440c500c50341000c0912040040c8412000042aa4042d0b0b40403200d540424214240c903400f90040745000c60b40d01034050b410101c05440d2130104200307000b00400110190b464446025601040500190342c45060b80801800303d41700d030140801582c4d810303038600340d8826842c10b064944480340c0f4507c1b40e490741042111040c4a611000356a0084116800031f111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 824118219 1250 824116969 824116991
    0x6090c0c070b0d0501230a050111031b06010321092706090b0a120b0402011b0804060806090906100e07020a0b0901060303140f0703052511100e010909 66
    0xd08562030340038540710750340000d5421000103d074110310b041b1040c80f01004001549048132940719981c0030021a000006030804002c19807080c0400b400e91403004083c0c0e841c142c3d92044041208440030701510103a0f00c114010070800c80400080c1000c40d40018a00340242d84401008290003018803580c0301e81c0c06008a400742134100584900c8203001124001c114a90340c03544110040c00703e90440c0c501c07605503002c0000f0b041076900324202009a0102d030300d4031903a6071b603030065031450701d8940e5104032a20160450740c00542100003c1c00548020785841842e440c10000708a8844001489810150005018000d189812006210681e8102c4d24405030360340c0c0d0107204900c1c0c42100355018110800c1035041c400160340643c48001030328007aa0320005100403c004a000c00c5c8030f4055881c8600c070040050101207403240f005044400d41c00c0420b5410b504c41c502d81200002d41c0311100f80d4400c00350807000b83d014684210350f8104d840311414402035410110740060002d03030480c810080d07070b50b441d0800405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 824119469 1250 824118219 824118223
    0x72705070e10020703031b02130e010204171006060309110f0102010f0c03061a0301081e0309060304060b04050a110702090901180c030b09031903090f121101110306090c0c 75
    0x307001e800107403101c402424081e070b0084d5610b107148000e40218000a1a0884804003d1482102d46401a00c0781e001c0c0740703681349075100a01e441011402c07035550a20000c1003a1f13803c1343e0001c141410850045c0f4100d5101050b060498400e42d100405141c9408034810004d008422400c071500001c4643c66441c404850050380501031004078030380f8181c034000768040010b1b050351001041e2000302c00c1640b03914a0007000e0b000548000c1c014032030a0344c40691805440c4400c843c207001411880f030281c80c2003481d01c50128100360000d0b07400712100d5455001140ca5400d10780f02d85a030204580b41e0a21082040103100601403280b800040d00503070540c00000c81c0300100750410317404206402070800d080b025a08108100000130702007222403a210303a01041c1e040200100396120113448606483c19121815019001004040d4045031603040380702c4490041814080c2c281c0442906c1d40701d1443c08464088100e0031501c5a4a07070900c1c250052051004c1c13611b82403403103270b0300c081e80040c8e40e5039620824039024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 824120719 1250 824119469 824119487
    0x140a031b0f0b100308040801060911070b1f1203030b030d1701180e0708011b0804030e0f040f050c090a090212072712031e17330307270507 61
    0x117001c0307140c00500090741d60300542c8550212a0404000c01c00e1400341c140601c035621a001001c0d08845064001c5000004445480c5400c2c01c0060301c1c817401036035180b42c2464000b0380e2200170b034007080c0d4072034110006007010712401e0410101d82c64810000c00301a00c21040d0b113001800341d820784501a1540039451201c9500c00c18050035803c3c221820650341e944054041c2081500c2d0300758176003a013220b644c49075002c0c10845005940c907442d0701d54070910600510002a601e481e00e2075006813900268040014144035840c0039a001d80c004c41e6550700300c0002e203e212181e55106418203481040003401c0ca07610001c40c0c9411080902e40350700ca1140258410344c01e011004e0b00d80d40740e45600c01c1c0000d500c49591401c920741c0f0b4480c0d160041d14486140f502c050040f604c003444800316500003409800d41000c0d202075640000c0c0810900141180c440785e0400c0700703100095120510301e00020b111032a00d020011000203088031001402c04010000c00c650000b81c10704c41c100c0303045485402190009001e0302400e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 824121969 1250 824120719 824120723
    0x90b0a030221150913060207021f0f0e01020304060905040b01020c030607050307080f060d061d0a0b0105041a010c0f0c05100518121216140a031b0f0b1003 68
    0x1075000e0b4201c0c0d6450084681056809904192210015210500700401030034440c00103480c66010110700d58540c82d019601411040741d20a0388108080c4411500c50710a074407204050365003019450480201901e607000c20a2428117661050000b00300711a80325040b94150f4000f0707140800c5180c0040c0050f86000c1e80362007540d61601400c000c0001240d07011020314070880560745c1c0c0c410103480b4172101031030b80c4000751a42e50700b10820700d402001003603c9811010481c81e180000c0b1005840c2d2401c0c40b810140e0501003222900449401007001f8981400740b019075010b40300c20100d03601c07400c800180400300c84090080140507840f100030144107014010400501c000351442050711100300004100f60f218411188030084283d04d441c02a05040c41001003500e0810000e10000b04a03003212001900702c009400b80c0d6440344080301d000144406198507803030300ca100040a40320018640980032220030441040d45a010300c00031f001068200307030040300c12504649044456103c041200d400c2c0b0b4416000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 824123219 1250 824121969 824121997
    0x180402041d0a1e0c0b1305010302190c150501060903051e0a14150f07031505010e0d021306060507050607080f06041a090411100203090d0206030711060a1515090b0a0302 74
    0x2c005007410110b8000c000e483c14410360f1404a47d1150015001c901400350b40d0348512100340c0560409500070443d80782d0103402000d80e4181e81e80b4801d40801514000d07000b007000a09500300801c10000c0400c0041d90185160250f003640c64417403071060756501c641c030202901180403d60f021030070003814401c000710101318080d1400c252824000c52030284905a40e04070000b881c004009403c40c0c071070309800c0140c42059480240b000070202c1007000c00c0c040341c1030070781c0d00101d00e854240510600340b04413001051a0307241c2c20b4a03091242491400c0104c000d01080c18040d000013000a2100c1502c01c482d4071000c12503001400d501c0561240703200e030000f2090b59421281101c03e0205000c00316505a0724201301b2206400d26160124080b40c80e402840388098202583c40e50000041c9400005503900000500d000100302c00e947d000186050002d079200c10045540786e801e170b800005e800310110301405e84c03940041c0f00c085179203000078081502882007a1f41c100b0041403810140e03100307404982030654030b206 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 824124469 1250 824123219 824123243
    0x20607050a0b1b1e0d06090204030506220302030702090c0d0e0a020a06030e060a0b0303070206031009060906080c10140f0c010606080c0403140a02180402041d0a1e 72
    0x141c60011244282c4502c010007025030035941c01100d0358012280c0302000e4036031210040c3c0440342c0e204d525070403c106001d182030300c0300404202ea00e10380c400b4000450040c1e0007030909040110300c8603440b95402c50a218032002400d4030f400840c1d00002210350103503054072410200d17a203c000b5180507000d5000603003841420f0008141c0094800500380020034001c81c1d010b0b42c115502c1a099084130b101018040340b07a000791001802c004501e5000514902025060b6840c003220703640003807031990080303401c44140c214296044c400c80f2600c0c441c0f68041c0107003410400c01c0d1030918140f40c1c2c1d911840c14140b07108210341d0100380360461140d60b10020070b00c460300000d034071880d4070301242010342c0105008080319813030040c000600d5880382c100c080c00380d556003099518041c2151500f550181e0840d0414606104030415030b03005803180b28507020b03050048420b1100e107081900c1000700350703015041e00401c2865030424031610500302150301101190b00403500c0500b0b1080244070801040d0b440740140140001071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 824125719 1250 824124469 824124473
    0x8030a150b0c0d0503010614031b0406081008060c070605190221090d0504030f05250302032505060d0905030705010209090c0a0507030f030b030f07060f0302040e0c07020607050a 78
    0x78040c02001e0703002c0301a500d15050360790048031140030900c2a40000741e4518803460421010b24001e40d0841d40f0b03410025858850701400140301e60080d0300100000d900c0301b04000b0f0010300c0c0495980504198001390030903090040000085004030700c0050304590382c900114a40b898084201a203100c103400c1c1c01c1d0b4482c00715404070601c00301480350103401d02212134002003485a02145000691840340c0300c445c217080c21901c03403c4850bc0c000c81c2c11102442009520f03490740c1c140e800d517601e00f09000d207140c002503030a510605007050110030001a20540c40350103804860003c5002034242c0300c00761800360b00e4012201501d405000000300207801e0b4000020450b00b40403041d001411070302c1c2c06403a40c81c000c2c0c8503142020017602c00d610040000960a000100010b1322580b183c185d03111840c6800b00d10701c6822030000781031220804802c04240d01ca00340800c1950b401503404da05580103824118186032034400c0d00e600d0004020400c41ca65400021244210344d01c00d02641d05041e007040403201558018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 824126969 1250 824125719 824125739
    0x903011b0201021b01050405032203062c030306031f0906050f15010c0305390a030e031605040b04060b120a062102040506031015050a2108030a15 64
    0x1013164142c00340d0048142403044050054501555006000314034214036110b080113000a5184c4c10702108040400000114485000c1c0044000350508543d000b008020b4000401c5e041001c2c00c6003103608184108901030741c1c0030920700707540403141107801020500b909104000309000300d0b00501c2585000d040c0061340e051805000d02c0b58040d00c643e00d80300c0081e00010744842100c440c004000440410a400c11307500c03400441001c0182d014002c0352840301d004404441880262071121055101c401c1080c01c1c1684801c01502c91007044d0068601c8180c694a02c00c0451712034094580550f80311074114400391030301d44c0080000d00c00210229103c1c0303900341482c80004016108009441e0500c40d0108100c2a15602c460000013190103c100103c8a0350030301c400350400408090381405024406248041e6a029200500c842045004c0b41c2d0340c10502041090050394100c0302d42c11f0f042c018451071104803540e04100c419000345515803a95281e00780d0750068030405440c52252480740d00c0000342041d003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 824128219 1250 824126969 824126977
    0x3071707080c01021518160909030305160507030309080f0307050a0905040606050d0e150a0e19050a14030706110409050a05040b1504180b0708100303020705060903011b020102 77
    0x907038000e50388046004001280d80e4500e45a00c5040c034010039010a40070060110104049101e40e81510140d000c4854003a03a26981f41d1310000c210b0f41c59005034010180d052242ca5801030704242003110800b10064002d0040c0508100101455614200d44003401041402e94611212140425560749014100100540c2210b501000422a17a03000440c20b4603260040905441c03541d5181c07030907c08901d1180c00580510303991202240121459481c7d01010200d030a481000e4000d4042801083d06e02072501d04104521005c60940030715198500240c00400c1c1d8403c0c1a03000852202c8488080c28141d00314400c41030700512052034442070034800c002c00400b4008691500200b0040c981e98a4480000e843e01103074000c144140700000215241017044104070503541c041c0000401c4241d41c42d285050606091013960f64030480004c010096038803001075a40140c040c0e102170011850340d90080d44d568081d0041030710a0b1001700303032a4076588095205005602015001c01000b03036140f42c0c007034002d40c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 824129469 1250 824128219 824128229
    0x18190309241202090d030e060d0c11070f120305070201091d0f0105030a02010e091b03010906170a050a0f08121f080f06010b030c070b0106050c160302010e0d0203071707 74
    0x42c1d03a240b50b40341005100f03540050501600c0c1c01e40b811080d50b0f0444d07603951040300f410b078410018004400502c2580c401c020b80390f040c0c0c2e143c02402d072a115452900d40a0241d10440030880c0060050007690f4100030b54400071a414209141c0721415031005075038404c425000401c0041e034004010b04170b00322880b100ca00610000c070300018140d0b200d009250711900d00200181c0820003c03040302016050004006602160320900720900e42084000f07042603500070f038000d4183e5500e600040c04843c554400480c0c40c5001d420060408030001d9840743d0302c07034000b228081c21084191896106000c0e105013103803d460072204910f41945440000120400b0320700031005001400032070040303040c03240082e250180340e03030f10b20042c000b980c40c2c07400c83c24450703100038003517111110240451030000301c8000266010700f01d1070301c0c1c05464195001d946882c00280204540c03142c54804000c10250f6082080c0054500064503020820700081c0086071604c0030507408447c40d40070104481c80e0f086c4d8080303040310603a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 824130719 1250 824129469 824129477
    0x412030f09050c0907210212010e010e0c030a02160b07110c06040e10081e0c06040506030f04050a050615090901020301270906020d141819030924 64
    0x54031101810407a001401c00800c10342c00701c0b0005883e4070300750341c00681c4010f003860b107059030310880c1003d004240301541c15241a1a00418061224134540b40410301520f2003509440c1c070356140c8410b0031f428250180213001464000000f086d114925a012100000b0b0f90321050126100940350071001c4100c11501000010b403149664804c1d40404501134241150013013586042c242081d0742c0c030803d904081c1c00090040218180000d06031020301c030715001138820011001900540c2d00405051084010080e0300c00c050401090003a03a0b0b800c4140c0390007024100d4590079681c2d503450b01d0b928020549102030170b544600c00411110100e10050403c46c3d14080d6607880c419140c2c00201c509034042030089094810140c03028955400c4040440c150280910101181c0d0b003245464203000c82e401880480d1400362030340468201401c00a6086070000e0348045c001c10700c0301a04c145692141c0942c030319031118424038500750381071502c9210070b0005444089003aa000d940b8501500c0c03288255191010045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 824131969 1250 824130719 824130731
    0x3060c0405040f3602030a05010c08010602070b0406050a0e0d05011a010507050601050409020a17030d0b010c15020d150801020405100c052d03130807050f030a0602030c12041203 78
    0x20155034040e140d140091810a6a0b41340500614860b07540d59034075514100104e00c114400250b80c007044401c1d8014003803400000c2c061040c0c0b0300188030510580010341954800c5804101000000e803c40b0200d644a142031364a400b1000030460b03100589184943d40f0200e04401803092080651052101c40501c1c010302041c0c1106800540b29800760750030150060b004000104020305082e0031010100c3c0c4010320b40c4803002c0d11048454a540301d00708001945034004242c09005080a00c11003030076440900303048a0054160390b5100f5403a007514800400d0307507000300d82d440400f4256040508656846901e162020b41c40b200307454000d4000e0f1141c184030b43c0036a98800c400c0ea00800e0381075081030300700c8043c08041031484940700501b41e419041c1c01c82d01c40260344007100d420051001d8035000d203504084940c843d140140d207a2800e200364106030301c10044445420015580005c000e8240c0b980314a000da240d07600c601c0e03031f07204a0080a001c01c0300b408004007080100080340f0300c0300ea03840d80f00303403820040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 824133219 1250 824131969 824131991
    0x60a18090c0c2603040b090106050d05060403230a0e1306180504020d0b0a090c1a0a080c070c120c090203060d031d120703021203031b1803060c040504 66
    0x740c81081c49601c001c152002c0c01040070600040d180500c10740a600502c600c07007007078070080300c290b84212401d1700c03550046000e10a880c9030a00481d0010705044414074001507042d2501620f0340c40c003400040c18000e058007211621414036a00c141d1b90340a1824031038403030320809809041146007503110b03803180d2040d032452840c4013514420b00e400d99140c5c900750000810301090310310081c580644180e9111350704901100014000c10400e03481444405408030325803003545048681c9a509800048000c2c458500e0b2100c0c403004101601c99003811032030f1a140701d4441c1440380401e0b00c22980044c1400496103000b0070a10511001d40c0725051180050008440e907580300300c01240401d40300039a1240356a068200441d1241c20311800003034881b07110000c2505910002800c21400700b82030700c03050304070300300c00c000f589409004100c0f640354074000740d80b441c03070321a60203001400c01d60140340c28820003103490640d80c0602d52200600c2c500180c00c0721214246100040c8085d08280302c1d1034855800d0002c1000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 824134469 1250 824133219 824133221
    0x20102070506060d1e0303090b040804172811100203031b0f070f1a040c0603110403052508010e0c0f010e030606060906070b011202011e09061805060a1809 68
    0x194164100302017001000c030a84000c3e60341d50044409408040d1280f00700f50208010b42651801540320740c4d5146d64852500030100c4684840e240301c0308194200740e0348200340622031407080d0384604034600b05207202000e03071910700c2d4107003d0360000d01e400902000801711082e8000000314095049118200300070154090309454911501d0038400e40c2a005004800002d20f12420600c017040c8180712003080c0c0e8000c504981d5014404070f4050ba805803d90508000c3e50b0340501c80c40c9071400f407881c012880c19065443e6240d1b00c1021a00c0000300004103a001040c410007401500041c02d2864000c1c000403100800103a5150165034030984154440180c541e41036002c3c1c101a0000c2a0140190485555400c10001c6079000900d03201e802c00ca0411440c000140c1c110603250282c5203e2202c01024842d80c0001040103198032400c696007000c03c080c540c51260004980000c0350418039160147e07054030140701e40c8144e819030065401070008102450707295004042c088003540421042e12120395039a403800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 824135719 1250 824134469 824134489
    0x11031506031608280f051e01050f2205060307090c080a050403120f06090e01060630111b070b1e19090e0703050c0a1d060a02010207050606 61
    0x140b580425084a812450302030035405030b204818441548103210b40e854045402006010f111403405c0c5c0d155042c140c4e0180d144106500f1100384404180428902c45100e0500441800b516200c7d008034022594182c0d104000088400444200d0550a83c52000c9440103400709440c158482e018115010460300782da8400c1180b503e0700e60b501c03e2201d85482e0800d000409002c1c00c10383c200000002d135401a220f46000d1043c40f4072100c3e10002d004c51401ca80c91b03003210766036800055140d0602c1010450564407404c49450001c00020a03030201030300082010310901400b25290b0720b81c1c1403030a140142c182840140281040c0c040d801c4030010b0b4100703101034940c4103e0040a6540405003e0301086281200b26030342c2c1d540200c1080d0f0b242115408200b03001e030140b01004030000740a0b190034494052452310781e0390024003a04081c003880c204084c0c0413620340110b6022034200802c07503000241201d02010204071005014189660311009100003e020f5401040c065480d0f22404010814504140002d6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 824136969 1250 824135719 824135731
    0x40204150f0e0f011d031e0105090a05030403150b03190212070503070b070602040812191403070e21010e0f120d20031003020a0905371103150603 64
    0xe07540c0c00160401940c0017034810001a55a0941e0004022562010800b08540b600d4440d040d82c0500303d016103c5094410082a03010705411203038007140001d400009850070349902c06c4403c0c6030000e1422401c0001c00305810225814840c039942c84a400c41c03141602841d06000f42c50140c3c0a03001e6420340c1e69203102e01e1144940507400321078100201c03004c0c0005484018450b120241c43c041d41e901c503007481c00042d81b0780740780c030743d440090540c041206100c000e200300345c0e0600b450620440300e1304102441c1c3c00014030213018801d1040c7d2417502581d9800640003118481411103c4802142d80e080e4020481e500c441016403048012a606500c80020040941900000340e0791070210400010000b911418044480c044064246000c0c0c43ca070140141d40708a81c100c0440c14140d28600410030b5540032a070090b03191038039140600c04503160554611030031900341e6550300800416401c010b8150241c3e0341c3c03010359003490000080070700004103005500a0464604010080442c90200060b6100603180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 824138219 1250 824136969 824136979
    0x70606122d03050a0233070f080c030a0608010903180927060603050f0606031605010804020f120d03050402100f02060703091b120c09110a1d040204150f0e 68
    0x11074000288288014007884c0b8080c4162107010344011082d0702c101d40c401042c401c0352048981c102800d840819115a031001c070750714001c10310510301c04018028600180c0b0b01e90310250000009103004001f60419001052840c00800c81c0d00b0a504000b00b4002c2d090380c2a00108223001d00000b03040c00380c0d0007541030024004011940803041c84c010801554440c59007228500e8a41c2c1000010510900410391f0700034040e00508001c2c0b606504050030700e44a61031094000c0ba000d10f00f404242d9010380072550143d410780348142a61004000544000c51a50020003540304a400312900a689500071034003861007550291050020040c00b965903c0807800c40720b0042e801301001a600a1098101060079806500d24402c4020b8030344641c66241416000007181c007003000422000c011040841000030700b41c01d00c04100d627120280080066105e41030082c400c218103d40618003034040e0040711185400010001c40d0744581d01c05803000e0038841d8240802c041040c010b40c030940305d070054810880c1d40780c0043c1303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 824139469 1250 824138219 824138303
    0x61b0207081002091207121a040b04021225060e04060303050a140c0304090b1801060e100e0301060305070816060c1e02090a1b0e210307060612 63
    0x701d41c000a400015210b0342c4617021444180320700c0c0050024102400384840d004e0030340708a500300b1640d0041240c1c2403082519074041084081a0103000d11500540d04503402e44140001041d420302d060180c40700d000400c0c10003072000b01e00d204103c000b807040740c455844034070303640040c0d81c00c00045460901c00076022a2003040600c816a10a000b1281c0f90001c1c007648904004420014a00e544c0080e00070000d01981ca090b416040d2400e1180c0020040d81140d03904181e41c11f28000505110f0f0031503644c1d01800c00d0000220801d4080c014042485030701800030085141d49050043c2c1d1004036110710b290306e0081030501c288000c0016880015511191142000ca0354190740d8680c003040010042c61038004004840e40069683e6000540944c1c441600407443d0405051240c5090700c4411400303041c0302c40340410a049031070f0000c4009800c2c034802000e001c9001a41c05aa055110b860002015245030982c0032031454010a01d180f1994011160303e85502c100c8081c454291080e00020510808482d0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 824140719 1250 824139469 824139493
    0x6010b03060d050f0303153c03010b030f030a1e051c060803070320010b1305060f0d0318090b031506150409060302090c07020603042d061b020708 64
    0x10000190310b10803012281041e140b400e600f400c6410980b84610103003610140300b00203203800f2103c90202c0301d041c5d6151080f03141c000f00384d482080c149003000340c1d600548d05c10740d01d055a00b0752080400c9031014042e00c0300c3d95070030406140c1f6076101d650741d400450304011015110203410303c0c802c1010364080d00c41610b04400b1121045c01c0c1c04000c0d240c41203c0780c480c0d1002c528042c060021300000742c800d44800440180440409542207001c28101016070b141448082d000d40c0d54030760000078081c0143d80001d4644890001c00d9810b001140d05517080101c01307000100b016440032201c400b0840c41018003c1c682c2c1c03030f400701c441912026201154154090241d05640c21000404d00350000802004140351644001d070440c565000365010030307845c0703568082c20410b500702070201c0c0707500c9014000d04034502100356001480b80e000c00381014103c14040054807800112002c484e9806440809801c0420566032a101c0007908010702001c055420f60ba00300320559000045a4094079141030150000202c25 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 824141969 1250 824140719 824140729
    0x1c02150d06030c060c0302070501110a0f05070902070b0907050f180a1506030b0a090204030305070803040f0605040f030e0d020105180f06040603020a02070b0c060613090b09160806010b0306 83
    0x30480c01240c0390340c1e9800000000e40b4003c140c001410030751201700554a8909010341801c405a00503030502201010b646a1008041842e100e11940b2140032010900241040c900c1c0c1003403500403031006840090100f06010340d42043e2407003210020211144e458880b018041014200c0303181c0740d00944c0082c1c0344c1c1e0b8001c50342c0206550201920750002a0020010544010000c0ca40c0c41035002ca50303513484071166801c1440000001d0030146505600c1c1a1556400428900c40d0f028054110580800410200440c1031044103200340c0000f4140b01034246800c000c500a5000301085003c9250041441109d05102c0004c40509405031542410410510071030301c514000020050b034041d080c11600b0b402c41c0e5802c030181c000f0348003964005803100410080a460503180e60050a01000c09000440700340d1360000e005684810b0580e04000c80c0c100031510000a402c1c9880c00501c00445d910800680d07501c006941009040c80303400030003119a035600c615440f14000c1c01a440005c0e02000040c20034240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 824143219 1250 824141969 824141977
    0xe0a1d1b0f0c0307121e180b0a11100b0a060804050d030b1c350d0911060c1518070909030512070e03010f020f0901030b0f0d0606051c0215 61
    0x2c070b4068a1925156554005d9a118441c5100b40410045542d078091811a510b54001e00034141c1171011100d542c49002e008058905c0c40b44461010001a100403600e11034101300740540c03d980104c0300403444000d4020050080008414020750080b18001600713482105058001c5401c03d000d842603903041c03141140038141e05203415412255007010518140b0121402015841c01039143d8600d948288056100300007054460b1280c40851541c3c282205035001c088404030b01004000156000b1240780c04a046590a204250b2180c40030407009644c0d0310200e030b507013045843c047d080d9040d651100e0102c0c24210f9201100411940090828485101ea50784031b0010305001c0c0c00d050341481d08503030f0034580c0076008942001c00070702d542000c100d181c10240a4140d42d00c400300c10950500301c20029103016800341c10b070a6410507032207a16108180d03e603036030340f001081c0e00039000d08501c0c03486040031809008244a414060041600b904400ea50040b110412059005000031640800300e0780b11495070300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 824144469 1250 824143219 824143237
    0xc061207030e032a10110d20040b221206020904022206080106022a01030b060c0309010e06040506070206030c0f180907031b0f0e0a1d1b0f 61
    0x200411004140241d4007144c080c401414488004910801d84c41035401c040d601000d0000643c14404503543c3d80d0448070580761075043c48000080d4150444c030800b86110311700500010400d40019010400c0c241010090010902010004080c845000c005040f840401d205000d441942480f50344000f40094006152004004201500780f5903d040c0d622051140c402234000c40c5c0c00c90700c4040002c0d0303820580881c01028103002400342841200c02103010b04c1c0110b09030200d40da001b007074500401d80c060f42c044040c10b0f078040c00d070303940b10071090a0301683c03540503210950102d00c41400101261502c0d4007144c0940e0005040141803040725800e001890304050108401050148500401e617104003010f8032211031015040c011090b03901060040300f01d80a040c3c1030426080a02c5c1c680201d5032182500c42100c8640b5000740c40200303031081114503019034950070398020404000050180301c040d038000c0e8085c1d030686014805446a9104200d46918005407400c2d0303500a10072981c1190001000d801c80351f03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 824145719 1250 824144469 824144473
    0x15040204031208060306130515092d1902060d051b0f030406110c0705120705090405010506101706060310050402030415050c04060903021005070c0b0403050c061207030e 74
    0x752a030ba0307504000060341c0c4414000400c003908002062404200d0150070203e0183d070a0740f003164036190107458400b01c04c01208680c00380c9001c00c0c8800c104211502c1e9412044040b4040301d020354140300a110040c96400740a0310450003003501c580e842c94003c00c0d500d0f60040100e40391000c00c219110181400422078044100c0740036140c00c480c20f410b80200074000c0760501960b5640b8107403030001e08483d4803041c0c3c3d0000130740520074010a9070000590a081c0e0380225002e0072010300040300103240c05600d8100303d401191050030f00040140540159010b014200c1d02c60855284a40e81216080819030482071a691998081182da043c0700008542040d8100d41345007901e5183e9020a007a40d00907101120307541411042080d80c0c041c14130440340c11122003103032585800d15210b4010035444a07804041c0c49089014400c4581c03500400407120043e42c420741e0414030310341d01c100c00f060940041c0300c2030307a541c05110031041141c40d1039000c580320380100c01680342c510b0b16417010450080c111041100c4040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 824146969 1250 824145719 824145727
    0x13050f07030c0509242103070326190e010b0d140c091b0306060c0f0d171006030b03070305011503020a150503060607031707081617150402 61
    0x12490910050300558000c0190025031407070b09003804a8100000c22a103402d03140c2d900c070101c948400444c0880305a500312034003541d9410f01008a40c00d5140d002a082403413100103168000c140e04824850380c01e003450840000c0c45800c1c0f94414800020446218034100f9840d440204200b5207a4060f0b01105809400040d2140300b0a001c94058140414140c90040198411817136500e010450482c46400507100000c031402e2075a112000440ba44415020003200440080c01503100d03981030b5901e02112a0458243c0203c80400f01d0301ca282036180000084c2103026279980d005104201580144240c05503206e070103140c103034220010814144219454002c0c48000000714200740900b00d410762410303114040462552040090040c036585c0300d01c950f42c1d20500050280c9422000342c90b4088400d0713417900c0c1d990145207001c4034a0303084014806495820032051241d542d0b4002c00f020f1040a841030301d108110303035125040d01c501c91002106160300f60200c000600d500031080d01e41031741c000003070009418 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 824148219 1250 824146969 824146993
    0x131509050f1f12140c040e070501142701110f0307021e0924030703150903230703030f090b04110a0801050a0c230706021324030c14031305 61
    0x1900e148500241c0706280000c441390191007082c00600c00084080303400f0131030480b503018a1625280329100d02414802c103a0b441100301c1c08003208803801c29a030202c402650700b041d88003203075081d860701030181d00040c42c0c10305800101100003490b82c0280c0c042d40c01541042c00c25801c201c0300c405108003c01c1880d15003024100592100c1204a000352030407203003c20308888242400ca540a030f8440030522a500000040000c5040d80d42070303180c0000710020200740350a0a0405075860001c500e034412185402809409603044002e01a0410901c00d507411300a600101c103018043da081000c0c003400d042c09840c0031500040a014070320076820b03806080842c11580d11108070b404c442c01195045c80c1591100c0743c06000581c8030070229400d00c01102c6403030b42c4000c81910b0203201c0c002c0a100410031540021503500000135407a01c075004218128500042030f10b40b40d09800c1c2c0038880c0714000007103801d10007031081d80e034001c4081880d885400300a050450741d0784180601000d0200b4001d5516004196a22003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 824149469 1250 824148219 824148239
    0x40c0c0b0f09010c0c0201170c09060705030a09091a010f21050414010504030f030207060902040606030b1e011b020f0306040827010e100e131509050f1f 67
    0x44216140001c01400b89441c003010790035111810000420414084407100041c4e070801442000e41c0d1190031020155655002c400c942403080d4007841c1c1d40500c020445208114001008061361142c5d41e031070540c12551901310034107540d02c1ea070400747c2000340386140d14050352041d110001c00802c42e15010801d0100d042d09e00c1d0000041b44a0150b28586410400003030003d58910440c10142c001e0007080725160030f0301c004180c4078040003640101a00000d034541880741e150041c040080c1c00a0003085059a1410042c0090046002030b90249520f090091114081042e800f040000180c4072855840180c5a10140c0884034200403a4000351200c403500c06a10f003006501c0c030682c450b64525a6400449030513288440c030b0b21184040c008006030030005c0690784804050710040003030320501d4110700452800d440540c0c5104046401540e041c0602c2991040e03038100c02c1c100102c45644031075594807080e029042c1d0f981210540d00400082002c00ea629036680441880310b010a02d10000c0b4948032142e0304 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 824150719 1250 824149469 824149471
    0xc03120c14010e0f06060d1205040f0e090d0c0b01140a0f06090501020f0309300d12110405030d0e130509030703090e10051009080a06021308061302040c0c0b 69
    0x24140e03542d0301c0030111a41007000403200803c594001003045191103800141040034031a0003e040382120180c20407112701a8007036601400285a8a03450786484256a03508503030201c8000d581d500c0b844020b45146030081e0804604c150f0000b02c00c031071503800c080206140070701040400d83c00c1103074a24006a904444240b400140245a1b82c0b01d0300e540c9003400081c03600d01400c1c03e036400d0360010801c50300d41c2d9566001c3c00070700790100d221a00501c82c40303a01940c4924000d055144d040e001d20346a1503c0c40c4e03031244515854160850003007014241d404403420907030003240a03054156110680100d40940940381c1d03070b020f00100614000202d09640400b40940d1001d4a5040241c0d0010843c6010590800210700181a4140c81c480f280d203081108040034103490700c40c1600419203034001c0080d2a100382941409030810404881c04d880c0c4900d8400000e40c441390710101c4560072164041110030011030321500814281503d041d14803855000c1100900112800409012660041d14006101c00c4005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 824151969 1250 824150719 824150753
    0x1203090a0212030d0c17011415030403020c1504030b18030c0708070501090b0702091602330117060403050a057516090c0306030c03120c 60
    0x1641d01d0b8441c007071007003003541c90450a0800f40906d0780004010411480b00483c1110080700c002800c142501c0c01185100400030384210321600d00000300010b041d00000c82c40405030060399109403049480210702c40038000c9002c014254034229010400f020b1a1541c03014041c020003098a150607580c0d04c1103407400a103907012030141e42114030104203541e04014040700030075103040b45c945805000da0008104480080927016042d13000d00666503901d2082207100d1a141003411116002d0014a010302840c6c13100c802807130402c4120034000b203241880c80140d181c0e1000314000814450b145e03554161000d401000581c0100242404840c00519102d405140032841c802e00c10120615000903561038103041c2200c280c40d159000f50703100f600e0511881c041650012100b140c1000d482000c0720140001c0b030302204a040341c032600c214a40414001821003007141d140110410201140300c8045e0191a50383c400905946605101000459020260500c8040151404481c001c0140e03580c003211308480c07205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 824153219 1250 824151969 824151973
    0xa080313080601080304060e040c1205070903020f03010c0f050d090b0a02030402040f0608101d01050a050603071208040506030c1e2104150b03030c01020c0c010914031203090a0212 79
    0x4100400c1c1c02d0200d940504580005985020b0405070040c0c002001d004407140995a1205685100e41c462821f44554441600b02804a0b06080c0801001d880d002d02090348583c0f014000c0d1441403405206480d2861000e40721401d10401c0300c0c07800c0e1019005078202900032500c0e2180b00000860f06190b49200e1542260016120309003401030004840c296802007440e40c0c035210301401030142c00900f41c0d0b00c8840b04000824500682c4403504038421980c00445500d40c00c0c0b006100d0004410b41100d07109003c00da0445451a6a079124041c400c045202c020b44245001c21060000d401e0290017591721003441c0881c035140c00000b003206000d6000c40a03004440c2c03075002ca503684500d43c1c110203444407070030711300c01c3d04225042c1612054a1007030b100c07000305d1105070f84280c00c81c55a1010b1090360740300a05003008540b01c9211500d2192a050301d00e10039400980b0148000c29206000c0410340c103150b1014004281c42418100d2025055001600d40a9148a00181540140c2e5040c0300220242c1c04440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 824154469 1250 824153219 824153257
    0x20601030c12050c040216060f1a190b0901030b0d381f0305030f070b010b0c03070609170f1801020d0f050f16060c121107030e0a0803 59
    0x700240d207411640c0100080201c0c1c808030308003180001030001c518070b50031a001a640d100c03416854186240d01d030f10041c582070800d0b003103844240c2c85500c001c421b5a4125850103070a1040002c00039100b00c0b1980c405410f40c100324052000c0142c10700a07215001043c140003031000e611600080c541404000210b1382080c00f042001c07130340a13040c0003400c580d801601c0c2004488090304d540c006c041e41e00034100017002140010400b0174010980341d000085030000d0650760340d41404107c681c81a4040e95003544d0302000140005088410407003203400c042c1e6100c003c0e504080341c540c2c0382409006550401e481031001c08800e0100250550020000010321080701c0b0780d14040c1800d80130443d11000e4006044d500020f04840c0200d4020501c0400c5011505e042a551a615000d0090303038056164021400c1c0703008014030040086540c01000c41546035107071120512003002d255010b56010b0a022200c245050007828002406a00f44d0700054000910310050281c8070704030f40381783d81c0003c5039150350418654 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 824155719 1250 824154469 824154473
    0x406051e01260303010602152a070302010b09040c12020f030303010603150e22080409090c050306060d21050405090405061b030103030c03110f0d0809010b06090f2205040302060103 79
    0x40d800c1200100040d50139036140003000794803400c1c00741d041c61840201a0000e0b8010700c0101e10990a01d000c1144282403501c0a60310180c140c00c210400c402642c40c0175203002c454a08040124811131340502843e409034141b000b5004104a0803804036000b011400021400360740c284040c40c040c25040d500081d10076900032054a1707004560340110440c0c1499024000c00488803241171b98140280f502c0b02c95040c00364500031046206a074400b0840300e1030721403a94100600011a44e046030022005c0711115110b820400c02d5030001010000c0220441000000b0001503016a101e41c0e005c41f401c0c01ca003403039601c2c40490103030312085804981c0f41d004102044020780c5401e40e8400822034104101f4195811660003810b0240c8d40300b000703410703c032015011501c0d04c1c00c104020902d44040c0000d5030406405d009001d0003441007910140910350900041e09281c1c1403007003d4078041c0b80020035918003900400144225044100241e01d04140c014050000d25456405000d0003540300382d0041225600d18 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 824156969 1250 824155719 824155769
    0x6060109090b1c0f2001080a14010501030c050405031006081e0303071d0d03080702010522020420180108070f0c02190f0f05090115080406051e01 64
    0x354200403400c5103040c804100c030303888064801c001c16071400c074200c076070080c81c0c141400c070b809401c00020f00b8000305040440110042d40c1141405620a88a101c00341c3ca4451651043d10042603460301d1481a0000400c0550700c6038008403540d110a0418601e41511940441e080502180d03180c100c03907441c2d2604001c00c1004018050180c00450400c0c000540c1c500c07070f440e490f03200181c00c10042080030f80300800c2e031149094994565007030081185218404501e000b92601c5422160380c400f5520300030000c1e818000b0340403030b0041420810005102106aa420400103004c8000629581136818511041106004c402003401003440b801c80400006c405000620191000b0820010010001014801c407604002103407159503045510b00042d4111003a902d4030b100e032a500002035450603040000b082d8031a44903810564000381c85800540c0c0c0c80700a421030750344d0410000c1d00040e1350078002070007142c0140c0c130454006a403040744900703604512508600040082c0c201c070341078035800101040c50030f000b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 824158219 1250 824156969 824156987
    0x504080706080f01120501110d05040303052202241611010203040e01090f1113051e0901180b030102040303030c021908043b0106090f18020a02030c0708060601 70
    0x200c2c6031121092038061400348050f001031280404c0000400b180c5420440700390080c2c504911130500450311415800d4054010f00026038060f00841d00e0070011541c0a07000141d0100d92a21011250f01c2000c07581c0d00344500b030103e00c0712504800b00107a006402c80000100248807031034015110808600050400e0495086000c00650555004010801035031206848550449032a200c0025442070380b09952400341100700320918104600007005056401c4401030181a10000d46581007130305030f548069030041c0341e103540442d070158810004220710321389040900c20883c0c0450012641c406544086401c0e84c01541040703005c45d46681c01e04a00903810412891144910612001c0f5440c6a40b10032002d4459402240e600f50103043d9403441441014051004441003407003145a030003003080c23089401c660203019410016980ca400084c0f02640d880da907605488248440061860000442e84025440140350905500052180c0c1c40d510f9010302040c001401070f08058822231514400050009070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 824159469 1250 824158219 824158229
    0x31806050403170c060601050901180b040f080703050606060304021f0305040b0a180816080304150c02030a0923121c0c050c040504060207020d290103111908070605040807 75
    0x500307004e01036465000041c165000300c1300307080481c4d5405180004a441c01c0d018203040200c007924503000a01c05940300014001c40d00c0340d4140321407058440c2503e549072000362002408940c04000425120301e0031030b0003944c103c0d10040ca4500c0495150340d58000d0004624103090200740e0758030030002030001c65009240d004080010410880c5c0424400c1092159910400303050b104000c10044c2005030030070120071200342c00c850aa5207070700d0035180070302000010844600e00e090a0000c03403508035000100b5200051925140c0d1b02105080100b6426410a001804840305040004950458490a11000b040702201d00079241545003049034081c25005550058100110240328001040e008220546206011100410261283e0070082301900542d100a54025180000780d01080322030103628005000502c1d60b140100180a40a4a080800d20000e4651205249450141d150010b01803450440c00200803148945817400549003401a422540101c0c3c40060203002c800c400b0050040101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 824160719 1250 824159469 824159513
    0x12010e0f100302030a03030c120f090c05040213090e03040306140601020f0706140c03130b0a020c0108040f020424080106030302102a05120717090a02060412031806050403 75
    0x82c40c690100e42c1da0200c94601804155071030040740360180c41a1701c01107425003410414004422504e0300840103010106044480312402c510010300d5003054000d894038046e845003c500c0851030304110b0400f601d126903250007280810440440010128450300c0301d002c03400e003c60ba110340b50550004e0b19040c140c441c4451240d10884040014542c0101c102d44d035a840c00e841103171a4141c01000510b580075080d0303403a9520005040124860001d0f10203030090503130683c201c8034000c460310b0056440307110035038015003600240101000581032a400801d601104072f99898841821130580c0c10181946401404950b510f0300000c0003490b074100440c10300348058403410002d618440795481003c4990744280168007100300400c203400344c007850903207590b01c5041aa128a0f440d0408009040d00c440284104918411038042090040c001070301401d01a40076029519060414146000c107100c4910100c0810100c0e45c401c0344455952250040201182e4840355183e81c254035100000074802c4144c00101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 824161969 1250 824160719 824160751
    0x302090c1215031207020a0e010605220b04050904020d060e010e0106050103050603100905030c010c0e040c020c01020d05030606091c1109160c031e0e0a0512030f030a0212010e0f 78
    0x60380d404112558204181e1314400d1792541030b4808918121265030088500040d21800000c015030080001d1114404d40800d03580d240204620150080010340100c081c0d421050000b80170328107040d46801c0e00a400200f1414054070503549843c00e64145044110040c0d46501c07803848005401d00601000d00030900301805a403400a001c65a2140585003000c24191941a0242480400d02c201da00d0010324400a100701c105a81000d025602d02c850800d002c2c501d04039105c04038034070104000d0038085050f809410400e51020080750300790070107040194003103c10000891540c0c0d0309003230180e0400c0d1030100c40901103c1e5080511180c6070110200e40600b1100c03080010300e136107018400c10000d0007410b001c072100190f400d0031246002c0c442e10307054101d1003036001443d001c3d4020f50580d5010b081100e0104109494909210011410303945100003035105200c00050003600c640595804880144014200b0422080e8014041801e034440d268024120307091040c030310070501c0050780c807007000d4145503d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 824163219 1250 824161969 824162011
    0xa0e1309110f040209120f12030115080703020408010603050f06011a0a0f02010f050f061207080316020f041506090518010b0d0e1e010e060603030a0f090302090c12 72
    0x4041400c0341c400b446092008607105069a80780d06445d10403502400030307035001c3c1c40710000d1555000c1c401840c1046120310302c1d813810990454001c0340e059484029000019143d074200581c0e86c403401504d13a0051540074000400d032030209110f0f407401540035000130803542e400e070010b040c10000d0603005251103031030700c1c4061080499200b045a04031104c0c2e203407103000340d001103408034010f08014600328402403c001c2407100c141800340318640164021208c200051800d0789059503508080d200b51159600700b403181c0040703208441c0380b500c51140084e10070100c0c28070038000241200c42402400600c00d0507a881800901d50210340c1d803001c2c280955170723085c2c03039640741441d02c401d10030520900f0003504000425104013000740c2c11150301200a04200c61002c841c8140312400d4601c0d2074505441980f03854011190b41c0c2e800103e03540a22809006145000b2860000701d5800031901481c43c01c2c0b1940040000c0141c031900242e51040410140e855119180600c1c2004005000340c1003820a03c0c0309541001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 824164469 1250 824163219 824163233
    0x2010e090c070629093301030b03061009110f07050d080a14010b0f07230d17061c0b01141008090d08150a0e16112508030a0e1309 57
    0x1040e80004c403402e9201b950b618506a14004011203000e03214440c1d61100503041c009440c003094090001d8070180052001d01c02410f035140021035800c600110340020400080542e640110003038810500f480d89490025a280070030359005040c100c846034401c0c00c8420034107a00c01421600038540800a1011250b503441000500074107005582005000203014810000e803401201c200c40e900c11202c5450381007138030b41c2414400c00c460090065014005084007000d10604500008880f14103901c005900da01e0284070f802d41c0808020420704441c50f16000104041301001c40c000d00841201c864200d01d59014080c4103081d1a00030014002c272041400300e0303006e0119400440201d2441c2940c00e80c1c1d41e0100c94141c041c41d204003070b07030171802c042004a44150410b100621900c0e5071080b03207190001d6000c0c12600c04040b66046000e0b0340114031200134008003200c48050001c0c92500d0501d030f2646822003a0b086500040c1200003148072060060780c1c9050a944030b103403150381e070b050400c034014103070710303084 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 824165719 1250 824164469 824164541
    0xf0b09030c031801201b01030e0709021b06130c05060c100903090b070c05041d030a03021c110a080702060c0a031503080301030b040506091f050402010e090c0706 71
    0x3c0200b03010f40c4103401a40d2184400d09414180414524100001d07054201e445060724501d405005c0300800c1441358950003801220700c10310319030004044080c0385c0351458009402a48a4119072a404141c004843c074003085068001d0b15604100c00c090103851134069030702d140030b03401240140e0b014408505c240402040d4004850340d095000b050b0301c5c24500d42140c034a40c60360040d0300c5d1240081860410b000c907942040e41502e000750b5081141248500b20160101c1d10192203c045a00070012145a05e10a802500d895003854100d19804402c0f111050b0554100740c40d0320b04006000714007003d440380d100c01250b802801a00140c003480c10041c0d603040c1c2c1841111440c90916446816240d80515020b1300300c4000c0d600324080365105d58581c645080411010b450030f458511038400490103824010614550324440303944075213000e000c038480e03010140c00000c01c141e051000808501c51030b500e425070050710176290b50068a42d40c105ca03103001400c5850001c00561004022a002800d4544e221418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 824166969 1250 824165719 824165737
    0x30d0207061d0f01050604140121060c270b0405150904020d09051614010e03120c06101e050111162615040803100801020f0703030b040203071202030a06120f0b09030c03 74
    0x2103000b12483c80d11288400c4038507100070883d9103812044a8190f82c071081400300d512000b2002c08d003609004941c000dc44103a405034003480b2404001c200a0b500d010044003101c41401040c840c01d00c00c0104c001000c0381c00114540300c25075103034900981082024000128512002290210300a041c8200e410855031200111414414603008501180d0f0b010000001441300b4400c9065a07285a4080302f49c0382c81d401c3e5002074014901043c00b25481101610005601011f00f048400061501d001182c0c0c0ca40c90140d100c1079400b510b80e41d80c0041c0c50f8601d5000c050701001c0d0003403004402c11070f80008518040d01801c282c41d0806042c803d1400c00500441d500709400846c6261240c64001d10a2682d100680c41001190310008800ca071044074003002d0003600d800381e00d0400c0303c2c444050501c0207131300c011a801800a40c254070703588880501c69001d507070418a00c0b88001100c5849007629945030085100644441d000150743c4d80c20480c4500280341d01c890450041d40c00c002c400a88c440e0740c0d000d82610 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 824168219 1250 824166969 824166989
    0x6050316031d03030103061b0903120c080d0203040609211209020414010f1a030f04060e1c0309140106030503070b1315021801090602030d0207061d0f010506041401 72
    0x3100302c040ca00c0361100d11103001c1e040643e40c0e6960340346404002004503082c0709401d10000b0543d1443e144c042c5900d002100d4200f440c0c881c0c0c3c400e106070211a6403440c95811549048180708802c42d1810314030286208a204100000f41900c15051803400100d4100c111880c08590100551030700d075020941e9286841207020104203103d0a100140240c0100d889a405622000d000083c5040f07800001d0f41c101d692502c6a556915251151400244400c480580049c90f030400454005180d603401140460851425214840070b40b6100000701503034548124000317a210303003803041440b101014030303011542c5200003000101d1071a90b9283e1a4000c41c40d0103025440c4030000200615140d444550010781c0c4000d01d80b0702100007840010080d000506007070306110b6030b02c0b1540b0265011303400030b03025180d490700110700b42030314101c20001a500c1164121156a150320560151a026140b081081e07000398014001041640c0062821158010302d000e102c0c0e41002c040e44840b40652200c103040d01e4807002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 824169469 1250 824168219 824168231
    0x213090c170a0609140109050a091707030c080412110d0b0402150405031009050d0e280801020c0102070210030203061302072406050102010b0117010905131e0b010605031603 76
    0x11856004040703035481404d20341d080c04250f0184500705450541a41d43c0a101004552903c18080d0b040325540300c40105241011000402c008020360040c140c000d00c2441c1c9544010555a01c583d059041a0b00c04024002c8000f00f10381005074440300c0094110068545038a070001c9929090410781002d00081e01880c1034000d116440c01e1604100d50140c240070b8201d031400320803003c0040080046030740c02d403418000c2001c103a03076440c80360384400c45c100340041551807607a201c1d100c0d1010503214001c241d03082c454a20000620341c0300038000b608080441c40001a1030b1586e80c01070001c4480703000140307002c052042040000650701d904802c6002c0c5070070000162035038850b190901d000001011a0022804401c9458503200d8003034000c0720230f45200b80c1c0240103e1202100669198100c2280914101c1104006105240842e0301c026848400700302e1200b280413441e00c440c960524030002c00c0000b0724046c0284000c1c0801003020718010000d610305186180381c148481c06040c2040ca240f48101500c2d40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 824170719 1250 824169469 824169481
    0x6040503120c0f0705060f160e01050f070f05060f0906091c1101020304140709020906090f04110c07410a0f0e060307060c03050304060c05070c06030213090c17 70
    0x2059400f40c00080c844182d90ba441d034107200b541c40c80d007124440b10002c240c4d40003403000c0c0008a00366894a0064458a0541c02d00200540d010f8009000b102c200840074080403020803140034640028034016070141810342000824403440500081500607a81e2120050006a00c00003c0f032120006030003600d204941480e200071900c0400c0140c0140c0250b0020060109000046940074642900c4800325250740d07a0300c0c1d9524040e80103a0b1280e0b0f911100a00100d0243d003801a070050a18400400001c1c4a20264419203155000641341c1c270202e5005c02c8050100302e8024040402d503501a0340004150b880c03603400440820b030500460140d00030422482c88140d2908080040504110b041c101401520784180c8004490111044d40c0f00c2e100301040000c0703003401044407901c00e58140c0d4038180785075141c0d11000003811801644504120741008101c0200d1647d68203040580301e1503402617654003420084010030171568219032150b628008200c0883d507086a00c10f000a820002d540e0385030b80e100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 824171969 1250 824170719 824170741
    0x103030c0807210905030c0d02011d0924030601050609041a10121503020a0302060c03070503120f090d081801090804030c031205070c0e180f010506030f0604050312 72
    0x9a10003000207404000240c2d0306034800c140310f640794489130340d4902800da948003003550316802c4000090b040400c503c03210016520070120112401d0245900c40040401000131880706c03007084403104294165440306005000c21903840010f2003008400a00c01c0f5410180000c070790f8403912071140c0c4139030fa48030307103030113400c00502c1040780081c4000303007036002c0e140084001a011706021b0f0501c0390050314050240400480c41190642600d0300601032210941c1503030309004040e403203a000d80d4070703602c800d0280c0d10000e98208000c0050454140442d40c050402500c3c5165900014103400b00e250003600440103181c0d401b15019501aa080015588100b42c06032a21f0051285200180c81400c0004010041c000310f00b0f980d42c101c0c0c1c0304890000e54441103210441d62030150903030040500944000c03c200c42840c20307001540002904420f031071402c0038446603600d051802890b140351651a80e040081615003402043c22014119000d00a5031a09940b11030b02c1c0d00c242040310302c0a6403841d02280d9500d01c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 824173219 1250 824171969 824171977
    0x2040f12020f0a0b04050111151815280203070e1e0d05010615090b090d080f030a0c08070f08130f121706010e090402090711070311090901060e0103030c08 68
    0x14000c0d030340b26621013941442aa000d070240c5408a0b0f8500f6807424400c1000640c60845160521903000c1c9881d90101c43c402e8911100c018011845030113014040303a00708584140c0242d2038964060a00c008a0311825090701060075030395942c52060042203112904214945112542118410822110280c1c0c500740341140d0341d07155400ca02828044420484154820001d9500b14000c84c1460b128040c000c0ba00c000c50340c041e505003210240110180c030b0412440314107080e84240070107814460b1402030064280c00c11030300d0307040540e124100d06111503085442d03039400c02000d01d03092080681e404005000301602030602e407880e04020010b00148642503501c1c81505a002c00c100742260a80c0d40b000707060703065000010b03900e0b0740b00402142040d805a955900d0001000e402e104c256510781c0c08105800500030116414014504246c4103003000602060014511801c502d45008484905100b80440e0080000712140e1520001340100410b22058a044943c9441d0078882c0380300034988503d013401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 824174469 1250 824173219 824173249
    0x313050f1009060b030f031b010f090f03090b041a0306150c160f06080103110102340b090904020603090a020a06090512280519030807110102040f1202 66
    0x40c2100280c5038014680221402c68082c10040c024a5040e50030940c64020740c010081055108116881201050b4000c80408080d00030001810041880b83c94003aa40000b404a802d0300c0204498810190804d8001018101c1c840180c0d0800d8104200a6450032840c5008e15030158084001281e540e1001761880c1ca40800108198032030100c034110719a29402109d00243c0c1c0d40000e0004600000645501f030111100d540c3e907903400d80d2854850410101502aa00f81180942e43c0070f032816020607894600e402041e0200450000c11521101041c134040343c0004404039001c00403c412603642c010540d0b00560100c0d0050703a01c1d00d59008003854a80b440310020b401c850000c6001a04075044004e44048038801c4d1801000103200c0e1541e03a8807200c060a0800400690703040e1241005290164041400e129104403158203040c0722003d20000c030a44000c0780000d03a0301040214066021010801a1a6440c02035082500b00340000841e0700460140804d94140085c682042d5a150210005140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 824175719 1250 824174469 824174473
    0x80c1201020c010642032a110d030908070201080705120c0310050907020d030e100510080f030a1409010302070f150e0a1109092a010210050403050313050f 68
    0x50742c0c0d0000344504174407a150804102d1600070382e0030000003040800001c0e80c0b843e10f10000c540b6000040a800500000352106caa080310499148400d00000c40b0301e00014200c1e40720001680d0801e15020324002009030850101810402031500080f440026600c0740703507090a02c0c10311a9201e0808940300d01892070140712024800003803044841403a0011400381c4141e01c004000301e625902800312407034041e1130791401640802407003070403640701c0c1d881041400c800200780d680309031900700100241c1c0c206481d00c10558107034441c00c1000200801480001020400145003410746001028007000c80c0800c0d0200160700000b440329180e031107541191649648110402d68646641c02c0c88200b032002c82448400452500004070104000019041991607112030382d0380e015980c14052200200d40078003080c1b807510854034200f03e064002c20f00030081902458030396502010481c0028901001108100c602c4ca25100c00c0c000481d510800b201d80c4a6856599209030444920300107141400600b1044118 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 824176969 1250 824175719 824175731
    0x30e0601060e040c08061f140c012a140d0204031406040c090b150c10091a01120305030c13031b0311060a0215040c050316031a01080c1201020c01 64
    0x7a5410030200142c2c814191000c110101c0c0c420802c1d50302c02d0f019541140d0140d820010565038400724000c640140000c0e141001a129440b00c1a000d2504840c2c8805082d946800c004100b001c8541d0406040e10203400c00e0309020210003001400401108504076441c000019084c4076450058044800840c1e0140d46c0d0140c1c032107331a03051500e80c038066804075a1042031003000552414140240070325008001c002c40d0310216580c9440d0503a50180204011a0003510130a2409d050288113030011103000346110902d0b04454440c04108142c1601700c0e0071284880141c01c2c001c03e51010650380d001c1e900008803a550480e02205c110b03140c1290b48010704038111000b642141c422410315810441e4851060042c560303e055082001b1401480c40d81d10040e407000843d48440000900075503007081c020303c0e248040716140e80200b810101544038035180f2000d840420801c001501c0440c091810342d004002d190b035414581034a03120718440001074482c00303454044101c00e0300e00f0342c1200d01c1740781044002c000c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 824178219 1250 824176969 824176979
    0xa050d03020304050c01110c04180209090d0813080427051005031006180b011211030f070c0c150302040b130504060501110703030c0c2c1005150a030e0601 68
    0x7a6008441c100d400307020321149542d45e0f5000f8004103c410b0f00110141c00a2105038040c0002400b0b5081050440701c81c200049003d41c4078800701031300032a0000064064031580e0079001c0c280080160507206502c0c50210840d0100d5a0407081d9400d6410408095100132412003600705940608070440240700d1801c41405018145145500210b0342e0039002c0e140c1c0c400f0f01041040803124148552209005138594000117001a94080c0007002414104414a4181e03851100300301d0741a1900b44401d1000002032108281b084c440131075000300585001051002d46544041c10300e800c6d440392000011000d42142d981300e000303405a5000c0c1071700c41101900c82c400550340040c100030f80e10401c0d0245e0f02e407040c042059441514580e81420310700e40101045451590204c41c1c151030108151031410740e40c00c0208107400713200c00e108100c2d9410001c0c11582d4400d41c1406050410107080072021181107141003181d500c1d202d500e96040880600070070785803802040203401a244040725560240a12800450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 824179469 1250 824178219 824178221
    0x3020409060902130c0221071104090524060f1c060b10030617010903021203090709021210050405130206090415120b070203041a0d2004030b060f0603180a050d03 71
    0x34078a034442e0f003203a05298895107100401da041028100708200d0800c23282c0c0100d440380103040784046010303200080340700a9803601d5082040410114079480f06400c030400300300060b0850150032420442c0c00ca08030103280000907101440c248090011540407428503018406980d00c65004440d015140c00000e002044004004040d64024600300728104504100445014420182c00c103a040d00204444280a441d11400c4e42004020001e584540c200115a0800714005061900c009641038046800c04400740c000d0001607400c0107001c0c1c1e140c8130820071191420070050929503015103900e5030748c000d45008200031f003080c1c10482c0d03c242ca1291001400e8544110050041c40c0a4a540052902d801004a8880c4a203229156010384a103035180005240e440080160450b0010001050100c00500700d2082c01101d195004902c808101082070206200078143d01160440310b00d0515040440020414003000c1c00d107051949420034013049400c010444204855004400c070b8881c12200d4000074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 824180719 1250 824179469 824179481
    0x18030f1809020d0f020306010207060c1103030d052d0a020a0c1a1b0301030b061003091205031803030c070809030f030d091a0f0a0c0e27010806040c0302040906090213 73
    0x44645482c3c400030440c139011510980b07000e600160301415403140b03442c004542904001c00180e440328140a20500d1315582007005100c1660314400103c1c50703107401a50380070b55020a8240244000302c0a01074940703080a4103000e64042e945810058503441e180390111003040d44214014420038030f1180c40d0007240c003a40615403282c0a01440f02800e014100c05034030f551301003840020b0402594001107519031800c00c001440c804003d10700081c80c00615258070100010201e12140890030020a014081188218801204251900640c5541000c6442c80b00f5840f4815014007450740100708078a680da01400707000900000d440480e5160360010111000030100c14004035400001050000404c0b00d094000c1e600c0b500c5071565543c0c107513541c1000c09002e0302148014104112502c842240b09941300400807010b841b51400710050319880b16032b03002c002803041e040b10800f54480c40400002407004005101504da06442c08511042d1515000d0050000c403500258084502080030420801e05c0e4494 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 824181969 1250 824180719 824180737
    0x515040e0a0b130b0a0906020d092006040f090b01051308030a0305060405040203061506091c02030d0e0d11131103340302090a1a03040c060318030f180902 68
    0x182c2254440360741c0701c03420b0020400010003418214000510444c0a83d100d91040c90140da009407034814002001c20803030703602220403034403510a8410341000702607016104440394010354410385054103214440000441a102d071004a9031038861030302041c0d00c24401e4840e083c5412014220303181e180c14900d901ca03081444004000307468000000c006141c540100c902654000c1c002c0d11041e00c0794800608540b1302d1000c09030700a00300700001001c075200c511803070040003070001e03d28000030610301c105810441c204c443c0b1810000802c500c204180e0390300c41c0740c000c2e00d40d1200910980200510105169821441a107050149890301c0d100084840c1c2b00194491015920b5400303903c407010301296590800b152240e200c60702d000d8403410140b0700079402401d8801c401000b00001b1170762400c48044030916a404410000004000c1c441004030342110800034141a060500c100d4444003d5503860540941015040044c1d80b070a429246010b816440d49985904811803682c0d0344440c1d030040651701000c11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 824183219 1250 824181969 824181983
    0x90213080c030a150b0a05090a091506031211010e030d0209040c02070f060509040216110102100b10121803050c072304110c06040303091713090515040e0a 68
    0xc0c20405140105103c01400d6200c0710720b02c07200500409900050070792414258000c030b448200407a02d55101c4944501c103141c0c4030004201e0460b0351034250100c003132405034881d855041a800784005080c000f800314040c0c00c0340c0740041c2c03403c039040e0040f405801480c400c00b00381e00000580d945090300503002403940341005d45082c810409403990480e03076480075126414105451410034410749201c1c0000303011013031004001500380100704108040c004092035044442800040286050b075805201100d45c2e61540c800c100a44200b00001c40c050051540740d041c100003284412004a09441d400a44054080490301400c4c061511b005007107a8807143c0600d06030b1141805c0000c507081044885500c400014000c0f40300d01e4002018400a0000104044501f01c010b00400c20106010415180b00e03074007a81d408204080c25003401d00395041050150510120f080000c4079042501d4000c40e801c40b1000140001c80ea5075107031036940c2080355100c840da40a420140500f590395070000754191130700c0c042c1c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 824184469 1250 824183219 824183233
    0x40305121f051806100e0324010b0412080a030f1803090f050a0b0f04032a0504020403024603170a1202030a11030f0a0b0108131b09021308 61
    0x401c43c0192501450102d00310204002811900f800d20308600b000b005420301003c082c03009000641000040c46a491044e918a11084a11011111100c0c01440524403580c034107420310950840090208601412054000684803d0f141c4254004141501c074020100244051520300101e44841c110043c1d001801c10080800c98402c83c0c0d2480040703030f0005004158031807905d12620302c0c0d41c0080c146d03807041c583c0030f000010114485420340c825640d4250881074017030310380740d00048040364150440d5008510501050006840c1c1c01000c409200f501307044079046a640a1500c40085001d2303420000c1008107418500310010f64000c404140ca21615039440f035044c00900001c00360284006010000d1240d0359944c0c1008002c0c1d005581040400101040b0b810001c4043d03c3e156106503800e0a403070310340e2000c20101c01450320407036800038424a848041d0381001c01c0c58148c0c0103100310700501640c260a0044074014945065000240140f03002551900c0035000d980b08030001030722440401d801412 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 824185719 1250 824184469 824184479
    0x108100b0303090d0f210f02070b130b030a0b0301020a03150510080c030403091a0d0b030a08300f060109080a030801031104090c03120207091107020603040305121f 72
    0x40161062200c0280c41040f18504c640c68003691103280314820396800044802030304c01000f038071b8080314010000351200748074a0030000c80245040c4050340103111040c02407001e1404504a001c40c1da00325200f40d890180ca944038049110f000340414103100798150310015a1a0580e03404d07800030f9102e142660548101c6035502d0091040300c1c0c4040300e01c2070004000800087e00c8500710b8002c1d54215009151403480543c60310b440d44800381c80c04a40b010f02d0800464040403003a4640550180c00d8400c2d005808800610340c2c5104c0b440c02182100c403900b86442c0a2405a11001640e021400e00310186400c0503080c415501e40201c07506680c00741c0015009000070074004000584a04c7d80355250341d8608942c0e00c0d503120480b05581e007058569200c0d44400c14030021510201800000c0c500031141c40c8a074480702003002e858480c95500005105003082042000f54100409560750107070190707001c0703a483c0c0e50b51604031294454680b2142c000700b40c60003070140c164401c040c0400361028a401c0c40e036000b5219 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 824186969 1250 824185719 824185723
    0xb0d050603010b0405040b0121122105010e010f0603020c0a060c02010902040216170421020109050d1a091207080706020909190c111e07180b1903080a051e030108100b03 74
    0x110402800400c200545101132130b1140c000c440401c0581c41c003041d81075100c402fa12082e40d400780d100341100e642c0d840051040a01508000004009908085150144807040251210107104000e40390a668605030a0141d00030741103034284550040085680b0460598524800c00c1d07640016510107001c00c0b0100c4100300303445c00302ca0950704105050b4031b0740741544403000646089508128100500c5a100007400d40319a0a406909442504032641b074068620f1040e83c1c80000525900103940400b40c510154040d480480e00c61a4000c030441d130783ea440c1c0f130030071402078868124550f800c5500403081000d007031681d80036610000803000040c8164040000d01310380307003010035448000c1900100c1c54181c420746100381c020042240c8400380c1c0c034660780d00c1075a4650207008200e00c180c1e0315206c0030b880c0e443d454041e003040c20010060710402c24550070754681c0c01d807a0103010104002d0205c0060f0a40c3c0c1d421000d505050b64880143e40b0715034a68440814945854046011031900b9090541c501c0041c940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 824188219 1250 824186969 824187029
    0x3010501030c0e04020a090c1d01080714130b030903120f0705371d030f060c0f090d080702130b09060d0311030301060903020108070305010b0d050603010b0405040b01 73
    0x1110101c1d81d801d204003560f040078043d00407070b480303401c03000300041014150190b0000c0c64a40d4456104078000080e200319108040020141080410410001c1040c2c1040c6490070301035000000d1922140900907d440320f56554010b03d00050012040141d0304000000030503080462036198001501c0e200c9540802d03100503940840403490034800f22904000301c0ca254207a008007010b0300007204021b400e040b40016001105503001448101c002244c0850400050f00300c00307010350082940d11500458951a114090a884190003001920640031400f6200f40d4200c403038010825089440b26103844189075008440c224064421200d0b50000e508041c0301d03068901c40040c00514441d84c829042060300035004401304e0a204202d403c10006090800185018102e542c03110009582140000b51600a00910803010181080014450b2481c032200341c910078021480d000c501c0d5200c4200003030241c02801c800f1030b0424949401c010901c0920071046040b00c07203074220505071810050f83c001c0d1000d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 824189469 1250 824188219 824188223
    0x5190204023a15030201030207060209040903051e04080a030e01020a05060106020610050d030e100311130f1a04060e0a030b0a0f0513020609090a090c090b040b010302070b070f020f010c0206150301050103 89
    0x1a441c0f40410155000b03400a000183c41500c0040c40c004c00381e0001422135407245000d60000d42c4c0032441103480785075a812510b40304194244642014504a5100d0b615004800c00404003c031484a09589074020889541c5c511380c004c040e102e0b1580c5490000390340c0d41084034240000c996520000a540c242101d4115100381c05640c3d80c05c0d8201c4020601c450a0002c0100030308040d911301480740b01da0b03180b4020340032416504070400354582c54010350b0410740d50180c10101c0110f4250780302e041c241c00c1c0d50382183c3c00c42c1e51034208041c80c0c00844000503921481507102a00481025040041c02c5c0340d10341c01701c0c814800c880e01c200700d03e840b480c168038401e07840a00c009400160400100703080d880c1209a42e41c1c440e017184000300b21031a044e9030702021440140d02205580c5d840300c00082c1149454000c1e0346103070700207280450074225a615940d402540140510090040021918001c180b09014402e01040ca950080c0b040610f80c01001b0340d104400c441e10325099001104140d01c0345018001e07981240c0e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 824190719 1250 824189469 824189501
    0x50601140d121808011b02032d0d240609150813020d0503030a0f0b060d05060301090506090c090a0c050417160e0106080a050405190204023a 62
    0x6a8603615240d2035064030b1694018410401280d115450050400c50064410312002088141e445421311035680c10820001056420074405909038000035400c40f11881255001c8401c40f68a843e0383d45403c6c407030080340d406010300f003044051404481120b41110303000c81005502015980d8003084510280c24022101d04403420310701080c1d61445a104903400c140c200c4250200c6071110b0b03002680c15041c80c84204c45641001c000c02ca030b850346a12450728280c80b0746070181306c0304240c2c4000a00920820140c84030155545007c0344194800350b001c2200d403684041280c200703040901403982e5508040c400e143c81a9110400626000510300070f00d0341140c201e4958900b442d0030320384503515140d1140d0f0b0a020500c50b1428424080711140750413401040d07101d51600d4103504080c0000c004800041441145a0929040c800040c1c00042d411102c282c030102d12410310059840040c0184c8035103052410820072600340e8004107a00200e440404542404216580203100f500100a55421000d00d00c025 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 824191969 1250 824190719 824190739
    0x91415090a0e120307020d120c02030a030c230301150309021c08070f03181e030312060b1206040b0d1707020607080d0b0a060207030c1e080a0f05060114 67
    0x4405402c080448120803040d9074025106050800d4560011648007005902501c0d0408903e90040d07507403410751030005018006040045000b03581c034494101013900300343c1d07100a44000e1a2007001c2d141406d0440c01c0c1c00781507042407900000c049070800c1c0103140f2056800031050740420300a00c00e641145178080c2600544075425402846008646807080c0c0301444100101d800143d694490003107042c1c0710303440d06000b0392204c622502451905400903c140020701c10403043d01400103081004999051134041c140c41420004c0303401a044a03440000d4004020806040d60002c00d0100c0d4070605c000e0300c0030815103800300d0402510805011000e44050701c0466030b43c0030103007048018100240041e0180389807961655034051707a64030401d42151411b5a62190700c06620303001500400803e0070744000c00c80e89003151903c2009040a10a540030310380c003801d8200042c5008401c00c8010310016042c0c64580301981423034002c0418403002250a401400000b05408031641c00a075035410b4082c03c40170306 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 824193219 1250 824191969 824191981
    0xa05041509021308060a050912090d06110c0f07030614060d032d0f1707091e1a0a090527062409090a050f06010c0f06020409141509 58
    0xb580b0900350514580014100860020313020130809000c1d2001c0030f4001a42d242000d0280e0400e00840c00440c2105e008120220f0039956460850a03213035046140001d25206075000740300c29100b0072000d0900e60003602c0d0030300016070000c10400102c0c5c1c000c1a050120f0f100c03104400501810441d420755000e0081c002603c0440e20405403030851403514420030352001d00400e07041c00382030f0901440d03200150420444000440d07128143c00c4c11084c0902526459052041c2c014100310040c0c02811b5000c04072102801211222616080007040700907070304c280d400e4240300404007603800240382401003000190009610709198100d91411411110323450740307001112000200c1c2000140400c4c1d44140240071468000780050000d1100c0a090300e042c41d074410b040c0703062000e440002412025817034500802c201c0c030150400e1305030f540010240380511f1001c076280303000904e803403011002800c880d20100c0d020400032040e1384a1071910015041c2c1030841d0b502e03c0d440000d81010411000d81281203003000c508 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 824194469 1250 824193219 824193221
    0xc0a0507060209090f070e010206220503280f090e0109230f160306081c0c0512031008010b2d03120a080603060709121106070c050a05041509 62
    0x1403040c00d02500d032443e44000508480401d031051490b4444480c20300c040240c0004041d44051028000b034803440c0740001c060000490340b00c5d04c81c24021034640b0b416007084428000c9590380c8200000a41d007104800b00c011002051405440f40480c040030b08440d600d80c080c0117a10201ca1000e04e000059030700b000c4c4404082c203d4000c0d82003d94984c10041c52044480c0c0c581c00344140100b241d0600740349410454038501149824400c07003414680070050010320004500c41d01130400001111150300c10710134040f10003044041014005004103240404100b000b5401540900c200c2e81c91445001d80b40c2c0202d5089409003030f54558012200780004074107481c9000c1e078505842085000d854400b04803404642810801c1c10880030401e000a03450054a82110520b0303000034081d8024a03451520400140a4002500a10350f0080c2c0106005080040010130003005c518007400c0d19071501c60914280752452054001d451060f1175658020400d030803d481500501100080000501d03494140050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 824195719 1250 824194469 824194477
    0x110c12040803041a07061e050a02040b031b070807050d02100e100506041b051312080a03090602090d0b0a050c2502030a0803010611010501051e04050a141014090c0a05 73
    0x740f0020140a03005c0070500d117108040342c0c90680b0380c000c0c41c5a40400012002c90300011b00408000d44184810711405d480e590513203a11100d420117071708000524220100366401003c1c0000e1114900150601c1008004142415031450603000c40d4600b08040512500740c0d00b00a408101300e900403c64800c0504e0280c20a5400850103000016042c4030044031002e1000c860b512000030542c001949190a0001c1c01000c00800580b80c041c044c200e0596180d0f1220702c5855009003c043d00c5403200001d000c00b640c1280d003640002007a014104506140480004c02c0031907400050615045c00540a0f13a0b003601110b82d0080c0003825951901c0a00140f101c2c4180848000da03094030410201d8800140e400d00218064042d640314000300b00c0c1140b81a40c290790b41604003500828406100e2541b00c101001c1c0c4011640d8103c6001c6004d686064590004004858044e13030342141e03640600030100d10300b01c2090251446a148100800314400903c14421825160307c0f40320b110070081102c00c1c2c1e101d08007034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 824196969 1250 824195719 824195759
    0x303091b06031505060a080c07060f140601020d03051b0d0618150b0a020c01110c031c020705041a01050a09080307030203130e0433110c1204080304 65
    0x40203400c9810190034a29140d40c1008020a070307100452080a00820511002000100d5003d40fa20450b001d00170480306014012003c0b1a0010551004204194124102c0842400002c00014890b64803002c410b10b8141c0340715025018840e0b0311840c1e14400d00610348646c0d00340070000c10034586942d01141641c007a05681c640c591f070340c0310080764140d80c0d00503042840300060300c0404d0400520050f11904041c0d50300404000c1010440c0c0c0d80e890b81c0120300c80036410340908003203590b160007080c1a81060301440c0401c1e414041c0d58002c16400d68490511103c0d44555030803610b1380c40e02e84c018803040740c5988054850140712401e40c00882d610a0b8012b102011092402d41d03d001c1d540c04040f49503400c0b031304045003d41c1020030640000c40381104007400a01c00d03003403000014181030300c800c100c20702d5100e0303180c0502c0d24210030b1800d4410400c0c8041803100c10300604202c0c107090b5900040c0650000c03080d0a5182c090040401c4405500e1400c2e9425104000c003d14039051521901002d0300000e1024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 824198219 1250 824196969 824196983
    0x80307030c1a090c060a1103041403120406020c012303070c030e0a0302010e09040311060112121b021e180a050603012903070b0a0f03110408120f0d2f0a0804030309 72
    0x101f20301414005040103001690024140d10f5011007007604000e818520072000040070700c0100603150740000c800c501e413030082c03c060701d80e0480c03125240e0900002c4c2110840c407403130001c184071200d03600560054120307020b41d5800800060450400c000c140d40c5110107070019410180c011228940f029209402501c6401c01c561501a1900c0090520300242d100e000004038225061080c0081d1100c001e04000e520f01c0c1c00c0b295030061149044035030340301440203401500501020000151440700e078100e040c80017402c8441020340310f2004041460100c2d010400c0c241413001051450405005844014030a01041c02101041410f80c0c2c01d08031010140951501c940400025089481c400505000705a075884090180e179403140a016034211031440d092100041004104914000c120096058041c080710b59aa01951300b044001e4048c1940c0b000b1910318140820042742e42d0340d00882481d144008400501c0d4600800e250340d24000d044007200828100f000040c0064481c2c0c0c4410780c0144074102d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 824199469 1250 824198219 824198237
    0x1020c03092106040b070206071e05030405010f050a0b1914011110090b0402101d1003060911120703020304020a090b031507030c0212090a0b090109080307030c1a090c060a 75
    0xb003040c030b407050590b02520386980c41c2080c070055a90500681f5846203103030074101820004807940d000050000408082000008804101080000c0d0070140000320307001e4051001c2d00f040c0d0003840080c14a00c883c18031500d001d20f1851001000c04520070101c540000c044840303143d4982c01950403a107141d405c41c0150081c00702110035848284100d80501d401a5200285803500384140100f40b40600c032101d00348510306c0441c519807003801081840c0c103e8240c3c2c1204034070300584400c7e00a00b00a4102590040c141000c01c42d40c00d80760700180c942070031082c0f0174041c0342d19006003c0c2c08078441601c0194011041c04800d20044c407042e0021040140041c0407191064a80d0311800a113100580b004400a0b8485414400040e41000318101d0142040785445c504800940054590341c11881401c01280010511241d140e0003420184000c0005406599468881d4a0018148043c2d002d0494480030254a00c3c0034101890103030510402c0030600600320b0340c0d082010003141350001040304d4208446a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 824200719 1250 824199469 824199529
    0x18110d05180d03090204060e09060a0c18141f0e101b111021090c08070b0c15011d0603010f062603030402090f062115070201020c0309 59
    0x28480b14048903540018080060310400007034a8460313001944d00310701482800b01c0904085007135a045005142d00240c0f510003482c09a586410714241040c820760b8142e4001121b4030441c59140c01c5e80e07821554484e0270046a802040c29400354515a130000340d070a45102d200b410044002030110340f041c00d040502880b0106240300c3c03408403950842e011010382003c6111410000c03202e0001d4604c904009001d20b050325110161400301c60700c450000b03a181d9025a044c00606103021010380f030444159480d5a072603440010b1103901c034070f40c241d0061103020b0040384007441c1401c01d00c1c1616002d0a80303210010102c548810750860160159501d5562010300d828a11064400c04000344a40c59245c251404590240380d843c604044885000d41c008104200050780d03040415684040c1401b2040195128800403500d907080b00d00011040c1c00280c445220040c01c006801e005c0c007440ca09084005070341e003400480c240d020710f12401d105580144101800c901c5d010035140340a603001403192160303685e60 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 824201969 1250 824200719 824200723
    0x20090112020319060608130b06060d020f0a090510080f092505090f01050d0b07050904091505060f06040b16080a03052a07030c11091018110d0518 64
    0x352000c826104409983d2103041000f401040c1c01045503003031082d4545080c0d440d503c0d8035104060700801245800f80060859070307401050f1751300c004010400315218210b148100241d0f42c03055064401103108660005600c0c50900c542401c0854a5a00c2c17003440d4a881e044900410409400f0003900c0c0200c56405100e010741d007000038200303030305403c1e450141072401e403e200c442030b0301030301c4005000010401032040e51034121f42d240045900030010945a42c03611001c6580d400780c241050341c00340c10006103a00740300c60050003011444089204006648500d400c1080000340700141130780113501070004005226403c005804101340d03220389110f0000303050383c0301110760740844090302c00f180e170350014005004031000200c040c0325084886510040c20b850a01101ea01807510f0043c01c000900c0e009900b00221010329103a02c400240010781c0300d04003540049241c03040c0d8024035000400341e0409480c01500ea0040802c40c0c0741e40d1800340d24142c1c400030f0303260240c4001450f0001c02d00000045991440e01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 824203219 1250 824201969 824201971
    0xc0504050c0c010c0905120f060402060c160603140f093c0a1713050402030c1c0e2811010507020603041a280504150e07080d0201200901120203 63
    0x7141c0c0c0c0c2d040c45c03901340010403948004800301c80ca17060340b10010b84141c034200041c00c02e8220307404450403511000c56814442c50000622050a862800100d000544c160183c000d0b2282150300d0150040964690700c07001c11402040b22401d0705684111b91001e014501c50141070074600c0c4105a19131420000c4910050004001d940c812242d030150080b00305210240c9802c0752981021400d651400c4180316110101c4e040c54001c83e44100c0d40080402ca0006128003140c58130300560ad0700c45140d40203104007000401c09a07802440600801e103908070322482c0309610124109241480f0b80c0b4494040c1c68401003005243c0c3c1107410b0080801c0200c0150f41d582c0082c0d1300c00e40c801c80c1c14403020306007460741401c40e03c07015104107400403400105042d0485a9182640a4a07008000181c82c0e5110b040002c103035102060480d17450f500d4003140400b03081e00460910250f418901c22100300300b0180c6012400c1b03c011041c0d0141c2c0703405202001000300e620100901084505150564612508a00c00400c03070f80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 824204469 1250 824203219 824203241
    0x103151d060a06090e0115020709060902070b0705090a0e0c0c1e0f0c01050a051c0c0e01031a22020c060708150907020d031812020d17040c0504050c0c01 67
    0xd89080060a00d081403414010f082c1c41d00d80b407000c55180c205001e44140341805041111140c2c10301c0c0040790f80c404c116020080200c1c042c1030080d81c0c0d550030900000c0d40031083c00d07603101080030001448103000703d048949180015000d0272401c0e140c040107403000c200251265200324401c2151562500d000c01c64010042ca40f08240c03040860502c0c003a610f80750040c018141e03250400c401d00c01030740e078002d402e88080000030300304990b0390070851510b00409000001c5020480f494104124042548040242c6c200307402a02c1c10004800809640b0084031900381d0581c1c2d1054108590899880b0641c003004460820b000b009802d00e43c2d8a082c3c141400b01c12107a10001500130070070400341d0f26092210740b00c180d1041d682c088480c00c0c0001c000303465010071100c5905050302c030380c445c05801c1c800010449541750002c3c107195284d001c0f2900252619111a1802c0005403034000500022000b0340e1641e016603030151809081e01d150000b0b000c09040c000b86003000405080c401c15608800a00480d12140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 824205719 1250 824204469 824204519
    0x100504150503100905040308060f04180503030718050a030215120406092306160e060c03040509180d0f050c010f0605120f25030516091802030606010315 67
    0x494820004440043d00c0e03800300b40742509000a00020a80007808940c0121003560900c04081d192030200b0040d119403221320f0402814017094405004000c400740d40035000f2941e80e80c20510000740c0c4913107842e84a000ea41c0c1c1c00070490100300018a0b0413170002d80501d81300518581001c41c0340e101e0202480d030456060324810380b244411070421103100c1c0c0300f80e4464042078410b4a0345507007e2025a8405004104610a110721034103850403500a02441d0462103006002c0f6603222506400300740c4030340052180f58010440b12002c150171744040d401e142d45031290350000301254a400e0340e04446140700c08a074030f001d1080820001401003028050421500d02e0a440850010f14182c1481740d14441445800d065400c0101603291800011030a01a116181401c88900c138500101e2100241c1c2070b60f00092080c800c1c50000380c0c884000f500d0030011116020001c22101c908110a070002c0c0c200039500961542081d000a48950700a038880c002c01140001860813080e15402040c25102040741070008030307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 824206969 1250 824205719 824205721
    0x120304051603030c06201207031b030212221e06060306140f101701020904060f06081b0301060f02010914161703040b0c100c050301030218060609100504150503 70
    0x2205c09400740c0179200352151905403050804684101d81805507104041c200440300c4045185030307103ea0800ca070b002c91298a41600c02c40c006d81e01400941c0050404003c0180500010300e04000c01d03d00c0306502502139004101d04825039a601c07006144600c10385040d81038000300500441d18612078000518420440000e10341100705154402030002002210b1710000c0301c04001c5418810150308013240e500d00c44043c0001d021148181c0a401901d104d550021320740b48002071103c40e0000907004035007081d21001030070345801c06130800040c042c5c0e8503080d02d10000c100400c0b605200d247e00c804070312410302c000940c804040d51180350644070305d80c540000d580310010301d0f4102007101c0810b030010885080030b6050722a115a0b515100d014a110b5005020008200d24000c2042030040c41041c01803807000700100041741d030010f00150030a02043e801801c0c61110007802082c0c0600260180c1801404079003003060840130444403a48c50003c03003080000030700000401242c03031780c41802c0c0b0950076150b403626 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 824208219 1250 824206969 824206973
    0x9100201230a0e0d0f030c0c17070b07080f31030e01030b0406050306040b250c0b1f0b0c0102130b0a020f12040e180f1005070f02120304051603030c 65
    0x70b41c3c090a45900564002c0c000892240b600080341004c8031485040c00326680805490039a140304500c800500203e007850303001c9100e82e02000c01049024441c01c11807015890b10001254520400c40301c0e54190354011010852007680c400100151901c00010030b245108011508200192106412408205071040d901519a01400741c000404401c2c0c034200501c3d880c1500203651030001400147c8440d101c603012604072043c0903140d9040c5501d40c42c400e514114100720080015403904016202040401f0200d00d40d030481a02c017584422050380000004c90910740c540c4d4180d0300256080d00150350130042d042c16032841c100c0c030000502d4a02409515020400c0010b420b0078448858622a6000f03100c0c040b450392400800d0301c094920200d000801680e50982c80320015020307054a440520682c601080c840e00300049514042d03000b400c2c18401d644035400b0980e444c1b100d008100b000361300328800f40000b9081c400701842d40705010704104c2e00406c50510032910345080342d80080d0005980c00c0070043c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 824209469 1250 824208219 824208221
    0x80a030207090501051c080309011808091309051506270906060315130204150e0411030c0303090405101a0705070e0f0c0c10061d01050604080309100201230a 69
    0x20040030240c1d002809551101b1031110140000030009002e0817022000c16883c032003d6101101818420412007030580840c00c0200d821307041010310341c1c421041400003a1100416016460810b54080c000300b103071142c46c9020141c0f03100004c2800d034101c04680001891341401e4150903440d040e0500e41c0307101a007004c0301030f00c2c01c2010041ca114041d1b80324030944e20404c900a1030302644543c501c6061801c41c0300910015001e4810111200c03004142503101141c8008075040d82c5000c2c0340b050781c94000c0da0b07c110042c962202005041558150030502403102507040c260031582d407000e1500545511581c40704040f54400340515001c0d010620007180020400808200b0040a00403800c956056850400074440164030001c040459000010400c00d81580c01001590305280e05500c0600c0211345400c0d28016050212151940600c601d100000f0709040c0171003110f040e141c4000c059484c050b0002c06018507400c000c0d024908541d80c1ea000080e11055900a007501d0200700300d02400c0701e01341280c0e1a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 824210719 1250 824209469 824209471
    0x204140a050f010903031d1009051207150e01030902030d05030106111513050a0501050903210603030706180b0916060e0d12120608030408160e0112020406080a0302070905 75
    0x6006101c4080502e07203c0ea00003600c1c8086982c540381c07000c00b07647d03001036441242c0421035456400651032140749003403681049000c010303160155444043c102d0302040300c81d51080c0354400c40d4605d01914207250395841c402e40685090000604012540300c020f03a010914100a504869000980210050021680c024000285003101c41e00401092214401c0c0c00315003e00a0310306281d840801106008200060090b00341e155007181c0200500d103002e400321526680214190382040e0710140d444100d560356036903150f000c1c40c8003400650800400e42e903070000511240b01100c0b05115140544c00c0003595021a0030f114460010151002043e05064403012200c1600841c0901500840c5038242d40c0300e043e40181c0240c0c00964104690f0180c01d810346168050a9200b040e090502c903000c0381d0b1103000402001180c3c0e40350201c443c06000d00504600c100014025001070405070302c0100401ca254191020980380000c3c80050410350b507121080c038099440381c0440168008800401c40200207108031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 824211969 1250 824210719 824210729
    0x30c0302180411270a0e0607050703020c040c0c0b0408090f060f03131b0f0302090a060b0316051306110c0102010c1b06091b031106040b070b190204140a 67
    0x1070301407402c142d0340c0d00351004081d40240e40030782a9019003d080c10a210850141c0440114420384a401c01a5941000e0204052407460071b101c6d40c0041042d00e841001203505158155000d800614403540c1008041c243c211600003c10072202c40b01c1c00841c0a040740340c0d000303510901d00b40b81c3d00c15020050040521212441500c20b420920149002074014421a6402501c0d1b01c01000101e54918001213100c80910000c000302864240100328085048414001d40b8022070382040c0035550b200e03c2d2804c0e10300030302607461403410500c007103403242200c103000400f02c0829050050601c2001c075141004410b0580c010700c0000c0ca505085001c090b0705000070940d0030b10a100030700a042210001803c0015168001d51031124500000d10a21010740d11003510710b68801e01c1502d20540780715500701308110038017090f82e0712810208580b42c1d038a405c9c3c0888040b01d414001203410325504d9180d0030254079001302019280d0034505d0a1845800c2188000e00c0900304442e007482140d0485000d0000c996159002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 824213219 1250 824211969 824212009
    0x10e03070e160e03011b0c14010501090b040f200d061e051c020f010507021207030602030414060402090606210c04090b0402090a050415080a03122f090613030c0302 72
    0x4103801020310f000613440c80c0e22400d10f484052264680b4510518010340c084405512b0400041044003881d08005032100c02101d043c0040c44650401c20304481500f1907083d6141044480308581d491200060803958801c6c160010310b4581d100e031700300096151138142e41c3e481440108280814600001d10f40c518010501d1010b40007405a408038101c0c40c030b100311440c103018022844008540e9000784480400201c1000d03980b40f9503580c98500c0187d001500c04858031804d11208601061000461922941e0010050710040c4c4500d0706120203a0b0001d10b0b1401c2180b06000840031074014844414003c540c819901c0740e44a1403c90300208503a0f076404c142c2d215a004000071105961580b40b907406070b0308122800500018004024403003c14694400145405054415002d15400009919a03942001d03014000c05074215000203d00326030200394000a4400c0c403c0400024946028051200001c0d02d400d00d4150081d0341c2d454085c9040c1e1003140c4d10a89100d0500031424074460440c1c694600b480d0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 824214469 1250 824213219 824213231
    0x3031e02190e0406080a1208090307050606150d050f010612110708091c03030203060405060103060b0a030506030f070b0309010f0c14131706090c120a02010e03070e160e0301 76
    0x1038084295505400e80104140004100001e40d504c0d40100014005ea0741124880411490700303600108000c6144000f01d900640083d58024003c4110790340c403a40f110140206a85000800c0a0305609002e0003100c111b05001d180318a6400d449607500034030801d000403c40e503150400040586080540203801c3e2070034071b114030200101600c2a10742c0103501c40f41040c0c0742e414400101c0c4814090105100c1604501c01d0440b00f8190035134000c41c000e60064405000d241e80d54401502a81d90a05c80c0c0e43c28003400700300c00c2c201188264415a001500242030780c4000d505050074a140a026410803510103d0020500c05071400034802c100d00403080e01c43c107006010b1301031800340c04131041e0320644074040701c0007658141200e00300701c3c80c0000d80b0303145d901d80d408402c0c0952100d0b034684084841807114882d824103400186040c44402c00091200001803049540ad6401100e1285200040c15010700c41c1b4040820740000904a0901c5501074a8881c40b120ba144030008200b20a8201c034540241d140c18 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 824215719 1250 824214469 824214487
    0x204050d0818040c2a0503040b0a1d1c11121b19030222050a0c030c091a0c070504050a0c021e0d27030b091b0a03020907020a0b0403031e02 61
    0x41c034510491100040580461300140c1c00170703240d00c802c01e0009089000008004c14140300560281000240d0313541e8200601c2002600603035034141d410305403580700311070602440c00714800d5030850883d107100380180d0200e0701211010070180c0e240c104814130329402c04601c03500c0c160128800440500c000300e5801114222091010000681500000c1c1c05540c3c81d948800e052035400079101d5100250100802c09880d000e40060020003041c020300340040d050915042d2002d1081c0150415030b000400081d07555024001c0614541e401161055058011500009000c2e96248250362040d4004000441e2100344250000d0030310351074140450080c81412035191452500140a020b10030f83e906140ca4100c610f0404580c41002007042000a11032404002c01000548090180203c0e1000204c0f14170000082c030741c000c56020b454449411803102c400c101b002d442c00404642c2c21111a0040d034420103010380b04c803100010110307416004261142c1030015110745a910651402007803103400c41c20031602c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 824216969 1250 824215719 824215727
    0x190b041406090a140102250611061005040f090b0109090b10030f030302031302061902100603081c1d0f0c010f0c0f0809030d09150c0b0109020d0204050d0818040c 71
    0x15010708503000d0542c80c090303a441d0b40200303c80c00c9082c414407600110074035407a000a0441487c4e0207180009220100c403404040b0001810340d0080e8034000200b4265030510301804020012400c06401d01a181c807045c0b40810401c608203800b903e284440402c100080741814030303c80a001d4550300c26100300280810204119449c4a03000d161715103000343e940c0d01c0794060141302d1050788401030b51006000403558082d0128000d01042d10a941c0c0a80d00c012620b20720040864000c3e10000d80010400c000b074102c01c008031128841d04480d4160005102c0d500310048030b290001068231000c956205d03105503035000c0810007600c0481d841c00d00e07100c4040290100001c0204100c900020011040d189603c01080b00f6030099400d0203d000c0d0840d0030200414000515244040c4203031906039181c80303100c00e05240705007000110181c0014103013036141d180c180303210020b603c01444d000e070490782440086125900d968101003418011b0046548a04800d80c2c50118642107803d00c51043d80313025403a003681d40d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 824218219 1250 824216969 824216989
    0xf06081506190809030d0c11010e010c390c09110301140906180726040305030c03070c021f030c0306080601050409080c0a0c0e0f091b190b04140609 65
    0x2d41d10f0b08801a444840f5042c0c5103001d8a1a41604c081c14140100a00d503802100503446000300700c002e01001200e080b40c0c034201c1e0f1400400c0000207262030200b04072460700080861054400c4009801c4c4001c900c081c8805c0e103804005e0869207958203c60400c00151940030b0b41c569922101680d0b41345500d0600c600300311800402400e801520040c0014400e42d586801420f03944242500c214424038110000a000f078801c8400e0007034000c0400b0840603d0004c10124910459050719282e01d561100408202c05400040031a81000340f444661801a1581038031041d501081501c4242c03140103010700501615100c05911003010b1a00100b0040d038040020440d0440c0c50580e800520f20301907080004040c421503000c000e642c8074070388581d0104090018984100c03021032046a1480e1252281d03d0341002081d201c807002035204580e014040120640720388100e1400402070b0030040c45000c16001002100e0303002035007486001c40c0401071104109103030028040100c0d17440d45044020303400900460b00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 824219469 1250 824218219 824218267
    0x120114060409060b0d0b10080f0d030e12040b070b09010b031b041d030a0206060603090319050c16090b0604180510080f10110922060f06081506 63
    0x2c0c40d4016001030040640c0880710f0580050400d204150a504140c0c900c82406d8070321440c0c5501810700000ea200d00894840d00d440503000c040c0c6007603004600b0840240148030001c1c1918001d850b1b806c1c2015070020000c000174162107800c40c2d100d900c2c6013804c030b0070080d0051000606904245142c0d0a594020880d10418040d40c1400110001e601010800a00340000c00f420b40410482e004824141c00002030700c3c2802580d42101d05590703404040c048603000981d00c0802940c0140020050300c000b00c0904c980170303000ca1a1160410300417410480c0350510404540e81080b1201c0000c0c001448203029403011101c040c0d0b100f83c64a480d181e1180b8120070048808443d03c4d0307969000c101c40c9015000c06070001c040c001d0032141e0f200b042d001c03407070f45403060200314881131494000210001c528071010f035901403600038595151180d00c03580d00005a0b42c0040200c80ea90b42c0c0342000310384018241421405040d40760344107851440d104050351085410704d41c04900c610000d214030342c102400000751400c901 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 824220719 1250 824219469 824219471
    0x7031e0e0a0204051906080312090d12110f0315010809160b03060616081305040605060d050702010f1b18080309190918060b151e070f0803061201140604 67
    0x5551900b10008444030070507080341941c01c10b01d00090444002008d049c1c0e4250304001200d60fa02c07441070642c1c0c0c0d540542100d038080382e858600d42401e0401640024a26060030b00311500c1c10024a4244007160302c11274900c2000103c0000c041038650340580d5140c0c0c40000400180074020f16a201026100c40900c220494908000006551600d0f150291403e00020025810100300107240c80c075007a0b00310301c40103018101d1072100005c1074509400f40a04861024120611300884200303100c010f400c000707200305e05640d02d882e10000082c22510940d42d40a203402608c07040140341c068010806010f1001d0f0720300510034a4010f100080001c4219140c045040b14081a0701105002180d6465242c0d800740d00b006103018200320340050703070107501084107100c1e01080000a4250080006103803107100784480d00c6000380011801e4a1440b081103030b038029440103c0d410f0031040c0c0c3d2004c0e00c0045002044500c40c074040103016141c2030020840401303500303020091100c0030704000e0140c000e003c0101010320071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 824221969 1250 824220719 824220721
    0xf090a090c03051504031407020d06092a05030c032b0207181b050c060106050d091e0516030f0807030915030b0a081506060c07050907031e0e0a020405 66
    0x1d03904088020340d400010350703680040201c05801803000c22101540404c3c09030f100c26500c940110200c80d00650300502402113100691200b00c0100309801c0c0490f4401900810b19480140700c030880300d1009108010380300c0d0302c0d00700814903041030701b802111406a44001101998040b24650089180d52143c00400e034102142c2800c81c6007600a034000c17803091003141182c0d4049440e54101a2800c030310800741400045802c9021509807090300b407528010b410010040c82a00d1146004011180e80c9250101e003051070b588441480150303c070102051800d0001900c4104081800749290904540c15000c2c1305929540f24070520081c0700e10f00602c040f000007203a00401d40100c003203801400103c402c80f400b13000c02c20700c094020f001d840704031071054141c0c400000e0855000140703248a204801d124444544511080c803644e500030801d1042c1e540240040481d10303444401d4490b12480d441e03900800c07002501c6040b060701c180204c140c0844c3c01d040811007180c0b544002244d4a03055419140040c42e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 824223219 1250 824221969 824221973
    0x6020307021c11060c07090b01080106020d0809070b04060e0411030c0717071a0612061006030e010605040c2601050108070804050a02030123010e13020105070c0503160305010b0f090a09 81
    0x8046080c0c03039490384444017142454042000207105019503d50b08130030440500d60300c00550301c0c04000d100d4080103034031540c0c009079118481e114142e0052284821039100b00d880380c1540c80a83c00981112000441159501d9083e02d494090001e18504111201d4950f00742010044828800e006001c4c01c5d290200d685040300d14084022540244e810401000c004514100c08240418003038803e1881411100141c5206c40408103089018a07000c031390040b41280b0340782c1c06030094442c0e00d811059656903034000140d01d03103a030b0244907000e8074640d840000c6450302c0340104000d442594014035240345040018410f99803c40307080380e080303011400c02c804113075120324150b441c0003c0203000135059404c161203d01040360781d120a10107036000d10341000c01c580e02c580c50a80c2d02d85003115442e440040c02e882d200c0241d40220002c0c10201e01840140654a4840d008203142092060f1256034043c40920104203200080c032440e60003101c00c89141801c03000c410002602e860000d005002c0050f60388801c081 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 824224469 1250 824223219 824223233
    0xf0203030c0a06141b0a120908071202120a11071517070f080a1d0f07050f040506090411060c0d021b011d13090b0114090112030507120e03031b010606020307021c 71
    0x860103650300240702036185032500c0083d8ad04030841c01c6541d020740d501e02d903c04500224464108200d9082814204240100100c03001d40074400980030754010048045101802903001406e940302c940c441c0b40001c1080305110b5075500004040b00704000300c501100c280b00fa84404002d4005032000030115140800c1408214910b01222100481c1d105020406c4c035000310104281003264022190051210017a000780004e5900c12940c8a40c03141b140700008000619403410810351140c050503036401d202203210514600b062841e054405070f0300180c0740c1a02c4d0440307030381c221100c1407007803828030642001128000304071051307068880e03c200c41c46101441c09100c503500c071001040d044600f4000f6941e561810340c0b56421042c0345940a80704003000071401c1d480414a0b00b0615a155843c0c503d0a0036517107810320710035901e61100d41044202102007400359020005400401c0e52414070a4581301c103d049a82150116803015040d50424004480903a95101c0c10400e075041d21810580d840c500c1c2d02d4424 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 824225719 1250 824224469 824224487
    0x302030a1b0c0303050105040b13020d09120e270f0c0903032b021c02030405150103110102011b0f0e190b03102108070f0203030c0a06141b0a 62
    0x58040900751039141e05042d40300071059041d5010752000c00099888105002c1070b02c4540000301e0300070400240420162902c0e0b4000d100c4a05071034030000b11300310b01d50f42d1004015504602500010001c0745600304615044440780101600141d541180f01401d0220340340000000380000c042c0e4903607a000880070035000c01181c2c1c3ca840001c1c141c960726416128074071800b0350690320000d28420b24140141e1030500d10300c22076241907034810746c01c065400768004c600040c1d40001c20842d840e0060318081d50f010810390300b0040c0614410309002e0900d9198038002030840c0d200d0007060005104c100e2500c00010b07080f04400815581601c0c021070f21440c3c220125581b1003180b01d4984541d00440c00010b0f4200240f00130f10b0141d540c040d0310589007130362000302c1c1641c0c4c903c1c0f800762010f04000c4071202000441d010000e146240c4610040440c0c0c0c01181c00103400d58200442501090700b1561142003002440c0c441c0c155044980c3d841d00c0f4186c02c014a010300c40302d01d501804030074688005007104a40d4009d607901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 824226969 1250 824225719 824225741
    0x170d03051303081e160e030703030c17040312120e070f0501140f0c0a20060909041e0b1005011403010308071713060909142a07060902030d080112030302030a 69
    0x202c0300a0a2050421105c81408007106000a0b600d2044010a25011588070300310ba4041d030b2084003450098441c03500201906c1203e0402c00c00401c030000c00550540300e400c1c0c03513a015490b00c1c0810280a04950b05a41c0c00d500808841d812001d01030040030b5440500c0b07001e075002842c103502220002c6d84421450b10035440700c909015404201100990000150500d15510541002440302d19107011440c11108c6901219400481440481517505000010f1a88540a403020306a0441c41115029004000d505c042c0d07801c0f08400b0802c00891250f42c0528000c000070319181e031114540d182c440c4203e0006000080050700002400000d1281044204603841d14030103450b940c8100d00e40503580402000e104000204001510001c3c141c00688a821103444e00b15080081a43c1d80d055994502130307500c5813090f441508940c20503034010240002e45440c070b00c55000007e8909a60040501d04201d100307100040018490050201e10100c0703070115001c560500340541c0b0b035242d00c4102400341c0001000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 824228219 1250 824226969 824227021
    0xc052223101d04061202030c0d03080109020310030f030801170c091b270a240332100503070b120a0b0904061b030501050d0305090a050901170d0305130308 68
    0x80400c0c6024000038006140344220121450036070200140100107100d02030140102f00903a0041200140d030750011984107000d01044d070460380d01c980c0c84114403002e125003503001075081c10040c452040c0c850f204041d1302c80310f178000b0004c948080b030000b40c0030f40000701140c0d201d18000700f904403560800e1080c0c580705484108800e000c1422201da10006180c400b210900c03078100d030ba00c00159041c05011900f100310f24400d074210313104508503080e0054203800e0f8842140e020000d600301100c411a41c2030818604003040c030440103060080c20b54407644d0080e04070f940320f07400c2280100525060031080300d003401e105c1c4c02140f4040d034403020620020b04411440903000074a4008103c01c1141d141e11001146c48101c214954164155004408842d024018190094206465580031a0059002d003204a100902c0200240c2e1104081000c2504c280d1002c1c1580c8020107440304510018411040207040500c0c04020354034013210303a500920880b0801409021101d004a44151903411000b000700c2911070b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 824229469 1250 824228219 824228231
    0x20f04020c1f050c071208060111030a0302090126042603070e03190302191104060b0903060714040504050a0209100809190b04060c052223101d04 64
    0x400c54100302c00ba102044080ca020001649000c580781591400d0f0380055101d00100c000c071400b901c2e078040142c0100e0500181750b404821481040000301140c12050b0f402586820b1104005084c8041420801d085030311042c0649006c104040441640683c01c01414004004043c0003d035803016a080d510304248070020401c2500c03030308888041e0003150154101d0f02d0003003000c101440b0100700c482009006070012000c56a140e44455408500280541030b01100f05042400188c112602c1d0b620000e855500030402d00745901d4144455544100c543c00d225018150521030300090348158003603107124a94610116082e10110b038161a8070100190010075412407801c806062500c0403031b1041140d02c1341413402602122070000c541c00313240d0f000103a100b0380e03102d56690700c0140241c2c0e08148108641400380c490718201d0f0000c60500e4186490400406a003042702600968800100ca5000c21032107410340011600c4d03c0d140f8800641c50f40c13401480b0000b9281c1140d520449052106038000e051030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 824230719 1250 824229469 824229493
    0x1e0d0525050c0a09020903153402011b1e03020705010c080405070f260c09040803150906011e023a030b0904060e1527030f0403020f04020c 61
    0x70750700030402d40c211940c841d8a50b9420301c0383d0a030f01c582490990180c110786003041d0740b24000b1014540140e26440b205d079884160803000495000b20488922440c00c403100d589107019028450140b00303005082c4907841c00084c05502402c0400010300074180f0440d200c41c1d86407914442c1c0d06507224141e109000b8040c0c420703450401440100255826211344c010301500013907250480902204403005114608405035400340c40d00c80c0c03500018454481070040b11488c080c559107034103520b8400d82c428403031341d612414404040710968070185009030082060f50140a0303580c2c0c021004000e803800300b0301135181d56080607000700e04003051405181624050249095881c1e10300140480004151035003a090740840b94004400b036a061800598000c2d421f000410040f0704241c0045001001038000c0301d86008008920f1403000b8001c590400c10001da004104807060808001002a0804c100065040c00340003581c100c194412848024861011034040c2d8100f0303104c540507030700d040c0824800d85107946020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 824231969 1250 824230719 824230723
    0xc031b060e010b1813080c0f030a05190206010b040e04110a080703060b0a060504030209100e0c030a180203030d0f06150f12140a0c0c0609141e0d052505 67
    0x40c0e03c0040c80342c4a0a00300513130041004802c01d201c0e803c1102ca600100207613495800b019401090a0041400b0304100020b00082c01c1000f0310340b4902c04c0e41c60580d20035860341c209107010046e941d007000715008030f00104400000c04050b98252400c10000c01c1c0e40386c46034980081c40043e01040c0d170390800d02415000400d01000b00715201241d00a01040c404012488100708000c0200d000d98004140103100030310140c02c000d210950b000740c49034420880d035a10b40b940801e680d94110b44840322100000704000140c80700740140300042803403043c54a001542c0e43d001070f8680c0a5003d90442042c0c2c0c910100488014542180c0d0007400001c00300512401003820085c4500440c40380701c0041000d1003e130141c00c220b5442118541042c0030a016129200c12041d803003e400350080385420400500174000c0411030520170419403030311500110001241c040580b0b0f0070840b5402d02c101c3d09080d00302c6c2d10745400001207004201d8045503d4031075551220f42c480700d810301400036040c03454107100b2540e0400300180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 824233219 1250 824231969 824231981
    0xc0405010e0702013605210304060e010e0a08131a0706050610090b03100b030a060501020111070302060604090503300c091807120c050d050907060c031b060e01 70
    0x1d0b03000b40711407a071028645c1710381d030305980503070007101c1d04950300d005840710040c10041694890b009841c01040302c4001000000e044400401e82100d0000c184000c106240c800c1c1d040480c6490001e21080c1e24010646884e01d003c4100684155070004000804807800e1038402d000c0d20510b00441c00c4001d400000305090380020304101c603480c0c03501010451503d03001509002d5103500380d0b51030450b030b4242549074116800250160050803c40c11002ca5584029000b0f0341c450f039204030000580916007000242510402c414841010004000d60b50109901040300396010f001610041079034007252602914503c1102100420080786102400c0c81c08241d400f402081d192004500c049520b03298100c08040c41610715156108441c030200070521001c1a409070790010b4941030585590709848180c0d425507100c0001140050000110004000700c148591170f0000c103500020000d45090141c041c05020341800b0103824040f180007035108440380b131907168240d90390018060007980e604015031800b03004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 824234469 1250 824233219 824233231
    0x17061c030c1217010306022203060c03110a0537050a090f06210e030c0f100203060906060c0a1e1203050702031b0309030708330601110c0405010e 64
    0x190814841c2d0005201d0340d03880c2100d0584140090f0280d18560351039000394814005c5a80701c0079018100d41040c0401ea0446000354042c19010480c0e0803680e02c020308560b108140c949284800b071040d80030890740b01b0141d82d80c01041d08a020680e0303944400100c03a585240c06000410040154501c021950050280080701c1e40c2c0c1d100c881815031103407400a80f04c007460107101c0020708040181c5040152001c0903c010345040c0c00001082c401e070800c03103030442e0300400700940c0e668400242c02c107070f000080101d01c50740c172201407045041d4181800001e122210281c1034510840d808180800094020b001200c20030340c0c0706041c12a06e1084904041e5605006a0180e415895400a140c07001c0e000c3e002d520310a10f410b034051454400c0c1850101035010001c0341255052000380000b01d01500c0410103140030b003020200801d40c039115060420b511074401c40c100c104035000801026030b41c00e8416201a00b0890134280000500c0323050000c11303e01801300b0141035110307082c9030001604900c84132525000750 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 824235719 1250 824234469 824234483
    0x1050c030c07240e1003091e0501290f24041806050405040c060f090305100614030d080604021c0c09082401050603070c05100e190317061c030c 63
    0x41c3c8407200a8411054040c81c81d504912807140c0100b203e803181d800101014070800d40381d0741d07440c0750314001a84020b02d0356045a440e907460007408800194003070081c518078203400380c2500f8158800c000c901803405040b00c00b80604054a50100c1c800c8583c6540e4040342140780d60725454070782d20840d080c5012041d0210ac6005498040f001c1081d041500606104a0b002035000300c00700c0c0b070214121100011070011000b0090440c4020001a1040c07001c0c69a50032003100100c0c1d6141010015595000c41068035446a44110842d400054100074502e84c851811a00140c03900e00c400781796000080955030070301d2000d28094000c0c0701550025215407c0d641e4002c12034000320240801160148098644071649503402001000b062174071000039a4440300714038040b51a070220340d942e030340341c654040300c00071500c0d849240d0b4521102d810071110f405143c140480c100700040e02d0300d01400303415804002211580050300010380c17544412074410781080e500c500051a500e41401e0042860031408002c852107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 824236969 1250 824235719 824235779
    0x52109031f0f0203070c020d05120c0307060c08040c03060f0f0c030915020906040e060d0804030c06350403030b030d030c080105040902180712061202181501050c030c07 74
    0x103242d0310f00c00d4911840c03494640b8062400241c003006002e51801c181140c03035101d031640300660030105001a0412441e10b0001319150812450308130300f601d00070100f0314200b1001a0400002c1209a000f00e0100d07900618002000d0105c892070130050f04a04130106225030420700480c10540e41544044070040c06850f00b0b00b5a03101e074080074401e911800b1000c55003c1414801400407082c6000754580085004000b00811150faa69640854202d68016103048180314410495240c03c40c2c2111321002121550209075400213003584010300100c41e440c1e2a1450582c001030415020703074466030700c0c90001030880e101050311440080103851440000c8000a00f104000922401d180c040c40c9200c0e07900a0184c00c0110304e07901d0310342c59404010700c0f2000f0003541106205002a492003140d026010142c244040c00e46540140041c015100e10b000034540341e02810422640b507410300f919500c4509280c110b0703403103014020f640c0c1743d4050740242c0101809078850005000405d10b2058400c82d03400004000342c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 824238219 1250 824236969 824236991
    0xd0e0d05121b0f0d060905100503250e09150c04081b0906061e07030e18090c090a09060f020c010c0507030206070315080d18050d052109031f 62
    0x60420b001d045848103505010b4024030001000c050f01103913410300c3c0000f620301c0c4e5441d011001e80350241d490700507072012031505010508003400748000c0302038407820300080400102e20707112004e441c6200ea80c80903428a0b020918040c020300c04c0c94894000070b40c0d408000e09101000b011140e1191003054070070311660010360112111406a0043c0a4004003038644a80c3c80c0001e003d19580074003070800c0e80c00b05140c100d020f240c003da006450074038005c1d903604441c524010140080c07107000202005481250808220346200c0c002060b003040348059425004540380c0c694000042c01c51244020401801c000c0301c00d03e5100258080c010603c0010000d0040424000f000e071650301c41d071000035005030411000940044e000750072031050707445504c030000b60007a504c40d4160308080011400d00001000340300c4d424a03040c41220040040d0a0844081d80141c8595a074560740c0d0205280d03001c101c1c0c0c4010180c060001d4440c0980714007140c0602512100c444002034203602011250180d10072500c1d01c071107540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 824239469 1250 824238219 824238241
    0x6020a0806120a02031c03060b0a05030402030105060612191b02061e01231302070515160203090904110d0c17030310141f110c03120702060d0e0d0512 66
    0x215160700a0090b10950b0319011b804030528007540c210700c5c03d25444103c00600c01d581c070f00060522038100e58589883c1d00b86071040509480c8094074041c883e0000b849460011001c400001b0303003103205641c60707007020702d15407101d08042c0a098101d400760701110784650614540118410744503410a401e01d0b40025842e9100b003002410070b0180000d010880c0a07000c000013060710b55000a000d0040c0a000903002086000007030740d20000707007281e040c0c01880c1206134a411f2694184e8000d400001e400036603034075204009580307004104d90240f161072140b000c1342c14041e41d115514644032010300320001b02503450408010b8410f451044007504070b050480d0382c00406020080d20700030524090312803012850030303102c1c100b85150041150750100c01031404a408103051141d00500301190780703c800302264100341003410311846800080c026000a100c4c00c2030340000300c04940c082541124511b4440700d14030741000003403158003003035040c511404445900681c0c00001900d10103440d4141200a581ca55010034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 824240719 1250 824239469 824239483
    0x203270c220e0607230c01060b0405010f020109050d050d0f1d0d02010608071401110105071101150e2e09021201050102011b0815060304060903020c01020a030504090903030906020a080612 82
    0x903001500f92100b0518000d96001a00a080003a11001703060401c268411400c45239164001e188100000404020340d58004441001d0b5403201e000070001e503402900d85070745800f1034021080400400190030241262684d02c030701d0000b00000c0003081040d01845d88d02d917030100d007001c2d071050300c1c8102c244211406105006030000e070394802024000711403030202103100407808020b001e814070804200d10040d10509100b400c0c0302d00750b00e0b40c42c200800010080c250855074288900c502000d04440248a10f409082c2059082135a0b91307600505600c0008a022520012114007800342d50310b40030005041c201030700034206030900080000ca141c0da070741700160b08a81808080042030780240c9100212940141c401c41e070b00140500e0750b08015400d034000201c035688215001c5031015960380820060641c1040280070440081c002001c90300d03143e44000d02103000c0d6102e45101940c450084e00c00b014481d800c45c4c0c4020307038015410354640c8202c040144c050001143e070342d8001c9241030300302880c40704002654 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 824241969 1250 824240719 824240731
    0x210a02071e030230060402010909060e0f0901020f04030309050f1e040509030c0a0c090515090c0901030b04021602040c091818050a050307050708010203270c220e06 72
    0x5030700c0c543c244a445031115400d1042d080100c0c000c1c2c044140c0b010036800d80a0b50040c080e201603d407510000d080c20a40e5002a1410f41c900701c020302944807201d404640004071078291030300c031b82d1340d040e0340501900c9180000c1034030b200c2c00300340001019000000700e03080d15401c4852a02c01c2c41d100c010310000c0d60a6a806035005100040134854074186540a141c21140141c00c1d20710b015000c0800034a041c404980c1216a41115581080f03a40000e2183c1d44d00480500e40908507800b1440014001907070140c2098141000040c02b00b00681c001c0e0301081c80d014000d03105645a80424003000004140e00400707030300480c140072080c3c1945115681c18800d40d8080b003000718282004018007002001004902a010940100c001d0046141003011807074031031144c0001d42d031700c40c49407801c0703410714134160301894460707006000b44180c01d6008424000794044d14071681440d01d480d44800391408065060756030700003040c410242003003822107010901e8068a000144004000aa00700b5601d560860301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 824243219 1250 824241969 824242019
    0x19060908030711060d0f0213140d050a0201080c19050304050d0f09170a02060705011514010c020103050a0b04060303030c0e03030f031b0d0c0903120804050d030509210a0207 76
    0x50f04000d0714112010f84010000804006100399882e40403200302d0384400858050015000c208114100c8031840c501da01100694024090751a903542d80c580c0c5d00b0100c0c0e030003414044104001380e5070001a90558a904682951426002e1658000640795500c251703015030391030045c0d6030040c0c030395030081c00c0c0712042000a9880c480440e240c400a0300000980422a001c0c07802040c05800150f1340b000064a401c50081d0000203010a41c407000c60f20100581d4006407840321594136100041e07030848444000c01e50203080205495580316800c20080c03d04241003a806071400703801005141d8540d00c00800c1c4003007611210340240024003095a0307406100c5104050110402c0003c4d0074481c440c0c9149000c1103d03940d10307410700d82d0181d83e1905840040c0c0c1d006000400345a020014070080540440c00300c0d01c2070070000010b007070070f44901e9120640707850003405144e00c0d507021a00c001e40c100046e41d03140602040c1308405401c0080b242005d0f0784064803140061003071000201c0c0302c405c000d48680184d80842c030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 824244469 1250 824243219 824243243
    0x60c050c09071205101e080318120a050d0305070216120c030206030c03040b070309110405040c1205010f110301050607060b0d020a140a061e0815190609080307 70
    0x8100300503100415840c100000c041a400761624a4001e02c5d010340070040302c0d00000742c10864603445c40c0708034026801c103840445100b0814840c0200484400100300110843d081c034841c0c0102e991440e4002607e40039219480040b03040c0180400e030350300b0b542c8856805001076150340784103e0752884200b9074000121180304040221002048148140910038410003890795520b400207401508116591000c002c8000200420400c00810355a4403010f18207041004032126125184145401e0945600955880000c5001d1040c0d100d102e200802140424840d610828901140a451200c2e01d00c005181414030060b08a610350040e02c0c1030712006400e0504088098451101801c0007249035a04000c00a80b04005a11103078181c1015007200d0702d80c0c10346100342d0400d00003000c9540c0e10000421039100410121040b0b848208000350106103800100750b116903840c40509400d910250390702210a107890b54451038608543c00441e80b03551219451103540341040c45d01c03032080d400010801040c0070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 824245719 1250 824244469 824244493
    0x12040501092d0f06030b0409080405060c1e0f0c030705100503041a01031a0a0b09151c060507080c04060f050a0e5413060507080709060c05 61
    0x11003080460460000400700e1411030080703081c0c185600307401c209644070720f01c0b10038805180c040c000c412012405a50401c66405543c8408580c1e026a008641c0f2441002901002601c000c00ca0008901182d20301c02d0525284105815a034403002d003107282d054040d1004007441840c02161060840b0006400e80e00c215072044800ca0306580014804c4030140141c600400c203030030350401024040d51180c4692407150840c4801031a5540c00101205015400d142a00d039090312201c0b02290000102c0c030000310101c11310b40c00929001d9001aa01c4031700e074071100c2001d05200403134020902441d1a40c403110800d031a81042032074a4490b602914001c04c2012603d8400148903500a14a001c0e403480c2c4200c08074401800200d0086558100c041998110400c1082d070024120503034040f00010608902c88120540d04c0100000c003800c08010100c1e002400500c0c2c150b00b101c1e1081c1c246e5441035081140e40741c4010058030b400e070b041c2c9480b000030b007003000007082e141d0290b00da01042070f400034010140320b1056 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 824246969 1250 824245719 824245739
    0x1503020702061b0d200a02010509040b060d0209040501060503010305150709080d0c060e0d0c081608030115020c0d02090a090302100c0201021c02160803100518091204050109 76
    0x2003030100d07003141c41005100032010040003901803030311080024040c24811820000e0110840d20a0015080307070450307407444050f00000d0040959642130070315944524560001400074504840f0298100c0c10000e003440319072103e41d006240041c1d040764200940c1c1d0f26510226041e00003400300800c1c0d5440007070400c501554458030998007501902c6c05820158440f088282070403010861f28022030000407a850810100b80109400080c1c4440100503400301c0180090403a62041401350010701f0024442c1d901058110300404203d4200c0341e096500d5130341d407e100d01e600308074040840050040c1c80b00701c00329180c546091601c0a400400e40c0c440c0d9155000d0b41001045000400c80a41c230540900c50b04028003070044900400c903d13000107803160304e8250b0149019001c0b503217002c521441005121010f088040403807002135004940c0c01c1d00e0359240002d200c540c9110350417040d449016000b240304044408c83d07915200b5114901074030403885007551407042030b014030f00419011401303ca4007070207940c400c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 824248219 1250 824246969 824246977
    0x9121f0b04060f03050c10020d172205030c21030c030a141006080108030306010906140c0102040b03041e020901061112070308010f0b1c05040f05070627150302 70
    0x100070400952603a8a0190108103407aa90007180c098002c41d075842050f10301556000a80200d0f4005445800c1341104001d0809086401804541c101c550104001c04c061201055103041c5581c04664900014102195a50031102c00480c0500c501c55500b0701c001003607070b01e22a4003c41102d1031415a1202c00745194507800c001d00403a80343c0c2d550090340101c0e051201d14a0f0040d904070000081c25801c0001c0100000c005030080882a8010801c0c841680d9218040c50100c400d6441c00400c1082c2e1914003004a1180e214005460f40c0042408076a00502e0001540602d1151a44000c0540c3e0059103041c2500a0100a544409031900400c1001d02807480c1902b000080000e9600201441580001540003034000b680050520001807100b489605e41d040098056842c009040c10194180b590400762199406240e403600e60b00810100201c0b0001540400da01c44203641c0f04039118900102500c0c401c607140c2c1717181e00e5070b10102400304080d05c40180941f999071a01c004010306080d0160301a501c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 824249469 1250 824248219 824248241
    0x510150512030d1515020c0d06200403030302130501020f0a06050c07060204030c05012006070c0804050d260c030d020307050721120e060f0405120d0209121f 69
    0x81100070f022502a1243c1c2d80501a05503c400c2000d042c02c5444241c2c2000c048280c040d903104240c0125169106260b80c20115800040400d20442031240030403414528803054411187c08140401010f400d90040d003d460004001c0c15041e80e1748a004a1791401003190003006030300804032181c04101c042c1c0041d030f400556100d0061511069075200400c0382e1241d841501c07501c07100f020601466030303c0001000e01d0181040c048410301b84900c0341d1529100d001d80403109100c002d20340182006110030564004200c010b2601162000d42d08005140000c201680b580001000c604845400b60020940318a010a00001c41c00d0503aa140100001e51010344080b061003001c6c003a40002610b10102c1401c4002c00d40b242da403100b001c0b884e0140500c11007080302000a424690f45110f03c04000450581c071a4040034a01c41980302d13800d1040c00e00014540e0070f18651800603501018400302c1c2c000302003411003524050724100e040d6040075141c00103540800a1618503071403c120088107034200591240c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 824250719 1250 824249469 824249473
    0x4060513120c031814030105010509071e020703080d050912160b0606040305030a1d0d02150304030e060301150e030706021e0c1e040506040b220f09050a0510150512 72
    0xd2011340440300b5820f1280c2c0950f2414148524848090800b0700901e8010601070361840c6980c109200c010380b541035110400483c2d8aca41c00d080740030740c510800c1900000e640010041d40d0341c0c8810060f600140104036030482c5240300e018910041100f04104949072000c80e62454031b561a401d07034074a504408082e180592000b403e200c00300100d182403004100792006516107612b00078045036901c41440ca03101610744141d03003286408016844090200d03140007030030094650303a0b0740c0e145801e4070b030202a501c0c0a90003c1c4040004500c1503c02c94401c03040004039100c0c10340d401a40c400b01681c880d0701380500d0005070000c1102c4a20702200300c0040d600d0b4581041540c10b05003d440105050310140c0122a11840c0c1c001c030440707500c0c180b40c400e40b50484000c0d40c061100301882ca01144140d481851503031003800002d0625001c0c080982d011403109602810117001401c40303030420540e2052801d800741d4aa0041c150110f000d00300c20b10505026820400a0001d02ca00d0708040103140131888011031468 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 824251969 1250 824250719 824250737
    0x50904110a2708070504020313060911040e06060f24120f07031803142101060305090703050c1504090507210605010503190207080309030304060513120c03 68
    0x204018030190500d404107548046000b50b100071a01420702c21003050355941010460706006010001c5001030994000b80c1d00035a030380e00c0303c4902c0051061140000b0300100d242688513403c00c04120344d0541c45c0e510465040c0b001c488094041501c800d07007a150740741d0100c070206041c000c1e414141d64101401c441d90f9030319400c120f00415040c0060380022212501201c0d0b000400c281c00500c190520b400c18103918082100c00b401110b071060b040c56081001d410b210102942541d0540c11808070b40110b1814801240c503e8038002c003032514400c080c010384001c6818440010340310a070024503801100e8011340107099202261040c818041401160050720040400c40810b072023189000f01c82c01081a6030307800f042c4200f0840d18100303070800840c0d070700c9580c2e0070010108666030748034003a260401b82d900e01c0d0543c03411414001c1c000a10030580000e20342c0001004000e50300c54040051031090740074041c2402560364035101d0801c8080600c0e401002c484007039045645191082940800302882800d0000c14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 824253219 1250 824251969 824251991
    0xe0901151b050109200414040b2806090218090c0406031a060a020c030601060f14090a030b04030917010c050f0d060521011d070b0c070f141c0210050904 67
    0x109404007040d203102140c05d0000030b90141003d11a201c000c49422000740038900f0310f5607132040094030280c05080744181c0d00c0c2d000400e580c040b540002165000c170008001e1203070744894070f00c0070b0f40081c241e80c86050140041d21509080c11055184075460741a00c040c5400d081c40401d0f0007c0814400c5030b500e5103a00040d4000e6138446000515054076150002c07c6101e0400c0105071500b00b05800150030015104d003203030b02d9550031a140640c032414551420f40c84004080c081200702402e0750001e40411105002d000a041e0080d040c0003c3e603603400d008006200e040c0d04040e0030303a03004102c0c48000640801c405603030b00ea001c501500400100b040d01141d00c80e0350b800000c9900d12192121119130b80c1c41d94141408071424070031000c500041242e11440301156901d6141c50354090700c25124107400000394104800006c2c010240034021840002d4845500c407d121101d0703c440426560051040804115018901c1100c00c610107038001c1004510343d403408800c0301c513608031088094000b61181c01c6009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 824254469 1250 824253219 824253233
    0x1e090e0a090b0601031505011d030304091d030f040e04030c0c180c020f06130c1d0709060507020a06030b040e01110d0606171612020a0e0901151b050109 67
    0x1008910300000441c1d294101d00b8a2038100d10050445030500d4034003d1801040781e0441c1c089001c849090170a140125001c0a07030b81e02c01c048004031150705020000d4040b078400015800300e00804038081203202003500d0700e143c4990b00d100b040703002c04201d50140410080d50714251030066000b4842d10301880804a15601c00c0a0504250001c035540c034440300d0360520501e01c0784a18000d0711007030b10042c42005003040e9085d85402000d02110010304454043e8414410307074000c4e66004110350900e8540402d04098904c0101c98203032a4040042d101c1400081c4141c03041e400e56403280d0300206611009450504141d0091040181d020b400c1915003c00c84402e62080c41004000f01e035100d1050b6440f000c4900281c101e8246030010350500001e01c80d90a0280710380e0303100c0f070361044204075240616490194191450038080d0301d18202d103800007a50b4414a1b621802004070810140e4040e502c90340c80c0e1102003000c0c01d40790040310014031069030401d160030314075012146550041c00001030100694803002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 824255719 1250 824254469 824254471
    0x60406200705070603150f0e04020f032506051c0f06081006170303010f060302030405011419061a0901120207020a0e010312030c0509010509030705100c170304031e090e 74
    0x2880e43d030030216013045a00d07050300840940c403441e40f034411019420b20303000c5000c2400707a01403001b04107540e1001034115200c0301e07005001c507003000b030490311042000c081101c0e010061820808404004100c0041d00600490680c0d10907100b90b00300d03901e06450343c541c01c8010712120402ca900c00e074454200080740c1100340455000c904220001040c040d0800340385041072480303582380d9480c960042004002d1000d01c001080c00790f864034034003d41d0703d4507a41003d6000d8405043c07910b019401a0007400390040c5000c00800148143c070740144503c035660070083c52003112181505045040c10851490558400d08a03a041075548600c01400d00d00503402243c018075803500446d0343c901c540e1300188113019181d404180130702e0013403509003c0d40520708002450360085400b0141844004100b032009070b9014040300001e001c01419004880d21500700040c181d030303080c980a4884040035280e408546801d4000c0301e20030798050b01c0340c0010b181c44841c84201c42075008154406c00241000200c0c0b5600310010315 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 824256969 1250 824255719 824255723
    0x20a021003062409032301020a0e040c03270c0905010e01170c0307120206070f060209100e0612070513031b0503010b0108010e070201090b040803041707050604062007 73
    0x510241000304004000000d400c2c80001e402c24000d85000496201c0402025a46c2c071001d52100c021505034900992811201440c0265002092030350056500c050301c5d100101080742c042c41030000503002a4211114500311a9485101052510024169012941800388600100305503944d44240d003204030395080c2c2110703c04440010041100101910341c1802600c131110250203030440c1c42d000260b03105010703c228054104c0c4043c01700195540c0b6070a03140d4503904050094980000d44c94260000d43c01a040c09216041d280d0302500308901c00c68401c0c0001c0d40207080a4900034080220080d1704800410007010401c2c10400000130039403110141008500c41d0b290b07007041c080c1c0d090080d01d07419060f800c000e0180c0e1512410000e140e0b4080c200c18115059001582e40544500c0012400b401605102407d55807240c0c06100800c03080c40025807003940160307140d00e540c03417610104032034074421848007800c254801c03408100072500302c1e40f100b103c3c55958542100d104040d1440541c450f0489042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 824258219 1250 824256969 824256971
    0x1140102150a14010b12071407060c0c020a080c03060411040b0d0c08100509030307111207150f0b0607140c0a2909011709070e13060b010e0a120201020a021003 70
    0xf59441c001c048444280c0500409800e05080c0700b03542890380c250b904c004003c142005050080c1d0141e20f00c540c4100c4440c16040358042c400c40c1da820300c0141241031020012405864007120000d00084042420349243c4001000b40c100c50301c86446011044028a803103a92142c1d0710700c80e6200a54074000e080e490b1501c00e44e02c0110541ca440d10b900d0070403a0321003105840c0d6041070100300c1e8402000c412664407405900b050188023a4000c0c01c1858051801d6404110081c00102c22040c48981d80101e0814504504144101070301d028000003604c2502035620b07040007050201d440051007050048401d41d15150403224002c0608000424914803940646c1110a102c2128401e9840000c80b0130b000000c07040450b840c002d001c8e00001e201000114110b1454001800822142c4000f484003134014400c203503041c50b15040c61901010f80a0801408650312071030704001c1409540034001000361003000510401203103107003941519006a880c1e00403411805064800e40c01a91040c0000e10861443d43d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 824259469 1250 824258219 824258231
    0x91211030718051e0f0403090b0a0504081e030a1b080301090e010c02010b151804020a030c17010b040b18121608070312030c090306141504050402030601140102150a 72
    0x9814100d0f01d0107000d6190b500100b01c0020940d2851412807a0070082544078906240d50703a0900300c40d41c1c0003d401c4403804150029100e00c0d101d034040c010703000b41c07109a81522801c0501a104000000800c0d102c1e16240d0418018028410701a24500590041e05209002002d802da502d45060754002d8000701880340da0382039190401e200034440d01014450b18002003206d403420f040000c02c0c801c160300d9074013264180020313003040640142465180102000e001951a05400b00700a0050b048a034414800118503910801090070f4081010781240d41d2003030081d203014100707901c802d06580070496802143c00c41140c0c40100ba200c0d090426403140c1d1480c090075010340c1951050a0064540d84040c01d10303070101509101281148284498141550031300040c809048101503c01020719480602464542283c00c01080400c0450500c5030340b40440c038035440c1018200f0070088460a86020750164007a034018040b40190403040d81920005004440302c0301d040c1e802c400d4000e001203075800d45890700c0b80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 824260719 1250 824259469 824259509
    0xa0305030a051e0c0d090b0103080a080c0301290702061b0f12030619050307080616210b031207082a030315061306021b03010c0912110307 61
    0x40b04040e0048690800302e10b40046020303e80c64070410141200303c10200002e0341e02c85065103980681c0c480c0303a004010410545c0d40b0300b012103080d00203003070180c085111040040c4500c100901124141c5034503000444014613004800e195594a2814a19208004104940150780c0b282c01030000102c03030505100d0381e02d650b002d131a4201940c2503422a0240c2c0141d0b0403d100e4a064020b483c1d12903400d55049400300060940780b90700f40c00da51b11241e054090600017069451010400500c14443c444041607c0300d48100d007154100344180e240b9000f2441105240307403441603504255800040181207882d900f62103030f0740c020700364840c3e4000c9540c0b0740c001800303401c46554168040d500d03032145840b44002d0750343d10704030f60b4480c070000380340d400c2407460034200780090355511050f82c03055400d0b6400c0a0304140c0b90040a543d0321070701c40e80b0800400c455401800c41d40b505000700c841800e1700c0d907105e940042c07030140d0300000303000010402c42e000d0300b100c40300390700d0b40d102040200001c200007040300c030800003c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 824261969 1250 824260719 824260721
    0x8041b08010911030609030f0c012705012a181a040905010914010302120f03071515050a060e010c0503070f12050c15130501090318050406030c0b0a050c0a0305030a 72
    0x3c3ca441c040d0b0490010080f0050780441501c1e0a8030001d09101c2e0b03141002a0f0290041c0034440002003110310764000504803d1500110100d40c40c441c500820117006040111106203020318100e45002d120801000c0c41240701d10681003400c10341140700103503681c0b1402e51114488211010b00c108080200742041600c8136401854014420760108000c2e04501078403035110201c0c1400040d020324001a64041c1c034a00c100328213890328403118207a03502e0b060b40b86008009959114011076201d400d045884000c40181d0030103c00b1640d004107400601c0c0e190810030340310405080325190601c0a508030f00380109200303000601c2d030a0311582281e240b038065464071001036601e242d102c004001003403104c00406200025201020f07204105054401c5e43c0c0d00b6034142103101241d038000d18a50a0501170020542c0008421007498480708051911381c0d1070f10148001c6503041e00c0301510b1102d00d800100441d4800500400900714289440c03490003280d104280e1414440000440001d0000403c02940d1411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 824263219 1250 824261969 824261993
    0x100215090f07170a030c02060c0106060e0f0108090a0605150a090e010c080c04050d0215120907080c0d060c0c050307120f050f0d051012050a0b06010f0c0308041b080109 74
    0x20700f401010701c0c4001c05029503550307410b1250050520100300c44020540d0b64100665400e00c07102002071080603140c038401070001585604090003004180110b28956004880d1036100301000c00003403094034416220706000d450b01078403a1002c4680302c10705060f5902c13075000043c0a0200e0200119801c040390b0300c4142120592140c01e4100310340c2c4814001c5070145001103408890003201d480c2c00c0ea00203800081e6000480b01c0028500480002c0c0042c8150b5030255503034400d0000100351a2601e035150180c544035444402c09070740c04243c4060340800102203a00900c245286454030700c2e920090741c0d9a1030300d554403150342503400b41c0307040401e0548141e00181c0102c9103089071818600780b007080900100c076801007030301740c461854682c0001401070500020100c010070717a845103000340d1511410416100d40c440107054a00c210650000f82d2154059003a42140f032409a9440302c0d07200c042c0d00d04a40804000c2c004071824030400450082030b0140030a132802400c0c0b814000224911140f03070170601101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 824264469 1250 824263219 824263229
    0xa031a06070809130b0303070609050114090d020d0906140f0d110d1a01080106050a030902030316150513140a06060312112d0c04090c050909010b0f100215090f07 71
    0x205017203405425803000b10a54200d40d83c420004500c130703019854058054914451410159600d040030010310000010703029000403d145c00b9550b0f0410384d020202c030420390f28001c030030205a4100240d01003a44034001488160021012142001c0503220510300b9034084001c1c903161010003140643c4039055911449644030801d200c0c95180c82c01100010b4904101480740c0014003102003440345005002e0380141461503030040980e9602c10940d6004401d10340000d6095030509a010f8200800c04000e210341c0c2e0060501c205402d400c00722540d00c3c003602280b50800c0c51524056402100c00203a8507006100145200703003946d00c2020b27504000209051610003070603000d58840e0340b10407165003080910301c044800c41d100340d0808a841c03201051406c3c2454008580082c5001c01c86014000c100c18400d003038910480d60002c1d25180c1811440c241c925044001e64009040c00754000d0529110b0303003018640d1220300544240050300720319181d0740c1c01c08880c841103d4110300036441103c80180034820280c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 824265719 1250 824264469 824264471
    0x15112101030f020d03170f3909060f0c1b09070903061508060a060e09071a070f060516020c042d1d0c030d0e060a031a0607080913 57
    0x1600d952140c6503082d0180c000a0b00882030300c0100c5003450700c0fa02507005540003c1e050007495007418a101135400700110340c0b10b0b41c40c00c603040d0b01100c8440e20f00000c5421604038100041026003458200c106940f14015065001e181040001c004038524001761040c0750918015002501d0300d680c01e5541c0c802074404062007a1820001c00a03000d8000b402041079940121000410743e45050b04169003041a81121120784906002c000001040e034218006984da40703010151075484881d1075599a130600c0c061700020564400e025141d1031404c10140041d030380a001209030603081d64071100201c51080c0e54440c80d601504a522120540400c8046459030041d6400c010302c000c0740f02801d1018102c045000620303880d0010b110010b040c160400c891030b442200401c0c84001003100f82590701d00804034514024040c14071801d003524080d20b0511001c03035001d0403d41c5040c40c001e008900614844d00708203220804080b210402c0c0d260a03001d000400d03c2002165a213030030680402401c8000202d00e41042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 824266969 1250 824265719 824265721
    0x114010906050d121b0807020f03060115080a020d0c052106031b0301230717010f17010f020d20041a0a1e09051905010f0507151121 58
    0x15140c0703e0707000c40019080a20380418040100046940940150800d8400040d5207041c10501c0601002804202c1c800c0710440811104ca42c00d25494120034801e6501100084010640450003020304540c08020340c1f0005290070200d8644070f04030b5a1a281c0e4000041010420384c1c81c2100d2441c013209030809601018a4a00d09000002da481915404510000c00100b000001548003500f00d00001c8a440c400440b4260304044440c0c002c1808641200000e00c444850212500403004894140c5c1d4014201d20344081c00c00e03a41d0701484180030307103040c00c2c1d640c0d41c0c0a001610843c0e00c05080c000507000400315841070300d40d60081500c10301802900e03032400b00b00010040401a03201960900428900454843c69140b4058032880c2d01420340014803180c80d42400c5240341c2c0322255400f690400c4030240b000010481e81217a445175030307001e030320b010031003840c2c08a13040e0b0300980107810075a100c1d0824a20100b16680c10f171040d101c2030003007140c2001c004511074902e0f0512001411004818138400611 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 824268219 1250 824266969 824266979
    0x72d110a020f010f02150a02190e0607140f010f051005010512062416060515010903170f13060906020f06070c0819080f0703150b03100509090114010906 67
    0x40340162050281400b00844c0d20351000d80c000d0200400c40c0700c0c050302c0302c1800c2c60710447e140041c0d4000d5440c445400103a001c2002c0b45401940034030303090076001e422541001c407a40c0c1d42c3c0c11010040082e0b1440b81c407400202a5032400c0034011308024280d11400441c0074103060304c40210b4168203030042410301c501400301021300420322400552201080322040c0b5554065685121280c1c58024501018200000c08100240d01d5a021500703951240c40c04104a940d130075148035a1071134094034540010200c074800c0000c41c0c00c5480c00c0c08501d50705030044e031900414090301701c1d00354000c00464032584000c40080100d50f40000c0030800800107800501075840301041125103807075005140d00140144910240706000480003556907804000114030320385c09030080e001d42412000c8a0307183d0600001c03000076244510900076503038030120101c180003407181001020020713500004c081c04050188c030100045c00355101007282c0c6c064044e0000008403803180c3d0018407490201600030703c40450a00340c0c01c00c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 824269469 1250 824268219 824268229
    0x606020d021522030203090109090207110906040e07091d030c0601091e060b12150303070f051015090509011401060e0103061e080f070518072d110a02 66
    0x20b05a024034400460756075504241c0b1001c441c038000140030741d41200c02c1060805130004002c241d140c0c000d0701c0300c6090030317510624030741a4415190300800d02c03101c482994419041280846801800080c008600400700741030f9107241040d1940f02c1c0003110344440c0d074071540700d010050240c45085088040d5103000030000c8a595941c0045c4507041a42c0d58801035030a9026148200d40c4d00524007a40c2806915911480040c6503008420442d0903e8481c00c0031540c1c580210080c5081d20070003034041c500701540d545800399807402c1c1032002d80d003d0080d60002c144d4070b501407090f40c80d10502001c111490508100390402190741c0108841e489070301d0680010b1145050940e040e04585051030403066803040c07500120090a855031201c80004080240d8141c031095407241d0400342c03001c500c1200c48041d9010207140e0b58280501c644c80d0420403108900e15002c282c1902d090f409111801e2031a5040e05c0c2030720300590000d100a01044007040100905020395100705a0100c042c10031000300256449500010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 824270719 1250 824269469 824269483
    0x9060403080c0f03010311041503200a0e1e0f0103020a030816060e0f010c1704020d0c0b0408010f060e092e02072006070b060d0c031e02040606020d02 66
    0x5024040c1c4807001030700080301c520464810200000e1190744950f901d182440e4405c90622074940301d01d00300482006e251400403007801c00c0b40d400c140e004610850403041e941c042e10350320ac41207820542890340803441c00203050105000b1a41110181c6012032014a49130060401a181c0410f0082010040001d41d4460744060240d039045182d0350303036841c0c1c080245600d016040b000240b045e07040845184601c000030910092600f40c3c00000d0000c005440412188804000c0d04200c0e001e40c0c0c140841c0140c00d00b01000d0503001d00c030b15590382d410794541c0f80c80d6006030400d40c8803182c03680d100d60030a120603c00f40640c81c0101a0002000001d050550700951115500e40e1420107488600c01d1040020206181c088070603210300d101156a83c02c1c2e41800080f804040d081110700101d890102022400c20310b0440b08038a40100e034402d03030f41d200c0c00204540c000700c4040588400c0d1003d1804404180c40040c2102d4030900c081d0580b551101c584103110990b01c00d548a40700755000074a0640c0c809402003504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 824271969 1250 824270719 824270723
    0x10e04060203151003060e011a0d0e12030a0b1908030a11030d0603050303011e060212161e0606090506100302070f1e110d0f0f030e040e10050906090604 67
    0x540c89564036215400703200381448903c0d5000415807101411140c040c2e000341d0a681e02c1c040c1c419502c0c2e80346c0c0340c000040001c50306070f40c0c0440f1042200c0300d6000150307030200d00c0c0d810315130055800103081000d101e07029800544002220340d68a003051015450b1103281001d07070031201562490294601100183c0700c3c0220900081800381202c411040b900782403080f03608421141504116040d140d003080c1c6c6e40c0360424020803040e510041c0e00b960768000704001b40c50444216600038099104255106800381c0c000c0b0308a901c118492410103000900348920540300c204011200074001c0f54142400300c2030361110b4bc003490310245000244800c0746c40d05400803400700b101d400c1c0903941d261a807408418201c10032101170005000d086046620400d10105100c00074003c0c0e210b4010b4000303c0041000b002d072030580080c8800081d40b21480050341c00e1400c000300305c0c080d080c5102513001c0c0d04003060540d000703d2100700464000303c9007c003440000d0b128594104034108014035452414040060740c2c1c1c0005400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 824273219 1250 824271969 824271971
    0x6080402040b04090215220509010b0a0c0803180c120303060f0303040b0c01090311010c0f0f031506051909030b0105090402060f160b092409070906080a05070e010e0406 74
    0xa202e603243c5843e00030015456002d0007014100c40388100030103c83e0801031011004850264a260001c6805130800b4203849009000070304030307442e24640d4842940b0100b201c00901c150601140017007280880603600c240c0702c00e4044501e0300c00f030300021410302444c460014803030400220001c80c1c1210000036280e01c0038064564659008180340000d20311b0007150311042c84040b0018a071040000107420102421307200341c031880300081060f03060138240c40b11042c8000000701e001203c044102c3c40390865401c8421642000101d80541e02051130040e1056042071021035000a60b50103100807a444840c01d202d66850111101421075880744a0b945061240c14414004a008102507603105012030312219609405555100c0c2e01b524001d8107481e51007000da6007488840c0c0010700e142008540707995440300000b011031030503180030a200325501c00a07003048038a2258a00200f41c040c280e100c0d1a001d82090401001414964170381646071101e5500050780b00e1404200412078403181c081001c0e00594403802c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 824274469 1250 824273219 824273231
    0xf070b030705220504050f0108030f07020604170d320c011b0305090c0a0b1c0b0d03030501260712050118080c0d020102090f240f220608040204 63
    0x380445182c000c3d0418242d81e0f0103d5107a084842d10940e003554100d440999042c00300c2d90700c60031400c440c100e09210f00c41c0c142d0010400d403050900401c00408030f00e4401407500e810980c480400c3c1240c2c43c0e400c1800d16a81c1e000225054103640c01080c040250025104e60361128000010100b031808883c144002074a60040f0722a0700f010000c0d0010401a1640e0140041015040500402400c2c0684584e2050b000b05e5034900300d2800c100b00341a05440303150031000d1901400e07007c0b82034411018000494180e58804035080035545004195844600075034004c0b640d035042c0001490b0800c1c080005142001140c00c8040c01c0c0c0101050040480c0c01d11030f410200341d0980d0070401c0c054200b60141c54408454451560104071a00d03010b080c41e0768072841103620034010554140e08030b21070606000d5000c021103410341558500440d601d000c1c24289001029411a071560100d4141c00420004142c44070203c0d194003011000f0610400d85020310340e840203058034014025015603409000a4011900d500e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 824275719 1250 824274469 824274481
    0x6070501090b2410090323030a021e0a0c030b090c1f030e1227030d08070f09030b0411012c01020c090c1204140a20030f070b03 56
    0x94060810560020841202c0d0310340500e660350580384407209003840c070b20710181803120f40c2890030000b01e500d181601e54044e0642140c99503180b04000f0800d1064001d13481440a54203c41032018005108054004048190281c00c88400010508203c00c0c1c0da680300403510b0001c141141545000c880d00618420507545880da03940c1c1c18203031081d9203560005510200041074242c4450141c03190041550200721003508805960b440f40c00c0b4690540f10440e0500c0000100980c1d00c00d0180418850501301a4550200003c00c0c14105440e80140200e01c2d50f104001009420408040103000280b40100c1c126040d0360700d1480602014001400805d42c00103c000300ea4024031000e101140280c050f0340c001001c1c3d50203079000e4104201d0300d034018040c601e1030380c032241410384030a4001c8810007420740c207005044400e242d452038010802d031140304c080c08442d05885000d001c0301060b00d018030b0390704d01324100444040d44910002034800d4083e40c400d1041c07500700f400100d0104203541803910040da90761282 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 824276969 1250 824275719 824275721
    0x601020a17030604140f0a0b01030b03060a09060b090403020d0f0905060304151a03030d0504020406030f0501051012020108060f06040f17100207020109120c120506040b0a06050f06070501 82
    0x489000302505031001c40481019400005584a840111410b008648602c0a01000000c0039076a182c8414090b03404601d103070600e40c00106103400c3c10314000600740c4055001a00c0c10788151500341c54076540314521018030600b80203800c1102800d50703d00070282003964009594440000444040241e03140f05c40024501c40c04110004120041c149074580c02e01d0706082c4940d0956002380745180c0e180448600008404035100402400000d000c2c500380b00018254802602d0020000c0b60301a50b030301804400540c030f0b040c0205540e070141c400010320f85020134480803104030640003140c4c010f150549243c01030703912240050f0300500c10b80c1c0310b189144404000c5a040d019030b0704400075103804800086100b00c1350000342941e0000e03440c201e80a018000702c10f0022441000c00c00b90020b200c1000c24418500c2c80d900246029209044002d42a40e1790045070075200100101103a00c0c0d0030017824842401040340210303401c0284080c5c108252403500000800301d0104111a074002e49001ca01e5070180074003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 824278219 1250 824276969 824276983
    0x308060f04060e071e0207090e0c0a0609031103060c030c07170307020c010206150306011a0706090b01031203050c0315060c0d0e100305040b0a02072406090f05100608060102 76
    0x201038002e008641c0c4034151800091401caa20000060302e26044103089022000c51348101d01468000d0a0f00c68241702d40d50001e4045080455030511819003151403d4448111100007002c1070355403c080d1a0031032800030a00002600f41e14402d501c00700901540c0400d61089a400461131180c10b641ca41062030640003c5000418208141e8404000c201115402058a09a4444c00d901380c490945d01c829044141e10968204503405600c040018090104101d14441e1009550311201d0b0501d450756440509a4943d0242260b4980760000100204100d5044a8000034840d0506201920b0b2039004095140002809a040485150400c0c001c6440386012685255a50805d40e03000455010020781600407501d082401040d4260702d00741e90622074400d0a0281e039001034242c0e815200c54280c1342c0690080e1000396410070040421400e003030b0300343c84103010143d0f076440003080b9180381a0030042110640e4554211550400041100300b68101e0a100241ca2060038039000c00d0f250351004030303e0894 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 824279469 1250 824278219 824278249
    0x106031e0504030e040c08090a02011b1b0e0a0216110607150608060106020a12140904021b0c03120702091b0a05030103170403030f0f033b0304060903030806 69
    0x310340418402850b038000d02ca1300d89081d040c1e07010302030045503150841d84100c00f100c1c24007081d003000c0c10020041d0320071089200103e0a203c040b85500329217464080d150080700d40070b080ca16880c080100036043d1500f400c0359100c11240d40450500031021007261070078003068001004109075090000300360b52010183d40c4c2c1650004086e64810a4484400d0010003d078000c0302c17883d10550000190880c0f00140c41580c013584442d12045039043c907039064591400000240c1c1101500340141000e9403101e03c0030f09018014440000e091100f40e032066070502810b582c01d58001d800c940803091000401808440145034141c501e0401640c030b21038410101074980c039010040c100000341850100d507001002d94140c1e4011300c01841034403100d50441065104a00c80100454003c50030720749030754081d240c048000d440604000c0f031790b69040cac00d48020340d240e10100a2480038840c1c450701e4014a0070711010071401c2d0840700452405040207c0604003405500c00101000030900000d0300701e4a980010008680c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 824280575 1106 824279469 824279471
    0x24111b1201022b0b0612071d0303120a0204030206040806011505070b0a0e1c0c11030a080f0a030e01051512121c060f1715010503060106031e 62
    0x1989600e0b42c10f0398a0354840d440381817621080300138035083c10b410160f00d00d545070503070001d0150000e200405c0c50244080c00001201c0d10000102c41440c001e10780188140c0e901d1a42c02c5021b44600d8100030340082d004600000c1c01500054010705844000f02203c0700803101c89000c99542c000c0c00005061658600003044c02220181d1008000c0d5081d06c09403100d042c0200520882017409200d4a0009040501d0385014400c0082e6100c00403281200580904001d41e100c180040c09092103200f0443c41c000351720002c45000741d004c9826440d4000c000c1c4282d18044000e181c0d08030080400314098804c1c88805129074402080c001600000d1300800c41c24010340c84020301c12900c1e80700001e0034855a4001c0170801403680c441500080501d50074001c0026841201c0798240458100c0c1c0d48110100c03171b801801155004180c1906440e01450001240185021203a03803c0202c0c0101205207 = true := by decide +kernel

theorem cover : BRFrame.Cov 824100719 824280575 := by
  have h0 := BRFrame.cov_init 824100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 824100719 ≤ n) (h2 : n < 824280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
