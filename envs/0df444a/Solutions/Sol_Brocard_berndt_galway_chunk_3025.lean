-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3025
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:26:50.307386+00:00
-- url     : https://prove2.me/submissions/8e3b0aab-91a6-49c6-8d20-5a43777d89dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 543884892 ≤ n < 544064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 543886142 1250 543884892 543884897
    0x501030b0109270c0b0d0f0b0d21050909010b03180106080a1103070906080d03060b03040c0b210a09110409050c19150f0e0306070e0f0402210403 64
    0x20000880c01518442c1c1031080b03040c1140090081803210380d501d0300700d001000940c2c00fa0005400081c184000d04000c104800c407802c0c000c03d071034a019000134115440c50401c90b008191009c88803000030480f4562070861120b9808600791144981822611405800406500281d00000116070556583c1c09184606000341c51449007060100800307081e185244605a402e0380048070f80400100401100f000800010b002c9a15a990310421282a20042d9021164030340012080440d00c1d98103000e40f01c0a400b0b980b410501d1403c169840d19410055840391622181d404203800c0c501c40c040140f0031a200d001c0e01e40400f480d040042c40d1000800780c1c00c03800c44120300d0031808610182064018040601e4004c2c004d890b00c002590700f407080000115000d0710128080300c40c04503101459803040007001c2001d541d040b241c2c550000c0c0286c402510254000d10a0b448032003005996940700d822150800d00541c1d070100503c03800320126019020300c00d0050901c0444520700c1c1c900c2e00c025813440340320f540240d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 543887392 1250 543886142 543886163
    0xc050c010c11040b040209100309020312040f051e031f2f0306031e0606040e0114010302011412040602210108030a18031401061502030a170a1d01050103 67
    0x6006490521203084010000b00d0548264803440ca03080e44460402c10f800740000d8034100d43c020004030101c2e580040e11002c282d40701f02040070750604102d003828146a0030b035132030b2034a410710410302c0a0081038840c06105209a41070041c141281c4c4444491001c0e0141c1102d6013080b01ca2189122214400b903507e0800b031800d681e41420001c1004804811000388000360426050703c1c0c0f0340c4a041e8130040400b030b014412144504004001e0302c084000ba544554017a10003410800304000544060307040c1d0004603030504803111a0300001040c0f15044030390908050001d50411031103104540921026018019011400c0105002d015001401d403d208041d5103155050540c5803a00509001c4c01014026402401b1100e0914090300130a241150219006140300d85ea0b5a1080ba0a0440a0081405075102d140c1040350541c00e103c009000c40140c0050350030032402400050021040c0588141203c02c40720100e82c10001c2c0c0d50282d0140b420890300d1701d4160f516020440e01030542840100c5604880 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 543888642 1250 543887392 543887413
    0x6100602011a0f06251505070503091f0f1e0606020102120a05090a02130c0207080f120304060605091e01050303040b1204020a0803130905010806040201020601180f0c0c05 75
    0x40a800480000000b09070444504010003131040e01e0300311640f5410403c1c00050601c0c4050441820b21180c944549030201174a220400400c040e5200500f9500a0020034000d012440502083c0440d41d0020820410118064010342e000585240c030140c1e4a600e2816901c100f00c2d0f003040e030400d1960260070900b032040d079694000890803449036000307900c3c0041400c0701141c0c0c2c0207100e8002d150400c03c240304440500b80343d074000409014148e0b100044aa81d1120105070050301030080c00003c101c0c81c2c1c0507203a6036410510f619191300c0006442c01041900200240030404545d00017006040042d01d10394040c03174100c2d41030b02c0c100a00c0216031a0b10f00c07202c00010743c40c81d0000c1190280c86500e01650309145849007042580c81c1c02410072680042c1c010390200740000100045d02489100840da165164a4081007500300c5a041e0409001a00301000700310260b40c0018800d0704441c5a83d804076000702420305040010142c401c4120708650800103080c0200364040c8505c0310040c045d00a58030342020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 543889892 1250 543888642 543888671
    0x2090112031b0c0b0a0203071b031505040203100b0d060507170f0106050403080a03020d0f050115020105060f06090a030503070b0403110a05071406120405030307020c0102030a0e1c050610060201 85
    0x108002e004140624503441441000e1040000c3c05034007040380104ea00b44807140da174119181007800c2e9402c00c440c107030040c10000d01001c201a0b03003481074840b000700301031300309600407075242c96844041124298031029141420b0b21041002e0071440e401041c00c00850a144400801c1c0c03a588a0101f141c400101020903840220100940d040303a16540343d45107013505c2c590703445089410402c581400d156080c003440b00b11111714081d0322550801040c00003981d41c10903151035626a000e6000c0d9085a2400e001c102e00703503c1c0e100504000400854407031f40c44100a0b4001480700400740c20003481c6020100b4a24100041000b8840c007482c801c2d1508404454000c40312643c1c0d015412014046a000c80c0e010005e00c0f130880070180d010791015016500e0500c1740040d113084c10750240c5048030168400000c000c16594180819186040c0910141d0310345051242c0c01031020040a6805118040c540011403071a07116005080c1403070b80c050151a954070380010346404a1003684500380142d400c2c0a109443c501 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 543891142 1250 543889892 543889937
    0xa0e10030b130b07180501080a0e011506030c0507081b0f0a080c01060509041109090f0d020309180103030c060b0402041505070b06090c04140f1507031209020a0612090209011203 78
    0x900c01c64a8170216485c3c4401190414005400c0104a5581e81d0071600b03410401c2c02a4102e202d56603070265001441c2030780040c11642c518445400f0010140309610005403950100c400e508004110ba68015000310703a01800d040899507400601c1c45401100010403546202a000d00c2c40c1700347c001c10806a4035002c1c4450001e0444000300211082043e052451070711000071600500e9040488008019049640d807804483e1139104016a001090500c00c038500f071011048091039035054500ca07075145075005032006010b400001c0600d42c84020b000360588031541994000c4c424454009440480340c030003e05580d2200d1016141c400880001a10351305007809424029582d80248501e40b0303191028440c5003481c01c2c0d4100303911181100d808422992001d405042c47c2c1980c00460360348201c2032602030482d0240248502c0704509260180c805030707079a160402c0c1150b48030704041300241d040d00c40c580d004140041c4001e6200d0013003070000c42c5940510301041c508034442c0d180e0300d94003052501d43d0070703030031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 543892392 1250 543891142 543891167
    0x1030314030408030705030901091b0e1014060c0a050a20030c01080703090204060312200c0d061116050309041112041b1208270a0e10030b130b07 64
    0x22941000440e405c03620500041d50712200c840000911491250f680c50242400030b544040003440703a05d17046c44190744200e00280c0041d0000c040100081c40e100088140307001d01d4000c94030805000c80c180c0102c81c0248051038516501100b40d80420266181522203189401181c01100340307481c2048603682400125200220750503101d2401554651400314060980c0e03030702c22a04a501e8440000004000d0b4008046402264036000f803040310400c0c8003005a00d0802004400740e007c040c60741d4090310791308840040f440c2c0200c4d01007540e00b02403c48004071b118000c03692881169005a07007041c80404406400c560303508a405100c0140b0007001c2c901c00d4018940280070350341c4141b0200300061058001c11145e03100f8040c10080c8250740b10a0520021b001d8041a41ea95034001013200d42d0f120040d02d501c003400401c40f40994180c1c40345003c14032030300f4180211800ca00c280004522040c0d00c0904040c020350f48039480b0040c51600100d03400104070521000c6030074110705404a13407500e00803c0c0c08c4512 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 543893642 1250 543892392 543892403
    0x6090307151e0e10181b0b040303050d14102103050d0b010903080309071d040b0f0702070902040602240103050d0806040912020a0c090204061202090a1d010303140304 73
    0x1c940c4001c004000414001c040c5205074450007080e026001311030301a000c588100c200104144e80d1107030416115206c070544081d02d2010080106101c00392840341a00d003529007602d44161612849441c8400803c80300c5003110240f44e0540c104031100341c42807040c00c280c4e12045000c20100440240301080c0049241e0b004000c6202400420200d140907803012a0012051611103003259494940d130300702da8000d890000c50340d0460f000900c556502c03014060f030741030680c4000d84903914043e1100c0303200b040041c110000008103403002c00c81540c0f080008402a00840d0300855481d951200c010f0f5980c1d6400d400c4440e80c0c0c1d55551404100d212608919040f00d410102a1455560600301218200c8000b0b00e82ea83c403503920b0b0040004182e4514500b012401c542e002444144000d00b00b0401e2401117600141600d401000309000042c1d100608803c4c40c107000e00c000d03845000c076500148109440760094100ca14043c1c1942c20030007004521a4103e1f8020380350f0383c02c0c25003a4030b0980d03501e21048401416 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 543894892 1250 543893642 543893681
    0x6030c0b27133204060c0c0314070201030b0303040f080606060304050d1101060f0923090c040c0c1704050a0b04060e010804030c0f050601080f01051302010c030207080609030715 78
    0x91022038000d80842d03408400a211040c2c50040400c0280c954007086422010a40c0f040004200440c0f140003194816070034007505620309980d00034607000900910b0202c1e2074004c600c2c54210b9009070818520208002d0a481d141c0b0348400d184001c404807446003013080c2c0f01c1d5402158442c00c01c002101c1c01590808060903084091480603100d000542d203070718145650340d80300054840c881d940900050182c00c28003080c0b10104150300c40e1641440e0411a649000342e00070710243c04c0000440c280614815580171641a01643d0299840400c0b48405802c05110340c021550307580c15400180155007048881c03002c00f03612200000701038003990050001091510700c5101156004e0814564042c0c1f2a281c540c8084589982d42c026844000c40c044038268003002c0140040ca00038024590f032500400d00070446803400309020304c1c9402c000e0078081e040c01044e02405062610038410344010301640c07011501c44e402c00c4544655640c6c0218000d80b030004904100381c1d1841c442e03000c0d2000d01c2c20318040484 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 543896142 1250 543894892 543894919
    0xb060406120f06020a090801020a0201021c020306130e190c080601150507030503180f010f050606070b0a0e030f0a0f0f03022803020c0a0f0204140603060a090606030c0b27 75
    0x20f00940c0049030b4101403048501000410b031b402400100908461a400135031504440b0321000c8681104892a80c1443d005004200d096210366a95503507441c1c1154020445a0702d82c0d8200342805840c1d29042c03419503039007042c10b040c8902c540300340c4211f540510444000d60303650310310641c6840c01d005294000a0b800c20004c400b0034410000366130000d130b134030503500c1180300d1040c0d4042c9040c1c1003003c0c034117969469201c04010380901d84201a48000c2c00d44009190203100d5680e280050401000144802e50720314580104540c10400c0e218201c072082c0304907588040c1000c2c0070301134109600f0440005500c49544095651280c020f44041c00c13024031a101d8585900602c010003104942080c000f055404c1c00311300c0060741c0401840d241c10340141c1601e1804840e500500082d5059141d4640e0303405100300074402141c0b40003e005a00c09040380000030510020318280c409402030350303c0a0203d814010340400c000d00700c0c00c010002010000500e00f0151201d20640d000c0403480044290f1200c4541a00c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 543897392 1250 543896142 543896153
    0x10507140919030609060e010510030212010603080301170f1204052419021c08040b070314150f0406150c022101050603070605090306010b090d0f0b060406120f 70
    0x40004200081020010100c84680d090041489070720a8500305d454a2115040c412540310b0540000781e1107000307000314134141d9002c20359000c2c1448001d000b40c203000030701c400740002940614090342d0b01032044c0c0d680396921241061400c940030b0861010780903804500195070300000301b01c001c0200001c3d0050806103840c0070010805502c00f0300a0102601c0d800d6816031001c4e0b10000c000040900040c8802050800341c003d1038588600d21a045080e004442c00c0321840c1c008014039809a4030145101a9035a41041100506003c4291a040150600500146848500740b0034001e1109407220007840091008100075600c4031300c240d022001010724400e41c4144900110000304e8009011046001075041c0140200c202e1041c5050700399545a05100d49440c042c024030000700f4861074010700300621180085d48440044c882c0010211001a001c1c03526240d0f580790011080d0810305280e85800e09081c021180c1c8001c0794a54800c0d89031003c0490051034072603400e071362544c120800001030304240c0d551 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 543898642 1250 543897392 543897397
    0x7020a0902072d050d02011a03060c0f28031406040203060f1002010e030d14070c050327060c0c0f0613030f050a0506010b0a0216060807030c180b04030c0801050714 72
    0x1000e80800400c103c4000c43d20401140c8000f003203507800001c040c4500032580c1170300580385100c1446074201200303109203080c14200b640d5000e1030085040780d41d15402e1500051051030b080d8100c00902c000401545042e0709544655203190404220000c29074401003000200e1000f200c001d5488403c0e0b180c11200c0e800d244071ba42030404494000041d081400c080d0b80b078a036400640c285601151220313518560341c450003030f40036084461810a04004241a0307100b0f502e82c0100115080700b080f2421040e21114a60117964541481c003070a01a40d079440816029228083c62212a010340000c2604182c1418401e0444864161004d501c0801030b05680c1c82080c1100c812405540b00e1040801080101d401803111034003c110120160346c0e80c10400c0b0000e81400d01003003900410301c0c5180001c11030250807480c0e041d4007020501e000a40c0d041004004e031038120140344100541d040c01c804c04140b00d0004001002528021051280305680d0b03007001e03600303031107044a102000400f4401c51001c00c40c0c00380007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 543899892 1250 543898642 543898703
    0x60801061e0207051809010b0402030f04060c0e0901060f0e0a05030c06071b060c1103060402090c0a0324030c080f0316060b06030f070e0307030209071d12010207020a090207 76
    0x58814140e0ba82d80080c540224681100091240105c24420260f20900c6001c908480a131029811890484820100d00c01e005001400307241c2c0341c1d00203040741845000703517121200300104000f005503100d00e0000d01018240d04074a010a4420318000081d00d03141b1180400c032100103005000075000c10381031040d03c0e00200ac1c100c440c4c00007910485e034071941050709040a81102e60f260005444c0608000c24507441803000c050007030b0071160030f0002580312036074586d901114a0200d203548440d5501304400820b2419015580c1d0b19070300188a2000701c41c0420712085900507100c04440300e072100461a00c9064150030548640d004006034440c3c40d26041c00f9844250158200107494083c4c60b003c1000c90b8401c071001800c4a40400c08c201c0003e070000301c2084104ea007500240f40341429903010403950035001e86038406110031078545800e14207030040d020120a00181160b461800e0409045002c1d4101d6a03081f80325421070000417483c144240f09441000360008207038502c913190402429802244040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 543901142 1250 543899892 543899897
    0xb0d0c0201062301081315051509010e011d1e0c0f161415040204180515250c0201050702040905031b01060f12060b010201060312090807060801061e 65
    0x210300140441400300c143c48151a110559528040e900380010015000284010a440707030100c01c0001089004000d0f070030344440801d00156030380310100b0042c0c20104c120034041d0702032141e800100e1144a10303802141242ca103082540820a100fa0f005030484108980e45800300c070050681c0c440c24902c00e6400e60300000240075040c9000d007002034120481c0c0c418488036401a035412180402c00c55448480d030881040c030405080b040198580049038044068400303407240303403106207071034140032808011a0015804021207601c00741a01414040342d0044600c6401403542900ea60842c1a2a511070b046d5424640d40b08080e602da154010b4840c0d4100403020398001c0d80d64104100010010001001040307440c09149101005d804a41829644240c0222414088a010400441161202184a1603445240480c2da0704030a00101e00405150b800507102d081452420a15036070807065400940e00d4010035180441d44400003a0b655040a00c80e002c0060301d0001e0a004107212301c0320140f601c80351031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 543902392 1250 543901142 543901151
    0x30102120f150d050c010206010b0705100902040f0915050702010213150c0c14040609110d051503011e0605040903050910230d0b090114090a14040c050301150b0d0c0201 74
    0x50000c00c502503c150002c90b180d903c2810503001039a010041d2600500700a0b104628051107903032120386402c1a0710b050407400da150310042045550310340000c1c070000007640040054500c40d081c151140301c014030613000c41902c5c050200340064418000c448100c4038401c85074200c686031460b0105100c0740340e41c4820800c031401031500005010b030a200001000290b04210b6020860801c0100301c81369035201c0a0341900d407035240301c00c060f012016940004a0090001031960760351148148048284501e107a040d4a08480b012100007420014101c8900c1810100201612103041c0408c5031204400540460303420302c54014249003407005502c1008481c5005001400c509041c40c5240c0d4440030481d046410100e1031003242e00301446040b50607031080b03d1444040d458404038900840b0b54084660149101000041510200317070800c10141880c81e01e00b46003031401e403c0c00c921604c4d190203158171a5080070f1194041440e007107070400076501410360803450001c02c000040020200d8059020665495 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 543903642 1250 543902392 543902431
    0xf0a1208130303110f210d060f0e0403080a0e03040e1906030b1927052103040c090b01020d030c0e03060109022d1806040302060c0a11030102120f 64
    0x848903040194404d844800110400084450404000c80c015071003036401140c82002d040c84420507085034064240c001551030080350252000b600168100e4030b44691402d41c0042c03030f0030f0035101841c0310718082d60300d82c0101c0e102c100c10841030301d00c00400c2180c240e0041c0820300820401140081c0c01a6103841d905012070031182c00070054a5465106a9014440c44100002c83c0740e0b04401b9000380102880030041c080607401c04110350075101c00c02c9a032032840300c3c9070441082000c0111a901c1138840c048002010f403c1440c0b040680c0c4200d4048074004045c0c51f0000f4145102d008540c81840140c001e082c0c0c2c03803030045013100108003150b0481c1c20448042c051281a8900740070203400380c282c00342c000d41e40e4045000d00388062401c8284001c150341c4100040000c0460910940740281700307010185910714000da00007900c9002e5034001a41c40900000c600c0401c21001980100e02440380c1075110051803010201403c07402800c03141c1c200340e005c102c0069100d085001c0c0c55503008015410701d0445889 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 543904892 1250 543903642 543903667
    0x105130312020d0e0a050f1603020a030f081c1b030e0d0c0203210c060f10030b041703071d2d2e020705031f0203060d0203030d020909060f0a1208 64
    0x1c103640c262007d030400264007803c0282841400e030694840017910079068556408a41d540078103100281c007200740048450b04011080c01211504c0d80c10319290380e20328a03826124030007017600300203150802403c00e001d16465800303400380754850800d40018200700e001d401015100300010070b004036810b005d040c07100d082c80010a1608882d2021100d4100d80707444055181c18039004020b001c020b81c00500c8410410051901d0000900381c81d4883c602e5051500c0c0c0e440c010b1150301c2c500181f07510202006c03081110803903105041030307008103070000560070084100090144401d5420720b10501c3c20394140e03e400d4600e10344500c803101010041c004414450303861204001c3c050100045540d88580300305810340459040144c0f01c0504003c13405003098082c40980480c1140603c1c9000d85020b4010000903442d9559000c4030100b40d4024007035035a2000120b884800a61001c40e1591203500c1d010040340f07990a240c016030080d800003504810039181003d151443e01a10f5400480d0030300010040c0e18129030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 543906142 1250 543904892 543904903
    0x1140f04020408070905250f0207030b0c070501141b0705030c0304140306010603060501020307061a1305180604050705010c02060d060e061e0d030f141b0105130312020d0e 75
    0x80050f001d44080d9080c42010380594002416603104c4040d410101c00c819038072204000e05140740740c2411407842c00c0d03001040e41002d1540d480034000380300300ba042200301020200102422403241c0020000c0135002401c00d202000161030000660b0321680300071400741540703002400b0700c6009001300ca09041425060500c1c540c8660088010602e600b1407400641c10200111409440f45081c180000ca042c480000d42d40d02481720081e1a1a450302500301e45060405000c600054010f00044450882800c042020b048151242d90000784c2842004c5036546004c50380600071540310010340b03045407a21004503000302c00104247d80c030000400c0005002c2007036120740401000c103441140e110f460008100032a00307850a82c4006a100300b4100d44600355a81d212030644d240d031600b1f0804a0103000e0208841d600100951a04044000240300c140d21201c01c24040350000c032000280001d54604e0390720201c88040600c010081001c131060b0005001e07403600501545400d00c00001082820140310781d00c1c05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 543907392 1250 543906142 543906149
    0x2406041e0906051203030403080c1204030f110c0604150924030612030509090a02090d0303020306030d022e09060c08060a0605030c070605061804200d0b01140f040204 73
    0x40c1034035201008108501d0045a0007082c0407a10410694400b00d8816128400280010300b04140301780080c010300c4044003900c906002c082145c0ca110b2030146801351906400c02040804540803c280007801040013440e00c000c0d41d0054001030a280c605181410030701100e81e0b2304820700a0503000810006080fa00c038030300b103a1340c000018607580d60b0305e8000380481d191a040700c4135200d40c0030f000c2400303e030304402200c17085841a6034602440d510360074000002e00810318420307030181c0c1c0411114203050b4142c02543c0160800ca00351440011a0350090340c4e123207400c001030300c080180c40c030f090704500440d075801d40c112015010f40412000a642d56007801c440b99013010031b0103d08060305000840c2000c260f124082c00450400a00c1d50411040c3d601c1c0601032139000811a0392214000b41250f2252050700c9120441002d00e60058281458030005170035604142c000120f07c8103c0c5074041d464030408858030282c010071100000d03420b00c54942c3d90070040c10314058201302007003140c882688482c40240000e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 543908642 1250 543907392 543907439
    0x10090c050703181401050a0c06020307111009020108130302010608070f080c120c190f080c010807080f01090504020315040b010611070b0406051c0608010504031106240604 75
    0x80703031940d1401a00300e040c2c0ca0360300d041d400d020b00d03400c2c441c1480e99882c0c00803162003424202d07250600c500048074280800c5e6001001c95002000f0303c040140c01001d0841c11600c00000e84811020404804044905a01c40070313000940180101b44038a61070350301d9290a60080c03002081154030740c2c48181c03601d0115031094091030301c0c200c030420440c4005d202c02a0520400ca030f240b821501c01c04030130750b940c49907010024401c10845001480f86410101500b00800c107186880401944d13030000c180c0c03266041c00c9901d010074200d40c0012071140c4241c09880c80707000840303800541070b42409a8a001003100070408c981510941d1959542c600d10906210720071841484e20000359810480010f0029000f03050002079039109071300a21070b520b10b00c13054505a44a07032803c0d51b20342d180040c0919224258000c180d806503c4c0880100d0301c0345040d0016032299010740c984002c1f1480079941159a1a070484e80f41c500c21100108100500032910450707658024010291420f003134503002e40110f00d80010084a01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 543909892 1250 543908642 543908647
    0x8030402090601020a02030601092f04030309081212060d08071b050a300f080717030c12090102091e090a110409020904180303050a05060a0b070b10090c05 68
    0x85241ca030340560b5002d0401e1002d003c0288035940801e58804060040c0d046550326540e020030000c0341349107a0fa04443c00c215036032001c52854840500300c1c2d4010700090300060b03440000440c0600300001c0c0001107000b2148658500380c0b070100160540342d0301401640d841100380400d00013069440014110041c000c41c0e50201020748401102c613848410f6000038042c102000341040755810001455010f80008103040000b04409010207030480c0c480d040050016906440f004288140e201c003500c1c0d80c41c410646003070a1004801d261000e8042215000446d00c0704001400201045d8418030780c01140120016062100074000079000807000342c1060118000c90b03489030660f00c4c0c0318082c50b4020001d0182002000300070310210800388298002e0302030041c0c0028161115845a41c44140d1600600c0c0c0300004c2e5031000c0c90010050442a20450503050900011821034509022081c3c11101000307219841c0c40c0181d5640c020200006000b40c5180c0e01110740002c01002a0107204a8034029544155 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 543911142 1250 543909892 543909901
    0xc03180b090d030606050913060308130819110112060e15090f0402060a08040c090c0314150303030a0f0b04020a090302100c0b01060804080705012f07050607180e040803 74
    0x24540030b030b908510002c01d0b003412800c011480d080421a241010f0540380000c41c603030304000210140002d54401004400001541d240340d50090000700255241030382030707c0300714840c8541107040e000c0c511005800c0b02000c0312950015801ba000403401e64481c00f2001c110640d403600c01c10054a412501c03900d003510002600c600c1032812038202ca9204000b4000034801c1e0801e500443c101e40130300d0381e01c80b0a124803030007c03074288201100c4031002031000c1170050003c0303001200010b01078987c00d524010035129042c08654210041c034005121014090000d50441e40c403400048050814010841c885590750070903401d140c3c0300c50004200b04121522000c0700f861451040c007995143c0ca50860042100c4035035403e0024204141e07190454600c0d1420100c079840e00d00b080c030303428810400d0084c82503203010000c401c04018800006a80001202c03038554241300c151041005110b0a1001001c64111000140301d007070244003290040f000b07049024501907200c203140c1e482d0345001d5505079144d020100820 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 543912392 1250 543911142 543911161
    0x120c170c0c010b060f070210050c06090c0a0803121b09041104060e061207030203430309030203030c0309160906051306080604113001060b0a09090c03180b 68
    0xa04505002c3d13801c01d10700307100102c0303014190160040007442000c40e48003056800c1d00c14005d0b1540501d00307800380c03120b505101903080d03a07954481c04114010510b0f5a40003d2540c40442698000c82004082d065155500b440200c100750110343c00420200040c00310a82c207407141c0c13145050341d034202c407a01c0340d4031400c02d034000e01104040d400041c460a800c008022541c5070200d1856000000e904005d1707181c2e01e5140e40010f141190b8010010703904115184103003d200000da022541485050107440e60548d045001c8013540d400001c06005a4410008150858002c6004603884031030b51055a20820903451302d100b22240d0741c1d1020354482d898075000d000d980f41145214404091030030007085054500380c9241c0c0c6408004001501c07441c417074182c813079068442c2100d41468101d103000412565000071020100d402901080620740d40ca0a90003040403281d001c01c0b251040740782e40301c402e40300c0d1400030180060040d041c054002c240d00c488400791054130310014000710522800142c000e518020b20791 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 543913642 1250 543912392 543912401
    0x5100b0a110c1f0503100302040e010203070e10050912030417060f0105010912060c09051c0501050c07020904081b0d03230c040618080a11030706020d120c170c0c01 72
    0x3098499a0600254018641c60412072640c903d01e41c1403041e200c1e0b4841c20a045444103950004e500309042c4240501040d0707040d80154810302c6180c60300240e881c032002c10702140c40912040c400118101308102e503228134044070611a207a00341d0080728034051b11452100400000d80d8444203c40d070080701489100c0314144117541c00341c4020311317000800c1450403041c0c510300071601c2805409a6607890713901519a00c03403142c40001e00300c09043ca00c030b00355a40d903402044c5140c804040e140340d407038000401c42001c641c1003140c20f0a500280b500c1034035201c42d107a003203141c1d004455000039000005100680e4680901c441da40d80c507036540340040c3c0c800d2003591028010440200034081c6900785020001c101e0b041000b0388013500e07a98903001c400b2004406054003122410b4024186a119500500c01040506900d00348200d17011390984080a550301010b980d5540010403c80105840101820f0304090350342c80500c5400d140d1401d01450b8071801c0c8042c90b10401610000603202000561040b00d40d400d018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 543914892 1250 543913642 543913663
    0x12010b0a0b071502030a0e070806060117100504243012050f070c090b0406150c03080601120e10060b0406080613020c071806060306050303090405100b0a11 68
    0x18450301e40010355072038605403c054911401500c3e070100114012400c10f030f1100f4207840c403500803108441e0b1500c032007950750343c0c0486245001a030b0303040d078004100703a03e06041802240506501d580781401c0000300001380c0a00d0200c40500ea844c030011640e008011000440208401541c011a180c2d140c0e80318005143c1c0303070303040710101403c1c1010000028407503005010030804525000340c8601007501d2030040d40c03003460400341c500303150800d01040015107503114115160741290104500c60f5240b541d40e054080d42c98110020510301980100401d02903d02d680d4407940514007040b140841c1480c1000311200d02c8040300807507110782441c500d06200d920504018010241c54103050501d0020300420903c40102014014403801d021100800f0b25a01941c1040d9056000d07240e02c56190420b2a03200308002c00340214181c100840080d201c2d0292081e40103072007019000d1845e080a4100703001c080c200161021310081008200001d490b01894007801e00c0b0815680c641c5543d040250360185020b95010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 543916142 1250 543914892 543914909
    0xe0402010219150c120906020c0106080a12080c13090507030507111b0d05030408160e070509210f010e0c0405130b040c080a0c091401060e15070212010b0a 68
    0xca0300004580401000485803c3c403400c08100000d0144007120880d00d08800016004c1c2407050340020019160040c200300003400008100d215981c1800680d03da8080c2c5015081311031005a40461512075010103074000340c4001045e141c103030800d0990300388032450b6000d11101591442400619035060042540240440c90f0545c0b104943c1c3c2d290720b031070f03481010702204e10b26a54032640302aa152a0a1161040d820005a0b80c54039902d09980781c031500302d00d41112040034210343c0883c03070003440c0f0310541c040e941942d1030604008204082c003030499031648000c00c5000e10a0159001a1410031007000140300860010604840400007140340210400322144140d05042c00c0240d1122207075101e4480f20703085408040113440342c0c1010072000c25983c0200d0000e00945034401d0074407003944030110840c0c0d508182000300311042041403201071000e001d1303140081c51070345000c42c080c50701e80b121006400b118800e15140c01599070016108624000074482544d450708809003041c03810740b8081000b49440f8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 543917392 1250 543916142 543916183
    0x80c011508190614070915020a0510020f0706050a0c030e061302010c08070c12170c06070f031127011b06020d0902101e031116020301090c0e04020102 66
    0xd0011a10ba09650303002800c0c40c08100c004009100c2142c0103d121140c0c096002c6400e81484034008044413254001c84898148400c5002c81c00d82c070002d03d0b92029600240900040f2203842c810380060b601017820102041d90520200d000f01740c252141c2401021031100000d400034100300c018080c2c688001588265400c120200103509159041403c41145d0900e002c11001059250105203030062400c0582a0102078102084c003c50028504202c2402a00c0909026160381c601c170030b091155000c20031185e0000030204072400c1c000c100b0406ca111907800c0c04990900c00c080ca4501581000380c403880035100020031004907612178110100b00450038030340746551104d901d0121018246031175004001e2503000a4480305845540d01940485600800541480d60083d900078400c0300c1f100c10900e00002d0b00c0b248410424002e20403000c441002407005410064060103041c01400032070020f90700341d5241c44040000445840454018221480c000c94081c180760000a01c0d00c124145000c126100c0d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 543918642 1250 543917392 543917399
    0x20d05090105070209130c060804170a201c0201020910020109080304200a08010213051009063e010c0e0a14030715020c010e0a0b07150216080c0115 65
    0x441c08a030000798045da0302c0b140325110900104000d6401a074040e140f40d40018010500390b83c400c1c0c4241c080e902070109040008042500d1094034842c0d00f680801103882c100204038105000c0022503031704602001074482e6a01189032a100d00c0c45200c21050060b5400280000c00d40307490b0030103a8044a091008101d0b14201e655030b80035612005e4805407840c00801c000e0102c0b030071b0a03005a0103480300601956a01581c0d510002d0107504040110159000a08004103040c20403001080394400c40d5981e000c21207240c041c0030307150710746a01201013480d11560300040143c02134149420360080b07801100c80f45110554810741c01c5805600d4441c081018031128100b103503640c4030020040e00e40180f0490524518280081e2800140c0ea00c03030112140c0005840f84810b4010a110f2000407003a2946c1003401d581204118142e00d081c0650f501d489802c0c4082c10201d105050380d8964882d8406006240c0f40401151200c064058841180c001200007051540e01d1800c1c090701141140f21404074050504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 543919892 1250 543918642 543918647
    0x15060801080d270b070609060e0a020603160c0c150206010b1303031d0a030602090a08150a0207230109201e0a12060603030905060f1204020a0513050601020d050901 72
    0x110041c070100e10310719049070808403c4142402c40000c0ca01c0445603583c503c0903181c20b0024017010f00003a64824a02258000100c20104444c8440c950050680340b40d135480c1c0c0d4010400c0c1d80002c00000c1000913042084000880b45800c590160005a40804103aa0b0802c0300a28282058210713150050062103e29540030300807000105a07549414120b241d80039107044c010303100d181c0ba0102a881400a500041400207a80c000d015061040ea600c0c620303581c0b603c0846564501460420400e00b40301000500040071660182c14000c0c0f16401c000c4400681c51035050360032000480368456a5580d5003c00304000d007940540c0d224030031014191007521241342c00216840804201000719000204050001e41e4480d802d00002c0d11041140789044070351230410600401030390000b20041070501d00c0c0410b181c9070040542e450280d0251071140740034601d2001001c0354034041d00172a00013880c2c05010880740c0e540c3d01701e5041303402007036000a620300d0001c0c00285840b8a605080c030600000700704400c060790b03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 543921142 1250 543919892 543919907
    0x10207081507031e0b040c0201060f0b0708040503060c130f0324110f090a061403220206032d090a1e0f0b040303050105011701052215060801080d 64
    0x4550140711030711661002c1054000d0030a5050035403802c8220b0600000d80c440c1e5a0000400000c203075010880e0740b0281070180c1c2201c3c15030007050001c507a510002c000c18101d01004010140c4a2020b00303003419981c00c003280c038000d010344644920749000f241d1505001d011610110040441f41c05038985d5500d1601e6212540c00840d105800e00c100740c58443c0c01c8040f50340c004400310701d4020072450340c82000304182d80003034100080c614032540350300c040040c074a440b90200c0207001441c20385c8a46540c0300c40039000040c103904424101e0403807101141d140540e0f1104003652043d1109504403c01503100c01c10210b03c0400d01d1440085050b412081c00910503001552a000c82d0b40000c102921841d1034040e070b205001c04a0b0003e1404030310548640070402130718400c80c0614400c0e20b041c4401d03600d81c0019518030b07402a1098100c041104010400c500d0641040e9200461402c00c8040140ca80e80400007950021302c00502800d40e21542000001e42c46171540b0b0040021001070040a240c10340c000f030102 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 543922392 1250 543921142 543921163
    0x1202040b0a1128050f391905101d1c0507030309080d0c020607080d020d0e0343020105041706011a13030803150409050309040b01020708 60
    0x1c00440032010070308500b0011100d0742403c0c080c03001e01e158072450b80740e001515143c404071010f005080811035003840020f01c14120101da444d2a102c8001e42044a4005001a02100f001c41c4804400031100703444010840c24184074040c13101548a003071009200e040700421210b80c0822843c4c00201114020b05011903010700401c0340c81d00703084020300030648114040b100b0058000d002d908000410590000020390031900341e61305039507038801c3e841000e81d0001048180a5048041040901c0010b0030104c0107194941c00f1150041c180305614145c281100c6003e0041d0481380d100142c481644a030311042580b00801268407800d00c01d2119809003207540a021414680d203091404803402c41e0300540a40b000b60411040410360300d0781c440482540d4000a1040c04890b100c08a071603448007034242c08840000004500d0450640d185a0300c012070b80d0710040c1188504003c04070f14104c20381e200d00503032101e980218001e6440b0010403082000b03c42403521001d065501c81541002640f0f03000c118843d84 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 543923642 1250 543922392 543922397
    0x504141b0f0f0c100509060f0703200307110714010e13141312110d120b04090b040b1005090f041a01091a06040b0d020304080f040e071202040b0a 64
    0x792140d40300d4280250040350418240031102103a601e0490400280c10000e490f0f90b000c0c02d0050b600d411680c03d440d1002a96201d540ca1002c5000421042c00380d00101d4507900001c0383d11b51b00c10080042404142c0064540302e00003075110307140314400142008500090855044205030354280d490001e4418440c0d4400136019040804e09941c0c1e01039241e1104000507480c240360071042c40c0828070086998051001128902044504003a41d14400c18800181d111190700502c11340b01003070401d031503c404400f0440801c0d078032003010480d03684481c003030120325501c03030070140c4042d00b40b80c41c0c100c0515000500005000d20040f004000558aa88101342c010080445c2e04800c0c1c1c650f802c040c0310340859018050b0f400c0c079040c3e00002e16148994003100240b160050381d03c0c0c00890b0801008001d05c5035200d40280f81348148800f601d00381144d07000b1038006102d09000340c0340070b031980440300081c2c20a9016402d01c0340d422080056684d0048060072400041c0d180031413406d030400895201602440119004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 543924892 1250 543923642 543923647
    0xd11151603051014011d060f0309121204080d061a1b03030907170703020910050906090420060c010501082512080904021c020d0b0a0e070f0210150504141b 68
    0x82025031340c030491a51ba000a0a032690300c0c2c00d440d5400543c0d61054440843d5449803a000b03000500101042d541030071050011040180c8503615080d5a0f80c10040c0801405584c03040000359100d01882940d10740041641c1c11030700c5060310081140d200300308008103034140d0020000c0182c010400b003510000e03170b40106540c01022030701c1d40c001c5103030144980000790880030702d406008048003c4040d080c1110401c461000e210340d101014426041c0742a18001e0507a41c80f140803c1d040d0458010000300140040c20580c1418200b051007802e40d8002c0c0e021040d50b81182d0740304d0030030407000079030204954805000d8081c107a00c1e00c0e5610b40314524150300a807580c032004c98800c9440c7d41d81c2d0100d0b10030032442000c5644640032a15034030020361000017910b4a1910b0001c107031070355040008250382201c85514aa04555464100903500d43c10640c0e0220110b008624612241c84014415000d00001e10f02c960300d10281003609100494283c001030120070000001004610032502d00c008801800c1c03840820f4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 543926142 1250 543924892 543924917
    0xb040311120415031503140a0b0406020405030c060708070803060a091401150c05060a0b011e0305040201020c011d12010b060d0906140601020d1115160305101401 71
    0xd032059244a09280ca40c0507004000c0000d80307200000e001660303400080c20702e40640911082d0b046850700080a80c5001081000f007000ca4080508820b2080e81d40b801d540c12040c0558507103100c0c00044070115000f40d4003203028803403421b0030400108900e4080e10041e2501e5003680307a4118038010800000c04007030001001400d2900c0d144843d01c0203000c01901031082c0b01004400d141c0458003402070070070340344a203081c09000e58070543c100300306950000041d01c0642c0b01d05024001400b41d5480301d078148007851074510300c01c4a000d9016424080150780c0041c190030180700082c2001c0171603034041e0401c8111300010202c03080000c240d0720292002c4405840410010a026015041440c4000c1d8400130106542180a0807500424590341c8240402c0007000b600d980d00c814040010717601140103134454503070214814043c0700c50768113040ea402c0484003049070343e440c2d62840c4041110644403c5031300200484a080c2c06000d61908262000803d00c1c501d030070100c080e02e40c2002880054104504a842e1b607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 543927392 1250 543926142 543926147
    0x322021507030c1127060607021f030501240e0d080301150206130503090114070c120501052a130e090601031e0203070512010e0f0d1d0604030b0403 65
    0x2010300950445099218442801d016204a08070a01520b16a58411101d281c038601003542007a11909201c841c0890141c9881d003a1315894000c210360f4000b402001150056660450503c00242c454800704045108240c001816070703a06a0003c060b40322001072441c1c002e50440c144011b02c4c1440c1c9071210500c1407000c00a10340810818025000c210000000301c1c0d50701504000004100311a02100d0303154886c610f000c2030501805102410313a070024407400445600c00c940900e9100240414039091074019100e5200d80c00b07880e40440c820004c0c452602d000c008080c007480c4d6001603c1e0320194482c080050b01586000082444640b0a10001641c01d410080745550000a0819032191000758603001021583d21542070109660701540000004c0c01030f6940c82c83c1240d4960b01502803c6110b1501043c0300d44002800300c480001c0d52a5284400e85a400b040303001041003210006090b800300980c4054404d844000010301c00641c090801202a00c81c401110112584071403000b1190340e490404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 543928642 1250 543927392 543927409
    0x150c0702060c011812140c0304060e1f02010c030b0d020306010326270d080f0310090c08010e16020a0b041b0f05040c0503090615030f12041a032202 65
    0x213140b8505500100c001402840c00d20f61049400b20f0315600c103806a91035403807a4500920005403101c0e441000140012446031264070840340d4007034a0036099080000c034801205c0a44101e240050799103400402c1055410701860f026030130191005182601300e50003003901d604050001070044c5032451109aa0701c1814002e4040e07146030b00034035035100c034017002c609404030100c550001c9004600c1070004005150205842010075480345c039030b52500450340302400e42c9400040c008a501d4052800015004c1520b01584072a011540d4a44607075604100e02c40c1c8040c900601090720784200c82c2c04000a068000032109285074114854400d00d80d540e21384400d002c507078035a032501c801c0d640110010f24518231245400688104940500c0444881001103d69020849011150f980004049883c1020344803c01c0c1c0c90003406030507151400e00702c0c2c40461a0030018811078078035202c006010008040e43c0c010207240e042c8c1000405182d420040202c18000490449480583e050140800300f1940c80d12803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 543929892 1250 543928642 543928661
    0xe06180702031e03180c091302011808030c01151a1818010e13030c0b10172b020d1b0c06030507020c040b0907120605040e010e150c0702060c01 63
    0x3e20004008040301d454540d00107544400aa240c40c2240b600000008101c1d822103c0000d80f044005a48102c0b188450080c205030a906000544c800203150600103a0780001410541b001103507140e145603007031802c45007840b4440c40c110356101e41c2480794a40414018600540c4600560344803d5090001011001c51003e06d55000a5002c49407641c6481250300504940c400044035415540e4080102485202000010b000401e483d50000000340b894000360303000411051f0f405191501c55005000f01c4141c0348044856902162424144602035440610328000c02a00e420b6402031010010b582e6825580241d022721801090351458414001c19620b4240e800003503003000c0d1a40c861001d0000d00040e520b0328014007883d4100ca01904146c050f01d11940c1018040070340710f5492200860b6050b60287c4003034141e80d11807000049590301c50090780751400305c050001590035064030a0038039118214000c0481c0d410518104610b800500c01580c16140c2c045e1900d0396100381810a040c010301c2c03241d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 543931142 1250 543929892 543929917
    0x503010204061107140303040303111905071809110103240b0a080c0316030e0a020a0f0f0e07020303061509061803010509011802040b040e1014010e0618070203 70
    0x80c00180b07160f4898036a010802840e4181c4001580725440418041e030104541505540100401c100081c490070181d11010001c009403450750380600c190700c0c103120143c401130703c1b81c1d840041d00f40021200c3d01c2007521122040c0808100c942c04c141d603800c0401070714002440c181980c1c1c80d14982e007509810404082c3e6000c42c44412a501d40f10050100140c01003004600007030814400200114210f00440307010b90480c0c800d201040540c40380131005484009010402405403084450050316034005510140481c4961240f034242400314074807040500d40c0c01700000031502014030070626008821660061400e0b56400406444841c40b051280b0a141410350041d400140704480440720f40100c1c900070108400070300440c0c5407099110700384d9a42499680c0c1d10034190400b50018030b0142e008000c03101028001003003903408207020f0741c1012003181c0e02003412903c90011140c501c0d143c40d00d141c050318412102c29040d080c55000301c0e05d80c0410411f2601d00c1d1400f50041100380e4000c00a43d2000b07481c84 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 543932392 1250 543931142 543931147
    0x150c14070302060c062401120504020a0801060303021509060618101a0c15060f0f0d120f0225120c08120408060901050609065b121505030102 62
    0x1404e45544c45100300c80e2499160401c01d40020100c0340000d80603441e00050391924487c242c188640c40040201a02c01c9074007450409000682c0b1a0078000c2200a50007500034005052030110346e1042c900c0300411004481e00310b0000c0000341c3c1e440785100c02e19030150081300002a51200d40c1000303008603d4100050811005109004c1e1803101001084071045050542e0061040c082c1004e101c000c05032903040d031009100202c1314140c1041052040b1001d002400c010b5011420388803903620a105140103400200c0e0940350012041d010041c404154001109409212420703210001001a05002e04803144590301070580600c10075034a02d1000d4160441070f50700301c0600d00c07010b40c0310303500900c503d030081c0c0101000107a415030180b2420307105140241580f2215a41d8a08110110203a40b2000801e40f03034800d03c000540155803545100c40076121190000f101640000c021081301e040d16520040d044124601d02c0907074095040300030800107040100360300c0401030a0100f04805034015542540c0702 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 543933642 1250 543932392 543932407
    0x60c0a150e1501031209080d0302090102030702040903020102040e0906160f020102190e120f030a05090612190b031c1d060d020703030605060c0714040f050a06030c150c1407030206 79
    0x2010b1400c1c12a07206a181d0703c602d51603014103684514551203954840e82022401c002010300a80040c041c0c2001441a01e1610501e07030700140844015001c1a07005039404507041c49208030b01003c03036800c004080010017032898403804002c0c10403041c1c0812000c1080801401200034000d4060b035014284066203014003c1160100070510a0080d00c41d911070403203100100e44a02d4003081d82d40324041d2910195103445006107040d9450303804186141d03000001001240217900c13400842a014281014a120078222000c100c801520182e41c1083c1c402d41000749040c1240301492140310b005440c0e82000b000c40390b4103c00300107134001a2540b45405c00c00000b6001000801a801401420f1080d01e04000540e103c07001c0c0036450044000214040d400510148103032450082c0400280400400c0480d000107041021130940341c0030790707000007100d0325002d05004101c2d0b10b100f084081c04000d1103843c40001e0b040300041c1029000700740a00b80046486200f148105e007071090704080c507005841d641d42c0e04034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 543934892 1250 543933642 543933673
    0x307021c0b04200105120610090305151603020f0d050901020913050603190b01060c05030d0204080114092a2806030501050108040c09051f060509030c060c0a150e 71
    0x309603e030380f00c40da0f0390300d22207612071340c00341040d59085500b90b40810300e19511034041c801082c682136070034014080d0301000000002c030100041c0c140e207810002c424403141040b0030754a00307101c01c5000510515005000340080c1d031842d00b043e2094844500000b14040d1200c011a500a1054510070b5400030001d09011242c050f80b40c21441c0100002d80071210369182080031008118240c42009201c07035264001084094400c06680940902070b90689140c404075030003403801c80e8056841050565154403041003401e100400c1e880e881310110029003858045d0510012040c0700743c40b44100b03d24039030314140d0f10944640394084001203001d5102050740000b03643d004051200303031007120000b038200340001c200743d4840c245440c06141d009280000f40d034284003d40000e40001441e030440e40c0d43c402c0d11400921a03029614000304000d4954650768840c420501d41442005408540a24400c00520490b079100086500ca400d030400f05855029810b190380e00050b20100d65241040c1c401c44444401004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 543936142 1250 543934892 543934913
    0x12120918010e0f071814030610050307120602120c040f0807030f0308150a0306050703060b04030c05040b0a120804090e0a020f100c020303071a180307021c0b04 70
    0x60221600c1003848800404080c48100074040e0b401018401004520821684446550440d10314100205c0c240104001c03000107403d5035001c1d1049000411186503035003418820b56800c40d00c0980002e600e0743c00c01c800300303655801a21443c190360365800c0c02c0000b0f0006581c10303100341111405400200f400c209400344a290000c0c0500c0c90000d9081000103000c1c000010b080c41101d500090602003481281c60031b48001c08000c9c016111803134440780b40406079986450100185105040c00030b43c2c1d0500c498003c084442a400400d00404100800d002141d03035540400300701c9104460100e0480d0001d8041000160641c0c001e0194502c0510030000700300840000e8400d0b03845240f41041002400e2005e5030341c0d8184c5140107504400c004140d20f14038109034210749401c1c0e0b42e81c02e22040742d504560100e40303160710840742503d048a1a5250211291850800d20741100000c13030411010900e01c03544035200c1c415050024403520340c2011586503c0b8210442c1040a03030000081072280c41c0505000c583c40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 543937392 1250 543936142 543936157
    0x91506030c09060e010e04021204060f0501080a05120318030c0d18050603150127080f0f06070e010207150c02030c12070506090d080a020a0302060c0a0e06091212 71
    0x34141101d40246600c901c0c1040d0446100fa503a2880c0342c507040f0010745422581c0d040064000e40c080100040c0c20b0b040819990045110ba480000c05000090b030714021503206030850103442c0c10504800c1d0115400141812030100c0380c59031a6a2901c03001307160030b01c00005c481401d543c4d0101183c401c2040202103168100108a80c0720042d08003c03980b4040640e0301c45004181d84100c043c804180b403c45e421803001c49600b018105284844000701a121031108012520044501005410f10039070070244842a40c030307910301d0014a02400c501c0b44a54a491004140204100c00b0032568034881e8401c015500040c1030401000d003c1d036164070350040c1030039804101a802881078071300643c45818417a5682c840c1241d5000a460543d003000101309443d808012042d40c40a9010100b02c08524820000e0024401c59002048140707150300c0c010f805c0c094000d16080d0064000e0102d169520f800081100c0d44a50840c1d10558800207000013516104500c24050413522a04e4840711000b03010b1001003424 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 543938642 1250 543937392 543937397
    0x200f0f0d14310f0302010f0627050105010806120a021906021608030d0b0312030c0301031502030c07141903020102220f03030806120318011b0b15030304091506 70
    0x4038402d0a80c040a2120807107581c80c10011500140c4022684544022070040e00c203100109030100360392031240545050307400c13107100e40c219020500702e40394909108002041c8102c0041c02290300d07003000640099001002c0501a05050009000a500501c400c062075036000381030745c0c80ba5030604514681c0711007070b0003030744050702c9031031032091002c00b07040040c10460714900c0c011407400811402400c00b81c01414101c0b609840350300da88000c08205800a980304088040710241c03a907141d800d1400e8905c03409840403c015204105010507054503030300300d41110f504090000f030404288010342d8504006174420f5611240c030301c0a00420540d040d0000c0401030410101c08080f10104404103010f00307610310441404011207030040001901410000380e200700300500507002005040c00b02070440c2e0045025030107121005445001300e45c1c0041402c00807180c880d80c0901c05103220758038820f000502030400048048958000d04d03860360100100e0f000381105406c1405051900800b8100d40380c4980a444003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 543939892 1250 543938642 543938671
    0x80307030605010e0a030311010e01061212091802090607120201050604051609090e0f030403030e0a0b03040b04032304061107060f1202070201090308030910200f0f0d14 74
    0x9040d84210701403035904034004c00300171066185640130b03100801510a100115500c4290040e440c49080c4540d01c01000303012004480f07000540390a14403010b5420070395061000103075080c0f01501c55010004400f0715200f000590b0b40e9240e9000030f456000300709005142a06416045180c00c0d81904024040e102c103807030034442c0e0b031500d91454260040d0700301840c0020b1400f400c10494581c281c0c1001036031450140c10ba40504580c24825420b5501c075800550114803c200106030b00d04001c4c00c400010590b106040307055040c5543c03001d08080c0c000c0d10240c20400300c003c040c242105404580010a040011410b0341c440d61198040c10005215840401d0340c064400700149c00b80c082d44040c200410203a88440400c01c91268801c02900843d00c180c0c10800400350203c00290240300550041e000034008004a00807985494162011841007100c541050500c0c42c810410000a81c2c039100454500542c42d00e44c030050f07481040c0903103d0f03034a2038641015000b21441e0200f032640c80c0207442401d140c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 543941142 1250 543939892 543939899
    0x2010b131407081b18060a09080c03060103080d1a0a080708120703020d110307150209120c0a140d050a060606020d0c0b0f0921030601030e010b13021e04030803070306 73
    0x10f508000072203ca0a5092040450f84029001c4400401d0036004a036100c1040c560040013280a54011902c00004107007045424130948608002400c4041400c03001021251704603550051703035010b5004000601902d841004030f00d458101c242524000010308400341d610743d5410107995030346c040c0c49200d00038044c2440c40c500040b81401150052a0550014086d581a0080c202e46180411001e00032500091007450001080d85115166009803c5070242e2211000010480d00001d01074022601d944041c940002c503440e004480c0c022989014040070041e184080450311041c14030000900d43d0180d28000d0040103501d51018050398481d5088424541d89480c0c144e070420560302e8040c00d98000724002a044004504015601c480f862060351000d1280403420b1622301e11080d03903000a001c02004110740c40d649403280a221030140c8009000140807032000c54406c100060003d220260001501e4007405040c4100c0d400020307007070342e6a03561641c0da814a0309a030b410503108140040e05254000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 543942392 1250 543941142 543941147
    0x90d11010504020a05120f010519110c1b01020a020a0902030708060108012714070804030834030e060a0204050f0a03020306060d020f36010b0a0f02010b131407 70
    0x6601c0780c1e90113040c58038058245400c2080c0784d080384205070214880c2902c2c4130b020764001c0c05064090b061401103160010342c0d2040c500160344100207002d44000c0c081c0001d8000303c00004203150303a546010500c1c00010301d044010dd0400c965020003940100980d000041c517034820780d00441c46006030740e50308022900da030307401151340c0b640c207100717184007036903a50f18528800e030601005040c1f1288075840003e003c6072050490f00520f0302243d0440109041d40100028160404a0345502c152a8617106080131250443c1e801e85203c90f030000c13600156091620302d40d00740290b21040f10000c5078001c0b42e60910385445c81c24040d501c00e008860080d20703403a951074130301c0c10006000c80a996004003c1c19040d074450060111481c420041a0707400000c141210b100da03124840400144903006016442d0701c11510019501301c1d900c4442c1e0800d1400d070000401420802a080e02d00035009450070f512403244101d0200d02401181d10206c0d440400041c1d01c0c905440158040255036110142e0701d517081d80d503450103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 543943642 1250 543942392 543942401
    0x61d03030a0917070e041101021c0507030e1206090303101e030204021804060b0c011406030a03350a18050309010507060f09031106010906030804050d080c06090d1101 73
    0x222010818402d000c0c458090101c2c0e001910003803040480d810140d850243c12a44001074406996846807120340c4400340d6814080f01103401c42085c001d400c3d00500c2140107140d4418240050304002110300c2c2c8610315601c2c00f50042e0b00c1c206240c01c0314102d0404044240d181d40c02502c2140000f9003140d00044c12820380f10820361099074100207100010319507001e01000c2d51203555183e0190700c00e2881c04295035610b229580291801044603902d03284800051b81c00c503419100700954088110003003205076980080c41c20911649480c0011a91605040000e1354209015019200d580500c00516510076500c407218031901401c2000d215110125441000b6403112000244c09a0420041d010b800d5003e04000c0ca60940b01c0e0b800064441c544094003000c44d4400c002c105c1c00500c1940c601d5a14100c00c00400d405400c0301c860401c041482c6954500031845248907440c09040d00583c89024007003110152206442440c0955031141303080321940d0380302d000c514100c80c00b08031410300440c00004141306 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 543944892 1250 543943642 543943657
    0x11d060c0714240108010605010e1003020906070804151418040e210a270504180b0f060909010c05030a02070602040803071104050604091505060f0307061d0303 70
    0x40503140803855110100004000754084001c0c1c4266550302140c1c43e0001c40280140010300300300391040d41442d03621402e540d040d80c031039810010b00c408040c2c42079039203814803500d96603907050050b0b580c5034104c0400c6940c0503098015040d07080100d8005000f64440404050395092070b500d85032500d54002840788903003d050f80547d10360340444043c696030b044c154404124440c04034101c4400b85000c9810061030814014200610400402c001c1c2043e41c00080740d8016902c0105041c52a04100c0c007441d0000340e0611860384699181c000d540301058001d031958103000d4010b1000c210500e4408101c1d2280401925241e024459a800043c0e000c0c6040c1706442e500c01c2a0b664861560f110402480e02a4105800546286500f00000907441c4001c100400c1103601c40c01103403500d08880001c1204859000f0506030107103003892a14170000e1845864900b00f28040e240c00a002c0c2c941d10301088135120354003411505481103490200724141c020800030f0a0180e01541d4011060b042010716460707005406 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 543946142 1250 543944892 543944911
    0x15070b070503070509041d0a030e1f050d020d1103090307050d0203090d0b041502040f06030b090103150218060a02100608011401050d080d1104030b06010e060904020d02070204020705011d06 83
    0x3840345c034501908000d00410300c8000c4689032180800740c090500c559072004801081141d80107204904214000c0841100301c10400800382d1000c5a01402174400c3e6080050398075400500d030704403012310b0703408104000200c80200f5281c0c581900e040e503032580508001e985502c02da00310305032117610000072695034041c0507000f680a58190f40c0c0745014000d000e0700c2240c6075182122441000d0f0040c3c805040105408150030b0f110070b24054019044034807000748140205400d600500c0440c2d1050500344122547d00401a6201d601c03440d010800036220501503885000001c003103440c3c0c1d50018030382600c0110000b0800c4450b9807120590f0803140005086109009044010442490501090100540113070300c0c0603c5c3c02c1854500d0011642ca41d00709100c00c1c0c00200d0140f00340408922102d41c001d00c00c0c01d11900b0805524005100390054075041c078400c940000381038140c007010b501030701d1019501420540d2200704501d00a4042d2114944254000200c088400803912000908900803040d82 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 543947392 1250 543946142 543946147
    0xc051c050319020c1801060f080403023403060204050a08010e060106031d1204170c0f040c03141812120c0304020a08100e0706090b04050607020a0515070b0705030705 73
    0x34442c1d099195a11003540194000c90307070506001d0300c90134007150b501211a0014613003581003080140c003500001049000b0004980308000001c1d400040d209291620b05410a40d0181410000585840c0c4006081000000445c0001c100851a0041e0040e504d046a00c0591140c4418a0310b00300c908400c02e4250561000d00104100d134029444082d00c006118800c003552031001c4040385ca040e41d02c0e48a40c40e0060002001c005085000c012966101e05840240038010b041100103011b800c0e009910a124903624081e0300a49030095004006100310201180c50b2803030914103000410449030318410207030084e0600c440c294161082140d40c6401149404200ca84964082c1d000c00d40000b131007280c104c40350301004690340c20b0030080321208550708071010901c12640b500c007a0600c1001d612000c140b240e0309400307020704480340f03041e40c007a80c3c400d039003041d115201e50001814401e040e0344401c2d000400010702094080384040100140350180920850366251070700c00b219640300c2106c4040001c0ca0a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 543948642 1250 543947392 543947407
    0x15020f0a120e0a06090303030f05010503150a24091b05030406020f130b0912070503071a160317010510081303030b13061d0c030708220c051c0503 64
    0x40c03118804141401c2ca40181c0415244001c80c0d07024a075900090049800c0c00c0c0200700b010303071500820010b228a494148a95494480404d640e0445103c2c4482c0202c01c1b4400102e00e81c2d00380d0f01c40780007442c43c0e940c3c4ae900000c40070002c40d9400c480d030059200711800c0ca618411b018440c0b00c1202031604a56448902d1507555840d800000d41201c4220f111205081241002001249030100d02a100c4228040c2c0d5a0405038204a43d8882c5803803a01110b4104c06010001a5400700740d410440d511207207500643e24000f400b140072842102018240c4d08103000c002070030300d40d200301040203080d004800300c0d14503600c5a0810a04079507000e80100001c0918000604952200301280c0f056803081c207021681c0400600040d038424040b46004040c0e9035242010042d0781d00d40d01510301440000d0901c4089401c0010810802e40f000826080c1400000c00200e000315030f410420000140c07200c00e000c0c2c4182c0703151500034042c0c010761003036503c14035032170030312034000060b9454411074198810f0007145032480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 543949892 1250 543948642 543948653
    0x20d06150621060e16140a050901180506030c13080105010f290d020c031317010f0207080906070f0507030803340e011404082410060e0f041515020f0a 66
    0x1004044030803c2041d580b202006c61505014101c640002d403107494071000c905c000140107a0b071201ea407121000407000304110a1322200c0480f13030401806121581e44190003802e00d40c09942e01d0780101c07619864440005840e0102100304030075184022008801d052b1030700706c0115480101d41501c0d0b1070400402460184041940c0100021b4100406907030074114003600c100545100c5900c081001208600400701010003840f41d001441d0707210800b1424056141c468032240d0156403407240c00b031400001c0003c280150326005045103648002100c3e640d079240c1c68244040d80090700e0307004810545941c005181c020740c00c11b100c040c1041046403044215000004c40700090f42817480e034140070b00701c42c0c007078076000c0c02c0401040581b400c207006041c010141c0500c0100710f00740300484400f0b203424000303103c04802103040b040704071803c514001c0120b41b22800000d210b59401000320307900c24134100000040c00c005840f40d1046888a1900c481200c400d400300740e03218207048010790041d402980c190350000c1c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 543951142 1250 543949892 543949921
    0x2030c0603071d0d060c08071101090302120c03040512010b030d0903240f060b070507060e131112041b0e130b1902040b0d060506040e04020d06150621060e 68
    0xc010004c00702c5860b603894607000c0790700d07420369000040d0240301005201c07500304518422000b0800700801024040f03490003522680306405003003103c0350000c0d03c19007260040040e42c001d400010b1111b00d0020f03039400c1d018000e20b20811140e010380909150405d00600400710701c012a500a0001001d058000006041950399002d1a0703100035a40d0000021030300301c07031266001900714032660325030320002810b041d80703031041c5036101c2e03c100304180714584001c0d220806039141ca203200d03078030204070007145a403c001075014000040440002c100e0800080c04404041c0b000a08218903c00c000207488502c50f156845049400706295004a440704001840b0000713220b500070b030803c0202042c1d03071042c038121090b42e2041c1e02070302103107101141c1461201d5030f0384940c00042204541942c07609107040c0d903102644400030400381c400c5000c448944248a215080030b910900050b004400e5903858020183ca03550003032403030401c0c4c030801030784040b1242c4140c461722050790022040c1c00e455503211000d440f40c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 543952392 1250 543951142 543951197
    0x306090703090302102d0203090a021011061005120c15070201030905030a020607020f01090c050f13050c030a0c18091d060109051503030702010806060f0c0a060902030c060307 77
    0x14495401d2540740c10190707104040b8000c60700a451014901074040c46c0403880599140402243c1c81007084c403000110001d00481c0c45641502d000004204034a01560202c4910400342c4050140c8010800f807460070103248415184c084034031810303125a64060070740c0ea5500100d0290090001456903441d6035a100291182610500d03011a40c092a55207d03030454110702001009030b4000401e100360340c1d8040c0188803080c0c200380000c00206001c0c4c0c03541c0c1c1c0c3c03001d50ba00c00c26020741c040119040141e02c0303c0ca005001514a07110512950500f0080c4a0588c0c0c012105420b074186050122055548240180081400b41c03070280701c2d0726803c00203100000c0c03000400382120114000f0a9007100700d02805514002c005000c0000f4840c5004c0f511000f0303550841142c140b0a4208120000044c1c0c2c00c2551160442410b540f182c0e11804410700807002481407881d142054404c220304002085015005000c03d2442502507074004100c2205001040c00305031034017000f0508054484101d50450342824001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 543953642 1250 543952392 543952397
    0x60a0b0d02071a07030c021c050703090b030414010f0911090705070f03030609060501050f0a080903211f150806031923031305010c080d05070804060b0603060907030903 74
    0x2030203856540c1540e040d001c1960048065900350030000c44503003510174284001414001341081e6460500032364000341103251b07501c041c06400700d81da07018940f00d24440c0c0f01610700140c509569003441d0034410b004030540c8021345841e40c00c22189600208070740c01516180c1d5803000d1249008940c0d02c0422400301c400600d0728007044002c0c807211010401c07030391031201c0c0c1c54000e490000701d0908009048056402d0f44d00300d1414800c1c2082640c05000c0c40f41c04032403900c51949015401d5442d085400750440c0306d604182040301300160180b622020041c4200d9001d40e004020052100c030001c889499002011f1080d1038003103911103050f030f03461070240c1855a031010000f0b0a6404a1892038060700704400740c6d01090f1030324443c070b40030300c80390300d0201c03180c4081258080011030920312546102c0c8a110598040c550400030550341850401c0100c0040d42c207000c00c0c0580902480c17420400082810300d00b10750a41d000d5060100400c1c5034101101201d00469002d071081c04959079055055002d0070140000b1002c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 543954892 1250 543953642 543953647
    0x40b0a120504030e031e07061d0a0f030b101d04030315060531030b0702030702090a0b011d09181e0d0212040303090302150c0a050c12150f04080c12190503060a0b0d02 73
    0x4c9c0d5581c5140d0301000d4540214010521401c60030907082040009041c503820b451944000d001c0c1040039045000c0e001e030b50342d55800c80e5a480b442c003140508005800f545501c0340090300819031640010161a40b44100402520413130701110460007175100c003035052603200469840c2400030032219101a94483d4240c0101c1c2d10341081c6a000c6605001c04a0340304181c01e13600e00010640e5a400189440701000302c00e49101d11242c50310002d00d0302e01020702460300721681101c0701c13100400241b1001501814a100400140428040d096141c0c00e410344035000501a0780d0100c6a0207081105a40a2340d80640e54286001d042d5424400035070b000d4003844031250020300507040300c3c580401080002030702c17400241011141041c1800b066803078124540030b0303582086144542d00159071200300d078402e082607503688940c0c940e0b04003102c20340301e0180035103405d00540da6101c6440380c00000030304860a143c1d0801c14403a50768002107400303000a40e40c0c2503000c040c14400b0020450620040d21154000714001403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 543956142 1250 543954892 543954947
    0x3020f0f031e0702030304030905120106030609050c102607050d020d200c0a060504111807080105151e04050414060a0b090303040b0a120504030e031e0706 68
    0x100c25410454480202c4502c412500d41e0300c40c0718408290b000600d07800250305500307103664090034541e410b0058600a8401d101c148401d58001d400080c01150000010402d00301903041540e141d81042c01c00e00e0049001d460206050740c4145410035880601020800800c0211041c018580c40041c0c0407038100b1506001c102614400d0784010900324020740d0000880e05040300030011640d801c1180075a02d184248130503d0085000708203100e015074401000240750b611454003000404e0143e043e1a04500c1ea242205c050010100105000e040d03142c860149aaa030740c0d007003014120480305101124001804941180f5081300086411220740780c4209040c04e403140302080403254045c8000003140c0b2000c040c40001e042c070b8075204e0041e208402c84a03240910001c0801d549210724801d1000c843c20000701d03100f0240c07085a20380f00c034544280080c4a00e0a20307050092040050440c52031003800b428140c040319030303122507080000c090030501504141b85450800c1e249491003207442c0c04100541003560 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 543957392 1250 543956142 543956167
    0x180b04120219081f3201050402040b09090402030a080f032a2205040c02010f0e030703090b03100504020406090311010f080720030c2a01020a02131d0607030c03050c070303020f 77
    0x10b0780040d00c0d0817003098090f0404040840040040c1e21040c0128410402808602090001c0341c050309404d4a14039072a84407032020a242480d60344018010707800216000810303200c5100114001c0074401e0001c498100358260003003c003131888020007484001000b841c04e01c8040445615010034029003002c0e18960381d6004603082c0c07441c099040c80182d5440b400e01641d01014410168070940f0700009500b00f0015aa02a19003003940c010040c0c0810b01200080d074020046040001401c00540150744955452001800d00c1110b804210f80b0089025203555255110b4089000080c103140d0b1102c0054842c00c1c01901d660130351800081850416010808480004200810700015100000c2144042c0c00030b00060001c07480004140c0081c4000700d5030010b82e4000342180c8410340403907901c840c1010400480001342000345001e500b806426869200101000c0707041c500c0380605031800d2150514800c0128100d42c021510f81401074401d121507000310380b003640039040764940c070064246800e5120004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 543958642 1250 543957392 543957431
    0x207082404020f09190e0705090c03090a05030d06060813020d0602092d010207081609181401061802040b12091501031110031407180b04120219081f 65
    0x10340e03401a1a00305031501728400348280d088000c016005004050304000c0010700250001c2d2208420741d0010000c60f6552005000300f0025a80c4403003201da50b61a024212030241102d44940d41c080360f1440c000421001b12500c18488407a8000d2603001c100d0103503036640c0c00a4118088240d088180280020100c00b580d651b803c5e011405221440044241030000a103005001d8001c00403941000c00c00006520020540d40180c4008030004540c0c4603002c0d8190f000010b1b00395000d4242c10008040e5502108103500ca441958100d00140c080700826806c1e100507845a071081c281465010080142d842141841454000740950709464480d210f5080d40340038807a0a80050702e10035130701e9441840c03034500440c0c01c40c01c0b040a4101844100340304145e898801d10014261002d01088403010800032803051149800b03880520541e0351200e03141c030300f05182c80e0702d4202c2c103c0c0940c07100e4441e218001010304104046960400040549106031120103a09580031506041000e8a80c000c2d125106520365a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 543959892 1250 543958642 543958651
    0x3050a0605070e130b040f020a0c060c022407120b0a060309021804050f011a0d0201050705070f0612201e07120305190b0906151201090207030207082404020f09 70
    0x40c01700b40544107404020403034403e03148244000344104880c2129940107400c651060b900b00030001801503d9240c1a424901900245a0300c0100c41c1d14003c282501c24800c180604c00b650b03079444144a01c0d220305c0080301e1100d28040c2d40455254030800c03038030b44607400c1840311602c09400151003601c8681440c1d080c61003542e00b100d042d04186041d00f13a0007000d104420072051011002d1800003201d40106641040c41d120290400c140001c02100703100c0d0410009009118410015500341d9031003070001c0603a1446070340b00c03200703604010050420010007408402c070303814102c0c0010300c0c00c0802c8880207940b0440800c00041c100c403d0112801090b11281ca10403e10203c0d10003040900d4828602c00130301d415103a50301440351030078004002c280c89509616901c1a000c1e20590345980d012642280207009070208010082ca40c14000300b0030f82420380103854254801c0e004c5a0085894a08843e2580d00c007004001e45000720007180c90b4000d64800e03100390400d002030b0501c0104135000c0003080981104a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 543961142 1250 543959892 543959929
    0x6080703030314100302130b0f0d03030b0312030c030a05070915050d05090607092303060115090806091f0b0301140103050c0402090102030313031106040b010e060a03050a0605070e 79
    0x1ca0221001c0941002c20742d2141100c40300404c0d4500715800540b51801010482c5100399540d00c1100d82e80d01d030508a22070000000700302c03059447d4140b4005014207020100d0f68001d000300c000c005503421011041e00e00070b8198101c01c43c10741c0d60751005507000380030080038501086a4003c000901c2d020088180c0c500820687d90a03541e0000c88050000740c0b54050010304d4558000d074100444107900203100d0083d14091000b6024030320940c261402c000c162403901c241d041c0201c00000810201100e41c058150f84a41c586507040d035603c00c02980c03540da0464900001e600302c05007000c8800c0d100d10700b200004481c0680054420207203008642110811100441e5280c40341c4014001d00104005002003181d04071400e41ca8811a680001c0d241d0001409452158452200000c03c0500548104d0008490303403049070014501810b02d010168004e04c240c441d8441d0080c041561030070a8801d03c815260032000070725880503079684100c0144401011042001003d50b0440307066a11810800700e40280070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 543962392 1250 543961142 543961151
    0xd03080105030d1407020d02150a0905041a010c030e04200306011202030709090906020405150307030e070b070305180907200a0f0b0c0721030c09030308011701060807030303 76
    0xc42890b2810840c00ea40009020401c00c20420107a007000c1281c10170755065030752001000c80da1001c80e0100050803000e203416a804540d803282140c2c443c0c0b002e01120000c0b50288415050100c5403940250309010250000d140e400d4103202090207124802801034002d08001500e01070840d0703803003445403000c0768400b60810000510501d903038070031441c1400290004007149582009500030b030420000d403095880b0f050f01d03440303101c051003c0d0790305507002420081d040200300948083c1d1408594821035080c0042440c00c282002c61400c005442d60540306c1310b48209141ca00350f62130035505134015a503000040341c0100310b410071945070402c801d4099012510b54110034465030300f1003440e042e840d14116005038040740d001781c0030903c2c4144a80403070350090303003a80480d210400016240d204146000e81510b51541040b0b2480c0840c80011954180540d41000816840e050446080000b444042c0004185034018808454800e0f100105428100c00000b4026500c45445090424991040d00403998a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 543963642 1250 543962392 543962399
    0x509220f0c14010807050a03090804050d0c030212010b060904020721050301060f0201050c04030201031e09080702132918090a0b06010930020d150b1504230d030801 72
    0x100b0107001c0354100c090134401943d1824240042007400380200101c101502c40f4840028021480c0840380545070241185040c0890380c10042040c0c5003030310049000e010781c4401e0821514042c42036481c850401014540307000140000c0001a401ca0807040e01d0034803804191011104401c101c02d455884103031980c3e6100e601d070400c06030603403170606402e03015a41404100002c200320030040700d0580e80e09007400611402000300721011134450306180004989000b080c2d00a0208040c00b91031428821a6025856001e0701c0c1c0080989a0b8800180458846a400c80d5620360048024503d4402d014051818050888064403818042510901031540000340404c09110741c0e640d4103940901e00b82051340503185003c07903001161581108955501108141072080d05031000f03807412660341c0081100b810305c1c5450a2001d40307856400c58009095243c004c4800c4903003070410318454940340c030b0b5461504007483d120000303e1010b40032210003004242e2141c0c205041d503d01c0d0010010a00a5803074044940c103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 543964892 1250 543963642 543963659
    0x31c0204050d0f02120a1a0c040b16050d17271b0a050f0102060412031b0e0301140c09090604090b0414060606090d06021309020c03220509220f0c 64
    0x520080c6405d074000720094004110702d07101100019007400040c41c083c1d80c94000055090042da00400428800019201c001007040c1c280c01800c070b4001c405840b540d03805130105407429007916082800b220440c1c40000c040816005052a1008001c0054810002090080750074042801d182413020714400040c035100c1c0c207200c1c554801815040d03400d18000d18582c0c0010b5038031600188002c0100c085005640c4481d88207070020325030301c4100c50441000228080303001c2e0085a104e00458000c1d880c26484403500300801014034042c0e54100c01a40c0341c00e0704030b002d006c024a0700904c0b01d50807a8527107114100180200300030a11450107400e114210311804a9004d040480103801c0030311030700d005e11864445550f44020b01e8407499001c0c90042c2e5070340c0c003a1a10445d0403096401001514400f082c0d5107400d41010000701954020b50800c812021000702d07505058003002d019440d00038030b0300000140c15800f00d00841648103508140c20b010721050390380b4000039040b140c4c0c040300c0440441100304598134 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 543966142 1250 543964892 543964909
    0xd140d0e0d0f110d0918090506070f03150f05060703020c1507140a0209070507030c0209070929190909020403081206060315190305010e1518031c0204050d0f02 70
    0x43c030740f002610b40c01141e010000c0c00c0c81150b028221011011844107000d4100d16071004080c0f60b40082a9196072511800140481410900c0c090100742060022410306254042039400e0300e00c842e1041d07000c1424072040c001c540d00310103170480541c41441508400c5030f880104c420080d074400d052480c0d0303841d8985445400c0d000c204a002c5043e81c460302d40b2900580d148040550b00c0f00d0300e460102c0d11070445050481305007151101c0603400070421407c0c4540c49600429800a464400400d000d013112110800324081c80d04100814800400b8040c1d1004052500080d5461380894544150083c1d02d0f442d00c00c049038040c2d40304442da880005000726800b41030b00034180e0321500481d81181186041d0100c421684031250181d441a00c084220250081d5030303620742005141c11070000c04c10244400040b41d45c4031f00403402019800c04120010301d065a58010340c80f04081108059030800703a50420740c1c280c0d80400c403440e003d125020b02c80420161030322444041120b006065440f09968240103001461 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 543967392 1250 543966142 543966167
    0x13091a18010b03060d11060a17180604020603181b0405010f030f020d050709110409180203150a090f0f1109060a0501080414010e0706020c030d140d0e0d0f 68
    0x4420360004010b649510002e5903071000084c0c0c2e18101c03980d203614042c40c0700c401c4088250b91000300450b0252101d42d0189071041c481510918004403515040c0c00c040e006143e83c02078104c142c2c444c5c80083c1c01801d001c406076400c480d040a40000000500c0880da080002484000d50340301443c02d101002480c15019050042060740035801d40d407815910340281758130380118068010489240180e04006041000000402049404005540f000c0ca00303464079030b001d40f10341c940300c5d801c2821202d42d90400d8030b20007000a60060041a80600800d02c080d9034410080c001141682d482304075401054100c1d109005182c4a0150181a075000346004403030620a03410755409550300d90100b244030788a0114410940e00f09082809050f5a280790800c181d10810b020241c0355400e05a4070300120b140060100c090f030300d05070203031140c41868109240c2c6d42c241d1108010009920444900001442c0034000c1c803200c05400d90114021507004811307860300c05013501c040006081c4104520041d036015280320b429 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 543968642 1250 543967392 543967429
    0x6042f0c0f0f0105070e0603070e0a050a1712040b03040b0a0e060c0c0610140d150204030803090d080f0a0b0d02030703080c0d0c0c0e07170705030609060d0201090b13091a 75
    0x101b040d0b00204504d8040180391000380b21003001d42c81d2142e6a9a07403860020500104085100e58480400d030184803c1450100309903c034900c80011014240f10980e000d991000490f075003103039a03a848020000030060412010196104800c8450441c284481440748402140c81565180348143d1185401401442c0542d0b104525005104804103100f011054600817548c2103010510303410160400c00c040d500c0c1c19001032001900008001c40798001d544074071030310000d644820a44242c107981c050750444111214110740b03030000d80b82d441a507000c51f49010010b0542c07003042d02d44d0342c08249010b9042d0000e89511602040000c1180c40c1007024001c0f0690b180340c024240350f840d40c1c90100e0701010307008145c10b0b0150040060100ba10842c207504032517540000c0404941024a80600359500a64400f07004140c8600000c01e50b0500b902003600d0540d060b962031600c04d24081d081e1840c2e412000740341350b10401c081c000090340d031264056000300095035583c0000d542a00c00420054158100f1406070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 543969892 1250 543968642 543968657
    0xa03090f05030307020a020901360204180609050717010317071509020405060d051b03120703080702010c11060402130b03010903030b131e050601021e0c0906042f0c0f0f010507 77
    0x42b07003400c111000c0300101d560f0810400f4111009606c080c0c0515040448442c81000841070610b01a8101d04121014070400704405c1e201d000086885880506800440190801c01040000c41d122466810891012801403d0140c2a9130703030074142d42281300b61611a9120440700d01036103824032031250400d200300c500c80258205903031195180d646040407202060b01c23148228001e0b84060000e002d0a0000c80d2025a8032426840d014001410070f641d86001503207050b42003001d00c1d015541501032085080c0042c5034030f0f9900d900f045014051180070403201d9441c0d24400406442c00d000d049120361003034a02041641807401881200008561401c0307000d42042914000c2402c51a02c4000b0040e881c603000c10300390348400040c1d00d4184105c080621038559120303a00c0488802184100116400b00d540700d0b46510f60b0303001c10080d6041112000c1400801300c9a031404408280c003110414149440b1180c201854003000d2070070801c00d2005104c0e40e820418060392900c0c001c1c030540d90b03c02c1d80c1d03050a40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 543971142 1250 543969892 543969929
    0xc0306090a0b060a050603091006080703150207030e06130303020609010c050a0c03020a200915011409042c060a02030f060f0d050d02010b01020d0c05030a03090f05030307020a020901 80
    0x6039607640c41103010741026480d4000c6400358030b440e00701c40702410010300f01582e80d0916089444d602ca00d2007030b11866151400c5000700722a540031501c842200e420480c8000110b0b040060b04000390700070101203040c0271004c1d511400340d44505010b4080100c9419250740814a5410081d0a00400602c203000f142d150620420206030040d0035214542c182e894011910314080c03905030b1034030148180c007400303404030481040b440d501c108655902e81079065840c10940c0c3c561050303032205420014082400700d500b41c10801d10203101c0b08050220740f80700401c0410203811382c1d114079021064101606c400101c65440b800250081040102d0b000700e650b0004514600c0c241c1e00611055201400161160244010040c00c3d0b6544201c0481901c0d0040141c030b03c03038448103101074002c000e070a400501600500184840d1140190702d030154450300701d00514500180210b00720000c00840504890030441c1031008070200c2d000300083c5116400c190010403c00d0070038010450304c040141d2010412800404281 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 543972392 1250 543971142 543971161
    0x10204060e04290117040606051c02030d2a05060714040308030a0209010329030c0d05150c070b0a06090b0904120f0e1801051311030c0711210c0306 65
    0x242c0f41181d00030058802c0e1415040102c84191203400c0b15030580910310180424010b680c0c0c000700441e0022101505031030103030741119a29090140c0c01941c19001864058000d40c01400e420054000310381800301d0443c0f1401062140b042581d20640312a80004100603085821002e00211050840d0f252400c0c0383ca1561a001c881c41b000f0100c61109030045403621040e402a0818400c1c0220b10090b00000c1d4901c945130070300310305c0d404070007442481000300d049000d003060400c0140036900075020300042c0c04c034030b00c4078080e43c540500b03445880c0c1400c028950104200c1c0d810540680030086020440c13034902511541619a28400d80d440b5071034023014400080c010a45030a09003a0904060300a151002020748100009055040d0004031034004070511b4480c0400300d40c1030303c0e0708031003500050040b48600d07811a0440e07400b84400d42410004214944013900141540364403c2c01c4075088040224040351070b0401d61b043e8040c0b4400b8071844050128070920510100f458240c00074001803405d1f0814 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 543973642 1250 543972392 543972431
    0x70b15150d020702060d020c060a0b0102031209070b0310170d0801050d060608031305030f070f1a212e060309050c030601080307051b01090b030a0e010e010204060e04 73
    0x840052420008204040507425015104219001000700e612a0f50341c0441c60b029510100004815018000000c2c1048940340302c0c010301c0c49410b900950134000e480501e85210000505040000d110700e410028040d003405009600c04e910700c0d0042040b40349044403115140e2440c0c500100550004200c5005442d030044071141180c00445203481084624103203907009042d26040080d450000186400c42c0a44050094040325025030170cd43c040202c0602c0030351220a01d00800204608524040241c0b444200307540714a0700203c4881c80c0b411110344188002c041c901340b403140024030548200909a10718100054074a000c0017020451070300000809030000010340200410f044c1c0e549086421b100c0200591482d8100242c101d46407540c650211560381d400200007121103200b40d20100e180341c007000c881e0251041040e102c200a113410321007058400d800003400e02c0c0fa80c9998a41c0c1d000300321003d000382c01650b401d840006a4550803e40000c0c480d049803104503010320301f000e4031001000d0142c0d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 543974892 1250 543973642 543973669
    0x60801111e0c1f0e010f02190504050f060307050c07060c21080a111b0a0209010b0406020c15250c080c0109090b0301020c031c060909020603040303050406110708070b15 74
    0xc2d240f0501007103840110040c0004040509035600e415202030050003a90700030030103180756655504914400c990121068840c60141303503042140720184120b42d0904001860300222942003681c00c0c4401c40c4105031030b1102c542d1000c80010404a42034080c003c9004806121b4170320303c9034940001002d44800340510102501c1405d4450382c0e001802f0305c4015400c19640021030b0744502841c96040300c14030f165119a5102c00341d104000030000060244840012a0300722151600070b410211220700c01c02400e842403031210b0b884400c0410052114800030110300b10740000c01c030300d08280303a030032810400c140202ca5004040c4c1039012b050f151444e40e0304500420704460f4144000b00d000340c070706408280607008840310304c0382034030010880c2100c0c4450707444225400341034404108045e980e07488050040e1540c0c0341300039401010070404030380464402d400490740030780103102c0810483d80c1841541e8090380904400d41e2000b1000c2001030800898441301500a0040810107030115030800000e014000241d9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 543976142 1250 543974892 543974923
    0x240a03051312140f040b03060901060c0302120702061e1b06060a18061e090b0d0308010905090a1211060105090c040b07060e01110706050f0f1504060801111e0c 70
    0x3ca40488103900032003112007000b002542c0070707180c5075070302d160807485d8000f500c24600c00c85d198000410708900c03901c1c4c0c403260241c0650040c60300d0483e1800704040c1d40d200c210b00366000301d010066004030501c8440d210034012010fa050700d41d20404403407914200c00903050101100c0c4c0010742030010341c0e030740c40b10a00260b6503c480005850307200c036551100241a03c0c3d000a404415424001d22400f08007104d4108030380040001307000103a008420030040581441000f4041040700b00180320140c12030740700c16070151020701100c0a2103415161200c900780d14001020004610b4650903447c00e80c1071017581e006040c01d4403c07038000d060811880390310340568054800c40c041301107911414000d15401c10b19841341c0207002004202401c00c52650b00c0c0d4000e1030241c41403420036010030312148485e04030034407407500100e86440b80e8860040c0320f403c3e458040741c0d644d403003a102c0c40080b8060b80b0038410100c1c0c51140080c425510181c1e00100c50440095100700904903d06002550f0005030114948001303002c0c44 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 543977392 1250 543976142 543976157
    0x170c030711030d09030c0320120a030b030615041512080306010203160302060f280b010c05190501051003080906090121060602010b030c180402240a03051312 69
    0x4211689180614088004100e050103084c400741500103c0d4600100d0017070f079480050388250440c2c0c06440e200c01d50074020325403082c81c60501e4050402c01401550388646408106001801c0000e45401c1069840c02a41c1c651842405010318044c460b000c03035641022128980545000000c5003194006d8101810a031000030000f03145a00c24030417079082001d80008940d0440c00340c1802580c400044840030940c0b102030011652134030f100b208101c4000e00c1c489140010004140400d0301a00c4510525418868400311260000b2414088014070525940045482d03000b80e04241d829200c01402445802c3d00c01e082c00c0c030100e0007881c1102e0050001f514100da40e00490801240e401e1215a00d800041001c0303680210052429002b4000316803d170f0b802801110501c404068491100d815415408288904400c0803c0d0150b0451039002d4002410803002e0087e440f094401003241080381d807008940051407000e043d415100329500684140800c0010481580d240080c42542c1d80d90300e8144a40f0303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 543978642 1250 543977392 543977417
    0xd020102100b0109030507240305041e02130204060206060f1005040b09060403060e0c01020c10050409200f0406090e0c030c070f051c110c0d15020706020a0c03170c0307 74
    0x140e81c1300b4021940001281c403000c0e51082040c40c00815003404002a04c8a0040a031145100703018040c011034001007408205130340d00c6a01c0d0f5146851441c01c9802039406036214007147d02c2d83c405000140000c0d006840f440ca40101001510b410303500c0c4091045a46584070403c0355408001d9905903083e00e80314580d6590740c2d60000b151400356030b10052589080c0b150001c0700c0e0344042a100c80d50602a000c0702d4498035008100283c445500c0c0c0c0d69000140306100401906004d60004c2807690b46401004000c09020031044009a102c4021219462400601000425408000d0000078103c2c00043d0902d4105001404031610010780290213600001c1041c600748440600d03010001c55003c4100c506000762204120707019442c401803000440c1010342d1103a412000821040a142e1000f0a6505018a20343d21038a90140540400849943c00e00c46103000030418030042c04900321072f4441e11740c500c2c6580740c010004030000300c040142d0710034941445020844a02902d4002d11642419440604c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 543979892 1250 543978642 543978647
    0x1b070f051206010806010509181b01081003260705071502060705030f010b09030c1e1e0603060420070501020d050106051e1e0415080f1e19020d1a0d020102100b01 71
    0x3031080140030140690007082002884a1002094030040cc0e254080150f0f105258964016003a11000d8040100118000d18286043d28040481104c50880c07034180482e0740c45541c54581c0640100c284510603601300600caa070100b0101d64040400d1900728a10310b00242c255400031410711481d0ba149401091019081d41c0500c15414000c502800d00c2d24510000484e07d00415101204180500070b20350f05450031030400083c0b10b03082c000190107140f540e00c074101400020084100302200e05002078408000002c0b20f080204821360241c400542c85110903030302c103000c4500603030004060040c00c000c4490011146a003810a100c550b1283e80d031541c6600d80300c400b691120344160046c8120005002c108898041000802c0750010f50b5140e01d035507030f9a42821500107042e9280c00700c00d0007540000101c0411068960703408205004040f6001002c04900d400f660041e101c80100c960b1615400c08111241805801c2203913000c0b81da0300d41d000b034581c0000c0d440704c4d40c02106000c8240c0f038003d05602c80c1d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 543981142 1250 543979892 543979921
    0x507080c07110d14251223010b09040303050a23040b151c06050708010509130206090d0501200a050a080a06080a03170a110a03021b070f051206010806010509 69
    0x2d45a41a211424000e00c1c0c4802125641c54031451841191817000c00d58083c1503410710040399120b0581c4280509081640c850a00c2c900c0f50183c02d5900c40ea404000c0c0d44401414500036882074401040600b440350f81d4a00750390011004820045e201c4851001d03d0020360802c94000d9040404207886444014100d6125081611602d40012140301c2e5940c4003060211805c1115016010802480e100c07200304075044942842039580c01811040803440c040c0420805090f001d100902d03451a000c9084007144560010b00c8041d03940e07940d50b00c10b440000d01c1411110003850810f0107002d282110921000d040ca018031100842004107040000d01d42000e0355200d1710181c09403070110744401440b8540280690a00c804074804100da110104055400c9401000c0d000d66000075410f0506039089422802500003030007580152000110020b00d080d400d1240341d002e08014204542c4290400c000d2065080303840d0603440f86913000c00010041143e0209030103040d61030865050300f00c0d0f16880800880c40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 543982392 1250 543981142 543981173
    0x210e09060111190b0c13061214010b19030b0918010b06030c03040c0e010602030d0207060216060506030c010e060301090c110304080c040e0a11190905010305010507080c07110d 77
    0x52160a0300311815100b0f03420b50042031031241000030000c1c0d881013038000305402007900311444400146e0f42030080038014860014141c14107c400110210134035404480031340280d000b01041400000d240d082e469121300e007c1551100d500b07042c0301e840b40e02004102061001000f14000f0001420000c40d540000e401020007180002c0801d6220f0605600ca207520794800e44084440351280100014007860404105041343c905802a5007400c10032004900a58084001140c80a42c01c20041c944150320b1107458030100d000d8000007800389050001e0520304802e042d0820306222030201c0e5994680e0318401100e040d0341d4040400b240c8000d101c201980c0c8c1d4259440100c05a010104021501c6c51000410b0542180700710b030b041c400c1c240441d030040c0d26481100c8000c0c0108900030803440c628280040c2e800c46003241c0500c03001e8034958903125881242c00030b0304100c4a99440d5414401460750160589400c88081c20000d441d006240c0d07504004003500640413070190503404021400e104099500820f81c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 543983642 1250 543982392 543982427
    0x3130b150901090f0e060f161b030c03090906030c1502071802030405010c110a170d0e03040e1b0423090109090b0a1a040506030115030f210e090601 65
    0x1656142c6103500c02a01c11071a859641d54689200001c0304840002d1b00c1d4001c98541d03e0310389941d100c1d03c2007006a0700f0762907039407002c0c0040380840101c41ca04100300f40c42024002e03501d175501c106092030000c0c920b40742070344900c0c0a9410a00c041c000305417400880c00849581e4410300040c071007444c3d02607003084116480000784a40c00a000582d0100c0ca030000c52040388520002c12860365105401e4400c145040742c80c054981c4242c0c0410000789103111110000083c84454070f00301402c0d1015041902c4180c1c2d02c6107081c0e00080b03020003925a0032072074680c11003030f48031244200c1c0c0744442004103140694400e07203c00440e80c0302c4141c136041d0b052010101c000406001da001e25078580c005400031b401622070440d1032440c28800a0400500b91207403000e214010a4100003045101c020400542409455076605550b45c1c0408499940000d10100086124817080052403c2078207082c1e500d8103c0078500c40c1c45008900c440209681e1001490080107030803181c0c20b50980381c010040b2201c6002414440e0b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 543984892 1250 543983642 543983659
    0x7053102070f060b0306040f0f0303090212010923030a26040c060e09060604060f0905040c0906020d030e06040602070317070e0f0102031e0703020f01140114040203130b15 75
    0x1e11200340300d000070407400381c3c4003400600314040915560320170489010304440611500400081e100c80f00c1103284501a00e0003080c844007580009450103480303100541f440c0c1d5124100c504112034525601540c41600e511104180c203100d035007684a104180740b6604210400541c040d0410340203045401c138405403910802c3c14503180c0b03022030700c12a01d80126004140650440c850710301d000d8030341c148520009484281080d1500300140d80503500b08210f0f0003841340da000003042980b10351081c8042c0110079901c541d140d40c0b42034400781c10180d41003a00c804150401e84212a4040d00051054201c1d500080c01a504c010b141003c5440526007403078004c1c0c000f06002030100c059880034024440da1421030780f0081600700a0010380e6644103244d8101064003886000e102103c1100f0007400c4c10038080c1c01580c00c66415a106c46c0e007100e84540c42c5076145044180140980040410b20f1407805000750340442c6075041240031004074400d03c10000b489091150700050740c140c0030520b082e25104002d0910072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 543986142 1250 543984892 543984907
    0xa0e070e0405011e1820030312041b150f050913060905010f05090c07021f1710081c140d06210804060f032003160207053102 55
    0x103000e00003d0742c0400c0745a0a004a200d2001d00a102e80001c08401510510500f403a5564030644441c0b00d0034007201000c21b08034546886e4030140020300d482c2c0c031081e580e02070919107440d184442507440c6141140c54005100140401760201c0b039400461411404e041d0100320711904102d0303441c815014440e410000c020850040070269401120568000000522007681c0b60914004c000c460fa1107030310f038018000404110340440b02c2d0001c000043c00a0815060403464052031071249410020900000b015030650440e444505551581c0000c0139006e031000184c41c01d652682d80349040074a84051010302203403014424010b4900d4460120074141070b80d115800114403000034141d0380300300d00b080450b081c01c4001c442084d03c00c42003581c0e8000c030398606107402d0280840b0542403c3c0c03d2841031603941d00d00c03200100d00b5046071200c00e045001d009030380c0c1c1c5001c0c4201d02000c2903c0d403002003950702001042c842607440e10b0b04001603182c0443d048160b0801d0b101d940307070b034141c02c1648000014030004444 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 543987392 1250 543986142 543986153
    0x712060509060a05060d08074e0905012106080f0f19031b0503130602010c020703030815130c08070212030106080103061a1f020d020a0b0a0e070e04 65
    0x10321038104007041d5400c50741c0f009015000d4a07801c0b6030f40383d40042d0200c07940d00001c0e84000a032540c6405200503e00c52004d407910901418411100803800240346440c5a00e1000d00c041c8000391002002e01da6005400103c5c00500f40444d41d02440d03040c0051211550076004081e440d6000700800c0c46024810340d9520080307184c5400c0110030049440c0203a040040465500280f403c15081c43e88209a02e415005d482c111282c510b110301080070b120003021f0b45004031790208050000d1000c402400035001d4030707000020b4211403c103080142950411a400c001080c0c12450a5901440b10804d1480100c0c2e00350020300405641c110620941c2e1a0030070740c0591070b512010081c4200700b07a4080b00e16446102c2000300d001c1c0000d205040c00502c4100050000a45c1a00121182d24490745000704514071500055003400c1d004ca08004019184408640950350411007400d0300341c0140040c1210810300e4039040305010b801070a2072815a145c2c0368400d0886810850360000b01140f1180d10001e0a251808 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 543988642 1250 543987392 543987401
    0x2121008010b010503090d05030c040f0803191107151101050a1b142520010305062d121b0411040819080c07120501050702010209030604080903071206 66
    0x4203800d030340ca401c0024480354092022a03000e006070300d00400c40d4003150309007200e2580c401005460740210a000000341ca0749150605000703440c100000d1901c030881c8410140610624080100402505440018423141c020490000b900d0f10b85000307140c580d618070019144190308840744200341d07117003800300140e0314095485103102d1100328182e80c104081808040350352303101d510000303541c081c030130056030300b4003081401842d14000300308580044800b86525144008030800320320200c2461000c0a045031503a051003910390104048498810300814010000b016060400c600045a074030f0500540c156134402075112529034030501102d000301c1e0030000e6501c10540c0326101e94042c0d410101100b402400140540d401e80b10f044000702201041078600c0e68409446000694210700200100c4800540500865018007106555a44441c00610b8100d007140c200801ea281107910600c0554100d94022075000d4000703801c55161a2240d26481c0040c7c00c0454907800005c6041c19964040d041000f141c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 543989892 1250 543988642 543988649
    0x111c06030b01081c080709030f06021308072709050d110d0c0201080402060702040f05011419080a150608191e02010e27070e030d03060608011206021210 67
    0x200e010240e660f4440070ba80d101e00116510003110001d1040c090814400c1d080c0d550300c800340e03281c1290826038984504085841da5041950043d40000d00641c0c0c42d110f49070b8150092001d000200040761900000312550b0f02c0f080080c85180c8090f5581c2101c51040b43c0200d0300482d0020151026802c0d40e800250100c0020031000c6014080e0303e0301041c049015049402a207038040c1c4624007656510f03804c0104981c040b440480e88135030303141e000700b4004080f849114042c01c0c1860b0280d5568100c58200002c5018a0030f0a4201048142040c003c555000c0341603200342d6030086c1c0c072089641d401440c081c05051190483c495a1155444044401408241804101c0d0042005284000034004441084032070480c010b8040b8000000801c80c900741440c0c0c44140f480b44486144c0c41d010382c0100c000e4000001c0c0c035002c0003d04850001100c0745018841171654040b03d00b070800c0700310f15048015080040510442071021b15088010043c0301841d01114a92051071200324454500701c0008a42c8002500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 543991142 1250 543989892 543989903
    0xe1c0b010b0f030103030c06090606091508030f040603020a0207080f07050a150e100c02040504080705240a09020a08010f0e0606040c0e19080d0221030402060d111c0603 74
    0x100005295440071084911401c40c2e03040042c03550f829514103603815000018110380301952800c0410104100d48901000307441042004140c400b20f4665400900415400c662070b15002080614401c0340b0050442d01118498100545ca03003014420590401700e0316402001d0034041e4202a8141081c0814100280c3c0c00807210742e10b0340ba4030703954803402e05550300c01d01001040ca07550383c8850624110120300c50014440c42c0860300141d5a90200e0141c0c0d0003568104c1d0360a0001c41c02104014082c41000103404c03154100303030440180c0c2038020041c1301000e000869100c1c3d0319500d400c150b482e015543c40c0038010401c003d0194030b040c0110100100b10612002c800b80c081c02011840a00c6c00340640d013100e003c030340e80b40c409210b1441e00700700b10740c030207860901001030740d602e03000802c5ca40902c40074464030741b180c0250603c540d032861031082d410400100705080c41d104008200050b0703034074030a440440d400c540c40024843d0001031008118859682ca2204000c90741e10419618180f0390440016680306a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 543992392 1250 543991142 543991163
    0xf080306130209011205100801090804090c0c120806042d0c110c0418020a1701150302100815130608160b0417030403020924030708030406030c0e1c 65
    0x10307250880c080d800c501800611308120051107140c0076000180c02207250042000c0c141d03541d080681c04c40f140690100c900300d1000c82c082003036045d60b1081080c001918100380c0a1400e1540d100007050030640d825105000d0803d0119500d41c4640d40203e01c10404090214102d486035070300031030303071940c8070310119961404c140004040c6486544140040c0340044000c101c641c6007801040042d003502c0f0b04a903032100480c00310002503514000e01e03100174a50342f14825001ca1a0011860a4503541c141007079002100c07040400040c0c42d0070800c0d01d900400743c80e0100b001c0e05c6030955521403503005080c46a1101e054035407501d03540d01ca13910240403100c10400300e40c0d4040f5103000380951070b2202c2c8a4411103602c09c1c0001c000e100c0c0c2c104060426030006c801620b2a290701d03036001071001d0b0025104a86007000c405c0880b41080e100c8241958805d41c110003d01e4280e16020245650f80308501490040588907070040400900500c40c040710b400c8005d0500b4101355820803061580f10600c1f10503100c00202 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 543993642 1250 543992392 543992419
    0x6080105091b0d021813060f150c0b060409060c0e01020d0305010819050304090507170f060d06020a020a050625110d0e01301d070e10030f080306 64
    0x440084601c2da4540300390359418010f02c07850442c003e4001c82107090a8040040c0002080d40c2c03400003200c4103000140780004c1c25400c0912400003004560440f0300d281650062006076203400180e001c0307841e5480880d108041d03a503074010a01034108008014003040c1450151032005400140085020100381d0880346015203500044099943c02c1c031500d8901e41006460808894107101c11120107801201124502560f4140107403c507002122540c0000d0300a40450031241c8010b1245034000f0340742214016a802c1840c0041d98002c5e48040003000c081d80000c0b8400e1850007400740c1c10f50ba60300700050303410500d040081020030141010440000080c0c5034210000a0b01403040c8021071201c840c01000c0440c1c4220341500c1c0c4034030303501c00c131814840b8450142040c0d030300340c071040c03422440d09030503d4a07107102c0300382e1803001d455806020843c0007c00d40e03502d00d5444000541034040340e250501c00003050300c4070a580004655a900040d020041520317400d8140038003400194003518083e90158a0440f1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 543994892 1250 543993642 543993661
    0x60406090302062211060403080310260d1805040c051206010903030f12060506030412021b0d06020708070f050a1b060801030b15040c0c0218150d0305090a0608010509 73
    0x314052000030500411410400315082e40c1c1da1000305c02029008615098807078894032491b0b00221200e600d8143c0c03805090040990050304210000c0340303d2402c02c821a03503640e031140c44501010520b030400052800301c00c1001042040c0340c00500000e0020040c001c10802c00500c254070985090000300c0440020560951141a0110482c0c2c0c140e56100003031001d00c5011a80780c13003054492215240c5844021903540e4800000b5030007580b042c000302e808401c1d84130001c2d04106100800c82d6120f010500940c33890f44450201401350f9900c2800142c0e034144a2600c041c442c0500744c8050108007059a01008210b000201c0d44002d9000f00014080743d81000d4120701c0c001c0e0346010b040001083c02e00108000307240090407a80001503c00000c0101400b0b0000c28100c03040d50080d4400551480f5110042d424505161000c82140c0410242c0c5840c0000221110b11b5004021501841d401d0801c0811715108105031a01ca400c0201130800f40b9a030741d00006c3c00d0344401e0050703601c40c04901c80407404100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 543996142 1250 543994892 543994921
    0x30703180308071502040905280b0603010b071b061724060706140f0703060f03120507020a0e1603050c09030a0201030c2106080607230304020a0806040609030206 71
    0x298802e140629048030780e0b076180041d00f2240711034141c85800703020202e059806401042d00c10031403420705c0c13400b1004580540100403042c00c00c00710b009151550b0b104070b40d142d940c12207064400301006c1e0780d82c403c500c1ca0809006041091034500c0b0940c100e0313000c503806500900c50350f07070841998a01d080e5925034142d4618403034a01c0341c03629040e6212903110007a6083c0a07000e06880340c040d82001820741030513419502e03020005c49082d03010a010b4000c224030250948140002303451126030f15080c42c0d0955071401012000b00c0503c1003031080204510342107642d0b4241c03030b01c00781c68045035001c40750900b82491003080e42242000303c00f0905101c001180412a01c00b40c0d8852540200140300c6140c1d990010350044c07112050300d0003040000016000218028455084800068840014182c0c507101c4181d04240c4040c00e280c003041084c600c1d490100000c41ca6158841d25500700c8665030b074540d807001848880043d4001c0507140144000c2006210490384101407940c000d400b5162156a24407501a045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 543997392 1250 543996142 543996149
    0x40314070e04020f0a0905072f0c060c010209060414400204120515071107060807030f0905060411090606041701181211010c050306010e01031b0203070318 68
    0x282030756002601519199007508095200605840c400d6074032201804142c4100702c41031b9000c41c040c036400c10301d140180c00c0803d03a0400441d42d8003d400f40c01042c05500c4840d424101c41c428500482c1145541e0402c0d4111a2004001023042e40d07515503d0420f03018048004007010301c9812030a2200540d0380c501a002c3c15881d401168002c03185c81c0c0341d981c8903815051007603c07021461342070001048098140848040d003901480c01099404218100040c1814001b03142c48100004421380200c1e0010000f81d000c00d0f40d915040130271295071085402c80c010607089190440c01400e00f40c14030244800410083d0042e406004207040b6525100b05000301030030240c80890300300d030082000f0000040b002d07034101c1088204800101744080381d00e4419001c03965100341075400b00c0d958200f8041054118000c1d00460400074001e00030004003840180817408014442c070305220381c1440c0000168480e905c21960300311b5a2164801400003090000c2d81e035005032100f1800304100103100c66200d0710303210080046 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 543998642 1250 543997392 543997409
    0x609060f050103180b1e090705060a1d0303040306090519020604060509190b091003050403050702010e130c020105150105070b04021c0b01060c0605060d0b070503060111010e0304031407 81
    0x6003407426004500070070f4101001ea00e1104038140c0710b4000740e51000c0344e81c040c0c20303000c28044240310660307a100c19400000e40f0034500359101c42800c01264440b8010f5580c680c2450505030b000309203900c2840402c80c50074985079814040020040108001540b00000c02e0740940105e408420380304d011350a22040f100b00182d0310030000e00080009512807c010507a0240140040c0d0315240500488200608540c0210304030010109202c0450b0804624024000c0e10310b2405208c1800d080d240034141c2d100c0c000e0040d0402c0000b8040b07100986400d810540303a15040302c020040c8042011b0000e000b00001d440100e005258011070450b958442c50a4415031a00494448001d403616800c11041481c46a0320b940a10721551100f8045096040e520b8000c1007551140c0202e101c561422000710340300181500c1c4030384440b400071130104100344110303588043c590400301c2d607070789407440141c036500304a200340262582087c180462004010001e0310440c0e11800d52001e2000a2645041d01d504050065480c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 543999892 1250 543998642 543998669
    0x22e0305090c010e09090c0a08030c15130609081204030e1905131a0d0b01080c040608030702040902030c0a03050a0b0601030516030f0219020607110c0616020406050301051603060906 80
    0x25610b17000c84407a42001c1302100303c0c0c90300c0040401040724200356038015502500301041c0002c01d40024071050003402c4404050120501c1e0140381c8078504054200040c219541c0c6801c1c840801c01030200303c03080c0d07441d01d10041c061840c1620340181034001a11285001d50880300d4001ea10800c41c0c002c00040d47c400400d1205840c5100f104030000b011410680c00c0080004180d051040d21411507e0411303500400180b03809604201c1035910b0b10324014030b904d000320300c0d141382044400320100c05d1790262513040350082103021450002030300d00510424099841070344e2502c008108640003454440d03ca00c0380402c03140c1d076503400740154212041114103c103c5080815000c00061196002c040b40c5c030b02891005003401c5c440070841c1c41c010000380300000035902c00801d00440a810141440b22103104e4002004000c0755000030980b9402066132980064684200070011951103400c840090000540208071510f080c0c00d454221000f05260380010070318050000c40e21030110b0281d0800d44810145182 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 544001142 1250 543999892 543999917
    0xd141303051623010608030a0c0b090a1e1104020306010e011b08070602042102030d12020d051017060106020a120c1a060a060914010507022e0305090c01 67
    0x841941c462002d05110340c2d0007925140c00a94000101000310302e03950005000000a00b0301c46007140c0d002d03041407460f940244070b0700810580c04032001820f03175800340a80545443e250b011a00e000c2031484010b2a000d10f1541e10f500ca00207100390b5000c0540500208625100400180412032200ba1529400114844030180e00c5501643d00354006043d04004004401e441780c03100c20b524ac0010354102c0c2c4490300002d00300035400c0a440c0c403a03c3c1f00d03103da01020300d007442503001940c0c90078000030940502007120003a0346402c229605a92001d600c8110900151500701d5003502c000b1034a0003a4008410b5080001d10342c0500026507505890494009224129850f01d60713031140d60400c103002d4204070303108004030006604e60300030084c0500c0048031801c3e03c3c10200100800d071203294215030100040b01000304100310828080b402e030f200e070038240f45540d81c0707950010401d0348010078240072010351590140c901d1380448100407102c034400c1c4d0b0780030055a200c1e4a03d41d501c035200c039503580740004d04004405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 544002392 1250 544001142 544001147
    0x60509060d03140a0c0c270510030c0801140705030108150a090807030305060a05060f0412110607120329090601121103100807180f1509020d141303 65
    0x458100d01900306014401030710001000b10781c2c401c684030300029440c03401001c05c00014501640c09081d2010981f10002c007081c039000540c5c0f101c3d09420084a0311100450203800f20f14100001842c0c001da60249800c2d102d6805c64081c2007007140a0440e1561100000c100718400c8050f00e0584040c08050301e01500004040401007101800da503844682e00c480000004034070400034801d40d4481e4030041036030719001003002840c00c0d82e6882640660002c1142c503080ca09018119019a4003401d00441d064140e414103020a181d600406500440e002440b0303000c0c083e01489400540c84950344c280040c410540c841580d41981c10f51440f000450100c84070003a00d002c0004684c440d1041c907000b0076400c40e1601000c03c3c1c85d1007400303a03c1c1540d00042072000d12296010203c0c00741c8407031030041140c40c1c9031140e61091640502d00c8142d00b0f40d0743d12301c084010f60040c0c22014402e99030025250b10a915001004000d501520090394003030300d03101240540a0704103032340c2441407180144145050405807000e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 544003642 1250 544002392 544002409
    0x1060e0a12020609090f090f0d05070f0c080303011e0803090f040207020f060f0a0e0d030e010503070504150e0310140601030f0603050a050303071d0901061110110d0b0406050906 78
    0x480c3d102c2024003607444584c0758880d0991240c043c080c00790b1500c0c140200103074244602841c1e00b00840c2c11000d40c07030841c65006012111042e50000345440c8208441c02c00301041c0005807c8052139000020000610040112940361300705600140034042039503c3c9065552480380e00107546c1c00c25091078190400d4501a4042d0402034005031440d0080a0700c0d100003031650f0700004010315260f402066a001044d0301034503c68004400b50780000701c0d0f080b1602d004d0000801c038411107040140c004001084144101c0c00d580040a0300408500545800c61000e019900414107941c0648151364280700724024a0040184000086804820507220580110080c080341d084560395261980d17000000110708010310400705000310095505c1e400c00480060011508210700c8040385142c0801c11081d40d070f02070301d80c1c0c1140c0c000d0404d0780020751403508003410041e041340d107207282501e07140400f105a0036440080002424042007001f0845060080000325a0107018071500f0060321000180c460428189 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 544004892 1250 544003642 544003679
    0x412050901030f1d010b09010308040e04020303070c080d0e030a03120c0207030c080102070204140108030f0913050709060909060b1b0313060e03060a0c12200408011401060e0a 77
    0x4000c1100901803000d0300c1a200c010407070201210b250b03151802201303400c4c0318030314040c402100c030400c4c00d500d1612000d00381d001d50300440c00c00e0007542022400b1036404000b1903002590020f141c40380d20707580e4040c031038840c03008008120202d81c42d0482c880300c42c175000c60b02401259158640da003800308240819801030403102404825881780750404404548404c20f80c6d0010304403040003680d501e0142c8140700a8609001c0702d6003d81a401d001401440c0d40132050310044075000c0c01031901e980c5000d0014003101c1c44140c54412040c50541030240c00c1c1d0f400040741d010b480c6e1716100c034501035039a60085800ca49440c803d08004507018040d0030107818035000801183c1c610700c1e003100d08064060711000350480c9242d00c101c0201c1e8a844c60171001d400c0502500c1c1d130000400400b000007041c9014003070005290400311581d120364071028490401c0107d1208100150144881900d0b81d44030000701d4000c0c05140c007801258589840000f54440c03146450344148100500a0591076241100d803083c9240c200741c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 544006142 1250 544004892 544004897
    0x1804110904200f0406080f010c020313062a050307060c0e0d030c05070f06050d0b0402271807020a02010305011202030a120225031e03140a020c030102031f0e0412050901 74
    0x1076400710291313142e008a20242c180f10340a00a41c206d03144c034082c00c45619241550a40d0014400c2d01c03e4110120050402c8542034149604000700191a00403c10074043c20144880c0c85c0c42094018041c000000c0c00200740300d01010458076080d05016510904400ca065034080e030b11003401c1001074426600c1d02c0c542c901c07400c00c6a07046604c608080b5840d02050300a10001140414800e02c00c1e071041c055010072000c10358045203080750380036003424641c40d500d010084102d030b04401d52000b80c554040c0c00c6c205240d00c03690040c40e820709900081d100c00d080b80050303002900784000401c001e021910000d540950043c01400001302e0740c0d548444010b82c4610440a43c000d035009410440030909001502000e4030740e50011642c194074107050b041507451049400d40b000014a2000a60441200c1441c40359081500d911128402422840c0441d040e46a540650021050110780601c1e000c40c48004e5811035042a489511500b01e000008002c03100a4414442ea800307001800340600018041e201040c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 544007392 1250 544006142 544006159
    0x130c020c030106080c0a09060303050f0a0e03060a0f060803160b07180b0306120c090411060c0106030b011a0c0316030306080609100515010509190302180411090420 72
    0x40c00020300311401d40d0310100c2c0c03039040290905500d142624448000d402c03080410071800c3d045031402816406100c4107c0f446103000a190381c00603005003413124a804005045400350325042c41544041c01e0714074444a00300e82448004100d006003c010354070080e902020780c0000e40803c2c0c644110b6002e0281109050210f80c0d40c0000e101511450b801000d880e20311a229520308090f000e1100d03078001c0340042249a045000040c5180e591401c038035030010740084841180c0201840007603800e1084803502070856281140000800088801c800c0c1201c5808280f01580140e403e6603080c18402c403000401e0540080122071104000004c0640540703000389000a01d858442c028180380000c107544103003080c2d00c8000301050021881c0581c40c0d100118008880312501c0c1d140000c0d0240c000c0c000102d10400300080e44015003400350160300002c40d001404086440c1d0400c0c2d801020074415a401d68004640340100c035242d040c0303042d405008d15030092500d1600c00c402070300c1741500741448060301c1d0300c407000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 544008642 1250 544007392 544007413
    0xd020d02091002030a08060a03031d030f10050103060b03011e09061b0c02032802091e010b04030b090604350f0c0715170a02070503040e06100e130c02 66
    0x8482e000680306400e80c00540d0b480d00401c5000d4400a030080c02d040c420f13000c0304800c1c40000d6103c9440040c200040d0920519501203100081c180030765580351180620500c1c0c3c0e0034060740c9041d007140d412280104400c0082000070710525080c3c0f084840820305054004814001c04002580461510b0740039807030014200d6000040501d10b0084502110006200c0c0080c01007580303424440b02007614860380201000c1c091581e00341c52584091a030103403144201d00c000950291000081d1300d541c040c0c1c000d2150391503031a0044019990094001603c0300680e5600088500400280450060f07400c13106003022441d1494861041004607500c1b90380605c2a104208c0b4600e4004014220703043c080a4100d4917043c6142d5990f2615060b58000c80e160a0f0601c8801240ca41240150880c02c038224088409542c0d0940a5006440b4009004015110000b40014522000d035a040d014030340032507500c2d44610f880d80d0211090711401c004140d1050303e80168810b04041540854006038550041d642203502c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 544009892 1250 544008642 544008649
    0x9010e0102040311090f16031107050d0c290612010b0405151306030206030402091b07050307030806030f0718140f01090c1107061d03030304062406050d020d0209 71
    0x195004980d0480040c525050318a09122031541c4400c0140d0603101e0340c82d2914480207c2c2441d412003c09040d681c1d1700218580232414100d075a8035030400d08584150301c2d03100300105036054204043d180383d5074801c82690002c10f4070049076151400082c0300b446035241c0c082003040c03c81d00c000e0ba071540c940d40c54400300d046450368040c8174403400c401c803418031098060f14103012800c8036060560522500c0c2c0001440141d4440d0240c07900590103036540c4016035540ea07c142914048044244ca040350046001c008000e00040140320840c443d0742c4402c5240ca030b02d814503603035100200d41e05d452904042d4041c00f420200461361140e0680181000c2400701c414030350b410141c1000d6801c5a02c03000a60f00510a0000300d008100103141a4a4550790080c440b000c11034407210f160203074030108609961a6406410516803900d800800101582c0e41c0303041c1440c007103000308041720300e040003c00390100ea100b2040c0f480800004403a403a40b40ca51030042c0b0001080c00075484100343d8000e103a4248001c1c1c16584 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 544011142 1250 544009892 544009897
    0xf07121101110115060f0c03120f0b09090604020a0e040b1816091b0207030b0f3c01140a1a130e010315050c040b07060e010c0903030909060b030f09010e0102 69
    0x2680820348100c11404c2200042400d2902c0c41c514040c0140c843c0040d0000b41c1c4940d1040800300710300d03c0010007522021059000e2f2000c41d0f1400d5210100c0d1090240d1008081416401184211500c04006584d46d80030a090340c011035002d0142103542d0b000403040b0ba041c0e050071038013010b047e058400d200c41c1c03070b44055032143c0141c00620900ba5078820304482d20a0784407564001020a00007410348034034542ea00b10551400400e825004090394000c1600b280d5181040300000e4200c50a40600e040302c0135a02c0603204075008038480c0510070b440000341220000b07403214190300000d40706c0f0000c541400f40c00244803c480c2200d003058481040700040d13182e003403c01040540b51003141c52107a540345003450092510340e0704440140d640b4002c1441441c3c4d4251702282d00300c902e40030381961207030045e0401c84002e00f01501d0003109542055800780032a1703804a65981503911907100c030b00c1c1a0784c44860710310407900c1c2d83c010400454400c00100b1240320480d03e1465100c51139900204a400b0500074650982c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 544012392 1250 544011142 544011161
    0x6030c0f12340b030912070501202101061b0f0803010305060906010918020d020303090a03050d0f170a0905030d09080414190b1c090b090f071211011101 67
    0x240581203803038150070400b80a40c010728400c07282509605040071510349800a120410003030950000301b01781081020340101c00c102480c5050b21002d810b00035020f070f460340e0140d00500401c1c0b5985141120924040500c107058604554414408500390940403070180c803000c0c07007928201c00004100c0c1c00965008021070180d4411805042c150500d05003641c913162040c1c0100f00d1241c14141604280303a0200d0040850980441da40828081d150002c00d0035480b0b5803482c44d4000c940781001005000300010070700a41401c503680c01c1c41301a40008100d803005800303802142c40301d50b4607002c55644075442e000b4815260241040d46d141c28045e044c90011600f00e19812181d501d4042030401441c405403440511034541a1030b01500c030800c080c200e0000d040030f4002c030b0311200300100e5074584d1101864404242d012240b02d04111403036160070001c0d40c01c503040325524024803840c1c0c80c0c00e049910102d00c0c0411144040c3c07255462030890750310359401f51281000e85041011031402c62110381d0f024041d0b0404ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 544013642 1250 544012392 544012453
    0x206102c1324050105150d0c030204170703030f0306030308150a0e0708070e0108010b120907080a030809070f08070b030601020a080d140601021609050604090b0103120806030c0f12 79
    0x41c2c580049030b25007030701c105901c614410840c6081000580c501c0c407048031000c0300803403000100d0498030402a00280203a8002618140c2c034569040c000c01d41c0000d00b1400d03a806074031410076400d03600d1340c11410303640140002000031b8a064080740c1843d4001424900ca080004c041061098075400c44181c41c5108a0f601d07000240d4090034402140e40044210440348828030300892558145090f4840d28814403001801c030075082e10004118420605c00c07000070b41104003d4680101050400400c1602c0603a18849207000d9541c0004440007004010b8040b40d031043c000c0c0136442d107060044421500000d10305810f43c021126120006154000206008c0d44078000c0021441d145034104c3c140c4000080c42e190565100ba0b44030000014000811402c4075100000800d040da51940882c0203031401000041030070304401c0011040021200346a40c1150341d0342d85940c495642c2c0410103540740080280700b50807908a2540342c980f0304183c81021442d0044100b01e4101c3c00c603010102c1d00300c044400d1000b40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 544014892 1250 544013642 544013693
    0x9030605090c06070b0711030316021c1b0507050d0b090d0807091e0b130810020703080705091804150b01030e0c240a0206102c13 57
    0x8018191051540011410004009115621022880510821001811502c07950b00010344c0c440c45028441401c00c4454196030f00d906184114001c803540c038001c0c000150144c0c00c02100046152a40c0f46407000b0190703a003003840d10807800c1c501010750b225034052301c03640540440446d0a46806041c9808180704502e2600940b80407080b480c20405010201c000300556481406a2564003882c800241d03958003905806180c82c0307030040c80213a149a802101022800309030310302e40c80c0800d5184c0049900c42400c1d030300b00d0208a002d04c13049124080d00100824030308004588002e1003580a0014114041c202c1001010012003040d60304404079800c41e0780703080040f180185070505000c0d00304000001c0c2000c0c88544850110740e900c0b241d52082843c082e205d407520103e044040304503081d01039a47c1c3d0059640e0ba1004442c0251907072801c6a0411420100100004818141d40361a0104950304d450b00070b11141050442d500b4050084d03d00600d40170b940f40d41c100498048188040c84044071018101d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 544016142 1250 544014892 544014899
    0xd030302071e0f0b161d13050f090c09010612150b1804241202010c02190305150f16050904020409020403140a0302102a0c1703070c29040309 62
    0x824440d8014030400f00e0300610300d0340960280d0031004038043c025818032018500c031146e0000c1000c004803e09000503042c10b04090101100c4c42c0000705014881304419103a8002e40102484401a03084c802d075800a1201d80403c140100103a02c10369a41c0601c0e17100c61196655903c180c241c0350064482c4100441698038030000901d003900ca0030030442c0150724400101c00c8641c05203004600648610491440b404504e2011603120340c000100f0706500502c102c40c00103115001400a00c0a40012181e92003403003a0400c04540c00c03041c0900c40d0841c03000346040c2e5500d2410000c03407201008000b00038440709001c0c9103c1e60b503c41c000352000e041e007800300585452850412001010012031610f445420100100340403942c0800c80d10120f101c122004500b40031441840d02c40c0019132010305140d01803081c0031080103035004c0c040301001c0c0d0152642c2c190300da00c86460074005100568a40c1c010408070058207000031810840082c4261003010150030381e44202501248031001203c0440000340741b1075003403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 544017392 1250 544016142 544016153
    0x103140a0218010e0f090c040e012402120304030e0f0301290616021014030a05010806070207060f2f0105071409060307030e010f0e010b030705040b0d030302071e0f 72
    0x20390b08440074039140240d0b0341c0c00b80100e411241100f680030701607000f16001520034581603007181c004102c058041d500c55a503a1100017048518024503c41b82645140c09841003440000c80700e03006a0001030301491a01d07030350b40c26610030f85a002501d800c00050718a41c0c24a81d028400c611101c40c0e0240300744805c82c4103411740040389071115011407040d0401e104841015207407210303101000794151410300c24011412010344001101110784030403084004100a0300c4213040d00034604846081d0b04407070242e2140304040c0c1c4c40f5801c0d0700070200091201c2c1650710a0f43d1082c243d06083c00c1808554030060303c0706a250300030705010020404420381d1078405001c2ca555000e88244460b81c00700c8a09400c00307a11400003000c83c031010700b000c403c0640341c081c104074070007081d8002d4604500c240c0303080103001c5912001901138180c0d640564800c0c06000000540d9042c9400350500010004006240f00300c1c04c1d03a4281d0080d000342d42e0079200380c5406c6500ca54000203805003050340704e01a031012903483e402450711 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 544018642 1250 544017392 544017427
    0xc12030306040e0a0b070509240a030507051c020d290a080a1106070c120f2f040f02070506040b1b09013606050d0c0c0b0a0203060103140a02 62
    0x4140e804100e0318000700c2c040d0b0850f550041b415141480e622110714000409600260700300c1d907140c081d03101507540c44000c2c00300103049501290f10140b0003507880710025111401580710150065441000c1008284441d80c000c00c403104001e600000c5d409102202006103100000070031031440e201da9030900661030701e914072800900304000141016407003940c440c1d0000c0c41c1840d00c00e002e00004107148040040007407070306000e8062003601c0032103100e05042403c0c142c0302c42e41c0300707948411050008100740d01c100c8401110107100e14000001c080c0b0158240710051a41d4640101d80325828001d52001a105001080c0124060002c203030440c20004017001e521641400a102d01c207400b04170788900c0e40d81244c4044401c04074082c04000602ca6512610407000200201c103010480c1130b4800319042e600540a41126520389008201803503004409643c800501d8030082c20300540c11000030308004c05500215808071043c580030484101d039003001e03016540182c424056041d004581d40409103148442d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 544019892 1250 544018642 544018661
    0x8030702030106140a090b01050f0c010518010213260102070b011409040f030c03180f08010b03070501140d1401031a060411030a0f0e0a0606033305090c1203030604 72
    0x1100400d5413004000504c00201449042c07203558541200800c50ba00800590328040b0003c4429680c1d44d0a000d4042c5c0200300444011a6002e0303020303001420464144290385030140c071040ea401070345081a01d030710303201d19001c0600b03032403545408814000d40f407007030002e4185e184c840c4662904550400200305031060000d020a80504c50003020800030800e05003031100b040e0b130035013041c029405883c01d0440c0c2c041818607020b5242d0b108441c0000d42405480c1e1014200c1e8407180081002c403056508040d00c405880c840c2c2400501502210f0b160380401c04010203071f0201e14840043d00000c04c04110340c0404090348192a408000c0711241008040305207400d0344017004407410003c010b4550400d040f940000b61540c586180c0e2a07070b49007000c0030241d012030341e100da40300101c410800251078002c024180d1404211a03003e41090340035032284181c8000c030070740c1001c5c3c156401030f03910306011003005190081000d185440b4020b41010700382c5510700f6413126104043c1c040d5659282c111306201c10b0354090740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 544021142 1250 544019892 544019909
    0x1709030d05032a0d060303090515130905100e040317060904150c030f09150606050309060105010c020d02040f06090e070b1213080a05030a0b0a030203032d0408030702030106 76
    0x41000c088080e0742249048801181c80002e004a88514081c0358044d035074640c0440b6292220100505402050030783c2101d8040342ea4604001d01c8490409142c000c07001001c81d60304810b5014050005550041d5510a101d5444903500d40c2da200010a00d07580140c0d0150082200c10390f41c18070003160218501c1c0d004070191060646410b00390348244c4845400a0814011a81d400503c213650b2b00c2a0003521a01045090500c28941142040d130b05481381c1700e0307245001c42c3c9800740001d403250190007980e01c650103d030050f194983c6000700549840c0d048100890f4484078480403000140e032588940c18142d43c1c3d07084001001824020060f044078500d65205c0695446544100002d121010440c2ca1200d090004440140c481417211030105d10300200c0100551400f05841c001c01d507105028600c245a5040d05200040c0010107110840300b1602019401d034000300440400035882c003149035032110400307049603203036480c00f108039085401c0b503000070b00c180c0c0000410303405519017400b42ca005072140742d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 544022392 1250 544021142 544021147
    0xa08010918030f090504090c0509060907091e1a09010e03030f1b030c010203010617070309080a03020304110901090b0316141003200415080c0f09030a1709030d05 71
    0x1010841c14080c1426401410007104400b4641c8240c4607008078001060040c2003406103010300d180045409406000700350052100c6c0c00010f2040c03038900d084a000d450140c8401030601d080800702d03c1100c0d16804c917141d49400310031000505202c1710040004c1c00c0c0d00f0940d516100d0b0034050006204522404142d4484e034814008d180383c03040d03960111108441c00c2c04000d09040c42d9004410300f180100f00c1c030020349520100c00003442c0c0b50001c42071480446614a25142c603559640b003074003102c10060018212003001d0110540e52406540110b40090042e015030442178600c1000600300b04090b0040c200441d1960040941800e080207842004003600c2181d501039402c3c042d0305a000c0c90424452486401c84112b00b0701024040d41c01142d507042800350200d071980d614660540316901c107100d01080e1050a4802c07001462160130114040e0702d201620910300046018041c0503500140c0c80d042e4903000301d14000300091b524144081100d0304040c0709949801d1500308140c1800308070800c0d042804402c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 544023642 1250 544022392 544022411
    0x402090415020903030a11151b070c081903110115031205070b100503150f0703110d05070306150c03020d031d03030f01060207060815100c150e07091505090c130b0a080109 75
    0x9440c0021840d03901d8140d271a458140c5414842c1c0c540401d5403005203240103070015206960b14402181420501036126623058070000c01c2c0031400c80c1da000c40c0c48801c00c0c8060205000241400843c86000d410a00d4510708000c1e19449501c1981000d0301e601c03030f0b8040340300000c0100e818148400040c151520700c0000003481c0409001c2040540102101c00b00340c1e41d021408072040142007074940d029100082003180d0f180a0030050000c0c102c0340526803503031100040502c18107224041c1c034101d007541a0301604030680c0d50f000680140c48141203881c0d02c10040c02c000b4210140070005140300748404250312180d94548103000c0e007042515000441080500340400802030341d01542c0020540040d80c1e81d180d40f02040b2070850f4040d801e40c400914500307116241c1c040c510500c3c0c11150072441c40d041901c104969800c0318404903800a080d120407915840010040c91510500717155006042c0b0000614082042d8007070030040030241c1084000c00b8009c6000007005034884103190140072100340801ca10b002e1b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 544024892 1250 544023642 544023661
    0xf02040501021b0102010912080702010f0903050d090c18050a0e0601030b281a0406080304230301090203150f01140108160c050d02031206090402090415020903030a1115 74
    0x1800e143c20311580c0c241404508159100354410301c0e0107a00144030194417001144003d00d40c00095035080019800c0c50b690311600c85051241c660080e40c0754a0741072415540311007100142c001a0000e441c00d401561002865400c0034403081441c8080e020001201c1c541007a104084a06000c40142698400c900500000b01c0c181081a00110704184c0c09802400b081800911480000300740c030045c5040c00074018181c500c11001245610b0b04583c140f041b05e4070b070380d0560f5490059108004295090b4008040242c079600142810590050000700d1490541c3d0040b034034080821001c04030300d100d28020414802d0610b40b56502600310400320010810000b03000800c211006040c00c00111862141c0d094080e0140202e540c1080e40007040d9440f49016440180d100e400002c00e4a41c000102c1000401519155048902c81ca6004007a00300e036454507114510342c1e224200700003081a90030080710b07401b44d4040020b464440c2c141c2c1e85241c1d204898034403441c03c0158406041a4545c241d0043c011441c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 544026142 1250 544024892 544024903
    0x102120403050705280201110f031905130b03180c01020c0108130209070201020c0c030109020303040312020709111908090a0b0903210f011d01050d1121010f0204050102 74
    0x7901842d00356103640b02800c1560404078817800a0314252103a01c4014151803001011400343c6000340ca0b81e100e06c0049480c401e171220680300000d15190800c0040b00c0f542d151000030004024014545141031840b54107a102c0300d0000fa400404540c0da020040245480f12914955228100032010305684000f180001c1e591303c4052002c0350511414000140120040c5129010026001011005241010380700603000350b10980200c4824040c0c85402c0d6600e0805009080421394040d000750f00e0f207491902c50080c15806001948118040e000b800105c50005015056841b18000c10b00c55490326a04141582e0701041030240051002290802000e204089141d04102da004410590729540341e01c074444c194800c20452500200c60320030240c0c511010441554801e414043c82c070780090740c80b500c2d40507031654287d001c0030100501b40010701c8103051500c04420340d20301c1800c1c440200d0040c3e00000d07610064603a8484c0d00701040001d144204002401051868840003404504e030504000000303443c0e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 544027392 1250 544026142 544026151
    0x706020a0f0218070305060f04060308030a1116050d0305062205060a0b0c010b0a0b07121409060d0c090b0415051b0106060c03080108150609040f0b070c020111010212 73
    0x60010740505030640d10340419641c2c001c0a94035002d0020b1401e0030f8050010501079a5513030003090300c4200b4000034102031055209890300320303c90f1401c6a071040c04600150002070450401c1c0701c405c0c4101d121050002155403440780c400d4020380b404007601c150044c201e400080055105844411444c0d95510780c4069020030a61346900102c0d070b0384c0c0c0b00700105402e40c5481d07010010405c030028403090ba0080c10360000c1030107001140c1c2e40301c030580d032640c0c190114020840e016002c0e03555038080080440c06008008465160320080b28205041e180000e44103030400301c100110580c44601c124100e40e40020803034040d001c107040b01b03424141807001c5e80070101b001c0d4441e1800c4c050002140b61108101000c030340c0240140d000207000c0a80c032148018038441720383c5e8040f808150241d00224403160081415040405000018041031740c0b04001c108002c0300203001542e03200c5544d12914085141c0042d418030501180e1a01a0030440b03c0c0f0004003040d05003c0310f0340041e403050000c0d18052000c41e080e40d411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 544028642 1250 544027392 544027403
    0x30c0c031d0603071206140306060d1403040303030c110d14090d080304050a020307060e09270703080408070501031107020607020622050909060403020616032403140706020a 76
    0x4295141e1096041601d503500075a81c04907011003007204441e48800d001c2280c00c150031041c07100994540c11810442d684000160741604100c0000741c080c1080c0751070044080c043c6c00a4280340c008080044d0444d809600281c00182c1c8408400204980101100e0700303a0840c0c900520706000701c0e6100070304040c100600ca101410001070400c0c0c1d86d66610070800b1000c1d400c00a20b51741c0c1e050070326001d561101c9500080b40203000c0e00d20300182d810f0140c0e60800100e007000c0d000381415905c4006015000c2400500100c481341a511341013200002040300354003841c07088107859074070790130b150a0f1890320025a0100341010304110800c800700070058244e540f801c1c0e05031800b5440d03010500c00101c050240303803a201ca42d52481c00507620311008000034081155000da0f0b00c42d08903110301c004161511030456003d0090b0f4030002c0464103030b24a495010350406130924000800890850780344002a60501040c80300056200c414400c1c041c0800b8000040c41c213400082c00010700d04100a9210880c50801500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 544029892 1250 544028642 544028657
    0x90601090303030c0e030f03071e0f06051b0a02160f0b0d18140c0f04050f0f19020409090c080a230a0c030308101a09040203090c030a0f12030c0c03 65
    0x14914000c107145c2461030300040039076004014501e64581d99400070350f0241e59070303d640d00488407405401c407941003415030044208500812551103420180a014004804100c2c100c10100b450700d05800c05042d56880c0740e80500000b681c0203200a44000058000d12400b2041040c200b00f0f00709164211060340b0114003000c14074100444400021024110b07015016514686402600600101e2500960102100d40e40c00301006c540601c81140d0040b5550009507484002140e0900008002240d00a078508501104045000602410b0381c020b0b51180c1d40c0c45031a100910108508820754101a0003c20300602010809450b07003800030f5101100100f0051035185c5146119074180035500c0c1540c0c1240d880c451080d0b0b01d1500818401d022540301818020880020980303c507051b44107591307481c002056500382850442008025440030f09803034811712070a903009003980c40a000341030f9104c0c05030b000752603640c03003908107a00801c0210f8902010185804407031181c882c2c0251108800f650580340410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 544031142 1250 544029892 544029911
    0xe0d0e010e0f100503010e0a05040c182a02070e040b0f072705130b2202090a030b06090702061e0711161a070c0605090a0f030f03090509060109030303 66
    0x75080e04421040c90f8010242400b01e80fa5260007000560407107800300c0603030200d83d4030038003a80c040390010307603009061000704030003000303210701318012881031102600000444d00081a040782c05503151030200510304000c10540141c83d5018081c00b401000040c0504055240590311505843da000f040302003210300c0390001c104628460650b4000d10100140d900a09140c211810701940d0060f21440303200382000010b4280d68102402015080400980101d51400788241c0311000d05508000300ca40051f4203000d82c0b13441d642d41c002c40d1030046004140d942c2c403905010b014030801c807900400107402e641c0010705020b4a20b21020365500014001451412241c895500c01c8840002304240e40c0094400d40c0400710182c03880f031400f1011500f20031110b4038a00310202d0040c91354040c180010b00303008108001000050b000703d00070309482d038004051204d0a5111003030054603240981083d00d4118001c0c80700710401d43c000e402070014100445c0c00740e0262038400c00090400202d0f0000404060b280c04040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 544032392 1250 544031142 544031149
    0x706090e0c070f0f060f0b3303091f060501030501061103030103150e0303090c0a0807060504050603040602211504020c0c01110c0409080702040606030c08150303040f03150e0d0e010e 80
    0x10784681d03005d00180202001545000e0140080c05c072440d108003900420103201c0c46d9585159408803100e82013101c3d1100461182e44903e03000184075940900400c01c3c25501e10714051000c01e2070700d194904c0011914104400101103a8050b0840814002400714005452500000350390449a03c400640d481c580c09050101c0642245a020280d600c0f0100501491a0740462000700c441003d4489044490b500e42005d40d0300c5920703100e9000881d00c200000d100c80d00300a00110340c094042d450142c90800c00c0a00300303042c0c0c1c0120951000390980141480040440c0b85004440054212019030820b081100c07100c1d2a1003141e00000e0501ca25800d43c194905000d000c00000020010001c000104113401c169855900800d8203d1103107240240100e00c01e4028842c0582040b034a55980309030365242d43d0805260140480020750520003408001540e040480400015502c03030701c081d0b0300c030102e011200416500c0500046200d608010b036941c0140ba44144822819042460030503502841c80c40407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 544033642 1250 544032392 544032413
    0x6090b03030a0219110603090d080f061003180b011e050f01050d0b0103110408030c010b03030a080718080105100518070509061c020d0506100309020a030303020c0319020706090e0c070f 81
    0x41755042940803003000401140480d8881b03200c00e4681b215021555841e00785500b10000303c0b0b40c2a03000c00c0c004030a071180d46c825400114564140f8641241580094940e100d1110092703005860891a9000e200741018120201500a02003623a1440340c41070304d01c1c00a00103020781c023a1848071a55a540915032603200380c1090790701480901910b41e46130740700c0c0c0900c2d440340c0c06901c2640c402d6007024500e04c0ca904000045600300700290ba110b0b000c2e03854174403003103404400e01520b005400c0d10100c03011840c03c0d002c1c416a402543d241c007d12040354607040130b0061080c1d8010f00c002144c206002041001d5800104030b4030b9812007154103503561002c6495500942442907213802542c0e1000c11711491684080e40201d0149004640403c2800c0380c20344210103842e0101070094001c000410100006406500035002d5251038005590806403a040290302002044e514000160301503501080b246030002c43c2080501549090800c441c41d000d04004e8540c031440d07000038000d03001c42c1c040d03409100a8080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 544034892 1250 544033642 544033673
    0x7050a030b15030115050438030108010c0f11061801020c150402092203121805150c0f03010b090301020f1c0b0108040b18010e1006090b03030a0219 65
    0x3600b1002c1202c42c0703401aa4000340180d009050a01c6600e003201805181a5422280c10014107140c1890800d404502c1351440368001160308070107440b2201440b90003002e140039251043c0000342d40244075030300500280030000c00c0c50038494550207600700f000c4003050f12940112a965071200e828116150303540244503813603404d078150250000c2c06501c0052095968040c50089078880c49a40340c50340c0400641c0340d10003011150710301c0030110f480000d0040d031200c03d00102d526400145201000c40e070741d075140c25136102101d80ba0008440c0d0b034051801d11003200e41003e1980000d03810040907400320602c034401800303501d100a030040303500059543c00350100e0b5041441d0003111a02d40d076140442c82a08030400c800c07526168200008810035510800340c01380b087d900210390101c20344440702d554428040d0301400340029500c17000514465001045942c0d2031101801c0c0c00500c851034006904201e4180201c080d10903041041242c6210343d00103082031080c022041041c3c170708109490060b40d0410b0610 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 544036142 1250 544034892 544034899
    0xc1e010e0307080a0602180f01080412121802130501141504030c08070f09090c0303180b1809090705152b020903010b0901060801120303020408011103010302031902060307050a030b 79
    0x15480c400704805a0003820407001f4032124141c3d00c4058000308400041c050040c41d00003068000000c0102c0c0c5030000026031500c8509000741040c094550f46404c1e5000c080e0030800c0b89000f0b214850440c24102180014030711103860400480d41026003035942ca25250480c54410004114014001200e01e42201c00441c0d020302811080c5541c0d1204a4942d40c4c40d00c6409255000b40e540040d10100328082d8909032039202c031503070a0203419640c042d6a10201303088109050b000c000808900c0c1070b2004001c1c40d0000000d0f026030380300303000c500030081d07203800003040d100194001e00d904114a4a40c050641c54010320000141c0d16200403100e0b502101c2444001d81c0f81c03880f00a441c58114036055801003651480c29030080c482e070341e810340601250b0902172013180002035610340100004151040692076641c420f28002d49072036a201d07003003800d41d0341f0031400369801070300040100308500c6c0c10891510820002c070080a82402150001165800010486002e008002035081640d610a601403000d40c00b008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 544037392 1250 544036142 544036153
    0xb0114040e1603020307150e041e06141c0f080304051011070605011401090303030e0106030503040e061215040b10151205100f050d05070b0c0f0c1e010e030708 70
    0x82c1100c407403080c20701c0240e0003406100c02c00701d080c494502e40003080340d6407521242e0800c481c580038440200300c142d0003103890f050340a01d42c64649101d402007400508103840d44a0800800d001001842d14000a95402d20486003041c41e00260340042d801c01c40c10780001b001501d9039168109030382414034890140e07230040c2c60301c1e006004524440d400351080030702910307007000980c2c0c968641850110310b1168240c045851414104006807181e00040d4440833804001705230f0320350f01e42d03900c0d00d0b54202d07401242000c9840010000103041040c0719080c4940360400400c100c410710b488907680a03101900180c00c0c42c10502c0001c00c0000905a200d0060900446201d404011010000c10f001040c0404900090030400850031001540c0e80344025140880142c0019030b140908014000d410810220307504d0003440030000d081c5040340007910007214024040d10001c0c02c41c6800700d0401e1000360303000344620410150080300700f51805581d80709000c01e090110b609282d240000e032400041c0e40c003144461090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 544038642 1250 544037392 544037413
    0x90804030b19060e13081308011b02033408030702060709060801060912050c040c05070303050603030f0412030309080a0507031805060327070e0103050c04090b0114040e 74
    0xd024815109400b45103180341160034101c00340c82614607902c9030b0a03850701150045164480403c1948003580d1003461014644800310101c09402c040b941d001242d2030359281003c2c100f43c1046560341c00213915920140d40380c504d10100d81002e00310280790078410020180d0a00c500240c001414031035098000580644a04c0e007640020740d01c031021220030001179aa2000090709a00500700c00707040c3c8040d600d402942c076040004080c849030f000c040682311803043c034555403034682311807065001110240e40c480d9650802824041c0c10350300c000e01590301a41c8104844075802c0c0b8400151405e448881111101d0f000305030408030080c0c40c0040300a040c449001036a80350094000d4000e00019119845040c1c7c6c82c020401c950001d04071314840c0c9a0054410800101c6442c0141c085d8519440265818500c0074135919820b403605090b03412048100c0c924000502c1032110400c10890100c3e07040300c0c00d03c640c020a80c3c5460400074184200c5181c0441c0180008050361160800c01209500e5022120103410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 544039892 1250 544038642 544038653
    0x5062409270102041e06120e0318011b120f0806010e040b01021c050918010513090f0510050709170742030e0d0e19050d150f060602060a0f09080403 65
    0xd68452034010034600003c816256820b0700800f80601080d80144ac14401d12101000c1490082c5020504000c1c5511610545042e80405c0305911805614070602c29501030001403c65154600007400380200401089407680e0711181c000c824110503200400c040071100c0040c3e10b008100050b420b00d1190300244070407481e90000240c6041c4500702c42c0d4018805205042440382e010a0190030f400801c9102d80710b41000700c540145074001c0c4900c4506803c1d1a681d200c076800c00c11a2000c402d40e0a4860702482583d50f4001c034414090a1b064001d413a060700b0004000360b0381ea00501c11015290469035031005410300d04403c003c0e84040130344020102400345450b038000410424bc640001c82d10701111030340e10442c0012000300d80805030b1101c44980c40e2314401c000900e00070002a40c421885940045480c0d100c034841c40748203e100d2a07542001e80441000d0a00f6903021540020a517450f2200400ca807135400200e1075002080030720001071a0021910941c080c00a00002400f05000024004200503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 544041142 1250 544039892 544039949
    0x2a06021c090302070504020f040308070f0503030406050a050f0106021e03091c0b090606010c06020306040906110703080f0c0f0d0905010207080705150c03040209130506240927010204 80
    0x1031081e804e9507252030305c90003007008900a4130184502c0c03800a2005000281340e4400908949015660668100307440350340703a070718542c01110304854950301e400510080e02c0341405803076000107025000e44080d60410f0402581c0d00e9000464218102c881541d501e90041e09004460070080040d000c100c01c0711100c211110015010001240c01d10201c0001407801c420104030107001d88416598540b4140007500c0d26070282d08046c0500e640b155031100b0410002d595072140203104003000301e11507140ea01d142006401150000e040640d15412481002020b03281c42c0e0841c1d000ca034090304025224128100404014800504010030790761000500340188401031001e01a2a0300c0380d811104000105159192419400d0700d040d00858014404500180303041645683d2110360340030b8001d00a0402c0e1151071402c4030654034180000b50440010b21805112a8482400e603c245c034003c0c41c03801d02c061b00705003a03143d075212600d00c441c000b003400100700f000b90100e07001054080210140640742d01402000031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 544042392 1250 544041142 544041161
    0x122d0c060d1e05280203160c0303060e100806060406140402130e10150504050a23151305030109080712020a140d0e0d020f010e01030f1505010f2a06021c 67
    0x131541d01d00341141c60810703402200d104800e1500c0000700c4180110040e104000b0091089080c5620b900d00803c000707949081c5180304103010b04206903c64508010321342401d8014155600460404909004a0302440b03007a9841d00030a41e4016519002041c10140c907411642142d072210810342c0512040b0703260891004240e03005020140500e8050150946e03440c4254405c040e04005020300804c41148c1030601000c24514241d06d0018000c0007200284000150020030102140003052078103054880100340e60280c036081d0005c01050440d0340b50843d56004000c07000b00780c0c008880b640c0780d503c0d100307101284500d070b030084d5102a8826800d4596441e9030743c10070b800c00080c02d102142221864403d02201071580c020b040f079500d41901100449021070401e541c98181622004070a240302214402ca40d0989104500c0b0100a800c20000510185d010074461040120210810303044c41919060f0803006000000701081c503000701c3c030b0710b48003074014003111200002c040c44607082c0141640d080460340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 544043642 1250 544042392 544042441
    0x909060c030b011106011806090207120201060801020901080411060f0c0a1e021e0a08030c010509010507030b090723030106020105160801140906122d0c060d1e05 71
    0x4200b200b00440d070241ca00d9000e0502940480010003003003414001040701450030f00b00c00301c0d820742c0760304081060343d00031350080314813404500300c0001c015828403482000c0c1842400030f62400030300340c0c00202203030750242003e0004114050f10143c2d980d21001281d000341356003040141c94500c100314450300c440700c429055420648030101c180f036070052680c0100403186d004201c0e400c000a0b042680c0e0031404d6111002c0e0304003a45100109030144200054448044020300215140c64458050741c2907030005444441498108801400540e84100308198451103501e0048451282c110601559004005002d051032038008000f0400b1981034004510400910407401107e440f10305089619090922030102c00156810411207145091040709400030402428004585032400c00b81e82040250041c046280c5d103500030004445205015208064131220007602e800b0701e80c103002c10b806125185252060541d0f0b041c8511020303d00d958022280482138204102c10301d004c45c48104200307205000e0008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 544044892 1250 544043642 544043651
    0x102040b2b05240105040501120b03010e0f0106031707120503100e04080307020c0f0f040c020c0405010e0601021204150804150906020a021b0f010c0c08011506030e150f0c040909060c03 81
    0x20f107540203104403002c540e0103945034017403681303520702c03200081c034213540d5042d03055481315903030090880d0030040840b45810070347c00003642910b145841c2e0301e5105207400c1d120b00000244640c801050740b1038804034607552113041095a0340c2d5000c440c01e00811013034110440c12400741082c44103000c2400091880b403071041c0c085a451503980001c10003030f0815646216409546034a88030101c1c14030b41c00003c0c5044260040703c08508600b00001c042d9282608007000f00c1f4200000c02c1160360341000b50f00c4440c41c0140700703c0d1801d8101030101034044481d41450701401340407030209040090305182c00c082c04444d40c400b001258894070300b00700a5840b83d4094001442103008407071b98140840110281c0d9480140801c402c501040010f480400c11610260ba120a1072440002d88060030b0240b40700b03942084a9904440f4240140a8119103550240b6446039000da03510441156840d04601e0f044422900c031020301d50303150b11114226200d990800312042e810300d03a004007000346d81c1c0c115651420a82c3c40900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 544046142 1250 544044892 544044961
    0x1f02150405011a03160302060d02070b0a09020103110429070204091101090b0c0613060209031c0807030212130c0902270904051507020c040c0807020f0102040b2b05 72
    0x1a43d49620170402c41d0000c1c0c010104200524100f8000d0201c100006005400d2a002e0f4075109109401100c0542c5007a4440d1880800c56905101303a1260240c00003455003081e04000f08401c441c038080c44503090300840340809403100300ca03980a0701c41c4194018802d0295051500d0000483c407805841e29010502009000c18a1500d00060307406000400300240f50b01d5403000f00c107c5031a6074000c07080d221280d0070000404c050b10184411001560100300d07002d07200000c10002041094010202d208052040c4800300c0c04080245015401c81a907034425241d000c89410000441c041980c003070001c01d44002110382e00a0f02c030711111030840e088984000c0090601c0340610040c0f0300121402001d0b41c100503900c0310208050f0f11181d0304025184103c0d48080e0707500300400d00303c513103041c94800032131080c0c020444d509030704114100030380104100030f50405241ca46100507074080c10030052034072010003942500d61408030134480300342005100184000d08140c0040001c148003084140086190741d209032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 544047392 1250 544046142 544046149
    0x111030702030703031806091a060303030f151927020f0418020f04030b010305240610030f1503050714031e011d03030603070e04021f02150405011a 65
    0x180d118a8250700035514003070007550102c00400c640d05451160800c40c5001c1c0010a91521803a12210700c110803c41034400b082c8800e80314054001c0c00b10788203500070010400b03004007801495401080030048410401c202c00001003440420b283c0800c802d4103c030000048220300102c80800c00c1800710180c03d45107148400c01403d9124900681302818810802000002813a20072441e07d868050401801c080610a00f003100d83c1c07060348103403460200040113000f404018400b4040c640e5044e5140d1202d028002200720134400c1c020300c0c0601c00c0c2280703000c0c903211900076040744034020020101003068100003661040801110302080c1c88500c15084042030101c1506030b4849070560040003000d840520b003410030103c03100c480050016549403804640c9602c808810080126000c07400b55440749011800c1c18a800d40396400816150385200038000507032110300390550000d00041c50803000703640c030302400e07450150394486000c00040c2c84402c00c13040c404190300110010003000e048038180c42c3c110307040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 544048642 1250 544047392 544047397
    0x121801090320120406050306011202040603090b010608060307210f05011a1008011401090b18010806100e0d060617070801110a020c120c060a0314010e070c03080406090f140111 77
    0xf804180002c00c0280622409040655440b050500d440b928507101d001c51101039030056445180401d484840303080403c42c5002000d809010f092512100310320340b5400082c1d0322100c1e07200e100b800c409911050844a10f60703035461110240c00003d075a80d03180c09442e029000700316250118042200543c8900b4061506444e0071844441d01d030355400305170b420000c90021801c40d400202c1d06001090600007001c500c81d40203400314103816101c00b2000000c43c030001d48403560041c5024407803480c100504100c00d03044031030f4040c3c20304180c1d84183e1894007440c3c03110090005412800f0500c40109840810041c0014028240c40c15100240710484032400002603d0150845003405038001400d800e100e8100700000228020580f02216040c4e41a00c000c43d019074042001400041d131a483d80900340307440c2841150060040d1803140d52280307072108004040a000c1c00d0020200400500031a041c4035141c3c00428030603801400f1194030284600c5c004074410030f040d010940c03950801101c41580e0004505 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 544049892 1250 544048642 544048663
    0x2010209010c141f0b010306080106050303040b0706060308120108010c020601141002100e0a06180f03111002030109091b08030a0f03060b040803071403030c121801090320 75
    0x16820301d0311181e9510f180f076440114000e10024860300c9600b41d104d000c168825107406011034400504900303d90300060a65619070000d01c65681890020052904e0000860301102e40044030140c48403000d140c9080a0300455001414141c0c003c15180906806040d101d0304076032070074008011841d007205d03090fa122102442607141200700e020310505941030014910b127031550f0070300c180e44010850720b1240307085404190004106038004c00706a000c003c0d0318401c400d2401880c0340c02c00c40703030038030b50303030345a0055120100003410020503001082c0030145c100501c0c2040808000c0139516903856100213801800040d8096410040d0342182c1c035034488100407441c05880400028520380902c100040c2c6000c101c10941408050b69503000055001c2500003810261131040c01542c3d90362000e05210503901035034000240d40b030300704205000d0280981012548900b103811541865076642c286c1e505448680250010700310350070599a0820075070310020b85503a8112521030800488504203007c1c2e40c40b00d4080c0f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 544051142 1250 544049892 544049897
    0xc0905011e0e130602090316080c0607120302090d06060303080604051305060c0f2a010c050f041e120b1030050c12030705120c0a03030905010b0a1409070201020901 72
    0xc0031603c1c1d14040c01c03242c1c841e00e008000240c0380c15840d801081c540a1003042ca08507002400c141400001001d1200d401c4250303084070a5400c1400c581c5840841004030f04000080c03540c00035802d0341c6074079159061200d840e04660b08110042c0e680c200684504002c03203040d4030942c41c1400148081080c0c00011000c1c980007801403880360f442c21440036507070340a4030391410400414050920200140440104041e5003c0e05210213003527410250b03402d44000200c1384003440030074004d008405150200351000c540c9c0829501c1d8000f203c038904c102d91111550840455192407402c100203111013182402c5c06401501d030340c400032a82e2094400d0a040c00110340241d07060800c402840c4480d01c1c900b120440500401c161800c050007580098090403001616521030780020541c0414400240001c10031b100001c41e0039840c0c20742403a00b00f515441c070083d0040c03d140d0f4a281c0c2c0300500000754000c100c24980a80040c0c900740d02c2c2c0304d2008480c162100814410f000b0200001e92035407041c0242c03074000d00180c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 544052392 1250 544051142 544051169
    0x15051312050c0d080c0f0a110105040812090a030b2404050105010507032706020a050c030a0c0302060c071503020c0105090a0321020906071406060a1505090d0c0905011e 74
    0x4003c002041c0070104050b581c032941800320020b14082031207091038541074100146500e034003520700205032444640e409418004d0501c41009844004503803800c1c5074918401050b950b00e280d60000712800b0350f07600013070181e040207405c0108101200120304a440c1d07451941c060841c0c2c0200400c001c2c0c80302401a140025424040500000c1c0102c0040741c8001540d1a110403400e00001c4259051401d9804840180c0c0070503c2c2a00b4030406102441e000b46041c0d0241a5500c0c40d40c85001140c209031000030300445000075054503505c03080c400f02c0e0203450400510710310710016203030043c00794002564070300c3e55518010104003507100002c1c4084115605803540d1070081c101425101400300c00000c40b0061917001c00c040d051541c1c0c0d40009000040c49442d24190b0212410140c502c0c0103002043c290107000c00b5181440703000ea500c03003800000c1c50b8605c3d007143c1d180480c41c0481c0c02c030000040c00030302020a51001068121203900100e050720310444460004009076401010154514451072000d100c25 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 544053642 1250 544052392 544052413
    0x103031d04111e07021801062a032d021f06050d02370323060f0711030f0414100f1b080c010b0906061206040b0a1505131205 55
    0xc00c83c10010300300603140d0a04005858020807480c1350500d07207004800400500510015401196854442c05848a000000309600b810766008683c800c41c0a001d010040e211041710380511051620f410190509114034040380c608060b64460f0000ca40c00041100704506107035908180c850442205e8008103005688100c035000c6c070610440301d041d0f030150080c140a00d00d03c40401c194944d0110004000c01080440c59814030701042d040e1407801e45095049000c519804502c001401a00082004450080c03038641c601c003612500301d4000240341c1404040b50031480b0200080290007242d0004c07141402c40d030108010807510070003040ba4040481c03401c3d5490301c40e05100b07140c40c44a4080c440e00910001303503251961031141c0c116012a8105030345426000c003917400d1a201480d048081980d900d81010f1014020641c0030400a10603400780d5500c52240307403a5502c00c56524010715984003d00c44400e1444002055507001000b13240702c1c182200c0740061034068000040011641100240c043d00c5034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 544054892 1250 544053642 544053667
    0x806010c030212070f0803070c0314040302131d0a051023010b0703020c041d0c0102070f030b0603030714030c070b0405010903030e150a030207030e0406030f0b090f03030103031d0411 80
    0x10080c03069505c0102c243c4154009032020300158001c010325189c10640780208e140007080c52035000b0507106240d0b000d101c02c20050f120a4080402000c920202003481ca903845800c02c540240820360110314032650003000d00388040072a000542843e642014410700e00c02c0c1d84c08205444c21035510100304070148004200c41824500035207100da100e0302c140d965410400b0f0004040d40e4031181004c21002c0c0c4000c484001c0c40d000c04c08181800c2080c009880131629207140008000720a11014010851038000508140c0c0e00f48103d490203607000404450302c0c0c410b5410300c1d0740c0350484240708900781f007050804240280b10303000b0365044a005039a209151415030350210740420300c8003601c1e50000e4140036038161014441000d800c0103e0386580050f1181c1c490306004158509020210340140d01c0e00c80d0600101da81c0502600c440b68100844030056226044824600090160440c420b804048004020554425a0005252542400c04403d078200303108203c11600c00e01f01800340348100304200702c0380c030030b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 544056142 1250 544054892 544054897
    0x3091707421d0f150d0903090f120f020f1c140c061606090201050403200f060a0c031b08031920041e0b0d06060806010c030212 56
    0x8052a900514070860040544480034164405644501e4100a403455040e808442010402c0c07852507002000b100c0503002c00c0620b44800035150003150070301c8203c904c480000044425040419000304400844c03800d000b0008402801007103e055842400060041102000f4041041c1c000c4100d8088985560070031107041c42503040e0940040200043d005516a0000f41c41609405a100003418400d00c0c40610b0034001c1d400c4890340f044d0360a008900d180946031114460113a804607000584490030b0006840500440e440203100d40345620700c03900101d0003065800489041a90301d01c4045941d4030401c5518000d00c054040015811581c40001c240b207004442200c4410042c9001c0e10300c45621034041a0740201c400800100070031219052025041c840c111010007101ca21055511007044010054802e0f8881c1510765204140d0403c0d01ca940c0b20056030040902742034159840c8030101040020300f82502ca5500481c03030000004160b540a5520320850719403560240c82d00707216401e00507580c1d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 544057392 1250 544056142 544056179
    0xf030510021803060f2a12040305040e04032102071e02011103070b0402090702030901171009060e0601030b1215040f35120c030a0e0102031303091707 66
    0x2e5450065041071a181400382c40d0045400c0802e0349240d03d8844000320007840e460001c00d01a911144002c0703100b0042d10b058801c401e200c85903c08035502d071810116494000d64000c45c0069641d181400304050300450400062413100740c05c103c554240840950480c050000081c1800c03402c42142948103421301a200f01d820710505010140b40311145180f0325640042c3c80448102029000f80800c1d443d01c408215403002c0c0902c000c51070f150300ca86c0004d20320b4009481070080e80881c02c0100300c1c0341c0781483c0580d001d88502101002411f9940391540c1c00140d05540e80c0c0e000c00d03d000c0303000100d4101040101045102c1c1e500801c400c0311918210300344050000c03c10303034964211825200000701d08660110205013104103040ca51000049100521400089500408202040841c00c00fa42c107075070076644012200d028030348a43d0f4401c042c00107050350201d514541d51000003001281e9400b40341e1580c0b114001c0c1c0c0c4008440761224030b40e4010380c01014810040d580802c43c00c120242c0990200d0b907a1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 544058642 1250 544057392 544057417
    0x70302010e030d0b03070b1e18270a06060504120c03020a0b0c0d050a02060424050c1b0a080405151306090905091606050a09080316020a0f03051002 65
    0x8400440009811500044110420140c0b5804144105d14041040401502400204520308081c2c0140b40d00c2c1c1000c1c11215071881400481c1902007800c08807103040b02c0c400c0150205941100c0f0946010703610000c1c4181c0241c0c008a078000c103209200310310851054079069240c00e0b19140c1001640c0714862050368049500c1006010003100585421400600a10822a0542d01c4d000f40c0c001c141d081190440c00082049801e00038800d0055001454a0b006500004c0448810410000045d01d41030208001804503080c0000d110349005000001c0101810301450500700b08011a4600d8441200e0040074042c85c00c248014080d5107008285104c049086003002031a04428511110100413240d21070000f02d101d1010402c0013a2150041c554466080070140c07600005050a00344903500c1800f6071000c014001c200b0702d070003601804000018018000c01c40751034146908841c1000001100308030b0140480400010715a941342d600031003926400b102506004d20340070211002900202d0340d00c0007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 544059892 1250 544058642 544058651
    0xb0a0e01060b090405060d08030c0706060305031902010c05090307030b0606160f020a0605072003030c0102070c05030f0102040b0f0a0302090a090c090b0c030403020405040606050a0b0d050f06010e040207030201 92
    0x2400a02440748400820340d008119480350426000c0000f101c400804050284520724008400100d00c9811242d015482c10b50a54507038809040c2040280496040101103204c001000b4500303080180e00360700b0386202d0b07a00034810a060114115141c0c01540c0035917405078080c2c502800080c1c50144802e07030020018042d581490708030803d12100d1018180150359100180d0454000d6042c074242c0703038014051074140030b0718000c0740e80e0324400f01d50102c0d9a0545403054000707811145941c04e0048404004a810003503407219101c0c02c022070032101900c1a10f201e441001d0300460504810300039a02106c10140e0304a0505611047e20b210701d07413008000d0001c043e420010305200da40d80999046c060444c2120000741030040c104081c1c500d005940006403140c1081c0000b40700d04c48000212400d40740e050720040b5060303e680c0f07404000703414681c01c1940c2c04460504017007068007026000c1c100240c2200320612458031641c003140c0f408101601c005000803070800c1c2c040494105900100142c5100f80700024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 544061142 1250 544059892 544059911
    0x30d0e011103042316180609020408010f0b09070207051c050138090c1b06010306092a031101051314040c14030106230f0d0612030c0b0a 60
    0x3542c0308072412a0351203940f4402c2c4580380d03410614025500d1a4000402c070103000c2840010702241c452207080c2440d280c42d484c0a90078001600a000240307490b503810743d00c0d07640321a40e0f140a440300155151601740740107061100e87ca4503000541c000c0c1015005851000d040c00140440d04032264248401c8003086940000050000d00c1000301c95941c40c03090b050403d1266100c0107502c002c0e071108522070950184065040d51744c802600d90007030f2207003801c15941c101070030449042d200c0c08404003005009a200000a126007a0014240302c1d1042c403502040354620500c0c1c420300040c0a00c0030141811001c001c2c800204004803842c0f03603080c1410941e080c68070513020b8070101c03003d64000201c01a0750007505900d80c2041d0003414061045401c007040140d6134004402d042d80814442d6108201c2100c0681450b690f0042a44820442d50703142c0319a540203a0b505940c155000c001c040000320318000c0000703000c4000c10b45020406a25545804480340941c4030000c104001400b88040e1607906d4100f107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 544062392 1250 544061142 544061171
    0xd0510030b0f0402100c1a070e0a03060209030c1e0103020f0c030307090e09032502011407030206190c0c021203130e0f070905030d030905010605090c030f01090e030d0e01 75
    0xe01c16074108490507014605403050042c0d15103251080002e0008549030781d8001100810040100b580c83e00c2012001e42d08c0b11000c403044401c600759a0b40000403d54040140140d5030010800d0b45001e908440c5640740900a210864005030609120920740d030741d10350101e42c8642c008280800701c601c81d040c200004881210706561083c4d072000c011800d0305c8406c014903816062110350240030b5130084e60500c0c1d101c00400c0c07500d400d0740c040441021600004c2c03004680c003407000b14544c0710010380c1080c0c841540d8036000c0d6070780d201600c0100c4c01001c030ba01507060514490003a03440380b944c0b603a40c01c184400140c1c24400380c00f000c00c00d41c203043d0005100c0310141c0910401020014000030790345012a00300b41c0185440d00c2c8010300300e84100588540c041c042c98030b0000342d00c0291000c5140022385412281851801001a13410040e44141d400c1e041c800d4118500000e103004102540242601c0d0360785240351011034003401c00c040c2468109000d41c904d0f03c25158807000301c02d0321003800850b0405141080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 544063642 1250 544062392 544062413
    0x3070b1e0c100e010e0a061806020708040e060604060c03050901090305060907090b0a06081b0c19060b0d050c01050702040f021908091f020c3a03020f0d051003 70
    0x1104400e074801c0340d01562401007401990104840070f0001c01118030001d41440c0c48400e580e00140078940c4175a03a259a01189401c03001c0b21a8000d1021501d41542e442c2a420692042c07003050483e071860004152540f806c074086504a4540c1e40b1001d2602899650991b26030300480380d264144043c02a00002103081440164800c024400242030280d00303250071030045a042007189809000185000d01c240d503008201a80c005d01c04403005406008200101503161240724902031841c0900d4483e452001c001c200310400b03c91080d070b41840f041c000b141c203005240d000e01e00082c01e19400312800001e1540510020400d0340d0000e000440d0388442a40d4020aa9105004e00d5101030a24182b469685500c18001e54008803048041c5c220725040702c00102c02c0c0305c044180f52000d41e60000c0c3d5986607800802148884800540c07559508900c01d8031b030103413104054000002d1198901d40400e0480b44603200300c03130030a100845a03038200250340354203500801c1300078045a265450100b011021030450b504 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 544064748 1106 544063642 544063657
    0x705030a0324080d1116170106031b210b060108060109030b1810020909220512091003140411042712020601030203070b1e 54
    0x440000e801490b4680704181035210368009030070b11000ca5081903065098943d20028044a1902c94031108080c3d81650b0b1a41003034000d010f1500c8480b0540c0c0b41c01c0340c481c00000d1440d00d079507806051621001c440c0070710035034866040042501c9140410224030b80c400c0c442c26400580e90350040c0091002e05400e0600001c540018050b902c581c400c60000d5400401d10400d03820301442d903040001d4903a83e200700b60301a2204881060609000300d40c0030450160030707c83d4540c1c41c04071000040e002c0040c961015510140d0803070110300100700a00c4541902003082e5a02c940c140704202c001d0800440400615040c54040d00040b003017001d41030341c4aa0007080c0307403007100c1070b100005006100041e207141c0120803030440140c0300910b2064050045118003983d10b408004400182d80d82c207001d200c002e6041d40004c0c010b00c5581140c101412b012842c1d5182a050103092180301081c5411444 = true := by decide +kernel

theorem cover : BRFrame.Cov 543884892 544064748 := by
  have h0 := BRFrame.cov_init 543884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 543884892 ≤ n) (h2 : n < 544064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
