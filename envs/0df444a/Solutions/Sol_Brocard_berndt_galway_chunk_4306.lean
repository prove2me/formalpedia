-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4306
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:11:24.370985+00:00
-- url     : https://prove2.me/submissions/b62d5378-5773-4f64-aab4-09c87ec17afa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 774280575 ≤ n < 774460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 774281825 1250 774280575 774280597
    0x20d0f06080d021b060a0804150219030f1e020a05040302120a02150a0c11060708033105060c0310030c14040b1c023106030209070c17030a02 62
    0x318006403010300072070140d00044075902504d400b034018440c80d407000010b00400701c0c0c0c082000c104268099015050040c0c0150048a15004507950b041d42c084c12a40140b0621720180d09035913011110540c180101040d030b042e03025003444810b490140303601602040da5031441005801203504207002e1b2290094a00454006010150505e201100c00d922000e0b5110305034020103011a1000321960100122a10144a540c41d40d0341d103981038541d543c5032040d850f40d49500c070404020b6074002c030301d000b4042c43c0550700c0203048650b43d5905500e01090480b1185d840702240540020500205402180d09170340129440c0200c1d55955442041610444d0a0340004007070680c0b0001c04248498000c21020000074240c03000c2210040020800202035030b01c1462201c5030b01200f41450040c00c2560049044007100c0b41425001c0c44d5032901020344100703d9140c43c0813a9650b0170f0400c254500108042c2d0412400d00f042c407416102500d54624441e0201c407000c14010002020680e00d40099045a240c0b21403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 774283075 1250 774281825 774281831
    0x3070309141f1d19090b011e120216051c08070e0603090f07080d0905030a17070609021c0204060e0106081828060b030d050315032401030308012106020d0f 68
    0xc0f400000a012080340600e1170124a030408050240d40907403032207003030a1040c032500f554048002a00f200c0c59a40c501c0c003049443d400b1304c2071401500d0010070802016124201602c00c01450749014010f840003684440e0801005206102905030030401c00b070076400c81a40c60564aa90f100c041300d1405000800241e81ca202d885000285400d001c204005000c05681d02c40d051507035544105a56814540400b9103410702501101401c40403200003048014484c0342e022440e00d4164000401803034104980403140500c1c0211001189014441c250140041c981002c80c154103102c8020080ca80080400c0006025842e1400d0001e0341000b1030400c20810000903000000350100702c202160101e0030883da0079082c04514500f901d40420344000b0684260349482c1561f0300c040802461148827590140c050080c0056440d80f4444002c03804e140030340500403004c0b654035614005242950507844440c031482c0400c01d80c0d4208202036002e80c103503a0400c40c0581c0700c04101480d540280030f000340007107245103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 774284325 1250 774283075 774283099
    0x90c021204060e100c02130c17270a11060327010b040b040e0d05160501050103051c1106040b0a060b03070906020106060c0c05041d03070309141f1d 65
    0x20307002106094010f03040d110000d09031380d05401501c848a010400a510030b82c020380a040b03090281d0302403802c2064500d4401461500c400c2049803160050b034400c0700c075580800a0a00d560106c0141581080361800103080e220040d031904c1d100351020b440c074581700c4c000000200b5070150010075025010a450807003075180031559004079000300040c0c5d000038091402d04003088000d241030300c031703514680c05047c0181044d06603001040782c0c2980280d401c01c00c040c0c200c910341c0000c41c6091040714044d5100d07500a00d9000101424200302681900e031036400c00c034885020112034000455141d03001a44050001d0b5161944c03c002805814542c12100800c000401080320895101f410103080f200143c000300403150300c529049601c182e1992020700038090b075200401c010704159000c142c0e40503019035040c06015400061605641c0f0100c0c01b03800148050f0301c140f2924220701d074819440c1904032207241c0d12240c400100003003e503600680744140641340000300c0d081d066000182040600007000e20980e02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 774285575 1250 774284325 774284327
    0x26060d290615040b1c0e011e0f020304020d1205070f08120a0b0604050618042306030606011b050c10020106090608030a020a0b0c070206130e07030504020a090c02120406 74
    0x3804035000d601c200302901c1c50516124030141110151402009410700c0c004040340401401015a034842400c10b64665a0403403802c0c0030b10401e501c2003451180c1c00756491120001c201034a00340c1d100c00c52400d02c108180b200580c0c41c211800704199218000c46241d200a0070162040d008409020f0901c1150411400404c2100c0f00141421204c070703a4403503541d40f2620038200854800064980e009002008280703d10f2a02101038803143c0d031444403a8106210810100d01500d000c0c5101d204081c4e14294012040d03007030740f0140c81d4480001d030028002ca10384100020444440030b07100c4c0701050610040360003413040520010841c040040c00d00c242c0c01034000d000a000341024881e5401e13071407524002042c4000e011048034107105090380100030f10000da07201d8080714400549800d0400c80100145001030300c880d40544aa109081d4021803154501140e60910b00d4004103039000701807402c0d040000517a10020700c801510140c8070b000400e451114802d03403038010300c440654500400441c0000d001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 774286825 1250 774285575 774285653
    0x90203160215070e060c1014061e010c1e060c11010606020606100f1107180f050601120b040e0f0307060c05131a0403020d030206040326060d 62
    0x405908464102c03010801056499400b81d8104002840d1091110500d10703046000c0c280c9021040c0c203a6000e0044104404c084038132185280305203001039010800c0c1032402d01c14440440c2480c410343c0c2c0700900c0c00c0c00004e000180031f50000300b1012003071b801d400c015450030441d0318585c0d80c0400c040000b10066000540307a0201d00e85c004445600b00f40e00800d44d03601c04035486006d035201a00f00b4801e1920340c0c5055442c0c0c00c0f0300c04c80d44100442c080d820090120100500e20040c01140c03540c4d5003c003214070101c426101503107510310540c1e041900b0b1004903684112112034051200d02e00050408410300068050000c626000b040c03031085021000c0800804002821601d108510411003c0f0441406446501079203154071a45003900d1801c2041003041d003c4511882c0c03a103030070240390544a81c0084d568880c030031001d60041c1d1202c02003104154010162041140a62102000201002850040d4610000c0406000300d00000502c000c00446030443c00f004503040380020488482014404c0d41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 774288075 1250 774286825 774286861
    0x706110d060302040b0a0b042303070e010504270201110115060801210201080c0304020301060f030303022a123a0b090708150a05120f0c10020304031b090203 69
    0x104e9850103c007000b9920b04005040e0031142421040d0b4100b034a88100c5500c16241c00c50202c661114002498210766010321a60028000c0c0070384031201c0d03504203c20700c400c403480c00310f460130b500e45405040c0f14402c1000210424055091a00514801d0b0001e081405840e020741d44810108413a0000319406800c40c154505841e0020309070b6004070300825480500100100c80a808510840f01082420041000465100380003900105110780d803a8906c0200c400b00f83d0043d40041c0c1d0200c3c1c025250107080242c440d2900f4030b06000c1615a03585042c030354480f0f4072000d005d82a440d0005e10340c3d00f418484101c4204003a41d2154070800000001c0c0c0d4000302c516808040c81c9030600e4000300d1a01d031700d001c3c00c07a00c2c0203103010f0342c40c0030362580c0e1603001c03001f6400445420f5500242c0031100154035500d134204e0070784c000c9281000c2d2004144400400345060103920740c07140b15544c110001800f1507400815039007180d0f00920000c11919509445400c6001b141e013203640d03c40c0c00003007082301d400084903100d44 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 774289325 1250 774288075 774288079
    0xd020d020c0f0105090105130b030c1b010506030705130f050c0712020307080d1e0908090a0503120d180807030e101e0e030c090f37020706110d060302 66
    0x3010101e824104030900c620520340034041074042c803101070326510500140445200c0410100b01040e21501c1800c50742e001258582d00241d00010402d02c800240b11201881c00000f00c024000f40c1010400a40c44d0b22940c01254010000402c00e0011203943e50842004004281400c0020741800259246140e2083c581034030112070180c031010004c0d100000721914141c010031400d0429210809400240181025954000d0508809030700c500142e803082c0300e0003601c1954131079a00c6e5011000d020200c0400d61101e40b09800c5030486100f1021507104803004241d40c130400241c440300710314641041041040b0080d103c9100450414101500050101001081103504211080100004540700a004031402040c07030213040c0340c040c10902406603061500002025181c9444600d80440d0701030b142120103a442c10403c0c403e000c42220200c00c1e802c41c5103c0300c07203003488410404012005298441c0c816041e810350005590041c001c080c0e003d200181441005583c2d90518000ca54000e49842c0c00140c2c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 774290575 1250 774289325 774289333
    0x604020c0a0c0e18150118020c03030a060f050a2d0807030b100f06020a030f050d0e0c120604031b03090905090f06090304080709020748050f10020a050d020d02 70
    0x81481307600140c06035a0140443c0900ca01c3d03800d01d00c070100d450030188480c1d1403881d000d01000b5095007052000e103100b401c052100041d10307403811540b1a6002c2642d804070b030090f56100b20900c0249400c002c1c0049000001a01c00d0790629411000c0102c01403d031710240f02c45c09000d40120070801c2000c0d600b8001c15554210b054002d494641d040500c0151784246405603000e0060f5400190003801c0d0784140440ba0705020341001e404603416801d44016244824882d00800c503411807070300d06180c0090780c081001005000d603181c0b0703a40c050710000d100c2ca000c122190034012900101807282229601900350a101404241003480c102941e80c8000e90a05450b40114000202d41004c0041640c044849040080000300e191800030002584000000c1c1da51000d02202540d15022600700052503800c0d40003400000c0c50904841d45003640040d004480006042100304410342d6003441200310b684085524102003014a403060380b41ca480b41e0002041ea00690040000540e00880c8400207480c85400351 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 774291825 1250 774290575 774290611
    0x7170a02120604150b010c030f1701090c081003020a0b070602190309060b0d0201020d05090409050a0f02010215010b070b07110a140c06120f060a1d25080604020c0a0c0e 74
    0x213002d640401c00d1060004040c0703d401c402007441840030555908103400c1005a514164100800051098003d851200d460341000400c2070342c0312020b107600000494444400c01c0c00c40c2e002556221540c403c0c0b524080d00480c2180501099904580901d00c10f0409105011021034004c1d0141c04d0412056565910b00005403805060102444400310f505074007070085c04400190580745500300d4001203810a03501e400800c0013030010468030100502072040382414185901c0024900040007080401c8000c0e003400400c050407001c1c069480303559000400940a55508108075110480d4440c0350025101d1420000103020203918460000001c01e001d59520594082c14000700c0c0c030030700446140105c80c0500140d411403140751a25081100202008011540c0745500721071000d861003000c5407510128180014200506003001e0b001101380710795000b0b0002c41d540a4201d810081001d40111b40000d050383c003480042c401d0f55440d0381e0101020705010b8540903d0f0210754030403611003200f11880c80e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 774293075 1250 774291825 774291863
    0xc0311040c020c190e01030c080c010c110f0409061a0103051303020601090905120a0201272028050f0108160c03021501090209010201060b040807170a02120604 70
    0x60000d07507400310340081500c0309070041444a0810104600201e4408070140820b0345c800301c400d4280298040d001040c80303d800d01d408541010f44c2012094180610194450002150000003070710444084800f1002c0219800100b400b50103500b00090910303241c0b9001705441180c01a0852000307030281c0e070420640d070703c07545440b29031b501c0750f140a805a44680b004001e0103029810807003000d0f1246047d20406a140054800c2d540c1110301e056026175150094004a8942701101004000f60342002c1c54040b905a1aa0ba01c00c03000026000c80018191160460b251101d04050310990710361182042c04107820bc1000c45001c06500a95202d6801060340c0c40e00340d0f1107891038900880f52500e1001034031508010a45018254000c00c03025401811035010424100d6117110f030081c510b80d80c0140c0d4410074a400282141d0b042e40220020703040502c410300103140002000410b48a10308200010404004426894400c3d100c600a42c0409440307030080803012b0224a00d80124030a6080d1103a0b5100c00700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 774294325 1250 774293075 774293081
    0x30e010204060903110a09052406120412090b18283308040b0a090b0105010c0201030e0319140a05160f050f03130b0322020a120c031104 60
    0x10411001803c018024008102030300b1012259400081048001a03a2814045e0541c1c008a500b514040d110502100100b841c2404c081882c03a400c8441a103810800e11914001d2000a070025210014000c3c41c1c0c01300302d006240d04409020000e030407039140c4003001441d0101c5807401440e1070080d40101c0e942d413008002036403840c04075280c2d1900c00a5141c01c218511100d024802c90301810411030000c000d8512200810300c090349102642ca141061a1038201200c00d09806407101010034901420900481c0c5000d0b0881d06503802480c0a04944c0418001240a4050205400010f000005101064800d42c02a66050a02644401c140400d82c1222810280144c0035030304040360041100321144c0c08400b9413588218441d02c1c04945002c1152a107526250f41961903107210f50001543ca40809451109180203102e0300c0300551662a000805604145405503880359030ba6030f0050314400c564038004404007500d000c0d40080710108143c00d00790140c1c0e90310b00c000d65071260310308526445410580 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 774295575 1250 774294325 774294329
    0x70309050a050d1205091e0a1a071d21070509010906062a020613081e0105060d020a03020907020a05030c0303150411070b1b0a0201020d0f0606121a13020703030e010204 74
    0x60203420340048010003d1f400d40d58020105036203000c0d01f05031400203192000032800c5200803c41800e00303407a04083c0540380c070103120b91641031900b050320a8005542c62204122542003044008070081250000c81d41c0740805607008141d01c40b990034000300c1c1d0064141d103e01c007201c00307070383d01c5a00e048040c0c48081020705441481c000c0d80444141200701606140004011036010742c11300c41c003e650b4410f201070802c520003400c000d190240c1e11202407107403030074020550016021074000c1101c5599500040705140705120090080740540000340e0720900a0004107003807078111050b0380d500c5508606107502d039070044031075201c010f07042449a0042c0c2494401c0c10700d07046440c40f0f9585031040503100c2c182d5414005010300b0210140440780090101204003601000195800140c1c80c0c4528038500e10070f680824065900544c9484400c20070f00341c0c055003004500d00c00c10000180d035085100500300c0301c8040303164103400c404071110720411280c499009040d20b5000b030360108008001c0c1c10301d640c2070f48118 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 774296825 1250 774295575 774295591
    0xc03070c150804110f12010c031104081e010e0f071a03010b0a081008102903030906160b0f07081008250302090a0e16030812070309050a050d1205 64
    0x1810000340054513200c3c10052a180c0100070015080304a00011103204280c1c40c84d00042c1d4440c0300303488005803d40030f940d5a080742e160240d8241410000d44903991501e415200c00c10b500e911550408403002075110030f00d4030308070400341c510041c080e400340c9640c0c04003841041540d0855046031040c0403010000d5034141d03803258100503d032241b100070445001c2d00243c000022400d0210000517001803c02021040e100e4010300480e00901201c0b07a090082800101080d00250394603203094555004401c440c0c0d03c60b0101e4280d5110005155019440691884000c05041800041c00a00e0f4003842d055440340c00a0740e11481c86541d400082c42c01c454443c8110040c0b540300b0203134101000801c0d126040902c26109201c12000d030382c0e40006103001000d0341c0c001d0005a8800400c3c5440ca0140020107c400110f2010700c112032075179460300c01c50320803880507400f01c050f8a008180070610030740204070110781180440f10030402c40c0c2003141e141d4002840d154040b403000d41d10b0030400b40ca07a014151040c019 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 774298075 1250 774296825 774296837
    0x503100522110904200609060301031e0f0f02040e0c0904080d0f06150e010903050705010503180f062211040507030b06030108160609120f020a05060c03070c15 70
    0x7400c0c014080005112045401c1649000d05101940310554254030580c0038400080801004640c0c1600000400304114014003007048810380d02e071184003c680c110784d4001100703002051400e1940740030414645000345650b0030128460284007160301c1c28440305000f100d080000301c0f44106e02568450035007106a802500040020703005c82c1c480c038082d210a4002c040041040718040c1c40a000f00d80340364012100700410008603d0f11150700c80b26141080c0320a00342004810f003181c6800390b49401610035241000300000004420401607400d00160f61f04005c1200ca641c140c0c40f1040f07442e041e0841e240140707000c1184608014a41c24488068181e0304261180403031b007082e20610000c5c100050040c03052544030001160142c036403200860080203502c0280203903c02c0c0007042805220590f0028040004086041c800110041003168400364080300c010403020640c4045810504130f036204a0780000003050801d52100e010000705401341c420345105031000d13219030034146143e44000d403540c00549 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 774299325 1250 774298075 774298111
    0x30317090c091503011518020322060612050a02040b0415050103050406022b05010902130915050402040914093c0a0305040303170421051c0605031005 66
    0x51151041d50045400324a05028112031404030b82560050071040e42d810700082800c01a00202104001182c7c0c042c05c400e5103141002c10a9a9020503048000700c0e8181c40101ca03007040086541c401c0000382480050301c000107880e07042854607912000d109034052820701c0d10102e80d600d0a4415030141c0300c000e400d00d5101500307000c011030040000070b0007200e10a41c200301900c08004155208901046482821750743d2805030081c4800740c0c2c1041c1d02101d4028010702c596a8000255840384050b203000960009050081d51072181d00d4030001c3e802140c01c1440010301140c1080e203a0072030320b50b6800e5018016855100c555031165034645540c1146406030b27200d0003408610031215a858124a088408400a50340e010442402c04800d030000300d010420004003082019000102c105441c18035031103a012925154591240700e200b020400050072908200881c0d60758081c009848022240c5104061410948045540103041900800d0301c00d1242040300b04011240c0e000701841134150149100c0520 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 774300575 1250 774299325 774299329
    0x7231903150b1605070b0318060f040f02010c12030515030f1203100914040b0601020613081309061d010509010f15030e060a0c080702030a05251704030317090c 70
    0x60041043c1c2c02c42c1c21090502c80b0b0110707004005040240c056100120b40d41e04060100390f00440481c0d100300f16a42001d020080e1486400c0900c0e584283c00040c00d0400024500c0121407191095030f000f0141d07044035280d40e054035416030009104007500c0010503001000e2078209551280c0e00da0040341c19501150750406103403103081c06560401e05985010300c881d91201c50b100c042da00c02906000782142407000300300034041340c0001590403041c28006800141444107130301054003d10a006000e00c403000590a0000d10040c9503080180028642000701a071246800f402030a80010b52400c56145e610000c200c500c1c1c0f44e203244d812078055945281e9054a003580400790080c000d400441415522038150320b40d0401400200d10a41032000f000900c80e11409016210000141c2020215441884a507030110341007803c071800e050840700d103442200800c100160803101601c1c07008180741c0e180c030f038a1aa81503482d0050400d0303034825141c00801715126210100f05050803103175031143d83c3c402a19040302d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 774301825 1250 774300575 774300577
    0x10f0b1c0906020408121315050706050705041d4015050718241b0f0302150601030b010c03050327101a0f0907231903150b 54
    0x552040b0005810559103100003814015201180c94a06000161402080c00c6409480015152603104d4020b0101c80050040c168011a04020440f0f42d4400100d85024080c00950b4010100ea961404054403184010024203006540303110740030b40782400014154070303140301071070300140000c260030094000c280300c82c03035100c59621090b18030341d0343c0c420404041c1119005da14410314450300d4081d080303d64200c0013284000e01e40c0c050a100022501e408007681d00c000301680d040740704ca1a00d4a581251040d0600921503000401040c0d802580002c208040c4c021501e8044101e5520410304181d5170300c80194151190208075a000501c81d08210000a014030041d5030425492112070300c0398803901281e0f05541c0280103040365584d01c41da8490003d0312080c0aa00403045800203140902c1d0614000304e400743c040c16000e41c0c490f004032030000d03884a01c0b40207091220407d03400035180515024070000b445600000703039031000454082024078601d01030700070b80c440e28801481e03100d61245400500101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 774303075 1250 774301825 774301841
    0xc18120c1306150c051501080606040207140303090f0607020f0601150509031e0106050607020d060207020102030d0f02191b08030c0c030408010b0337032105010f0b1c 73
    0x4a140c0d6140b0208814607280281c000d00f0308191100c0344208150704201d131910011078084a84104c0c3d440052150300da0200f400d5801c0034042e00c2c00341c0c640c51185410300700c1c5040001680445c1c440801003104a41000900344aa0450201070b250107440380d00003261140c5845034401340c1c1d80d108100400ca0032075010380c070030340d14020361600508103040302002a040611024203040c0c803200b90318603085c5080080c842e280007030100f00d884500e404402e5000c540307010040798003c0c04040d03000c1440419a4002d100b01c0d101004030030340c100000102984481c00a400c0811340081c101909854003030b02c0e500520451038124002a0280404a030540d51024190b000030020011418240408280d507c0c040000d080500410000403684502203014180340404d1200316104a0030800d00742a04124170f6070320600281d4628035607600c60400c03810141c500c5a040a046014140c03c000d01742408142e55010307906a0700c00410321005076a0394100c0303950500840b20070700712000c071142641d401e5003095445000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 774304325 1250 774303075 774303109
    0xf110f09040b1f0503011d0115060c11041503081804140f152215050105040e0903090d1203050f0c0919081c080c04180b0d020402030c18120c 62
    0x1a0a03a11040424203541890204944d00701a5505890207401c0038028099a039120001d9030703800d1454501c0086c241d1110390005800c03034030701424101194a0b03a8001c00c0c90030b0ec520725000b8101d50b891418078250703401150025040e94011200710348610341070103641c4103103510200044071500c641d0400001200c01500103851031446000290340d6071513484031007520311160554030f44244003410008081e03803d58031031455080c00f41d000038421a81c100c400d4406403900841500788036078070300203010310314418038040507484001e0760f0880d0100700f14800c0790b5055010550301030290341c032400003060701c400c42500c41d003106160900c2540702c0741c2418052242c038004894040f0039082d6480f0b0100341031400c07003142d1224803040d0b41c41d000314154101c8039aa400c14000c10810385050302d092564450100c1651400c644e990300c0e00e84658459680c4014100626001441103559040c2002d10070900c0e4042c2006845840000000c500c1e58603240e00715030810f20000028140070303504070040003404000e40c1440c1d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 774305575 1250 774304325 774304381
    0x160b0702010f1115150f03120319060909110310270503160501061502031e09030c0a060e0a060306030503040302120312090d0809010e0c090709030f110f09040b 70
    0x128052043d132506034041e511804400c142a40c0c01c03001e00c01d004640340225800b03544181e10f00c1d0b188405600031203900c941210b010b074440d112a2503c640103441940d0000c01070034104480c09003840240f040c42070965130300714219024000c481c000801551462215016200030108c40101c0801c24606c420091500c0341c400d8910749580b4140030440e403140324070280d03101da6480b1814006c05e428207030101c03100b1505000640c10440404800d48802610a070641440003000c80c2c88066600e080010450b456030080c200c1c8046510382c1e400808460b51141c40070f100750f4145100041c080d0003449041d054a401c18051440c05080d0380034840894940320408111b40300c00c00000440f0440d008515025907840703400b4200242c25508011310504010f00511516490b05424410101002030003c000080079a00311003940c0c0c03001d10540b0890300e1940041d007004800031907030040104880a80e55030010440c0e1903401009a24180220b800303046130014404002d0718080b8a000c50009018801d40f90441000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 774306825 1250 774305575 774305593
    0xf01030906021201031e0803041209080a032a050a020f031f060602060708070503070c02060f1305040e0109020102210d02040b21070c02190f08160b0702010f11 70
    0x844202e0f40042214140e09001c600140208820209002440203104030781100c0c50815484908851002078001404100b000c00510925405044820010020102658889155414082c01d409a030758040c01c004071004440105aa41d4085d044064503001002014480c1440d42403020050082141c01c0e4144107401030001e40c00319401c503070f0302d10700550500850010f1401d00c001e89445c174044e00c0c45042c02500010004100d90020540780d021000d450200c074002d03e1400032450302e1045502c62820460001040b8030780c2d4201ea082c0c08200c0390140d80070040c214811458130b081b02c041c21070090060704014612030b03440300c0d240441301c07030010300360300c0545080980aa51070881c2d10907481030f241c6900100702a210048040d42c824420421116917a42d5072502100c010046070480d54000c0c0702e82e2018410605400c00c1200c004043d18001d0080d24070f25844104842e0b80c0c2115104041d551103a0740000720b1010403000540d6045541a1158060702100c00425034100d81034403808440d6100304550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 774308075 1250 774306825 774306833
    0x10b0f040618110f0a0207080105060d0305071b091a030f03030402100809070807030609060f0501050a0b0d090204050a05040507300516060914030f030a0806120a050616030b030703020f010309 84
    0x20701445c01c20390001c04042c1e150102241c25910020540c92041d01420901000b0a8004007101d490547c01900064424280e10200c1c51040342078200b02111890030302900680142c0070103164010200310100c3c2e0f40c20040d4130016580340300807500290000c141080e20502240541011034001400400340c0b14220384590040c0c0c031f0f210310741d441130f5042c039241c01c005c03005d201080c1305080d100039004000340010741c1803074080749648072144189030200400091855100c0032607808804540d80c010400d1140e420003201a801424065030191054054140001031030b0410410500e2004014840310002e00f416000205014414003030075107440c007412698081c508440350078400580580d071550904e00341007060f41109008000760450081d440242e04550b4428000150740681c02d04d4680407032556500e00c0441c05045546845403201d2140f0701d40e040c100300010460503c600d500c06c042210460400c00e08500340c800c4c020480d41c0581142c141400981004090400d0030070040c1400306803944c8a9403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 774309325 1250 774308075 774308077
    0xf060f0f0b03012a1e0f0e0d020a03080313020a030c0812070b040303050c04180c020705060f121e091011040e040212011509091b03080a03230108010b0f040618110f 72
    0x11704000100c50300482c001c03160700640c616400301c3c400c0d44d4104001e41c00764082030a0f0b0415000181c02004084002a0207264400c5903194035940a08083c026a03170b07920340103442980d00e000d001410701035040998503160841c0d09445441d03400a0300c01c00107444070788041e4010300010b445500301c0b84040001040350000001c4009400b80310000c0000d00b00601c80c4000d060010580046103e4081001a0465090b20406482e032481e8044448046034550300c00303510010030308040e441040304420003006100c00d03000c00c66548895860700180168150304100c200940b04030301a03100490304000c089030150401182da010381980a00000500100300c0400300d00042c01980490111b5450780500d40420080102c42d00b515a526200003250078207507500d6074814002c01030000308040d07540c816500d600c40f11180d5040800020174042001d035846812150185c004c1a03031a601403044503a1031030184c100741c400c6408407a01c042950f8008020801d40d48098044000300320900c503402e00000c070707900d01c500c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 774310575 1250 774309325 774309377
    0x2060711030a17030708160c030e030c180115030b0901061b0b15030c030318120102090603010b2107020d0e0a080d0806010f03020f0409090f060f0f0b03012a 69
    0x350700f041d140c0c07601590041503800c004080100029031104540442030700000818101e982c141420010f55000342c020034a0810081072403907015102c1840a04085010b1807520f042c0d600001c03003801c07803400700315083d001e68500e004140c0c3c110383d1200040103042d11031841c80c4801d660038510001c4405981e180d2041040c0c054401180c509082c19080480703103020007038024214400d0300a0742c01d10711038207031105d039604141c00110300942490000048000c1b013981110380004000f0005a00c039619511244425003003410703401c421100c260407502401109541007171144400d5401003c0120b20720400b112481e80c3d901c405a0004400000442d0600c8140000c00c040059540c401e0f1803464160b0004000301501c000000c00e151041040702c0500c0c3e00001100c0540d207203a81d01155000043c5090a0011024003016221a00d03148000c41203202c55000013086080e1084140444101e00f0201400c03180e0582004c0000807601d681519880403000242080350300d181000c020300d501050151128000d00c13 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 774311825 1250 774310575 774310613
    0x50a082d1305150901030b03030d1e0b0609240c0105040501020a02060c03151903060c02010b0a0902120609040609080a0f09140609220c0215070c02060711030a 70
    0x104201001050408040008150444500904483c0c02168052522070f4a00b000d0415132a9030000702c940c0c504100b19801140c40450410856030300620f8407400040e1601d005a00302d05240b85210341e0701d0144144c0306005c000500c4a804000e41e002101103850b56490514035080c02030044204580080c8911845075015000141e550310306024020f091450052481c2e4504800b401408031681d11000f00303081a03002540c1c802c001410742c01090f040d106240d4001050346082c00c03400e480c000c1d4107400401c0c3c5110261024941680c0702c601000507401029034007400b100580c0c0028003540351000c84070b82c001c0c6c000c10001503081260b84800f8608e6007c000c0900209070035844942d071181d03200c105040108007038000c90380510040400203505204640440340304403920800244a071345885d96840100d4090348080200314081c0d034001e0745440c0c10f005540398075040340ac0000ca500f406001001042d40d0300030280ca1074101d0a546001e107400d5a40f0076160188101e00d04880010010380ca862420b00b91 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 774313075 1250 774311825 774311827
    0x301090809030c0a0312050706020f0301060c0b10062a0209280c0909020a200706170f0402060a02031207051207090819170708030f010f03050a082d 65
    0x8101c01d0603c0c10381c00c8941c1501031442500c0410108402112030310b0100c01c00d10740700360780301028104a4040d000d40d40003510759030300c000000904a500702003401d0a25105410124a070340d10a8408466003509100701e10200d000030701c1400028106400320100c00002c05c04816042540f0f8000c0340c00600100c41041e1000d059800c102c0c0724a2040d4080380100b145840e042c03101500039107000f00308200701d1181086140c0c002c45c08220160151102d1000066648c42d038500c40f155070b90607140d51740d505200e4100400c5541c0c92243d00d0040003120948070b400d034a030030000c050312664240047ca0b4825040c8000314001801b220706043d000581d410300683e11660340760740303490140000703901098024003001c003880b415138800c01c4444408284010001e000b070740411035030b07110707070420454181080001c600400d0300086e00008100150000e98000c4882d00b144c120b041e030700c0358021090a0070391702010380540d00405200001500e4000100014440300408070b401d040c411200c0101841750100701044079070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 774314325 1250 774313075 774313087
    0x9040506072706271802090d0515011406130308072d1e05060123040219090608040503121b030a060608062b0f050d02010b011403040b150f03010908 65
    0x12440484d820400b0581016083d86450b0a200c07260b408603000400d0207494010464420981d104481c5c00c00c019041420b0702c0c010f501d406e151105400c800d018150b6889184107503070b0182e0620308243d41c1d151040c80346501c030b07490450b15038180941203c207080b101c8409080700705d1103540510f01da01800c046c0b003041c81e00340f0300124a4413801c1c01c0c40d8040c41c1241012021a1980401d0001881504480e1150801060411812580d104a585082400d030300940001000581601c10131011504d8000e10340d9034500c15034840714211100101580d02400942c02030015441d051003d1005030742141d000f80017a001c020488082045a80085401e540031382c0da02c800400c5225081150300c0e0340700c4030403107440004001c00d641d1030042503450340709808401032a2000004200c40081c4008580d90840100d032404e00c04d00e04000c1c00b0703203001512280060070900201c11040d07c005c060b00d00a81e40213140c03140c103950310f441c0c0c603620b0034584510641c00001c210404072151028880c1c003d070f540c040c6401e0b0342d0f110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 774315575 1250 774314325 774314357
    0xc070f0f1712190e010e1b0d0f17090a060c05210406052d0c070603020918060102120c10180809060307090504060b0a030b09040506072706 61
    0x1041c4144580c15038034108500d20740740200c090050f6219640300600305408800202d4000145550f070704024443d803811902181342140040c448000d150500131440001c0c1c05102840501c140da0350000307165409001c440030000c0e50f0500c2d482080c4001c028120701381050b4100013241141254400004244021001001e118052009868014004c106010b00340c00c1110580d046205130300c158401c009011a5901641100c02e51030303900c1c1d410001c2d001c000140b10704280c40e066800042001201c1c270480c000010031902034007e0320001e00300105030326410314a0403d201603100c401020507045008286e400c0d2034540300a0301030b21700300b28060018000110891414001c03075141141914071540c1c0d0281181c0010410f03011501d41d01d10555000c0d44075102c042c8281c5081c4051341040e540541840c2012801342e02d18400341c440040fa0303560921a51000d20284100c0384030659003d400e81e04100001501c581c0508030108110ba441c560010016040d80300907103009416811600004145110408001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 774316825 1250 774315575 774315593
    0x41208060909061b070c090219020f0a02270106020606040e0c0a06111204060509011214040209060d020d0507080607050301061707113009060f030c070f0f 68
    0x40800e07180301c031a90400040255582c64004c0100307102d8403070070342d0324400280383c441625020f80c0d0092404a10700e0b160400c042c0a500601094a5294824449a60010300c00507241e801071040c40051b080394401c41c0c080c0415402c000024008121510700c444150601c0415141c2c02080030f0f0b4080d02241c10440100004d13600720320142c0d1000d502900c002c4101d66a809038400454000c1d04002c08000b8070240100d04000140d103501c4030294011400180382600500182928071003640e501e098003158410f00c1044130781d17101c051407241031000001001410f0201c020341e0040300062448213405115400200d900922710400c0711250402c003801c010070f07031081110030741003041824050f0443d8105a0300074414403001d6904c41e40505003d000c1031119000342d0420203000360700400d42d0304010a20203078210003241d65820454560055000352441c07420401603c404190092080c0e2a00c0c00c400c40200c80780d0005000c030912074004100a0000130802e40e02c01c1d408078403c40c1d1006500800e810700483c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 774318075 1250 774316825 774316831
    0x109030f0308040c1401050f0c1501060503070314070807030b0f030a110901080304030305190c0b09010c140c070909050c0d050604060e01180605101e1e06050f03040812041208 77
    0x180b07105d4400b684a90781c000003600c070740100800c00c5644800140320041c0c5404120b03640900c203030015070004140c2d00d520900852065080c0d072800d204440042c1402e900003081122400c0002d100140441c0e0b04601ca5040907400810040c20189001e0405000078184092011b040303643c800402c01c0700141e13040101500340123145a01c080c0d8202490b50b140a415807084640542121010198824410340907185019010350084040d0030710b450045e861500030b2080000c0000450620b5106d901c0741c007500f5003210501d00150019000140c40c21b20b640019210b8114200d0390b0780502002541c5988400c804141c12500880040030242001d042035011540b0b00341d5039401a0341400b9084da4903e00403030705070402e072794000790000b100d0755a030240400c20200c81e048150a08103c10040c001c01200380c0031041501c202c4841008004000b070002019501ca5200e4440410000e201c0f18450b454900059a4098060341900c0d207402d24247e105406114201d034200d0f12031201c0308001c00580e44c000300c0343c1c1c0c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 774319325 1250 774318075 774318089
    0xb040c0e2a040509070809031312060b040e07170f06070c0c060e0d0f141f0b0603060a0e070c051501090f0b030705270114030c09070504090b0109030f0308040c 70
    0x715050614001c034084244c0104948180714030000845d40026040048403821806020690503c2d074842d189200c1c020507030081a00c00754200322125141d031800d48142c0300d40c4040f4500038001e007440e0041800e40c1c1c0081030f5861609015414408446110510070305200e040140d403a28042101d07031815590066030b0390807407807c04c4420b6511b1400343c1c07142d00088203c3c54126055000740c21b410700d0800f010002407000c1c54100e0182280c0d5280100e84007403116020b00c1030010038003a031219001801300d103001c1199a142e018080f4a01003050012804540b07400a00900e0040081504ea40f561440c02c0b107826920041003200a004001c1c00f1218070801120b42441102840322250342c0c03000998488403800342c5807240d034003008c1023a034101001a49148010303066044404645c2d641d2008042603401c1544c26000e4016102036603039510385140058881e08044d1142401c090a0034490002443c070611141d0500c200c0c000b0202c08683d1032544a900f140c400c4d03480120341d16092a103a10003124942c0030038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 774320575 1250 774319325 774319327
    0x108060f012603070b01300b0744190e0c1201020304020f0922020303090402180a090204151805060703080103030e06070f0b040c0e2a 59
    0x10561040358205241115040800c1c20102030800384090103007078445200e102948000100f80d001c1154944400e8100c400d54116101929482d100128400440b49551200c1044a5001c2c07000249117903d0745400400514280116014560300c040d0078410195507a51810b400440c400104000d101601204080c0c1c11803580840c1000c40010300741100d19000303461040c0e245c00341071100c40400c016036050007000600038002e140da0311000c00c0c000d520641781a4060a00c280e003800407800c0804025009078902000c0c0d800e00884001d000e0305440c10900c1c00c981c940004c1007a40071980d9107001404c4049509810203401c00320210030070001c2902c0e680501d04250050108200300b0032100f0440140d5113140c01c0c60914009003071010f030141407040c2c02280e0701101c0460800c2c1410790100205050ba4820f880d00010409101c1c10040540039045000740341e62500c09a005c00500c040d041190401e104504507003043c0d0b11613400802d651030448091a03203164280f00040c40088640c0c01c04140c82021043e2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 774321825 1250 774320575 774320581
    0xc1505090402030403110330010f05060705010b2205090d02061f0f1d0c1602100507052a040603151e0905160b16141005041505010806 59
    0x1514601a244a00c1e100355400b100040501d4020241d550000030040e003901c1d5250b050070040300e418202050407022100540c0a0b02803000501405076050b510f000c0c185044040c40e0804000b4160b000400407103481d5200e210021040c0c450b41c43c40f05a02c030001e46400c0c40000900214411900e0050075400c9650001c20089091500407900e1a0060301843e0011180c00d01480300042c42112a40319a03003d0754042400240c45803c110b0201500e9100c100710046c9480c0c1425843d000d000d1504100b0141c03480e03007800303001031a01500c04550071466040250500425403500e40c00c0284200016802c2c1202e030301e0100080503401104a064842250200285421903c0d008000d40c2e50000d205031096032a02c5880d030f044000409002c02d5840001c0c1400305506602d000c43e101e1a40609112107149041404281d90300150240e03254400e10760f10b511040d42040d2200b0301c50081c001000754150141705409840e100341740c002c2a01c924040d00d1491000e8400e038078180d040741c005908c200c034650001da040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 774323075 1250 774321825 774321827
    0x61012030207090624080f24031002040801050606070c05041e14040c080a1a180304060513050a03120e040f0c09080d0801030c1215050a0b01090b0a020a14010b0a060203070c15 77
    0x461a081111a22340c03004422501e44001c10402182c03441903070510071945144401000c540007072040e28140002800319841d00e2040c0070175406012001480ca42e602e03e801e00c8241800d5201e000c10f81c6909481c540350313080d20500b2400f268071141140108000341420030040c0300340401c80324010840d2000802c0100780c185c50303074516050a420301d0b509849480c1c011880d00141001c0a901c9903240c0d009507681c0715640c00003d0210790090003a66030098581500085a02d40600400f00316a0080c003555861180804204c544000c3c0d1802c40e98001d40e2840c1c540c074041c07941d104141e803107401c640300c03156004c0c01c094070540340120700c20340e8800700001c200041c00010305444aa00840b00051552084100240f5141d51200504e200004090b4a824200b103a100d41c0c542000446020a032164001a511034102c8001481000440f40259005a45100001da402c1c031041c90316407580f07c0001050020100017a4100c0d40a500c0800181c0c0301145000c14480800070700e4000700b65000c480c4142022802e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 774324325 1250 774323075 774323101
    0x91c02030d02061b090a0515073e04091b090501050607080703300603021f02030f090411040303020106061d09060d0503070203010507050a090806101203020709062408 73
    0x55640c002132010442c22001e4403652021406082c0091841801d40300ca10a240415007200714143d51516080c03501800803469401002d10003105981840c0361141f0018081c501381980031b05490f0001e03641c80e02400031500040b004100205e4840245100781d19000c080c1040e6181a08606d00c252000c0040301d0010b03613054103e86095230b150600d14000076080c0c2c464000100825980501c081844d007141c180006c00da8003010559200b118078111001d200803241c09403140040f008070160b8404c110b60010b03000014060076213084024004108101031070034a056940140c1d0046001d85c2d140c1d1818000a0b400c04520200001c41840b00400110300e40d00180038580041c01c610f0080c0c104400c1c84007840700038021a20403a801a0080c011030410b8200149070354800d040c4640050040b10011916030f20202e01c49001d48600c00484010500b00340d03c02d400c00205c20011403c1d48908000060301c0700d9140030720401410b00d0300f62556212000b101c402448000d4100c00020800c0300c004010305112412 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 774325575 1250 774324325 774324361
    0x504050d025118090606070c080303090706020a0b0a020a030608030a020c090702030702030c0f2b0303140702033c07060b040510031205091c02030d0206 67
    0x2240052401c0300303060b0003000041030590706811009100940d141180b0201414541c038510050642004518458100014066008201c1004900c4604500945009015183c10040003402c2d245400c400b5520004034002c07032760201050350808810001118400d00c40c5000900090000c1c10010585544070f0031084001424100704d41e0f0301098202d000e0744698001809403012100b100d98400c10240c004e07545000d8410030030701c0b5280137400585010b1010064800465026004041c8003c42c9010801500c411044c00b94002031a4201102c50141c1c0046074911110101070740c0d42c045095084c01400d84500071051480300e44514140802141d000044400c100c469480b20b401c90580f082451942011052428030140340c2041300c0c0c0840040e002c002e091043c0700744010001140801c080c401500c00803142081849100001040462800100710052209900d01140342414081c00528a00304408155200241d4001903200b1800c04004008092241d400203004d00c1c82c0c07400315542892484 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 774326825 1250 774325575 774325579
    0x90c050a0b030109180f0b04020f04020f180d020d0c18151403010b09100905011d011511010c0503010810060b0a0e040209030102070308040218070806060702010e090702030a030c0504050d02 83
    0x240c8200300d640d802c1042c1900310a911000b611b844010350704001445541c1a00d00303138807418070110b104075103140910842d2490344400454504280300f00f40f01d2410038051955075138106039000100340051342c6945807030180c18802c0b510151000d0900709541000c82c2e50180e1584447e03d005007180c101d04610008008652004014130412131440f40841c0c094164520260740083c072807410720542c03440e501410300c2560300c6280108281d80e6a8461440380d0000800603040718009071006200b52200d00040b0700c0040b05604000011561001803582140c00c160b0301d410002d0000700061280000c18004920050610b600034441c1e40e08011141d00d491084503650010f115002d007a40e1130a4803242c0541d40e01c400000e00031900d408490a016065603400c0b101244594036441c0e0160b8115015018103016078940d40d41c20500f95940818400ea513441001e0507814040d0350a07082080790380c0c050310284074444a6001d1130315290040c5001e01035504907840e85040c00010712040c042d64442e801e200c1c00d41a01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 774328075 1250 774326825 774326831
    0x1106070c1403120c18010c080a050f160302010204090c0203090a060834110d0801050103090c181a011110020a0e091003021503060d0209070e040f090c050a0b030109 72
    0x30191691552040c0c52900305a9440f81d01081520755414025101030325440081500c507041542c01100d014a00c0c4000800d01c407814000c504c00c0d580321740040c1500440c10344509140c032000c440d145d05019841201100140e40015042c0200e01180c020240c020301940019401c100d50100000c41c1352039680203035000c010023600001c0388085040401b2080ba1408200c440c4031546a00a06100f86200c04030b440c0070591620b03619100c0200044d88010400a45e034803690583d0078000110081d0400003002d4403207640400002c0b544844408148051706502240000c0b6481c0000c0454a940e0381c2500c402d040c0300c00304083c03489503003000c103441c002d05001c2c410040e40c4041040045e074504465444460b00400c100c8100040054210300c880c00313481c0220b440c1d40900d0f4400009411921080707a1541c1c00034620850100141040c030142500204541041c540c2c0c00320314408182190000b559403031550352141e03030138018400701c00201c402030b100555454a481d1304182004140e440107104d501086a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 774329325 1250 774328075 774328103
    0x7090204053717251217220b040602070b090d05010504080706060b2517210f090307030c060b09010b0301140405060f0607151b1106070c 60
    0x15045000b1840e109420154244162140003903182100303080b0fa2001c141c411140388800c80640710b41d946600319901c0406101e45401d040d41c4041c201c101607070486407a00c1499000c0302c900c03200c90250003903821840903960210ba1030100e4407030809090b40b04181c042c208100500401d40c3c0410900300750394405142c241c2d210031a00c0421003d00c003089001d00700d0b529150a00c005c110b044001070204500480c41800304584400e0041c00a1040000300341f04142400700e10700070b52401c09101c0c03031a140109150100780c4003843c0f8521041c4c0c0840900e17820035851440c00c0b610781e000c403070200c0c4d0000c0e8407401460052070200b4402d5924420554080d0a000c1490b0502040005540114000c40b001500765102035a54690403000340d0020b0264181070440c043c203000b00b81c00e09128607803141c2c0b0300600001ca006241e40620543d54418002540c000c003408412129206d454003480012044030703803a02c000c4000c81080140aa01c02d0f850710b4006400000511207190350185103054900c0d040440d0741c41d1a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 774330575 1250 774329325 774329389
    0xf0221090310021c0501140108040201120c080106090807030b0114120d0e040513020307091a060304080c06010503032b14040506070f0212071101030e0f0a050709020405 74
    0x801080031040d030501c02c1020a20744502d95030050b210030b40b007001000003000840700302c00d0182d40f02401480404141c03411851141d40c403804007a90042d0040c108407110b40c520464003819560301c1d408000c00b040c0d058004003c001d0348008181c0041c40c201001d4101182980d40c0c03002c8502d41032266000035031160642181c5a9909050424412034840840e0007010360000050b0a907401501100d12a070b241100158905030400c000ea945154010050804103040c47d90701c000400d030100c140c20035512030200c100c00603154480107601450140b9001d94448206490051804c02e05030485d82c080d401c188202d080d0b40b2030705507001014000142d80c0c24080e05d030003200d0400400c2030000240d80115881c090000380040401c14900514140e81c44140081c401c0009030b07954040006d502d03280800c10040e2070041004060720440d1130070145808103801401003e00c83c9482c180302d045402c140c1100c0c1c140001c00c8402c21a01d401851855030541c10300c0c0c03170900080c130703410080d00d46902d21044000110b0188 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 774331825 1250 774330575 774330577
    0x1e0a0302040b0408150c0f0a0f120c2319050a030f09141209030a0f17041701060503010b15161523090a02120304270c0f0221 55
    0x103401c001640c1503e9641d00c400159480c05400c5540030320b8202000840d0880104034121341d00c0c01542201c25207445000c48d07044901420081c0b00504004203020b0411a045d801d006130000708040380d6640d010030210040584e01d80380840b01020000758200182d6020301e5103d03440c240d094216081041c4c81c1c43c000401035010b02441660601440e1401c110b4008020070007001c001803501c2c1d0740894a44a030b51000034041c0d0710807603440e0340d8158440040040054601c1e44124010741c03260042032112000e07003a0072140c40d0440d400000c400c8158130700b94025980244240e00003840c04030001d200030710441c80801d0020407004040c0c5908400050b01421225001c400400003551041c891425072400c3d04110009069103c0056141035130b1040d02d40200319084801030080c01024050800e8000030b80c10c0154941c48000307080500c0c0024080085c80041c25070212101c1e00d0000f802400c0020050311580031a42c001d046101801000003440c80703103540c002013510600c40105d840600c1c0758292070740d100003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 774333075 1250 774331825 774331829
    0x2102010e010501090e0c04060506040b2116120b0d030c1112030d0e031e131203090f055a101106070f030906021812031e0a030204 57
    0xe582400c000044124456001c0d44081004000b600c5420b410401044107444051142981c410410321040c003141c1601d49c000c4c058440814200c803035207a406101c12080910444448c20081840c078031410f04960171000c0d450202d8580e5404110100eaa240041d0301d01202840140c100120401840200998520003d002c18001001c40f80300c54082181203a90351f20810500d5100c900f480c0c1e4010401e00004241d80c900201d0380441c80905207140390752003050b0411140b15001030440130f000603640d070760b6440103203160780259207500400e418000303080e6000d040e80d0b0140340038038500107181402004021110790403501c002180200100f20010084c010054140307401c03075540385103513030380908040c01110b190910b4040d00d0301e42c5941680074055900440403600c2075040d0700401c0c0003805142c4625400300421800c0d007030010780760039039481e018100d030052000d001d00d0600f92524141e940c0303411110454030080c01801545090029040040408079a14240004401c007040f041c520038002d405441c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 774334325 1250 774333075 774333101
    0x1150806060918061f08161e09030c2102040c14120901060909030f050307090e01030f03110f0c0f130207051f0c0f050a1809020a0e03010504210201 65
    0x2c3d484600d50080ea02e205040c0d64103441001c44442124002d100d1080f41048044079844202c1299104000c5a0034819040e000e00104404c5514400a01702101c100700000000c550303c078003406085160034640c1a038542c000214004066801000d500340c0e101c0803800c0580e050303a010580071894001034441240a8202d401d007400013081c80070440300000703d0180304443e024001d00c9003a075a490030b0421074202150140010b844500b2810b603142c010390085800c402c10340340a281165a0310700d4403a40c50001c0e0400c40e0740340128920401850341c8500c0084400325000050700130034080c400038503903400e0310096450140d040c00040000c50340d81d06800c0c0e011941880e40030340d0313640100d05e817481c1c440410f0902c80d0300700800c0040a148a01c0c0030320409059058940340c404440700680380035205600840b015108000e020b660201c0b0104100c64031100801c42070801603222a00060003410482c00c4480a90007623140004100100c6e40c21080d00019004089801c8100c010300c0c0380403805003070b0340c01041d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 774335575 1250 774334325 774334339
    0x609020409090317070e060a050d061d061e1002030702090f042303031801090204090302010c0f080f0c0a021e1509010e07090e160902041409011508060609 68
    0x1c1c60a2590000d200d4140700341d4540003240f56140c4203104114041e0b51900009520301a224510f00303118000b880002c1450500f1824541c1c2010350750181e960580041d00c590080007404a001034482c1050758100c1e0040352111010400ba00b405030b542a60b00a8440c8181046203048507454004d1040358440c540107444034045103001c04a030342c1101000d40d01110701c0185000003c5054080c20024800444014040d501e1611a0421101411009244103005543c2c0f030b00f448005a80d507220301130055100780c0009ca001c00782c900c0090400380800100743c060001004c01c01000000c08042c1503803001861004503140c075130a00d004c038580140d012501074040d1184094200c007106c001105450160020003800300c2d540c0c0c042c26107098803454407404c2e029511044090040e0701007034100744200104103044410380d10b43c03605240541010380c0c2c40700c80c1d0b640c2c2c0000c0c24024509100480080c0b020709030381c0808507516200f100e00242902c0000d12041205410200340c02c0c0da1440d08407044480024825 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 774336825 1250 774335575 774335579
    0x110f03010914010608130b0421120c09030302071703070206120a050a090f02011133011203170406110406030c020c03061e09070803040e090f121c06090204 68
    0x20701e0003041d000c8660a9540d0303415000064040c0b155060510030203500d80700308001003255036000700440c0003400484100808621100c40708861198040c801c00d031031344e0303400c40c2c141c18580910111681250b000d81000700d504802d10100e0f40015001c3c08664000041d4500e0070002d0300190708500803024003d500000002d424031803450304903405400b90549160400c025118203910804480711700500814207102010700c0405980981c0c1d521120203408000d07509800503203044080c0c0c6000d00c4144540c1c0841c200040c410807902034004034050803010b80c02f600c40900c0c6440140003000162130500300010503d000404008442d040020f44054160a60707484544801c0003a000c0c04581e003002e00140f14a020b00c028510300060802d000d100030740030007040c070b0211a01d045880032000b0f05c3d00106100b00b0100161005041006000501c20100c1610741800e192203041e007821045074443d59107900030084003103240a840101d841c501e8100c95403600b401124080c030700191069902c01000a8404240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 774338075 1250 774336825 774336839
    0x40c0b03041505060604062c040c02030a1403060315070c02040c0302040519150302181c03080702070305060105040507020a06090b060117100902210c040612021804110f0301 76
    0x84146000c2c410310305000ea9950342c07007400720070b00642c892900020001030008075060010100000c11192400b81c074007038446403001241c140c0b559882d128005920020744c40750101e5201841180d00a40300c0c0e4064610b00b40080081d60310f102d0b00c2c01f242558500d18003c500d406009072500648030354042c0003440340c0c0008200103002500207105460294501c0c001180d10000402070a00c242c0e000d10102c00340003c010305044000350411a0300c294002168811140c2035581c0e900c00c20202c104602058440000034500249500d4001e090741d025507000c1070007800014008104175040d104156000900d5545004040b890302c14000c4015010b0b0340307005d51607824000c000c2022449080c083e2545880d00f20000d10701d110000045800001049540b2401e22828245400410360082e03011031580c2020340708080b0b40100a0300350b03915215404000341c100489600719200701c02c0b00b81c02d40700441c01c082e8207408608440c220003d00c3c0d4402c07035880c11407808018400f8192070340051080c116070303103a60315458 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 774339325 1250 774338075 774338093
    0x14030301030606080c0d11041104080109060c020d02030406030b1f0305010905010b180906060c03030907030203061509040f02060f0408100e010e0706030e0304030f110103140c040b03040c0b0304 85
    0x402d50340103052030404148a0f01c0041c5c4156a41005410507280d0300d0503494205c12800a401001e52094840e030f044d04540d107805010b03002412501000045402c1e0364a0f21000300d8919086400941d040084080110f80d00407055070121911030501052110b41071001450503800d2010802c48001c082e400c601085901d5880981a10081c990400c41e0f80d0721000d1400c980e01402d18060dc2005280c03d5840403410040d020035089a005010281000024052242503400485030b058030faa10001d010002d42c0b07402c0000c15000301c5000f180ca960503c410000c518528801803001d4a20791400520000f1074a610084403034180d80d045070552101d8030b407202251501070030307082c9003c1107061a0b1602500801841007481c0028a1801021b41600d450b0058015000442501400340024880000070543c004101032100c0d2281c0448181c1103800e200250444030410828030032501513008000c43d03030b0044412202a9221180c4203a02c1c0ea40e14646500703105229003004240c800003006000820241c1c3c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 774340575 1250 774339325 774339329
    0x8251a190207060902121618090c0806090d080103122001050106091d0106020c0d06020405060703050a030516020303130c0302040e031207210246030608101814030301 73
    0x3101001c46d440c905410650310f1201c400500510740e281401000526480300700341c0c0286541c0d08021680301000c0c2c40300c810120140d4004011a002031081142d00d12003801241407804140c01d01802c0e950641d102d4010800c1580020030078403041341100e184c020710031008182060720307010081c48550b85544005186c84081c1c07180d44601d5a40801c0032820481010034203040c5e030040d40c014141c1ca201d6000b00003020400d1141900c0e0755030b0810010903251260402040c0a90090710703000d40c0c030341c007540008040f0750740180203074401c140b00e06413a5143c650210880303820081d00ca0200080c4109403c1032012a0501ea0000754003903e00704189105050110242064200d03520854426640d005c50030741d140070340022200d0440710104010078085500c1c4c0e01420b00505030305810f41410f2000d19a0946801210680c0c02c01c09222818141e00d07035010004900c03c40c12280f4042c0701b400c0c500b02250b80e41301d14558440c803019441d51255003840300003d2003d614650040320140003000c249034510b031a41d0082c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 774341825 1250 774340575 774340579
    0x905010b401a030c03040f03050403050a0605071d1e0118030b060103050601090311060a200a0c0906180209030109170a020c090106050d0e0c0d08251a190207060902 72
    0x59036000b0155004901524810b02c110900c0302c0ca1690742e5a10304c042140c14540480c14070909100c08404160108030f400d0709603100300000551401c0c00360002e00384203a48204500c01c42403000d0240080c0d200c0c1034590b000c036042160f00c2000b00c00080016103222981d40b40204c07000d45000c80000521060000d024000c0300c081c0ca0400403502c440c801150407200d45e000243c03850450310a54010381c1402c0000740082500e610309a58548404101460250780007641e90902d6400380c956441803041189004c0300400a20804101c882d180150fa00c052030207072440d04403080d40c007090343c1c8050345007034203c9681940c1c0000551441e100034802c098294102c01100401807282001e0300e8001d081096406058a0054407030382d092218070503070b03036001e000300300e00b2200180280000c03130300240c445000315141103101e46200d50716000c0c0700800103454004502c0c050a1084112201408640d002d22802801610500b103487c5568030687c004460981074034070000000d100044002c288000c90f80300c80c40003482 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 774343075 1250 774341825 774341849
    0xa03030221010803041809060207030f0801061110020c030d090b0117010c0905060702040603020a0b0a031b091806051815120d05090a08060a020a090905010b40 70
    0x3407009541600024058206250320802041c01784d240c40700064200240c035103001050340c07d066179032038007039810540007100400d144078146000c950300035201c540546054034000c25062010241c4554070a1141806581d880e400114402c0f84801401103403105603564a091012103d00d181c40319040900348a2079032000002088050000d2040c0144407400d00d844e92203540141c20042002030380e13405104101da2080d40d0300c5000005032241342c4008014990044107a0302d80d4103181014090f07882807a60f0703108514030801604c040301d800000c80c0c2e040e51400344e20001145802c01d082801816160072090381b21500410702c0310148141105288110340788110080e00210f1801031000d111034804070040c060b04001c00501c4050700c84c2000d049040c00090403003102076a6a104c07103092000560f051109031342c00103a041d42c2c0e03581094a11004123100c1c0030401140d0715025040b80c0d50700846040300b02010124102204e07c0030324010206580d0a6084201c0546c0d03d00d00c405000c0e20000d2046000e8a11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 774344325 1250 774343075 774343117
    0x9090c04150e16120b0306150d150b04180f03081f090c120e060c0c01090b150405180703121205160f030603030c0f0c0e0a0f05060a0602031e04080a030302 68
    0x213007405400c03100c1c4000f80c014007050f104c3c42150000c0d1040b2804064001d8002103140e03011405c0c603062401c0340c030903501001850746801403c1c4802da890740d024043c88141c0080780c40c800200f00000c0c40c83d10540520340782e4581d8603103005805201045124242c0014400140424902160307440303464024919115000202140c02060341922514070800115420200018800b8002d0030010503d440800d0000104000d49a4822014440070381c2d120022030002440d212142c1094400c4a8000950310450b0110125041940f40d8603807060100a11303101012107020101800f40b1a40300201c044400244403601d01412009682e00b082035140c0300141c205694002ca40e0f009110307234401e80350165582c903d80e00090321034942d0070404500403078000c1030300040044c285440d8100903000d160140c0d008540c1152403080c01d01a90f2020348100e208884d0340300100001ca8001007140e1440801c4441c2d0040e94100c220100c465000b00c1d801000c460203008401e60815600d0303801069030719409511101c0c500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 774345575 1250 774344325 774344357
    0x10303020708100e060f04050f10090b060609032e060605070506070906050405121c05070b060612060f040b0909160906030201091206090804030b0a0b09090c04150e16 73
    0xd1404e0300700d400b20b401c0200410701e00164070300710390741c0140141c0488840c0400c10ba840c5281200b00c0b100700740895a1000d51000700b2603a40c140b5a0082c0007220b01071b08240c82c01002a44507241c000c00e1b1125010494040400c1e5401d082c00a00a11249101000103c3c0d03180000b4001e580041021201801000d0019403420f00a203032150940d2078507620a41004e0610040c40340c01d03098105640654420007080c12400c0001001d005020180350340c2d09921030041c0d182c01e000311070003c0d0110b2310803441030003c02074500340c0c1d044481d0b003c242140d00b01008042d04010400504c4015451a040145081040488000018503101c0d1030070911210340d429a4880b419406c517901400024001901c0034020070015220441181d2980e0003180000342501855039844060340c02580101c0b41c070084402000f00f01e0700144100402c500040d80c0c0300140b8500440c007141c403485035150306440f071a542d440c0b25241006803c0160041c004260304010f09040074980746814000d0241106c0001d88006200c410503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 774346825 1250 774345575 774345581
    0x3020c0108071b0f060213150e01121805012c01051308031f1d0a0203070801090218060d151502060a0c12020a0c0b1b1602010e0901030302070810 64
    0xb800071503494025888400140503001001d40384190748044c0c100d03e40d100401d02a10090005e03005a40d00010082d1801075501202030301c07180c5900a0048590410941366049425a82da401607800001014880c0707145001840c10881c00283c0705618001d080360342c1500d426080c22407222400c4a010a0700b800143d40c509031070040361061044610040c441c0009a5a44061500300ca040c0790500410046d00201c0d107005070265000030700c4244041c030b41400803080c0c040015042814820198a1854900030140c402d00043c400c10b00e819600145c942c80d64801300c03881401502000b0318899599403044000009425a4a20007070780c1c4058030400607400c03143c211f454085098540250180f40d0381c01030200010560208980180b00e0b5060020b00d04004170710041c641440d080d01c030725240303002a040c210500d25000b4503540c4c800c1140481140c1d40c500c403009031040340c20751520320001c41820f03100407100e4800c4c0c601681d810800b41c0001000309500450441d056884103011120b40c681c00140440503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 774348075 1250 774346825 774346831
    0x5010f0b0904090521030402010f050a050304031805060f03160509010c0803060102070b0a02061608062101060306021c1103060d021905030f0f16150507140a0f03020c0108 75
    0xa03008105004440c189604814101c90151040e01c03290800d42599410413264010105111100001003008540c0c1010080c90025a03d2034242d0170080d50040150a520002d803001d014424800d0a070b011160900d0050b01c003811001d45581c0e103401588102485c20340040c2c804280d59002c1950b201e02252042d41035138040b8005a5555000416548030300c0703681d81c00035015904500400401081a4002c803008090303c01c0581e000701f0880c0b92100344c156800843c1c4251700100507040c018440c1d0355850030405402d02d41e40001ca0300d070403000c0042660040683ea0300c020b244da400400d07841e01005051000c4011030140c07550a100050200f40443c40510045808607880f0100a038030002501341032814807000e00d091041000055101c800191421603940c46a508541c0207c058040000c2c051101d5284541410031200702c2c28200741c0c0c00c01140d0607036080381003041004140b1100b0b01c1958a4400e1002060130199420f15089040113841318250078004d50141c441c04446480d01d51160306070f070344 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 774349325 1250 774348075 774348089
    0x1a040f050d0b010b0c0c030a240605152214090702060714030903070609150c140d05091002070609020109060c022d03071d010806040b0105090a02041d060405010f 71
    0xd580c20f09411600c0c80e00300701c1d030707880c010710030100c000c03440b600c0230041d483c00503005100220510b82c0c5414421600c440340048005424105001040507407280c001c5440d400c0301c900f80d207a8807045904011801125860720020454102c0f510010703400c209240051520442075038042543d91b00c450050347d940d6000c1d1078420018440d07401d50700500310440061a0441544820b503454241ca5413500c00071740710012803d035100011884a60042082442000d035442d5050800a422080d040441800f5000c2c10400d9040680c079100001c0e005841400314107148811480210344a601e00e0510a00418041800701e000c0384514001150715801004a031030210b07030061010304050402a03a6060f40f40d4000e500750704844454655805680e014042c01c000b80c00303440400f022802c1004645103500ca8103a20a4109030061f805201c08221144401d9054510076a40111207840b41d00c080002845194011843d501060b844400440114941540120b00840e001e1246989030b84044034000740502c1822 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 774350575 1250 774349325 774349343
    0xc02240a1506051813091b0602010b01020c04050709030b0a0e0d1119150e03090a050d0209041713030b071d011b080d060e04060c05090a0302010e0a1a040f050d 70
    0x103c13007050600c0340500e00307040034100240419450a4980c1030b50920311007203e072560707001c5445c0d00707000511141c3da0007040c140c0f000384507050184002035140d41041e814036000d03644540018003041c0c0265489001103a00c125035076018034003400ea00000341100a022240c90007000118030706944920421406115442c0c00340c20304621070000040f40421214007250b002d4a8032000c521280c4252040940104c1d98002030341d650903004c02001000c004a4000310711805108000c980542c54129466501c030740d110b80d20003d49000c0340c00b003c1450080f0611180c40d003131a42c02c04010013042c50b21441c042c1c201c580741d4030100300d551101e40e8042040000c60500041c1040300880003c040b99a40c1a41d0501071051907141c814126900c00603100c16401c111040340d0360b80203020030084548148092280607141c11820905a0707000541c2c90b000c10300c000703410442041e04411550303a4034400c41006104404c0380b03450440000c800190107400522400040c0307441002d000170142441c012840384654824074503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 774351825 1250 774350575 774350587
    0x6120b060d0302010f020d06030627080c0c030607030606020c03120307032007030207030c060e152104061d150a0207171215040209130c02240a150605 66
    0x711007400c415400c1501107641314a01000c0210303262008004100300c1c4503000c074441d81942088010380300700401d0381c40c40891000d10604034520103000020000c0d404005199500081d00ca1185840201030205a0502910042c03150301900f603880301040742c41e91340a986018200c54201501d4510505100c3c8503841d0410008070070a00c80d500c549002d015070b0348a800e058101990403e040c0d00409411405688100d0050043c402101680e50040a145c80c0907150b0406100210361340704001c0a0f4040701a102080c110781d200d210b01c462202c013201c2d6690000761440c190400a019101501981592001c100742540541c100410442803d94400d100080941c5070081c461f40254065401950800e00d02c24001c0b01901c0504000c01404a141c011907103d0300b030180c4079903006814800064801ca2041111407526217131910700868013401c000d000070301e005071948180d0078900c0f0b8a0900e07109042d0120203180c0e801d072621411f40101c900001c108005850b010a81d52506690f005403000310340c0c14400c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 774353075 1250 774351825 774351829
    0x30a0f1b030509150f0403021204120308130209040507030c080102090108040b07110f100501090b0d1209050303070b010801140405120702041e0506040c02280614010b0c0106120b06 79
    0x210b5038014043e0011500d809050308100320651000365000400080103030180414141d0410142100c4442c07800924034003860310030b034031000314240f80c40241404240f500140b61810052070000416401070200142c52919241031601c441284c0811a160b9443c210040790f01e100510a5944030501a11000c08507103c90705d55860381d680c001c2c5450100102c0400c818901c0300107021010750444034900600000e0400107004059800580000d2001d80c40c0000c0b9656030b40e9040c0440d540310384c01c02c070384846030400e0326403c490684198010b01d13058440003d5550170420070942c01812104240020080708548050310030418100f56405003103607000d141024049010319005010301d40c801080090ba98031440740c041a01515499410f010a99a1080102a06142c0a120a5000b1501c0603008504141d031120519440c038400c44003280c00d40405000c00c021441d0700445204212a000b52001d42e96050440000d6019a0b00c40001e5406c00c40d000484200c2d000319681c1c2542c0c8102c1c1d0026039511982 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 774354325 1250 774353075 774353081
    0x9021e031003080d020403050a03110d08061008061504061d040e3a110c180a09080702090c03040309090e030306010c0f06050f01090606230918070302030a0f1b03 71
    0xa20407850307a17070800000000600811069040f41c1c0711f5210201ca03000c580c0c00140c108880c1c0404807051280340e070100003d0f5038901071005a584541d080884d01c80e183c15010841600c1405600802d1402c00280800d80325004400c0240c1a8039014045085504c410188801d85039a509038282903804204509840582e076411814410041c80d440c1809081c1c1c582c00c0900d4400030051080807407451500c00c0d9940c1e00c14030402804540640715500d440300c17071222201b80c541c0e00402c40c44650f0741c0c9081700c0e400c001d0381c2c4007202e0b0401e8004020280350b0400d007a2045495205503821000318002c0540042c0200c190f000e0310a031000e04501641c210355030303403005546158900c0000c69618400e040004009129031103514050115210400200d40c10a8050811034034a03820603418401040f0103090409070b621408902c0c64044040d0319115141e0001042c00500b001856203503004c40641000001e0794941e0103140305280546040c0304011508030701104840c004040c6080320a00300011042d013600a070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 774355575 1250 774354325 774354337
    0x90a090506010c080301030b061c0f170f04030803250504030813080a03080103060c030b1e031c020303040510090206070201180906060804050c091e0a1509021e03100308 74
    0x204186200c0300c10f0340d6800580e54030036002103965101e09414008103080004000d10000c503400140b480740c1c40280c035005c000d44020000241000c041340151800820b4010a43d40a41e084045160700c3e00d460b450203041e20380003214248010b4041804501c2c400100031781c2608080515202c40d854076013142c585042d150b12400fa840ca507080ac5610004615004100c284000c0d800380d03480784800d5040d0315189060712050881001054207210b1900702e42e0f81e4129090b410b0280e4103000041c10104040480d04145104583e40035018000000c0318900381c010000398030440c445c0d000c1d22644101078070301500b110607008001e50060340600c0100c0055008100c42c2d101c0ba0f10408000c0e803010790340c0701e11105850003034100700e0004205800303100400800f0000318404d00c40456090f492403400d07003580f04200034a8842240c0b002001404682c20301e95661080100209014840da0b5aa0f101c0401c4400713584805803070351080c21f071100c0d41c88681400d0b0054901420300e510b40c40c1d500d1807542d110028603812030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 774356825 1250 774355575 774355577
    0x30b090a0b07030b0f1002030a0305010923040f1b0f0b03010b0d0509070512070906090203010b03040803070306211203050c09151309060519030302030a1d0904080c12090a09050601 79
    0x4011759070400d0383d0311524034a070242907900440e600c1c130300010020203032038043e07100108803030400100008039003100020f030307440740303201600310700103a59078104421905050300340603142440c203158140d07000c010100c1c1c4900b0307561b0500021482c0d9695901c1842940310910500c10340803024000c1c40740010791500b1031904905c100d03040390074261725070b00010540c0008100e400300c071754082c090400240042d40120740040c60900c10450856160507852949480000c10080c814100000050030041c081d80c0306601030704402903c060f41820b24080345c1c0c10041910020b460ba0f03203c4022035000e036407103070081e40d105621104180e42009410410701110017070b4000365800d201014031842d00301c1c40401d500c45008114140d4007045440c64207060145048000d519902d40e680c4145c400d00101c4c0e000000c0b1000303003010f0310701951107034a80b81274202450142e1030040e034010211010302c814080200080d1081280d03c0c820b9948501000f1070305203043c4290181c05400200c0841d007040711a07440d9021603802401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 774358075 1250 774356825 774356839
    0x1d0103090f1a0708060a0e091e0c210c060708040b0f09090c0c120a12240f0608040818030102071110020703050601091a0907050703020715050d0f1e06030b090a0b07030b 74
    0x8035042c8889c054115800c40742e125444041c0c6c3d0b880c1407500e40004040f00741c062001013600c000d080c140c2503c6058294042e401307103c000804008201d0044102c1e00204894066503407180d41e9004462003a03031081c281d551248100d0800300326001141011900c0685100d00140320403410305610664035003018251100b44803450840400d91100390041101c0d10071155144030b07040042104c602143c01040e084124001105c140512106030171039060394001b41c002041c40d40310244103250380c1c01004022007468040d400800c80008108c8251000b00759500c0868050029205d610803c994429071444003514035402a40108003124030744d40003554105403034207401c1c217200d400000324144407010783c0c0510000b800000c0550030303d54117200310030181c030b80c0b84018103035607440000c0107020b4050000d4080c3c02c40d603503070030912031464aa0b1000c201c1140390040c19850b0107886520f04014240c40c4000c1d903803080c01100191000030041120110981e100c540a80d180d00c51300001c50050183d51100c50300144 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 774359325 1250 774358075 774358093
    0x190215060d020f030c0d0309150c12030e010902040609021806130303120603120503071403010e010b09032509050f1b1819060f090302011d0103090f1a0708060a0e09 72
    0x150a42c041b003605010b85c584520441c070b0308032144401c52280494108100b60100f00708006181e00d0101070500c0039520f00461109845992103005050f01c400c000e60141c548080002e44120310303009001d40384200920308441d0790b0240e09111329841214016103184042003401d00020f03001c6d001206902c20340c441e00085541c0c51b65280c0d1030f9030000701c09503404108007104112070341d54042100c031068182c051440e4190351404048080d00032040c00741581480d0046604081c54404100d00c0f182001c425103d4410b4000310b03179483e40303c21181d004030b10141d070400b0001a03031501d0409a80d40162900c2490300000303041e050180b01250445500408004640c07602c0311001d1350303102d0201c0600401803080b05142c0d4506000601840030b0030070801d041c41a541da007000541e822000741008a8000d1010292014031032004030018188d480300101030441042c480014440070340c001c0080c14201d41c0c440100364a5150701600c960308110742440e805007142c1004e1185000c160402a0000401c400700c405001d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 774360575 1250 774359325 774359329
    0x8030712090b010801060e070219031101140a05010f0b0306060a14190807030b0906030c010f030f05040c050301141b0a0903080c0604050d050c0307081b03190215060d020f030c 77
    0x80ca0a1340071000982d11a5802d010344046804410381100c520300062501c074007185030f2151304c0c6c0070030100130301031000703001e61a5060802034110410700c5004402c1700100b860598801002030000f80151000c03109401c4010603241c80c28800c0380c0c02200010101c50400c0444070046664460398000d0b0700710740c0c03c10300c40300c4020708a80f0203681080e2030030384807a038841c5040c960080c22900a01801d911030741c030700c1301400402c1d200800da08039440028a4844211486010140c01134140e90100c4403009180404002c2840254980d40055900c2103009002d450300040c8845c2c0903810660311104103410034040c900c948044c4000808080c1004c0c101002411364a4491103080d40100c099001243c00c90310400c03003001400d01220061000c0d9041450611304c101c0c00541e43ca02946900821a020001e40c5000c141c1c50f01c9810f11401c48047d0072250f5980c1c0750182d000101803c10b540c0005440380058240e004c0e80340170416031007410060155800800c00380c0030000d0b02c80c0d10000c46078040c007a4112008545d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 774361825 1250 774360575 774360593
    0x1d0a0b01140a180c1e05070b060402040f080c1f050f07150204030803090105092410030b041406012909040603060f0b010e0301090302071205191406070c0803071209 72
    0x181c40140c03000250090400c001500304440e954255a17180003100c074001c4010b0700402500c2010f60000410102e0b652104046030091150381c101c0d03218410341c94000502d4210008118032110400e03030b40c41500c2c180001c04030385000e0380d1009000200c0e1080c402c401000303020001400b165400344804600c2c20286030741d544201ea00c26003040c1d80800c030000400001c50b00c2400340c02e0b04502520001c110a6901040b081e9680e400449021910b074891404500d4440c41000b48170040c5401060882c1c540c20149000d07400344a0072101c0454500602c4000143c441c610f16045e80c070408071405407600c229803000c416102c0e46c014009503500a0395420044086422441410001700402600041541d2490005403400041e15070040c4030780c1c103200c048000241d01240e49405c94042c8035100c0600f80113440d0183c20480e420403d240e5040700c07005c140f0103106040f01041c0d1001d00490903103a1584910300c08a841c1d0303514003005001c10a00308007088030342d403040c08000070840c6498000034203088507a0b50a600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 774363075 1250 774361825 774361859
    0x7060204030c0605071a060109060c0c09020a020607260103020d050f16060e0301020708092101090501050604050c07030906080c0d0f020a031107050601030803040f080d1d0a0b01140a 80
    0x500003007099010030406c4411001c043c840d412101025113886c100080010b08140190020045082800740c1001100721483c00504194041551241a0088000e5842030100e0300007001460008544a5540084030f08464202074607614580b168295000d2000007000e90004440341d200b104407040c1c010100340050424030072b159134113400840c40e00e40010008014840e105200e0f910402000f400a40d1001c105d032100e45041d546000c01202e0301c0314126030900e20388941c14140d4280140e100c1007000643c8039620840c0c0c21501000783c1d03164008500168002c004008003c030701d0b8044107002c41401156410350203a044d000a519010008950b042a10000300341a207543e5008100c12524130340600a65410301540458182031038619150180d41e0b407410301c07019250500000105081c0175216505614064110011a50718056418010010440c0b81221020040c07030458040e480400844c3c96000e00f500500d038038030b9a90a241186280440040f00076a010790f400c4e0002444224040020207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 774364325 1250 774363075 774363077
    0x121e0b0a3c0c030218040b041509020702100c05100b0406150504080f060c0a080c1e07110f130e0a021f030b0f0a1509080715020f0a031407060204030c06 67
    0x922081c0c00102081030b28800c1092809040c01031000d81451608080941c04400048401184541c3d081c0c003c18010114000d204544a18024001c01da040c0d0315001841c84c50700c02d503001d2105200300170003180c070000144001841d07030304030b05050045205030750090b00000c2c00c020000207003c0d40d1245400c0c0c1e43e804050208004c600d01080c200203007002404070310001c200f094050304503440c0c10780017080d03103104010002c014001c1403004596408000700035a6200d5401116100301403142c030340c524800303800003401220070503000000c03201c480c20800b8019012403c003520050f140c9100108900140c500001007403550322070f6040701e00141c0c1d5030741424504d07004503242c107074034807044292b000f002e958011900501400c20b40141080e00c0d120312200c0022030700c2c0c0ba8100004007648010840b42c45016074041c81003485860001b1a004e030713001c0c00b82401c1d88060b03000c458188000000d0300e034131140b02e80c8000d40803825404503c081100041e00612415105100c0189003646a0361030320107001103500408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 774365575 1250 774364325 774364421
    0x424050a150807080606010f141614070506090d0623040c0b0f030403082a0301051c0b0136092a05040c0e0307121e0b0a 53
    0x48400d8000d140004003624802c0081e1850904061820b651481c014001c0c50402550043c0351200621580d441c03003100200700c035030f2a607607816206141880340c5107d4040d500030800d288446640e04002030104121500980300506114440c3c003040660700103000c054604a481340074001e85c004081c03803416008188040c1d0b108039800c0c50300742140e6000c510f8010410340b007010002080003110410035a0340c020361500c5d290080e9500c0300038225580849060303120b1130a603244c0c03964204440c41009035041c0c480a07111250201d648910b240c69405003440d024102902c00300052000540c40c0d1070710ba80302c1114000c0d6805c0002d841902020f03440041c0194045980c5d540d00d09070800022182d4140c86550501e281441c8800310104031201031440d1142d11321482d0740d045051109805410b010f480c1506c001d0035200d50b40d03074410012415103d0b445d021201c0c8000c14010322180184801c1c50094640c119240e0f00840d603502044400501e82c2e44d040710721608072540c6c084414102d44105420400746d00c01c483c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 774366825 1250 774365575 774365591
    0xa050a0b090d0804030c064109010c090302040e01110c01050a1103040b0a1a030102040b030a050901021306050f090604140301050a0515191a0403031704020105030424050a 75
    0x904042c0c01901c040100308040c4207220101c0c1e0300040000605411400001d000c6006d01c07012403110b50b49a4072000740c000070404150700c078901e0384805107111070b50b030700d00c5025540c0c0c5040c080e08032011340e40090702003810920288058240355000c0400010000000079055951a40c1d243c001d0f0040d0707074030b455a45c2d114010001945d00030301480c01410103219a080c00e604096a81900c20305004108090055407601c0501506911070400c3c0081e039406402159100c0c1c4484842c1c202e648226401d0110604040103d00403500510031121130b80d81c1044c44c58600e03810400100c80a5100080344920340c00b003844008419500d880041c00108903070840018070342d613036000749400e40d90000d180d140428a09420421802981031984000d50380c203d074088940a5000d6001302c160380c1e00d40140c145c110070105403003001c10002008200303483c001d4407848034000c6030720b580f81c503007103000ca6000307000070400d00205002070b80020000785400c2c6415a60141d5610b412514011900c0c111021140035403205c6003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 774368075 1250 774366825 774366841
    0x1a090a03030c080f06040c140c0d03060b040305031207051c02180111070b0c030c1c11010c170705120c0a0905120a0320070b19020309031e0a050a0b 65
    0x14081603800c143c10401e0191034011840f01c0500d5004013003074001ca869000007018503100d1040b134040d494803220b140d81c0703031100c45500755512184d407400800441d2500740b0210303503001401c09a90842e0742c000f008610f00035111001c3c154051000c0c01d8902070090a07c1040e46603100049100c202c200382c05c000580f98002c6211500800980e0300c3c106050000d58400711200000201d280416102101030069a4107904804c151851150485609442c01f031121001d0a0303e201d43d046544840d4242ea17641000040704024500b00e03290350303441c40301050701c6c0036020310782c1303081032560580c001d2450504509103052119a0f6014010803194104460400603184440701e1704000c14002a050a442c1c0703158442a14107040d0369180800b40207018003890440005c00c46844034124040301d01e002045d02c1a0076a00c51070781c541504148d0080c02030803101031004111078400000c0d9041e05400400800e1035140751800000ca00741011219100e82c0900c0d044000401c00410054010034030a80c1201c400c0d20306402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 774369325 1250 774368075 774368081
    0xe031906050a0f02070309090b0d0606092a170c0f03070801051e2206120609050132090f0706090f0e040c030b150a0608070305060a050a0b071a090a0303 67
    0x3c0058005105118010109034851010b0090b0b030020400011602c04180c00180c420841210050085013801004114030050b0780110f250b29201d03003a2200140c420010a040246250200000040409000b0071903041c0f01085140c000250410940c034014808002110560003240c4080100e50003000400460034001543c41d088840c0c00ea40b00551b045003000a850021180f50541741c40701503c0c100408040e180d88003c00034000340c038119015074446e00d0008040c2c84c601500b0b441c0d65207020180c0c170521004001e5962800700d09001c41d441c00700400c24034031080a02800c881142d00c100340c40c002000744c080010034050515621400c198501e0070013a03c180c040207800003010714001c103092000086a8404403010389a10401a82007591038a60782c06000703205010300c0e6400750001d02d001884542203501d041c0a12001d40d130a20040e50b032030040c4004240d00d44600c940041d04100200024100304000d440581d00c9a00c040000640b41c2c1044c24245505407a8140700783c00031441da80805030544 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 774370575 1250 774369325 774369341
    0x12110307080c13020906041e0806011e06080a0e0303010f03020319050d1d0303120f18060a020912060915150f0607030302070c0b1c020f09010e031906050a 68
    0x10090442c100100c1c00f0403106070361911140003140c0c0203c1d515986944240030f55001d40300901000d4480d20303880c1881d41c5c0c002e0303061040e04218000c5000205690400030440d074250031013803541000c1d01d4a0305004580110f00140855031a079500d207091444503000707000940c028100b0b4503c4281441c11401014200324100000420740c01050342074000065002c58401c108e41824203000868403031080c4e44441c03013000340754280d6150000050780e00200c0302c080c1e0000e0007122408804103d81d5030342000c50040100400e19080c00b43c4c881d20004041e454150004c011030840580310604c1400c650f203400345000b4050f5406801a00300b2808400188580b0340040d0340a1020b060006841c0038100200710764010f032000407801500c00160359802c1c14025012100c4990340001001401d1b580c842c15000b2913045011042d05609455146d43d01111240c001d9840814070806441e250018010054420035034410340c050b0075004103110500f0b0100c1c1c0b0000c203030095001d400085102d15095201d070040720020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 774371825 1250 774370575 774370589
    0x503090a0501030e06042303040f1a0c0c1c0503041701052406030c04030516060e0a03020303160f050f3016051002070f020a0b040513051012110307 65
    0x1000349013000024040e030300183c02c010042031201441c0c80700111007100c62420742c3c080c80700080018540b036285d902117088540400040c1c138088941e102c8450548100c04840c81503500c8400b003000146015145441c10480f01014032200310400c1d81c480d411078006500c480d010729188000350250707007020700400d03900103403072014140f4404038011544102c64041001c01d000703c101000160b001d105030780443e005580c001c02124008600e40b5001e0041d15880e004075000a00c0038500e403202414a4040302003a03950003000f075401c010391012100b080c400396010a56240001854807008070388240724040f600320524002c0c000e500702a0009030410001803142442c49500c14609200010515003034400c4081070007039120b118019404c1040c50107882480410b0302031310005860082005004420200030320940c4c500041c03603525007070f080b03490003240f0482c0c0d00700b14003e518070814911079100a602170124440c3d180266102c4402c00c155040d070600c120345078407840303010140c50300d01044400020028 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 774373075 1250 774371825 774371831
    0x924090d110f0a0b1603050d050405010e0d02060114090a020405150a0306080c0d020913120c03090905061507031704060203040b33010e06030702150a0522030c06090503090a050103 79
    0x4e000f0381404288505c0282114203901400c02204052040c8111154044034040600440c10142032a5001b01810b8100c0c0e0b50314810002030148031070010545604039140b0280301c0041103005c03001c0c4154000c004110003581303682000302050b50b0b598480c0c0650704031b0402034521380301c560882c006130891392950000b14080d0701081400390740b5542d24550084480d0f06540056641d200d1001403c0d42030301c400c4001385914201c0e254080703181e0388200c1c0c2c1e08000703001e03940344004c95a42d00307080c80485105842007904501c414140c80742d0b40c20b0750002040d05901c40d141044000681400f001c817800030079a011103101d81c0000920007440020115503170000c040915090340c29546070b1100b61511585440340d41d10003408524446180c3c0113210245414001600e544c0d40c0e840c01c580025110344d003540f445c01c134040c1c00b03401103444030044e0300c0b40074070423030b90a841407202d1a031200000c515040d400c6400c40410209031704400000f1403d01032406184d1041c8019526090401d0400c003400c01141c001c4c030f040500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 774374325 1250 774373075 774373079
    0xf060819050606010c11040f0b010237050304081f06080c03060103030e06040504050412030516020c06031b0a030b0319030c080d0e060f0105150924090d110f0a 70
    0x1001c1202030f000030090812441386000c9240458070558080411540945481103465402d10244c102400c84402603003503941c1c02c10498910980001c0008088105514403200c00c06507070368083c0300350400744c024011a42000e654040e8140b810340c0c601000c030412280a10b94804d200600d0040700060002c01c0e000c1c1291021420101e0ba41d480140320280c00c100c12042c500c0380c55184c181c202c5001d05400350043c0800c3c64141042d028200c250704c5d07920006460080040c3d030400c131030780c2072944443ca50b90140100c1031100c41000382d1608007420707120343c00da9030740302500c0b0303da50741c400800320b003400303504d02142d541c880c41c04050402140f03642c00106c1c81040403040c0e000907030081840950a5110790b00540700c403240c0182c84007c10030802e5041c854807414042c42aa010803904460482e0000c841060308600305c2250200140030340140e86420150010a8203809600b11303003030041282c02005114201464000001c90013490000140c40c900300307034280701e1801c0c14130500880080d5020b0f500850414 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 774375575 1250 774374325 774374333
    0x307090e060a090809010e04180302060612010203010821091c030311091014190503090706031b0e030f0610060e060f07020630190507020303180c040f060819 69
    0x84281d0718000d0401947c070420200c1992a80c2c8000307104150110b908980c9102490040c1d40d4103015503a191080d200003160a81d5044140200c9059a6490024001c00391044039400e03003581c0f48400c0000c1d0204140302101c2c817900c46e00c2c031812802e00a00a10a8044000d040242c1101c21904000002e000d04004007245ca80b01c20586d2241300484e40781074075004200e00606941409210302072420150542a01410168400b0282d03028641010503910f0945d42d07104207404860b8000141d004212009070310075241c5009201c00c809810740a8161050641d000300e40504121041390918010340241c1400d000d4a58040c02c040c2540c3c0d0f0070790340c0925050b030803842012540640c0c24000d101e510009600340380301c05058200b01c01d2600c000485910a1000706600c0e60503601118035080003501404000d03101102e034000c5c180555200c1d005185152140708031490344074000310b4404e081d44913004000c00a80c80c0c1c0d1086103001110a400090302c10300b40508a410100b0740ca074400c294168030f0800740702003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 774376825 1250 774375575 774375577
    0x31223030f18010504110f03010e07060e1908070302011d030a3203070204021e0d0b04111204080a0c0b0c0702180f0a0c0e040c08060a0b0c1c0302090307090e060a0908 73
    0xc0503045031f0580044c0380d0300001034007520600d42c0003002805541000202c243d0000003103000398900316000713100080d040c940e000062041d8400c1008952080a0420141d40103c1c0340e500000c040c2448508009981404240340104a172000c9400b855004100050441c121268096402070b00d410a030310403400c050100e0383e03030284085c042e00c110360008400e009489015001d040002d04005840d84074a1802c1030140100a104140743c0a907092140c01210110640100c6559620b2101d405000d915203860b1000c0b60b410500c40f0704148015801104042004840554400c0c8541c406c45581d404040c410b0002d0703001c1e00c5000b43c000c3c0b04001c060242441101d4102640507455820008403100314583c200e40e1040794640c0c0e90b4000d440c1c107102c603031450f510030051442000c050350382d680d41c1681d40406004a12070710800e40c00d65082001c0051184080c90303c50400c898140c50090705118034400080d0078540903902101c1a0f540e02d15400f10503500c00d114146c0e218000020421010315507403140d03100c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 774378075 1250 774376825 774376853
    0x140d0c031106070f0b06010323131b350a06230a090506280e070f0f0602010b0d031e0908010507020102090306010b04031223030f18010504 61
    0x459154012550781c0341d100d040070f50b000107812490040c07144c0d40508110043c100309a4080b4002810310000c0d10b0030403614031444036880e2800403100b059668200080000c1c445002080303d42513103002583d501e91510307604c4ca901400c2503680340c5010282c50324401c801221021000360305140b004400c50503003103002c05c040f070083c0d400c0301c00880c0013200600e00410014420300c030014200c0000f41808074218650784012165803245040350910784400810904200c02c5038800b1039075102c03000003864440e8030f542000701b460001400720f5075410389522401d05420420342005087e10202d03001009a0750b424020121541c4042d60f4003484800144c60042021b1541342101f501922401d8001c0440d501c1b606d0503100816008008100e00d052103d0000e003c2e40c0b00d54080c5e4868422980046060700c00c80088404807540042d800c03e03545030449066408415090010030314046244908a03e9a2004021841458907500f01c560526103c0f61588868204007984070280e8034020401c000103c06000c3d00304 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 774379325 1250 774378075 774378083
    0x10b130e0c1e060d050915060a12151b091e092d05151522030501020705160b030f0c0f0c150f0606070c1a0c0115140d0c03 54
    0x652089401c41d990400d1102440b60300042c00080d20780d060b991940c00309000364159801d55020340350702c03c5050600e240603507600341d21050a00c02001140d02d06424820744c070707108820380f41c07000941c001ca0754203d074010000e80b40c00c90030b84a00c10b080c55034401c3d00c400103007142080c2c0341d2103050140850000791600e800703208109176484085084a200130920f07901c01a0114000001220011041c54003520050351018808100401500054030f01138540c0520800c0041e60b807802c2064180c070b00c3d5204864030307019001e0b4454421010001c12401e000503d0102c2c02800101814100c00422a421092590090040380307428402d0204403203454203a5500a9140c22107251142d00820380300d21280b191103138500f420b02c01c2100c411800c0890f424528447c00180b0a14129030380c40400384045803191840060220100c60320a0226003c0110900701c901d404203441c0e801d0120320042c06007141d02d150790400c0104520032080100e0407140c041070070401d4041d02c40803c0b04070300d51f4030444081c0c42400010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 774380575 1250 774379325 774379339
    0x40602071503020d0513020a050307140418150504110616020d0201020c04060e0a0f0b060d180b0a051006020d3002030403110c010206010f1e0905010602010b130e0c 72
    0x70416110780c041c0e40080840f070004104a013081c58107141c018010b200100c0c05441440c10005540c41c02103260002c803960041124040e03800703101000001c0c464049980e0598540b0b903070b8800895000038003079401114003100020142489c0c10300000b011a13100110703104031801c011407006d40080181a40f080c1e58141c8104141c5146480141c1c20140c001c045580c01c946400c20000310f2801030a0348d01e01440c0342c0301c8100004001801840c00340e4499800041d003000003080744040d4002c0c59800301e0550200d400785203d00c1046541e44240d20f11003524194076403521203083c41402080202410003c000c18001810441c0c4038402c041c0c0240305010b00ea0049001c15a0b001440560590500581c1c0103d0300301103581c0e16061070302524003408500ca2401c2c40c03092a910b110b841d400000d12300d05039070f0383e80c0c0c0c0410700c0c501c2e18001030b0780401140c442c020310034600c450004070003249000701c0b4060b11940d000800c03030380030310342c20701040e58224400310328181d00301074903000c0003840410b0003841c51030192900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 774381825 1250 774380575 774380609
    0xa14040c0e032a03010203040b01120809030d0c060c022a010c0c0909030818210c060403081e190c02070e0f10051e121501181104060207 60
    0x140c074004041112030303030140503140040c00f08104100c0070460095484002008480010003450b080b0700085038000c7c035400012006115070304031015010a8144a4a038040c03801509802081c2060405104140803403003a96089040290a0250100c403440034801042d9005000804d560602d460508081001041c01c0c0c01007050b9210300710b2400000c3c1c01241920746995200000d000a14807010300b580098a0000403515400c890498460010b503020300500003039564440000300c3c0c8510816800305c0e13800402071404c08007400d001c0244914080c1e02c4222051414070340e904818804030362020804042c2c035080100c1410062107040300340c1030740d420004081030420801ea00c1d080860300451340c407071480380420048144241503540b103003140301100a42c1d0342c1d940d4144a0f4858080b0542d81e0704580c010482501c504240950350151510302e8200c4280120246582000c00400c2c5c00c2210811544551030700146008d0040c541c2c0340c001074000d107251a02d8290300940f9413050380106138600711100ca003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 774383075 1250 774381825 774381827
    0x80d05040b0f04120e040914030403170a050405010f170412030c03021218210316050a080f061306030302060105030c0109050a06110109170309010c0f020307030503040f0602040e07030501050a14040c 87
    0x110300101c0c2da00c07042230914601500001940d82c1c00900c41151005a0f03180034490444907101942c07600202d64a03287e050508103001902c0301c0e101012600d080010482c200c00b600801100f219004600885421245910214005098605c1c0c9490702c024540100b004010000300110603ea00000144028030b20049402c245428070640701c0c0200c01c2c0401c01c524801c40040c1100c002e40c0030b40603d10031042d9500440c60301b030320940188101400400e030184001810724070341030700031540000c00900305001c2d01d24084080c0c046904070740094006a01c2207005022505040000b801c0280d000d003041d540e078903d00300000701c61903414001d001c00c00549001c0229402c600b500300c41c080030342c413003401560203500c2e0f8907a09003604210f4070282c00b0b608001d44156542c0c00344000501c0501181d004e940b8124494030141d40d0380d400940101c50b503002c080c12480110700781d407006d071000d40a140036a101908008c0c030f005060b100d040e0041441032700101403c10941064500322040350506503030110b00c5c1262490 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 774384325 1250 774383075 774383081
    0xf0905130b150406080105013b030712020405010905040803071202070c330206010b0c0f060106050301260c13090209072111091507080d05040b0f04120e04 68
    0x56250021072400da002c18000032100540107581860351a1980f5a0380c4d180112185038003041c4c00c00b1070141d4550002c1c0300a8820320002144954500d6040c0300d101c6250109161000c19409000c1d048841e090990842c60240102401000408010702050910307071034152251002030440410b06c001c140d249030708100e0580555040f5504001207080d0305640704c0740c14070541070b00702207061a1980f5204651921003403a1880040740d040b80e00600640e0700305029030359168008000484144120f052100520307600300100da001c0c0140703980300c580740e5141089525800e8004481000c503e1207001c03100140c0200001c9400400c04119041c070180003a01e58100020461000080e401c1f0305074804010540307030454481450388550f0610010310103040b010270011035856003900132801c0c0c8100044c01c00b6103041400c4052140b048880540761074002e41da841c0d400d9010100321102c1c81e440e01c0c20001400380c4c0f07200d01c035400a2040d918003414039055031503440000a2000701c4091000c60303d0040c0282c2c64a038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 774385575 1250 774384325 774384341
    0x6200c06070335010b0a091403070506130e090304031104050402040e060a052409040206071a15011205061c240e0d03110301120503090604060e0109060f090513 70
    0xf1030021460251a49240c42001804512219101c45400001040c603041802c50300c81a00c00d946442e030b080d00b000d203180400110203641c1541340c812034a020505590b00c0d40180000d000c04000b2000092410700030039000d16004140e020315805c24130013040854903c1d80640c0d4040400c580010b4182c0c0d039840002c00808140032454014410340d400c006c500401c541c0030038010b8000c00740c1590301d101d00e844417001e10201100c070a030f0444808000710b801410090007420129200e5006032410040f0f15008800030740003101c442c0c11100a810300180203507085610a030003040d45002c2401541780150103d030a604210406030b40d004c01e03400c03100003800302c070010a2201c1c0140b846846459203400d01900003400c3c0455541c14580284240b5001a900910501c000e2100c000301c600e065030301e04250a081410003003400c2d00c0d103000400c143c80040ea60100100f006e02600d0712241c034240c100600040514105401800901055030360400c1c03030a4001509408031082260029858100c0701e51104c0641111 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 774386825 1250 774385575 774385607
    0x10e0702011811190b0702010806060d140412032a020a080c0102090915090c032d090105090d05040b09010c02040c0804021804080904020a1b080406200c060703 70
    0x40003100402c1910f214480038400300311001e45841444803074411071200584511681c2e2002000341000550045041a42c40a40204034908109005007000240c3d96030301c413216180001401084100190282424040450b6280030402ca1110107145085030010b250051810040c0d42a1a08140e10812481c1c0000d80c0c40241551205030150905003c0e410054010707105116940001e9600b01e4070402304403420030f00916504107615202c210485c130b0b50020b0020380c580b01c1907041d0312480301200819051307014030300c80501545280035030040d421107201600014168025505582400b90b01800350f070241d0300851005a5606c80800040c0c410080503480250810f0410180002c052b41040c10740e8801d81c026221003030741381e006201d036804122049900402d081c605129404d124241540508140d40281c14440402c28144803400800b142c0e4031412241e06400080901220394042000090405801d40f413240013000002a0340d2074132030140c0700c90300920001c50000c0c00d0600c1400ac0004034012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 774388075 1250 774386825 774386861
    0xf040804032a0609060f030e15190e030a0f0c0b0609060607050f03040f050d12120f090b040501150b0409020a02030909070f030b010903030e121f1a06040e010e070201 73
    0x6103e030050202d802c01d1040300701203404100c0d1a10f50714081d000d1040d000c1003d001915800c4035a1b61101c0222001a05505170203c0c2c82d840344e200a8600c0c0b2503000311541d203400541c0c98100d0b00304d0040117003071021020001c0008003485080044c94802040d0b40056044034144100d60720b000119601e8051002c0207003076413080b00581e0074900d0004c001001503801d8043d8264455072660203002804183c080001c0c48560881e519440c40b5218103000c8079400b884140c0414200c0c01400d801c0f0554207464002c3c0c441c02c0c9810705000c10040248180340810085010b10302c01d0911344694031005004510a034205250006074030b07540144207004aa802d19030041c00e80c221800c0c1460014106481c4050340740c01305c0d14002c0a0340d410760003189003c080340c5c2c0c0359603501c0920a1200912a1350b594014a115003446150711314086030240010040b4000f007400000500e0444100c3c0c8203020780340010f4000d0066400700000d03c035140916079002c0c10364807a00304025141c0c440c01c200300e0040091091000034424 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 774389325 1250 774388075 774388079
    0xe010f090b060312120f060103020418150905060a090207050304080d0216060905060702010e03010f1107150203060315130803012408061f03060b0417060f040804032a 73
    0x5464581d0340e005642c25000c5807101c080a1240072a984103000801001c1d080010000b261460720541b003591004041c50050306150b60b4986070211410313803100b080d1a041c2c80704004c543c210602c003c804018140b9450034007a50405502141180041340030315840c45800146400c180f0030200119001030504508896801c1c0300302c0b200944a1031016204040307034110101c0080c0700b520a08822080d0f40e0300a05071880e01d455980196400d154284040e5050754032140e40a03a80304251041c805e510058885072541e0300d081d4075040e50042440244148c24901c1402402140c0e1400140d017100c4c0c986144030f015258071620102441e60940f164001c050400000000c120b003140241050300580c80200c0740c050b0f425401d80700791020f0000310b900b141c006c0c854182c000f2025120a05840d400480780c20300003a29615910800c0c0340d0f40c49a041040c0038000d401c0c1ea440b038a8010818070340c0c841c03415243d148440c1031591b00c6004910272844090200c070364469250078100d40d00d1694880709010800744001d00c03a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 774390575 1250 774389325 774389333
    0x6021605030703020d030b150903010f06090b10080112031407062301150210023f13320a050d08090309010203270312070606060c05100e010f09 63
    0xb40c030100302103006010340c98000076201e00034000c8031080706008040ca119840251642205034015240240d03056480d28903010f1000214070948001d01340701a800f050050f884e4082c0b050004480203281c00700721000c5d0040152050720280a4000c80e8103181c2013203096401340341320015000e0b09101034941850400401c002041e03070528561800c0404140703448583c0e070380150030804551703102124050b8104441464403007400e54010008159101c907201e10402e9503003101c40c15150565038400740980c24480018807007040c1e80d4001d034880e01c586448034007200b0aa0312441c074090341324103642c000d41419140d04020b002d801211210841203900316031000f2000d082983e0341d50006030710340011443d030070040703510113030301102f101c2544006030011850a0b10114204500c0c4c0c1021090000c009004010f69405a50500207007841c41c0c0041882501c0d4425428640200c1d40581d2004040c400d0b224410740000c2e40c08142d110101c03524000000d41802041d0640d400b406c01d114131000000d25060481c8104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 774391825 1250 774390575 774390577
    0xc09060a0309020a09090305030f0414010c050306030f0313090c02070b071112060601021203090f0d02060a060806130201050c071a131a0403140a020904080307030c2102070602160503 80
    0x718021160600c5a5a844400c0401c44d10700c61b50140c006001000080c6614209000c80340c0c1180c40fa1045407000c8d11028135050031a02c01041400004000105215103440c0802ca42e030702c3c1d080000059480d05200b038244c0c8020850360b12071503459079155007202d400d0300d0081c02008011b00011001c00d42e41ca110385010315160300c2100650748580e50000b02240c01141c0015045d10514040c0c0090000c5268001a00626000100504541c0c42450640c1c2c07110241030040c020780307411381c1c2c00605540c103004510909988054109614581c0100200301da801071900d2080314054080c05c0003503171045018038042c20100b40e5084030000d00b02050520400d000c0750001091180d83c224000500d1548405403602c9103042800160000b00003440240049020480406c2c05610410201c131203859040c1e0110310103240c21107040e41c03922404400c022070765805001301403032414a440c200040d5603600365030000c0030900c50200c40e060380d8003080c202c3c200510784e8112806070703d10050700212002607182c02c6e13079a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 774393075 1250 774391825 774391841
    0x21905070201110601051c080f0703080919020907140d05040503090a050d02090a0c20030415020609060f090703140607020c0613030305070f060203070f0e030d1202030c09060a03 78
    0x283c40311941c484024004200c05041e144000c1507212018034850a400030381ea50401e0a5405d150704100c0d4401c6820480c000b03003500d44c82138807140030318078000c04170030b00b4180b42c840d001600080180d604801603840c00309866025405080101030324045c510f04124070f020710b0800b49002841c000c14841800800000750000c00e030f003100c100c0103070360b112410702c0700302d1404840013034000d075160001c180c03a40c5e0181c001d0030352542e807071070000140144445442c12045c135200c041074041e0400101440080d610000c501e800700780b41e000401d51410582d413030b5941c60000a00f0550722880d41e60114003008014001c4e0f500640c3c209005684c1e920b02e0350350240c0c0703d540949850026104803540f03c119030800d0002e40310303a25410090420311502d9500e0a850a5006610440e040491010003000088141c070146005010b40e035a0b0300903604443c40d01805609000c20310300d120381c0c441c0440303140032940803854512074409218050b0b00c0e0b840300f0b440c900c400c0c000e000201c0c2c0c0c031240c08680c0341c554035450b5100c0701e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 774394325 1250 774393075 774393077
    0x6060a11010e06060301050703020a0e0d050a15050f0612060f091905010e0708061627030602030a1d0c0114120903031b090604030b071202030114030c03030a1e03021905070201 77
    0x120903104c0710412781c09c07807180c003800c40c02080100100c601039160480143c3c00d4107004005450303240e08a55648002241e00103c07040c0d600b41d0b1141448010521104840d42c440d100303460700a4480f00040b01c407070fa140303002881c855000e500074001034102803007800030b100c0d400c61b0b01c04030125441c16450242d0207801d216000b80100e21410a0000e0880000034150303000340210350713203c84003109504084511142500d03d81c4040000b01e01000340080d00d144244c002140180c40041c0ca82c02c0a032607100036112100d909034440c00e0b203000d01b1844054041100306040d0b0090034003000600d61907039140202e004886060001460160420800c103c000c4000c0d4441d0306048081c0c0399250792600e007c00c540c01070a4915400420501044c030000d030300741581c80c0d040011401e01c80010700d81e1170100b00690344240c000c0124650300c003501d09102d00342000080282074044010754180b03007100f0b80040c40404540c4464601c1a0a400382c00c0c080c0d4000c0c1d044a2151000e8500c060340601010405001030340026001c078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 774395575 1250 774394325 774394331
    0xd0507090b18071e0e061605102903010f0f0e0f07080703060c0509041506031505030c0405070c15140109090c05040507090803070b07030b061206060a11010e06060301 73
    0x142ca80420010030b9200755810784400403410b01c284624000c80303220041807401d0201130800184565100d030058000990b0b503513034400e4182054079115083c0395901420005482c2428880040d00722843c120407180d41c10007403120042085880064007520f203005003480c01900d80402d84084a42642040b8a40203c078000c6071021100403080035507a800520a00d0750364cc1040308140300040064001400c0c50b846460702c2818034100e000001d048a200014454140460080030041590540541005960545c405002e00d41c500b0300840e8458450011061040c0c1d56403002409443c00345d000d0654242e0480040f1b100504035401c000014100440c07040410f404e01400010300b170304107000750280715a002d001e205100b498001408003600c005000c039024004451000700b140e003000c10180c85013601803030100925003001e0101604988204020b18041d9501300f01c07120203400342c1d02a8580100d01a522070b951041c490404841900c980ca504407415403d041d9000d2205000042103802908110020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 774396825 1250 774395575 774395599
    0x40b0909010b0427110c010614060c030d0f021b0307060621120e19051903020a030f02130c020f0606040501060c0213020d0507020d0315140f0d0507090b 67
    0x498150081d84900814141d001e12884d4502c01a01c1400e1524051110041390009120f89041d040e034222442202081c0e643d03d07807c002d100c0641c18404005c0f401a0b80c3c0a01d0003800c898240d03100c3c4a059100b8030a96250900300401444a5044440080701c003500c0001c820b000040260300c4e544084002d460b06d0381410004660b5008590300c04032081d4000b00c0401c081c500715a20820208403403564401804942d4a541035a81c85000502240c10748048011003624281010414031750180906260f0050201405000684882840e24290394000301212182d196504c0003078074048450b02c6102c0380d28140801c3c20710041c3c00080458500030300c0302c155012965610140310803220300340b04800c000340340310343c60002504000c41d15000f01d110003032016140040410050007640c50580b04440142d100c07240c2001c0090303141c0f09041c0701804071003111083d24640380705010f440e14100e544501c100c0100305941000c5ea0341c0c2540e907500c180d00a0940f52102d5651075150005c040040c4c04030f008100710400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 774398075 1250 774396825 774396839
    0xc0a060c081c061e080105130f0c030210091d07050318100603030305040201030c03150612020d0e0a0201021504080901140715051024200703050c040e0102090904032102040b090901 79
    0x740c3c1e125a003422300720709092015032129041d00c13a03598015074030419120b1011001d6160510150745000700c81d1510390b0010b00e13208001202d081e012803401c2c910000c441c00d000c1c03020350280c1105d801c4100d03001e10080c0400007516042c20000300e0820324001030300c1c1c00e400000305070f0190072851146000f620100710003078804006909a4500090f5150a056441002e010f10b074001c44200a6404410382c0c0142080c078480700e444200d9080860f4014180d0000e0a1700d82150b07810020354210251640c00104207051a5031281940c0c022074280c00c0c10b002c402c224480141d8400c0060b074100320f400404450728112180b00c3c000007040143c980200c1c0480b09500842c00c1c0c043c54100740d501144c0300560001000f0b541c6001c40f620342c3d0002c0c1001000440000610054800f0000d5102441c042c80140080c0d4002500f00400c8034440705500103141d00521596910303035078a8903c15441501400d10080080c10104c4420504207420070007443e09101080110b45c2190b800090986420f080d64406000c0c0d0301c0d002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 774399325 1250 774398075 774398081
    0xb0a080d1218020a09020c0c13020403060e1c030b220501051e54060a081e030d02040b2a0a060e03090d05030307020c0a060c081c061e0801 61
    0xa0301a4103c142c1303080821481007680c4c002d0030310700074580556044540c00000074400507980360403000c4094001c242841072100320304c500100c884c0c41d2401000d07a1210051100000c405c10f00d443d0081c0355851100410b20b44032110044810506141b403400b4062084043d50001c3c2401c2c022130b030040818280e00c496682aa0316490030581e03000700540000b8685038541e20a030017150b6917401d45805584003101601840c00c4044450341d4514189518584826060f200070080c0102032610410b00e0002c100414540440da01441104400701c00b0052105981d9091552180074145044144001400140440c142014000303032000410380c05411211260b900341000501d0408203001d80000b400440010382644c45000c5415819054900300700d0000001090381d0b40c0d040e01034071260000420003403650303030600800041030b40440e1030200c07044c01c11100602c80161400010300c00000025228002280041701c0d10300e44803551420f1100b10745401c0c4841040d4461481ca6000c0c2003070f82c002043c5081c042c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 774400575 1250 774399325 774399371
    0x2091f0b030106200a050307080d11040b2a030d0e070803030408040509090c100f0806040603330e1e07080d0e0409230c04090f060b0a080d12 62
    0x164500070300c500ca028003100103a800134100342a61080c0000b40b03000400c24005800000e0182c04aa038545d40d140d2085003d44200c04403012050004000501c01c1c07a10740800d5800002c24a00300140030350300c1c0518000214104c0301c3c8136402d440003040100101400b40c001d1781600800409503500c2540d9040361613941d0200340d0300100f00365001d000900c40c50401d0f002e0b29910401c11022a00d81c85108008990315074426800a00050b5047c0c0c40070001c180c106410a42164058900b005035034610b803543c0e654034020085c0140007500800d0712103232400c40807400d24402400e01d0700400800425000342a07881189010542804000011048400d140030981d40110764558024000d5404191801c40362003030f050781c0c030980c00303591000384d000842d12122102809000e07440c4100784420031740d8821403a10705040100c602c00e60600044000090102060401040d400100400c20740c0440d00000d00d50300e50349d0440b070501c0c80350b41c5c004029198860304c1c0d20003101d4162820030100284881280c01c0c042c01d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 774401825 1250 774400575 774400577
    0x172a03040f060b060415080f13050d0e01050903010f23153a0201020111041a0c011e09020108130b060d030504080a060b0f0a0302130203040203070302091f0b030106 72
    0x103000d590040b036903e4000300854400104036a140030b840360b440c1d001540b03002d44900001820541008001083c0356009034105082144074401122507039110b541d241012442c0034100540700e604403503181d000341d041e14890742000b002031008940071036520300200881c0e005c2420600c94403011609400d64021107500442905600381c001000794024000d4003682080f01d03401c200d00c051a0036540d5003841d0882d410070810400c503804035401c540002829200084144605004204410060f48102e581c0d41900c0e4903109640c0e07030720b0743d01d4840030314010007180c10052011800c001c40e811200c02a1741c00580c07128800d880d0300b402920303404081e02008240b20401007007040f144010031408d1521500340c4d418540320f85005c51400b521590382c00d09005030030034201c80b0281c6810f4036203081e1602e00e8401a401c0c00a0742e009003024a10b40020304c8440900d1901132090f94000081000e40d1001e00101001d540c014001002d1403d004649001d00803003244150491072254001182d006d0301001124122545 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 774403075 1250 774401825 774401843
    0x30b27041a0603070306050c0d0920090c0a0c050a02040c0507031409060a0c02040e070f090e030309071a09030109030522032f2806050301180507172a0304 68
    0x1560340d61801080050150344e00800c042c82800c0010720503000306044144140d03100a42f2007412025003219004000c01ca61040000c0ca00300000741c44480291203c0180d03e00e0503100d0340c2ca050820f141020301480c0c000e50800d003410200710503181c08c00c000b445c10a1003075844082126043c0c030a441b160180c1c410844c0d03c4102040407050091007210084100f82c0020030020b0300c6800d10380814500201c0303a1010b07042130b001c0314041080c88050310803100c081041030042d500d1803810b54011516040140266822041902e98616074000d441e003c0e80d03240074015000304800401801d000d8006c0d003100c0002d00d8140b032100324280700f48004100b0101140d62160045103a5500038440029510030080c24507940c4507200c504a02e99540e4070504503a081c2e001141c40541940d1041034100305c1500e1f042031003032200030401082a0040322a202200800d070700400242a01c0e4941c007100c4018400317a245040c40f080034280602e0182003211008141c043c1c10340e41c0c079241101e81c1007104600003200c02070070001c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 774404325 1250 774403075 774403079
    0x703051204080c060702010b030d020a0c050d050a0501180c12020102150c070b040807060606021506060a0302191101050a0b01120c020307050609010506040b1807030b27041a060307 79
    0x19038503034041d4106114a50b003e0800c046401d40d01e16003082240c02c0710060b9102c1000c128107060a0200c04c00c01c1e59588060304100e269520381001007100e610441d070207107800384128801c1c400c052054200c0365900c43c009120340c80c0000701300c4028000240e404d540792810600d001508400c010792a00c0320b941c1c10b8010b0310004101c65844010740a000700448110b00003002310b900081c041c0801c0300d10071071013007124545540023401c10350308640312038000406640c0840c030000300c101901d242d616800501201c40c0703640c610955004a000c1e02450120100c03d400381010307000250341000001d50500a0200208401da444e1401001695560820140814440075000d03000c24415084001041464011285400340c26911a46010703404c0b00e40d200c49940d5907052084601d071034014090100000c85944444000181c0e0400f55203d0240055090558036405241c60341c40f400240d800342002003842800d01d40103066125050790b0308603022505182c0c1d1078400342200c1c0030020f141c1d004188c00340041005074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 774405575 1250 774404325 774404347
    0xc010813050d0c02040209060d20070b0408070507050409080901120c090b09030307231006050609010e03011d070611070b0a080a0f0603080403050f010e1b0105070803040515010605070305 82
    0x1c08610070a0742c05c65001c22401d200c0d519204020002107084c05800210b009042808002c8044002808645020108004004640082845a0440d4101d082250b4407042c624200d03240032640c2d44483c0d0040e04001c20142481081400383c20681002c4c0c8440012540c001100f80484220000c000c0114092500501c10780b40d00c080500000c610180071030745041c070583c0301c107030040e460001c03101041c50100700300c5041c11006005001140201900902030b941c18000015000d01030044154100302800025480540d1300f50018031020a401094241d100c2c0201481c6480325a14099240400c1410500d03032050389000034004c04a91f507603c0c6040c1400d20100045645074005042c14260a0311480c400800e54154400c45000790b02c00d06a065036140b540c500300d03050244921240b402a454400540b0b07201601180407610407440103e800c2d401d802800040c0c80600032520094280000481004104040012014480a4000512202603a840d20103c40522580c40000c00081082c800a2502 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 774406825 1250 774405575 774405587
    0x1a09150109030503030a0e0d050a020d08060418140106060809060402040c120f140702010c08041401140a0605040b0d12050a120906050a1503020d12140403050c010813050d 75
    0x48041407514001d01035a075201c8a1070b507001602d8000b1040d80e60380a40c0e040820030800c1c01c42e03d01c85424440d00303040d58000043d4850000061101c1480354940c0050915030300e0740c0c407440c003d07004880e0350b5444038014208075030b0075072400780510b2032986821008503d8a00400146100340501c10050145540f10360911010b840d860382e668003400300c40d010100d40c0030303414011808020720001000510441c01d04500804000180040c42564035240360b5880d0300760b22203640e1b41e0203504100842004a02d011805004043c20307626514000705a8086c031a409850781c00c1401210000c490900c80e58028404101011184500040c20403240b203082a50080c0070f00f018000709040e5003806c0340b104c860000c486003a83c003000c1d8100c40007035444d010804810814412214580d0742d41c2607140c503590840d80406e480c0b045094001d03180780304480c01081400d00c1442c0307000da911285400191281c0da04c0c5401c0760748102000491340030594200c005580ea81102001c900c4064004000b0000045808010350f12 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 774408075 1250 774406825 774406861
    0x320301090e031b0f1b06190e0a0b030109060605031e06011b05030712051602090613140103150212071805041b091d0c0307030b0a0b0301091a09 63
    0x41d0701051280384003e001d480108583e504030b01c0084c140740142c0c0341c5400d0600034000220911505409609011500e03a071090701c801d20400e104080941004101c290340340c100d007402032540a002554041250080c1c070380954100d0b21005024404261200c03000c0c0c5d00c07804215002c0c03002c48042030b80711040005010b4910b03002541814882d25075078100d040d000320002003000036500d942c000960f40d02048035034101c00c2041800d5203019030510401200392540b079540504080e1052410801040c01d9a40c0c4058580711400302c11020401089a2000c0f010301042c244001d540940901c01c00d054640e045000300d4441c1c0b4414040d800070f555481c00300b41c881845103070382d2044103800c2000c04100f0761038074401c0d080d40c09010309007000c0340c8102c50710091107400e1607007000c400446e0b2540000c8124046881194106417603d075201d40f26580d0510860003404144143d81d40843c5a98000030040c102d440218103a500c9084140101c1072611070100320f022440c0f48258026510b000041d82c80c0390040a6007030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 774409325 1250 774408075 774408101
    0x6080606030330010e071803030e0103020d0e0a03020d09080a02090a0509100f2c03030121060603030f030c03090507210c03390b13030503070332030109 67
    0x102e50f0703c2e8030002400c00320098108981c0340640009200090f40c021000020350040d481c6807c80351030840e07800412001c01c049689043c03540208108896102a030170131888a80403004594204525081c000d544584c02c804482c04185018004100340601085200c1c8050700503104546035165682e5060040800800c03078410350250350708103d03108980b402118000c502c01c1d00003054201c52201d1000d90f14220303103913103407200002f0381c00c50720050008000e903030441d041c50201d1440980c900d110303100e0708032003540b004103024034041e00802051b810240404160015a07010800c1110000081d411203e5401000d00361303601814040015140c1c01a1081080140700c10392015a002a5660f990f4100140c008071980e603080414001c8000300c1c83d00c1302e0500c2c8080c4045c2419042600b42da20b100b241e03e40944203030030b4000603c41401c04194480200115032141c1200c0d9122f0150030300814101c2a0b1039415907203a050150031650107102c00700300420702d8030000b0051a5903c0c107400100105882d11f06c043c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 774410575 1250 774409325 774409387
    0x150f01060801170a112b020a1d040f0f0c170601090b01021009020f0402130e0a022110030b0406020a02060115090902090a1521090c032405010f0306060806060303 71
    0x600045103041b150080c030b502c2c0c00c021800e00310315441000282c075540d07041041c080c0ba03906c10b080d0a88030000c15580c1c005030007840d5441c14030b80c0390501070501d010010700501000d01c16400020072140c40f108400400c0810001d4a410341d880c4c480d43c3d0181c0c2d03d11401c003401079000818026a09180da40800300d405d02c002c104281e80d01d11100424161303080101145002100603004000004a40340160780c0001c1c805401c604d0b241345044515141310780071001a200640c070f8800290310715403503513201c8050364115036900c00d1403030300345815000303903001041c02c0006002d44000015034103800808a0b6180303803207460ba44221030401c04003800940040a400d640450f0f10440000c0702041d2000940040c3c0f0150b0f1400008565102030303c520004104603018124a441c5001001c030700d19400c581c00703603680700716101c9000604039114210b0540035100340d0822031a04000142203420440725504691180344140011507642c0900c075100c400c114dd546800d074000300008182000c0000c403095503040d0061101c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 774411825 1250 774410575 774410599
    0x201080402131e1d070e041b05040f0501090b091015091214190203030a0f020a0203010e210f03130201050f0309030403020109080f120c150f01060801170a11 69
    0x120703100a01d82c440300c843c507a510485184a0040103482d401070000d0362008101391481c00b845002c03200d60080014100c2c291a4071220034503040c170018800100708c0140b051108441c0160b01708020602032060444c050b00d042e814403000d04014000d1482102c0d08440941942d203403150b289104190006042d041121034170b00441c034418029241074080d40501c1140500070300841e440da2070040380d18240003001c00188200d2005941c000200c81142c4d46501d054030308500a0a030517031518800c0c810082d81542002d51011300c031300f000110814040d0354140e03402307545180c1c1400360115204101c2000c90300041080001c1650440341c868907002c1d441031525928080c03600000032810b130802d031004222074000090410540d83d110616071702511801010313110501d2030052640d1348460128184080410201e1194480a010b0200543c1c0032900c02140c8801c0c904582c140580c0701090045101062175030001049030121184240050300661009111890486c0c55000b2141d048400d40780e4002000380d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 774413075 1250 774411825 774411851
    0x1101080a06030218070201050108030720012d09060518040b060702090106030e0c15070312021306020c1309031704081b100c0e0d020d0c171b0d020108040213 69
    0x21008041c41120f4500130141004000203080d100103901201e000c0d4014041e03540400c5d0a205040c0c40f1842105108015500a07001030f034203a08041800001c07800380600c0a848035064200c2d8a04c2d40c862036494100c1543c0750241a1024021001072048500304694400c2ca03e06080c0c0c00010310440061103d4101011540069a900c000740c0207600020748500d0034941d041070801582001540c102e404401a40c01d08080b84598058207402a040041e030546090b0210280d174121000c0c0d800c40ca503481000d82e211034010703603940861000c0c02d000341c0c1906038140020340b091041e00c003401c1d8541e950b0b81e0721340d81d41c030205000224043d2069030380c0d4400308003001180e800301c07c1e0700840c800b0010142006c00d01c4542e00d031089072030504419040c170400c040e01d140706a031100036501002e5030482d601107140c00d4a00b00040b02c1c80180e00111518981c40281c411103450010b40108078060448004000e0820310050100d1a004400006e010900c11070102c1c005140070444401602e905c204002000390030444 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 774414325 1250 774413075 774413089
    0xb0405040e1e031905030f19090c09060302090a06081c0e1f0e0d050c01110f160f08010b1509240406091a0d020901140d1a030a1101080a060302 63
    0x1504403651000410151200011301907500b100203a040181c01c5150048008120074402000b400030340c5c20017a8907801450361a407101c410b050700903403101104d41d210310861000745031340e0109905c1010380c000040c07032040481c0154000d4444140103030814a0070700e250040001f55403060344060100009241d011a100c1510035140b900202a2252201c1d0034024080c103100c110700202070203960003035408404901d00203401800c00000b880c010005011a00940b030529800c8154540a4007454803490000c07442c40c900740081d031320070800c07010a8643d1103820600304c40d64828095088900d1034070981c0143e070464090091000042c02198042d60091000b60300750500680107144c0081c0483c06100c01c5a2000b0124050284003200d0404030000300d41d1840710b80907818003c049640c000405039507507441510180380d1f00490381205030300d82495888101c0548220a00421281004c01400505240018020303210640100782c40050700d003110011140044000c0031882141d40720280000143c40310700c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 774415575 1250 774414325 774414373
    0xf030c2806090809040605011806080c041e1502070e040204050604021b010f050c0705070b0c03040b1207020d030b012708030a0c02041503031224060e0102070b03010b0405040e 77
    0xd0943c030342d030b0b003544801c02c4101d41d42c94220303e040101c0c2074040011116144046020746020b030500c8480c0d50760321380f041003e80c4516004524040221114000a1601c01801c40c0076543e19a4101c0f80c22081e448080740d43c1c1d1000d04ca980d1113038904001007401f600703290307201c1900302c0005040949000b2040300100095144030381d1142d800da65524510b003014825206180c1c010f60305060152070000030751241640d5400e540a112081200090f5043c05100c6c2002150700030070800100c41e0311603000c103000303480c00c03182125050054012618850050b910912400c40a60016180c00320003003000e2411105800f20b80b4052112141d601c0b0340841c691308100041c203d1002d1035544c4118450b80341c8140010b03a02ca082489410700382d250810b00000390041841002d4070000040014200d00c510400001216040c5420305001012800810050317400f00c2e1000300f01a00380c088a00326599440d910406120074031410381030300d405110038003c1e03250940122650446620031200324403034a5480c182104120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 774416825 1250 774415575 774415583
    0x13151a040b0612071d120a030905060c030403020609031516090929131107141612030203070f03080103050624040c030e0706050306120106150e1903080c0f030c280609 73
    0x51f02d1700030030558080c150303401070709040e121a804e024050310615500d0040c0d000080c4659408900d0701c1082d2020001840c1c0068024050a014103002c039504410410314030b00c660000340c000c940800d200310349001300441445000f074180401115214007100130090880c901341e00024040c4c0e240925101030081c2c0010004102d9090782d20f00b180d1404c0300b52038102070206030703807900070a9088480ca221052208120b8440b400c00700c40b09030192500320704511070300000502c440c440140ac00281540318590718180c0c0e215408807502da44070012812020041000c44075581001c2d903003102e0050400390007001c5081210305012420407075118004e410049550801c000244c0040300f000350f50700d0b014580180c0d0004540080090604128110041400d8041a07005008500035408440c0d02d4640203010192018100510666101d26002c0384990204c0c1401c5210301c60804000980349021049403c100301003002040d40d1201e076407600aa081d00f1001d08074441c98001c0c584404120390703000315003405201d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 774418075 1250 774416825 774416833
    0x1605040c270503071e061b0c0806040b0606190f11100209010e100e0d1103010507020a05071406040312020f06093313151a040b0612071d12 61
    0x10074060524102135035103c4558807102030b440102902c0308550842c107072180b0b0324202c541540c001040c01c0b04640c446100a0020705508030018070540d000c1203240c0201c0c0f080900006a84030f440070800d49000d8031401c0b03840f200c44d070804481568000c0b41045c040c240380703081000001d080d900c002d509020441c807031840002e4000074440c00c0740d0382c406803c1000300c9040b944007800c2d101607900144901507510340c25006181580d8560705111000d800c940300140021300070b022504d010340000b502c626005608a846114040d800701d81586021840ca043d8803000c0c0001d401c10389144c0300d408010071403520310020350103501c080001d4604140181440340b400000249030700c4021100b40f002c00318025000000448907505004070181d014080b0740c1d001003006844111183c0e003030038080d900f801081e0354042d0440c035281d8440071400c1408504941c918007140c0400c04445210b061140510480c0070701100c16900070f00203840a03000d0310880c0100c0400492074403103141940c0c08220084a11100300e025940 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 774419325 1250 774418075 774418079
    0x220513020f1b2812080c03010e060604030c0b07030809071d0612010c0206010609080606010801142b02031005090a0b0a093207050303180f040207110a081605040c27 72
    0x1404e500052900c42103842c1c285600d2401d5040356206e4001030242540d1780d180400815482d03910003003039074095a0044950640659500d82c01241644446402c40204550100054080f81c0115241044413215400d101c00c90503041c800f00020003001304070591010034101c0510100c2006d200b40018130311160001d000350350510700d02030a40d2940707510410703a503442181046900d1b60700c06c0480d41114506040d10b0b031a00c044000040d542c107118000c404210f601e03407403400c08014101c1802d03514103001360250345180401c81304030805c1c0d4504440c00e42895005625080004980ba8156980700c511030030002500205695444007010b030b00c82c0c0003139079024020b0445203a0020603510041c50840c04004120741458800070a4076801811103904403142040e000004e16141c1c00002005220001c1c4119030700d03d0b561904104042c01807040758083c5c1400c9c14007203002480000c2c0c092060119540000c0980d2400040102401e10202d0340740410004c103048521070031100c80303956424821054004280e40c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 774420575 1250 774419325 774419333
    0xf050c090c0306030a0b25081501180303051b0703031701060c0210121515030b090f060906011e0305010503121e0f220513020f1b28 58
    0x5001d07201099210701042489520ba500184100226500c044110419524400e810440b60000a48414030854070058040ca40d580600306520600c00c881070704182c995000e00440d4807072a40202c80b0204d080080c400c1c004640a080540901025101c072003081030094850b032814859241c3c001c0300071460380100c0c4a240034490040310b015040034508502c07041071980009000c6e0503045034410a20560304030800200c030b500d411420045904240701c03156541d6a04a0141d0308160035003001c0000c2ca0000e0131032580c50301480403400303424440843c05007929104100841e0500240095043c000d0300341e1030b05a646039a080b040341c0500c4503240052198548001d050809900c490005010042040284480e21400503842c0b903c0c200f001290f504c0d100d044c464103901d03100311a19404120078026198492107143c61300b69003070710b905440c001b2030b00140200700e40c20703402000b940101c071910070700034111500a451803c261600d410303811100c00c01d400000c4650300140c80c51091040ca200c800c1458284 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 774421825 1250 774420575 774420589
    0x20a0e07080f040807020d06020405030a0c17010b03100f090b190615140d091b1503020702220f0e011409030a0c0f03050705241015050d02070f050c 65
    0x40c2c0c0e0300c00d420300391519a440c01c4680c891000024401e400b0552104180300d030550694020b0200a804c44403151070381d0070900740100031403003801e03900040d0300099846418107016411a200c80070340100404c0c01c507824070034054843e0704225054560358103400f40c00302e15082c02c2039000701c07000604201c40c0380d1405481c0046d605150000302d40c1400e10195444841d034401c81d205449209440f407030f900c820141c0c2c0c0c04006886081009091100c0c0354502c0002c4118644200701112003580501107918681c0c078058069010782c03070001e944524000300382c0402409405a0b02d140100c440ca002071240d5841c0341c21400c507503a8a10500080e9940c001403c660030b19916000d42090b2980c0045061622039280140251040c0400905440880d8541c00405029400340c4d00016440300546025001c03000c40d10840740400030480c0d001c0b400600c080703040a03491304a048181c0750404450500065a0081591141d000d2018890103030781c00c10030a4089082698089180b501c580d020304050500c1400b00000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 774423075 1250 774421825 774421831
    0x20a020c030f030d15050904050c01110607020a02060325030b04060501090e0114011103030403050304020109060e01020601032006130801060e090a0609080d021801080c0423030a020a0e0708 83
    0x190b4892903041000890010544940c50703415400801c00604078604141c04c1035680d8050b54202071004d09000c00c0060100b680c981082003a603420b00504404680c955542509480400158000444490140c20414006c5500c0305001511500d0704070540540e0040641003102c3d980000d42d070742c40700b462a19040c00380000030042480d1000c426410a410a0308401040c4030b95031185e0307107a0142c6650359024002000c100c0c21a0010f503034803480c00342006801c5a108035402c80c0003130602034020880c0c9020b28400c0340c400700d040e40200550781c02c650721b040c0302c1c0c11190050070140d10030b0022a0320f150f40340801484500b10072412080c0c60f520b081a80c030b0a48583e41c0007a00a000c4210420450a02c000387e10048180c201c11f01160507511410160704c548034070040e00c0307840760002800000d244000070304c5005008081e82e90242660b035040c0b88440b1030003640203d0041200c0456801c40418006189025a0b48010141c0d4041c0c0100c7c2d0004000881981c8211428107480d01080441c40d00402c003264 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 774424325 1250 774423075 774423079
    0x806010324030b36010623040507050c0d030902010908030c0f1509190303060b0d0c12020c0304120512070506250f05180306130b1302090402060c1f020a020c 69
    0x1000b41a1684c01d1400036032540c0781021501241903a0041d05802d401c00d2008103841910b41c10040100c6000001036404880018069401c05c004648003d00c6031007124140c1e00320402400c0411210b071000c80140420090036410440503400125504100340014114240b81074010640c0c2080c0c0488035003408954107a40314a54200c0c001c0003001207001c198120515040100e0702d010a0a624082d0000c00c0203400c402241c410120303584410140b5940564007415994656181c0e10032121210000d07849183d072001c24640042c001001a10301c0800741c50411807141040e240889603102c034681403500902d1090741c00361f01c03840c03d110202560ba102c202e01031200ca80781030a0480502e4000c3c09000741503402c2410401c001038201000f0198096030846414020152807450400d200c00507007808500d403041c1d9501d04840b001c9940d1014003441b43c4022030740a400c0442d0b640d181c1c1c00700240d503000528031841c03502030342303000614414405203a44000c25003113100507155624410002d00d0003a000c51340c0e41c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 774425575 1250 774424325 774424351
    0x40e0c120313090b0105072306131505010302012c280f03080a120f0903020f070f0513020306010c0b09070e06010503391c1401150806010324030b 64
    0x413416613126003229003060f0009040e00c1140000380141302da41001c0d40c0d08202c180907840c10321401420405000c13401c1c0703000301021164010180c25180c01c0352001e2100a012606c10702a00100e422500c500b041c4006c001d081c41d0804880f24070201d041c0944080215140fa5111000c102c420070349684808c000d000d4000c20780d2502411a683caa89030f100e040c820300d042c003450940340c2040b40c4268002a90b2492200d00070b000b500f84910f4065651248107958504602032991f02007010a51074070f009044601c02000b600d0350307141581904009500203868a410071600b509150045800103524501409082c001400301c50726110b80e280407001c000d41043e04010302001070100700340d119441c52191081c07100c0b541030050110001e402d0112132208181045120114150004c424054110590340b1225001882406600424551020803d009055851925449090354607110f0b11089a105071f060500081c031072b0002d0b040f00c1da80c40c8442540484103038041420710812203143c043d40d0700101840441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 774426825 1250 774425575 774425591
    0xb03120a08060d110d031d06070c0b0a05070b0c030109050c2703160b1209030405030d03020f040e0a0e0f0d0c1e060203090307050705100806040e0c12031309 69
    0x241110700150240307124848648050060215600305012903440041c0103083c2c030103e51030058841814204c400c1840c0e15840e82e40007403403c2c0881160249a1300c408515401400d001410580d0f4010580b03510801c4030a00002c00000d048512290240c0c04100d2031317980320b41c03600c07503c40103030b5030014a1201c2c05002440440b001c0000401c0c9019220986080040748507c0326010030b00e060010402e040844644280000b2003481e000002c00482c0040c141d07208582e41c66907095a528800d41c4112a010707401030490146503482030340a0000c1e0301158850701c1c40c0a5440850703519010050743c8940160796100381d052039041c010424490400d040d100541100c00103100054580031a103c00a00f00c90030b1b25081003a1004c2c04881c3c602001c0c0c0c8040b04549901f000703d0002da6a41101d40201c0c0d01e072081c000c0214683c503005000608519a55880030001e5950740300388400b805803160380c42d00c140b048034220361244e52030002c038031440003c42c401144c440840440402d400c2149030b01c1468018980140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 774428075 1250 774426825 774426827
    0x70b0307021614060912010b0303030a060302010e240a09030c090b13050c03130f0f03080117030309031e160b1f0506090906011701060c06061409010312021009060b03120a 75
    0x1914404d5000f03c0e003100d646d8104100190142c42040242581800000304000c29140d095015009403030003031782c4200c40408070006010940314090a0381c104000d141007941d988440e81c600a1540710818030701100490b40da5500d02c0c1154801d0741003200e045071501d10354402420005108014090990418040c07410107901d2007401d44000b41c6116001c0406080544c03e01509902c0c400c40503a2085160540940e43d007002040c100081c020125114600d500c10000402c000003924020307000c030400fa40c5012101c0f030411040c0564048403d110b00818000304440600a0480d420680e00072102c0b8911482c015081150030f880e90b0b600c0400140e1b441a00740722548540043c0c2d01800c41c203031b070030700910b0300c0e0400140c1c5c1c8a600c0c00402d18001c6110400810b013282d0111001046922900c000d02005441d500581070020091380390742e030007190f0311004002140008194801c440c145005940c1542003000d2074000b9200d5020065335071589400c0514091b040c100680496100740c0c0d01c8550030504d640744 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 774429325 1250 774428075 774428077
    0x6031f0806010e240603060103110301030c080618030a1b0b0403020d02060601091226040603020901021e151902040618080607050a081b030406090c06031104050d05070b030702161406 80
    0x44c1090241e8004000145503074020340c007030840d51807191600e540300d60392898005101415805118442c0c0148400708110031080030201380c01d240040d01940c10042081e400701e400c802951016680211415280c1c00411203241d03800b40558001d0303025100e000d00c071a10103840c2c414007922650401c4141c800410003031140d611070304001540441594450344041c501040310f0303052485e92100c1c030700000800042c3d05401d0760013442000030a0b001d6940b01d00310b08007000d40f2500482121b2541e900301d0010404003800352004181d0100d0203155035800d80d010b4010b02c801300e8119411034804125600321b407a00c00404103040c4001485040001c04c464605820018414041c220015003408840c2c008035070a9140d00c1101150440c0c0582c42c65160324050034080040c0000843c20b903070240409202103240da220b4001c0821101248603a5494580780c082070000100c2c108405031513034045c070440840e034100070900542c0288440da00070f008035100714400d18110082e50340106031820303d041b113840858540c0303c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 774430575 1250 774429325 774429391
    0x14160e100e0c091504350f1b0922051c0207080c0901062a05060a02030a140103020102070611030d11030702070902040522021e043206031f0806010e 65
    0x4610110404030740031801180048160000b200e001f4410588804000001c2c060203a909011091440d400d2540500c0550b0b4810fa0745096012480901c501491100460824005104600f194090030741c01540003d00300c03048004030700603004000200120141009911541d00080b90051002e524160b0040d210601000c0050030751002000e21700000c50300044e10260b11500f090944080345401c01070f12000354400c070384041c50f003823501012081046100450364140d0798183c0040c1144c1e404d02c201030780c0f00041d082c00030780c4e640b2041100080c4400c0501850105150b03408000b6200c2c20604006400c1c0550303031700541c82d402d01c180410010307662448400c55100c860010071920f03000c44071340040003034800c00101c03007030195103050a451407200d200700405c1140c1c0c4492205036000309100b04040b081d41c00524001446918041d02880b92828030029500440707400c051005402507030584d040001003e03801b0030310907080000108804030b11103192590290412003510580c078a610001d03113801481f8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 774431825 1250 774430575 774430619
    0x6080c0f010813030f14041d0901090c0515040909060b030c060c1c140c0705040b040204051516050604031218020105070b0403031806020714160e100e0c091504 70
    0x4200d103a558a0700401c03110300c3d404110040c0c1b076903c80c0c4a5280440e6480c42420030b04801e0007982c00145808018806c0700b0203284e008900b003121600e000c041100700703400802c1c940403d03841000001100c1050b8440d81c3c28aa02c1038102041c0c070b190784020103013022089041c990040c0700410000d107500310082100307458016000710700652038440000880b089035100e980d246c0007040010344090341400010320002150411a0142302410804003400140c4c041c03442540e0300441c581914a407a0008500903140d100300302203021580c01101e44070b084c80c02c0e40681c5c1c03d4010920348403103075048840d503000300c00c0ca241c8105c500750b00c958402c0d40028440e201d02280500341018040c042800c01d4401e8100c1c4c0095402d00104003200c01080c10320300001c5d03029180031103d24a64247e0071281c01c02c00f01c0c2886d1031030110202e960249240c8528503640c400700410818074048481c02c040b91040c090b4082e5401560500c0c801360300c410f001030501c403d07060b030b02c0c452641ca282c06000400c800304201d042720034042d0003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 774433075 1250 774431825 774431837
    0x6140a0f020a06050106081609230312070305031b0301060504051905091807170c270f060f0a03050c010c0606030206040e040b0a0203190c020c0406080c0f01081303 72
    0x1400d03012030074441c829a0040c0480d08180002401c180c0c000c50740d41c02106003241600c6011203201068400a58501c588421151441105100c40001d00509040203002030180d0744541040400c6411560180b81c04030b000c2903001c014003160b522400b0f903602c814094508184d2465042c142c1c050524000c034822944560104070340106841c4035001ea40c0000e180152003041141850506c2e80070400640c02c0090040c4101c1500040d548800c5c9111030111b1000006420781000074000d0008a0200ca00d4034021303101e0003c010380c8288042c141492040003901151007050400300208202131540604591051036460424404518003241c410045002400e198501810074900200078261a51010350300280200d00000d8082807040c1c814881c40c819840b898071551400304d0b8200324041590310a124910311002e001c0324403415400001307541e89600440f00f51100400c00281542e54175046012a074004407c0c40b01103090200d0356144295003401c00f1203107480d0844079005400c503107503030203020444 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 774434325 1250 774433075 774433097
    0x50f07080c07081e0c0a06050c0f060c03061e0a06030203090a051c0201060807030f030f0e030609010c030c021b0904060b09041a100503030315061b1606140a 69
    0x4030004503141801c1c80c0c02520081c6586484490703c403003d5401030410883c3c1440c803071310303404004103c102070041c0040c1101020340c20801d045850f40c009082c1c51400f403042c11081d001004040000300e20946590211541d84d00d01103043c4408405880b40801080381c840e5942c3d0400c0d50f403110f010b01914010300e80103071030f0742d00c2901c803504d0f081b08000d028000f030050a0a981c02c03880038a01a040180c6560000d105807a550000303240d03544038031f20010b0a101e100e203403d480042d104450005103000305191941044014200080c200001501c100c00942e40d00c0c00c0c4428404d4150083c519065014006085494151050640c0f564040b4282030b01c91001500040c040101d243d011440200c8094000300484c41c151516152034081450600c0001468100040000151401900945002402441c00c5465188060070060303500781c2026444002404407041c02500c00f043c2149000e41c140052442c0d1164080c0d99915401c00c0c0c00800400c00c49220380d04403407903080c1c11100542c2c228501a94299 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 774435575 1250 774434325 774434333
    0x220803070e0a0504060f030b090309030a15020403020a15030e010506030718090f0b1803040b090405090708030307021621151e0603150b010206070c0302070306020310060816050f07 79
    0x4402d80000d07512a14128000c92404641a000007ea91042c42c2d1000e580d103400542547c1c902844030601d5165101300c03003001c0060742d008401b0034080010b510245c1055140e81c001071542d00185c01040b00328242e0507108003c158140142115480441c0080055040101c0826242e1805020b42254000d80711400c104c1030510f41c0c402a40b0780d800c003550360b26507041c070b2a103052658000d481c10311003696012018102440040111012114030003043d502d4040c03620280405484002e1042c2d52030701810070300048048082c0029885907207698003600031000c40304230401c02092546c00c0034412060081007043d000d01840c81d0701c1451a00550002c0106540745c030050050300301080c09902558440d03034030000e007a615030030000030340e48944452200740c101403035140b0032181c103420040d005a004501140b842401290076808082c003a1040d81e01503612034840e10141e82c400c1e1080650000c0e42e070b800300f00f116030095200f900400802c0b81c00a41c0e4441101c01400b90040005264800d840007420100708 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 774436825 1250 774435575 774435589
    0x311060a120507020102030105030d02010507050405010c020d0204050a0b030d080621160305030406091527051f080c1c02030c04090e0c03101e050703140f220803070e 73
    0x2600c040038050102d850068030090107034100f84110741c007038030070b6007100107840d8018012107100702c410395516400c05141c140111912074000038140e82007030403c00ca00300503803114060036104103d100800324a444010040c50314000c00645c8140030412400188842c1d6999980c1c05001c45d010710542280d0400c2d50145582010b40d0f803102d49050300d240500000c1000008070182c01114030945070081c05554460581d42e111010b0900f400019100360080c4a20440403051600209a2100d03145901c81d12200400d1901c00c001d80c8941c40c1c0c040e0620b443c1ca074240c0c09261a50b2010320304c0c85060600041442c1e00740c0412880b00c4840c13147e500400010310315000642602c0040c0303040301e0709101080c680c0e400f0030349640054540b140240141c24103070314000f542d4018003c5064655040300c42d4840402c24042c01000007800010070552984500c1000b52020040c40d406880d486101e100e071410003429451100701100e0080f01c42d111151240404640f200d416247d002e00d036411701d02d000302d201c40c00040c90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 774438075 1250 774436825 774436847
    0x51903060903031b0903170a1b03090f0b1308030427180f11030c1003021303020d1b0e040f240e25030b060616150b030c04060311060a 59
    0x50002d00e00d269844256022172610300b1640100d480e40d41d880602008094684501c04501000c202c000c00021899605900e04d20710613802403410203003807500c6024a01320b400e441d074050700184402080c507030a8014400c1080c8002d1410500a510702450540c4104a03800c80c2c0441c00070003d0039004204003c01150441542d03181d500707407a030454891601d050b101015070b1081c03d507941c4d0085403103030119081c005468444990010444040b4003ca240e0840c0030394840305051000d501184000801038a80c0d4608130040e5101d00c50ba9100600d405074580ca4a0a040e172083d05915889414000843c0340307098061689034000c166000504208031205d0768075071044805010092414046036001800400c126660140008003e40506151304213840c01c01814040a004504c0050200b2400d1a204004284866510005504000c403d40355804035040b012300401c80c041c1c441c02c102426143c02d2003503001c03107001198208201411601d40b00d4040c003a075000341c0c4c02080c0000e42480c0b403034028100901 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 774439325 1250 774438075 774438101
    0x1401111b070f061209301d060c211209070e15060714030c013b07090e010c0f0c0b0a02030901020708070c0536060d050a0b06010905190306090303 64
    0x40030058940074001e41c1d0f102241840340300c00110090301551882003240d03105030310380701103901514040c91f010003415500c1074812401900c0340000b0102030f00707002600d8190092030241d20341d85820b8248560700070b02c2c00c01802040c03150803d41f418409402c003510055000485030a0816044480d403001c90410b2144140c00703456203013001d00303580713010f94000000c00040c1202d070028409070070720440d071920060504002030707094668516414992000d03c0740c82c1d04000161001c903003000d50f85190100840e4058032a5100f282d4560001c0c00410341c000119450503001c62070140c070b4031511601c940c40c1c80341029100b000d4240e00007002c01c138542c100350141d9503020782002c400b65445003c0d14100358408000d100c1e043c00b40351120304d41c24081c0004041202100d8029a41014012820712055a0390900400b031560000d030790003081000c1002007051414692080c03030b41d400d007410b148c8000f40c4009095841036116020000d01d410740409100000710032a03603c500e011600310b800f1700d406d501510000f481c1348 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 774440575 1250 774439325 774439343
    0x82d0a081309051f0b0a05071401230403080105010801120638040b0d0203191511030601110f0307080d060506070f03030b0306011406071401111b070f061209 69
    0x1100203404c90259440c4164040301c40d1070980e0792503090100740d02036000e0300001b141090010b030380410304c0d045031074070280c0000c0e00020b000c40040080c90856440d20510440c4408402c040108040c0c000314090701404090802d20b00c650701d800340036031003d401100c009003200e03121441d2050901d030591400e44102820150031402e1484140da4408006400c6221032042d814046401030500703004103076040264024028290a41002d01c0300140b014032107a0071070b03103100c2c1d810f060020301d1854485c0d81e00c01400f010360310b80d803400c080f4001010203c03130405e0031049802c580c02942c0921800012608442c0d4428080782c0c840010400310703030081c00741e50b1001d50490390004504042000f0286074556840c480d8904202136800a0207250b510b60782405080340800e0001c911910782e1810704050b06e00b147c41a0440102501e0040700340d42522104035040e22810404030300c1c0c0751100c850700c4803400421f20200c018041c151400b00f45c00049126440780506004040d6034050807802140c200d09407031a0000204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 774441825 1250 774440575 774440581
    0xf0610200d0c02031213170c04020316020105090d1d0a0915030203060106050414040905100912090b0f040909021906021f020a0e0609030c0a082d0a08130905 69
    0x10300b25003071001c002c07803003401000402c895111042082c0c0d007071810350000165003282003802d9a42415003102c0212030500c1501d170341b030006584030700066205000940c1088400c40001c04040e0954001410030400ea80002040081d200d42c13100c0000012550802c00c100f0800d00794011401d6549682c20100e030303e81c101210491501e800d48103010881e842502200da80e6a60b454044031240158002d0820350314919031802114585900480080c030300a03416070f480c005074009403400300c9226490444080c030a400000b000e0581113514035004100d4034002601c0c1290418014625103d40d01443c048980d0303402c080c0055490b003d002c1510b401d418403500030181d03140e10019582c4c80070042c0003a10002c3c0070400b0038031625140247d600b030102c96100d0311107400c2d88204102c41c507045042d5660301442450320058459072400c0704071000346140400b800c000d00300040c100e000005c2c94920480c14082d140408442d0040024040114a4024078459110403081080c0044514150b10040105082c1030038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 774443075 1250 774441825 774441827
    0x209040b09012c0702070b0d110c060a0f1109041a120c091e0a1d160305121201030b040c03080c1006141309020402070b0117060f0610200d 61
    0x500300d22020450701d0814007043c40c40c0c0001d56041140c1c0f031001a0032415042243c1d880400140070308040128004c118441000e864022941000382110400d071300800902c100b880403440303210381000080b141400a984981817512036485402c103a1030249030354580d44c80c0e92041500c030300304e072800c0005c0000c140c040c0e03545442c3d642e6504011605204280c100e0210740c0d1001c1d00d04030103400701034820452540c2d503100840b00000344001c444c046129002051f588840507414040c00d020340c07540301031150b074243c00d6082141c5400241e1507108010441000540d000030aa45c004d181169880310a144440d525403a003201c6100003680010055140171824144450010400d069003481a00c41001000da540c0c0034000c890804064461b04148403e401160403034030361300f11441d114009080540b0304283c2d5900c1c181d1000d800d0784801d00200c81d800102001c0c600500040c2e4002101c3c24000c189414079800140302041800000c1050200c9030048800d08561240361145014094040d1040205a448 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 774444325 1250 774443075 774443099
    0x20303090d050d030e03030621071820130b0d150e01080610240207050a270c020601050f040b0d050303061504080d050901090b0d0902150a0c060209040b0901 69
    0x40301c0c2010038100724120445c64000401c1c2c030320072800101000c54070615481c0746007940c000320320380300164080d60401040202007060703410300341c10480307000182d512055800241640c00d000740a0a114004010a5041d25200c1ca031030b0056818000d1041d07511043c01c00040c0003407101205809468450940c0000d240ca5199503182c12201e10300142e0340340341d8615004480782c04141c00703400601c06009101910301c04050171032008000044c012200d900c0d46840005000608960000003810040c0d8070310f015550000f0718401c281158940c1c244201da040c9a030113500c03000140034180c0603c2d034110007104141c0c0c650b00451003040b0083e04005100c036a0307040c496100d92046840ca40600304540080300303010340e80021503003141c00740c070041c02c4850740002c0e04503000e6200b10001410003211090100c1c0d0901410018600c3c00ca2015000031014043d2040c0110312001c600c410300d07001c40a1014051650f008151140700a85c48507005035100904400100248441640160020340d144004240c2a007001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 774445575 1250 774444325 774444343
    0x3c0209060301020a020616090803030411030f0d0804060f02070206030f090d020c1804060621030e060301231207080102120108060c040308180d0303020a2316020303090d05 75
    0x6154884503545110515080c0d104d0645040d0041e03000c040052481901000801084041443c02c144065601c440c10381c903640050780c05594001c400340c28564039282c204492007480084078090030110300500000380501000810151101d502c84207074014810480e4120703178000303a004146646030b04200408145001003154061020306c00c02500c1135115000003010b414010000344208101e0a10b0706a0450b10000617108458860300c4900110710001ca03280d407082e9980c2d0b00b940102d04854181801800c0d681204012401160100014081410a030300902440300000035000141c40c2d520004c01e00d0440105c1844156004856000c9040d41d419001801c1c01c103072240d20303042c1740d0342c8030742480ba200c281c1500c0e8214076500400c410000101d03030381c002e0050405460b298884076441040400c480c0001c2d1081100002d40c000b4640960725040103004000780140303244026500d801c0307490600507200318101b4002c0c2c103142e00d0112003150f60810440b0940d071406170451540c210700b894802d655240f44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 774446825 1250 774445575 774445579
    0x4140301060611030f091f11070b070b060607170301060216050f030a0b09030c07150f080106090b07111306031505040f030806011e050a110c06073c02 66
    0x8000140c0c64450010101c07492a003801031351520b000c520000ca0b0a40c007212409400400c0b100c0c400b0b8070b4100d80e01a007101401030b0b0300c940c141e44241807a030f070b42000c82c0c603000342524190034402c05000c108003041040d40043c042c0c0742c0d03907503c1805003803d68090700042c80503c00150000700101e132003580440c0340c8810311001016103244589803820007001c8031410202a4160313000e81c5403000403d01c0000031030f801c8412201540d140250240354a0305090203a00880c0405001007042d0351195841149904e94403000d1501c01860750500d0740042220030741e0311a4015104000c5805024030125200c0c003c802c00c0010022802e0951050100010b407a0b1031100340c170740d4107070850341d070b41c1d01c203868010180310301c1e8050b8003101249029031341070f6000704e4060407541c100460352040c0880401c10740407410881255855950f10380300072101c0108190301c06e0020306040d42009840003990b488040944900c607a11400309810004044070000c2410703007445485c91103d80440640f44c401c9100107620341e8240c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 774448075 1250 774446825 774446831
    0x4061407050f031b0a050a0803070909390e09060a1e06091d0402130603080c010b130b0a05040e1204180c030501050904060507030b0d1401060812121b04140301 70
    0x1044e41039112091540050039540040000100182c0d18800071a80440281002c0c40c49544468006003120036121501a801000660300407003a6962000b51075a41b2407a0200000e5501e4450000c181d10030075941d8500503804000404c4241d644c004000000e0080000425020191700f100141404000d12030f02c008160b5100001c500f0615100c40700c24114000d61000360b003900c46500303010f011030059040400d020358a000100000e00c0305001030005000000c004900c0245103020014400d9074088007146ca145171406241c80d03511001a4402201c60480b8001006e88540c101640dc04580144400305120300080101d4000c0001e50340c10b54048034071008001d6030f45030301d13829400c9400a0040a900c520483c0000d0002411600110b500a8441c900420000146404203610f4075003c881120b000c1d80d1200403510700305091180c040140506002000c0091186609c00940c0c03040402c100c514035051000212695003880c418400c8100e0500c04c10780c2c480c1e5401e2907003074030702c080745580e8400d5007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 774449325 1250 774448075 774448117
    0x21020105060a08071511010204030b0c0d0525030b0406240f14030402060a030e0712020f1c15061a040311030d0f030b010c1a07140a0504061407050f03 66
    0x143c0001c4e03000503500c1065140040b062007840035180030041d4030303101c1c400399000c1001100068201c5500c40c0111001c2c19406d0b00c4030320b00460041a91801031110180889c070501c0c0034a0700e4446d030f8454031010224100001c2492500c00880e024002030742006003104c1c2c110703a01e89030702ca030481103495500045070740e944c0a02e850030600300c41020030401084506282400403078050325061006082101c2ca50400003010103580c20341d14140404e0743d04c20b8060f0303000d005840040d81449041840c041d0404c548003d0b01e00c5e4126080810350b00d0011014204202081120309030304819482000580042c0800718206065203002042503481800100c0d4002d0110903024443e08000810360200620303500d0303144186800702c104a0003000d640039801e0401008240308804108802461502e070782000741c01044520300480094030000070b410320811500c608004c41c214169101c010f070f070b003512010b180541400c01c03161280c1600d4080c4440181c50307030080c050801d003284400801420540b00c83c400f81e0003105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 774450575 1250 774449325 774449339
    0xf050c0a2604120320090a0905130b1906080c011d01270504050c0d0c170c070218090a1b030c290d0501030507050d120c21020105060a 59
    0x440c0741e4110031a030240102090000e0141090a101c814480c0f80000d0342604041444100c4c110002e860300ba40f6000107911a038904040c07002c04064070714802c090000f4242403080c040d00700080070000c1c1c41140c001012641002580482a50000f944038082c0006502c91500c0e85d26402c806e00c2d50b50100d250341d028480259a4032071100042d8005858058195841c407211041c400c540354104100d03205401c0300810341e07654030311585000f03082d01e07d101ca072940181c542c5401218240c0b031890083c0716185001050840c035a200070380e4040c1c503030708038103440300030364400300340c0304101841010260b138084020480252800100c00702c285005080c401d02d441d45030010114051060700019000b903440b20000e2009920200e06c00030242c0071915480c00c800c100340024800740d00b145600038141c9032101d00401c14000c0811091001d004100c07480c00c5160801d964a920204148189000384214541c1900a1103803490280400d108101e0100c90001d40f2208001c0c000c01c411104036200d40a02d28001c2240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 774451825 1250 774450575 774450617
    0x20105150f0f04050a0b0a0602030c2116110a0608090c091504020c0a020d0309090b100e190f120c0e0903092101020f0d0b0411031501030f050c0a 64
    0x80780d00a00b5032034010742000d0a0001400004011440641e1510300c2c3c240302c1d448243d540720003001c142d4061520389103894441030510a030b5900c045c03900344c03090f070175020000490000c0720907916035001c2c4458442228a0030380b12441c1080c82c2c650348840c04640005010350400704091158500724282c9800c10340d540d0800500041c240c0d040c0d50300850f109010f40301d505041d4010b1200c00351206c119054000f0ba070380000c2842481d00c00c00c80c0046c84800040210f94454005c250700c261040724048080346400034020024192074124510030005c609841503c2852200d40b4000b80c0811a0003110303a940b1802c03c04004a0080700440d044c455403200080c800c01c0042d2098000c10004001e549484900400c010b0f11103051124080c0d4603001c20089070221800744002c0c64118581500180c4508240c0c1e5080110b4050707038031041c0120b007400c0c0c50307002150744442100d5102c026a401110f105600100484c01864000c2d54614540d2130101889140107140c0c001c2e10400300c0d5a5255040d860421000540c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 774453075 1250 774451825 774451849
    0x90b0f0a0f020d1209230c1201140423070b04080d0503060a090b150309071d06032d0102040e061912020405041a1602160f05040216020a0602010515 65
    0x1e24844120440740300d030b581010405c0c03409250b0109881d400c0420a0030b000c441001c040c2c6080d0b0041115028600b1b00c01441058070300808000c000c6c94000082c503401c440d00c002c0c401080c500030012500181c000348072120002124031004c440701691984c41c03072074040d80a4083c61126101e0710b60301c4908244640d044910501000c1c0c40a41ea6600d07103050700e005814010031255010071f441054040306405072020314072928500c1d000b0210701e403420182030650b4914401c501e013404105820032003a40c500082060303502e6120300c5a070341010a10103507401105048a401c110340d500026000441c2c0218008440c0149011034018002c0030340e800030341003030001e1481b03a6406000d4040812016182a0b0710080e4080d0103041c1d05c404101e401e0f4a4191109412030b16600c1102d030b00310400f000e8550410170b06400440c030341d40c080c00e8541404480c1407030140c40d00c1051320480d00001c0304109114018624081c1c0782d07001d410a042c3e25110803007c0d01900040f10030070000040d05100000c945032140590032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 774454325 1250 774453075 774453077
    0x100204080304120819120c030209010e01110c0315090c06070c14060714060a110a23160528120507060b0901180f0204060206011203090b0f0a0f020d 65
    0x4541403400d0f8034400d83c2003c1040c00c0e1078a420034410000301e01d503100341e1120060a41d9a07010072a0190751411000c40c2e800040880400d0301c140807040d42c50760004058000e400007400d1100d048552110071518203c00d6162581c2c00d80030f402002800401145c00a030f0080c0349131816100009925800d000c001d00500c64040c04841c0310040c1000300c8c80d5054001983c001025080b0b601e440c08940b902003400f03000401d00c03011944030300704101d03801005202d402e084d013804440052030145c0c200001460380807020640d0204404050b0040148010a400c645480b60010803070760540185050075900c0d598036442c01c0d01c070303c01201f090005003001191940c2d005640880c82d01c000200d100b900700d8941e044100b0449541b980e40840058590301c0440b480c0c0249840403211030003051040c00b40c41a10344144c84004242d00511040c4032441e0003041c40703410f49100400b024401072a5003411295000154844030418a0016080010700044030062101000949424074105c000130b038201e0f80c8a08400e8010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 774455575 1250 774454325 774454327
    0x6030615120c03030a0c0506130c051519200703080d05060111161d040b2e03050d0e01020d020c040507111204050118080303060906210f1002040803 65
    0xc0300a2401000d1088294401412100015080c1c0c010a245600081c0d1010101d034584041d042042810481c0680c800030403c0903600d00d400c140d407940040c1242d0b0062070301c503005444003000008448030650b805e002540341446c001042c01c40380a0106410174680e00e6880000c0c064403142a00700091040803280e00c02900d502c1e140d0040c941c0b400070100580300e141003210304803040704407a0301000601300110813061444030726032030100310080b04e000740c0054004140d41c000400c4045841140070541c4410000c5403002107009488040310000344000035000005000070000c000c2c020002140da0201a05484105d007441506005981d1411080c2140c030050344410b20700a05400c0c1070300825040388007400c00c52804005c1401c01424050491101108004041410410b56a2050300f0303082e00c80c20300046142c040d0600c4407950b128400145664026030042c40400c1e816128410003240d0301e1046140344642d02500404592200303c40e1600001610541a00680024052007298102e89010f0021 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 774456825 1250 774455575 774455611
    0xe100602060420010903080310060e0a03080702041107080c0c01030b01050309100908090402040b130b0f03040f0812010312030c260c0d050112050106080a021810051512060306 77
    0x1a10a20800c40f01680c1003180e4010000000340e0544044d40c0190314080c402c0d0002c0d4105907008204d0700d10500303035038814802081c04001007a4110100c490442c2c05860101e14106001c01b1030b4242d100b4120001c0c080b22000035981c2c090035003c113490b80c0344c54090b40c05004810f0303640c0044a03a80801d80b03407005141c1000018610010352035110403207092080a800c1c0c10440c42900003002c070b0300268448440c00c0d00c001200d2510306580d5007521b015180e0402202c1c280050010001107038080180024028461280034205008102d03042c4c0300b43c440e081250285540c1c503440c208000101220504000c00c1c03c014006242c80e000d040007825240f00c40000e200741c150118001c030b4200102615201e8440c2041201d02070700c0340140142c6018003109152180300d05680e14103a403c4500f40d9100325142c0c0c02c454030000050380d480140340146078801e003400b190741e240ea10700d1382c000000d10361040c4c4e8440d00c041c080b041074220813005440140c81030001030780517550702c00c103050702c408040b1344403600c09400c0511 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 774458075 1250 774456825 774456863
    0x60703060518060a150c0204151a0c030f0703030b090f0402100e040b0a030308040c2907031701030312060b0316080403020709060e060406090c08060f0301020706060e1006020604 78
    0x280c0365000343d00420189100350756111264212151015500024403101c8003082075007807500a107600c06c210380c0340c021003c5140c060070b001c1081040880e40480e2800103805501d0f0403040080c2c0343d100ca00c1d0010140d50303a4151070090024a0b0680c45035024020f2070000a4620302c14081c0c49100f1500648066210005208201c50382c1071010503040d0700a90344c1c458015a40c07509a4a200603509c2501e880e5540d0a103410115407013a40b690000b4140695246020b035140c1c0801c0a585036a80d00c404c1c01600c41c40030b86001e440c5c9128450031a07200e100b40000010625030300901e081e40f00010707804200328058845a04510a100480c1d81140d0744600c1200c1c048194464010294040d0092041e24151a1100e4000090700e450780d000000c02000b0006000707080c03030944a036200410380c00380208481c104034800602450710003001c1d180720b1004040c00d130809071002e404503031031164041c40030006151103050310003040b213090728a10440104510b0102c1c17820f00001d2241e00840e006000780c2d9484c40c184907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 774459325 1250 774458075 774458119
    0x2010c1d0303040e0f0603120a09120f060c091a2106010905060a0801240c0b040c1d01230a03080c07030606080604061a060904021b03040b0c0607030605 67
    0x6031868252008002c002000d010064003140a0705d4003d0300c0c2902030411200f0145840111041018107000c00c201145146030440030001c1103404861484170b8010480c00c102c2020101d680018285508008410402c1070b4400b03080810b40300b42c0b81c91b1154a415600008001d80100c01c000070030290400150994400c400303007200c0e48018140b41543d0061b4451000c5140d80d00b001d03c695010034007450050100c15041071000b82c42004004080e101030030040c40003440b01643c0d40c0040d002c0f44585011500303200c0c40c005820054506211303440700e605c0e03090602c10080b140034800c200c030b2980c10070307000300040c0c1c4ca0162400d0a00300c000c100303007030741415502c511606902c00e2804200500c2090300000c0040d25600840e4010305410009c2c1c5a14509800d1920035a91200b5001c03510a8080c041c4074035a0781c83d41d055603101c990a460040e10740000c1d0b40031a40220706511f0152861001040c00142c0b0300d140c000401c5c1074040720301a9071003a181e1900540546000b8020300741d000c41c00d00055846900010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 774460431 1106 774459325 774459377
    0x7060213030c1d0106031a033a05040501110f0a06050601110f19060603020a0f05030d08010b0f09040b1009050a0e04050c0d0c0b030c04031202010c 65
    0x4080d240c0f4031030050007001c0134155149803860100600f01303d0f80350b000c08040c00310341c2620500401d88100b1010042141d05280403a03016000010390b8215240048805440d0b0504040c20b103030041d541e80704260308480c0c0c2e13840b40080c1040b00303020411101c65500d00078400000c0d43d0a04a0006014180a00301d18030b0680c4070070217589106100041a8259080c410400c2500b40c1c100d180c21740103054541e10180d40007500c01008610010b0241e000000c4a82c1182103c01411107181c041d983d40034244140048d000c800e00c81500c088080710300405450130004d00014070054490000740d60807100030139440c0000c1d4415024405410245e0b103034005880d410740b2114184c601907030355990b10301d000c100d42805400b04e0200c0204010f0700c40d41d40c00161009080854485c94003c0d00700a05030090b2100752004928002154544e038018400e60142c00003660320004040e0001c02c0c4455111603107 = true := by decide +kernel

theorem cover : BRFrame.Cov 774280575 774460431 := by
  have h0 := BRFrame.cov_init 774280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 774280575 ≤ n) (h2 : n < 774460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
