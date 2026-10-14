-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2108
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:40:04.96565+00:00
-- url     : https://prove2.me/submissions/3ac81b01-7a17-4300-8050-9809d9adf200

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 378956834 ≤ n < 379136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 378958084 1250 378956834 378956839
    0x3070203070503040906090c110d0507060906050c0703020d08010f09050a021215011103031306020f04080f070906050102211602190501260106030b010c150c08091b060c010209 77
    0x3600d6949014a8004106d03d00c00c0014a5040490b1074444600424140c1e944095683c054401c1c01c54103a0b0485455101d16800c88040e43e4500300d841c0402d403a4411284240c01e080d00181c0e8400c0a4280a0726010030466150100300900b401845005a160419001c446150102244c6a122110700d13501074040ca030035110814030608200712888003028240d0880390780c04c2c3c13155442c03513005281d107d403644422914020b407200b0b842e00c1140042c1d030781c0c0c1c010300d0019a500c8083d4105621142000d05290304545484400d03407090a00380084181441804001c1109000400429000c460640782c80d280f203c00780c50b40b1880100d1182d00031203880320480442036004107405c403991701311009040d0603c21405003500003200d151814040c403244501c1020000c110003a50f400580c40c1040450240c9000040d80d070410180100b0800007072021441425800c422a20200d07601405410061171f000c1c1c010185141a88040c41002d5030140808e6144800746064a03500d980d00c000d40c01050280c40f4004c074594 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 378959334 1250 378958084 378958087
    0x30506040b0708091209060901170a0f05060d0f0311011104030b18030310030b06042007120503072f030309071a0a080a0f0b100203071407030b060603070203070503 72
    0x1004064420a4401d185944804455131242115603030748078110040504410703020483d8007928900807024100102d0705160400002844c8118440900000c0d030301105c6540c0c41d41000700c4d180465015083e03100d00305903840c0c0c404c4045901ea039010040a1500078083c0484655510450042034103c0d0901154078440b46954503900e160110030303008100d803041d41d240c4519020f154103983c00f1040b20b000c0c1d81c403071070020205410742d01c501200500103800d043d403141d52011904070321410000d407216500c024084054584249040c00d001402050404004100d400c004205100307130400c403400418000b04042406c1c03d981d019560141e94007244503a16144008801c0004140001030b500c4140c413980f003200c0a080e1a24a40501c240c0200c3311000c000c20200000902640ca03075900c00700da031078103218002c65468a041c01140103680500260001030f0400210403080c00140c85000c837100100000900c0194656142e003410a00c001c0e04030b0303104020000106100398801c005981d0702135040016213 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 378960584 1250 378959334 378959341
    0xc11040b0303180a2306031e1302040506011812030203090d12110307020604274b0216290601030203040c060305060420090f1c031404030506 62
    0x903da2070f0400504510600c081070780813417003d0840140f002c80365018607019401d2000e420801c0040d40000f40365507d0300113000c124205400c25001c84c1800f48114612039075002d10140140000c1d00d400404081c1031004070108008008481d040134801c8400a0610141d598258030f01241136106600409070300403e240c40390010f1015140c030441d02c01d0b040d5280d828420100d5a0140d44034000d03204040e51000c410f11040180a5501c5500d5628070b0691042840ca500381071031203821140d46101c0e03402800980345524a00c1e100320100300e005114103a60342c400302a00c803511083c100e0115250100c1558009c01d81513140c0d00046a1000ea40d5407115040c0040c1d040b00c402440c10314135401000701c54056807404500c680d4000c0c030031603000d0f80d0000d900e40302d0941403101c183c01600d400b51603150044e079070740d0f40d540a0011480d83d041404148c0b1414a0761018a20b0800a8100410440d24480c0a030f00d0505243e01e9544005159920707818100601c0340c00e035400d50301104c2d00455001401501a50041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 378961834 1250 378960584 378960607
    0x130e0106032910060503130f1e060f09020f0f2227021c0309120b10050102070b0304110f060a0f0206090706090605070602130e070906020307030c11040b0303 69
    0x24400c1080d00104006225a1040000340003101e244c480c90012a1080000c101103124041c0114542401a030200414011503900c15101e4255103580441400310500000208100360281b040030340400c2c00d0a01c0004401c5e000146803158414240344a8990700b500103c654441003030140000e803031900c440042000080c20031000c1d00e8541c01459810041354140440e040c456403841000c5c940140a1403039180240100342a2440642400c0d014000451000501c2c05000f01712481c00901c640d000b0b1a25042c007a50400780100a5000181903402c540004d0040e80a40070550303500c80d070049956180780d0214404140d580d50800d061b107800540018001030b40701d4021031504001109076003182e01580d6542c180e16181e140c54000c180000c1c44002003040503500c503902610782c0c2402840c00528001c25441d203515458140d50000174204603080070041310316000884c0f00c000b4255030024602d030000350b940050003041403a2004000c021096030311889038540c0d07444100000c0c1301070704590703480700745a50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 378963084 1250 378961834 378961883
    0x70503151915080610030305031801060e0703020a090509010e2a040b0301140a05031f0b03030d050910020708090607030e0301050a021b070302030c1c050601030b010f08010b130e010603 81
    0x1400031511603600442c4520703800581043c2140d402d030b234505003103450b01042100d80070400001c040841d902c0c0d880120740c0f0000e121115000301c01039180141e4400300c003840070340710345a903030700042c840e040d03e20040024038040340800350300407000300316a44040d00100c50306a501040141c00034600301c0100c0c0210350b08079620015030503504850502c1070b0480407103042088001c114000d003605071700300c0301c2c884200d6003514000041d10b1022071404500d14440d4030200c0e186030004603d80c00f1040e25101800305411060112401481e0034500962620a090300c502142e840382c0900b0310f0185a0002c3d401c01418851a0040c3e02c528000340244400e0500000b070401035082413007045480b900045c000900329030b001030020201c1741c2c06030140801d001c1d18410400000b0f0710343c4040120b0f40f004440080003500074800240a58030407114a1600e50405032020b144150a0b0444141c0c0e80c0350600b07400b01c668a020540208400c8001e001c16040b0395030b1856405442e0f160300082540e10a800081684003d040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 378964334 1250 378963084 378963089
    0x3070f0c0e010e1005060901091403032b29010e010519110705010f0e0d081207020a060f2a1202040b0315030a2a03020907050c0f070503151915 63
    0x3401e944c215444008203c003500c01e004815002c1f40c86181c08014411050300210700644009065908201000d0142c0d50104880e0804000d060105c0704030400041a0b413191104130b042205480000100d0110b050842681c0c40e07150a06100f0000c3c0400600d82c410302c01c81d1030841d010300c48600c105140384d0002d8075480c010518170b8100c1c02104404503155108442c4119900d9081d40e801e11050746050501c02c0e01c081c030013003e60304041d00b08680e140310208003411602595030f6900800e4098002d0900310222070b000002c5c03102d100d050180d00f00d000f048446070f481c0c001c088035a089900b484801b50682c0d817000c0c001880444540085400102d42c0300c000081c41c41040070300901c840000240003011344840d80b5030001400e602e502ca50042e10310600e025980001c800081c1c02001903512900012144c5008840c00400510300141320b41080c04180700c01c82506000b034004024240c2807000103a100e408014180401c0450b0400046960f00400040e4040381c2900f00100101000d0310300921349002d0a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 378965584 1250 378964334 378964351
    0x21c08070816050d0e01090e090a0614011805060d12020c0a0f0f0e07020303011a040305010f06170f1b0a1a1b19020411192102040803070f0c0e010e 65
    0x81070750480003400303014940c6045c50b050f51020400d0381001d100d9516018045c1800500e0311486104000003006880743d01d0146203c00480c0c2102d62401400c0c45698204500032681d442c108010301c05c1d5501d450481092480c1c1c4909101b20300c0080d007100320300d00a000407400380d02c40d07980a0001402642c00f01280c06850509103801c05094441c1ca4060300610305449440040e841040100005141d00440c0b2801c0100ea44d6043e180c540d5036103500d400d50702051380082c2e1007030703503100b040042c0340002d40c003440400b4071440035120702c401101603980c580c0854000d90b000c0a1141c016907005640e103040c008068829040702c814080e0002c0643c04898000311502600c15002c02d09800100b80c0004203210b012040d4814040089019403d03c4007800924091003070301c1c0380034401e1111030203100030000c000c2041a0f9440107140b211050314a801007060110314441c6104010602a0140200c01c0320591500201c0e403190b214900d28240e100c0012a601c091110100180085892055000384a0044284 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 378966834 1250 378965584 378965593
    0x9040b0103020f04030f080d15090b19030201030507030f050420090103051b06040b16051b010804111807080a0609140402010f110a0f120309021c0807081605 69
    0x20000150102d2107180000b00c0c02c0103080c03208000040d894a422640d06106031285814044041050010384035484040c41e403000100c0c0d028048000d0f0741c8665000c11408440306a40f04503000e94031090820030b804041d04040c1c580d0001400d081c0a5040b501d10046c80160404c80c034502810705110042c0510f40c10064040021503c440915120140740e050b80d420202420203e241c6403400340e04030200d1107840380c000307500b400300007040807452020b401405425160388183c049245000760402540c15200e80e0410030303500e4240302c20790f404504560700941c000030b040c039000c0d450000a02e01c2c40c04403100000700c807603010402046581c441d5085000d450618014800c0540b20b07032184050726981103801c60705181c12000500990310543d89440788903100d00b4410030b611400c64034541013449e030160549195040300300c1c9200b00014610200d40c500f0481c41c08103d94801c80e40010420200301403110203c00705610040705000c00c040441d205580e0002c0c81c10f170740e0712152090540e407000030f1070240c0c0d0720b014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 378968084 1250 378966834 378966851
    0x2031204262109150f030c03090a0b0406090b18030d0b030c030a08040608060303090d021e090702032a0703030c060e03030403120506180a020c070f060201050f07030606020c1203070b04080904 84
    0x4c010b040c0c680b030740d005550345410355940342c0f196038040d0001061000380d480382c800581d0120301c0c46070714540681c8c010600454240f200e0300782050004405811540240300840403d840c1482c080242c0e174007461040400704041102000203843c003001d807180c860b858080c2e140a00100b100300801841140c00b55140d0040a82c0c0c1e6404140e200e00a00d00800d13048101d0104000042c5000d20090384c41603002c10380300d90050a5440883d00800e421545040568000240180d02c440b041100c41d4903082c8015554080808620901e17860701064031004040c0120060b59104005958000000c2d107200c1004a03038803480c050a0061400301006003a02c1054a404040b9005040c0105400050050041c5092043e00c4000300b00c402903014034203089260140901c0410090300311002d50008180d070364004102402e00c41c018601100000c5c0100041c103103403050030460b075138011511944410302222408203400414000c98154814880001c222002010400082042410107420701c00300a0300c04212809 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 378969334 1250 378968084 378968119
    0x5030d1e06030c1505070605070f021207120c030c060203070e0109080c0904200301050108010903090608071209170309010f0c03060302091306060503030c03040302031204262109 78
    0x84503030002030f01d0001055401d015000c0000d01d0b04046010900e0201c0c900643c0341c80750390071160140e4107030001500d2102c1300e0342010f43c1040013008020000684916290540c0d80f8198440440e800350010b20816140719001d00d4001d4080c6804a500007006550302c6c9010b502c000e14550708060894040350303040002003a41840042c4403e100030021346508015141c40e142c81020188142c81140038030031103074424a654800303005041c001c1030480c0006c600036280d4900075140724000c1c0c101100b00041901089042c951115003503100c41c00c1d0700c100003500307411400c000403041420394081d07a400c0400400c0c0125102c0541c000701407081e4202d010010407461510031410f4410600c40690f0094600c404996420403505d40c45c40364501c80d00740000d9041d5280003217420364010408480b9103410200b401c00c20f60030305001305040c066000c1d16440c80d250030b1040040401c843c0c40200d40d5041a5a410065183c0040001e41071740d603044026941644080c54000e4101e41c4030784075040c00341050019031000300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 378970584 1250 378969334 378969341
    0xc0e040b070c030f08060a0512010504020f151204050a06110a020708030c030901270303091701140a0203040c0503251502030417070306051e090604030207140d05030d1e 74
    0x32079140d680c130f03640d040c2c00d072008070f0f80818050300042c1d12440e40b15002841c0d982321010398007059200740010940c1d00d407900401401381d8222072024064a0000e00079522004000c046800702111000d400e851030f01c0e40d080452824026410040c03c0c645880380000e215508107010782058001c030b03402c8544a940764040d564681c01341d080114000d620500100c0021360148801e14000c0c006030104c464180410b000d40c00380c03251039506c107902085d05c56000344441c02c081160429101e42c070a000b0307c4903460711906448500d00041106200c981c0c040086820444184010001080000c080315106250420114880d200c5021140f2100a070710340300041e107011440021004800079000745040038600200c1c85030f180402105a252409500c0001c00050424410300d4000c030042d1000c841592414114026800030242450000d80e111408000009034009020380c103940c0c400d41d000301911400d2010a1407030f03031b00d1200184940004252000020701c0c5901000c8141508000380030f84505082c2510200d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 378971834 1250 378970584 378970607
    0x80c0c0a060519090b280510060f02030f0d050901020c060f160305060d0204110f07150c0810090f0b060d0b040b010903170307140d0504020102010b150313030c0c0e040b07 75
    0x20b0f40b890130004841c550300c21210104d6015003240108103111111602003110760423070301e90664560941051010b682c0c40180070840d002c1c2c80c0000d528021503d8800341e158014011006101ea46603030006080c003800b034040d603528800e808111000b504200c00304440c4090102c854520b50000311040c151450321900030343d4012500508041c2803040f00b90203210240403c400301a41000d02048152862990f44000b000f00c2d0340540c18502400060312548030507100100030b42e00030846110140031303a0f84404000801212400c0c18001030b40a05001c02c1c5010701029140300e9440040403420121405c102c0e0130070113202c50100d84c00c022514117a4015030b408401ca000c05024428181e01844100c00d04000850f04403126007414009814108059082c60b400240346a089544410500085507024003680b0b80c2440d04588144000f03294480800b014000181440c2181d603510b003404040c540103401c0a010f0a81001d5404032081d1075405003510608180c0e0221003e0a0000c0010f00c003c0c880c1146109 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 378973084 1250 378971834 378971843
    0x80c0a080c0304020a050d050609070e190c030e01110301050a24051e0f0a030c0807230706050c03070e030a2f090109150f0312080c0c0a06051909 64
    0x50380c031408807086450300300400403a000f009612000ca1107070b03607000242c503501384218020110b914041030034508003500b076480682c3c40001402031090b0180f99029040c000003689500084103188103a0441c00360240100007c2d0551904403900141038420000714140c1d681610030a9560303544034158201c141e8030505c0700050380c0a802c04180c842d44154028881030501d405008003145000da81d007c0140d20440130301c45c40c11000180301b041260140141c248803802401d0032007661400310000b40250030245191b011640d2024084008031b210041030340c130161f400001c02c01152926130729040b0780341e006440c000040349216104900030700d400642c02c900c11364803031000d103090002e0818040c0042c518021034006802103c0014501d5113485107414004e12541a01241c000744004104240716183e8000300e024800c51030061022600880b650f2010300d020745064005a0307180080c4003402d001c1c60032402c01e01d01413060400244112a00014010070349000c01d0ba840030241608a012a015a40c0090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 378974334 1250 378973084 378973097
    0x415110a08041e091d01150b1e120702010c021b010507080304061d01020a0f0504231c0b01030b0f24030a020303040305010501140603041a040804050d030906080c0a 72
    0x99007000442d91408410000315042c40f440e04e50304100280c42c503003200ca00f0001c95109004424420900030002040503d103000055a03091869078036043c441c41040300c880301d072035600c10a4420203a5003220402d0385d803d070b200b90362030401c4d2800030302a002e40350340c010041c85070007500c040b04900100d96100c0d880c0144c440d546800c01607038500c400b030740005105841032955810311a03091100f48001c000b900c1808400143e50703a1948001524040c0c00e40c2070042002000d20080c0200c0d0162450b1084d039100c111102c20001c0d040e071002070360043d2040303030f800d9002c0120408c0d0301c2000160198203050300d12600d840c801c40c0e030322443e4441c400c2c1c1084440c01801c4104080700300890404c0d802c0030f05403080103020b50f00100f10301d0b000b003442d40e40951700c1150103070340d501d004000c0350418088600380762204890061550030191070300e8014004030040210081c6190300401d04002d00c90301110700400c0c010341707042c0c145185800e010b0000307030031441280082110400050502c0580c40210350f54401c158440c2d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 378975584 1250 378974334 378974339
    0x70602070b0313030302091c0c0603090218040c05030d090303020127030c03030b1908071403030a030e0307020d0605090601082e02040504050405030d0e0a02010f0509010c06020415110a0804 83
    0xf40b001c100b01c144151300317050f400c0040802075100c00e40540c4070410441015031508819180c444038a102c10390050f0b0401d45032a40140040c1e07101c0d20030540150400d0407840840e00c480c24078001c080c000b42d00040d8984551008076030029003048202c4200d9000b50020407480b11240d1340708100d880050300c01c03e5901c1c500881c2c8000280500140c02c0400d020f032500103810410300300401c100d1503c2d480e0a40074050114401c02500c1000c08c2540c01074041140d59440409040000c40c0eaa80960001c41e018540c444132060b0300120200191078486030010002c000342c4d051410040018101075034a400203016003000403441d46400111444841d007082c00c0c01d0003103c001d03800320031508441c0c017521294903002c210000d420360300d13800b595018901903800341d69240302103240fa00c21681c0700960002aa04003c03480005030f038101a011502040c1c50820751703a030b241c00340e004035500c0203045801059140b0109001c6030940c410b00507001e8646207034440e400032101d696000380e501d40120600130b00031300301003005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 378976834 1250 378975584 378975601
    0xd06020705100c05040905090102180d060e060f040501140906010918051b0316030b01171c0e01020d080c0a14070510140a0c020d03020c0705150c070602070b03 70
    0x1003003501e0050064030651803010110700251007500204000188002c1414806030203207100f41c1b604012580001c43c5480300e64070f00900300c1c4016611355407098402c0c2d40305100b444210f8002405014014056819030300d0304c0e040d82e041130b610a803410344543d031074410b4200e507880c0403164460103040f026004240e1a880c00c1d01d1840603040c8000300c90355a00c1405503050010b0001c11004031001e004901004c10203c0c1b850500d458421b0303a501c4100000d02e0210100b010074003813020103055480345030300444d0100000c0d03182440d0000024000d000d03980d104020300c01195000d420714619110907403e80b504402000c0040740c10980030f0703e030f036105040d0400a000780c0e00d000d141c900ca0f403184c3d078484a1b42080380603101e0509042507030118080c5640c9818905804150000705640c1c406110803007000040f0161000a6a03018842c1604041c140d00181c030343c0101100b04040c20084c0b100800400d40d0580031000d11943c0c0d004400200d06a1080030000301d070003400450f811098451180e0b0044c19607650703559 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 378978084 1250 378976834 378976837
    0x11010f0215071803060603050c061305131d0a030e15030109050402030a0b0405030408060703141308040b1b06070f0f080a09120305070909051b07020307050a320d0602 73
    0x2201c20b0124107a800703c0c09015040303580740114001ca000240840c910b003040340c07d281200b64400c2c81001c1c02c000c03d41a51038101200000c0c0c440c2070300c03030801340e0038030014450050903006040d1050115194a100c60b1490016000384090b00c03c1d51b40384d500e190003506201844028484402c4008000d0005019007165a030000340d02c580020100c510300c58503034071109610b01e0252000e0312141c00c0043c00b4007046008000081d000700301c51404011941071030959076855840505a900310300c0300d103440752003441032070000d0741c0203004820015559a484028a541450310001c0c968006000700e40001d40070602038641c00305000195140c11071000b684400403111110004c03e06101e0075a00c00c03201010030b00d242800001910b091302c00081e9420413400162550000341c1c018840c40f420202004180703054601c440c1c560f03140d0b6218140c2c666515200003820304809401c05500040c02000001e1065846010380003906450b0100400f40d40700000500810780801d096940c103d5003000000000403034550 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 378979334 1250 378978084 378978091
    0x14011103090609240c03030109060501020321060a03062306181303120203040303060302211c0314070804021e0607030e010201090209162a060b130501060c11010f0215 73
    0x403039048603443c80201491760019a8010381590010006008000c00b511401000d440c090000b141482b160409031141000150718003074001030b02d60301050280d113030204075030091503002005010150018070980f25640c000f00b0840c10035103d84000c900e040c00d00101c415004402100c28031203035501c40340b8085200340c0340070044013000500d5130240d20481440c4040c42c0a24466500421800c0c6540104580b00e510702c4000c1e03038420307030401c50980c1e8040c0004d03580000051000c1c41c6010342050755020b40003054901ea10000201803c030400c900f181d070004049201e83c0c801c07501d540304e08441d1815041c040381e040c0210b6402043c20410080402d01482c0c0080c4a108144004150302100d64045401c54000f41c0d9031181080240e0006420300d42c10203004489444c21502140c13410444004503400d40c042c030b1801902c1a940d0340559140794031102000402c503001650309025a507920744006014070402c540a072130f81d002408800c107103036124141482207280a0f41c0203083c44a8843c00080f42050b000e07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 378980584 1250 378979334 378979369
    0x241312080d111b07030204050708090c090714040e07020106060507081c1b0305040624181104060206070e040b03030a080a0b0409050f01140601080f0a11030114011103090609 76
    0x40c4403940035001c1c0e0f195407800c08000f0001401a030fa10314410300c01a644d002d0410424001304c8000c00115190015001c001428202e601088540301d543c82590210038200c000d01c21500f0018000c101084100100350007214658000c110195445c8811502030041d85c20042400400304445e43e8201d0303040c00000840c840c900f40c00a90341d0840070ba40038840301040101004242c49200f04414000240b01c1c030039046d4114038120303164021054040003100540d0090710001140e1001c4800082905c1c0d000c030927030030720003c0b11542d5961110303030107035a682e0100c400c0000150030300304d0710240307003014010242440030203401942040c08a400984130600b00616040c220780d42e5071840d032000d0307540d800350244140c01b400141c210f00354061849403e490f0120168100c4150200600c101668042c2030280c1c040161500d084107138030b4401a13103003e019500102e00360210040004144110759003849500c0c0c0b507017600ca201640031030960072a1203000d180021640310001303000d810720b03e040a01070380302180e041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 378981834 1250 378980584 378980587
    0xa0507030807140c010507081f050607050a0503121503120909040203100219090f060806060c070317040512070503031e070b010f08061023241312080d11 67
    0x10000c0020590081844d0b114641e4450b01804540f80c5c01240040c2c100d003a580744030b20550b00807031448103000b443d07115090080400180e15402d000c410300c905c074482c3d5030010035039980d208207009082260606a940c4600605030403207040d0240f900040a644d840c11400f0700340c3c20310580c2010014501c000a106982500408805d070300c00017601d10040c42c1c1c002101c0400c192402910300c00610700b208070342060344d59109101e018446581c001e15200e070700103022102c0036030301d91031204000d00f405416400141140d02d8044c41d42134141c2400081d00a490066980c02d1204050310107a540d900130500c00c058250b0420804030010002403010420a00102440945001d01e03e6a94450a8000f43c1c081202c0c8000307000284902d060034040329030002c144407050f266031400c2000103400f142d040040b50041c101044611070039902c8030b060710311280d9910404201108025045010103070301580342e0620134109040041100d140340c3c0d41d80303020550024121400c2c00b59036290b4200912541415180c02c0d2310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 378983084 1250 378981834 378981857
    0x9030607110d030c0e12010204150c17090d080a05030f060618010807110f0307112202030a090b0a0c121404060207051e1006140105031f09021305150a0507030807 71
    0x1182c202c6c1506428039000010707504d1b4600074914400d80e200712614420828140c58913000b03d28800d1102d80030b8940341c00c91582d10b43c400340015545100207800180480008a00302041503040700c003541c0301d207894148890666540c02d040251300d22441c02c0b8030700b0102c0c06443e070341a25441a0380c00b5506c00481e04211071002c028140452804900c114551301c1d0398000281401003040760942c0c40c0100c0429101184100c0142d04940900740f544c81b01450740704c0c0c2c04000204404003a800c000100d9030015101542400c168082c013003d4150b007941d85004c1080c0c0c1c000010061018030a00d0040d100c003100c2c0c02d8142c1c03103681d01c1c03d02031f44c090a41a0b42134410341c80070440d10080403008521100b441c20003000303101a01100c100584140b544829000d1099013006d008a91700f26007120340c0204800c154283c1d100710070346001038955442c0c21a480d141d07c04038810411031480002d04043d160100c1c1c0c0c00d054005010310480301d82c40352803a0319002810500400000a00548101e900802103050544070940c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 378984334 1250 378983084 378983089
    0xb04020f040906080f0a080d0b010c0204060803310303030510050a170d0801050904151509021e0703020a20030307060c0f020f21130b09030607110d030c0e 68
    0x70050303045804090b944802c100a016401c014a081a40c100e002030104001039848842d8980101e0408e902981e1b00c444404c00560b100b0407000003140c0e4003d104101c00303500d07100119501c3d0814143d0440e8000340060205201501c007200d810500908a1424174007819035070212f0141202500420a10340310100124040e41c80d40f40307100182c2644d99441e861101e400b0401403520b04a07007000d10601103100c0051040782c842500540c0e01ca03800c00e01c0d2080c513901c0c06c0c40c0300006041c0b00b02d900b8800f421180e40442d0242e070540003401180002402c1200031903441c030030740c101c82c421140000c01503840a5100300008100d00012502c401000b540c0c00c00d0700b503071100400d0465020080860350720342e85014a08032981c009004a5612500e440140781105520140e113903518100f03040d10380380b0082c0c8407291000c0907403041103644650f2704103a2013000c1a40e60201609a801421000703200b0f009810000708881d119000045910750050014244440e0115042e0000c00f07881540b001000032003040102d864 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 378985584 1250 378984334 378984337
    0x9010c0507060e1003091a0c1c0614030318010305090a080f030601110115061805060d0b03060c031015120c08011401050703081f120302060a0606050408030d0b04020f 73
    0x4040903158040343c43c441d84200a004c0d1501480b00090510b845107010100c0c10100800b000c031200301d4280e0125440e8443d180d001e900803800c0034400c80082225844041c402c81d00701100b00c81024a4220000300319008054aa000340100301b2003181d82c8008001d03e540c404e40065030001c07042d0096400124054441c0d608a50003c001c0c540004800024403c4c2c039648115518841210301d03000f00040c0c05150040040d15403a48030b0700003000504100801c3e205040040c03c0000c0500030b05455883c06000e820f03602030140403408500c60700039000050750303081e2000d007203d1148800758110b18209080c04041c1c0303559001541c1504c1007200b075820059180c41544504644e50b50039455684d95589840440c0a102e8024100141001814454200000d40203450300d40c0181e50311294050180154104080328100d0354004a02c0c0c40fa01e1111200b495000300f003150140c00031280c20301085403107032015103031403140384207801c0190f00030015007098007035640c003e583d81c0c80018409071504c030f603456180046 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 378986834 1250 378985584 378985589
    0x7170d020c09100e090a0b0a0204060203181c0c0315020c0a0318030b0f1609061209050a0b0412270b0c0a02120d020c0f0607030807020a0f030e030c0f1509010c0507 72
    0x10f0740302c081051b003444403046866500603d00041540b4143c240b620003516405001000900c0111006030f510703003556129043e2080662282d406c85044405040048031000c49100540741242100d6403090250340f61b008545003111008001c01c801c6003e07940031a03020781031403005d404e050102c01005c000030b05048403280c010b1064038500760403418840b20111000780c0d40d82d410018400c5100d001c008203900b141001c0740b8010404000200d9003028140f41c0d007010041c1030014190356000c8100802c2011002d520200e00040d55221810409403990510103880c0b40000c250b520002010100901c0c800c0314000d01070b00d10008151200c1e11075685c0070038601a2011060f81c031030b8004900c4010300d640e0400424548130400c8071340070070141c119004903885115010001d02045000d0f40043d11080c020801c4049030350380034188031003c005904006040420354071b80d00f0f00c2800b800c04034200c2403406003c00d00036404020142d104111609008800307a501c0ba01c2031030705000d81062400033280081c01700000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 378988084 1250 378986834 378986851
    0x41a01090b0f210702010b03010c0f0509030a060e0105101703070803150312180405041e030203280908030c060f1003080f0307090e0f040f03031d07170d020c09100e 72
    0x844e00b80b80d603029094a0003901c400c0c1c000d0307150034001d2101c554003c60340060740f4203c0c14050f664164000c0400d051140c484000741c00c02d4104510f40070501d205600c041e1140010310400e940c040d840314282202c2c2c00340e023440170030319030700c14041c00c0c0200d0003030001144c200e4240740303800b0303103001180e40031130b092142d41d1a111550440100d13501c20f080c80d00f018219584c5004440c1000030f40340580da8441d240500340200504140003401c44003c15000300210f40b8010765071907498000a1300340c0c5e018101c0c0c008410f13030000068110b860000b920100002035880700e041c6071003d41240d64401140020203a001041c1565084000c0c000001040e4140010702684c1e441c840207e0b524a0001c0000e0809420342c2c2c00204009500d4007003110340c007480f0711010382056025001900d41019800c00724003810710301c03100c0403900c05441c580440c444000101c010031100e031510010340c05549808901d032286e80649000016070804900c0361668500600d9a50b4000a000d440b01290fa4031194034624010b800c80c0c2c0c01c1c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 378989334 1250 378988084 378988147
    0xf150c02031f0509030c0601030807031106010902190504080d030b150703030e1603030903060c030f050117120306130506060f0c0d0816050f0a0e040f0b041a01090b0f 73
    0x20150402e0f4080d1a900c11600c100a514240ca00e014070703907607410144405841d90001103101020036104003d698000ca0005088545958403000d880c002036000c0c03074007070210700781d1072804643c000d018500766022201d022020b0412021620001d8010780441c0c00c1c075079404a60b40400d9515401200080e010190280e40c6c00a0700d1080903402a01d0003002c0381400b50701600b0100304000203a40907500c138040d0396000c0008992010300d100141c014045078a40a4451402c000010504ca80a85441040429007100301e42c034050408902c10f64a100070707180c2c0368000340c0c80c94050340a41d03100d800407500514042c05151a1048ae00441003070f54008548014064002c1500c0364212b44d40070070040e41100c0756581079402103805031400b0303080e8071904424421039140400e01500181c0168600488460054814019154500b204030002e060007107072248a580f5104480e503c00007003083c0015904010303110924181e05004050140e50000804d811a42c03c04000078076505c00d1300d212411303e100320342680700e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 378990584 1250 378989334 378989383
    0x50601170c040b1012110313021306061b0c03020909060103030f1b060e03071407060225270906050402011202030f270601180509070f150c0203 63
    0x49007810000d2080911903820502c58074090b035500000407070083c01e68140700b046494038000d0320024003010641a10111408010070a2249a119000184510031559003000d4a1580516400c846a5008a03400214400100801000c0884010268074021412046040d50740e80c00682020340481d070405464014500410030150480c858104446142c2450b00d91309210070740f0704198800700d05001e0320b121749034028444050024022109d0f107641109050300030032440e100c3da550380e0505100d4500148102003443d801c0c1240f002c4182400d1000c0300702881003525080c2004540549202d810039001a20100b10294803141d11819014510400d40803540307107803134000900141d6100a4192601d40100200003400d0700004c1d90383d5018240b03421148180076042c0b9013050b0707103444005e072411900c1070300000301e0700c50340d035007010b4440081090050080b40d8801d400e00740c90307a20038400c4055000182d002070095902041c08103c140c4841c3c9048111100540c001a2504860718800e00f005c0911000f40d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 378991834 1250 378990584 378990629
    0x21c050c03071202060d0b0613140a050303121f08010504150507080610051902070f2111040902090f073207260d0f060b0403020f0d050601 61
    0x80d5031403150440180c0042840c0000c40c800302682010000e103d2100000e02c0c10f025030141d40b00031881e420190000b501ca20701056146000484c2d8024850805c1207011462741074504000c00d2000d4400c050095070500c90381088c2c00070780341000f82400803c45940f00d106120b08440d40760070001454400000b05184c01d01e42000d07410780603c0c682120915003000308100020b600100611341152040c4d811403002c0515850031144c50190b41444020303041c8014020310090f900080d030034107903043c076255a2100d03540c8541842a1410b184502c4c40701130400c4911724007051410380d001440c139901400128180100b9400120611411581030301030921060a000d411980480765865040310540c40e4102405891443d840f40084288014400303600001c1590400005003013462480407008000300d00352800c0002c0c0d042e00d400c03118841244030325004024015403404d00659080300e40c621205841d0a05540a01001c8034800c44159000602c50400d030000031400c0099038001d1520326003900c4440c00c410070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 378993084 1250 378991834 378991843
    0x2070309140a0608010e060a080f01090c050f150c070801060609031e021e06090904290103030e093724060e12010c02030702011724010507021c05 64
    0x655004151120702030003042c1e0090130701070546084684400d07803a6501800034010b2031031908411003900074081d0301b110700300054208206180c401c3e40f11100054460061100000300508000c5d4000444425020f114544070000c0c9080c0b1000b0080d42d4095456002c40c1e07080d034905602040000300007410400600ca010062480381c0c0d0328160402118000f10b400003803c0c0e214108007440700941500380020070340e40703002c01c540a4030406444511546040e0510442c042c000614845401d041800060590440800c41034180e036031545071080940c16903014080102c4008010b80c00e040d24444842c0104000b440842c501d016000410502c4101c40c40211002d0b01d8103000308820031100050382040800c01d2000c902c068400a00d020000d01c0400c0b0005081000305808442440d40307040c11119501da40400180860350007a21600040e044516030004021011250140714445200c01400d040820003c0d107081580149000b90810589030001112030362703094880c0050984141d5003004029041c0f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 378994334 1250 378993084 378993119
    0x82208061503031e03060d15020406020106080d0f081306090b0907080d05070807020d021e1503010303022509150f05030102030f130c12081b0715081005030102070309 73
    0x1405907080c102a2445010202c0c0141d01135210200040b0024816403942540403950903005115540000c071610750020080d4824000c400040d42804d1000c0b44030403000800c0043c000071b903580d650400041110032200341030064128501c5003e40f00e1103801290107805000030b100e014108100e16800d00d03845007440d19040390b00c0314010303030800301e944110982c000d010f0380c032099005901c1c0d583d1176480f840010500088040025440030202e102d4081d0714a003034400c8104200103407108030a10202001e004194002440024016400240520000120422141c000e000c2c5899054030090300d602140c01916241c500a04088190a000304500c0000840e06801032038260b000f18a50b0502ca0301d43d0425441c000c10021601255020318820028145e224100900300b03c0d4000c0c20030102458411015071025508002020051103d03c3c03024001088070801c8524415032a00150001d980565084c000280030404090182e080004c65403401c0c0010041d40b846aa5000d82082c101805102c0e0442800c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 378995584 1250 378994334 378994339
    0x406050a0803040e15040603051c03020301030c060534050705060408070611070e070806131e09050312010e01180c0906051c0606050d0c030902030a0822080615 70
    0x221040154103030200494044d1340e041080c00043d03690702d00c10040703000c05190040e600b0900c2e182c0d00100344035020a10891308001083c62074806140008120141e000038040070f4505031400a040080e540036400408516844603c22443c002e40d940c004501001f80c070b4240500368012040300700400c441805010050181187c000707007020f041c5070340f40b5a6101c581c0036590900060078a04c00706a00d0804c1a00c0090440a002c21894642401c00a00203075040e12103d001d006100241a004a682c0c010844001c1144182c019030320041060b020141442907410349082c0030422581042440c0407400301e021701444004618154942000d235045001270f8040810141e207083c0c030b5210b0301035110403003404440e540d280041d1100003018807040e0040340980000205450082e0004031507800c0b0f40030b064501030b0520100041c41d01d420081d429922401c40007545508018204800a5540340107403c004a030700034003000002c2d816200d01c4042078a0b811044036075114070200030b1000d20b960b0b184000404203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 378996834 1250 378995584 378995599
    0x3060911030406090503040b0d1d0c010804080306040b0904060b010807111b01090b1209070501090501021e01060e0106020a0b31080c0a060905060c0301030f140c040911040605 77
    0x3048811009400058401040652a956610103105040003660084c1500e00a003030340d603074404005003008024401703802030201e807a44002d829020300411a81e1344060182c40c4c3d1040740c0d0700daa851400350b61008218070313405039032040c0303a00321503c0d2601c00c81e00c107904c100c0c40018800306c91710000d40b4204000303045004101c84a280100c511001080d074a03d0f8241035000380440200c400c00603600c7c440c2d40c1d0004055800045540140c402d00114510b0042c034048081c0c7d0703101c3d52101700444142200340107040c056880182d04c1030f144030b000a6100c2058416100014407145c4403c540010014281d00420050784601d2400d000c1c8120005802d41028401c518034940c4407803d00c40301c20340d0000b2004a100e506134003c484003800b81410480300a4100c0d541610b00e41c1110746492001012900303000d0300c4a10589000420502440b401c40703041e80d801c0640c0e5050301101c0d6990400e05500794104584074001d5400300010703074545000340c140d0300d44900500a2040d01d02d4050100b200c003540c1c4101d06c16000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 378998084 1250 378996834 378996851
    0xb06060d021b061f0b0309010b0913020111071d0a090203030720040912030f09050601060f021203150d0503090d11040e0c0916020a1203150b03041a09100516030609 72
    0x4606402c14115010300418544a549031f440050040a02d0070f070365900b000c00c02e002c00600344050203a00c44502d1007601c0c0c04520030750200d0350030f56440e8540100003054460f401c00c441c45081c2009116030220303100401180280499000c82d0440c4c2102600710351030360750244042198504a5641c80f05904142c804203c0c0340c0381516440340c1401d01c1302d4510117041c3e0b68942444640b8144d0040d109064001088030800c0d655104002c092107984c0d4000c000600a03c00c081e030b10103150404490040441200d0300c0160040710040022011800c072007180c1d03501c000c01a07584140c44086812300e210380250b00d2002007103128130a07c03054502c100084400b03038000c10020301c0c1a0759042440c1d0740051003038190300003003d20034230b00f0f0385030801c9d0040c0980350984058156545940c542c00070702440d8241d42d40c9039031099480c10144681e00050760020070076600064407044504031884503940c003100c4501154800c510300032241080316815680b5104403004500744803807103501402510b0041c00356950402296a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 378999334 1250 378998084 378998131
    0x9030e09010812070305180d03020706020c03060412050307090315020325080a0b15030117010606091521020a0c02030d020a0f020f010c150f1a0d0b06060d021b06 71
    0x11840c040202806400301e50707c4581803031207104041805000e8010500ca02d80c9040181d5a11100e219620042c0320320400020740e0708010441074001d0390302010000c00e000c130b001010760340c030b41005000d40c0420200010000125102d0180c0d041b14031102d5000503521f0801c1032604050b11020046074480b85403010301d4441060b480040c441c1d004528902c000b95104280300015240305407468211f940c41004000880e880d080c100c48000c6000c9440001c0100e9035940c3c6c410f0350f51602c1486801e0b111040c000c40d00c0d1600d400b0b14030300403499805a070701c40500303810b04850300200e8015035410710005030510403103c11400d041100700c9200d0b00e00d000178010203003540d60302d6000d8010281d0090054114000010842c0d000e166543c10345036202d034200340585145c52400e40100000c441403071803d07092000901ca0600d00042c0018000710182035000542c00c0c64940c1440c0394000b07400550010020000e002546000d440070b410850701c0103600c0c1000c41c807200460f40c508400170309031075250a90109003d1110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 379000584 1250 378999334 378999337
    0x90506012309060a05151309110708180d050a0605010f05030d0c06020705061f0504020f0304020108090c09070309050f03030c0a0c0512040f05010305130201081b0d09030e09010812 79
    0x301d04807102c00300ca540d0480415000c15030382d80415000607003e010340c055070075807801501d031004406c1c05030707041070390b6070140101aa0208421490121001c0061102064148000748400f20080c864008940340c080c0c080745c00050442401d46481d0020f40302d1030108100d0303010f1180101300c01c00380c02000e6410040001d40711002d88415038103200c0d500b0010700400c420b640544144507040010703070b0300f549010180c0d50700e450440b08028040000d601c20100b041c1c41d03c0d02c242c2d00801d01054865085070b5540d401500c11441c06040d9114a108294031000c01d039503800f8125102e43e2003650040744a00d014503150703103030200c403040c4080389410a10810200b8125207055607a02c030120301e00200300d03542c981085810078221080301e03c2c2400c40010003040180485d04201c0884900ba40c0c200019583c0d4500c2109092004200030300003507121012401e5103045000020303500d0440000d0524013281960440104e42841c00c049000c60300c10900c48505281030f4400c1401080f0383c002800c4c142000d0040c03160309 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 379001834 1250 379000584 379000649
    0x2109160e06010e03010e0d0206010518100311030f0a030e01031503020d060c090902040311120c0901090c050409090f060605010804051203100504020d29030304030807020f03060a09050601 82
    0x1000b01036043e410b03ea95003504402000700c4942c0c01e803041040c0c0c20380001c0d1140024010140501c0d8607014440002d085024110b10038030003207129080817420741d500d842d07641c6001c00b1015410700c02e10481001c2480c0500c0402075051081d210548018281d0002500703540c003001e240310f258400081c042001d6203405901e030b00540c0e4095400078081529880c2a20351601d0344d08072600f041e20100b8084100720140100c05441d42044410100740403000c4000350f91401c001b54810780050900004005841031a00002d914703429906005007050b40f102c0c898000c840345010f003540d8030304e0210300c0c1d07005000c9540324080282c4001e01c0c1100c0245466122690b0345c03194003102040d8000e000001918220301d9a404030b024100051007076503039020416050029251080070700c820341c00703108070f0604100d009031403258030103a001e8095400c1a28684880c8507a4015800903070f045406023074402d0f05070b50280300c00c40c03180710030800014048006003451031521300141c114245441c1070f030301c2e2480501e40c0d02d02c00402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 379003084 1250 379001834 379001837
    0x506010308030406230603100c050a1821060501081c0806031612060507030506030c01050f13030b04061a010815031c05040806060d020901030f06022109160e0601 71
    0x1900d0303d81d440c2c22802440a2410fa002010f4140454590070344040e00c9580182411000c071080316032001000400c8903800420302002c14000c02c4009181c41c00380b820300d03085800301e05035021001d5607090306105c03071a0b400551264610748a0903c108014143c40f401e809090800c00403c8580e0355040c106c49040d50744480c1c42d050069410004503e0303a020015035140f0031074100003084542d929050b120420301a0103081702c8203424540003e5240e0320901c2a00d01c0340c900100280200d00c5030703a0055500382d220322000e00c0d040104004080b000c60499005c00e008611608131004a03141a040c414100d070010000b001c209480f4070030103941a07034051403450f0403901c00100866030001d2440005d2401802c070246081c94003910024558058001e00a00102c0f080002506e80c00d5484100308604107511880081d4041c8441d0010300214048145103c90300c2e215820040c904a2002515940541800c10030b060300b2038a082040056282885640381e0001e00601307205440e4141417044113000c10062500b030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 379004334 1250 379003084 379003087
    0x10f081f030b09070609090e0606060c010b1302030403030507110c210a11011205100510020a151a0906030703060506030a0c0f1419090c02101a0109080303070906030f14070e0a0b070506010308 84
    0x71f01c440cc01e600c00108400014030701102000c6000203030029401c101d0f07083e00420714100000d8200c50103283e05444442c404405403000038021030070404151903e201504492406030035011030302d01e081184001d1180103d120411001e071200c0014115510011307aaa417990410050000444180100400ba184200c0d200aa928981c0070100d140c4044188080e044160b80e000c80d07401901c00e0b1780450922040007261038910686003040c400c1d026800d44290340c2541c80280c0400120740d0f29800070b5008100202903030b5442e855900d4803540041d40350010030000404000400148142c00300d41c104903d401c0d500f11600070b0b01c16491100d100050b10a5050241d107170589070501604c04d020f0801840391004040210349810341e00304804242401c01c41c1d02040c4440b102003040c44c2e001098074031962403607a810001c04e04000c030032400740a00b00511940c040c1ca411307040c181d4032041c0d509248984011395801079409030950402580180c503500c0384101d450100840c2021800c003288e0241507039000840c0c079 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 379005584 1250 379004334 379004347
    0xf1a180a0305162a0b070506040b09071d0109150302031f150e06040f020f040306110409050103060c140408030d09080c0d09060e010f081f030b09070609090e060606 72
    0x2c43c0d03410148001c0c0b0400c26443e8043c004d5550580d280110030f059008803503d5501c5100940d040e00c90b808002d8080d45c020400500080e8510003000e52050007a011760382455592400180c20307078900343d89241f05030081d20051281c030b4420312a0450703001d600140400e00c01e19503004241c5032982c1030042c0030750011b80381c0c40b049040099000140740309207112104005030746d10304401c401500c1c03e03150240f01d40e081030a03000c0440e0290090300c8240400b004218901031443ea60308006006280e11945000b0041c0310019802a171803080e140213601841c2e02049441c602500103013220903011003a03020400500c4203010303441001041d00d040903100800050264110706050f4164003414030388144510441010b038414680c88411030003110155150a03400709a40c00054542014070b0083d100040d45030070000700840c00619a038029001c01d00e10000c0c11340e40b29102d4118800049071600c416901140081208540c0050458024404002c04000607a07001145036160503014100d00d2242e200070484 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 379006834 1250 379005584 379005607
    0x5070201050304060b06180306090a110d0f15050604051303140a0e0301020706200c030d091b0806090c01170705070503040b070302010c1d011403130f1a180a0305 71
    0x45c3c010840c01030009484151350144222088140c140707850080c010080070460890001507500c5059a0206c44000000c1040003400850318032000c094036400c0c2030032120404038007002481703080d1108070000440c03946442018002510005020741c842000b41184000229900040103000758250120322955060700710707800c81c1c45032205107400c0d9042d440001c09001f0050158030502080040c0340c3d1000b082c12140710017070007030b005180d40d4071510f4000300018150240d044c0d10080e44248034407502e4141d06001c03038001c50201900e8104040c59071054081c810026030400c5146101c000034607160410204580311a5904080a04810180b101c04140703102003090501c140d901400501d81715a42360200d605000303000c4c0050004510200f43c01c02da464892044d101c124020610f41a143c810710b8101d03074030b11808070703500c01001c1215000140440702c00140c010485c01c0266030064041030701c0f074000300310650003e81e009802d028181c00003013403a004030351020504606145d010708181e40c80300c0142c0358 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 379008084 1250 379006834 379006841
    0x20909030915030721050f07080121021302030a05070801050d030c06090f080f04060e06040803030f22081206010503010524130608090124050f0301020909071d0d02010507020105030406 81
    0xb170700403503001400c04043e107603031a0340d01a40c46454401e004000c02c0c0c40d02d803003e07201c0c8442070146517242d80e02404d0340700d040500e01100f40c001601c050300030865422001105022a001500c880d4100c50721a414000d21a500c9500c5a000d4402200c015460312003550b4054280341c0140c40042025848a0307440b414013a050b508010000d4018044664030a0490301c030000d2907000d4050300300132814426501d521403c181d01949d0955100c58010b510350785903201c5410323246c00700070601c07000010b01c01e0441340b40c0e986d071041070901d0381d02c5581c41580b1080c40403210000351500070101c504000080c0010005907a0b411000c4200c1202c00750040c0c400e482c1307081c00e403440c2e204e031328903050580781c2000e00010034951102c0050710800200b0001c200003001c0050640d81012009036180741c42403172802c144403034070308243c0c240002440240014a442c161074041101003604031001c9021513110002440b145010041c07110b880344046680e10355010807580064883e00540038040c0c1080000f1001904200f190790 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 379009334 1250 379008084 379008107
    0x2011a13150b0c030c0f0a0c1707030203190501060902070f081b0d0908060907030803060f01030e01061203080906040206070b0601030906060b0d0e0f060a0903020a060213030209090309150307 84
    0x18843c0d640c103848070740341c0c1d981d0703200300d40d090940e1040e0309065080e014042841c20405610030b04000000c0c8c43d000000d0080545071140c07402c0c0340104040000144d400308451a1822418894000b02d4103c0303040c0350342199041d0348012590342c010409400095029404030f1101a4082c2e826900c441d081c0311034800e58803102441115a00c43c03190071000c00c60b04081c00d1812a0340c0d140445180340d61344401d640c1c0740d1065220003042c0700400e2020031030b01d103085c0c0581c40c0c5140c4185400103908001032501401d5510582c0704258540d4100300c800301b4194446445030b4046402001400c2c142059030215286101d80807018000c50075031030101e5003683c4240c208801e0140c0044050000765242c01c0d0400c1d0990040c1072014115242c80e1581c40e405401080403104c0100c540050030f40c940d03501c803e46c0003910740420102d00710700134425424005503084c80136000070028080100b01850851041c07046041010380300795240da10a2110b05e4460740d031022280388161f202c98a641e2242c8179010207440500d1302e07c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 379010584 1250 379009334 379009349
    0x5040308120604050903190305060609030102040f0e090d0c02040c030902030307031710050a050d0807050f06040606050105030108060403200d03020309010b0d030906030203102402011a1315 83
    0x165911403110311080150041808030f60800c029101d52003c9a62807042c401c2001c07c0d460901180321041c0d020750301080c0c0c000c0c0040c0000b890600d280b4006800c990140e008000d102d56004400d02054803450f807420b91280707006000303204012040c04c0141001e229604024410703912035407001407448c42074000756203a6038081d0440703407250001d1501420703c1d1080558400b82c0342030680050407184141ea601401c80e030011340200b80d20344c140802d014082441c500c0503107030090100842800124101301c0f804000c8135501c05002e0a0800c0c2ca0060242e07022030348a18100030084c070062106420100b185900f00364107052048a030403c004101c1801c2c00c1d04c202c2801e490180a0b5441c00c05a0150000c1d03115422180c0204840346950302084482d00c0c5070140900042e600d1601804490301a038001d54010f02c4070703482d8090495a50542480000c40e80c0500c2c6807060390300400b010314030740902696100341500406040f44854050202d003038181030152200050f5120a402d0002261030711854029040742d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 379011834 1250 379010584 379010587
    0x706080c030a11070f03020a200f1c0803040c1404060b04050d030c051204030618110909011b050901020f1c0e2206180605090c071b090c12020f04031205040308 70
    0x138103000e920b81b00b29070800c1d61400b04640404860884045127007201e00c000406100308034012000344540102080b0500307521000c0224120301080c1c03603001035881607202d0b07080d40b00028104105410020b040907185802181010005e01600c281c07501a02d082c0e0f0820b580c4041d00003100c1c00c0c02c480344445608040c21a001c0d9a1141038400401801001640d004540034041050991014030054400034406080c403154100000800d01c0c0554030142c10001302400840c100c4071742c2d0303d01c4004003032407041c00740400d000203001d00e101d5030144400c00041e91041c0180c54a0b0354000010110311031110501810000e940803802d034580e4801c0c249503044050138041820ba240090781941c0200311a015401d0f110036042d0351704228000700e01038407050f504054152012922444580901070b04041030445e42900d9204130b5181d1044d130800c0780c800a090300b1b40007144c40b01c12184040c100c4100c800d80d6596071401040240c04010144080b9400c603079000e503c40140c0c2c605050125200d015540004000600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 379013084 1250 379011834 379011863
    0x40e0c120613032124060c05030a050f120109062606190608060c040f05060304050d05071514060405090a0b16021207050309040b06120a05070306090f0203090706080c030a1107 77
    0x22a114507600e00c1d00d004642005c83c50303c5503c151500e11071b659005003503500070000760b2000f0303110700d003d040d141a02c62031882c1000c0200d0102c02c5190800d030040c003840386d581c240400040b40c181415070741544405810805c940c44600407951648801008080c0c0681c40520021041405a1000e00204070400668146081a4400300c510340c1c001d2280141141144a0108840c5081001c0f02d010390782c400020514603d15600698503a00440b00c00e071409007130710a0903004007a41b8007401115a0320041400d503a031400f00708010803200040c200c0c1e00703164071214400d400114001800c0307403c014503d120811104d040c9000700d142c90042014210340f905d002c5030308010058008042c20071000210340900000b0965402d00c41203020b201e217000c417098074a5010034040f1400e0391100d90030140901d0301040319a00c980c0368005031b8140c1481d0760b2150381c0c00020405074840501c004030240c80d1910b860802d908003c14810304c0c03070002400180880382da0b445c640f80c03d0890001100ca080d075215070f81026424 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 379014334 1250 379013084 379013111
    0xb06030c1b03130f080607030c0f030903050706061e0e06130506031009030504061106060d030c02010c0203012906030c030612011503030503040b060306190c0e040e0c1206130321 78
    0x15251040004600c00d003000b003500c190180c0103040c01001d04ad07940c6425031402c04401c501030b0198a0003a410310108010000102e00f03e07025120207807010a109051003c042c0312001c0141c43c0541c040b00b014600c05052213003566035402c82c50f0f07600200d0704d004103040d108c0500007824440b034041440700c85031500010b8020190040050011078245442e000c0d21103003011380030364503a00100c13002d0b54801141810140042c2c09807070311500560062410140c010324030340c017090031991140d40710142681c901c9021700d4524640020001d0400066407200d04600b4225020030f09800042c0c02d0a1180c142c0c0701c1c44c500714500c2588612200c00701210600102542c9060240c469441503400347c5502031750750009605401c0005565004507054a100c81602820040e0b0100800881c4042e0b4100801102141d007540c3d12030040c030b0303658400500903240040c40d040c03c01101d5026115410401d400c01d504102c00d040c4c0381c42284c03100e540c244c1000743e4076401910704081c5000340384a0000078145801130418541 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 379015584 1250 379014334 379014359
    0x9190501020c0f06040b07060c1115070c1b060e0f0307292b0b04180201050c1006081b09040b0f0604021b0c01140f07080a0c05120c010b06030c1b0313 66
    0x1c2d00c2d6514ad604a203001000480d48601504d400c03c405802144003288055102d940001e078454000d80e80304120890f620b54036120390b01c55601c00b10010b08800c90091052820b4481c0c1002040220014502d061903c0c000c4c561140e460043c0c0071b0841140106100081c40ca4004c075010342e1451810340a0401c1070542c903000030750045c003020405520b0b02d0b10300e002d01d040c039105150512040303d201040142e586e500444040d409180502c00c0f1707000d000c19038032540d01e00380900400361441c0c00142c0190400098010440070b002c1c00c1680c414071a003030a100c0821343c40a0269048141880424110307900d00d070104d0041d11801804164134560582301c031101d21804a114020104d099940e02d400c03c0b0400b4200185001c0d5071460307540007101300300d02000120020000e00c0d8510483c00d15a5200c2d000b5229079040006d0b82503c000303180400900c5988408080c820011252800c03241c10303042d803c0505801c0d00300d0090100180380014407a407619400380081041d100c0d084000601d040f10b085d107829003803100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 379016834 1250 379015584 379015601
    0x303020a0e0616110301061a040509070215011a040b0409021b0606060a030b0a1a070507050d0c090e0a0b0c431502030c09190501020c0f06040b0706 65
    0x5001600d40c0700340c1d45811012203200c03605800302c945210700b0648515207080301001000340c0c15940c4880005000710400c0c00788403100d40c007004042e240ea1070901031000074000201600115084003824000c0c40400302d9484d41590704007503400d4010904420241c4280c841c54200191010303011900083d008040d40040581e202528064440e01d140d12480c19550340301610f416502c110140070460002d4400d600c0721081c041c0c010119589140c0d81e4501c00611030302801012000c0ca400106181444010001e1a001b0324050b11219008025038407104044100f50181c90b44c0e0a0300c0b00d01e14180c00c001000103445681c2c00903030301c0c03400f418000315681c01c0c1d90200344150f1069100d0072000803103102e00c1d40183e030380d01c042029000d002c1030040c000c50700900d8002e0040b103410170b40340780c000c156030308500c041c42c07041920070074007a510031040080040c01d405211007503101c0d050700b500030300c03060f68040b50001c000b800036600d1102089041d80000c049000ea900050078500000c501c0006015050700040711 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 379018084 1250 379016834 379016837
    0x2040915030323030106180b0c1c0206160f12050c0c10020301030c15090b03160801290d0b030f062d0402010f03020c0114040201020c0111060f1003020d0303020a 71
    0xc0100d08401c0e4140c0d01203c040d064403900c2c40038001008464001d03540850950700030f10840f1501610307108103030300781d400c42c40d403480c0d040e4131294600c1c40e18003100b41c800d240001680001e000e05d103440b1001c5070100114411050811429002e150364842c041c08290041e0f001c40c090500c0146010b41c82c000b09504101c80780d4006100350302a1541c4254184200c03410391381c0156a003100d45061074680304841c008130b03080000f00600d2841c0050718500010140d401020080e0054600c00c10000000f01141c00c1038001110301321020b0058141c400100d40380d09820f07a400f6030510f880d0140750407104001c1070162901d030780500900c3d44048910201180381c92003000010030440e50710100081544100d03030030004c2c19001c0007095010401541c00303207808440784a0145809807400021003e03e50070b5518030740d20700159041c0300051008540c1c06201c41100e051081c078010001d0180d00c0100e41d0381d01c0d0040c107914029120308000c42c0b6100d90018206000c0e41d00600b000d4414040c0b807a0081c000c0d80207080690 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 379019334 1250 379018084 379018097
    0xd0312050109021c1a100302030402040b04060b0a0c03030b0a0b1b01060810180c0b07020405010501050c0316081207021b0303090604031e0501050a06180b0a0b0a03020409150303 78
    0x9502c2c80c10700c2503c0c1c040c2460203000403045140b01c004402040440e40d681d24842908001345065921007500806030009541c0141e12070516106000550742505006403249080180038012450203070251440c7c00142d01e050784402400b8181a401013284111850300b1101c2c0c0e600103e6450680d00c024503140d6040c43c0d8102d03020b05101001e40c2241c040b400f94840e00d40000b00c11695100340c0d034220f142a050084580800314003079a85a03811030308650b011000205000ca0000d06501e03052151500504007800c200e0718040c00c9140c16512886002c0c4407a0780c803444194110244000070b016a00030303001c0000111068140020042e50301c1c1c000e805141003a0359034820a00d00c0781408000d9945580025240d03500741411581d85002c0d00c03160031542e11856103220702d00800b02e40d007402a80d008866085001602c181440c0010b207030002114100006a400c4c140704d810503884000f0350804454032411908e48501003490106c02900c1a988082c0e889401c02403509480b051b0741c2c80c00030460348243c07943d9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 379020584 1250 379019334 379019339
    0x11030304091a10020319110106170631050106030618020a1205120a180b09100e060306060705100c1e110607030b03010603051c03051e190b0d03120501 66
    0x841400300c01e0b411001a0024400022a62540099034911400c90f0402c100d5611f40000180c2c05c4030f002d540020180501e4403103c0c200e800d000c0c0813054004940c1900075944403941d00001e0a5013440b92501218400c5890840003408800e501c03550186a00103818084820351000c1000b0000020005038462590f946000908102d01000321740380c903901c00701814041c0c3c00441401901d40281000b182848000c0d01c20110b4460100d110300041c3c10464021901c821802c01449010510180c6640903c9580180400701d03680d054190b9501200c01c50b0141c0d514a240c0c9002030a240c080c682d031864943c20f01c141002880e4002c02d0103012011075031a04000d00c0268441124000c4600b03203015000c1c2c10030404582200c1c800e401100203007401a0011801079509c0d95221300c1d0105911224100100303103600f85030008d03458099590484209401404001714480740c184000001900f1040e288500c900c3d40381a00742c0c01d0b0409001c00b480100807200c00800c3e401c0240110704951f82208056142c231002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 379021834 1250 379020584 379020589
    0x501030c0501020721020109030f05011505010f120c091d04020102120306180c0f040b2512180504020f0c06060303160b06120106080708010b15070f11030304091a 71
    0x1300c11034105001c00c5164640c0307a0801c0c039103142ea800d030503410480c41c80c0d0003101190309a2000c5040500c00c900000750305204566039640704009030415810840034481c141c0807140d0052002c0c0704402c0780d500004800c01b110800365180001540820b00b15051184641070684000d4440c070711440c003c1c4c080d65405c1c0c881c02e12074400da00c0111552a0300142d0103841c100b90008954941e903000c0c0281640c0c1d0714040f2204400d181c02c1d0006d43c0455014240010306e03504024900788402141c21021000321940340a95444601202e40c1030411002c00c00450401c85030310152901e064000d00000d002159141d03203964110b2505c1d8800b0140890744c0c82202c020070080d080000448140141e1400285c121002d107a4031502c4d04e82c406001da980c0b084400e052800064400c0c464130004007404402000b4880c60120b4082c251260b0040b01e910843c00468000880b52920040b6038032554014440c1c99001e1480c41e02d01c514503441c2c0b42ca03a0301840301080124000842d940a050b00080d00d074501200e01c40311104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 379023084 1250 379021834 379021843
    0xc0f0102030f0c0703090e15030f0d080c030c16060605010f08010f060c06020c0d0c02100f0203120a24090e01061401052a150705031018060305010f0501030c050102 72
    0xb00000c0349203015002407030414021000c0c05040d446450107501403542d1300c00118001005a404404201101070111185c0c9000c000044054145d40080c008102038410040c040303e00c010320307034a980a4000002000c0710504411074407240004da01c909444041401c1000c004d014a01949001c80c20300c13001100e213240103aa8142c1200c505140c1c04500e581003a000b00c1c8e64241c20f10741150516000d01500b16603540c203003e400a403004650700c0e105811058010082c515080800d050140031800110a14a540c0407048966280c20a903520f0305030b8540c078511348000d11a00c1301c450070245400300c0c0b4044a040040ca070208039400544c06000540000c1da0550032180795200b007048400a503404519294003d20150140e2440b00d440040390000c0081d06600c4181c07900c85801c9280c1084d175231190050442e42d0200e411116a1802508601e40354010110f51030300742c000d60410110440301c803844c1e5046500300d8006181c0c4000240a04c6c0c1480700c80c10041d18082c082110302c803400b4034010405520014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 379024334 1250 379023084 379023091
    0x32c070e010b031312230a0306120305030105220f0c03050c040501080f06041d0d140405210f0d09080d030c0507140307121d0f0d02040e1603080c0f010203 68
    0x440361041a0113035503c0c00424150704800c13500b8407901e034005401003200c0464401400c207980c00400c1d50b070b60300c070f83e0b00508540503901302821003088a8543d40c086a40b01040d241074a60940314200300351a0329240c00e49801c01c004400c9141400c289510954030016000107400e04403a842c00e020380d480b080d8410042e40103a0240c64002115540003500e808608003065030000740162000440540c0c0c520710650b03072440015409019441204a50112a800010761a45c0e0407000703596814141890005030502c1c52509805442c0003284861901844040c000714107407014601c225844074007062009400d4850a12076004180204105080b100c1d0203405100412415941c0381c42c6450065aa843c1e03c0041c41e15403100350741720a01c003134000100d02c02440404200c0c9030300c8020b4550b0302c60485020b2102c170031400500440481c0b1000910f511042d505070000350b41110041820000c40003914980b208224a01c40044040003002081c0021640200000e589000c21303198900c965401c0c0500381d10054 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 379025584 1250 379024334 379024351
    0x280f02070506070807051206120a08130b16020d0201030f1a01090801230405010b0306040312050a110f070312050c120c0a120f0b0a0b37032c070e010b03 67
    0x2001407403d00e000c1c01f141103034441e030020000810340e800c2d21401703880c1c80f0700524102c4205500003156403504040c5c000000041642c540441d01d46203194804017002d0810000090040c00f0a80c03810003168080d8000010640c3c123083c00f08801e80c4180c0400740c2ca10360098519011800710400031a610106020341034031043c2540c4182d800b81d1210822035540c502c01041981c0c035550304d151000703081d40c01b40841340c065070203aa5082d40c4031045224040443d00c003d080d400000b8500581c5041401d2018241c40300030420181c0651030f404507017010340749446118000d01c2002d290000f049070380c0e91013a01070004a00d4252a951071980c6049021f0071520440003d1804146040940c4030342e02c105030002d9101c00d81407480032a602c10740901140042c0340c3c5400401001304045507001280301501124001d9901a18003c2607000030880e0340d881700503100101108060300d400500c0001c030030380c1d5161149120031080c444250b0b030541000b82d1302d0f24103d0040c1012100c042000050702c244440a890052442 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 379026834 1250 379025584 379025587
    0x51914011d160e030a0804060504051c120807030b04050408030417160b0a09050f010b040e0a11190503150f06010903050c10020f010608030d06050a0e280f0207050607080705 76
    0x107100e055545850038442c0c0d81c4d252088000100000e06080003800090080e502c07011f071034604110402c0741d19041c0680056020b4010480c0101181c0307844135420540c03196042805240d00c41319400c8014006180c02e01d0b8015003020706000030000d41200452285000e07000c41650b8003403405000c4a24407500400841c083c80c62554400494141210540c1000e000710000842c0203603981d807542090161042441c00340d64841c14048981450300442d00710380910005002c1c400c440e41e8900c6d007600d001ba940f040c080c100403582107612a50303100c0410050500101224000c010800d241901600f0031203040b50610315400105907030354003c42d0140141ca51080140081309401018040200c900400c200214818800c4c0c03020095400e02c100340c0507113401d00103156079003200580c001c01c0e6080c1e0351200d8004c9001d06401c20804050304205070b000b0401040c4160003413001050091200c450791034000f219890000c0c54600c001280e40180103651180c03003511890f0380c504400707440c01442115940301040c0d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 379028084 1250 379026834 379026871
    0x80a0b0709030c0b0f160b07171b0304080d06080a11040507080114030703020405010602030405120303100302120c09010f05130b0609130e03030403020d0908060c0d051914011d 77
    0x1601350103000701c4110600014180b684942080f062080602d0058954030030710414001020b500c1050070700070100484222825050400c5521030300746140340c07441d04602c408800702d01042a9182181c0300345008031341c280056501c0c0c030001a110727500d81c4000c0f104191261414013080c1001c0c05001c1c800c0000c0c0e1235400b9960301c2d090f03024800086407040182d15000f100004001a59a4441c1601800480d07004548807804d0400b8002440d5841c121000c1d42d034010b20800ca01281c401a69030181c0c1ea055658042c0740e01000103d524000010b00034945c0000104000f0841c8040403468800b01e400480700740d040070b030304000e050b81119101461690800c4040210440c2401c103960b2220b0300154510340001c103900480141400d40c2c20079039007240141c1040440704180350b440341c0f952000c1c0c41098081c006e00d00702100d0300c0841d4070415409503220fa0b140e00000b201c0340b402010101052841010620029070a81284c03030343c0300001d00820030030381d00700c02e1041d150141c5140c89a04c0743c08100d900d00c01198 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 379029334 1250 379028084 379028099
    0x311030c0a0c050f0601060e030622030504090f020904111201030b061c08121e01060f0504170120070809060904020708070f0b160c030e011107080a0b0709030c 70
    0x41c0400035000500500030301c0b24002842c100040c0400141801c0642442d504048009280655017600ca501c694010010b20001d090002903c2810140c00ca1504401c2c2d0458502907802d0b0040b50b0048400d18502800c4500c14040ba400625a140342201d08000321001540d0240f074901403000e07401c50103c0e00400600004800c152403541112004005641400e01140c00011503000391208507034210740401c946443c03c21400d40160000001c5031503603034240209031b1004660005204000412030910200300301c050040c001c46018007400c2c0500020102e80c0c01c0154081e0041e801c51080c114007843c076281203082c9103419114002d80c0004200c1c1340600e01401c000c5c8076009441556031040d0f0801c000c0c8001001d441c02040c045100f1b40c04000e8142003805c0c0940b171003100030604d07101031031601007401c0241d6012078807021b01a89401c11102e01054440120b9040ca6000e4504000c0c0c4910200403924280015034142c0c0e41e072003422104003c0c1d036000012903900007113100050103220499810301142 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 379030584 1250 379029334 379029337
    0x901030525050303221202011d04060e160f030c02120903070806071d030d05030c0a09050a08010603060e0c0307050d151e14040302060621010504051c0311030c 70
    0x8011225248030711921540000d003194407104940411520600621444404200458008004480c01d003d4203400940001c0c05108030080307807000c0304e020712044c0503040d91681e000b10f01410702158030710300c14545424102c440704032455907031000c11405001c48400912074000d850040c041c0d82d0281481c03064642508405800c2510190740c14001c02401148001d0100403451003801c03c4c0d41e481c2c3c43c100d20159041d0030b4100110086000703030003001c00c0b03580d00d075040300031a030b003204404401c19560207030410103c5443d141504242e5000000400001e950314054100304160f0b80150310402400c0300f880080c50b41c1358038100c4019019009881d04100518007040c46441c4503008100e0780180c818094200000c84182c24006000720500380000140f03044180b14448011581160f001a0342c1040d40b400303582d41e00c000301841d10489411405507000010050030003d181c8400000340513606082c03070300544407980041541070401d203c0580200062181c0511090a1440c90505103107407183d0300c1d1180c15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 379031834 1250 379030584 379030633
    0x103020a120501061505041a07050c060903031308100e0109111002030d020a020a0b070c0b0a0218150c0d210f02041706090606121b0103110406081509010305 69
    0x503540e20f04001807803a0840c0035200e0a085103582d2142d44a040040d1000004d054010044032900c0a101c4280010340014240c0658541200c12a45500c0120f00083c9184508814600c21401e00c400010300343c000000c40a01403e12c242d814400c3c64401e00c00c590898880f51005400b050482d000b4461311700300450036a0300c080c4548160f900d800c8e050000b04040ea800708152000580c0000400c03010710110701d880b1900f00046180c200304108554a66503424100945131507441a40003402c0051402410b011036511600600344002601604802001c01e1300b00c1048003c480c065501c140c012140b0822115451411500d58110644030540100000781a5a2043c410039a4200004180410303c201c40b000344004500007131843e03141c1030b00c1752401c00d01b01509080c09651000c02040a194011507082c080c145500c4102d1005000d44004902070610040f0010b0450000200031038120303400080c06d8404c0030341015401c044422002803200c000402d11001d00750307030402800380d00070340ba4040c540d110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 379033084 1250 379031834 379031843
    0x606060f041a030403090b03060102060412020c030d03050a0f06030308161403092103191109060301151e05030f04170301080c0f0607050d050d0e0a060c03050f0103020a12 75
    0x203054482e10001949060400440c0e03212502100b00810554402540409007800f00385190030341c02c0001c0040d54860b8040c20040200401502010000c4d1003007040b2100514024100c644d10350016a01072700400f0180c40d00f0941c1400c001180c6100301d914010442201d41c541d03680041303071f691010903a0002c0b180802d400e080010007041d10110350010b070003460040300030002400c038080c0303a02da4614140e01c1c9440d014502481c18001c200c000c400108050080b00060000414103000c440760172120f510500350701325403020010001003400d0340750000502d540d58aa45810212030309501c3c00b0510904101d0251001840402c001341c0e456581ca045540c00c284128401d07041444d0311103840c1d0303075a0400d0700030700055404131454014510f0400200010203100b81c071030038a001080c2d01e41c55240d4041400a0062000000c0c841d080e00c54994030040e58480c4550070340342004043d150403009001c0618007540007038186800b0500180515000c2c0f8120b0b81e000b1f0106c145549040140c00b19140008401d96 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 379034334 1250 379033084 379033087
    0x10e030f03280b0f03070807090e1e030717070b060d03020f0609030d0614030d112b09170c041806060806101a03010b1b0a03090e060301020702030606060f 68
    0xb1503004907205402c1682d0280300002c2504001d640c1800340f02c4041c0e003003a5100341d0001008022102005c0b58501c180d0300c1101001c1141c0d6800c3d040186440c101d80c14a01c3c11010700307060121b82100c0400985030803881400902c0c040704039684103204900904501900c042418170100c0d06c24039010355200c5059220740160b517404500099581c2c2800c00c100c1d114551500000b80030321582d0101c2c440e07040070344880342c044c910145140780402d40d220074040b540020700c0000e044d0010106400c04c034102c01e90400361740207080c51415404040c030400c0346200310400b241c4101c6003c2450018251484180941c941c01040201043c00400000c0e004064280754032441c032a08501c003007449030042c0c0c40505030000007804a401c110100094800c025032003580d0700ca180c01e0011007550798000403070b41100c00340d042b01030f1125205042045038402d8404400398501c201d0443c41d0406030803941c00800c5134007e40d5164a01d0b0356200504d0300340c0c818590000e502d50080c200040541c5031030006407030920502e01025 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 379035584 1250 379034334 379034371
    0x190506100617061c06020a200d2c130906060e090c0103050403140d05040b0603010506130506060d021801020607020f0d05071505010e011a070f080903010906050106050d0608010e030f03 81
    0x341708a034400a000c400282c444048040404c0307500100c50302e250030a000400403d044180002c1501d82092400783d000300d520141190b4013126901c480c010b20000400f001d51141081c0800d0005004440d0101d982604100340040c07044132084602e4403840d8030b00302624040391201e00440007010700400440138048030110206400c40c4000180040549494000410341071030b050400f07241303e00404442c460382c10035013005016202c0080c02d01410242c10001f007210b17191100010620302440780404902803000c01c2e441d20f0201201b904041050007a0241c9200340c139070690032600c0b841c906414460940c4070300300c0407c5c0d15119200506031a402040000300d030300754482c050003d85000780c4c080381580305500014031584031038613a00250003040c4403140e460100035588980039004480c101420b04500411218101d803400e400c240045c96120904024541c0c480001800c036400c04262041d07480d107443c8002c54134981c1403007009659100900154102007002750314000aa000034400344200f08059500c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 379036834 1250 379035584 379035593
    0x70609121a13020411070f08070606050301091518020108160504090c0c1e0b070809101506090504020c0705100216080d030f200c190506100617061c 65
    0x4980203402c59540054000c1c503500401c016a00c0e800a0700400c81d008000d0140002c0f07078942a1442580c4c404446500c8500c03504084004250f9076200c90f4141d4203000141c000c001850b214541d002d50b01400c10007050080c1e414801c80b21110142c024003190200b804180625282d1800e000c510f5201d04e40702d072a00d600c45010ba42a07136500d94a03000800c1696016030100301c541c44075003500100410b00c103940b40c0300385c1c0c40350b1505034400761400c1d040c0321092000ca82820320500c00c040900001c000c1c00c0c4541d44550704154441051441031200089240101181d1803500340201c0b00c41880c008005c004c0d5034100801c00c40c41032003442400d0150b10a1140e017249502e98199240018016040500058980d140c00501511031940711002424600200d0100c0d01141c02402c4201c0128100ba41d0303140d00721840101e14001151100306440d200401003e01000310000321280f0854403890542c1d03a0b2541c502060310310300c0c444080240081074007000184241000a801146251f4224401007c65403c1d02c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 379038084 1250 379036834 379036883
    0x2060402040f090c0b040f05030a1a060a030f11101404091d0a0c05090c07030c030309031101020c0309040f020a0212031312030c090803030601090306020306180112050d0207060912 79
    0x5c02c034920760700420100601c0c080c181c00c1d14000c0c00709a0140c030444003199070300842c24178003640d81e0108481c0c1c1404915a61242c0f01807201559000c41d00b4540c2e02414200f681c00243d02c4040345105411000d00340c400c907885184a141c121080200c03640c00c0604002b0503101030302081d1031800d030700e41c910f142002908004200b5521124010390101a40170304090501c020303000010000980140100302c9c40000942c40901289596094030f0001a6100c031850126844500d40341070529560012031038012400021000b0100a00c048400f0011000804260f00c164092100e900c405a008a186003207000e02c0d181c000d5a00028601c0380d03004424140c0d8030604c101c8070540481d00082c0d50780c0f0b02900e44540241a0300f0140c168100294103500c0c1040000704020114080240201d8020012503041c1c0c85102242500b2010b9410190483d03866050303206500559480c151068030614005901080c00443d1705001d54125540c1d960400d410b0030750310015084683e00c01c4564507030321018030801415144 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 379039334 1250 379038084 379038089
    0xe01091811071b140d150608031804200909190606030c08180c2e0f090909080307050903033c1602102a02041103060102060402040f090c 60
    0x28188180350421444860032560b0681050f940007074459004040e503131711044c2009659500005030841101113207022805005951700212452102041440190710703001c06480c1e4919094900300f041d4105503250010014080b54003402c0d00204001b0201c4074200611aa60302507800486008591601480c050486d4042d520000020307940d03102411a44d45d100900c19081200d05007c03403018642c034032a09480b4074001c0070491155840c40c4d1450404800d08400841c069205002801a101400c4024000940c2901da210020b0b0013681c0210b80c500a91140d0001c441d0401c41c04c0e070179075485c002c05a5140d8814a05654148001c3c42290910903114610703005015034058284502a8030105054840203048044e103038541091104060820079820b4101c800b41d01100c2614039884800300540d202c000d43d030100015040e100c00071a4801c0d11028900c055944203070f90800000001c141e210350140016207920380160060300c0458058645500a491111152180029180440c2c2d440007140030707943c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 379040584 1250 379039334 379039343
    0xa0f0f060306061d09070e1905010f0f020a030503040c03060510050112020702011b0609050d0c031d0d030c060b0301330305150903040f03140705010e0109181107 71
    0x454240312903070781405003500400807400c1407004008105040d400c02d6050002450007610840001100c2c10300c150034600e000800034000c81d02001014986000d0300b0154002da0b404614440300e04001d940c85801030021603142e607800f03013503000304030340d0219a41c0d440070380240c4a113004400e020000c50080c1c13090070301560440b1010f50045150000242107007203440c0c813185206d4070501241c00544d1304440080180c0c466503105840e011802e182600040169420242045c407900b003020180300e400040c40c0b50118001d49495524403400149041600c40940b0184d41104082d075a10300028000c054048100b84508070214801c2d01d0705002c642100e000c001c41e035098a45000140d5900c440d024002c412070f0902c03001c2c801e07040e81143c0fa129034503000c3d40d070384461807950b00c00000d204030410310564016200c0e40e40502c840780d0b0703241004441e1420f4010041c14038013401d4400076480d809050004403040f0181c50b1007880f945030074240b81c0311010700780ca0321180700d445414042c680c03103188000b4409588039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 379041834 1250 379040584 379040609
    0x702030d0e0609012d05060d12081506040f15020709020310050a05090108031608070f240506130c050403080d1418030f030711101a06040f030807020a0f 67
    0x70f01c650a40da042102c01d525800c0c0440d961001c4090b590400c0d4900d0080320010456440e2213011908185410b4400b82a01a0000d04921015030196489018400c00d2207030211580300301c0100500341c031940c850200c000c1c00d050030800c5150340301c4a40080103801401591102941d480606041e42c0c41140d22082103241c0440a00075441c1c4842c0f480080c1000742c07074032441c5604050410f0b42d0303480381c0051084592941e94000003004128000c0700e41a80d84030907100d1004a43d481c0c900091100302800b18081201c00d03c4010454056100342071050743e005041d02c45400c10a0b42c040700414611481c07104100c4d0800000c030101d40040c0080c000024090070000380e1448100e10265840c9001e04010180480c20603142403551300001641c1882000b805920360341d4035088410b0341d68001b0300043c400301d0701408015110a0086174011001c20f02138040100c00045280100b000e540301d503000342c0c0300385c1038007078400c0c800715019002a03c480b81c03000e030985a10b10317140c40c0d0720010400704d5800200c0f01281c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 379043084 1250 379041834 379041841
    0x60a0509070c0f0c051302040b070308100b0a0e01030b0306160809250504060602030403050d080c040905091b0307061715130606030f0c1e02011d03040e090f070b030702030d0e06 78
    0x13003654803a41b1042c0340742c0381141440c0c20300032100d03640d102e140d501604000c100c1e40841c5031034280c59044002440303816069596038040d00d00241a914004140c2ca000c02c1c9043c1c20306509007004119503100b40c500c0b0045d14400341c8032002c1030b502d03090084c11240c081e02c141000f540f0402d41e01190340401003404803121200034074208c1084280ea01540280c0c2c1150403d0200304009400040c00b81501c009030b090203003440d80c9084c04101d150013035900403401903003000c0034400c1020001c90500e0303120f0004a9100d007214040c1c014565501c00074032446d00010403011680501c040c00a0000c0d4022660035000ea00034500000020424540b441d404518140e0b43c030410050705400d44598601c894048000344014681c0d8900a1303c40c40b0303c205035100b0511030f1424011386034030070340c464038101c0c0900e505000c1c2007006c038056696a81040c080c0c5000c02c040d91000c682d03203c000107a1881c00d01c15a0000380043c0381410552445c4d41c0015009c0d6040d44030038845010f0802060180c0c030364058106001b400c0322b19 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 379044334 1250 379043084 379043089
    0x3060d0312060e040c08071a03040807170a030605031216050c0405040515010f0510120b0301050c18040212191e020a30110702040515120105060a0509070c0f0c05 71
    0x2c440e07000041e2a40502e1f401c01090409005140d10100c400759020703140d035118100310490340314220000709016013844806522900c07030400751254000c240d408000c032a840b0300906560b240c100041d119130382428030940002064035882440c442e0f200b03a0540309000400e5010806442c01a141107410340c2100400100441419440a004100c0b203a00311130b4462070280800e20503040d14190100b007110a07085480056080c6c1c100d00c4041002400800c003501c2c0c48400f01d10580c103c1000003441c0760700020108142d01c0c00d8002d58010143c190001480750301c424062902d204210120506000e88400c000c0c12054480703514500300381c044030000b5a031000d4541000f0410115001d20010892129000541c059a420b1000b00b50000004001171140b414945441c40c070301a03150029845828942000103508400015132052502078641b103a680ca0705420803400e94800301c600c3c80c4c01010b4000200000c0c9404c800c0c0d0360300410305007402c40401c0301c0ca031182511021b0402081e2000c5580f20f034104180d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 379045584 1250 379044334 379044353
    0x812010e07081005010e061b071503060b0405240c0c01030b0d0b2e0306020a020c150712090302040509010b0306060609130e0313080709110f03060d0312060e04 70
    0xa00030b24000b0014a000a0f00c0c0ea0070000c00d004550401c81d0842c480c0502e52154070440b4058810707100da20b8030003e80d200440b40d481d0b1042c00791003148050b03192034001617070003409103800392840315070000d041c07a09260500c640b66030307040380034010408040490b800c1001a440182680f1703203458083d0901c8050000058155900602564060341c0d2039217881011540704804160864a481d1203038400c01c01c0641c2d40101c04103419540d4100c5001320b880082080043e80c010a10000d407502070f620150700c0201007182c05500d04000070301d001420000d0b000050b0072a4082e040d800905d003014003002d03490350003140c00c654040301c0c140040d0703540301c64a01c3c15250410010b9400310040f10b0003894070080c40081001035003000440b20b842929082943e40c098000d001740c0751003452421116041a640e02d955076651304262051249035890708120500f403511a0080340c0c0f130390080b14040b602d1a2200e80a000c0b4420000b101a810400d805804d060322203c1805000002c4c1a0040100614200340c140341c0b0380d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 379046834 1250 379045584 379045591
    0x121605071424060f040902030c0a060c02030f0d0c17160317010905130b15090f0403110c01090b0d060e010801020414030303040b01260a060e0c190915030812010e 71
    0x11200b6400400c030542d5540300d00f4003d0641d040d2008241c01500d4800f1034603020700301d02059841110300304045807007a413203201c400605000f2411030301c5600400001c1611031f807012408400141a014a400108101c000300405200c40341550a00e8400e1130020f5003001e100c40d5404500198010070302c003120030400c0030218050400d5800410083c10081c00180540840b0380d0024400840c540c0007501148502031070001066000d424405203103044520303040180001c031001c801003040c3c00303900648840d000507412a504411384a0807000c0e41007618940050300407140d6844241c0d115131005c10808124041c2900a116a034000350f1541c0c10030045031101162040198007a81c018001c01c40460b0440d107400e070460740f0001214064040702d0303201c50801c698003c0030750451b10a043d60401040b03072a600419409400806488203035402c10200941120400a08c40e40c00c41001002d00186d6083d0f40840317840c400031841c034084160f0f40d41e10b050340c0c0d40100650068130240c0e074004000361021031407480c2c2d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 379048084 1250 379046834 379046893
    0x100b0f0c010c0e0f0d0606050319030f0806090408030a020c0d0519021f050c1b0d080c0a0c03030c0e031f0606090324020705031612051216050714 64
    0x301c02a000010540aa60b440700301441131100717440b40420b0090030703849440038000207002d4901d0f4400c01800c1e026518404070007100001c9918a010354201c0c45080940d00075000104600800e44998a50b509190009400300b150154204210741a60000f0490510380c403801d0b40b582a2078411004000c644080d1000b040b100b55045000303807100328600c920b00028a202294400501c4e0340f90150448880d00403010040c03da848130480a0011900025046a01d42d81d030342e64116490350303100380f160100d00a01305001c000c6504008804000307400b0340c000c0b100314001e030318006015140050000b441d003403c1404084815440c0280c24010100c64041e000147c011405d10301c0001e441d551f00c046101b00b000c80d22003003500220541d105440ca0310b4040358200d903009021a501c40c1c2410703007041c000c2150707001e080f02c00b6003545c6510707110580140103580d000f10f404808425680d44070700407507010070800d1231440700b0801c08002d024005007503400240c0302020b540e4001c1c42542800c105404400d0030045002a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 379049334 1250 379048084 379048097
    0x11802030123060616021011070b07050606012727020301080706030207020612090105092506210504031d0d120302130807061211071208100b0f0c010c 66
    0x842c5103055046090b0003400a541d03295480090707010104400340b04540095010700c0802c60910403541c0000c504c800305c0d07031040c156031400c1d95410600308680300d5050700500507000b410000d400b42d0301030750903072442031040090050000d102c17400d0008484c1c2c1c26080800c900740b400750385401c1c00800c1c544002c4001c4c500e9004515550400c0c2030320307990380542d00c00c40301055000101380c070454449074143e40c121680c0c1d41d0012124105050054040e2004507000d80f102d00c181c80c0050300c501c8030710409800c1111007080d80750301d903810080200c4284800500d610014290210382c4050086c0c58070800d80701e20301a40c0c4039401d0410781c0d045615140040d1051501ca1800b040070310000c10b0341c9000c4040c400025050050741c5480c064017400000c00d881d804540b15018242c0c0014246810000200084034030f513804200c000c02c03036089212640180ba801a0466100701c03020b00c189409044069000313172038039058070440d40e522000d0401c3c0d03034001420712014800204149103481c0c1c0034041c094641c200c60500a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 379050584 1250 379049334 379049381
    0x80307050f0a03080613020904050403050d0b0906150903030c16030b090607080a0b0d0507060306060207060c0c050405060d0b07030b0f0603090d050d111303110a030f1203020c0118020301 82
    0x80403000090103586c45154500110740221400e0b9049138155580a030003404546024200601383da00100d03ea000c603903081c2100454170386800c11800b407007108020500b09031100f02040c1c009030344d00943c0c840d6425210421903428104010401d80305034070083e4409460b01801e41c0b601e08280c180103404141c15901110601041540000c1147e0f40203010b4100002da01d10b40c040094043c4a6203007015005018903007011806c0c0d03502d9004002a15029021214901e54400080303804014026000d00706001d2554144a10324040d04000e4128030010445100180b00c2e446013114a40183c0783e241c082540e4452001c10b6040125107800c100d10122801070441c41c0c010300d1613845440a111a1040001c00100e084504100b680540c080500303500d0801d480c0c1c0309070304c06036081b400c0324001900d820000c10901d1b58180b0f4140f0700c41087d20b9100307000340004422075448007844103c546000702816002d10540c13070701c50b000744120403040b01e00495082042c0c01d64014542161556005550108080c6111 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 379051834 1250 379050584 379050587
    0x309010b0915040f060509040b1611031c0915020a02150c03040204110c0102040305100b04020901050a03050c090d0809040b030c03150901231602390a080307050f0a03 73
    0x4032818805450102d1140c0044e00c1d584014039403a040140c0c8040c034101800180200440da2602c80c0c10042502100100c07207a106880c81c50320f102d2240001d9000f004410500142c20800c119403d14058012030000302d540c1c2e46404101d51602a003904550204084440560412040e0804240407010007103a040200320f040540c440208007074015601c0744088003401c91944c080f24007555409008540796502d81c68032940b1240750403815844541031030352800f60341c500b600c00c071081c154058481d986040840c10041d0003410005040340d0700b40d0028020a034964648085c01d00b441c61060003019035854080301048200d03090071455074044d501c880d88000e91070300c000951380e0301154040d02eaa001940c49144050141007401c0c004148101d10f48405001c490780d00c540540a81c401d0b0f207040c2d450003403610341281d4504084424250342c055000040008404034920900d0002e456603015054080e8440410300480241d84120b00f66403002882405000e001d0040b0351203103903400d002c3d003113031409a1030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 379053084 1250 379051834 379051861
    0x5160f0509221211060603060106090608071101020a0305220809040929040201140a05030a090614070509130204030209061002030412080a1e140903010e0703080309010b09 75
    0x382d10880b0495152600700e46a010300440c00183d070241c00d1940803800301000a01c40405490242103601c61000880e41510380459620306848080d80ca91802e80e15040044440380006812075043c08015030700d08403090360a000810000c1d505407400702d1141040c111403140542084c402c61018100f010009001401c0031040300ea05c4601245e0119a102e030a04004108020700200350300140700003103070030310100c010002e0b09100314000d0300e425000d4084440001418884c0954000010f0401c00c002071071800d0b41c0d0300040301103000310b00015184408100d40c05181d0800e840d508041030022440811929140d03040701e01e000c95441083d03050902c3c5030b0104440321800f4202501c100d19019195030120f2080041d80c1c0148034209200c82d01c19803d040c103403165802444460300059040441400e1403205540c400074000656884038480380f01c005004050350080b10840d58155219005523001200821020002d54000e00740c899903810100d03003050848110384507441c000c08002040141d04803581a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 379054334 1250 379053084 379053091
    0x15010c0c0315020d060f03030201141603090c15031b09080a060b040b0918010b06091e01210515040504080d05060328030207050301111b010608070305160f0509 70
    0x30210381c40b11910380d070601c0070380140040c0b0b086181c0360503030000d940000c00d01da03071045a0003900200300c0c199070345142413031483c8115200780c4aa1104c40340441c07614482d5005404880c002e6141100c0152210b9001c01002c10080318900000d0700c40090180220100e200300d0034110407410300b4030019242140707a41c0c84410301d42d0080c1000e81e40d82a02000c64441c1d070404c113110701c4018520348080c5007020b01c0421031200c030741000c00745611301030083c412130404ea011603003807134802070140e2400d4024440c601d0000403150f00d96810042803c102e1038201a0f000c60711582410307005000700301071800d045040c103481c2d0550320040c13056081c84d040c4008a04564101c989250380c01001240d99a10040401d00c0c143c40107409011801b00800c07101482084c0910600503a8400d90036154400e0f80e8000709405d071006050742452070301d4200129140d849444c0142c0d41e206584000102c0c03030320340e9220b405083c0592a40f0580392500300300c44541e0b40b82d528441030070142901d45c0c40b508480c2e0419020642c200c2004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 379055584 1250 379054334 379054343
    0x6030d0906050c0a0c0b040e0109060b09100c0c0f1d01140910050d11010305060d0b0a09020d0506010b0c100507020309100c02040c110106090905250f090515010c0c03 73
    0x2c0d403a040c0300002c1c05401c0c41349400c00c240700909960b80c4c070348010540c0075205400d43e80b80020300110311507110f40220303412200d420206509242900b020400c5002c038030905171091140b52098103001840c010440780c01850700c1c3e01102815481d0101c1d000a0b04c101c500d203040701000400041c00300b88060498180046026504080140d40ea20810f200c405200c2d08501e030300c8408401c18208018400302d481100d08405c0c0d9040c440790f12100705000d035403c60098010306550440c0d0015040e4142580100241130004050715000000b584549007441400c2c1c00140c2040c00019401d005a00d00b0800c0520712040c0c0780040156207000c1c240213490380601030980c2e2083c08050301c60b0414900c602400c41c1c0c0142c00070010004145c91075009401c3c841c43c075070b01c031040b9400c0c400c00142c0d24015100740c0800c1500040a40120954040460000c014100c5080810b18080d44003189590b02405400060010000000782e142418000c0c402c40700f80301c10990381001108004400040c1d951440001103d501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 379056834 1250 379055584 379055587
    0x80703030506120303010801020d06120201020c040b040f0501030506010806090a1a0403050408030a03050415140a0506120f0d1d010509190510020a02090c0f03040b092a030606030d090605 82
    0x1000700151000c80d0f41038003c0000c0c44040000f1880c0c2c2d070194001c01030300c40200c408021f86955004014240e041c2c501010740943c0084841440504242d0406200d904000388005210b15020300900c0407a442030304180d505501041c01440703c40e108001c180d411850f41c030000c25045c0803954071250b0350301104024803048000d91010400301405441590060203000d400d5a1305c580805d80010000e0034122001d80d2031212a0851107000005c6210343c408800801040042a42ea01c141060192402804a0b030b005100440030966040050090b940c86d8420040604a121001c0800600c1c1000340901c8110340041c81203203c10302da8204080700c80138503056031038281850001401c00906a06d560005811250070700a101c00d043d40407035a409254401c40e0b00c01c000d0380310520840319030b016070310100b0011501040420081003c0074a91540700720001b0840f03c0920040031203007420100c28000c0b01728031520304441c809914051001a9001800b41d000746504112010002c05c408200d1007000c0c01d2120 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 379058084 1250 379056834 379056841
    0x30a09180912140f0d151e090207050c191d06060703030e010f0c09030605100e180a060908040302030f060705160f05030c06070f0309050d1d1e011103070807030305 72
    0x2c2c10f400e4030150f081c8038a41c152180101c0c4c0389076001c4c01034070030142e0103010041c001241030310000c0c80b80b412150303401d146642241e08020180d80294003000003035600c2d104030442a9081d41e101c0341d640c2c1503400070506101c80307289000e8040e40341a94089500950501390300412a081d00e81d04240e80e035943c0c0600c1d0124840154116040c010102c01402032030311802c00004800094011508000703d0344624010040c950340c5001815404e041409060a00c010b08004205000019502c00341030744e0340d400031b0f102e8001c8030356201c2044600050f400c8441c1040480c04206514003408001c0507060100302a241c40c0c13a0040c0d00906078880d10340252441d500300c2c0846002d0040c00744c114664258090300b100d80e1446003540e01a034520007140d042c400501e441094800c458800d01855240d25070090041284d00c01c806c03000d4608100c0020516030b0300170107048045190360b90311507100c903541c1080340070800505030400040c038501c2204072114255004101d081c000882d410120707143d06401d450b0010380fa44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 379059334 1250 379058084 379058117
    0x706090803340302070513050603060601050307090b0d0902100c1502130e010b220b03060d110904060c030f0606050423030313090b10051218030a09180912 68
    0x248400c50a2000700c042e00120b4101a0000b85980641d80111401450b2079205600b600c15103004584882c1c040d001a80443c03040e5019101440e00318030941003101829031102c04200054000511201b42641c6650040f01541000f02c80310b92541d4192403c02d030b00300c2c425115098480c0c20f054081c00c001e0350004500c00b41801d00c90404000e0040010041a1543c3d070300740003a01600b00c011814a14041c190144403607210307211180048030300601c54075081d643c601c400c00000320307010381c4191040840f00610f422983c0c0d54244c0d05100300e2040e00001513100018200a0488108a00e4105a02d01c0e168051200940020550701241c220300a19402e02000d03000ca180f5100b1011206a014403020565031a6005207180901c15035031504410840c542902c2c08201c80c099000340f00c800840c0742000b02e038803c20910000c031035111b02034465010f400742030f020045196612030340b81900040d07032400d800d00020096440d0540502c0303285505022400e45a01c83c0c400f0701054102400c10310010420151a44 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 379060584 1250 379059334 379059397
    0x809130b04020a030f0b030c0d1502090406080f0f0f071206110403080403170403080904020306010c05070909060509013818011401020a120c1a010f080706090803 71
    0x103520150041d9110f004030703400500a0060902d169a03103608000c1c1d078526500700028142d9071840010074450320f41794036886e034042d01220804800902da03020010856140c0700c0d800381800a00c0150000d040a000311513007a410b0810301400202d568101d0320070441440d00007d42c5000b81c45030503a40d08d090340c069140640041110142c0580b60700400304001084c00030607406002140d0290b80f2401d4140040380000c841f612590200618020f020321100c005170915501441d80407a060608040700c00054807464600350003540300000750b90f107070402c3c4020040b440c001c1030b402011302d4000f4068244801a000e44601d2603242d40f1020182130704111100c8010300c41048955100904a42d01c030b140c440e2805847c050090203202d00807102d0155107650355100145800200783c2200400c07400c9403405070f040707900d20001035050303d25903403140c8800c001d0208041030314020900381003202c2056107052140781c24029039500103002d001e8141000c101305e03c4040203e43d203589408807200a20300c01c0351040703001c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 379061834 1250 379060584 379060601
    0x607020d11160b03091204060c0f02040f1a0a0501090b0d1119050d0e060609061905180708010b13090b01030f1a0306220b07020307051603020f0904080913 68
    0x408880002d03126407810015405400c9038010795800c1ba400002e00040d038465441600c002600d10001c09006c80c0c00c104c841c5810a2005001103800d03400042c1c0039066404101005200381c1c04100c42c0400307864a1904440282001c3c01d005403042d1800c130101c2c3c02406009104c003480d41e2561801c42181c81003d00312070004407a660b403070074500266000140f0540010112070102031501c2c00c1903000d101d00240c0d1780d1180c40000c2001d241640c0d18014400114903a000402485402e5040810165141d800b400c41168802504500c0c602e08108020038801701a0f2111170300d0715080003104048100d03280c03084151003440c0e40200c0d42900220048008117524200c0c4088545008140d4002c80c081300c00c10208500e049040383e45a40740c403107404561880c0005d01c1840701079208141e00c00600308250041e0301c440c0d81d0050702d0034104180ca40a0803c084007150490a2201603414411481c0c4a88a40082d883c01c0d50b24485d44d14050760781031101e01c902d41980707104a51900300186c1e2015a904250038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 379063084 1250 379061834 379061863
    0xb0913021e070b070e0f0f04060812090a090902150717071b0e0903090d060b0607141009080a180306020c0c0f0d020105031f03050601030c080f0607020d11 68
    0x800107200003503924603040752000300e031010b0449002c220b8243c1301c5c1072650307241100104160310b0446d00070104400d400007058280c0d0041c1d151040090b00c601e0a1203040b5481a010030500e540d440308204200118426402c801c0400e45810143c0340981c80d1288141b110a81410f0001e07aa9110b9040c0032120f060512030695120700001003140800c141c0e20f041c0c902d0502d0804000c1d04403500e400034403548081c2103a1001c5250f005003c4d03c109407912610021441d4003da4001030511602d0300420815404803e0030350300801d80c0d04000200034020000013108900040c3e04201200095807000024400c092040c0304014151080c80c940c0540d2280c3c80000f150b00240855440b000d03041200c0c0c54040100400f0300c2003161122018407810310500040865034141c0d61b040c6075039076209107424241c240000d2030b500700f00c018502000182c41040128007a60080040c240c0e06441c1414007031234400c00599980f0b0680003c0d0038889140c0c1c0000e40d50342070b1032060410840410700d640303550307240c41c0c1c0503803040c6c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 379064334 1250 379063084 379063117
    0xf010e070b031308070f060518030a03020d020c010603060c0f020307021c0213050f060a06050415140c010e03040f0b16060e030c0714012c090402010c0209240a0b091302 74
    0x10001d442095600b000e07c10030081c403459488284109030119111021a0719030020040400400d104c2cbd03005001071000b000005080c44280107105003140c070241c004450066840303128540300343d00185c0041c0000b0442c0300031403800000e1f07400700e5480d68200504840c4880307001c20000855842824080803500601c008100038a80074003445980c1409407100740c040e401303a44010036246d100d0307070840301960b10107000e070242050f1070441100e0242020045a03207682042c008001c10740030038054540c207061003500441d01d8134140707a0b045c842040680e01c81c40c0f00d00784c1000413a2080450103456090b940c1c212200040c1c48041c642003d04501c07502d410041035005001b4086514124240f451350304400c01e03a00c00c4140440e0444e0359011100b81c08184c504035228800ca0040c5280c54030b0b10710b500510601d0b00f2034003030001d40d000c01c0d4a41c0e02502d0400c1400f4050310980010a80e0131052090550220b1b4100c10b544d142c0706100d000352094a40e010f0248000c1c130b8520030386c2c24a0307404490340340804182c1d81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 379065584 1250 379064334 379064347
    0x41e050f0103020a14030c060c0a05060108100f0216260706021809090a0f0312110c010c030606050423060c0d0e0d02090621011a030f010e070b031308 66
    0x500e00010900003203200c1c100194001c02c0299128403405150400030740101010780415003000002d401490718241e443c4148000d4000260041c01440d0007040724400412003c100e1544044c252420a14a40d114a01c10700500c01c4100718030952150464111450000000d185a001c00040d5458803c4240b0b80000050003420000560b004150741c00850010311943c05424007045400740b02034440408540c000350f480001318030122042000c507482030a1101140b994540b04005460460703090201007000401e00b040150001e00481051003460b1500300400d07410300d000900b16009601403a917110092110620708094003220318040500010959a2035400ca00506907869030b2400b032840c00110b20800c40907541c1000180310705c0b42d644c024215215aa58a4107008048401441100c2000302070a02030400582c2172040700c1e41025661803c40740403641ea018103240056000345400c0c260702d040108216060003182000c1503c1407080580d07902e840e48034407201c4d51405100e010b4044034000620 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 379066834 1250 379065584 379065601
    0x108040c05030f0d11011404080309010207020409060905010e07030803150105041a041d040f0312020d09051b010c0b07050a050d060602030a08010819020108100906031b0806070905041e05 82
    0x80e104c656455542422082c2c000b4101400d0b5038514a06410490100c030100300000c00c028042e41e4803103a940001818010183c0000d0180e031000a41580c0e40c0b50f8072080030062040a000da01d500c042884000c1c00064a141c0d00c1d4905840000c046000c5245e09540a1421380e1040f8101e40c001c0461440c11030410311000400600d6030700038418400c1d200c080d58228404900205030705880703550800ac400541103465101507402910300d850160250303608101e01d40b00b0180703910401f800e5500a5005000c54038440d01000c4040807607460300340c14000c0c1e0340c5803200052640c130b107540e82c0311a0515085444400054081e280c0e409070603800c00714207090860200c0ca459000016081e003142d81c1c2d0b240c0d0100d90742c40014549903032084013030008540c081c582841c05540240d0040340c004000b01190300040d9500c4d044901200d201343c000b01c1d030101404800318005000d00e480ca501500050700030f0006414503010150980f41244078140c040e0ba12114690050030340d403440c40230035006507801404945080c964 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 379068084 1250 379066834 379066843
    0x402030c0108071125170d080705090909010b010e06070209151c030f12180f022b0209060303030f01030b1306060924050a09090816050610091104050108040c05030f 72
    0x401c5c484621100c640051021001c40522802000301c10141126071282203040b25032000c018466014010204400a8175807104a0440d1060701c40784000545089020001003445074290016803240304c0038440000036942d00030406400001070160320781a80d559002048440c1d12b580e44951504403d42500b4042c10b130001220f40005089a0b02c07030304540070041007802241c1c010b040358106c019103915590006480c141100080500041503001f074124580201100c0d104030110050b9040703400d075480011401d001200640000f001c80c051030540c6810390112280301014030018007903540c4000410703145c2d44842d8150a40b01d0b041041403000ca600ca04600003d04000d0180081c800c48840c030325074030700844c059000c050340d000a01120f40035140000e00400b410800c1c409544160042000084520303074800020f12251040c009080d2030b151985c1180b82c04480399000100040c04c140002e400005404121403e40d182424411025100c4d82404407120074290007958051080e8002922003000024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 379069334 1250 379068084 379068133
    0x181b0a0f090b04030f1e0c0f05010e0901050f06030408070f1a07020604080a0c02011103070516090504020303040603090303150b0d0f0b0a03030f1b0303060e07080402030c01080711 79
    0xc07603280c03000340e4500b8904031030301c00e520025080400c89049100052600700c4030314540304202c00311440021072501d41800c0904541c1c0291001d0142500030000c0d960404000618504115142c294640c0b4000100f110002082c1000d0300c102d00003c0020100f180316029594090340000003040031141d030f8503004940303000498030046d40c000003400040c9507a100082092080d41d000c041d182c140b0551000689051030700030340807810b1020885100c88a5441000500710300b070300500013803c0e02802c448040300e1006068000d4607129003040200000340e10008221011561a4540090501081e04049000b0b12903800c041160341400c0c6030015100780c00101500c008905410100103100401a03054221078203605030540110040200b0400710303019008440c554095400c5c9506210541482d84000016401040700800da8416062205c0201c6540359a4004440d017000385d03590809800091351802440c132524100318150002402c8548240305031144c41241c6011201d075040c43c02c440380200ba80d00c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 379070584 1250 379069334 379069337
    0x10504020906100e0f010908010504060f18050a1e21030f060302090f060d050303100618080c090c0f0c0a15060e0403110c10021f0605181b0a0f 63
    0x1070101d40ea40c50304604000103035a00c0d860303003103046220301c052000d1504c000c0425814051160340019002c5401e00034180301c2d6100c1d400000d48242c03001c070781e0340480f1500000ca80890900405403400694006526007481d60070411110341c8900405101d204034282101c001e12031880403003408005882c3c10380010042905440622920700c001480004494060bc0081d40c020315010208aa012072040165085640900110702050860320348a15651083d65020340b0030030000f00070800c0c1e0f40c2c0310740221180b9580c0da002c41c00700f52130041d08540d00d17440000803030f04c2145034001040c034075902142103881140d02c0030138103520380942e41c4010780c4520380d44e041540c501c40e2091602421702ca5610410050703464020101d407058449031003c885803103c01c0402c0c066841030040c62001070b69410070a075a5a01207900616063fa81d08003d140149440d44c0901041410070a0900c203c0c1d4520100d510b0680d900010207805640e118011881d620100c1d010b0707541000b0028800403140e43c0080b500e025034115 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 379071834 1250 379070584 379070599
    0x603180f050c011409060f070807120c03021204060818070e010f0302041d0a0f0602070b0f061008060114130b1303120206041a04060b13020a110105041a06030a080c01050402 76
    0xf5441161907a101310170005920072020005410300c00002405002d07024002c11100e4280880303a9900c44005421003044008038080b44194410141c1c100150700d410a80343e40d07901c0c2450310b40900a000902c001c1c1510350f10518480540c005403a0412245004001c41c0d80040700c60759541c40034600d41d0300c00c0d0009038000d030706064140045041e00580d000555402d04006d1036000020303150050140c03610350040711040d808020f03000105442400b001d00400482840071554285102082108850144003505200100c000c02c040742c0c3c0c0018400c19012083e241d06555201c08444e40041103626401035a0b407204041048080d008804a5020640380b1a15004551030200319040c0e0f81c1d44401c95000f011200c0c6046070040002d03905508070380041c4248408503410554200040415004503c0c040003582d0210340200403d41c04030320507011000d100000c01042c1071949501c0340070034810603441940031a14011900d07e803000c201040000760000442603c0da04074078012800780c00306031801e0340700c5c0c0348 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 379073084 1250 379071834 379071857
    0x51002041716030b13171b010920011101020309060106030e0a05210d0903080a0617120304030504050d0501020a17012607050414040b0c090a0603180f050c01 69
    0x1d00280041040407010401c00c010342c5995103110300c0390001400940e80e5400b001c1032100140c010500c1441100d800c9401c0d40c0ca40101036401544564030300b0360201a68104041c0c00c022490004414141008600c0807402c8100e03203030016030703480e03112021030b0f03446610000030002c481c000803a801c3c0c16034400d90f45c01c0c07000300b0f048213026a6510014401078642c0d0010300d044d44211140c0c041c501203541e002142030f401d2060461081046518000c07055010a490004021f108801031090101400d0482d14810000080d00d01075a61030007001d0100316542c100101103410b160181060f500107080042c070b684c4c8466414645503010750490740d83c3c1030108200100c040290107580316a035050303c20040c0303c1c8000d0900c00c05604c9980c10303032a080d00818003801c54003003541c2c3c846c0d01524a02d501c1c40d426032403c2e405e081c5040c07211214018a160913509061100b214140e49000300303030045490030310300802c50000110500c0d02070014a4002071040c01c020f80c80800704440414081581d4400f40c903031101070303103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 379074334 1250 379073084 379073129
    0x10603020a0f031502030714160614010f0b0c0a02090c04060f02690d0c08030709080d270311040f090c0803030f0a09030516080705100204 61
    0x8140c040101a46403884d010a84603680f507015540c440001c0c0fa0482004100a5240341c03541e04ca219100500080041c000040c00110f000c2d4001301c1c03d84481034006589000220081c11146004032010080002a070248602040056030600d5400919004280c144001d82a0080d8018415100800c010025491469002260b460881e2020980c0115910304c0449042069860301044130303d010054000c030a00207000c20328030b44100b08100c45804c14000b112400020147c1400440b01d5254403184c0558081507100305858100e0f0b42c4a1130304c94503912200300982d0782c0b0407950010b07010f910a1a04801d83e071740d400109880e081d0038180d841544c4082ca000311042d0588240009041e00c0c83c8445040e9403410305510104c1f103224464000114400300d50789180e4a0b41c52544011191381c0088180f0203442c04009c01e60760440c0901000300088504d50b81d002d003040c00f0b01d4482e01002e0440c0400301c410700c19201d04507803030b59520505440c11564001180320094109000307081c4800004007107450a903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 379075584 1250 379074334 379074359
    0x1e020301030209061c051605030f0a022b0f0501021c0c09180e0f01090303050f1015090b0a09060806010906021f150b090f0604030b0f1b0c010603020a 66
    0x729000b0703250302d9259403404180190841120034424101081c0000103021070001e00c41c1c806030807407403e0180c201600d090101031074480e80026042140e00000a2840180e440ca40340c081c000078103450039068402c001c086500f41009010300034141c90480f1107124200315041d03005000c032000001d10404054448a099003c584d52a2a05008144040001e0285000030b2110b2054030141e01000b142203140501081d0071310002e4602d00c130307082c0e4440d1040e40403d605030280075030002c0d91003611401e529040e800c0030f20404140c0b0402a60b8042072443d40c0d0114441c200e03c1e400341031600074440e0360300142800289041e10a1040c60000f4a5803000b2582d00d610488034241110b0b15a070003803c40c01d5506c505a100c0403106880300c40340b01ea41d51003181c202c81460021f4401446840070064880080b02c01307000d02d505201d0b546500c5607400704014400a890031421980241440c3c2102e41281c0e2121802179070800e14904080c1d0b40235020030768600c08203054000328250381c8281c4915107080d50750903103035040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 379076834 1250 379075584 379075589
    0xa0213121509080c0115050a0b0a0207140301270b0c0f0f0d150602030406020706031b0f1403180717190309092c0a15021e0307031e020301 61
    0x601d03410281541440d959082590054003e80c1440d1a112050b4801401c44500c144901107801d141c903810005403401805420080012140061501101440c001d4490380c19000f4420914400600c0c488c880e1025842162820080c0f8000010203007030307051040320f444180104035884200b0070005216040f40c60282c8152000c1040100d040103080e03035510f1744542102400302c1c0155540c100804c0c00340d00c11342c0500010300711a000b4540d03450034008000e0610791307241c200380141410550101ca0402000118180c441d0542c5440f181084581604a0360b0b08202201050305510201c01d0000403601c202141210160080031900400e940e0030b9800da2181081d0a0b04a068000c0c500c15121889e04500302d500d03451003890140340310f545410080d022268120611110500300105041101c40d200d035244820901800040ca007142c0c40c0c2d40e854046c26a2818010800742e0045420054502000309600803111044076041d00c134941800c0c000c006050480c8149400002d82780300c107281071124400c8030706 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 379078084 1250 379076834 379076843
    0xa1e12240506070203010f060905040b10060504270f0b010e012604020d0501090b04110603160e03010207080c030702040c0516170c0109200a18050601020f060a021312 73
    0x410361804003044143d40002400340e815549440300c004001c2070912501d400303429210700000b204d00f802d08201000c2d100c010071803003030041b0014050110503080810740b4100c9070880f0220201201c44841091400c2800c01503805040c20440360300221140d68010b242d044000b80e0303a00442c01491001164401003642c4841030b007041c98114402c03032801c01950250322074000303400790740030169a558480c01c455102e0000e945142898082c071081042036086d43c000100203c03001829400d1285124202d04001c0e8082c50503c030402c400c111079520290103494905400c9189261504502d032200b82d00d030303400320804a110b10f1401905981480c000c0341650251081c1e004540240c82c505e580e5071381509114a824440c0035024003003051031381030034002d00c1e180d54071903181042c00380c034082c1030072142110703260b0041d01c1071000140a00c10743e04501c0b01c0300703d90844100003140700c0e120500140d0419001c0300c608085402500b041200e40c1c600c42e0000d107441110352010418080c0e8070350308624044003007000140b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 379079334 1250 379078084 379078151
    0x1509230c0616031403010902031b0903060f0405010b030a0606031103010e07030602030c04051e0f030c180408040302090403110721030810090f0f0f02030105030706050a1e12 76
    0x19641d2000300c0b449210a480380c20400091082a10f0700311a6800991101840a400000b00600807030070545030421040b03800c2c1c98509080355540080e464901c000c010008202d003250001e0180042500920170307040020b4182c0c0d055207568103100c806803032580019900b60000c68103154a60405104101003880f07080c02501d041030031961908060752002d0001c181468046c0000308a030341d00c00702c92001e01c49043c0d403030560342c40c0140180036124000e1101d540c070a8101c00e800e03160320340718401c10305181c00d83c05040c214203039690301d4542070b0b60156400c0a034200200034100070405030080041128446d8000403201944e0313440d8980000f860880b0700d0f403d00455403141060019010380902c6800c058a214500c0d0100c2d103481407082111288040e000c5d00944900f030100b00088248102a500001c00409615540c10180801c6d43e61009200341c00803c0400124001d046111b02a940d10301c00c41c6103a40740140b0740300c4c080200075494803440d807211039281500300120241d41c541e034941c00c2d109004400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 379080584 1250 379079334 379079347
    0x703020f0a111002011401170d0806010806060703031d0c0910061706212d06151207120c060f08010b03090a0b0405030a111203131509230c06 62
    0x21966404043c0e201d400e540d204d6401c6c180c03030b400366035800340a004520b1540da03204040900c2e80345040005401c0c0414440d2050512107181d9000032082c0d40800700380e8103241d03154031502c1e08400070a200c49049110301442e0030003020b8000c1c081601482020b044640c0c0b0402d031503031012000c2c02080d41c454003001c04e6549000b0a11420714051696002d0b100400240b07030510101c10317041e4002494210200e5039040385550740b44000c4003090504070802c26020440031103007400034a81d82d603c80501526a0010784124081181e540c840b8480791039240358003036a4015a0f40c0203003c041800340401240e590080840200d2a036200301d1f00c210100040750b50300c4071580d20b88082c0a116500281004019000300c0c00843c003c240c2e041d00003405144240002d541c0d9189021004000800e085040c88041c0c0000410440c02c11280c3d0940313411920020f040303401c00c1d103a868949820030904100f200c8240c00c0030030b01d0087c080821002205c0980f0401d0080801e04940321260f151110100155408001400344 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 379081834 1250 379080584 379080589
    0x60e0d050f12100503101d0c033705030711090708070f091a040e01050d0c030b071b080309010e0102041a0d020f03010b0d110a05030a0b0a03170703020f0a11 69
    0x1c05800581d0b0784641c1503415250000729003010f080a00c4200324603180c2d010341c040c072900d1f50010102a8408409080c00d950b0340720001707440320044803411400485054810031000c5d1601c80c2241d0410081161000030451441c2c050788075080701c0da00b5600304414007a00307035040c00e100042c10303c141102c0e920765000c2d0390b500c1c0c015a640c0b80d818905a00f000301c1100085000c2c0080c0c2030f03100c82202c0c00100c1d2515186400c4191034032002c1600001c2c00b500303048200500080210034114240d0307034030082c0442690b4074140201c4866110200382201c0c10000b030380d5281489074040003140a01154402407044900c1400514244d1203640f182010f84882d8170307440c2c0340c0400404003901004091760005450503c1c2c003401040d154100385c0110b46186000100c00b1200c01c540d1141c07400c0e007051541a035060450460020741a40001032203000c010b07481d10705181003965024000c0019603840340f202ea000700d10302002d903083c1d508031074011800b5210364096481864000980d01600c00d5210a0402094103180107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 379083084 1250 379081834 379081867
    0x315120b07030e06090106050405100503070611100f06090b0f1f030b040906050709060314061507050a060b0a080102090d140712030c0303110a08011a070609060e0d050f 74
    0x406002c02d0782d80e54804010050134040d99018a010f000003181040c200002c1000f1100041e050000800500380300308440d45002c20403208644650034202c00d1700d00c070110081d0400c05406c155100ca02d14002020a245685903ca4001da81c2c0c83c038010082c00c0346410600c175007681c1c1d110348240d0101c8070001404c07a01d1010b0030b84141d040103500d800f00f200e60600011030706481400004844141d1600200041a580408500d00030202c52a00b4010f614000d51201c94406028005a008800040804411914000071180810b500404450415880f07082042c0140500304c03559102d00352541c40020301e00303014000ea884c0e00000400050300c041041c1d90342d02e403101c048003428056001c0c0e403100142d1000000351007410240261901010360150740360050484915058400c0135074810700441002c142c1c401211410350f0001d0468039031079030715a6070000841c02120b8000300850f04050700030040004940055119030482400c56407000070005007510039006889107418400ca041c0a1004d0000c0707540c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 379084334 1250 379083084 379083091
    0x7110103150506090409080c01052a07170714010f05060a030b0c0901090807090e1c1b0204110c031b030f03040b04170f09190605040e2e060315120b 65
    0x41000810406d20f503260811900819654401c7e655100100269202d070755114501d400300f203030090340041c0440c082000701d90280c44009040c0e003500c1c0b6101c0c0c05d5200080220fa50a9410000d00c40d80c04c05219203490107084a00303900d01e6010b0030f000c045111030801c2e94060081d07079440900c0348a40c2d0354002529003140c00c649035881c10040b240e140000c41200038803d01020b00a12103000c280440c85001c1c4174507081c0b241580391505010a00c142c0c09550344449180043c030043c040d2a1601d80243c00002d0251000000e0721006400c00212004031710030010082440001c031030055240d22800090703031501da000b08908144036000801c001000100380b0b0f0500b65010f4460520003851807418034003480c564010340ca030700b0340703030600060042c120385421030480c1c1044c03020789008540d507400c004d802001401a8030415103035540b03100210780300040490041c030088001e54020404070044048084030030541e8403031100880e207024021108502e0680748003003950b0900d2080c080340c480d182d98181d46907100a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 379085584 1250 379084334 379084339
    0x9030e091b0306240403060605190902070515150a050d030e0907050d09080301180506010e0f031009260a0801210b040c080c0603130311070e0703020711010315050609 73
    0x30007002c454910711406003401c544522071380039162411441c0250884945821180c40341003040100e801964041c02c0010030b640c040034000d13032038550600e4110710305120103c03944a80e000c0b080c100315841450b0784d04a21203007006ca039074500c0141e035101440103c0b1440301018001614040d245445400c06411554003c3c4903460014949504500c0c020110f40e05100c0889410400000400c90049525040001e9050340380080113a0305105001030329181704168041c4c091102d40102c0d040e103a40c188013500f045d500e03920050000036070380c0c600000e00d10b46418440704040281100006031183c2c1c0019500c1c0d01d2001d803a007991907424058400d010300840410700d05071600003181e980014488210040c040d51113403041c2218542442080c606042c000500d050042d00180108100e0350804141d030066513425041a200f09030141c9919400c21059400458000b03543e1828411040c2d0b066006062240c010054200100d081100444c2500c4110081149035183c503d0140030078501800103103c500d000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 379086834 1250 379085584 379085599
    0x14040b07030c05071205030f0105040b090a050604060e0103050c040e190318090c0c15020f1e07050d0e03010b040501030b16020c0d03050408010605010f08130c05120109030e091b0306 80
    0x541d2041854102a454500000c90100a0284144030b064442740500f00441d000d008824562003c01d003110401000f60b8449501c83c0d01251250301e07554810400750421020013080343d0b03100e0038400d940f41c0c880010640298913080304800718201c04030310012107400403000d80850114585040320001c2c50b040c40500405542103000480c8a0603103e500c0300340b226902c031425481618200007221108240240310101c0c010804049100c11010498030343c02e031143c2040c0264101000da1044502455030014954802d0b070040503030894011399140641d02c0100e000348030741400354091000744e8000f844000c0995089001281040c0450514652520010b204803614405680d000400c0c24510002c181e001c180001811701014100307001e0100a001c003800c0c804070901007190010011100240700d005a04094880101005840c466580080200030f101500641c01084004d00038807400e601180840d5000700a14000c1c205000800e10464030703410b203e981d0f285102070200f070540c4000d00003903000d080b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 379088084 1250 379086834 379086847
    0x9030d08040b01230418170a02280b010605030f01050a14010f0210050c13210f2109170606011d0f130203040b0703020f0702043b0114040b07030c05 65
    0x55500c51b03c00c4145d101801c9031007481c41414508007422000d00000101001041404012500000c4422031400c03400890030b407040c003000d0088078102d8050b40090a0359400000046c0466110001d1400342241c20508a0603980e5038042101000182c448d4513240344060340c0d000d8156010791038801100001e80141c0d5000581e40c6180d108031841100e9511422001013100e02000341e0341c0310b048024012141003285204001400b0110384400002c000740501d6040000703804102c1d0b254030100e84e0400c0d6260140c0603111001010302400304d02c0c0540e460030001c8200c140408032000070500e0242030180c40300c0c0001500001c40c6003c0c01c2e81c10f800d80340c000c40b5400c884a025120b0a17140750000c10124001a241c0c1854a014020001c02178204000c01d4010711040c021408010216100c050341260001088003800c1a402c5070005045200700550107448500c1c11046260b8070390500e0364004000810614140703038116aa01c1c181a20301429403440381c0b0006d1200b0340203601036601c0b0011070400343d08085 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 379089334 1250 379088084 379088089
    0xa020c070609060f0309050604021c080a09090c020102070309360c03062925030c03141201030602070201020c0d1202060f0f070315080f0309030d08040b0123 69
    0x8181e91062000a84440c0e0030040194000c0302d01140892a142c2408095015110190b8910024001a110b1001c035622440c03402d0740998900c21303c0340c2c04004a078032004086005082c0054030700c6660005401d0000c20a40148107100b160401c1d039242d100d0000c0c0c03909103d45440038110890f88204000c03141002c800020300e8a80800c0d01c03914001002040f0b1030811903008040c0c9506505c904071010640b030004441003a845000304607600741d10045516074510110000980040b500c203506600c255030b08003400c1c10f0340044000041070181d280c0c0040034012540c100000d00c100e240100000450f440188002200341d00105415401441251300d40461100020788101501c48200c07a01403813403a100d40450380501c003031584410300120400c6685010310641c81c190400a29450806a482c0c0c04d21004184c0400940050303d0000121422942c036074031015030380d41c042408180f007031144d0b88240758035038407941d01548a2075011060070201c0e4070303185401c2c1d001c00142c40789000350850304050007000c2c3c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 379090584 1250 379089334 379089343
    0x2509021204020a0b041505031f030f020405090d0212180901260109080904090218070c050106050f06120703061208090111150105010f090b030901020406020d0e0d08030a020c 76
    0x14006980209501e040510410032080541c0d8000c003564103051000300000c1c401501c03c01c42c10400e50400c140c0d42c1da0348501802c180008450383c6145441c000f140071050100807219141164070070b440400060f1a20343c103403a515954001d800d00164170908460040120a0000e000c4840440469040420a1800250300010243c100500400c41110154508080c0c0a0014030106d160030013000720307002030340390364840344240c04945001d25145c2180e0300840d03d94603100600d04507c454015420300f070003a07000304620303080c420560b150360030880041010311f442c1e140194080c000500082c608101400300a07010b160061505003410766500700001c0e0444198845000c00788514200c1e0346d2100803130000340840400b003900aa05070b00080c10900444103402001d41074a1090a2103001c1c01d030b111008545100076500140c001001c0842401076250054000e001955410703003e8803a10041200100d8925411041c4140c0c8641c5401c5c06601180c50701d002185c0140402c40301501d00090848242d00e003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 379091834 1250 379090584 379090597
    0x1050105072301051b07110409020f04050103060c021b0607060e07080609070f06020c010905041116050106030614040c0e1005120601052b08090d020913020a06030905250902 76
    0x780d441e0005c0055840800340700400740300340c10b5070040c240340d440d84070346400211400e00d0b640555a9800050b003595a085901000b82c01d0003401400190385074038003c000307420720842d008051710030846020b0140b031030500b481c60782000c040c0485040400703940742c1c0000752007100c0001e40715014200000c14008414059507216142e80401441902d00d00340c0c481140d10360980c0903008542048641c0340d12607074406440403c45404036400f00e070120b80144180224410028490400c040019101040107010340103603080b41d01a000070041e03a040203038413420b10742040781c0041840b10241d100740692045540c5e4150070000d440603400946441d4808105c0c2c140e900100c000c40c0f507001d000100300300e01d06102c0c01c911000240101200480007004486540c02c52401e0007806050040780328101503d90078081480c1c0c0f40c0003000541c0340e090003920030040380300b00e0100f0790045500c02008540c1364000e02417400c00d1540200106a501007405050102e01500359030500d05006401d0002107030031150014020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 379093084 1250 379091834 379091903
    0x70809030a14070b0a120c0203190c05010b0123031506030c03040c0506090a1217160506130b0402092e06020f0a0f0305070611070602070203100e060105010507 70
    0x80d07001c102c01c0700c03600c1c1101c90b5000c011150420481c13140345991121045031140c0c5064808a00442c004200303900714014820315108100c4040203503039405904c9601103003100d000d80020443c940d00d140044aa440c402e03180241c10013140f0045125100b0075100850b0b0080a0f030191001c056021000074080c3e5005580e60b0301ca1100100602c014010980c40785001002e04851003840e1606d0007000c5141d400c414809d41ca05051f0440050080c45425140b10301700300181c100f184d6891828188056841c4280d500540d410301c9180009040848100319000d0340540014500660ba030300d0342d0070080a0700c030040801c2c0000920711000e21500034510003d401d5522081420541c850030120020f20340400e4000028031580001d1101d070224001c0e0942d0014250176143c00740d5501e4150a11001609500c0c1615200351800512039040c4541076010f00012482241980c070f440300c15802c2c1f101924000348001d001074208000401207980114002c14080b071003065174840b48002180d0008064504007408070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 379094334 1250 379093084 379093103
    0xb040b090a1217100302150d0204080d0c1b05060f03071b030906030c05030402100302030c0c0304030c090f0203061e0f04020316170f070309031101090f0308090304050d08070809030a 80
    0x11038100b00c1d0f9015940c84140f98000315521403440c0c00141185099042d59010301d0000603d441504032640c0445001d440c1c14811a50034201c1c00d10010b103607101025007500c00c0160640c10720a40c00c041c4c2c05610450301d00804083c03d05800240040c80c503400940804c0620070046000700041c607201c52201c00fa60300a0f1154080a4074010028041c2e40001d4082000c00c0b1040041100507600d881030224055414900180ca984d55078406281ca0f12840071300e020380b8403000c10000108414110312200380c3e010608203000c524506401c400980c0429180301e0b92040395020700011a80403101000b44138000281045c216003800d0000c902203910540340d20f001e2048200100302c1040d0071010101420b6000a46a0401c1c82c04001d05003068002a14840c1003640740c0c0b04801c00d00d403182c650400d02d40c91040003001002e44900d4a00014220303110f040300407034503c0300010003560010095a04458020b03001c05036006482d900d1341d80c0c0341c0c06424100e40b1402c05200c40381094504100d00b4004602c24071122 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 379095584 1250 379094334 379094357
    0xb0a031e05120c1506220911091603090503131805070f02030703111c11061b1c0905031201140f0d0201180e150a080a0b040b090a12 58
    0x280c14280c2a80030b421000004100c0c4a00951000400c0e48003051542a21003098072800005600c01d009051800640d0000b20709070102104c0a03408448104e00c2102800c02c0e0401e0710741800700403481107481185026240418101240c000d8126042d01c91040055914111450b684240c1146940d04030000d14074038860341c01d2070510588101e03500101c0d030303050080d80748a0a80c802175503445980340040400c80048414500460b0801580505003020305405029110510009080c0c00c4000d495050390301ca10408100c0c801c9071304500e000000c8001e890645040c0d40c01c90003113102001003004910081e40c4100c0403010403000d0018044501a180850f041549404c02039200d0b070b42c9a10707140d4810f80036000f1040f0990303070700780012505590a0a080307082010718580c4505403a07880e8000100408494200802144444039004030f1003011100105202d48590101d5a49c02000354014100f03800080492301152a005182e50701540709021100b01c015145d5510040d66822044040404e00f190040d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 379096834 1250 379095584 379095593
    0x90f0311120f070501200415020a02031e1b0303040915170109020307090b0306010303080606070f03181205071202060d02040f060305060f0117130506011d011a0703030b0a031e 77
    0x1403244041100040044e0300c0728035501c0c80114410343c41001c0004955210640c6420b000344050ac1c0b000c3c0e00101502d240110b00300154050512008901903d8007d107603a00b040421420a007251720880500258203180c100340b240c2e4010311744c5402c000b41c0f400081e1130000d490555080d14012550019001144d4600d02d407040c5854078955410246589050540b10a11514005040c604598041c5882000c540b10030000c05d0641c4a1000f024004042d040082070074160001110b0684c1540d810310071a0003a030b10420b55031160711078403008006410451082051282c0f2007818050b0341d000410191a0400c03840e000005c82c0d2141c0c0c060890410518410400c8035014803030107600c4907040c0c1c2d40840c4003120100007400801c0e040d051130803961100d40415210740c1c1840388180c20a90000031180c955840d10003106004044c0402c030005024100c00200d40b2180c99070800d80c140201d10300c1142080101c0c2e4040c0d0103800c0e0901400d400c1010141b001001c2240c015621042c1d000d241004058044075080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 379098084 1250 379096834 379096841
    0x40b010c08030405150c040303050703054006020a02060d3305040f02040b0313030e03120c2407050d0906020315040b0a0501200a081209010c03090f0311120f070501 72
    0x84c21b005414001040401c0d000011034850700c3c2d00d450160765446090481c00070000329a18092480d039241c0a180075042881d4590800d88424100010100342c0d80b0380c012a6903860720340c0c0007900882c00b40001c114010b826089000384131005021801c1100c40b100f4580600040e00102900c03241c0d00401c200714130b003420300c81c0340c402e0900340006525013800e100c6215070030322001d008100c1016100010a00f854415003c0010614000381991242c03d907a5241c01016008a08050310a016050310406901c0400c0c2c19282d00e04040b0100c80d0803991810410341c0c142d040106540322503a29180ba22001a4003031008600c503990448520352500003010501084034003148110340210700410040c004d0b43e0300030960307810408801011080e0100f00610947c20442d81040003410204081a607469100500311130070310440c200c400800c04096007404c2101640c0d0002005040203d80b0b0b1080004a840f540080c07000300c080c01c00b228983c0c810a0300f45d00060b4449045d0521014000c50a0410442c0a02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 379099334 1250 379098084 379098091
    0x510020c030409150e070807120c09030b0f010e06101e0804030f020109050714030115090920010507020405070201141f0e010e0c1b0102030f0a0506040c0c02040b010c0803040515 78
    0x140c007251300d5030030011080c201500181000d401c2c000500e0010b007a0511035001507042d1880c00d1028404140740c0403000c1e21508050008445040581e4002018a80d1544509048580008546c041611050244000390820207442401c01002d501011180b51440d03903c2c0301d42d51008d642d2031210b071402c0e0800030402410145514116418854164081800010948203a8504032520b050030340ea4000020700401580e5101c41c884290302c240002e05aa0a070310142c01c42d40580001e4141c40320b0350750506050001d5800d8540418801e0240a02500f031903030080c4d500c0501400000380d00c0000700030380750351440110f03074440d94000e0301458485143e09080c603a00040c20114001d40895040030b91400c190ac000805400840348041001e05201880b00c00c0100700c408590300031503403803d0404100c51180ba0881b0424000c90a180200c3c01c1403e01d44581400400c0c40e55441424261650030040138140baa03030070740e0400c000106280042040302e401180654807440040040000d80f4050740d100d810000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 379100584 1250 379099334 379099361
    0x3010303031b09170304051509030105071119080f070606090f0e060c090402041d15010c0209060d0510110306030606010c0c030b04051011070507050a1d040510020c030409 75
    0xb811020400303810415043c1540ca015800d208030340d108180e407038514040c0c0d07445140d104506200111101c54141c005003003840e02070b0700910a580e91400c040d44c00007012600d0b210031b5409110b02c64001e40d407507523031805024480c0d80c0c0c5a140401e1110007400507000b6800039110f503556020200040426449024180742c1540c4003440119541441c031615050001c101c01712034240050480056581c0ea41101e018080f078001c40c6141c0c05071620194100706040361500c1100348900d1400303407590302518122003100d900600081030b50750707201305001c1b100b000396404503414400c2c0355001c0c80b400c80901032020210040c010b035946a1625504040c82c0c0b0b10302900c45d038103100c00c0f59140004200445000c405030307604184811242d44030b510308540380658eda50408405403500000c100b0810800c0014020766003d4800c681e42262101c04000d0190040e1007444036032402064840091052290442d6003d80070f8001c1d210742c06101000c01c01aa400701240c071840d5080081c080c40300030003d12801e02007400302e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 379101834 1250 379100584 379100621
    0xa0f0f23060f010509060c0729280309080a020c011803020108040b1f0e01051003110313050102040b13150f02060a090609210e091009090302030d050c0301030303 71
    0x10049516408450b482c070b8108240010602c0300c84d10f50340100c549107005107040781c03d00ca03aa1082c501c3c502d40003111080d01c008141c10305440800c040d03c1038518002010142070007c03400c0420010009102c8006502456141c1c042030010940c000040d00c281392140c2c0182c5000b916240004110134100b19485506070f81d802c509202503684052041d50250340302010b1561501d50106d060b020580c0303100c1680c0c0440500b00042075080548168604035002903c0a00308101807850540a5840b240c0060f1281e160600014041c801741d0100080902d0190000500e4035443d95001e003459440040c0e1018048000c040030050072031502c0c00702d0610f101625081c3d05641881030000d40795180a0500700b515500d611015050007815030104242e00c0e413100f281d45001c1d501441c050048801e5030f00340c0d000310f2010450003030942030848034a486003104200c82c9003424100362006008003881c0c0380a5085100030307c0010002120740c0705042c012012850752507202e61662600805580c808852a80c40105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 379103084 1250 379101834 379101841
    0x17180a0b0a15080c090705071401020409110306182706060f0109060507060902060909090f0d020a0f020d0809090106030b040605060702011205190c0e18090709050a0f0f23 75
    0x810100139491084410b071002d07844d040c0d421950b80c080d1080207400705003002900c80b0f000c601580148102c03441848144419030b41149034443d85d0000b00ca413550020310010035812185010701a441e802142865406031415940109400318120104032030940e5100790180030041c41c03c034000d460307181000d01c0c14181e2141400801002801000720042c005516070a0328800c40da0b866003501c28005024059240d1841d01c080341d5a52542044504440380c0105d074004c0c900c1e5840030840f100e0881d04502c41c22880708896080c49501c0c0c0d1b00300002e403440202440075030801e580b8180e000740280480d40e00810320000306002c0104852082d44213502c144c0d010091440140d800c00b0060341c4c0300c0380c0d88400107440c0e9982c440041000131071b10b4080c0503580c41c10029401e007a400c5404010020360644041150241c0b1200d01d1140c880181c4000744a9407001000b00301c0041c603a0007950b404a190b40011407406c4141001d802510b4000f20310343c0056071a0054010254142e2058110710386102000154604 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 379104334 1250 379103084 379103099
    0x703140607020304120807080c0312010e07090e06060408060c030a11040f060c0c090c03090b010506030f0c070507050d0308070e010815010e0d081909080604020117180a0b0a15 77
    0x4c264403441c004211402d0b580c409020100c016520110f81110440b0354440015072460b8807039110f201e070b0941d40c444840c000300d04140c0c01c0c10301a1150f019038580040076400c0c20558a01d408005104940c49030f01000302148074076060090030f0082600c0750301c240c2c176400c002c9807520503140881da542e0189275081c40208817110000d00050126051800c18a03100191030418084642c015000b8030349032030400d166102c00070350541c0001c1401e800341300110196602c520420406102c281c0300d0001e81401440403071445203502d401440c40c0c0d440f4500711440b10780d80340c000c100034186420080d00420210300402000a0308030781070807130202003443c1415252400560002070344000c80b180b1410810303010a21180c9841e4052f4210301940c00500054442c0d408480400b440850074a002000902c524000034136000000780c0359025640c143c4641400100010559103d140010115038812552030b5010700b15203000c0c00300d026502d0107000c00050614118052000f41d413009a0622411908000c0400050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 379105584 1250 379104334 379104337
    0xe121507080402030a050111030a06060e15030916030308190903020a0b070905130c09050a060c0602031506030a0608010b030d050d050c2203050c0607080307030c11010e07031406070203 81
    0xe409801c020315992a6400840c0c602070284400406a610340040e00c40c0a50304540618030a104030401882400e071601011515004950300490b04804050309507040d21400ba800385a001d07904104444142c0070708a10034024041d507500036404900c0290a10200c1c600c6160728045101d950601803003102c04590f4020740d51710320040042c080032010404a179a442c1b048030398034010100100542001903580d203e40004220821420010920300030300080c803030038000142400c40e0b2041d1100c0c00510b003591920400313548001c4c112103401030380c2c0f81c04030340359526030303000d540101800f6600203401c50030114881e085444400c2c845120b030340f081030f24047c4954098101c0e0744024031250085a161103810464005004078108140101803a900b0f075284003900c00c0c2040200e90060045410400550301400f2403803051800250941d0ae0401c001034080d80650041214541c5c0c62030880a12810050400d0071203c0511146580d608400001c2041c48a20600c0b01e80c025036a0000d403a0390b00b801000a0360301d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 379106834 1250 379105584 379105591
    0xa05090309041109040608061f180c050d06170c15090d02040905120309070605040f060e0f040e010f0e010203070c03180b030106120e0705031f0e0d0e1215 68
    0x1c40d2140c040c5102e00c41c000007071381c1500e2406407041c007166440b0313010182c503140701b2107081068440c10721900c1860806c064030841100d400400742a0030001d04c0110f02c2c05440f03603100742803d00000300414240000ca6203c0c0074020034008801c11903030640e10102a040401207400d1a12580c11200d020350302c2c00002c412144000f0303044601c10350000c8a48085400307081000400341440c09640340c40c4404040c0c1070000c61180c2450b006940707591f41c031204203480600550003a5081200710040601c0740c40c3c0980c410095003400103004d103030620070284c00582030300c014003a00c03880c2c3e945401946000c5e4016000c0c1d0841d50801100035800c5281a01b8010042c0302e0140000c1e0400040300c010318503030002c6400142c054050444076980d20341c0c40300000780a00102c1c000d81490107290403000e01c21180b021440c241030b03a0009003d002e1440300070145d00032602c0c0e1041c00f9514a607460091245010007040b0b0b566030706506440f40c100c000b10110800c038480110300701c107005c1500300c40911807a004084000b01d50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 379108084 1250 379106834 379106839
    0xf0601120605060d02250807120207141003020912030a020f010911150705010509150108060f0a020c01020903190c061115041106030a05010e01080f030409090807020a0e010e0a05090309 81
    0x2100c1034240b1480020140c0343c9100e80f000c01080c41b501007440f00100040150f070b801000c40c02d050142c0018100c0e52152140300e10329558003001700788881032916a00e8400480107a14000d41011080d0000520807001070040c0191644001041d01030682c06121403825002c40d440204800b01c01c5448074940000844003440c815040403064a80300c100b91001e0301c908035000402002245000f503020f03076a4650381d40e00785080440c42c07000090302c4400000c655110705440b9500080649440304c20700d0180d04417041000095400380074400d03180d1030401c4030110911b08290500000d000071305203414000300c1030b00800100a2042d004407d0b207000020744070014158641000403560341c0341002400c440f540e41829600c07050000a004880700b06130403030742c142c030858100d140d401d0740d84031b0180340e8440c520701c0f04d0079483e001404200020026648103a54040c01900d14900d07058882d40043c046840d603403c0907001480c1800144a4003107a91811580125241c0701009141022242941d59016031401180f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 379109334 1250 379108084 379108087
    0x131d09250515160b040507090c02031204020f15030a0f0204050a030803092a0907050910081005040e0d032f07060b09090703031101021201050108071103030f0601120605060d02 77
    0x2c10300d41803075044030b140d07403000310269200341c00074035040305285000d40e010396041c45298000700b000b021521816444900a03001141341440b4050301e8040400028800d0b0307440482c8102c11005074a0f04410b041060880c20302940ea24640150410200d6140c2c854020a03e44140003e0105842e100350b8582901e8101e11b00300d0722540c440490900d08060001d9a00e13400c0c0c3d514001703601002c920707101e0b07031030340901213808039400d948281e4100c5050091068240d406600342c0b0051500c2130085c007003140c00c0141c4208200e070a40e110b40c003060680d07140550403416540034103445180550300d48100e84c42e00c0d1034035801e4180d19400300b200c11035000115002c55074400000400301c0030410903a00408881c1e5024004440f20319000080716210070140c481580401c80c1f40c02d05c1d0481e00010700c00c542d1203a0080d25902001d900b400c00440705444000d025800340014180300d903842020400103544202a24070980c2098074105000510b402154102c0505903030401805008940c7d4071002d90361140f840b0754005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 379110584 1250 379109334 379109359
    0x5130807082206050703032f07020414100e01060905100e03010209130614190905061207090c110f0607030c0507060f24080601050402131d092505 64
    0x98404000202c601400800110740064030315081005400214000d03201041754919122440382e4a011010414102003004402c00300500c0f03000340500086400030304001341c0150340174444075510700161095400f100380300c8400c010864945001c82d000d40800d01e4140906887c1c0404280c543c0103001c2803c007800b41d01d04201202e5113003541900d52a4030018104180c0310342d4200c9401c000c2105000d105543c0ca0210342941d412304003c520107813002d02c2085c40d522842e1030b01e40c000004200c0075000d6607011903c010386a04004003000310f140070740071a801c0010403a8448070083e1200017440501c903860740001041c52990000810030035804001c508001c1680c481454044a141c0700b0a000200340d5441d1420800c140b64640d070202207401c81e445003000c02c3c5e0040304c504000028052060b80c10940c419401072106040640140440b00600d91f510411240c441c04c45d110180c0803c0c3d22b20701080343c0c0100b00702c00e504041020300e182ca2001036006000300070480e081070000c0e62a0042600481403c2002c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 379111834 1250 379110584 379110607
    0xa081207170f091b01050702090405160803091e09040201030902060405151305030106080303070c02013b010912030c051606021b060f0313050a05030309010e010513080708 75
    0x4041c05014905092031034504414010780c192802d695010306803042c0c5040c4030002e80300740040488050161281424540c1c2d0b9400c115000744000c0c0202c4648c020100441c01c02c22030610610b010744402c50184d40c071040406c0520540504a00285210121150030340280c0d40703406001c5070b002034081c600400c20322128000308040b8841d42c5e014070341002001c1c404001c0b05041c00054240d0310140102d03400c01c0c1d65900d0806081c0ea00c80e008000e0039030010000706aa642c080d502e003a030303014810305015550800c00e036041d800c401c0018101405444909072800001150b040764500210303801d0824105060402040e400b5a01c45200d008060044200450b42801010002407401058400d00c4a50705611510029211a40d40c4509024903c034202401c1032807404c1410f41e20b070201078804150941e685da04403980c510810761b000790380c035018048114005c00c20500003180300b18108400400e002200242a5084030f0008041e45000c0340e02d00a56400501b11008444449811400107912502900781 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 379113084 1250 379111834 379111847
    0x8010b220203101a040812070506010b0d0f09030509030d081b090102100207050f1c020c0402070213050130020618180103030c0b0106081302151c05010305010b01020a081207 76
    0x400e55031340c406140883c0c40d0760034004205944039071055861200c0340241103041c902412200901d07903044a00103114556058024145058000e5404103200302220a640f08807100054107030005540041d140c9207501b800c1201040301051440d2040c2c581c43c081d08102e100083d8a010703001c0c8030351300080c4690581c0c801c2158054070980034004566854032403519a03529032400e0440c10300c90107001c0d000c521581401c000d6541c1c180311500901010005001008000c0d40003c6040f82c0c0301e164450041412001d502c107007400382801308207207041a0300c0c6280202d410343c3c880200075031407141aa203050040e1500c5060780d480e10281d04c0c480c12103d0407040014242203442c0b00030300d000c00042c8000001c0c19401400380007824003503102c110560b62500000c4416030b0301140c0801100074030184130710060402c801849500000c0c001340a0401043c00c4012100032200004894903584803070050003800028461010395000074001040300305482d81d9504110b008420703504511101150000701102d000c0d05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 379114334 1250 379113084 379113089
    0xb030702070f18050f040309030b070504180506040f020a0e1e0306070c12110a03081b0c0309030c0315040b09070b070302060a060e070e040504080408010e0708010b22020310 76
    0x140b440b926455002405601851040300c8000c1c1303051402003144415900712981c011600343d643c0000306c1e03003503446a07061040080d00101c20402c0811001440d410040310200c0303429030f030100108443c24a0002c00c000d8601c20440801e03140d104002c2003002d2a041410900c6c0c000041d1103101d602c268142070f1080140788821195090b000300c81c101f0402690058004030f58910418881520010f280c4089600c0040070a00003001d9018841c0f01011038043d00100d41e00824442c81600308000c107030f01143c0c1f507401803d1600425400402c2525180ca42448000b1034450150010004007201902c010301038134001c0e1000d440303035802e403010a10981041c000d00c0003504107007155959590052174001c1d1398030401c6070202c1d001803400340046250700110720301c0390152032503a5030740610800100400004050150041b5545581004000758401d02801150398411170000030388600341c42d24070001e01759180c60001e20b108040083c001c24180008402c00c1103e1038280c04c0050320f940c0c42d105414454000e98 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 379115584 1250 379114334 379114349
    0xc010f2309151c050411061602040612050705090403020c011110060b070b0f0402090a0e0703020901081608010e07090903031e0b12070506070b1015020a03030e03130b03070207 77
    0x40c0303001041140300000400624407602c081000490300940348404456054400501d41042c100b081041c6c0d140900151104003060107240c1c409055170340c0083d040b1601036000340e280c803041070040c0003805818042200103140544021605260698009480d1002410080e0501c00803145045404c0005c004035450040d131404204007040d105d000c001c038990040241242c400315500005110f01c030b400340f800fa000303c2d800f030014007441e180c0d2000040038000c0100001c5c614800d0080020150340c6802940b402001020301030104410300050005400c2110707000324003580e041c6096041a441d00046400032200c0c61940001c030010281740032009442201d6040d41c255100c038052a140b000b496101c507074102c004803070ba0715801015421594070f80b0028810b059200f5014000c58001c2004d030700769280d10600301c0e40e500013103a858800207580d041072000f010380107a01c101100d4042542500c110040001050021760070101f2a00c11103203104058000c002c0c2490010003c07901c46402001084090301e0316 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 379116834 1250 379115584 379115599
    0x1030803061309030206150d0206030a0b04180b04080d020c010507091412030f031003050a0303020d050f040203101d10020d0501090c090b13030f12020c010f2309 71
    0x1241440401508140c5419201d150303040081e814040b0303103105036200103605401419503540d5201c000341c42c61000404080e08440c0664420006a8985008504c81d00b08410f00242070f400000500c400ca41607000820107640b461a8500d01040c0200400c561160740701c8840c550361441442604040d010b1b25054200310340c200000d000005030000546c0040da026503200498610700c9804000d83c6060f2200740d142e50380c00803c001d06818107041e005551001d5440030948080355281e0780c852a0290000003600003030341c0803c100340e0702c166501031550402c0c0300040484113400e141e0000b9840700c1d2801004a03500d59a01030028640c00410703100c80c1c000c210366003030343d90480c0b00703d0103200650711940c480e100d02031a0030000f044940491148800c03060703103039552815540c10000749407070640c44810006822820f8000000000d01400b50f040c08040c883c44000c40c00014100c406071400341c3c800701407810700284505888055500c0070006210950180a05c803900244011040c0b0a200348030280e90052036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 379118084 1250 379116834 379116839
    0x601050702060408010e16062f03030f041e02130b0102010b19180204150f03060509071d09071d011b0b010f080718090201020115031101030b061206011107090501 71
    0x203040d80f2a0000e030703401c03006691400000030500c000304000c87c0200b0000c9228903403000485c0d0144400ea03984d9004c052711171385c0c1e441c0604000783e146410855189041c3c8000808000c208111204d0896a046050380203035003103aa50b44c001070401c0030000c2454045691610340400c0d9078400d41012107107910241c50a15412030440841e044100a4003131b00c0c40225540c01c0901e020304d0b036072084600701ca564060b200f09042000e072080303462040342c11041e410191280b40c0440c5503030755410703418050000e40d11103a400b0409050700510038131100074135a00c1070341c000c0c0400c541d090300103c40680800a8603250b15028072a0f00041e230b0400b1140000080d0051011002c0c401c10900c244406e0507244040d8080f030b480c541d22006240e4034881c82c02850701d0700d82d4481d80804520855000b0003c1c0d28414000856418804003280c80d0448dc594020303070300360601c4640080c081d40c062080144541066030910310303080c10100310040b85100902858108412040c020408190601c04400680201e982c140015603 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 379119334 1250 379118084 379118099
    0x1140d021e01030b06090306011202150a050307030c050726070c1202120f12340b010603060b0316140a0305090c0126060a0909030203030108070609120b06010507020604 74
    0x911041050340444c1c40e041d88411145084c00c1034540341000100149102d030300b04480b82d070a5815080b03049800200e068065031000700b1420140c1007014030f550340c05440b0314000100a05484011a0900600104200c51008a4810702c848591400500c60511155403c100030301154400c400020b00503000f09075010556035070031031303004860354001c64410f80700052104015880f0400318014281980c86510038403104510360780078100d01600301a41000003146a42c03400d48940d18585113564440341715038048100207150304110701500f6103150802c0200d0403e02269000d10010702a010f41d107480404400c9614031400d5842c007000b022002c0c0b940c8801c09c828021740685800d8501802c2801070048514007544142e1000d021a80d4400310405551603100345420900c8000e421550004600440407441e03e00754042d0640d05403080d0b004550b0303589001d0411342402c0785074102808100c4410310801c00070310320480303161041e5000043c6104a880b4031006036218800c03003400030b420510100c0c0028000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 379120584 1250 379119334 379119379
    0x110f010207060902120f0d0e0102070f0b0705010c0503151915050714030f030610020f16030b15030304170106050a03080d0507140a030e03040503060a0606110d02030301140d02 77
    0x861080e01d211801700310040e00a52141e039500e1411403150700600315100d51501c503440c03c690012041c016038440c01e884584918030907090340c00a1505800000d0000200f01091161410004052a12604505154094200350001c00c001c6a1284086410001480800c0d4104000030800d02584180314808000050156000346005903880c01c1c1040c1042da00c2e8001000b101c03103a45440021900e0355644408010085108640800841c89101c0d641d27560382d40c08120ba0041503800b01500000c003403561800c0d0032102c00c0102040c0c5c3c05184024425050748000040e40c09132800306403503009890651550030300500155005036445080704100100340400b200c01840c401d4101c2505000654a840d02175620050031615103820000130069100030f184070b64030807200b48030b200b001d49107003941d41c00c000f91030000290341d200c005c0303603550004010f0542c109012003400b09040300501011420201701035100e0005118041640c041c0703807100301c040d50741c0700300708811154000c00e11904c40c41c890003d250303070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 379121834 1250 379120584 379120601
    0x5012702220f08060606030a111225020c06161a040f0210032a0c06020315010306332609010b01050903070308070f0b010608060a090912110f01020706 66
    0xb41d0025200410032203000f1401610803440030380b0031440c0d911046030000040035050740b1003d02701c502b400034111030f0651140f200d016280394009001901055400d0500c0000058000303010355000d41c0140b1044d8980200b59082501420f1001d00c6004a81c105030101102469011108004940c10001000f11501d036184005000f81d41a1986404950082c4e08503410010740c2e0007200303582c404040d503401ca088501c1c2da083d20145000b2412104983d03d01069810540d0309107120071070628a0242568035208120003001403a010108603162290f100300c02d440e1400c1101500261800d01d10342e8140a8903005214101110f40d08485900c1c22003030380c2001500382c0c1c10b03410382d5081582c801041d42c420001d4410030344008001c0d204c0070b8070f10b6440c0a2640d10031002100e150b54095807010100300701315007950080180383c451000a140c808200201540720744c10540c1c42c0c5150540302400b1450301d07000c03841c0c5408141003840055060080303c514114070110000341ca0342c000a09807040042c04e4201204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 379123084 1250 379121834 379121849
    0xd020301090b010b12010b040e040f05010b03030f0c06070512150406050a06080702150115050d090c0b0711030114060f010c020a081f0204140112150909030e040501270222 75
    0x18147d0b01d422a0400d5032165205030700d002c1c0007030008200401c04035401c40b008203214500020760440c01401107070864000b8824502d20a20216001c8000082400190360144d0340b8544a45031a6002610720342c070712f8000c0d0a070b1503c041c980c0f0700e0f0309007500d40368005406800c0c005e006952171540c4403402001c100301181c052005004010603248161130118249041ea0829000f080102d101c40070100c034a0303004901a007040d56180c15012012500b40c00d010f0b009448400c00d0b455845a1034101882200b0030740e00441d0090389440c0343e1154580303000610a4011204481e50400d2183c4040101c0c0c000c6020ba80195002039590400211410000f81c51007039641840c0c1c020300745c07248140340395049020300e1091b909659100e41d0180c19540c402c00500c4403003409001e001503165102499800b1101c642d80000c11b2640c0e0b100703101814150001c4070407d981c0011903082c0500d42c10144012104042988a140880682e102103880800b4a40650f40c0a83c9109001351641555030340301e0031a02e440c0e01c510b80303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 379124334 1250 379123084 379123117
    0x50c010e10020c0f0a0210031127100504260f060a1d0c0a17190812010b090d0204052205060402010813080909060406090c0c1502040807050d020301090b010b 69
    0xa072100204030749003400d4009080d0750303440d0350001050307000c0c16892728803441004e42085045503980700e02900b0490300c00e400743d0400300484481d040c440d14060031300000341401003c0c0410007400202c5006107c0358400744131306100d20103222110314034010304110340c01c2c0b041c0104030401a4000241c2d1000f651016030a00c43c0314409040d40c0580e855583c9490b0041d0801e01c0007800b4001c40000d18410348800400204941c1860703031000c540010082e403a1000c5a0741440059040d0741d00500307620743c0380946040e4026130b00d0b0084140c009140c0d0311025200034043d50715140041c0d6180300402e40d40d921207c1c010096004070b24180b4015488100c2102c049000c65101c0c004240b401c8c545140041c2c3c5203520070316240c40d1a00b184100300e080340e8001d00140c1e00981b1160f021071450300c42e000d825560749950b00c6200001a40d40360030425580c2030584009075501c103001c00c01860b90005208030460340107a41c0301c25036007403d001213405020310040c0901071000c10000000c9a00c018802040d85071503180044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 379125584 1250 379124334 379124353
    0x10060e04111c060b090108150a030b18061510030c050f04172104090b060f120a0501060e030c010302030c04050307030f030e0a031a07022107060b0f0a06050c010e10020c 74
    0x403101e50045e03100c0580010183c20000b0240385c42c8488010040e48020300c0300f048543d40342c0d605c11b44c0741011550b101103000240140044088100300458214a0488141140005810118010034880c5080c0d50402d922801e1105c0041d001d9002c85e00301192101480f43e4803030b20384042d52094207441d00d040010384074a15108203d0803040c417800b012194005c42e007600d014501121030014002c1000c0c10b81e48124100714140e00602d00e40c00800b1880d006450701e03281c0d490108000c108481059110380280f2481c2c40c881d84107554037048081d4104800d007030041e103a44401103a0503c60145800043d0184117640c8080140511070110b14001d5101e99162140c13003d900051100074246448000c0100900d0942503c1e116080792186600c00058030440e468840400030560003420015650158031000044038814007416000c1c00b05403100035a100042c00c4c030f900c2c01044072454980b14040401801183da07a20352039083d00a000c004843d01c0031124800030aa4100c1c0003580b08410500c524030901501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 379126834 1250 379125584 379125599
    0xf041508030c0c15070b0103081809190c020d0203030c1606090f02091b03010b0307180e011415040504020a090e0103150b0d05100e011d0703140610060e04111c06 71
    0xb111700f8642e201d4400c100d00e9185945280103500103241480d841c42d081030303c0d81e030385440d49101079208804c44900d100900d20b41190344000c50301c034a0442400c40d0080c0840340302082d0001300b00c0707800600c00701c21240d0762a202a4405000030701c040008000c1420300e00440c051100c2044c0082c040d41c002c54500c542074940480710311002825a041215002e4140010001640e402c0080d503480702c51401d00040e082d2070180ba011600543e0741010031110400700041c011180d42d6200e002e00b502007660301c2d050101c000c651821003406280b0885100e42e400140c1c01214500c02c07c0b000004000e0000c0340389855031a8a01218420a0042c601c0c035030301d00d80b40a110f0303580740c119040d00c0c00b540c000003c3c09140c00d96034481d00c0541401ca14170a159900c6503a203240c1c1d0b50300c80d240c100c5031003a80009008100c6c11441c001c1410a0503003900100380d03101c1c806100e003444c200941c1c0e80072200740742032500da814140004a400307032240f07042d482e8144e403011481c14a03c0201d0001e006855a1321041000a9a1600314 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 379128084 1250 379126834 379126837
    0x20d110705070b180d12080a0b130504140a03020f01270605060619090302090f09190f140c01020c01020f03040501032412140c0f041508030c0c15 64
    0x4003805542c4110350400100000d84010114055006964071450301410046007102c04601c600b01c403030851092070280880d074002c010301c1e0406c80c1c44000f4802d030429400000d4003c203985500c2d040c1e15565070082001c12103681c000301210641c0741d00303541e550581fa0030040d40754241c0200f40036443d400c0c003016100343c51211b01e0001440e08030032807050340b48400e5251600204801881140c100c4000c101c2c0710100d0a01719070074040187d8642d0342107407160840c0b050240805000d8800d8002d4036118090207841040441c0e04007140d6089004c0035840104e50500340f24248035020b010b0502039601c0180d0b1400d02c2e02140c900000e000c2030b0211840c0ba040040120780e6446c0e417043d04080ca030810300060103558032a0300a0740c0c00110400503a81c0c01d901019140c080c40311642d00c440d4151080c015104104a0714443e11300041c000007029040c440c0d1605d000c54948250014001c0c491079842e0440c501c80803d8800b61809420400704407502e600c110081c09690350401c84030395100f107101b5003030004030411100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 379129334 1250 379128084 379128097
    0x302040926131502070801060b04080106140913050a06020d06170715030207020a050312040314160e0405030c06070e0301060801051312020f0615100305070c02060a1b06020d11 77
    0x1c0081c4a6103032040e0240d0f006680142e020850044820001d02543d007400b81502030b1090880c003540c5e4502e002c03086821541300364001500003400b0300801c815a92140c0505a0000c80300040d41228191841c000303083c07201120005058520100780d694281d4540c0d404001940d0700c5170000700381c0d40220440255580308038411200071030364090042e1000d500c40e4018098262002d481841d0705074682000034108048040201101400840c0070402d100d0f030245410a681e104c14040c4c0104000b204060740016881e0207002d07200c44041000c20100581041144c01c44403840c000c4d6040c5080c0228010042500d68007074a10079824240003082c484070612440d4084c41c5500c81314400d11072184e41e50300411107032820a00560080c6809848a0b00c018407819102d03070592031038041c4860f8090b04015015415624003c2018039004c1003001007500845480080307030301151040c1d00ca0000c0c2c10b08841c1602d010002103400f9408070329901c100020780e006844070749004a001d001100665901040500808 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 379130584 1250 379129334 379129357
    0x105030c2808280e0a060e160506190c02060705010c0206010810020c1c0311030a090302330a06050d0b2401091e050603090a03020f0102040605220302040926 69
    0x42c91000f10407072141c1d020940c1c20781c0e0301c4281e801c40b082a0322407800b16602c0f404a0b90391b64110003030240d800c0101e02c0c0300601404007101c00c00d080807403080206083c03103101450041844030301101c4a065590b004141c0d0f6209078000000d101101200c4002510350000b846007024522030098400c01549540c000d8501c41500c64000b0a1340d02c0765582c0d0740006961806070401807556510741d4040da482a88001d43c81012055000300d800c1c1c0041c5030007481d0128040c411003624002d00800030040e05c038007802c0c4103260b880f50030761112a00c513130140b0401070400340d00056200d0a810a003008000c01240303024070820080316003412041c0c1511a817100b44078003015641c0000e262403000e01008654464691602a1103801d401d249611100413480941c810788142e0169404bd03908102050b9040100303801ea005014029030515103094800790150094891000e026840c1000c07210590b105110806c005580081007408510510304000c0d01c030803428009011590700340c1c180741c4c6038020360b00215190300401713 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 379131834 1250 379130584 379130641
    0x1306090b0a080c16260a1706150a030903080a050714032e0524031303020a0f2a080d1d0a0b270f0105030c2808 49
    0x1c0c1d80080710280001410a007030600144030040720315150301c001000d1035210b00104081010b1012603140e01c0110003000400d0b0b00340400c0118000c650290400e2429403020200f241282c07507540000d02e900d820f962049800c8000826240112541504602440c50181c2c440030640d0b2540c500d88015554219002030105519055940d400e01c00d10000b1a8414810817400440b810900560703400c04c03214201c0820050a0100103100f0f0349400d0b040c0c0d40404010203e980a0110103a00c442c0c01800010110031055181c80d4000c814903009001c08006558040f215100b82c1d20145081080090106240b800c03200078801e074010040c451350803103c00d032281080204540c90308100116081314401d204000350611005040481344c65420328100942080e0100e203440d1030140328200d21001c8107802d440c0190480701c120940ba92154110400360f01c000380b0f4000e80c1c9a403000f0043c181c034443c2643c60520104842c40d45041e00c1030060650b041300116aa0f130307402c0c80c3c03151024034048c0d012040c6200241c1c060b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 379133084 1250 379131834 379131847
    0x41406090604080a08190201020703091703070b010b0a02151e061309060f0b03070f050d03020102120915070305061c020109180b030f0d0f0305090109080409021306090b 74
    0x180400a04a10600100a5403405889a00103418440520011030304194042010380c201082a00f41100c64620380c0300841c10000700d62002004449540308001c04056285181d4640314030030b10842d443c40b90004036946e203d50303407001c035840954050381502006000c1e40d0707011141400800e0100340204840d0301c00b4034000710030388410885032401510143d8801038a0066000e981c4240c0100c0c59000c0c0510400a070b04da586000d4002500c100b06090762003a0420300043c030454041d802e02c40d080d598103540000080409160690083c81102050395100107503500700480c80341c000420b050396610f220114003854540940075401d655090360003c0c0d211154091402d0002ca40341c65078480d182c01458058081035039002c1584410245d598100007003515010071100c035040070030003150300320450401000790340c40c41c10300140362680c00b8903481d040584034400b06100d410250000300700150003a019503a56171b41d440d1450025800000c0900f40880180c2000450901130740b08a007c036580707410400e00d08003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 379134334 1250 379133084 379133089
    0x306060801062a0f0c0e0105060d0b1315080d030605060f180405071101110304080a08070e130c0f080903300a0509190203070501030c0c20040608030414 67
    0x403031044106020080c3d80d01100d1a503403505010380b1560300920b808440015281041d00024046030041a80100c107000104501d40301ca0040381c00718903010700000340311000c00c40010010b0350303441c079411002d81c20200741943d054101100541107811040484000440509003901583c105120b840e48c020303028480c079042d4134100c0e00103002c018200602580c40e20144c00008046a400f51070003000141d46c541c106c02d41c800240f0070304282c4030052002d503086191a03500d18039148212840c92081006640108030242d002d20321841d40c0160041c0f20117103d06d43c14a05c2c50003003007507620650000703503039500003000180140b51304d0b8080c03007500c80503503c2c140c4407038040c0030a20340044001d80b020030b60700c013510713050302e00302e4040b6000d940ba140f804100341c02c040e150b0038905448a4078182e01c0e1204080e1900041e6030028281045035400e0801040340c5040000c15524002c04803000b8001503e0015000288009040d1010040c5001c98041003490b403205ea02075500d02a500895001c41c415045000851 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 379135584 1250 379134334 379134347
    0xf0804020d0213060b090f0d0c03020402091302030c09040c0813060e120c03040e010515120a022b06080a05060a02280903120318020f040b10020c0a0501030606080106 73
    0x1e0300140c0041001042d0182d00401c039042d6501a240952002c03842c40c10768030b00540c05820f141070440b01c40d0204411900d44c041850014800207110710b030700181c0b2444e1034484040305410380034484411500e9151403980320b03001e5406510400e10651030442c640c000c3c1801040e009009420100840c2c20074032407983d480740181880090f9011601c0388400022509a1140044c64501c0d030420143d9101c52030440748545485068014502c00c440074810718003491038104c1560946250101c0d842015101c80303041c4e6000380700e2049115040c01c103d0038011000030610000e0700f08012111030400c400d5035600b2580da1118038000006046402c880081400d5001a40140150844580c07410328020400084000ca2a411084050108210032070410501c20b40c07070403103e801a130900341448041c0070359000300c0c03d141c211100288107010b0041c2030b900c03d4495900000d039054016104040f20a024000a0354420244402500c035000303007003005c00c00c4c0d4030038060a0104c5441d501e501000d130342429410b4490 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 379136690 1106 379135584 379135609
    0x30f030e0f011112100e07030209060909131103010203010b07080c0708070807030303060902090105070b1504110c1902090103020111030705160e3904080708010e0d0f080402 76
    0xd0a5801000381c1d40102c47e840c0050352451900b00103502d5000385040c00380c1000c181c6040040d00e1002e402c0d00015a03014002c1c00d0009086c40c400c044c01c4c0d01c42402a41e55080052200900140c0c02e0800b400c1c42e4420101a5046d640d25416170f51b28140c460742c0039070305541c8510010402d05415105000c0901103091089d46032084620000e4400d1003280001041c040080c0000381c0000080e070b03421000303030400030820301016901d0101c90301d003900301c140000d905001d0404003100041910305c607040d09a601801d0710300c15130700e10340056031000351103007500d1000c0c00200016000240d040c000c00040303003503900c506034000d410401c091a81c540002c0029555500b44001c0c050b0450045400038103061851162420006040c01c00c041c0074061680000c144d446110030102d0a10419000712007038844c0c49003211070010412200b1541015018080000310701e11601240142c1040c00c113400a = true := by decide +kernel

theorem cover : BRFrame.Cov 378956834 379136690 := by
  have h0 := BRFrame.cov_init 378956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 378956834 ≤ n) (h2 : n < 379136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
