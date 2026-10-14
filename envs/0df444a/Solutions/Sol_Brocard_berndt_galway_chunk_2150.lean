-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2150
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:48:01.507179+00:00
-- url     : https://prove2.me/submissions/f5705582-860f-45f0-8ca5-79c380f134e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 386510791 ≤ n < 386690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 386512041 1250 386510791 386510797
    0x10140f0f0f0406030b010b0c0c1005030117120a0c0b06010c210504050402030108150a060e0a0207050307121d09090601030b07050d1b090509131101031d07030c170d05 73
    0x407a6201d41d655402002203a0800101800b800b40c0500e40c0d90340f228211190392404080c8110a44039044080c41341c07007542d178001c0903603044810210201c0043c6031003406d41401c11520540201c6200340104102c11029031040205040314041c0603107180d1906c5450045500700c4014074003400750f002d9403039940c404425550001d0300114092400600b0076890304001016030b8001c1c1c0c03010540e035212141c80003c41b003001440f0bd030802c03441e4000704800d52816000f074040308001002c09103415404a44c0e94103000042c01101c0a195000c1d080e500f0441c1084000b0f00384000c0e9041b003d0741d03108070358240300041c10000c850502030883d05004040070b030f1850b42c0314616520024194001c01c841485059072005403400790482d1000d101e20758280c03215420310000e11800c0640d10803481035010005002401030900d01104030240c00c10703e07034403121030044016005000e080403000181101414081031047c80890040b059920400c03120790400da0f00c0301d051100d011401a918285d800045035410001d00841c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 386513291 1250 386512041 386512069
    0xe1002031b0c03120406090605130e0a2408150604060e010920030106120b1c05010203060f1203030123060705030901030e011a01120603060510140f0f 66
    0x440e4644004002424100c1280d0301500314140e00480c1402d6003440d040c401114010304031051030742014a40f00d001850400700d4030548040c407000140007070f4071078810070701c0c40050031074034200480c80d00b80360f040036006043c511280300880001d003070896130200180e0101c002f00c48002e070040000c2007020800f50182d5001800300765000b9030365000000c46003004503501d4020111a01d000805072424000c8080c1c000104202003441003003000180309142d004054003010996400000a40741d084001203101500040408030f04910800d140c0341c2041015001188106002d0f2034140c8140e9247c1c050208400c0142c0b00040190403c0c00188042016049441c01e1104005022003241240a02040640d440500e0581342504001200007095804d400741d848481141e0f0300811130200c2c11240504208403200c002070400060f01c40000c605e61240e007211026582080c810000c03810300d2400c14498035014491945054411950342c540707844d0103083d00c800c082d0068650481c8901d0748080006088404031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 386514541 1250 386513291 386513293
    0xc08060a0311040219110c010e09010603020c0f030313051207020a0b1c09030c050606030a03360603050402180906040807020d0b070810091a04020906040e04061e0c0e1002 75
    0x4072009810905c0d0700d100c100c2c0b10458a80015144814041c0c0b1305002812030200c0c18050000c20303d51a0b40c881c00382d4181150031910740161107500303061950b4148009030a14007058400031081c018000c4040b1500d20310184200c04030b6014046183c01c0d04e03218018070301c000c1d5028040340c0c1c08004000060340142007044031100c0c207002e1210340b030500b401201d0700b040c020b800150780c00d014081002020000301c0d4000c0b104a00400300c103005a0b070010003400d10000d017a0380d41c003030340c980e0152030b10070209150440101c443e4030b4042c1c4c5901d0354070040041c00100c078117030b00c1007520341810f40c212203244400d540100140409003400c4d50701c1da00c0d10070043d07110201c00c80e0402601d210300e00100b11041d207070b18001c188070f58842c00181049040d01d00d003400d842d04041c1880740f42082c503801d0100c0700c4e0006403c0110560340581ca41003c8400100d060241b41e00000b2540241020401007141d2a07008001140034080c4000c3d407242440b0703010f421101d1500b46080031a075031001c0400d5520340924001039243e0644 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 386515791 1250 386514541 386514547
    0x10050c0306150c100b090f061f170a0c02060c0705070608061c12020606121005040813180c110a0308062d0f011704030507062d0c08060a03110402 64
    0x80c443d52420060585410a103035448400100300d01e081e00b0490703000f102c0060804e680c2c3c20030100058005011070702e00728400b80002c0e008032030140507018603070325020104141492440c1814410b005420707058003010040c0110400079641485550684040b43c0e000301c000d00d41182089016200088041d1110b0342c092070040403040802c04030130704441118402d4060260a0f1280340c8068074107040903145501c505a5820840e010703550020300290030710036100700803c4607150743c00c1203006071140300c0c1ea0002d43c0300c00120101d082c56040c20b102005a00062007000f04145481085a440d065410800d4080d0403100403000030034413609030240c01140007030440960102092000d030200c01c4041c0703101e25520f403410784c884591403c54102a8048401e080c01401c50b0211030b1804507405004000605009020a0300700600c1101d500100c12020204142024000c803505520400601c5401c40c2100700c2c01c0802c1c1c02c4d031052186400a0003440c000d00a101300901315600c00b6484035000c80c1a0340c01c10b030f0038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 386517041 1250 386515791 386515807
    0xd120203070210050a0b011d010e040b1203160b060f090f1f1e0b04050307031e08040905061c0804120f0204020a18080609100c0509090c03060310050c030615 69
    0x1403013214091003140340001001707181c5400150003440303083c88240031207508906c91285030b60004aa0300601d071003107038005440500c1d2000a0415002c50018100c140303c0401c03110211031911011000003401000c8110850303540da81042010000d4405003a0004000e03004210b8490b42901241e401c00b19041002c8000d020450b0300360500116540441400320340403461000400c0d04501000141c104002000d1403c0d080c100482d40c1c0e5126444000c3c0192600b00c4611103140b030b450917403221154040410387d61941c3e6214814040c2c0f030140e484510a444d500e4262110180b0840c0300c00c1041c0c3d0000c0d6050034103140881020710344000e84402e440c046c544482c40b60050740c0f244000c0000340300a80b580345514021005141c000e0b580b540000391150708c64800d01150803c00508200f5100301d100d8045440b4480348000ca40b14000c0014403500940d011081c01140000758015505c20a4140c0c1120141c80d01d40c04440c0540c1d00c06e07240745981c08030800200e0003508213540208803d00900c1d240900e002c4803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 386518291 1250 386517041 386517073
    0x450d0f02040b031c1709120a02030d021204020a1403070504110f0c07170a0b221a010315090b0f1f0f0312031b0804050c130e0c030d1202030702 63
    0xa00105040c44d800728622040c04c2ea42000c1d0007040c0f420803081c0c1a007146404000d240d80d4001103800b100c0340f4000810440d124070b20030411030328020380d201403e41d250000003140c4010311308203a60803031203040c0303170a030205510f030055284400610008006080701403410017070000a240c242281a80c2071400c00044125030b5491004090610780c3e0b0b402454440d2518215000482500008815981182c0441000715800410301604a642c5907480020600c4c003200450382000700740e00c010040091800003440b40300d010982241203c1c0107801003000c000702d000c1340c50200c0d41e01442c01081c201c003c201181c00b0440202510b40d010781012854a2160310b00c1490f03108840095202c1900480c0c03c0c0350504c10404054030f6696455803d0034240441c2616a03a44501d410b0000c04400810000c00001400d0200c00c0040015805000d80818214078900c1c4c082c03005003440d03240c951a40c2c81800340400c40c6041c001542c0c1034204050b607500e440b00841e401060060741c0042c007070404510503c0c8551075a000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 386519541 1250 386518291 386518303
    0x1060b07030806030c01080f0f10090609020d05060f0a12060f022208120313030e060309070302040617062d010f0503061b0f0c03450d0f02040b03 64
    0x10294486200914040c2e04140c0380a17612803105041044407000d1058078030603840311a40002ca0003d1189144c0d0743c0c006031a103901e4490307000106807810190000380b1135000e5401008410b107002c60a1080341d032018180010002034903411508a1845441001300510403584181041d00c195008502d0004805480c2c5c2030340c00440c41e40c0202c0324902c0c0110712107400d1100b954000c01004000d80a80707208480c4541c418000182501305040301001c014003014825400c000a04400520300c60322401d101c4041c6a50303000c01d000490240e0320b00000400c200000c40441c100d8200c3d144000d0a80340d8075411070049020034449030b40051300c03a03104a040700d840c21809841c0a081106182160b1500e440c082602d826000380c902070030f680011b240218050110001c449150360b440c0f040d69500c01148410900e1445040b04080710143e8007505000a00c0c01844024401d038022880c20510300100c03145150515110103460380c1c41081d00e442070740090f0045450b50f4144e4002400002c140314000c0200381081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 386520791 1250 386519541 386519543
    0xe010c1505161209030503010303082505090a0f1a07030903140c130506030c061b122a0a02010c060605040218010201240b070c05030304140a0e0601120e01060b07 71
    0x20022560070382035610a20b181910f007003284051009283d19140a001c900c03042c0006000c00c9a800001508200300481d4034940c80c1c0c1c045484007030007608410062454100d80301c054413230121000f0020307030041416401030958100c00b20b0080000b5800340c0700c64050740400c20440034410010340010200d020612444021036448010746064200c54040180100029500c81d803114907060900c042c0392000a2983c03910481592826540c2d20000f000920034003116048032020f220b103255111035006c141e03014141e503003100007030700105204032090f41131424a482d400d04441d6103c036a400e0059803250369020075441c0070381400941e550325a004101a40e00603070981101c00086d014541c0156424860080350b40c01500036003820048091111040b0320740c9125004542e0f00c0031074034000303005042d0f045100500b402404c8980d00c030b9a440c08a0b800d24210310191b4405c0d01c80c0e20001804a02c9000002d2040c001699840a81e43d02001c5001c005e048140c90040355668498011814841d140d000306005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 386522041 1250 386520791 386520811
    0xf060c0307022a0a050402071509080d02040306060512030a210b0405010308070308150a0302010c02060d05010f0e0c120106050c07050411090405010506180d11030607111501060e010c1505 82
    0x42480300c418000c007441c1340d0740031500a610401c45080400c035126481c074011180c110300821029a07500300040c0302d0240f4203106881d5440010000108000c0e5400b0108407442034403480c002d04504001c2d0343d00e90150350703030090110700c1c030444000350441d0441100d0a0484aa00700145420050300440c0455900b41c2089855950003c1c100003030603042924954451700f1807801906909001c00895400809880000e050056407442e480c02c5583d03e0069490045041c00e04120380e60792031002601811551003600c100010340d00210f1400b403010300c1111610640d80100d1042a46011b104803225400350b0100e0195028400000c00c02d91348500610540705c070840c100e2500d80d400201080100c40040e4000d0b4070405040014024030b1541482e01c0b00d03a060122801942c4000034100b1302800d0031000007456050044004002d5081d401500d81c0501010b180c08452509028002c2d000e40ca0000b8000d000115503807882c4410700f58850b5610080951203514034428141020741d144041d20001d132251031794 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 386523291 1250 386522041 386522113
    0x16020d0f05060f07301505031501031709010c03050a030e16050f0604032a03080406200c0901030209100b0c0d030b1c0609030302070b07031a030f060c030702 69
    0x540d502c4500484201c41d5001c012602c81600000c8003140941d084881005603120405696544424a401c80041c50702805a94032880b680e103132700c14502000d000898584c85103000701c900b283e1601050769140001a11455458030301500d06a4054008180441c02c0545440d030b00c0c10a007000b03201c0c202d011040081c40280e2141040100001c0c2c41900280030b006940c18401000842e11840c400315070320701841646200000b94132404d07070080031030b41c001510f5640d000800003941e9074006001030f842e40039900d00518061004054035200e2220031401980582c1a500502c007625242d00001c0d00040c0044460201c1c95a84260300720980011809445030340200c15400000350f0903009054503000111442c0d00e07258080410750500c03040e900406031038503a80300a031204041c0a40d04440215412410080d603a01c0e0003c4010f003c1d184c2003801080d90109880c5801c11400c0c000b50909451402501500459458202001d50307600700804800842c450341d128640103122a0000b180e08c5039030b541690f40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 386524541 1250 386523291 386523301
    0x5180c2a0a03090e130b130602070c060203030f060f0d02091801110319050105090a0c02010609060e10060311181c050616080115050306010e130e0f0316020d0f05060f 73
    0x280c600f80148510302c502c0140d1000302c0082c0c046d03103001d076029040d1281c848003803c1e581400c0000780100c0000814500c1040b50200380c0e29000405540b01d103c0380c03003542a580d91040180440689005201900001e007041d001006203440108241d00c4500401c203c801c0320703403c0c144942540c007002c000406020b0f0000a20455940d020003a40d04c13440500c20034841c551401001c901e107079400600d0070b0b8050780d4580400108510039000a0700610b07940c0d406211464640c1c007481c6401c5010b0350039012a44240f140058058000d00035543c0407801c2d1503080382800da5802c080b070005200030441c15444400c10405504a01008502200480c05140100850310704410300815001400c6202e50500a12070010804640d40410603c210145407422907200d44901c00143c44c14221440d100d035110b50140010582d5981580c415122030114800b15079021401440c0c06840e4420b600051050072400d80c40d00307015013004200405010703c2803050896003074058843c9402c4c00d40540340c280039450b41c002480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 386525791 1250 386524541 386524559
    0x71d031b040e340b030a0501080d08090d12060801110307080703061401110c03120901030c09030b040b06011103030406021206030c09070e030a1b05180c2a0a0309 71
    0x10307480007004001082c201c14070650448030404a2001840c0107580e4490201c50f14a40f4004000108413a1000030707228103051548801402c000d00503081c0920807808552503480c840c40d08a0f0043e8a058003030402d1644d903190850310011045012004d032621500c000584200900c1000081000400c0568503424101c1c001450170801902010415007091420710400040504079410b000d000d082400a401c03e00c0324460501303207420005941401a00214500b010080c0000c184580007640c0800a8812807c41070326008060f00015001d6400d040018000507140401250041d9050400c004600d01c0c4804040c6150b00c200e0b001c8504603008503004049c0407640050640040084015041d0481004042000a41e000b4800010004000312200c00740e10306000280b101ca412540c00690050346c03040c2030031075080034481e040c00f481c103c490540d0700c0000c00f11894000c400c0044124902440560941203c1c601043e01c50080407489171030358a840e904000301300c15144a5101d5480c5c941c600303130b0b040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 386527041 1250 386525791 386525801
    0x140a09030315060801051009120309060315060207150c0c1202030c040603080313060b121c0503060d06090c0506120406060803190305040f060908040e060a0e071d031b04 74
    0x80a060341c00d2031041c03000340d8004d5049815500c3c2a184031403100d12902c0308460507c1582d014900b002e500c01640c0d001d150b03004070b0701d00540d900361b101804000180018440551200d20400300181c0000300300340140b26007000d28030140b40e054685803d088400e41c84122120605a000a0030703284080442c2e811420203000c08001d24a04480400509145840e00d070700c50302c4003c2080d10195044030108080001c294032a421107100500701c2c0380c0904142d013101c4d584140100383c0302d4011101c0050a1840d40c41802100c4c8940f20107400c0316403480f82a80c85d40050805100202c40c2c0645104000c5900d49504025060010051804d0340980c100307400c1541c1202d180da084515180c00c200700c46003e506402103801020240d030320307002490340c1c1c85041c42c05050f044a103000388040e0a005202c01408004c002a00c03c0d40c0100e0305144c0541c0f110420814210581c2c400d14444488030340000e201c040c05900740e0032942010100000b00803004400082c244209800b88080901c0008211306490074a480b038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 386528291 1250 386527041 386527061
    0x1140402180f12011803170402220b0607231b060c0f1209030d0207050307062a05061e010305060406050601020f01021306080705071212140a090303 65
    0x114602007040100d0480760000088282c02001c01042400c02c03502d500407521154848040200614a03864246114020058005400254800301a58803e00701400b000e80a20340c0100100c0c030020162408801c20601d2903001241682d031802021540e440e900000c010275031240700000100000d000c070031140d0110807051900554403000c5541d0002045130501c182c0742c42d04803010780c4c45070107200c1100c0c03038890200d60303104450080186440c103105140018008082c001c800b070f81c46d00400000204c1e56040c0c94400e25a140d482518200724580c090156510100c0c00301810822a0318030868030248054000801c03112503110008004000a0001c810184040082c10011055140d03403a100d640341030151024010726a203c02085080c0e000300030111005001030000e5440e41c62400301103000180700d1040c0004507102e580000d1040d0f1298040b1007030355070b10602e1400c030455421300490b00041503240341070301980ea81c3c3c800350041c40c0c5240c01030310620146a020038411610b1030700a0949606000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 386529541 1250 386528291 386528299
    0x507080f011d15030f07031a25050d0e061603111809101d090c0108070507060b0f03070305030d0b0307030308010306090611030705030a0b0a060903021c0503040e0114 73
    0x2d03038042e40810780011034001c15502401d640c1144420b000900b4103400c07180001140c8502d21000003007085907000044c1c20040c0d0003442c4515520080d10f10000410040e90f048100003061001c6401030054000d800c03c1c080c048800a41c040030303116201d18000045d0303000301c503901048c1914003041c0e505005011039000c404074254201803c5100c00c842c00c6026401e0144036007450700000e0304869504410b4030040400d409080f00c0b4102e105181e41a42c0b41c00d403110310040c0196030000441e0750203045000c0c0150000d40d103180c600b24a644802e002002d00c08071540c0d001242d8201c0c800295010440100034501130300103140d40307a90b00c3c0f21500440d825480c2a5010b03400032a001c1002c00e400c1a10181140e0304444042252240c3d03150510080204104503075400b2030100501c20a160f0107005548100d4285000b0444408020204213040a1074460f500004206450034801820300500681d1441040368000d6a49001951800d003950007613000040104000c03c010800381e1110a203804040005031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 386530791 1250 386529541 386529569
    0xa0516030c0504061211030717060609010804021003110d02130e090706050f070204060f0311010c0b07030c0e040603050a290c0c0c13050a0b2d010507060507080f01 72
    0xc0740241150103240300b0301c4140328891407013440d5507055800030800710b42855400c0396241740100000c2c3c07400101000f07004658801c0c100240890400104a03229414145c440d02c80603074407503003004400e042146004041640780e44030b4000c00c0c91400b0103022441402d483c05a10340000020401c502c104651080030860781100c00d2021019000c601d02c400c0e40e0280c58101e540d00c202030a0070805200b00000250400c0c502000090800380e40c01500c01070303e00c07401402809054410044500b907103510006014034007000003040c0300f5802603110401d212064180b5000d0b0090040010342210390341e0707000750b501c1d4005206250070007005110f0f60b4180311528009c400b036662204000885c0345030090400c02c04280018600e40000020003c118000d00c0062402d50407007141c08408000d03080a84061004c02d0600d81c40683c41d1400c20180040c40b8284a40614000a81014141014446860315050000801c0884049812400341d648a56900e4844081505080e0701d61101d24105a01070012801d1003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 386532041 1250 386530791 386530811
    0x509160302100807180b040306061e0b03060a1d010905180a1e06092022020306011e03090b06010c0201021903021609050105040f05010602060708090709050a051603 72
    0xa00c6040c1039403146840d084541da500c07010103850340c421003545d0745ca121102c901d00052144210300103105032889040240841c6a80c0e0a11222400c440310003a411403076144404c0c00500c4284002c0c60b40f1010007450300b11303091341d80c0d00101400030045540080c83c40201c40180441d0312107008043e00100c201c0c006802c110400c2c004a42c03180c5c1070480040003401c500008949401c00400408d0b50303150001d400700050310851404d081c1803170080e40f021501280c903100006440c504041c0c010602012040b0308542900c402a80d2802944010010b90511041d25003107803911004110b0880c1503155501d0004036000c050809000c8030400501c254100241c03d1f1490006136404100640d0344a40c9900e4a031924100c2d2070242d0904503120385840d0045010100000c042d40d068020764101c070020f5800f040410041200c2401740c0d802402801d0259119002080c62240700c0d0680326440140300b42501c030103540391440c04040d0341c800c1ea982c81400740c5850a211101000003500580c01019040401103980e01c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 386533291 1250 386532041 386532049
    0xf140603010e070e090901020304030f0e1008060a09020417070b091c020d150614030604210318031d030705030c0402070303140106050307110f060a0b030f010f0509160302 75
    0x1050041d003001c0462100810400c90090503070545880c4c000f000b00340c4618141019a0003504111019000105500b950400141c0140b001d221048000742003000306103000746041c2d5107001c0180c030340c5811003000c0d14009000d200318030280000d0f012401301c4404011003112268640303c1c4641045001c2001080903600c4c9030355029010740c061600208125000c0704500015034039182a60380540683c0000c03400250340c10ba50b520003002e6175001456110014140018103503142c0341118020140e00d01a082c00100008464402e81c2c0b800c9903140211700c41c000c07085040078034800004118049945003000820b06259898006410783c000e4000700101c518101c00030b0398501c0350519490096600040001c10700d442030f00480103404602c920fa01d015607407540c0003496540700302d03020800200c0c0c005420310744820115401101c5000d00c0020112903c0f501410001842d030300070001d60501c50401e017103e034404203000e80d16005400311000611442c1084200742010107000400f00342200c1e40805000590fa = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 386534541 1250 386533291 386533297
    0x604230a020904020102010915050901060b070f0f02031006091d030c06270a05030a0314013b090610060203070506040f020414010905041a041e05070506040902040f1406 74
    0x20701140c01800035250f600050380100814040681103c0d00c20f000081c0300b00d11500054001c1131480c00820000b6581e00100100d0b0040a80c003c2445516940720300109484660b000c0d400e60004040c0d0300c20070302100e00c0d2000c47c1d40580c0440c1d05161642089101e450400c43d49000b4000380101940c82d051803a82401e40301c80c0d000705180e2502801e03140005c40d0306409c880c4294030000403000c480c00905c0a05110b0361b207800007600c0b54006410014010088080020100d0403102c6505041c0484607804c6105600c650074451054040c6039039440c4050784035580100c090007000c0c1c2d40c0181c0007078140041054400000b0f03402150940d4010081440020b07c0041d07007640c05038000c0c406c44464141840000c024010002d5007004041e0a64004503000e207107075010a0140e44120320f65203100345075810700c040d1541c3c00c91380a4101e941c00c070440b8010003444550001070364459010745040640b43c03000141c9640250b044189801e501040c1031001c041d103024558003030207980c60303180c00c2c0c081460002000c503c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 386535791 1250 386534541 386534543
    0x62d0c0a110901240203090a1403010b040908040303030e0327030c06040f0b090a050306160314011a0304020315070905011206080c120a08070f050d0e0303030606070201180303020604230a 82
    0x818421040e0503014400d00551f00b80200c0105031304ca12541e10b40c002c44451b10380001262007075103481020012407805120328418527038030121140c1428070b140c5007980104104410314201d4001041280851010b0804004007550103a0804604d15890024035107040d01e505076040c02400100400d02031010040000310031646444000340d035803030944c40825081d80c400d52001c0c0e010f1113161b040c425500c4490415010500080c0d0781040001511100c9103203040c420700c6840491000149451214440140155030203400501221180b0074224407000c204601160520006221080180f100c0e69000f00320b0f600c140c0c6400d10034400b19087c01001070320b448115011038441c01c4406100d0105840030301601051503001028a0740300c1c0d00354104004038025100b022602c3c4c1c000d283d01030344120f0041d0183c41c0b40000c080c00031425aa500824000d00b603111050581c103002014484051101c05440004041c502c80d0780900101c0c02d10b441d01d9140440740c000000b03c07103d501d03c01c101098000281035219a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 386537041 1250 386535791 386535839
    0x4020112090213020408030333090a14040507051305091c0c0507060f090602060702070306050a060506031e061806010818030d0920062d0c0a110901 65
    0xc0302a100140f900140d8807083d50010b400820001030303848012014511070100342441c0d2500480840b104034400d52082c03201da1292420548621840c00c00103c0d55500503d250b0001074824005929070700d40709000c44013260342d58064103050040d410007030742d501603e004000b400c1c4040d06080050300d07120002042040d03001c5000300f40c2402c40303d216012220807113807c401a203116a0700c500d402007881041064041c08900001b0001408a06c0000d0a40c4100e03840c2d409804080c1c1595642d00160502800014890b40ca8001c042515642c00b4010f501940d0242d9400000e402592740e11061a5001008940b09032820000c0303000c800c1c00c903006960b1002003403808031401d0341d60358003100d06011071130070245452002181c000141c40e1140c0c40a1000c50051a00025070400c8000321301807500802030043e04000d051000003000002401d64005003c7e080d4121591320300346010004040d04401d151400590051a81304188031401c045010155000d440d0400b00350f041000b03695014041d80084485 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 386538291 1250 386537041 386537051
    0x11030d090e01050405150d031701060c05030a0f05040801151701090506010b0d150b070b0115020c040b060906070c1509031109040f08041e0f0305150c04030215030f0a0504020112 78
    0x49240c84080c2c0315981c3c0c0f0014000301c50507c82d0b0a00501007040790110707200c0f1804400001c03404034010303400032401c00e6203c4010f51402080389030481c6c441c00010a214103203c4144000f04402c0c5080c0142000c5500c0e00100c1c0d602c441c60911006c0d110320f0340c10241c0d40700d40d00d040c00c201e0100c0d40200350641903035203060700f650b6104003015241006080c1c0c409000c1440d5514134000c15031031503404c02042c2450141c0040100750741c0368250b240c600485070b03000d08007581c003080c0c001d162400e203078200c6002481c0080c05541001e41c1e44020810641c8150350840364109100301c03d03c90301d03e28801007007082c1114032f0070600c4c5a045940e00d0300600350002c109482601e40c0e0300042c0400044414028003241c0c84140c10746c0310760340c0d103000000002144030341c580840b000f040041800140c00841208403500321000b1308a000d031404c560030080d40301034010102080d0400020000d038030b804041080c18080004119668503046501d6008520b0140c030244523242000240000341c0c0c0d0008201c0c0500c0d18603207002030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 386539541 1250 386538291 386538301
    0x611090427080f040906150e0901050319060f0509061e010501080402011d0406031103151b031009050c090f0d020a270509030a020601050117010e0601140711030d090e01050405 77
    0xb040c0200c0d4403001c541c1b42001c0011615180d410412a004115502c601d0001540c02040200109017401606c4d0142d11490310510300032800701100d000b450060710002060010080300005a5401301c520713058a0f1711503400d01c03820030a0000303240c590840542040810354141800207144c018042c1029040105c0c01c20f141d540b114003007804001c007040060003001144d0b0350f854080503649a80d00a544280912031340307600790300340f04201c0f0382c410545540f6a04010103490700e024640d810180040040c49402840400c1c1c15655102c2d41d07003c1d840803028103440780203640c20083d0081240000e280a4030035103e0f400016204d400e959000d540c18582da11400c620005210020700820003102c1c11a0b43c03c260520441010103c020440b10501b0390913100703107a0b21180150740201300b9108044036224254010410200480074545d045801454442c501c1c41d280c140761551a044450143e4a9030740e0070070100c40b41c3c6010025080c5402e124108103001c0e0f4074001c0d06400503901449028000d50716200001c07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 386540791 1250 386539541 386539567
    0x20303062101051509010b04060206011a0712022119030903020c180105030714031513020901080102120f01060c06020c1e1506011b030c030c061109042708 68
    0xc0c01c1d040600008106510b400c40a081e5003980c028026070044c2034910020460440c400111001c0d5401d9400800c0d42c3e900c2d051203821411220700c54038081c070a080c40060b0018500120700f40c000185070b4000d00a2840c1e02c030075191261080c055840c407148041000f640b81c01204002420340b03e41c141030006070440c65080a034106070030030741400c1d0b1024800001030545903014400b68180c030029011070b450741e83c80e144000e42d40b50700e11106070360560101003070000c1134100030005039021400703541c8031580c0680ca030b010400900d8203070804010340e500421000388400e00f14406d02e900c60544602a80b1a5160040141903104400000380141e40c0015540403107400402002041c9210b9402100449120500d110788645115011001500440001c80c01c0d0b0b62042d81509850282e24400c0100300b586681c040d42e80140040044050144500f200360108026119100c1946100c402c41a40c4840c02010401100c2d41c06210703090582c0300f0400101c8007403180801542130740e1701c082d0144c0d4450070b4034565 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 386542041 1250 386540791 386540839
    0xb01140a050d32010c1106010605071b08030a080a0c030b1c03090b1909080102091f0c021503090115080304090c1101060602160902030411040c050d0212010e01050108040302030306 79
    0x10410044030103024483e4090541c840030035211503581d00308101080d20701d0140c8401b000c1c880e160000c5c5043c411070011a4000c105518102441d400610358581c0d10180d09085401001c840404034034020304100c5a102e0750f000f07a00744103032240b40410042075044002242a148022140b510340241c0e4016000c05000349450400b900c202c2c00565118000e6100b450294003214024900044e414800018036002c140241c91340550001d042c140e10306104000c0c200044d90101c200b0341001004034008001d07840ba100e14004202ca01e011555070391a005140c50b0a40700705030222034080317803a02810041e510f004810740b010789200b10b00200c0c8000c0c0e6101c044038a08202c84030174071f65520b002d4002a005400042c0303120008070354142051107a988104002c2240001c03078014000d085140d6205a01d0301c0c190307001e03d00400481c18543d040243d021030702c5080740c1000c80c0c4d12050798a000d0040c03140a0b16291140e004000c01d107062051464141d40003500c0340030160489000c0d00742d00c000340100072108010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 386543291 1250 386542041 386542103
    0xc0f08090c0d0f060c0504270b0618041a1f020109050609030703090506090d1104060b070c030b0606032e0909051f020a090303080a020906070b01140a050d 68
    0x41d108540000e0400f205001d0140e00d044034428908680300d43c150b4003c0c41620b0449085503c41d0b80c44035415003034030301c0c0c0d00705404854407081e5413917504101560764540505502a8031021b2a04400a0181403004450409100c0046071002d9103946c0301c1035842048190548000200a4101c110404016405408200e4008005001d00c2e0304021160000001509800d800f07950f44422190362401840f0341d5108580d003641c4c0101000c100e21000c5002886100c942c05000b4000050b400c0d0786040220280c0c0040100b01d0747e122007000c080091042500c4030607007203101110420b24609120202c42d026800480c12204910f10800700c1d880441000c060402c0140319901d806d20072803030145005a1152001529402c11040003440703040071505610035103504802a803144000c0b142192019160340034000d10b036408854080101032a540c807541c01074200d844c40341c00c1503d419410100c0c0003a4410302c2040403405400320443c01c00041d52805090b11115800000c0f010004202440c42c80010110b091 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 386544541 1250 386543291 386543299
    0xc1e060406080f0615030a0203041113020405040b030c0a120c0503011503051b0918030415052a03040506073f02030309100c0c05060103150509010c0f08090c 69
    0x18001070100e03044041e8a1040c2c00b00041007038680d9a2408200c44059904c4401145140500004003960317040c0c1e00841d0458011154a54a9810b901c00164458540341d040f14419030045402c21040c00c2600940700504c400310050801c4190a0001c42d810381e270103104055049501c4c000500174403600500400280401400078080d80e644009820300d0b0510b51301c022981c901c140c030002d1300a110302c540c18112200c002400d07c1255210341c90a117a15003944220341c21980001c12000500405050007405040c5054031503945409030b101410f0040c068191100080258200c50851035010201c1101d007907030401c40300e4541340c00d01e0b42060060700303800f050000b40654040103081c0c40307501a01c03000c091112440404890b88404002d040f6201d000c02c2d22600340780d0380201040000c1c000580c000311162a5146444080101d0303036254546090000c0e0300c191b0703030101d60910301c1c2c581e001540075040e80a0000c0000f0301c20362603100e000400740500f014400302042a4600401d000d15418400080d800078014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 386545791 1250 386544541 386544547
    0xc0b07030c0b06030109050a06200c060121030504093b010c0e060301151b030e090a2711121c030608060c030a021207050d06060e030c1e06 61
    0x8036018016000340603050307941e40d628000041c1e0b145014010b075103c850b403040150107688215a2010080c128648002c0501c034140c80725003440d150020060080d6052410080c1002e514090f6040444600c075042c0d0740a0700c181048007400300e500f0071304603000c4522000d80040e01e00050b114421003c419142884047d281e1502c412110a442503898955208042e00801c481288083c081d80c0544000c21013981101090004012017400c0e0f02501a614601d42000c10031030103420641849882501411070124074428560551402c14210099101041000c01c0105143d011900c00b0900a00800e09a40d400c00c1030f0300c0c0e400c01038880410b50008a0181c00004d04000b082a01600c6031004448040d1154007056550310491003400ba40c011580b00a0150030a070303e17201c000c95910350009103c0d400c40c940820015108800003004584500b040b0355030152902640205c00301500c0156010200b00040d005006415980c049400d007544002242c0c420703000f04500000e034030807549600d0240d600032004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 386547041 1250 386545791 386545793
    0x4030915020d030609020a090506131a0d0b0a051e03282f060a022506080907060f0c03020f100b01090b0a0503040b040807020a031101030f0509030906070c0b07 70
    0x180c0103110004030f49051100381d07240c40c5039000b2401142200390000741c05940401c00741c10010005c185080010034041d10994440c10719655010300741200700e42403040018202501c4089104091883c80200c03a42d201440c071303081c0003075810380d4505e501c0542c042004201e00b01a40d0108100c100c10410b4a248180481e03036524480700f40181000203448030114000c50803600340b0209505500780346000d07074094000d10448107105d070030781080d404402540302d08010949001c400180a100440000410400c1c0906000000700706d1a0044d00d00c0c0300310751007910140041c940000e41904500b001c3e15000380d00c20941d050480c904030b60b841d0890030754050400c80e11001d0b0056009029401001e88a450109a99000e59482c900c40d401c0e601c4d002035801d101040c00100606c07881034000740251009820600f454001400544469100312103002041c4034a0f119544c2500a080c021060705c40100000d140404040d80c40303110300389150784a54000103015040056801210002c1c1543e5004a9103070a40c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 386548291 1250 386547041 386547043
    0x19030f120e09010906080d030603170319050c04030c1202030a110a12050610060c030207060e061b0619093216030302011d1005040203010204050d030513051203040e0403091502 77
    0x9401203006d240502d580503250a40603014000c110b03540f0040c001c01c0320403260700ca400b031500042e208240440d0507070b08046500c401405114011118907094507507803403451800040075680ca07400b40000d4017540c036203c400342e80c0104160601d2a002103042010b005035100080407024141c01c03441c0500081c040c03110600c2310014550b4811000c1080300c1015039283d540944801c4403588000b401607003e0302d810b0100620491890180d550040c0419040103800c111103050383d998084c00300c40d954005800c02020302c1108400d40e80c030380c2c000724003082025140d403a040f05400079140b070310b0a4500d031011030f00d454640302c84103501c0e485140c0f0300b41c6612000351a1250284051448141c0040d82481e03001d80e07210fa1050020112480c4000080800360381c40c88032240a0a40204183e0341950f09000c00140764603403000d2200124480d5441a0366a180c04080c0c1c00d8014103608010300444049c955078481400000c11642079644111009c00c2c190b550703103000c541c9080b660b0011001184c0555036845600c1e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 386549541 1250 386548291 386548301
    0x120301090c080c030103060b0402270109140f0108090a0c030f03110d080a0c090503190b0a0c0804020618030a080d0507170610020c0402040b0919030f120e090109 71
    0xc2501814048401e104404990465055994800f05081000100300040155000c07a92a440151025060a450341020b64840e5813034100702c0c010200ea148407055079a0b03c0300c00e210240c00d4140d920400d88069a0102d6a03042c0c4010506045c01000d1000c80d00b610710800800141c1540f000c03084030500e03100c4c900301c001030041d01c10403030214103040540100f44002042c140c440380c4507591071141c2941d8060912001d412807030000d03400c4c0001c0d03100101e1151400e11403401d420316038200c4c45460340202e143c03158108100410300c070b4000340340908151200e81e0000b045038105d60121403903505d83d02d031441c526000d40d10603103181d40d01d840340c0c20800003000100c00c05801c100660010800080c0e41e0804140c030030307485041104400310900d20014216150504540c84406890320448600c1030042000ca000caa01c0358104000c005c901003049070440c130f803c0101b107115114400c02c5941e10340c51551148a111001c0034000c00024030540641c074210720036003903441940c1005060f80e0240d40e40d06401c01c000d04c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 386550791 1250 386549541 386549549
    0x9110103060f15351b0313080c0604030806010e010203130306051b070c170a02030a08030c0d02040e06030705060c0a0609020d060903030b040f060609050d030509030307060e06070305130b18120301 86
    0x1800c0000001c0074042c17160140b60070640e807100510310315a00c04440070350b070340e05000080b43c11140a00114540c4036040101e288104d11a0b03e81103c44d040040014205014129081781154401c001d1460038024646400701100d40c003500105140c0c603481c0e064005020702d010880d200c02c2003c0f500000b8021486c5064048400c1c2000b00f01080e442807604035140c04c4144800707034140e0710031041100020500401150301c01620500300b410f080c920300041f41a81d202d40e010300318200700c2c5414042c5514003440301780000c2c0710845031036203016842000551034000021024003200e9580a0780d5055440b0265069415913005d032040200c59801d00d40039009103416481d060180d8030b014055440c901181c460710098900649660401e5481d0008200c5484000d01c030840401134140803030581a1410006001068410400450201c1904c20b155141c170400401c1441050f003400e060000520805010000c02c503000002543e5680d00c0489003040b140e03410f140720640c0d21600041e0004812010041c42c160703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 386552041 1250 386550791 386550887
    0x210050712170402090411130902180907063519020414060c150f041b1203180803040f08010b0d0209060d0302071809110103060f15 58
    0x241d8404100721819007079004110849010b0001240151410340025507006104444402a001c1c55001207180f0b200404248080e03a03880d80130000840c60107401410421401c40001201032a103d403546036207101c00e12607001441740c46161460301101c2201c03008080060660326548540941d9040c004040d0700b2078440c0003503100160554032545160080307500701e4541940301a060341114040111680c01400d2500b06403060380018018104604069485103d6980482e01c051034141000700002c0e40d0076004000300c03026500301f0f21014841590010003140c240c50045141c0382c080240c0b040c41003041d0061941e80c03002080c000b0b8000b001c144401e007a11b101c00020f0106d5214001840820070234400000c0d030140b0014002011401d0014141b46154041d20480b90740c180d6684e07800c406424120590000c00c1c2e25062408c0a100a101c10704615403000c0c601003128901d0301c0c00600900e425030042404800c00c81070b44140303151043c0e01100500192059500c000d528142c81a501c182420443c0051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 386553291 1250 386552041 386552063
    0x4080a08341e022a03070303080403120506100e1305010b0301080c0f0307060e0d06020c010902100815040f0b030102041e0f060905060f0c030d0b4902100507 69
    0x4000304910300b0700c040c421600145205000d00140800b130981030703102003840e01c19450000c50150f50070001c0c00c000714040c1d280d6854509160a00a0401106401e41c440c0d007420141031045648840303840408065240c50032002d03903a85103000030702c06680100080807907410100085049001a40294100c401501c1200d907406214403d020b0031706911900242c2c150030a001c2000594041d03410000c090a00910380c80d8400141d513140300413a0040c5403410f0050b0354611280003103003003510868020b600d050620781651300e00040344510103d00c004c0c0031401640c8500c8603540442c4282c20903501a80000d000303544443c3c4421070a404000d15000142050424010000700103c0030321440781903424030354030444500c0c105001c0c0300d41a40040301001340d003003040050400302201400a4800f03400e11100c04a181e821050400c600507e82240c0c0300c082d4900740c50301100c6030000043c180e60140091a1452541d401c41b000140c20012014001c0d4102d0002c0c8204d0311a99401750052444510549080503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 386554541 1250 386553291 386553317
    0x70b01180618090320070f17100f0216030c060f0b0904030507020a050409060b030705031216111f080708220f02060c03120c0304080a0834 61
    0x415907600e481100210911a01c4041c9240196007000c20030f0f03406030628000010340c5070082c01e01408116010609034014070801d02100303d0041d03605004010414900495400414843e0b0301c1e03144904c0100d070060350f0380b5030b00203080b02c8640545e018441c2160481c034000842d030901a1010048260413036041e0314010102080c000e251080b07401941e80640103003c107549540c0c05445650041c04242d902900105000030a03030b585005200d04144107020202d0142000010705140c0741d003503040188603400501e2802c486454072025103221410700080402f04440c281041140010310f208aa030301320000682118001c40140496440d03081a641c6a4403184e642d11811a01c080d0142d82c2d800086c00c640b00d0b034807950400250000d2515001c1d40c04e0074004502d99000402036849400300058136040032410880016400c1d03000c0354458000341c10a0314500e0143d88191071842903050716418010204041011280492810f020a5031030304d00040121092450400e018080100304000203544121501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 386555791 1250 386554541 386554589
    0x203120a05090a0b0405070e071d030f030f0f0c030c010b120a0809040f020c070f1505030f0a051003300f093b04030f05031501120e03070b01 62
    0x2910031090b5030050503414109a0703a80b0448140038000b0303904d0344070784c00010400840c030ba01041c0c002c00d010f40b01c034100d00c10070f00c041445030001c440c1c0c00c42c401c0c2c00c100b510000f10035000c0704540c6c4044480c04070360f039100d002c5c4c4036081c407501510599442601c0045030881c28898158003880c1c441508842e4191f8001e01c40b80300946d2004074101c010300d040024813200c1c0003814150440001da20385011b015052811015190b40f501c04194000d128440360b81000701f00c4410f0011003c1d8410220307140c49461450a1a800e545201c0e0150100e400c80766600002420200401760390000b85502c80060b060001540c05503c0304c0241965180e00e068100b8592100c4503806040c040d9481030b003540f26403201501c0e0001d00140c0400201c95a00034010110310031404541c82c2c44a0461004803204c15034183c205402c0041030354443c4030096041c00300400601c030000c400000006070862003441d003203440709100e42c5071101410120108045030311010848101300041e0149070f0f416120900164020030500103e01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 386557041 1250 386555791 386555801
    0x5031306050c0a18240c1202070f09020c1b18070c05010f060e0703050a150f03060c0c0f0605091212090c040b0d061104031703100f0515090f0603070203120a 69
    0x4070040c8042800000384142030031903100021904094901100d1607d6440300142c4941e850001038001c10b01c01e01079002040d10b588042c1c00407040131420490031064080e600c558076111008506030485500c4001e0359641000d008951500c180603009051580015255946030041105c195003400c40005542c125481441c003201d0081800302d8060300d41c020150300070030016010780007031501c0300c010b8458901c0c04171240c00100102c85045824902c0d5080c048102c2d01c1904100c81040414454000810144080411500d42282000030151502c003052031601d8940050514a07003c0819440b41c40450380d88418441c4803003000f030b200d02202d044104000c89586007000780e41300819401c0f20b07010441d503500c001092844d6441080c5015103c0d1509189940d85c11040c2030f08060000810000800713408141c002030002000d442c160b9400c150004510040780c1d1980042ca450101d040c2c160350b0b0341c2c0e0003000c100402c00b800c015528244080001d481341c3c40700034001c09880c1e65802007502c241b01d078412 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 386558291 1250 386557041 386557049
    0x108040f030c05070317070209100305030304081803070306020414030601060801090b060c0f0c011706010801060815041b1d060d0207140f0c1c03080705031306050c0a18 74
    0x10a92400c14999090303030880e4412600341d46901c0740c5140840003489000d01d18100e441a003d8250f10350000f441001040c0e88010240c461458100b0340c00c100090700042982c0d04030f0342c0607107030030b031120b22484015113503000249440d68517109541c800801d00080707600800503a0810700b18005007041007000c0c942c2d04d040070700ca0f000024042d10010003a1136541e42c801c0c0703a1107070b00400c0903180454070907880307190840002d02403010350842c0340301840355a0041c40403140010b010600a9a03440e00c10000381c0344010511038041803103c9400020b0298058820041c1e1454009204001e20110100e41d04807001c000003180c801300d0104140402d8034440c02e101141da0000041c5524903082d800c0d0340c1200603400003141125002504403034140018014040b09000c508060014081039201d641080154120030303a0b000c0e40180740f0350705c1a000c40e51000009503c2001e50600701e0b5a034070307003801000030303516104406000203150206100a02c0d9803c0006c000c242083e40d1307080d042001c035136215024003015100e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 386559541 1250 386558291 386558303
    0x260c0604211b03050a02030408031c15120b0a06170607030c09080c0d0201030902060d0506010207062a030909020f12100602031912050108030a110c010914042c0c010804 74
    0xc100400607101c0c200924045c0d403180705582c101580c4044a5241d900304108001003001c55851218080035144a03000079500c91031010401c03503150680829030303000500c2020300403841080018000c0800c03900b0243c000c1000603c2012440300460351952079110699003180002d0520f05803010b001e203e410780d00c0c10340b003c000141c600000d03054108000e00c40301e1007049040c5903c40700c03070340b000d030b81c0d10800342003d0581d0303035000f02c2c40d86400f600090030f004041e008103040c00b20b61081d00d81140f43c078110040395503908100009402000d82015a508080d56100402c4035000107045a031b103c8010000d03000c6461003825100792a26058401c40c1d07130300e801d4026800140d005104944400c40b43c2441e00c0210005820710700000d2a400912134140c80c401d81204030380e644001200000daa6008005200240b5074801414401446d10002000c42c200b40c0b00e01c0b5004a41c14407032803090398079035007d00c070fa00400c8484090030070030305000d60085441c20300d100f8086c1e00900c8400d060950149003268842c0d03900032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 386560791 1250 386559541 386559587
    0x30717070603020c0c030601060203070501110403080415030b040c03060f0b040b0307050a050702030d0f1815050903032503020f011a041113060921260c060421 70
    0x1003002c030003d4104405541440c0325003907081e076082d20140500780c06000d03150301035a80e40d00075040850a5509000c8032420642c01040308102164081c01580d05603920071305509081c86500000714050b00f5140c075030b59841031815031141a100d802d82e001c003042394680401e00413943d03a11425400540902d12880b0a000010400101214441d00c02420400c2030fa003403140c101581a008649081c030148a80b101280c4a0464240b0b03d0343c006100d40d54055000d02e07003200080c1000c0070004480070380000c0006010f000b098070061079030144169104c00940103811680621801784c02801d44c0d50000c4141c015005040845030064818010200580c1c456810180d0740404131092100802d02410452000c00e0140402c0380b945207a00c01e030703030000c21031503503280446400c1031800c0080340003044411181850b01425100019449170f070b5104210904058004480310360b0704821124840d902c0c2110060040720108020420040028031484581440040c041c000600c0184c076405030b14100b01c450f010a00e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 386562041 1250 386560791 386560799
    0x151a0a0611031b07170106030b09010c021b060f030a0b12060c09101106190e011e051e0a0f0f23090715050304060b060901090b090f0a03050102030603071707 69
    0xb910203a61861011400c942c42d845e42c0307800b0700200700d10f80ea8100d0441d94580000f0000d010b01d13520703540d4020100e08020008040c203114003a5884d00304036040f41516009468035003551356400300380c5604201e82d080080da031b4941010444020840b610307640d4840c1d000d9001c0418031100c00100e80e0700c20701034000c0c003614000c60340307040110301240790408204109140b03410280d814004e100440c01100b1150300d101c5e034662592a80340680e19102d45280c8580c0c905110150040c0000d201290790300c101343d41c0062a5104c03c2a80c902e008030000f03e0803042c04030f2030184011103100b90300900d82c10100e040708000c0c2146a401c10070684450381e44030f80c0c082030f910b0011820440101d40450b00301049004039845195221182ca1032200400b052a002c40c201108200601625014400561100b01c40d242d10301500c000000c0e250340041c0c0550042c01c42e01042c0e00c10103841d1040c0340220343e24002c3c121582e169982c54164041c0d801290005e0190148050000c1c01c0b016030101c0f268240b02640141044500f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 386563291 1250 386562041 386562067
    0xc17011104142103030412050c28050304060f030c050906070b070c0537030203030f220b240906040c020703020409030504051e0913151a0a061103 64
    0x80282443c0d0b2141c001020720905000c40b400f02c0020304060805035440b0b2030030b4141410248000f80e00c0b6018401c040000c0310070040003007100c4e1203860640c207424884c45a0500d030305107001034060000700548000135010800c3c2d41c12140c042c0c1c8052943d941480002c1504c0022a200e00400b501c03a508800c0600110b0002501502c80c2940300c0380500c0c0804a51084e5114145800099440d602e4545511410450b0031408104120b82c81d100548070078007100c480e950f00964a2000803c101d4101c5050008100341d642801194812054070941708a00d02010f0b0134011b004030b8040e140d071004200b209178024824014001500414070000b003814400e2340d0346406100c081c3c203100300c80c07000718040d81c0d10100041c0c2d10b910541110078001d6503160348036030411044c446248004000140d200300c001ca41181d03d44e03a00000c07190b00a01c54056030700030710420301c1c2c00420840d101c03104014060500603154608100d1005990001604aa010641954600090300c040c01181294005a0002c00401e08100c2e6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 386564541 1250 386563291 386563319
    0x105070605070e0901240203210405030c07080114011202090601080604020409141f080a0f020a030629010c08090906061207020f0714060702011413030c17011104 71
    0x251900b40100c203292208000303911400246c03c03809007401c5d460507a00461010740003202865596000951401c612080202e040c41c0c80d001600d00c00c0d52400e40005c0c100002403003a602c0e0b0144510490751400e0b100da10780c0340a40606840841001c0c0d403030000143c1c050f543d182c00c15665401811040403511420011215000300410240d00035801f0000060346c01c0b8035208084000d03416810810041c24031007034500c0c0c1500307000e140301050790f08201c1c103002c21200440c00345c004552140004d440820288007298aa100c2944007600540c50718800000c84220401a03400e40e840300b0081d003110803481030055403001c0140c080900540310030b10900e4601d0404c040310701d802c54001403600c3e0810b40c0b101181d068900c400c41b840700040c1c00000c481031680c1030810010002e018041390f02407a61500001145040c016004007038100705504001f040303600b905c0c804858052071841d000c00b44e83c03901c908007000c0c50243c5125010700800300c00d00c02c1d4400e10062050244c400090403000b40760503d0302d66803042d020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 386565791 1250 386564541 386564551
    0x3030e0f10060f0b19051e04080f160f0509040203030706150f05030c090a0902040f0606020f0609030a0503160201060803040f15020f10022d0c0f0c0105070605 70
    0x48030300c0c00c104080c04000c01404881c40340e000d030086082810300300040200c00203a44502d00f13140301480b803070907640311200280480031158605691510101c001a410715034850b401030491010004010828400100d51006000139403004c50300b03088480208100580c003513104000c060068a2024801403414000d40381c0c026000400700c0342404141d4440030225129880d4040421102c1c010420190745074651010081070114054071252100300003207200854020440d00750315542ea011102103503101d40c0001d032002c848181c1007203483d8803500065500c02084050400310312030070340010521840001140d100044966429045480d41d05888140b50400c0003a1015035480e148045240e81c0204050300050034440c4030503440624180000c4004404030800700c08641002c3e04e8080c12040004100302101070305000184c0e900d00c425034600400303040e030607400e183c90b00c2c03150200780e8035903440081e00d054025903040c1e40c08021400501d0383c1c0d401c00e51035101d0110b00148000004500a6070005a000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 386567041 1250 386565791 386565793
    0x6120607030e0708010f0605010f020c01020703060c0c06090b2e051002150c0319022b091403030a0615080f0408040510030c020d170a0c020a020d0f021905090403030e 73
    0xf1603251800182500d46200100403040d6440d5010021507078003000d03140603400680064904401c2540000352903005900001d03190b06e8840c003d64061620a14019030b0007500514100201402e40c60700c3e0742c0910003920b40ec44811800b0205100e004016408007154058224034140800c0c9044144030880400403174040560103110415026855181d4890b4410f541038028503a0f03a1508a480407402c804500c501c0e0780c3c680c030501202c5241002042250141d5069010003644180c19066440c040c0003440401440040800d4040143c0366000000d1801901000010301455484040000030700d0558900c03c03000949880124a8030340c01101e8054005000ea90741a10309611140412000d1044c2c40712000000e60756050803255985c140300004206a291415401c0440a800e5040d200c80010b000d002449a070b0b0541c603502c0034003c1004104641d4050580380b10500b850034201d41c0801e40711016400381d40001c6044100c2e6040701c3e070780b0054804c01440140c0d262200e480c22001031400f40390080203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 386568291 1250 386567041 386567053
    0x2090a180b07030212010f05090a020f0a1107090e030d0e1c0e0d1205030f09010515011805030a0b0a0501080a1a09070512012007030215041b0b03040302010506120607030e 75
    0xc00321207030b00590103003034811f0600c411145804240315010f0001042012002c0c0305001924580305140111b4680c10450701d44001c2442d05043d501b802c0040541c060584540b6003103a80482d840040040c0c021922619810400d0036440c0502c144c032800101604001080c04140308003982c0d019001007503004201600e980d104134420740d030340c00844a415840ca8041000401000404600b94200660055030030000b0300c039904046000d188090142c00b4040c3c14000615540c2d044003a220201900a01004040f900702081c5410702c044d28040648a591002d130800c800800e0f0310340b000601c500069800f08004030350400140604a100c100640300c00c000380230303190300007401c0e5071101241b000303050280000240481c00f044070710042030300040001e0344804003440880003083e008155a4101118040d4144d580c1d07545181041341100c4100300c0d51000724025901080c0152004090740c840c07480703034000700040d480c3c41d0200403102d600f14080d4400d0303a21640c002104075200c3d0304203072200308202c2e0071200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 386569541 1250 386568291 386568307
    0x9180c08130602040b0310051c12110a08030f04140a12121401080f2a040903090b030a0c08062d03030d05160801060807050d0c1b06060302090a180b070302 68
    0x1700c56000341c1d850242d80c000d0503c240401d00e402148208802c1110000219081c010750b1041c5903400541c0305c035024404525000108070506100004007142d00140c4155a0b1404010f20010301d1410b07203090300c0900d82501d403282140381c000303901d1100daa084035110004c404100c81c11102405811041c085071501c5e10300808002d110380c490580a00010006003041058082c11580b502081c2c1400c0f2261034011140796044807400c0c2488035008005a6000c01e556845041c2555001d1840d806055000c000004200412180354040c1f40ca501d090754400d501c1d91134610800505130801b10550b60170342084440465001451401180d644001400741c0b8206118400c1c0801100d1040700c012100d0501103400c40050360348a05454090201401e0110690030191030040250081d00c00d4002000e90750142500560301070345000040c40c8521407841d291442c1071802034007400181c0f01c120701500c1081c010410607841c5000d02c8260718010840115010b4590b12030000c0248040e10304d02c203056007004811 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 386570791 1250 386569541 386569559
    0x1050919050f010303030b1507020909030c07120c090b221e0e0106052b020f130f0f02030108190c170f0705030303060618010e03060709180c0813060204 67
    0x82c801c120410740429150702d5801c0203420340c0c48903840a8490640c000c214240d030342d0448156040e05d030f0103840104103a9200d0720000d01d984601348030b61656104103c0006004148401000d8050b441100f07190340e0660f44650544c256640d404030185c1c404c8600015400c003210102d040c901038083c1e80c00108080420404410707002541c05c0b51908a95120400703010125000d0081d54000c0c0340940b00300240701c52030020518181445020020303c503440000c481c056541d288680c424070b0400416000340c05400b10744040081030640040c47d03500b410420764a8101030300d8426a412201d88801401200c41c0140343c0344030b1522518001c680030300c440c0e500401c001a01d8403003584a0700c41100102101500c1a81141ca00f0600398003040c0f003540204200405500c42c0c0c410f4402c080b4425481810949140c00165000540b08085640510510742001303009644a4000d00855034503000101c0a001403011034400e541003541004003003a801e00c04105410701c0d80788010100c0307000b50710042c20680c56030125 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 386572041 1250 386570791 386570801
    0x21218070e09010b03210a050d1515080a0c020d05070c170109050f0d0c0809040f0e1e030304171b010f02040e0609160807020c0d0605090d110601050919 67
    0x1148160f544a0304c40ba140d0030100005044442c0c3c580d03050965128200c810b485601c11007078240100320000c140340081c45070b140c02c0106941204446a1030480d281e03c500204005180301c40f1000401060200300c0c0244c0034802d07041c0c034620590280884100c40700c01914503920000e8111012500064001013140304544010385040f41e004c00071030725411500303000c0c0c9801d200c020325440c0e079001400b040da460364015500c00030580c4c0c401106a198034540340041c0040c00060703080800d8500300480c5240c0309401290019403026500340300307030141494401300d0396079010450b0010105110307858155800b0591002030410800340c0c01ca8440b4102c01488201d094071710110109980e40d8011409100c8038022560a03944003805480d85503951a007941104241c0310000d03040d0090201c90b001041e00c0c07610a001c42042001e0185c03421141400901c0c0120003810b0071501040b69005c2c408100380c4480c840e01c035060030911a0b1008003810303400c050070010f100710042c118401504c102d001d5001c0c0d6044078050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 386573291 1250 386572041 386572051
    0x1e0d05100e0f061011070f0f060f050a0c030c022707030b0108040602070620030411010503070f12021308070e0601050f0703032705030a09080c13020f070506010b0a02010f021218070e 80
    0x2047c010f03c2d00c0d04074800ba643c100c640020091200311140544450f07403080076a6135411040c6440f807414a03850800b5070707040c520101d000e508620060349010b500c03140c1c0044146240d080c5202080942c0d14203c003142187c0d4100017140c001001e4002050120341d10383c01800c0003500440c0c00146202c00400984000c949002c0786e106041004400c1000380721140142115410080c2040c904c0d516002c50024000c2000301656014004649444003522031194140c5601807a19941a0560741c3c644a8003940d5010a10841031002d160a0000300c00e544900151501c100346c11803640d007400070507542540070300341c1082140c500c4902107411150004cc89481111418050005941d441d009840c004100c016182c021030317000c4d80052080d141c00d860303000f6004401c030a14800161141e98007240d40c20b80b40b21f282c1000d05103100c0d9500200e05c0106d9040203003d2500c850300204480c0c02c0c15201e480690013042d00640e03070a1000d0000518040752030380203526403040c2e00d091701c25040c4c0b622010b034903174401a01c0f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 386574541 1250 386573291 386573309
    0x70b0f0c19120c03090314120409020409061d010314010e0a03030204170c150c100f0b0a09060806010b070819080712021305061e0d05100e0f06101107 66
    0x242600500203269020640c0031898907082d6030980c0350340c13405400d9903c1480300619041e5545062091042c0a000ba05001026101c4440d9542d030340c0c01d0703c03102940281c00f4000c4000e24050700001c5403284180c47d03645050715580c41c006542c1c03031501c0782814081c1c8403240d40010754a0701c20b06110510f0030b001c0f40030b00740c2c400d407001610f407400c10384414588282c420248001f40d010300c8a818540c0e5400d04e4010440940daa0501e50754101180302500b0040c00300b14801c84181040b41080c0340c2c48042d000484040c0302504e00f000386e10381c0c8108102c191146407050a0091f0440e0f030051102c0c1a00714000e02c8141e00035100c3ea498003050716030480d1410307006490a03000034415014041110381c03008520041e403101010035070805c0c8082c130710360300c8245803841801e02c242c40c0050300d40c000c1d041000050701c100c940100c040342c07140c01c21649000a09412500304031081c28001d00491720801c01c07807809010b02c42e049111005541d0380024030141d015119444e4052100e80c0364602003000c001c0154002074811300d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 386575791 1250 386574541 386574583
    0x91c06090c080f060c13050a080105012108040e070302040308031e060d020315180319030c09060e01030507051303140127260c010e10020a02070b0f0c 66
    0x205001c101090650050681030b000150250480500000d200c3d410400c2002d07582d40c0c80c0f401042450050b8419409540c0040000000040418040d40214120f40000780c0081504035845604401d54281001c01440180103100c2800788420342c82d099540300015080040c5802d440b5200c6048603081110f0f1023015003503a080d44030f10701c08940f4003d42c1282d0103407200d00f4880144d500007512004203030017640c1215081da000440d031800c6a448040008085000e480d980c001c00c2c06800004c84289109801103410b09102c09003541c41502100c0071208280d03282c143c211004030046000d0700010b8000010004184000d061490184e11954002d42c030135034030902001301a41e0300c142035030b003022114840000014000520300c0034041c44604074541c045001c11440c492003238141c0305000fa101000010450100360020400303415400810300b880c622003281d450880c400c208505a200d8402c1d6030700141c0000504209130402c14010346445c4601002c950f042c080031022103403818120801d00c8071242c00f11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 386577041 1250 386575791 386575793
    0x30221130602061005130207060c0504290a051c060f06091403030915070f29010605040b0a0908060705030106080901060f1401050c060705190306080d05091c0609 71
    0xa40452402030101d80042c16051a04044514012a081c45014007603800310480ca1035030401681100c002d5a4080c00c200807400381c0210081080d00030307000c3c01042640c03c51245840c070b80f40c1c00c0ca00c580e5040103021702d40340451081040720075030807560f00948007944919142607000320350f0084001602c000c0f500700c045035142c400000e01c0c50540d82e2109000d5810900801082c3d10007104803034080000381c030509110f00480c800519203100c0e007030740509a408007005070030400250661280c0d508101842e44511441700e03040c132528130182032084002142d402c200c1003004442940140c8164800760800a000c5580c1b080c02604140d421140c101c001000003005002054111583c80d401c41000d0008215080c1804d9a902c07215945003e9a11007140080714511107a100740100d64040c145242130341c006080114000c0c0203034028801e1806840b00308451500c203a0320031b2295008a40200000b85100d4420700c00c10780342c51f40015401034000c50740c4003000d01040b228409200440d88140c40c00141ea9040b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 386578291 1250 386577041 386577067
    0x90c090d14030a030b0d0c120c12060504030f05030601092705310305030a02131d0906150f09270a0213181103010b0a180c110316030221 60
    0x3804014030f01c00da040c0d4080d0404071f14407805c00800d403a40b601c280103012400342083d1071404c0c0e80386d001c80044100108030500704012504100d01640c420385035140c00c2c444c40081511607000441c1c105002070003102c0c0411190750f9403003018407000f82c86002e6009a90508400c6000e584007100c140c2518000c40d20030316125080c1c0c1030541c040342c960313a54070040d291407981c008005100241c00f0a001d0b68010468640040400d0300c404014210031440442d48030019501c0312040008032409406070140c1c1e0300140c8a03c0d082c01c080490140014150714403002c0c10410440c60301d00281140d260110b4904500d07101c0b020134619200755504a10007015950040c1c41003014000381070a0000341d407810407946403070343c400c4900125507071903104158000c000003090109005003040710700a070f8024814200080d402c07208104410980150440900c00681210300c1070b41e51401ca4000c0b0746090780104821040d03050b040148411355403084c41a2110907012744c494004508944504040403080000c4500c64006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 386579541 1250 386578291 386578301
    0x702030d020304030c0611031b0a0302010506010e10110c0a08210a120513021c0201090f1d0403090e071214070806040f02390309090c090d14030a03 65
    0x50a480110f1600f411940c503096660002d10840f0f0602240c9001d00900351402c1c03040d50003d0201420440c440c002c41450719035960071601068015518010216400754801e008030500b1000c05040c4140403440004220344090f0b03081118a5680a010381a110941c0c4103000d0f8002801c140001705034440011850b04401c40701c0c80e0180c09225410094110015000010040300e00d1146400103440d0b55034101c1741146070781c3c500303000f980004482e5448201c00007071104112080c1c000c3e80c40c0485a510b500340c5042a4440d4040d810030642c07440d49601200c0841543ca0341d01ca80f0034500402100d503125a08440c1602c19100e80010400c440401c2e01340101503c10080c103011400450116030600c1d40010708074040240840e40610384551140040030380d9601111898801c401410054800034040c040b140342e0004e00c449410015502100d83c0c100001003603480502d40104088200c0c2ca43c81c0003101f15900c01d901c1e450b0010b484c021480d0118580c3c1c990b024403840d0344009165140304042005003251 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 386580791 1250 386579541 386579563
    0x7050705090c09010905120f0d050a030b030102120604050705071a06040c0206071709070f080a031803200406081015080d0507023003130e07080f0604110a0302070203 73
    0x40c00900643d07060b60391202c041c2c0d045550030b842c0300c3c45081c2c03204202030400d000340d0b60302c01e0544191546a00c00560040003424030342c009940c100006900f2000701030a0b4480c1002c0010ba0410410120b4803504e8240d201d1500b20000d41055440c1250a56608800c0c40c0705240c46034a400404003080700b5401c0500a508039403a151010701910b01d404000542828400001c01020840c208006103031000100f2024000e00000000c00392410742da042c180307a548040260481c00103081d6220410081c1e842c5440310181d9500040040c04009851910544000c0040300c569015449010000b54a40140580fa0218418103404500995480000e58040555034016105030b80450365400c5640d40c00402e0340d01c0964120b54560340c3c140c042c0401629050300010f90003040102d00580103601000000418405400c4846a44a03603522819484800c90031030348040420600d0b800640442d400d410f903d9440310f401040000e5981920a1641e0076070030521800c0d01196001592105624042203e071100b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 386582041 1250 386580791 386580811
    0x3020405010314010e0f090f010e01061a120a0c0e0901060c0209060306060303040e0402061909030b09071202040c3b030a11060304060e0604080d0f11040b1305060705070509 76
    0x10313501d0520780807200d00005201004e240660310204450320000d001c5040c0d480700e648005c2c81032100600c4980d00070901440381c1406103803d4040003444019036016100001850104001540d5541c0444005494420245020000d011024224a80d100344a05018180940e00e42c290101d4901c14003050010190000d8803d90000e01040383e1550004103e4050794080610101517444030f101080c00341c06060550052811540c004000c8268080c100600f1a4003e00440c090f544078102d40a46914003409207864168120b0b1116002d824690400320b9204080d02d8162510a1240456000c2c8148411200001202c0040c044002500c20044682002d0100c024142c0d8036104d54890b984010003495903030048401100180500c81e45d6400b1441c4581030b10103903400c80c03401d498030120075403021105101d006c0c90307c02c880940b11040c1c40381a220040c00400c840c60a4100304600b4080d401a07444103041f90800314000c61151074400182251a00c6100108030043c2450204201054014101011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 386583291 1250 386582041 386582081
    0x2901170f1204140d02030102030c030912040e01140315010b040503150603060f040f140a0218070903142104050301180f06021e120702070b07030827070303030204050103 74
    0x15001075441142c003141c25445200c1c44616401d80414511040c0c500040e40c03551020080049030440c16006510a14000c01034802101c440715840400707000d6401160070151110006008030a90301549242800e03000b1b08a5005000d0180e0b58506040260006105600301150400490804200c000b40e10002c89840e00300510701580481c0d55124014900c00074a03240d0740202c0c050000c6881400362550b00702820003801601300c0d5010355204124081280900441000811906075450302207000700c1c00b40d61211070f000e207540c4690600d0b100c800c42640060080c00340c41560401c0d00c0007100e160240e1107146680b910700d400d08060846245103081d00044149000c03030800525404040440345074001401a1204400300700e400c829001544d480e185d042c0001001002d0700c811020251050301c141d821511141e40f98011611140128800207000c90140c42c0462044100400d0860800c00c85400c80407c02c0340d00c1d1001031920042d40e0050700400e0340042e082c0400e50b41406810904d400a48000350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 386584541 1250 386583291 386583313
    0xf02211003051513050a0515010905010602060601110c0d03110f0105010b031b0f18040c09080d050d140c030403020c010c0807080d1104081e0a0507032901170f 70
    0x144410340c01c850940d07041d507a5070010b0006a504080062080c1d082021036488021030f141281c0d5a20003030004032304041e851400040c900d981e0f0b0240314181d84040e80030388203d0700d51000650b101c0c204003800449a02034001d4a40840e100c490300307207602070300940d04c01d13611401840d1902d04001d90036800494690408006010854210040b07a070001c0600b482e518400102030010744080c05a280341c40e602080004e5001030030740840075043c1025034210f804115a00e0f83d030205403540c40480c491000290840390000c0b000500aa018140d45030f110312002c500c00c0703040201203c581404544062241c0004000c5c8000d041e810005603039085c1c420b081c003456100e031039140c5400c04c1c01407150041c190080041c1c0e082c0f040c14150062000b102503c0c81302600d481c0c5486090b0f0b112080700c444041a099194441101400b000401c84d09498102c80039044640c110344070b82e29840e00340f1200303100841011f111815900e2170801968000c101564403142d502c00e4075080182024842c00f00c6490641c00040746c02d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 386585791 1250 386584541 386584543
    0x5090a02010804230102030708060f0904020f041e0207080a090e0f061e0411040501030b0102031c020c031204050c270106030b0d061104080c09090d120f0221100305 72
    0x1a003154200e0505000340c009403c1c2c4082c004200704104c0d4555001006116500c0d8020074082d005000c100c54225100c509003040c450081011280079500100145c505411307828160300c02d08442e1009907a0311070140c640220481a07900280044444e414005150b0710300c0c40d4000c030020003401c0c8000404805082105000d030b070140c80503112130308c51000c6111100010540d050800940c0c100540180030f2004c050a007402d282d0468412203001c20704041608643d0741c4040b040354007680010f81c800d00006401d100c0d43c002900300d48007909281c4800c00c0407109458001c01c509114511031402018821040b1003400203401600001c0894107a250035480012101000381c01c0c103440352442d00145140130040022813042184001825441c0340c00030060340901603d00070401c2d10054400c0310079410341030302488410a021600a40c07641c110340d01c100c0760684210704802141d00c400d080456405442d01032502203074000b610560008420108104800300078045d0141d0004c80440c180348050300d162035031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 386587041 1250 386585791 386585807
    0x3090a030e100c17070b0720011104170c18041b0321090b04030f06050c1c0b06131403060601050307020703061805011d0105090c0d06021b031c05090a0201 68
    0x510111300d00741021240d0b05007606903007250381c1024180340a814480ca015060044520300e04c200440746a0000415100c14010f64014030394544049180034070303040e41c4040520368030b11040c6072030013007420704010340e030b00c4c0c2c40209909040800c0c0c407003660406150000e05540c81c101100c0409250000800101e164281e0b812a80a101a00b80e515650b48a01c100c5101c0d00e02e41040041c200e0128003c800d10030b1f4081111841807040300100400c0e101c9207040c0030b441c016002c003550b5650441c030020103010f095401040e80c00c50040c007040d0401060300c40c08802c0e0300742078001c1500099070400b03509640c07504014a0741c0280c400e0910034514108100c0080d11070b0011f00002d0710b115290007082c00c1ca00400c0980021868020f402081050480d00d4041d04400c101c1a84500b19820070340410b6049402040501e0344100003441400c60340090f680d8640a508000e03161840306649000900d50020140010115140c01c99050003000c0c51001540d800c550002d800c10358141d005040c0c040050b40c005003d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 386588291 1250 386587041 386587043
    0x6030b010e090109050f0c09100311060c030408100b03011802010e0d11060c0105090d02070602070e07030914030c010c0309021005031807030f0b070c11090c0f03090a030e100c 77
    0x81c0044596805030564050059000001d0951040030380c865040d000205031002004030132200000152501e03d45002c604242d030001500c00c0914a6202c003251400100500e501000c0b602600e0a203580c80308100e0810f60200c005204d40c07a00d4850a01c0302c0d142c00c1c4268510b00414105107179500504e500001c00096528011a0003026119401024800603081c0c420304014001d00c00340d070710350900c41e409000c0d00040d41c09105a20800448010b600c2c004900d100655500780e0013002c05d14035084006600300c2e070140505040c1a03482c084c010100b402c15540514094403100116511030074840040d003121b56600c501803c06140a80b00d10042c0d03184000510203000601d40984ca07500d0380442d0000c1c00e80d14001c51000c51003200b4001040080d20022a01c0450041241e83d450f80e80d64107081d601d031030340707842d00401d008102c402203845071a001074510f41000c02090064103000203e8410403490340203541011203a444089564205544040024401c40007036502007001001048060321554035810 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 386589541 1250 386588291 386588309
    0x130303020a2102090a060c0b0c0d09020627060a0e0d0507050a180605040203070f08071107090605030c271e130b0c3a020a08100906030b01 61
    0xd4411400e4810038010071009160030910b01d45600d9420b01c54000d40c0885959800707014460f40c00243e160103144e24100e650b8100b000300c0901d0341d480d602031480b68007025504210310307603800c09100561600d0313019001000c44414442c140c1d039040c480e06000c1c0c1110f010007a200306020082840c2041e130118a509010720259101c0070412242e25003682898015080142c00002d200e6000507090b0321032a0401070841d024404004068a44007840164401201c00401141d007013030540c001540304a10455020b4264984195840c801084540c206103613a801025915111030b07041c846441d0500090b810b205044442082c030103030041c104400702c40d85901000d03d2015500009000c40c5006184200d43c6800b02c07464103580c42c281c03600841d800385c521001d841e001ca4480c00540740d403041e68101c542c40c40c198003611403004681074005142c034071f40e0b1484820454584010f04c5590b030180c0050042c0144545451b02d40f4070308120700501c0801c2c25401041d44604244040020407c0c0308119419100d40c82 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 386590791 1250 386589541 386589547
    0x106080714120c031606030f0920120303090318061623010912120501030c120501020706150509090102030f0106030203070e0d1209090509061816030b010608090613030302 75
    0x201042c3c100f8a40b030a0281c0c060280e104105400003051101c503017581d8064500b000360403d1203411808450381d0340801064000d50480b8484110fa10003c000c150941c004e007d4442000388aa51a00b540c1007626810020750001c60f88400b0303126000d00e680c01c0200c058860703604010b11f02111016102c0e120101034490501400b0007503c0090107240303000d04212040c020300c050606840d05034681c0c51020664000100d800300c51600d0304c019070050718100c0350080102c00c40982407039070303079199494041c070f045034a594200b0184000480034000d89241074401802091003616001c1800380c4c1c0c0030300801003d070b0b9034410010042c0742d0000a1900741075070307028500140c4039501e0841c01d48008401c20b00e41036002342650604410000b000000c0360764802c4a9a885005940e40c84203002554400d403540300c01600000d00140c8202c0300c1c1c001062100c8011400c90702680da400c40041041c0c8201c0c1c00548442e11004010311000d5008595190000c2c40ba030000c1c1840d1414031031403251341d440d0f050b008041513000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 386592041 1250 386590791 386590819
    0x20a1104020c072c0603010c02280b01030b041e0812100509103012030603021003092102060411060d0e0a1a0f010b03091006060c03020106080714 64
    0x7000020003400680c603602020130082406800b5044884180d8120490f03036000188145c14103000d0360101d8800c82d0018080ea0100ea0808100c00d00c540e03d044100d050f0000500700407030030f0702513854000d60091603061030b40d080c83e0510f00c1d40303000d480c1001c501d17618811281c03c00280c1010101d901204181041c0b83c41d07a2103006034500c8401c20740d40042d601c015540c2c02d0001c0c50890303082d2031f0f00301d445807240401158200c82012030304c00083d40c45100c0344560b00c00c1d1200801e200c10001105100c8a14000800030b8603a8001060307810002c40d1040001c3d51001c8050030032010304558001e03c103d9034004080320612800c001d680d0030004000031303c0f1009216080c40756840e01802e6800031080c0a00600c1009a04060240e072103894500a0302e1041e200882c1c450080400401c43d030260000e4400855140c1c284080300c2e0300341e80081c0207200705101d5940100b503030480600c140d5014110175a101030b0f0b60012800d000742520400d4010900740d40040408000d0b0042c8500c525880d1101642c50050050032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 386593291 1250 386592041 386592043
    0x91c0501230f0c0d020d02030a20040b1c0606180506040e0a0e0c1011061b1204080c01091203140c160201020c090112032307060f20031006020a1104020c 67
    0x43d00001c041c0ea1360020805404041c8141c015601c2050f840368100f050b01d1038000c440c11031481c8208841d202c4601000103020640d1500b0040c1100440003100845440300c3d0f06070401194a40c0c1e0080001076135600c4c091502c4150550300400521040f034440e0300700750802e001214254000f910114205607540017640d59401d0610860070440c8000b80740f811884a10b000103040c151000030002c00740e021b4031000400300040d901d101d03243d80d609041601c0c00c182541c4403888140d00d000e002614100814840003900319024040c0519180c41811201c0c08642c0051001e0281c500d000d0341415070001d20420000c1d00d0001030140d44a01e0840403060203c1c8446000603820700c1d11018005030071007c900000300700c0107814121040306a20a81e00c400f008e5202030010702c0400500741e010346201004000b000c0c0812166080020182c01c80c140004110145000042c10903914000421b0304100100410240b001c2d0500c0d4440201801d001908484031582e6808a5203094140030a11456011400002d5514 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 386594541 1250 386593291 386593297
    0xe030d0305190c0f05032224020705030313020a080708010204060306050d0b04061a0402120915010e01030f0309080d1101060803040e06060d11030702032a0a0609030302091c0501230f0c 81
    0x801040350390540041230606200e405d51004050450121010800b0401003061007121115030b0008080c500f15180e064a00410141918007642d04c090200b81c08508044140140d5000740f07100400146d6a510341400902910407941c01355200745420001d04001c5110344d840c195100b03500100026182840070001034900186401d03054000b407000c80c88402e50302040d20807a01071030000c01299002000041309030b850880074003801200c0b4426000410019070a1080c400101c1e01c6401d0200115072204c4100d440c0407000044540042c0100c020204941c03028420340000d041e41c0d401031840c0030b0801c0240d1a000380082c01da039005401c00955805d03030b01d03642d900c1941f44805482001d6900c0c240250000c0d40ea8104c000c0d12602c1c00803031860040909000e02c0c802280020f0280070785401d441584540c401810241800d4041c95020441114a44d0f05d04011100c441c1c1a22005003611080781050340c01c690105261302c1030294100c03a58400410010f00c004c3d48612102e04210280e41ca140700348013540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 386595791 1250 386594541 386594581
    0x1a010210052e0807050a080304031212090609021f05040509090309030313090b1f1805090702030a1404050102122101060507020f040b0913030e030d0305190c0f0503 72
    0xc01d240007003000c200ca80010b85080351800b904548580c0e455004000403400d151203101041d0b80700700410000070301041940480c1c80c210f0705041000e20b1542813083e0580340d07a00812a100da9440c0d01c036030114903010904480c0c5442030b09054170302c1d4038a10006002c0b1301c954040d0520540c8030307400182c41d04004008a41c030b8424042c043c0ca03120a1004c1e5218003070030290044201e42e03410946440c80c03508004440c608640c8082c6614a00c40b45905401e440d0129105100b48102003525404902c1e5143c1c20049800342c02e9030f03401590307a0700400302c00900f01120700a114150035001c0000f001140e0780000c42030b010180740b10807039507aa06159045185945841700d58484d20100500014001da004000303000342c1b078000d4030a0342012008400b008115598040b007103074800f5901d00031480a0100c1080c003c02141f0070304062040110203000039260005c0342070744c180000d840340b04120b207441554803482903010180406200d20b200d07203200038204c40003c848843c2000b07804000500030041d4080b80890039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 386597041 1250 386595791 386595841
    0x31413051e011b02120906030a0216141219210513020109050105070f1403120103230d0c03050d0612060b0a0605040e0408130e0f06041a01021005 64
    0x207804000140d50280068801120420040b074a400e80001e0021900c041c1060300034448078901380c900c00c2042610742000d0b00106025074284101c440c0c88034401641046103000764034060086807002411807500300a00f801d1007002c0b07070034080c4a85000761901c2d40b4140e510581400403e20b40102100f42500030b540b80c91b030f0410707800c1005000415407407012142e40c6a0003aa21144150348480064940d4071403444024000036283d030401010176000d0501c10344e0003003e542540d18145d641240b0340283e80e420707042650b007103214004100750b0208a40c1103500708012031000e171031846003030900504082041c0c08094207104000070a900072401c030364401405003c0e013106a060480050404a0051038540244c50181c03403800707400f00b0032034010000c0c5e808072154604800d185664650322508030350030040b4011200e001090300802d01440e140005480341d11840022442e030324001081100b0717100c810b0f074118814003602c24200307400e982c0400c9031803064550b008081110703103404403131140e0140f400e4403507081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 386598291 1250 386597041 386597083
    0x904020d0c0f0f0e07020616020c031b040e0c01050a03021303060e06071106010807120501060504060e040b010b12060f15130e0906060a03020112020409091103060703141305 76
    0x481c0d20844808280c40d843c035500310909848804024922000b43c0e504400b5074000e800003980540385007410340d071501c00e41c4187c805401041d4040792401803040382001070481026044419420705100780f080c28200d0400038109040060001307400d51040e0326000b0304154000810103904d01041c00741e20002c55004604101c01d20094080540364013065410100240c00d001144d4100c4000042882c10fa440705405400c0030352400b041c1250340000c040d000c4845548442e00020b065440d40314140c0100b0410b1540000ca18081c90701030840708050700100310607403003803080340302c0c040a0000f52030348170009481c000700c40703d0071600040300c3c0038442d111a04807940020301c2d5080d245005400e94100c070ba118990901e5501d50a50454448004450740c0e81c01221403c010030146d840f41d0404d142c40001840c0c01440c0c56100c41042060300c2f10300106540c0c03015074044005036411b007080398951101e0145001c00c80c62150340c0e61010000c0025051852241240c0315000c28010288444030840312080e82002c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 386599541 1250 386598291 386598299
    0x403020a030f05010e0d09140a0e01060f1803030503010e182505120d0c14010204060914040213090506120102030406060515041a13080d08040213090503090904020d0c 73
    0xe80d128481c80200c0c3d095080000d4080000b60014001120346100c0e2601511035040c40c00d03d8021840b07081d0016404110810005403040840750150301030499070f42ca8004200140601030000f412001c45030340c14540f912002c0012a41c0700b02580d054541c88403054050340ca541c0070301d56454006010351102070241c540312100d01804030038007400d10703002913074040005580d50003013284514200705001241e130003c01350f041c0ea040c4103002003c0524440c2c11001c0145041e101c17800d089030099000100403d102031402e00c0800400300011248880844042d8600560115003a1082c1e4040c4030724030742ca940301d80200d85030f41d03070f40c800380e40b10300000350021901ea2400c0d06245000d03120904c540c0e8016219031066440c00c5280000300d0b8192920003501411a80b16103100c0071550b80000300c80c1c801103d501001040e18032090050b9000d04501d031383e443d2058141401041209100180244401860112a0030001d20b011007600c2201c44210344180490391140042000c0c0300018200070700800b40c89002007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 386600791 1250 386599541 386599553
    0xc070b07030b09010f050102120708040816050901330219080d060503010b1c030e10180503190f06150806040501051b270613080c06190804080403020a03 67
    0x5005001c00710f0300003440343d0341c0b44400f14141e190b030301441740160444130607494004030031001445251702c10990302e49015901d010f03541c00d000382c50202100c0d90814880800092078143d8145016016440c0307200c00034866404050012211005003c0c0c042c140c0354451078040e4000d001c0e0168000309010804450446858440d00c0e42c0e000090940c030652404c04045140d050510401000321400360204406030110040500f0800b0407250803001c100c000d100000c40c41e2209554642d8201c01c0d921003410801c0e00032401400201150480e034000d0784408920100d5200c503254944a03581c07c1412141c940801d0305040c0054502c080002a281c0b4071144001420907000403a40e105078000c00003048903840f03142c80045041050b01740ea23403108400b40940083d006544e5555040060f403150152020350000003c1105908490a071740c5607040c80190410901d10140310080710a101194614a800c01d0385160150720b045980009082000000006041240801c2113070080c40d00141a001d140f07079689008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 386602041 1250 386600791 386600801
    0x912030c0f091e241709210705010606030e0f01090804050103020a0e090403020a02032109061b1209040e0f030301061809020d06090c0e0a17011812020f0601030c0506030c070b0703 79
    0x113001550b220101d083d803600c00300e15240156020030150002d880d106580e03205142d07015001210301203041009200240091040400800d4151004a00740c840e00d01001e0422107442c411101a0b4107282c0050b000600d81011101076a50909005849102c4000122001080d401c19030340c000000c0001e0000345034000550394101d6100702c2c00c540d8907030b101c00c80101d142d56034040c0041014005109544461070400040c2105001103428054507842c1994035500c1e1951400301c02c2c2d2080c130006400461810940104604c5100520042c4105010303c0320b016501d00c0144a04820020501c10201e06d03295800702c8840144141c0138150348504045480800604841c401c4248039032414000d40c0b9101d0052a204100b91401850075a2851600409961401260301e00400359543d81000300401e0750340315005161280120500e03401c4c60307030506029142c008050014081640201c0040002a030320002c0201941d4013500d1158070398030f503070003803080500661000512030388202041040d00f541c55888 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 386603291 1250 386602041 386602109
    0x3050f061605040806010302061b060a06090c0903150b0f090a1e0b0d0209071209060b09060d0b0403110a12051905041421010912030c0f091e 62
    0x1014502030460090b69284030700d2042c0d49040d0810b030f0040000d0315210016056200c40e030b82e0051301c10894520240d040440c1103a0116065903240f05c1403111210501c1211500340c030b2414103204060031900e65000c05051844c03040842c9441e0014440c16132150300011580100140036140c140c1440290035001e4030030400714046c01c040d2582004809a040c0c0145103078080f01a00c035aa601d13a16800788035030000300030700c0c030414000c80602d4000c000b4924469249214000c420001e0166080030030040c0f0050003502da207204044500e401d070302090b88548071603000b0390b042c242003002c0c28540762914100740c0000005050a1264509100015048001000360074202c1c40e14410b035801006040e90035028a00840c540e4030b204036020841030030049090030b5160752a1040350b540c042d000000b1800c1d6940100c0480f01c0090380310200e002680c00d8001c10340002c20b14207041103200304041d002003518600303101d0804020001c1030401c8515200b08002400b8118000b101400840340c0070058402c0e00c0c3e400381d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 386604541 1250 386603291 386603311
    0x9020d0501021902161d0a14070201020721090e040501060e150906010206100b092d031005090d14190815090906070f0210020a0305061305070c021201020403050f06 72
    0x105c1e50304000081072010907a03d031400550400e20170120010341c000801841c540b00e5a58560906020b1082c0010a92090b5496400980d55820320300d05803600e4000c004100d0361907040707500d100380341c1d58201903142c040c0d80706140590f54070b55480c00c055001d0f1996500461000c0108810f0180390308510b02e0b5400700c4942540c1115032915000e004903038408003182c01804100c01000107101046000c0010203002c00003e007076050b1151154011079603081d80302400b240205100d00030136003608007072020400c502192001084649404500982c840600c0000d903800c001c0000c04100048042a0a40701024030320b9002d044ea11f008100d019004040c203944a001a10b101d0400c002140b03041045a8171812015000d810310342c82e41a0b06a074151251000d03802907000384982e44000003146d10140c2004c26581e5000f0845080440030b00400c0c0d020032220710031032800c1c182040440e940040000211940c155460503802290381e40c0c20340207009581000f0401d00454111101c181d20002c3c0c414040c400c1c004c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 386605791 1250 386604541 386604553
    0x1318060e0c030412051b070902030a0c02030703051903060b0c010903030f0b011b0507030203120901080a02190807050412082101030b040f0201031424030c010e0409020d0501021902 79
    0x1d9003440032800115001401000007a601c880a24800c3c409400e110aa420b171000d01d004404202d581012030036005080d45540c08010030051158601442c20740742c6881c00079614040e05901e009000d44281982c0580f500d642c00c40c000400d42c4a94001030040511052076515201000c2e01c0318080c16031480c040c4d00003410240c07080e525021611903100c0069058641107060809410540c1c0a480505015122401402c10000258400307019500c06a0301d0700c0e0310680d0700d80c4010005803500c03201811954031244140507401300d030108004600f040360103509080010f41e4034900211000e200301c0d080450300141c400c450004000b80c8102400919022402001f00d8071001c200e1640900e400b407001a20001c8450086408241d402074103004a900600d80401c2c00101401c01ca0800c1c8000e03180e4542c800d441c00001400940c44010201c940902100074189564460000800110703440d941984515aa036040904655074100300519440d4410029502d9008002802c800c07514401340410240c05a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 386607041 1250 386605791 386605801
    0x6010b2a0a0c0506030112021504050d05030a020123040305280c1e0c06050c0a0c140f180615041505031915090f090c2411060c1318060e 60
    0xf41045d24140da4001c640e60001401310380030088003040114541c81c0c441d000b0000440d40745c4803020300245081c000d4000f5039130b548210741c00070b00b19202d82c240440c94400704040030b45000403c00700682c0040c0c0501d405a12a0540d407514980e240d5020700424905000441000859130010082d001c0c0d10b000d6198286000200046111050003020000f0070303044103c107083c01840e00820281000045400440d0100c00d0a6661819a88010b4201c45900e50368a24107900c640707400d600f0500e0943d01070b544203440fa01c02d42006504000e01900c058030031100300540601c1e202040c01594000d10300b56a0340c11186405513006840c503801035814825007007441c5007160364640c860141842ca8000c000700ea1115a1070010500c0061810200600c2d82070345904a040205002d020007a01074802c0c110038142c016110101d01082c2102c1040003021b020206407420303082030012410380d500841c0304954030b54542d07410706400400c16003a0046415014501109411400c19a100c0400d42c1c1203900399840a0702c0b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 386608291 1250 386607041 386607049
    0x1e0510120c05090903040e10090507020102120103140c0301110d061d0703020d06051809010b0d05070312021c1e050309030a03150b040e160806010206010b2a0a0c05 72
    0x854003018240840080c0100400c0c2000c1c2455507202c80e800c0266420141c48004d405840c21040c0c0b144a00c00301442d00c28080f0311700074825540c010342c89000844c80c040325072003070510042d0140b10244c9241103031440c1c8035a210060100c4c2500d000c00800070818651402143e14480e08500311060a03240b9200c0701184507031400c1d0300d6402d0b42c0c02c0e09909030b610759904441200a0f5118442a40d03046490350800511610780c04c042001d0700b4002c1701c024040d498821215421200c42104551140c0c01811500c03000c00c0d004503901040e40c1c3c2011181740402c03640d0500341d18184108411111404a0000e0130603a9980107003464085075541c0d102c0c00603042e00e40c0302250f59010a48008078640c104003d0744195038001d900c580b11058642108070b51a65944c890850f00d60031682c031201d03500810f1005c0000e03402c84103000d080c8180050a01c00d54a09040c80001e41e2400c05000b280304008001800d2030889044612848001a981d0050a00100c400b850f49403a403000a00450720a070a8030b401082c58a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 386609541 1250 386608291 386608319
    0x40e010608060a030b0a020d0c2102030c040e0a1112100b0f0405060306010306181d030a0516080706050117060906070e13021608120708061309061e0510 67
    0x1d0020040c80400e0300710b1311740985003e805041c0003286a0708000c0844407401500400c902090262150003105900d0881080b099118151216415204001700415054034106503015103944100111095503000c9a4a00030602a003c80b41c640742c01041c60100d10f003103000010b100f514480584042655112041c0c0382070b001d1200301042908080c4001d0080307081601c00b85500c21030500d000701d19141d40e20028164400a00c00c00e181a40d2a00e06050841011504051404e4645001507141507043c0000034024003a41c40d01002c030800d41c10b801401d01c241081554200b0745c21000402555960354071014480b01020801e0710603006150000341710320404245540314207056215248010190010004000289691714541940c24004080d008544140c1d0281e280c3c86504890ba403800130480342e15448030002c03e03410400282108010040d262207881ca101008003110101c2c2000700e40c540030001d0583c4001108150941d64155052040d60790001d0b40103070355158040c410b541d00c44001060140c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 386610791 1250 386609541 386609551
    0x61e01020c040b0f100305010501022a040207020a080318280308161a0601030b0607050705011404050904030309020f0a061413080303011403070e270705030d05040e010608 75
    0x10308000444255410b01c0c0e082561030b244020800181410910002084814800c9040d03000a90350401406156010030414441100c0d114003040c030703010303a0101007030300f100500e540c0340c0102e07004590201191900300210003c1c0409105598640c0c0c0350540101011025000c0c0700e1140e41102e500e00340744510440c0000c000c50542c084612403034215185c26450b03520504100c00410780d61442c90011512503030b224001c60110102d90780c0070b810400001030a5035402201184078110400140002070f50000300e03c0c084442c2130800709a07401d11501c208826028540c01a600700181100308400c00d541980062010342c400c0320390896608452041c000e043c0d03940e01420001c1064a00d0181c03ca81511000e8141840544075540f04c940c1c1380e816684c2190000c0c3d11001c42c0d01c0c512142240075160911185000d03040440300300303101c7d1502c0440820f441103401e030506074180545412030300c002e10600c40400a007202034206c3c3ea9200025200900da42d02a00ca0040300280d088000700b05180b194561754011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 386612041 1250 386610791 386610793
    0x1120501030b1602120406020609100e1f09060f15091505010e06040f060c060f110d1a061b0c030c0102030304080a18030f03021507021b010521061e0102 67
    0x90b80d9495521908990544205065100e9100700600b0170501c24001c0001e08080d601404a03401e00410807071414455a8484d41c41600744000e07905009170005101030000000348100c4040245050038000601904001800729030400c0300c200d04c8021070740c0128248203a5401242c0d256503540e0016001c03183c6030704120241a011400400c882e40c4a0f100c500715248005000c5c61900b6501c820b030101040c1c00e60720031008540560b5405082c04441d11071181140c4c50b440c42400000089011500b19108503043d0036101d95451920320304400c01c071440081142c0c0090222075454030030755102c992444440303075804003900c0303540c501c15810b08010852054108040e0001d50031034540e9650300a40c0d4108160340d008000000390400d00003003200d400f04001714081e1840b1284c103580d9090081c1000310455080048404e000c0c107028000d5130025031004000c21105c60810415a0b160040b5500e104039904041124961040c2c54044c120601c11035000711011100f0202844911090b0751104940c0350b520303405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 386613291 1250 386612041 386612063
    0x1c090b0f03073207032007260705102c030d14121905010e04030801051207091e02070c0801201207050705010905060a111c15050a030605060112050103 66
    0x3000c903010b40038140042c401e0400e000042d42c1c4c0c64030000c0d9000c04142854041d802080108000d8004005280c096564405040102306010600955071421407094502501079a0740340c004c0315109100d001451a10030134028840340c800c1100c52140c41408000e148a8001c0f80d0002410780e0250103400e8000145050032401e05c8192001226103050080184403d8400001828881b842c0b500ca054064000002c10844078106400e00819400b41600001d020b40d5200c02c11540307180380003810341c0450344c0308600480d005460045000480c03140c40c800c402050300101d450020040c054501c0e4050301c01a000810001400c3e5111400d410700501c00403c3c4030104100040b000c03140110160ba00100c1c9052691070803865540c2c480c03c444940c20203969903003016091204582440c01200d00395124400214201035140000c00034040358074000b030400360340d40d010b01568029a41da03c0402414014100205240d032030030300102804040760034500003003005103480340c200154481c141c10b0b290015020a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 386614541 1250 386613291 386613377
    0x140d0c09120317100807030506010609120f0f05010f1d060a02090a090903020c100302030406050702010c02030d0504050c09070815030d0e040f0b120a0b181c090b0f0307 74
    0x203910f1001c0c0c1140d46a03890030300c000c01d2070001040814025031003840101865890b00c04002c0001651344c01c200c50002d10422401e02250f5084400c40034580c00403a62120280b29280050041426003510740015041400d80c0051006031600b10346440c1c266400d84044c0e64070052075804903ca1482c80f00e51041203e802407002c2d20b0700d03510101d48603120340100e4280101d48000281c2c0300341c4019900e40000d0300001040200700c00f078010725400541e140000c0c080c002e071108000e92a402a00907076174401d43e5807030000e41806070402030300013104005030150501b4145100f008290120445100b128200c00d40f01e010302030b050003e012031200d00c01e699001d40540103081000017a0891030303c40b140391503c03410402483e90f1404c0714000a11094002464071012502c0c000914550007014484145174600f42d00031070381c0e40400c030080121164500c20440e288000c40079a01c0e02d440c1d8100311310b001008244480000044e00055008019940780c045201e032895080c03654a14001c0c4061110012058100c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 386615791 1250 386614541 386614577
    0x110c1816050f0d0204050f01020a1101050c0a39080304091a040c020f0c010c08090907020f0d02030441030c19151706010807140d0c091203 61
    0x4840c1280d207040c1c2d20340300d02c155100700c00750040707800216019130000d4100241c0c603050210120b0003000780060803814865803624901d80305168201c5040c8800015090625402800000102a400b0f0052070b0151501c01c1c04c50750b0f004d086440d40c011280382c8468401e005480000c40000c40d40d0210045d4a0541400d480344050f14240420758041c00700b200e511109540d45000703055000b5001d41c014201d0704100d000c82031400c0c110b45070007414000a0384460011500f95070480d200010255104031454072602c50407407415004102c0c01250b401000716080b2040e50120040040b10101c020490787c028440c414500d0150480311201c101c0856850324217201040c03040440c04280c0014152002e0f41042d00214191503030a0021694010b410030090158a0b040300c0d0f04141ca07c2c40b458031840099220b0303900701c08010041c01207811700904900044119118210700380800e07078564440c42e201c8600c035640c030001d800c05440001c0400c103640b074080341000011100040c110f07059076885c034104283d92100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 386617041 1250 386615791 386615821
    0x60307030c0510091203080402010216050904021c0b040b0103151a040522050304150306030503160f140309010906030c0522050a0b04060f02120409021315110c18 71
    0x60000e218031504c0000b4580c0b0804001510320f070198a40c0100d511b058400281801c01c0c000302c840c0b014240d440244200d48402d1540350384158166960941d880006140c40102c1031080d00084c0b0382c607400f42c10402044050f1440354100c9201c2c0c140804151208c1808100303880c40310062030321924543d00460304500d403036005617410074014a807c14000e03601c064548581041c545051700c56a0001804105c41c1c003610103031007000195841e040124a0850362100d40720303c10143c0480c2240014064903007440713183c01080c000d1550001450154008080d4519103035042070a1443c04540008000212a8041d000d0410404a5682c45600e84017000c1c9007401d03c06550750f400101d4031441803011070035468002d00c0801402c10210f00039181c6141410042070b00306180120301c210f42001c41d06094984022068030150340545001503190804042201c0b4480e241b0341c048041ca031082a0900f8426420070109519100b040003035420911081c0301780b0000117a40c1e505049400224400a20001402904 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 386618291 1250 386617041 386617069
    0x30708070f02120304061710050a0b030c0d090c030302060906100b0f0708030f2a03160e4b0913050114220c0501110c04050c04030b060307030c05 64
    0x44840b5143d100900c080c51600a50004000b0852540c0f20000305032100b080707c1e038030003c02120b4100300b0f0b003807001046144880d40b141c100301ca403000c0041542300156000740c80038202c1e00c410411240c01c8a003450002101c1b80d100030740143c001d010218602041c04114180b00703200240c01c609941c0e141c048010441d5000c0340501609400a01c445800160041c1c015401001c040c0001545410207990603226201c881c090070140009804604a02803029800e580d44614040001041c54401c1e0030140c541040700300e50b807540080c80d10640020700540d030070241a028100c40410344003036030f014a2450a20040e65520307500d041c590074410600c1c46c01c100d0751903200020755002e607105074856032242d003035614035426155410003000c20032290a0321002c88026412805900c484070f54140d45803410988180c1c01181d0402100c00342c3e035204100c0800500011079006403080119152024190100d40c20038007080352803041c0c180129100740340004450055036049090300c05514580f4040007840511031031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 386619541 1250 386618291 386618299
    0x1e150a170d11010905120301030c0602061603050a0905061003031206030203100c090315050919021c021c030203040801110408030d0207060b060a0e04050a181407030819020c03030708070f02 83
    0xc50080061740600c01c2d0800d118070760700c4082e281c0d4113625000795165025000702045502039010000d43c1884990342c000d030100a41000607140d02c41d00d5504001c1c01e049440641a44036420a1140090030510080304a9010b03640b086c90001250120710f00307461a51101960507440b08400b500341c00b0301503009107040816810700407a03842d929910718500008004400c1c900b1551017040000800044c0321105500340d064403038203001c03c2c40358002215440d0108071002d055800e0b041243c1191a04001d000c1c0c0e40c204405081c0300c0c02d000f0314000f5a02c1c1d0003030203240700c03070f5007402c240b841e42040340c8040e182922002c0b006103041c800c012508800135000580e050b9012920380c0c0c4240303029143c080040c81e003030105907a441c1121b40210300780810f9540251a1000d494070b8040c00740c040f6081095641039080e407080ca50030b4091758842011349008159080a01401d000041c9514940071860360469040650307000d8511003205441055100d00454a0240a0100030030107000010008084e080c45244014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 386620791 1250 386619541 386619551
    0xe10240e090c0a032004060b03041401061a07051902010c0b0919060506040c1706060f210f0a0504080a0c03030e0609010b0a050906030a0b1e150a170d1101 68
    0x8000903c0440583d0096032160a130062280000d4541000031031210303070550b400c0c07000610f80080c2c10f1292000520140010b007010381c503030031407240c00c1d0807403001061101c404000000140c03a84a0701136000b440f08035164813840288103002c0c42903584110fa0680c0503101e6100191060300c40c51115a00105502c5150090f4003101080c80d0005402d031495078081c50000035103240c06420310048400c100c8000081c0300b0204a007007040d600380341d0030a034048010303502240c0310410482d400c600c40c0100c1d09100c1c0c24261418a2420303e81144003968807d1407144200764940d01d490441c2002c03030b40c0c00d80340900400d50800503408824002c1ea04030102070710070310700000e040e41003100c00c40c2081d40075a000e040c503075154400007105240910880001c0d00b411280410141065070020355035141c5500b005259006400004000c88070100031902002350b0075001207402d01c1c00c0c8800700c140e2082551018800c2c8499480860710149003000e004040780800014074034a81b1040c02070304e58000070700510741c09648078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 386622041 1250 386620791 386620813
    0xa09051e1308040e04060609020316050f041d0a050c0c07060309030509030a03170601050c0712060e0f010204030302010f02270406080708011d0f03030a020f09040e10240e09 76
    0x1100280001d00c060744a04c0343c0e5041502d4a402500d1646d070250182c54014424000090b04001001c911000c840c200300c0d0f5517440c280103000aa001c0d81c0d2200040c0c0080051001042c908003100038401c81c40e0080800455565000201d110700900c0c0d000d00d05a84202404e01099020b94040c6607280d00a080c058240b000041c0000d1a001200c03200f1000941502140c0703021944d100d0b002500b0004c2424120705150035607020035a509854461f0307042c00c4c01a01142070074002c180e44840300008a92040c1ca0300780d44440c030751038041d5020744002c400641c40c4c61108000d50b51a48203444002c1440c801e400d01c2c52800742241e884a829050405511607582e08002649110400080c1c00801c102c10001c02c00411480d0309840100c00100350210640101915404490011044a82c001031650340180ca51800c1c03021042a4092984000d81252400c500110700303c50000c0d00c10301903c0b442d10148505502142d682c03560800000401918240c0000c05101426001e202198050213900454002002c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 386623291 1250 386622041 386622053
    0x316110112023615030a020c1c020c010815091803030a0b1305100611010b13090b0a0605010e12030c0a031e03021606020702040e1b0a09051e13 63
    0x200543c80341450701100302400b19030b44810310306100342d110840006840550301c40402e01307003018680290402440040010b6007803c01d0750584a018007903004440380d0b40c142000c40c2c40d80142d1260170601502c01d5080c010869071003003181314450400c94000b0700a040780ca40500c491820058080402e0110403030300030303054040070000786115140000010480100540a001401000014140500382001d0402a0300c03111148a001141c2c40781c5804100c1071a0402a180140080da00513503016841030281c50024210340c00540d0f08030b0007601c000303da9403110900b08048410074071039507011034240e41c48201c071441c1c000b5034101e106c0c5e00788080c1c0b850003081c006d00504080303008400314040760403000050708042c0100340d4981c181c50503040451501482900d03012101c48150300040003150006146011505c4a07080401d104007110704449551114150032005400c114603a00d000303001c01ca84c00208a403071402024083d01d8100c180310103003100c0c0c500358429100010b0030095040d050209200c00a10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 386624541 1250 386623291 386623297
    0x6170303190615030b0f0415090b031501210606030303050a0b01050c0604120302040e0901090b092b11010c0c1b030206030c090301110a03140109110307110f030a0c020a0602031611011202 82
    0x2c2e2010145108c50414602404a4030a03840c06030203503100030803400c07884c008404103170305403496007001c1c03004c009624040800c8500c1000001300b01a041c00c40c00003c0507055001030f40103005015040c00010300c030100440741030140740c80580c03581e0b00c21004140854020b11401c198040c20345030142c50513407070f003031503850b800401d9450401981d901c40014041c480510011a0040040350162142501600d1116611410714180b0034181c0404451100458050010341c14199035850090000c10001e810290410101c0903007a1111050301c0f1138040c461400303842d618284d0f40d004101170f046032560240d6400c00d421a006480d0190742e100b03001d0003220f2449000c1c0c5000308441d41d010a4005417042820b48171170040c0e00c0004080e08100040e03040e94545801e5a0340983c144c03418000800528102528250006013201f1003800002441c0300900e81c44000080b5841c001e03285c100080e40c0d5100f0880c3c0c1d91041000b0083c0091002140c40f002607050a10a4402c0f401490083d100c0e28402c502d00080303074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 386625791 1250 386624541 386624561
    0xb1512180708070e01211127090706080907090203061305012d03030504060804050115080c0a150f0534050c180c070606170303190615030b0f04 63
    0x142c00f220007007003400424003400d0b02600002c10341744104120340a0030554184002e000804150004500e205152240f424440c80950765180e1000c1c901c060090304080b0b0710082d00c08405901a4040102e43c0f2402143c0d51402521084010002686801c12803002504050042644500c100b0308a01c03ca51060080328040c18028091150105800e81b2068030380302034401010001c2200c40741000440c0c2c102094800700c45e0035040a242c6541c031450b01c1c0740189490f0604080560b50040081140400007a0b0740e84128010b03200012071544401c1100d0911480041c034200003401c500e40079800c18410360103885500c60101c48001c92501c40405020540302c909568034214280300b1100084c8401048407690606081c0c60b4420300f81d8003101c010403400c0c0020541d14142000081510801c42168440c030000d001c102c0c40b01550780c08015a41d03850b40d1040e03503026128200c00030741041c2082c0d43c0c403528040324a040ca020000d0424004180c024010f07102103542c0c000030803204038440b6180d40c001c4d07a2501c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 386627041 1250 386625791 386625793
    0x31602120708120907030f061d0a110312090a120f0506090c011d0906011413150e120705040f3c0b0d060b120a03030f0b1512180708 58
    0x800c074507191840c2d0202c0050080b00d917a030203da0100041498102030441454001d440401d5880041c84010303644d0141801c1240b40d803090651f01c03414440c506901e80e9440d0400c60968080304e02040d08204903015443c0c1e490340c4816500700800c504204202e02072085407050070b0011080c581901c9039810864115400601508100826100d960b0702c04c4000060000c0f10807000001000304002c41d1011000901c940c0c144150807526440d500000c0040d2041d00003452001c4124584586190a410b803159045102190000050440ca46040c841c10101c0344131500c000c141007413500c2c0404c00903186004620100c1e070364444807800200c08034070110403402100c4e411440c0034000e0800b03000e0050340032803070007029900e4510759103402d5135007007030555000d0703044000410310380d403040c0c0000c031904040d1240960510610446c04101a007541050003040c6100f4800c200c215000c2e8248038001070b5180d16080c559800300001508400d1000195800c124000b640980b0207480311800761801000750424445 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 386628291 1250 386627041 386627047
    0xb1e1c080c0a031403040308070c030e100e0427030507021f080603070906180e030f071416031703040302070512100f02040b0913151401030e0a08031602120708 70
    0x603d5008401c42d503925411400c658179514040d100100076600107403000c002c01c0222903070345051601c01c00351111b071040014000304950010301c0018040481d0100e00ca4015401c1c1040c1500c0501403104080c00380c0020030841d80b540e600c5a50450360b580c00088202ea115040224a074100f420703a05800703000d070603e0303101c1200e00e0410004061070101198007124180f400e01005020078245004c074909000b00c03440700402e00300d0280341440d041d4011140c441e600300e0004100c800607c24440c0340818124006000d0b130340c80d018040800640c414060002500340c0c901483c0325044603160100841c1c1c040d01a00c161500700b41c0b5003000803200d50002d4a00382072648019040f0400310020311801803000c0c403601c0114585460058a4810741c01034070b01c0b442c402c446e2850510302151481e001030200300d0341d903040954200c1e100d94048404450403692240040d107000200d1000d030310005114071031290401c2d80b003030541e076400b48002d10065a02084408500076000e52982682c00d607400350100030300c03800300161 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 386629541 1250 386628291 386628293
    0x3030f170a0e0c0405090d0e18131209050109030b060d0b09060603071e0603021b01230601080417180910031109040b01090f1e06090b1e1c080c0a 64
    0x11804050400041c426417400f03040c050603200c00a200080786549080144480f84a5400036100307682c10f82400003100b03c44000c0000160b8200c04200005126050070405007520500803111a60580900390210300c4048091000c19000d5070000e60041c0d0013080345107010029520002c00c3d000c150b50307980303043d4800810b000d41e91505005034000b922100135071a000044208030b04040040302d105500c103056000940d80c80042c3c00c0c076222546040070b42c0003402101d0b4004d807601a00f0713074086000030a070b55850002c50040c2d8031541015000c1c46c4c11103030300114581400d0140901d903204c00c0a80c0b90300c0e001d02c03a1440242d164641502e00c140481e40c01e0510f028a1403c040c080d0604103a0014428001d4208100c0021600445e650542e00642000540140b0740c410a50041002800686003421030f00f1400c88840066088142512030b002e50a00c100c031017080501484420400c1c901d61109268040340d5014200000700e03080414010924810501d125190b55095501c03030303000e078807280d008041904 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 386630791 1250 386629541 386629543
    0x703030c12140613140c0703021c0e100504080a030914060301030b13110a030b10050420070501060911120610091512111b0a030903030f170a0e 63
    0x40d01c11603800c005001c0300800100c414003481c00207000c5480b401128884410340c8140d503021917104142c20b0b661101508010340c0707a2001c1d400100040b4018030405c098902e1200c0080d11301070711000c19031644840e0303003001e104100c0858021000e0394200541404001034200081002c62004d078003d84400c0c40184c201480c071812a41c0c01014a401481c0420040001800c0000001d6106c003050540035403203805c900e8034543e0b540b1a400280c1d0310161204001c018010200070440c081c10080b9580701c00c00e03a6490074401130700c0607000c103d440c8030540c006100b013803154000100004c80c032981c0002040f035110180a4200c0b400645c41145014000c2020a26903143d500395a80100703080b00c00d00781451446000801d0910305002d240000c41d800450030008a00031031498907038420f44441407102008000840384135800c001c0700030800315141ca910300035003107012581e6031481b5019031303c03095850705585094445d03116105112041002030300328810381d002c0c0828882e00668a500000c01d41302440345043d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 386632041 1250 386630791 386630807
    0xf09090f0d09090b03060c07030507050304050310270302030f07150f02070b090a08071104091203020910141206031c0f08060414010303200609060915040b011809080703030c 76
    0x124044e41c1b040003800103c0d0303c150140c1d07080544c50300d08540c1e284a10324104c0c0c114021341d84605d805200f1540542d100c5860307a003000c42c034211401421540c107858230180010300e031805a00a80560400c0002c807421071000c50081c402e190003512901c0d50746502109000c1180c0c081503058400690105121017040541c0a01c4e030780020703808008103107400c2c81d5114207915204051006110701d010a49490b041d03140c1e03810108049070004125450400d14800244c0a503100001583c880c820b035100b4402a94014103505200088005034203041581c600101058510003070440780e8148120011400c025401105400105459595102c0c4141c04124041c1c1001c034040c1070b0300e1040e0700788070010004c2101c00c8040c07030443e42c240c90601130601c040c0c0d60144c01110030b1140d15107103000c1c0c0000c1280c00d80b40020000d014600000458041502d04284204004810b0320014500003404004100901034807041c586914050300000070301c440c840d0303500a802c0d0301582048000c203444d0700b04600180d81050003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 386633291 1250 386632041 386632061
    0x36080303010b0d09030c0b041104050105030703080319090215070308060103020415080402190311030d050c032b0c18151b080d021201030b0601020a020f09090f0d0909 73
    0x21415941032075005001030040410b10b00c1071590341c090700c1050600c180a01580345405c180880c1050401d820038a48181800001d40d005070300b080b00006550900185140444c1d8206618030300355110b480152006012100a01204070b40b40c032903080c05640c5084c0031650300d4603601e005542d0b0302c405140140c103c4e030009051a06141c8140810010111034038403102218181d807810a00943d513520000d60800e0250040c19880b24001002000b000100c00c01b45840705021003c81d9100c0c00d04c0300084946100b04401d003601500b0078403103000c204001022280ca200184019405084100e000d0348003200d8913483c5543c00241c00300000200305001640d00009000d60192494100405500190455650407030303681c165591b4505c0841030000940035603e20016145040d55200ca4000d62109a14400e02048c1c4000340c1d803001003a45503000149403c8030a50103040004c10b90191003c11009005c01891056207000d4040303400c0905405002d040c160a54607207441040905141805080340c4003500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 386634541 1250 386633291 386633293
    0x1306060618030b09010f060b09011106100e09010605060f121e011503060807060c03090b03060a09020c0c0d03020601062c06301902160201030c3608 65
    0x14040a001110304074042580d81011081d8110f458200c1d000740140b064800d05c414544c604000401d54020366401000511426038a0310750392a1009052034603001c00740e662a8007070900040812080726290140c1d80d201601c42c000141c070070340d20004155030340d10040b410300b217451001a005150895066400c0c0e00040d400040c3c00602103181c0388c000220b401030051008081c441c1c4000111f0718400d40000c0050500c2c1400c0e281d0690381c0310800303040360708003010440110b4103540b00408e0069800c8140c91081700b00030008400700c0e14240d040c5000f50f1181100000071700440c40203213690b0729041c0c80510544e01c04e90040841358502030f8014040c45c0ca604000840c030710311034451241564880b0603180c500e82d00311046a6034060031104240d01c0f0180e14010281444108404611070b985451202c0c0304101e108404190581241028403c1744a002d844103041881c00c203000c00594801d5009260f9150310b030400c01c55080488015064050b0b8010112000c401c0c2001c40c41c0002048000358001894608 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 386635791 1250 386634541 386634557
    0x60c0c02010c021c170703020606060f0a0f09270c03020f09120a0b0a0c030b0111030706050c040b0d050405010b120706080c190521060d0209060406050913060606 71
    0x980001e00d42ca2244001901c40d413250000580d40701c6140f0341c0603a0265100740b0544040e41072100d1900240c00c80303402680540151000500a414040d0454007a112141900382c0743c2507014101f038030240c2485411808011307204d000480c0d1105404514403504007a803410150a002c00741001043d40d03900700142c0300705401408054403818440303041d9061a44d044560b818001c80c3e00302c80300c0c40c1c80c1300b41c4000341100e00550f060180d00d288075849000180c030030703035800c0c0411480180152490020b451880e0320540c020445000841c206a02c100d030800c0c0100384a505d816030f079810b01c6010350414a1040d0001e0741c1d034000d01040000900c00e0004c120000ea96240d42c0b0603010356101e80310f00d91885100d0a01915400154280e02580216040252034506005c00c85800680040ca541c220001010020440306c4104808940c3d8158583c40b4500c0240001c401e00350582c03e000364410090011500103403a000b0115a80c0d0324244980c2c0700307141070720018000e40b80030704040041d5000e41c1e0141e42400040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 386637041 1250 386635791 386635793
    0x8090d060911030c0a1703120705121b0703030c030f1b120603020a03081c021803060618011202040b060705010b01090905040f0f08120708100803040b0702040e030f16060c0c 76
    0x20500d944c08503482a906ca04c0301c0c2448208890440c407492910480d40041c070010440e416070014042d1000b0912403070908003558541c80550303882c1a0202070428684010300501000038442e03000740c01240c0061801044018110b4a800240d40c81300014282c0421003032950090558446c8500810009208051050a207035402003104c10501d80809400b90340002030601402c0c1110314580030a81c1310070400c41d591250035111043c4986049259807090240c400822494509689002d41c551204940641164a01010404c0f880000700049030082c0e02d4a0780e0102e550f880001074850079006400105280303416a00060202d11941c01000d10749241106000200f50000c1c00807400f42d90103554140c10740807c0c2040a414060540c01c00150301040007000001d640c0550300502490703d0040c00f505181e00c4102c4030b600da003d107009000303010009110183c0580b0b0a5041241e001c0d100806981c0ba020072902c6864280c1e01a55105094494900050040082e035102d4190079000600c4c1c1246103080c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 386638291 1250 386637041 386637049
    0x7080708101808160c0305011a19090c09030b0c0301081212010b071104020307020a030219111005120a02070c0e060906010c0c0801060303021e01140a050408090d060911030c 76
    0x70101c003800f201c8001c643d582d50b401040c4403130301d081038028200701041a601c0c5085406400c0482c130105d2000303210000040c1c24100100454030010300c503410034034070300d0a00000c640185140c420080c00c20a082c030000021480e40303075107280980940f0158a5581d814459814980540e00c2e1020720744e40400c002d4660020101c18445c1d041d65445807035950358900d1814401e20010160308000d901c1440001800381c05500069582e5a25210307400341c1d071a000d42c0c01d807518480814440040c01034038001114a0031351502c1990039500304090b003021400d00d0000c1400c81c2d03628404480f14001c0c40d500090a100344140850020b004009a031900f00e410f24149004c80c00c0707803001400b21414400e01c000004100130300c1c04000300241060f074000700314807a641c0c14000c0d0740c1c12841150007140d81080207411021141030140e01298200b44070030742400d07241d201a20009050046c01501c01750000d0005030619a02d10302290a0b40303004420100b0140824141041001a0306040314400ea11929114031302d521 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 386639541 1250 386638291 386638331
    0xd050c0a0308070e060a0e090709080a03030f020c01050f01060e19051009030203030a050a1b0b1b0904050423070e06040e01060506070602190e0906040e010e0708070810 74
    0x6032524100310240c55900003034660304c90903500d0680c00113001c0f0700f205007103a001e14502038005080f1018451a103640388140d480c54400d000300b0005800c01c4140e800800d029820811001042e040018502105140018212201070721081090b8044d1401080403da001c0e400510309601180d44c3d907201e41190500781040c400e04e10985000341c0761002801c030428041c0011400440d0080c0c00d45e5a560a00d000c000c2c4554003684520002c502c0781c02001ca84505040c14119200d54030040760196611008110403070b1000e11501403850302d004016045070b648032030140714040d5103d00c0344031850b0030900010038040c1c203003040c104c9941c0c0d00030841000f080b4103060300b01b80c00800a07030740003c08140c03481c0b10b10302601c050f80001d50804800100c907001c2058590041c40c1e40b400901500441071450b40041301c00e1441017010300e9001c07842001194a600d0240d00a4900310309020000441c51a0340c0c10660401804d644080c1e850380180b002001070f0001480034030800f040c9807800f003015110100c1c107250041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 386640791 1250 386639541 386639543
    0x6010f17040b0903120f011a0c030301140a090213140607031e050c06240303070f02040f0e19050d0314011208041707080c15070f1509060e0d050c0a 65
    0x11050b50b0100702d8180c0140201c5030a0005000c00510514240c02502c0c1d2211081c031a0a40450b0b042c079001c04056199010360f10036000482c00f031887c0d41d182051b0400d02d10100c0700007551020f4020701c0050046191300c01441d8410602c0c2e546100d40b8039144001000030a4030041c24043c0c1c00400c5150b000aa000c011000042740300f40001d6050000141c040b1214024000d403401203119840c18414184501d910f15030f003c09040c0000c100c187d804405064590044c0e6100030000310744118250300500c0c0940103000344001c4e2400c00a10110140c3e00c3c86d181c0b0f60915081100c150341a5400d2045c80010b02800c11004400d0400f400394449103c15110a154140309031040a4011401d800c1040401401c450090005284891000c108525070319194180c83c410306080d44662045203066050803484059840304d400ea0280c00c15500e5110b00d030320b01d082c40390203c48800c0810500104c0310010300c110f03103000d800781000043c041511089549451100e01a03242482018000b603800070030005400e01c83e071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 386642041 1250 386640791 386640803
    0x50306011d0a0f020f0406032a05180303070b04030305040b180a06090c090501030309090606020105150607020d0c120605010803030105062203080f19030c051905090a0e06010f1704 79
    0x110780310a00f40340080c02400d005401501000400084250703044e00441561120136041600c070309040d030406024010703000c500a0229109120f01100200400c0307444040f540090150391804045039941e0002200c12141140800e6680d0288001c1c403030840c11450340000284691001d601c01100d6096482040c8000103060316102c08403c01040f1544043e503009084483c018009541c4915002d844580140104c40c07040e07242c00c1340054050f1050040c2e034060b0071031407920b100200156041c85040d502110701640c010700e0036241d400004241c40b054000420444034200c190900d50328018017580c0c010b81c00200c20b030340184014040d0b40d41d0f2204035204942c2c051500e42c2c0f12000d1408141090311190300150a8940105054482a04c424000c20717400d47d032030121035443c048145064040791121008030000030303002c0c0401c08100d13500141e40504141c20b801c5c650b0034010680d001076420304040d089010329140120500805503017000d0203840d0b56840b803c099510402c141415500b07100014805014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 386643291 1250 386642041 386642051
    0x10509100302120103030e1203040501140307021e010c02010b0a051525050309010314130210020c03011a01081e060d08040909030c1115040e09070f030b01050306011d0a 74
    0x140c54001d904542e445003550403020803969490a024050482082042d07014060a40140030740b01004012681079800503101c180c90320a40f91881003141d00000c00340313821351040f500310f00c4000b82c5900b0341c460744292110020070300b1084420000e0030756005209540c09005a04818842540c8010b081b44804150b081007949903144003100740c42808082d2251019492280d840b402031181c080000c10000380282c074240858038a410b00c0c4000144111144c103030503038a0704543e10052802c1c2255150b14884c1d031040321501d64a0400180c2101c00c03c422003c408010400014038558200742e0041c0e110b1001200400d000d0320f06615443d11540003040a803140140f40048010050f0305015113024010900c82042a0040c1d482d01070b29505886009a40500011b81c40c4c41c11303480c100c4001c0d800708680764207c50134107140040e190f4190030081c005210718010a240491714401c04000e2500843c044c0076040c07010b5241c0b10074542004010307005081c086208031010031501c598541d00a4028041c000c2c0000c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 386644541 1250 386643291 386643319
    0x90503030a09050111040b0a030501050906100c15061e0e010e07050a0c081b070e16030513020306090303010f08010501031205030403031d03040503010e1501150c02030703200d02010509 81
    0x1300402685002c103d4403c40442c012031001c8040000e02048500e43d01c081040c3d036202c104010215901f21145030780700c110411401e0034140f059044181030b40c42014801c81c41c0401109407000d0744c80b650004181d020110025003400203e00d18400b006020008001501d07506058040208900c024082028420002201c1e15000d10424000c117065412a00540d101c0c09041000c048808014107507194a210b6540d0108104000c14841780c0a00c0720101e503100f0281580c5070650140c003008062590820701001c02030090388007407140c60310844224002c0d561720360400309003100d001da0f03941008030640c1c5010018000610340d01c00e0702000750380504095850380e0301e038034088000d1705254920200c02d0f0040e5214500d5420000013800071344008800030b011010f0102c0f40c20b651203191501e001c0364005107800400c814102c0131b030b03001030302c260502d4820044611500468500421544121800c168500100d40550490504c4420001c130403540401d10410b940c0000380680a2070710064410686491940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 386645791 1250 386644541 386644543
    0x1b010e0a030c120503120c0408010b03010614190b190f081506030a020c0d02240f060d08040e0f06100e010f0509040905070803030a0606141c0f0216050709090503030a0905 75
    0x40c042d001e6410b4040300504d040c0021f40307a1500301d4415400315608009200e10f8518043c007441040e030b10380700503003038450111404000c40802d0201c1400044641c001000c00c08600c080c0080c0207280703141000102106610380e00811030248494901c1c2004000380600000c5d8840c02c1200c404090200c4025803a6110001d422000b4459101080b65600c10901110220b94020440c04540c50400c001500101420010840700f002c1c1103d00c12101440740d070004603a441c3c48400809aa8001c440e51403c05450301e0407209480c00580790395401c00b104600300200c07860a44260301074091240380421200c046078002901012000c0011018014046105203482e152548900d258a4010040f10702c1181d07200c2440c0d80ba58025105004694208139002c25000d0051104802802c00002200d06e4190111414640058050740d000ca402d40c0380d0000c005000c50500240044844068820a1030780c12898030519001050b888a0a544d081000060100f040842540d911800110006c900001d10345852 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 386647041 1250 386645791 386645797
    0x12030421020a0e1f140303041a0702030304030309090c09080c040506040e1f0515030d0806031002071505010e52020c0316061d031b010e0a030c120503 66
    0x41403c0e40144420445850000031584a070542c1da224800c05407620360442c840b00d8000c3c0c1e40f1107074243d881080108008420000500a644084903006051038056400207043d6030043e4400d400264001c0ea00744031a0b440d0344288070111f1564180006601e2410140741d844000100c4464491543c4034001541902c541d00180e001100303010588120000109a9000652003144c158000314a40320020711900b00c2d00d065203000450082c010001038126503021580450000c1c1940c0d05030007400070410100f201400540380c210304c1104183c0c4030543d41141c1030b045a00591000425030f21050030300071104106c6043c81008a01c203c940600c00702c0d806901003000c00300b21501e000080c41d00c43c20080d0901940000640c240807907094074840800503080554828180034201d402088411b0708001090050048044903201010541113400a03040080d00f02540c3c9900c00c1c1900d40c00760b10303080c1c4642e80410010004941215882282d0f0b05544440540b0344c61805103058103d521802141407240030025 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 386648291 1250 386647041 386647049
    0x62705040f060921050706060f030b01050d14070605090405090c0f0d0215030903070c0e070f210f06090b0103060b091219060b090106082e170106030212030421020a 72
    0x25807100715551342d80007003599200c8030069414a160400c08200c4050741908601103a0704000304802590a0000308281d450110703104a03403806d406084540841801c3c8141c1008022585601c0d859041210a210070f44400130074001d40e5800c01111016503135034410601118210581c1e540b19041d18610205414101100110841c0400401040b00c404c100100806945100d04424070346070307a5500510320052011307103040303012038110043c8040e5644071b00861100010801c0e40b42c01d03480c010400700c01c1141d900c10660707c1c106440300c50034054052075000b20010010700386020000c542c03070f01003403c903e400f8200707015105003800380c10004820410801d0b400100d04441000750212001d04c0c0800042405100f0940144000030000a02a0280518500c605a910f00c0c8411074a20461032103200700313401c2032001011440102c0880c00c50200d5460750b1100f800600000385040c103600410200030020aa40c40065108110600c001c0c181122a04030a000e4818501201e50203807000410b035034910b0700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 386649541 1250 386648291 386648333
    0x303030e0c0904080306040c080408090f0f06070c090e03070818150f03061309030f2a030806150f0418090206030f060108070504140f0a09062705040f0609 68
    0x140414080a070f001907006e41030484041121071000d940c10754010208a401a00c1c0c0c00307060018226504104000c071400382c40082c0b02514101110000414681250209460034500194140084141e6100d440360b860071a070029070501034650344440c807520400c2d40325862039003101c0349144107890301180840300801c0c069980303454100070406403006030400c885851280e2000d40c00010021102d200e5103c920350555203400070038000600503103000c1180048040c10060001c81a046c1260302146101c1292103a60303803061900f07015041020301800c0d0803502d507009608020411007030843c68129012225840c0b4143c0040c400d2220400050400210187d0805400010003915140012107140f1a200c00d8aa03104a40c41b00041292280918000d544001c0980c51054409140c24010004280c070b00500070480c076038481580b0400d5440310b81c024000440414103401c0d51410980680300c1c03443c800d031010411403800e138455903501350546002a18240e543c0b080074017800318400d14007011007800d030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 386650791 1250 386649541 386649559
    0xb0603040f1b061416081602031b010203030412030e03120121110d1b060306050315071704030201140709050a090b090f0603100c0f1101050708010303030e0c 69
    0x1040103612500495030481e02c8051071406891200002907091094030041c1d95400490040f41d413040301194000c204103a03025071201107000000b0032500051400c000505800e21038001d1605c18507151050110b0a1059462107089000786664000309aa6000340c0181c0b000c000024021002d4004043c036041c44200c0b030000007036035120b80030b0304841141200d40e04051030380d00751981d034038000303200d41d03540e00080c800c01c135142440c1a503190580100015070f0140c00c25610204111820b458070114662046012949811041140b850107028001c400240b281c500700803442c0080700140a116003c07144901c0c65002c4012a0906100b54808034482481c01c0503a006401d1201c0b0180c000c082501c0b609110f456510740200e840c00f02030150b500245405401d5045c90780748e01e41c4003415000c00a0400740c151280700000441010180a4807403950b100b5140c40e00e09d09000c01c001040c0032485c404410003030307050a0900100942c00b00030541141c3d091302d000a03181c11101c4a05040003041c061150740310b1590 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 386652041 1250 386650791 386650793
    0x26060f070912051b041e0209010306051f0e030a11040507050702042405010f05030402060a0302070b0c0909070305090c0f03010e07170c150a12060e090105040501061e090f0b060304 79
    0x40d444205400a169599580c60b01301c201700c15a01d00030030b9110903540c81864800b5000d41d03a005052100d40504000c1041501c0d0400300f00007007101d03400900380e03e051540100c489d40e0402540c41e00d080094021b81185443c1d52258510390345201c0800e4000c55550340003a2103188030f0800e4840c51503004000f80481d013a6081524070812980d44080d15100780440300291960088013004080007990300e42da07085a03034a0b020400f442e00f02404510625408010000c0040c04a03622a03101d280409001070325481800c00717000c8440030043c0850705144ca050b040c0460100300003603035400440101e4024807d00340320310203c1c1c050400b00c982c24681d480703000c101144104c8030600c08403007946640112001c0d00048420084040780380003006000180401000b14183d1255011042c1c040203c80302103036956690380c01c812540c2d130881e000c400f5650b403a402d00c8200704080c003410004190b21031400742124913049444e890010701d403090300300c020f03544d00244410f0080e03a0000801b1040040c100c645034549 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 386653291 1250 386652041 386652043
    0xd08090f0402070303091704081e0c04060b03010e0a0902092e0602010c0e0a26030717040e0f010302030606010e041413050d050c0604020f0d020310020426060f07091205 74
    0x3642d082140e0032007c0d1100403000b590280c6c00d903001c031455274000f03203000142c0580d4a061102e0070702d96142d10703005502000c0583c7c1c44074000c9030010315030010000c2d56585800b408000410003e0a8881854185901c0e000035035100082d0940107900e50150804801225195030a410303c038070341041559030705070b1f80025203540644c17011000305095110100c580d00d0500801041c6601b900401d908410104a880710fa6051040621080788014040380c0c50b10885848143c20310509044034840c80400150600200701820b00050300990841c00b040c80c01d50441d80040c0c1c451100600041c10010844502c0800d9502c54001415646940308140c0c1181029203c0a82c200000c40058400380301300030308280b000d88640100c80303070800c4000191189444d0b903801c0001007034100d04165400b030301c000900b4002d40e800348120700b010345a0080040c0d9451800246c03a1070207600700701440d030103641440300703114001d030100c0c50503804074410b18580125503c03280b0585940801d5001003d40c180000b0300b00c800c102e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 386654541 1250 386653291 386653301
    0x21b121f0f0b061c05130602030108030a0905030f06010317071a0702010c02160509070309210e01020a08120c040803070b0702060f0702100c02030d0f0204051e0d08090f0402070303 79
    0x7000000d002c0920088144030040c4103480c031080c0d0050000c1240e40910105a00880c0c2140d4210b510072070b051407940f6100144e81003070b00000d030750ba040010720302c400700c0c0c11441203402400c0945c064001241d034070104135201c0f141403002609614404071008243c2406a00b00c4080c3ca90000203da551280300d403000044030000c03200200958070384851070b001f0900009403200742c0e400800c949010303681031005001c840c00c1e014004030113050300e60740a00b00150448010018000404801c001716108400008280f0443c01803101c0c150741000300468049284001100c0300c004401d01d00640984856003019024840c0e40d21013009404041108000c1041030015203004180315400c036555038603480070380c10a4100a54902c0050fa10520400c6a002141d400c881c964564500590741000c820211078000d661000b8800c011040d030018003400b16140c0300016018161b140c00c082c441d03411034007002c192640b02c10880a003c480c00421503442035662000f06000c4c40d500a40705540301c4500d40b41c0500500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 386655791 1250 386654541 386654561
    0x609030d020c09010608040221010f05011d060103051b0f07060903020601030c09020301150f09080105070f02100203070c03050c0703022e0804030806010c030e09071e021b121f 77
    0x1c40040f000048040c400ca24440c055a0000c040c040c01ca400c00d0040100c3c2c548011068440d0354a072580003594000c18818940241080002c2a411156a4842161031140104928149894082804890003011b800d660043c00b120007406e42d41c0502180702540c0d03025080c4020540c5051242000400d03a0100e00790303048a02c0713a904000e00e280c8030032110080e80000d024020703194040900c841c010700d02c12481d02140b840c95040821103181c5800c50356007941c00441e404408200c000141014a07581002290a050741da02c0d002c6045007807000740240305001c822000b034100080428550319114007801b141c001140c0c01081c2c00040107145000c0310700000c0c80445112541003480300d960020307001d202c0b460b126541c1030795030b0402541c51200544100910724015410003d030114001c4058607070004040c05900e1503217a1280e0740d1030200c40c072030040d00d40140450854000301803424071540045008015250111003c42c00005120380d80b9150443c90701c248010020707041803c0f101050198020a001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 386657041 1250 386655791 386655799
    0x10c09090b010f0e0609040c021e0102071a0601021606020a150219050c01060e011202041503030927050a09020f10080a0e0c090f010524180609030d020c 67
    0x40e5660500c2011a404455880d02003024103021540c07040c400c84a15200520003010b0a04204408000c9411201404240030140c1e0010385a107250880c4041c2c110a401215002545410703111780d110b0500c900c00c1c1013022038810300070b0301180c940d078020702c04101900400f5007400811961001c00070341c0c9207040e1000360784842d824240e40703d401209000300c071035200d0340c4429103450086c44901114164030145da200e042d550707104004100c045103114107070f0080c50085e480e2403880640d401044112506200c046580240c80202000007035002030002040310f0b0700c2c41c0c0a041d6421149003011480c5083c101c400d2945207043c0400c440c2c0300c0c490f4050a0010b000f41e500d45a10420b00d01030003090502514414080b03800346c0c0009840302603e07045007001c0f0b0f1004003a20a02d03150200401c00c0351200784c64032000402d20000500880c01e080c0e140400211440590040c140320306001849648106078962145d03040c142400900e90301c1d11411104201d001070304035101120154802510741032024000303489 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 386658291 1250 386657041 386657057
    0x3090d14030f13060b0303210c04030506040b040309030204090311010c14040b2218051302280506040b0403030305010801050c0a08070e090a1b0816030c050705030c010c 74
    0x86003802054900c02c0d0035100c60b107082512105807030460042907000854110f500e80c3c5403c0b64039102800503100d503103640d09024498480108542c885540000c2c080c01e150311080c0010804a0400102c46401ca500005249e80980b41c030b0604840d040595040a500a800e024101081640c4405007402100e1400001c22801290312003c60740703014810a410a817600030301003444482c41c540c004040f1800da50f81d03858441c6804840582d201c00143d4085003451442e4144000648100d000c1c03554480c41c1031003080f8070300765540d0000d603a040c02007407290b01e542c0c10000c82550f200d10030244100603000045c000c0e030701c65079908041e481c90350107404110002404c0038000902200d050080d24050040da15481c0d00b0b001d401c0000701c0300341c88018900000c002012031b12400a44440e0708150064249160200e510710300c94010381d5801a504140c14100300e00c1808000f45503aa04002019084040c0b4010846151847d011030f01401496005003042c0400100c2c54810401580300c0905040d5603116407034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 386659541 1250 386658291 386658317
    0x3061e080c0a060905010f0210060806011502010903090b0d090b01080d1b08030c0304230a03110303040b0a021b120403050f030a02030d020901120e07030303050c0f04050f0d0803090d 80
    0x42c0c6261244220008aa0580c00a100703940c081c50b0390900a20461048440e1600c60480035401c0e900298440f99003074214100500003541420261024169140002d03c20400d00390f4009020917518424121070701001b18124a16000c1074112143d1aa001140c1c0001d958403080242c1e2156469181c140200320b000401602c2c0c000c1e540c0c100028540c002c00f8031402d59580a640f01c81540c00180110360350110b0010450312080c101c0041c0b4001f02c8424010180322885240140c544c0020030120010350740140308001c00980a0400c0541c0140300000258541c0d07041c6640350344480407540304441074014a04890001c01c0c0c140701510803a0301030412901017450140905480b031142c24507840050b00100480402e1445640041c44000410324003940c408a000701d15204440700302c41c07002d10541140c601041415418040c00780c01000d000220b030301d0140c101c100c5265a10861060b140603080c03246c1400c09554802c0c2c204248542c2123212581d40380391240c4280d44594101c50079601080411a40795 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 386660791 1250 386659541 386659549
    0x90e0607030b0a2102192d180e03091003090b06100f031a090f0a050702030c030417010902061903060b09060301051c0c17061e1603061e080c 62
    0x30f0112401d42c000d0100f001482c83c140400007040580c26030704040950141d50130b14092400c0300c4c0040c040b040f0300070060796044001489880203410280700e075070b03039070a030034001c008400c2c3d804400240d41c1c5070000b8114140071340140c114040d1007a001d52202c00c004110954541541001c904140300704c44116031039440004008091540100c040009403d0140e54074180e8001d030b215008031035140348003044220200d0300041c174a01d801c44502ca0003040720320902541c0129801129000080750001d5420142000d030315655a004130700c25444d0f10380d01c54140418105003036015011294000c2c0c091503540c0702070051020913130303201e15101000a141c082d0000700318141c58107442e0703a040020100317451a4070700030820400130b030701c1007410300b140844411482c00650f407016014001c3c9000d400704422104141c0300a81408402404444100c0d01c1c0c40c01c496108070309400c0258400701c0301d0141c80000000c404110001c2c101034001f911003851400780030b2050342030344c8101c3c42113859440031501c5101c1c10100380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 386662041 1250 386660791 386660809
    0x6060906091e0e0712081c09050114220309051203070201080f10030f06140a0b0102070b120c030c071a0a1a030606010509030a0b0421050703021005040606090e0607030b 74
    0x400f010740080c03d0910900078a100d90300d92041c05800501d0422030381501c3e040100700085013205440c1d035100c1c0042c003081401e006007091001540041c00380741c80c04080c440d0080104200e07025020240c5050307101058041d04500e406000d0141c208894080d2070044c0d603559521220040e804280480c000079440080088500c0c8559580e00079031202500e940d50300781380014024001c88486468107181070300c0c0304403140d41c82d208400d52840418002030010001e4105034013500100c054517400c0080e0040c2d0078a0303800c0300e90000c291b40c01c4c00f9900d9451091030083c902880c540113005c1d900078001002f00c0c3d100441c0c3d90780508014101049004107181180c070001d2407001240342c01d038000c5800100341c1d40c0100003600c1c1489000e003d44035610915500c6051601003102d04840d5500c4280c80c010200000c0707101e00c1c040c0005800d0040c07900c0010307200655a485c14086406200341c407240010100821a00304c40c0040042c8038082c0012052201001d485400498a4000213483d04900301d507071f45044054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 386663291 1250 386662041 386662061
    0x1f02071503091407051906140a051c060302191d180607030509061006020a03180504020708130b030606031f090f020904111c020706020c0a0503120a06030b060d06060906091e 76
    0x4589010340080c105042a8000d0082270051020510269050202c881048540066107190000741c8600f1071041000c4c240d80c030031509440d200350010a04c449069014094091280b0311400703612541c4084003203010400e05500101140510030501034442d0305500900d02808004040d5482d65031105017802e01c4040314441c410041c6c1c0032540100c0407074080c0c40504031b20000c2048500d903e0f138075100414140d0f4400b05084403414000101c2c04e40f41ca55210364500034001c020b01e0103140d810450001001808040d10355000600b4010040807800508401310004141410040c05000041d588a0b802500440d00c02030046090000d480c4256014004030344080d0802e200d4020903207003982c0400000c0d00511000c0b81c0c1d1310303801c01c4102000102040ba002825209000556941d03584480c5c608144102500c4101000e00781b401c2800001e420094066110310b0596001c07008035070702e040c55809070400340d100503200c40c034003070000c40c0c900e017150000401d0b0480d0041034260744005820910403140242c0e9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 386664541 1250 386663291 386663297
    0x11107121b031101060e010b070506090c091603020d09080a1b0b011a07080c030307092103030509030730140a0302030402130606030504021f02071503091407051906 72
    0x68000a8010840145043e000340000505244c03076401c5c1c04002d51003a00440041000424440700b00b100c2041001d030320404035000740c00b40c13142d00c0c000302e000c0300700107411481e81540e0203050740c0300103100b0390680340149144001031000d80224200f070a400c1c3c0c06034150a00050010005a90760001c08071070305141944036442c50301c00d0303181c4100e00b0a03101105070140c40301d84003004924040380c102c0014003140b41c442c0001d556a03080c0010061b21a0400d070744016102404202802d104226550f0030a428a400d41800311350369940c200c10324214400d201008003410070510702510700d8070000c8111f030b070079044568003000c2c2d4424a24081c2d5501c42120070200e5003400402004045a11940207146c100c0d2001c0c085001d039058200001c0c0c01d036202a00007000081d40c5100b00f0007035181c00521440c41003003101d804c442c16003241e034000303449404e1801007107000c14164540c0c100c03051003640851503c1e40c000001e2040c604201503490b84071600c1e03100b2a881b032200c3c6440078950011245c141c8085400d242c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 386665791 1250 386664541 386664587
    0x13050301090b1f030f060501061e020a15060b1612020a05071509030512030907141818070801090b07050a090e040503071202100c03110a030e0c0301110712 68
    0x100e00f0061500c249a10009034030f181400000024080094589103580f007814041184d6050060042000c2e140740000002c2c20240c426240e507094010075807440a46d007120300707800c2005003c40050060f0080b03a0003840920310020307405007000229400d9104052081118106d403c620f101d00303c1c3e84141c080400350081d00250710400801c108130400c42e8000125007410b400b001d54a4541c1414079500040041180c500041045121481401a50040c02845580703284030016100803800341018500040d0710354480002044810000c05184d400e0000c00c42c044a0004e81c482d0a014041c0c090702000701d80c440800070100c5c00780350268060b170740e405030a581d038190480c2c03030415103100703c0070301800030380d1240000c0004801007050322540d43c0d80800c20b0b400511592020080d400111031420380100200352800026031300d240c841d4002c544021f00645400308000307040400240c10484101516030f410340ca8191134501d000040f9024210040c090f0b502d1082c0900005c600395160b0085a4160380311800030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 386667041 1250 386665791 386665801
    0xa091407140418061503110102060c0f03090a020a081609110702100e0301020a081608041106070318030b040212010c09050409110409050c03100b0310020a140403030513050301090b 79
    0x25038080074605444020280030a481c5803030391301c1100c0906400b0038003601c4001d42801440807221811000030801c0c40248440e162a01c180306440c00f8503042542e08810000201c2e208600c2044811016900100019001c0381d8a000d119030700e20180c0c0d000c1c0170a010320780300000c03103c40d00c0c800c02124071200000c46241201a0307081050200b06481c2020038004952643d4800303480c00d00c09024040301c191103101c800d04100805130302c2038500710b825500f0007005000300f100281b60005e00c86c0000c502540d580761145180e1400740c0301080ba00a00c010a051031000c0002031002030b103a80b6004a000741e40d50403c0c0e103a8444110b090b142c07541342e41c03008294110001c0115041c02d520403d801341c040d6000d003140514210004042d111411000e4680342c0c42501c1c1c4030100c1c941030043c0f64003409050800c0201d0800c540200ea00c40c501594405440c3d5804a824140740d07005a08a00380003100000c40c1d651151a468060150341082c0722014910031901004540e90405215560341a90401500c2d403c0340e40d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 386668291 1250 386667041 386667049
    0x647011107031103120412030e09040c05151b070501080c1602060d02210106020609150f070c140304030507050a06270503010c110c040501120b15090a09140714 70
    0x100d03284d405200c3e0700d030380e12485003031040034201804034000700380016102130400414202d040d10f101e03803042d80c10a06200001d04900305005c101c440544da02c15a000031962840494002c075482c01402ca40000d00c3e011100c800440c0c224141c9809807182d000b10b072a0380b6580640c0c0d00809203860100c220784498000136141110242c0114281c440d40585413004d88100c405a001c0081142001c0700484030040c00081d4051101d1540045a0301c0184003c0c40c043c4804205000054454000840c0b1900810010703403250b6000d0140b02d801c981c1d28180354100c3c4500c1540e90b40140f00a90b907901400f540400e0f14908001104212011590b841070700d010050801c0c0b00302c0d100d010503002c070700b41303c06000242e13034400380100c154000c00c5480b442505241c02a5050810301c9540d1952312480c6400018400d0450b0025081c4406410800507030041d40c0721143c2405d80b0b46440c144c00d920070440c030100100c902560f040f00c40190b11420006040e0303400c01c90394030b0b0384150f0703802600c0038111981c041140390b0030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 386669541 1250 386668291 386668313
    0x30706030e0c1f02070920030a0b18010f0b0712050c1006150806062a0c1f12290a0e15031c020a064701110703 49
    0x511403095901c5968648001011000a01030a08943d5000707072603000300540510180b0002d041c445800d001100700300203103480590100281c06907595001c00072031000c2030640e100110704640540500340d9004030b080c41140c0400240300744100b221203c400421032034201307030503506125404a00040c189003042c030b0990f010f801c0960b110700c0c5072007203032003c801e01142130040c40000d1031440b85076038200e405400000d0a082c0005d000740d002e403030100800b0b41c0c1280d03074410a417212182d400307a540b146040041454181074804032407075030081181e1035204000b48541404900307200c0c140c5400c2c0c81095940500d10584900e04c03c4041c0d036000803208101e44000f803100c003e01201d40200b54842c500d0b03d07101d810000036001d4800c45407a01c500d842e0305105040402a00c04015220034004815048441d4000c1d500c0041400081c40b40d0740300d807a400d0104492803180d8600c1c0d8011041080c52004200e0404000c5505040c004501401da02c45808203500800c040728200084602a0134602d0850308d6800440d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 386670791 1250 386669541 386669561
    0x161509210e010305040819050c01110f0403020613150e0f090402010f0807090902042309220f1202100f151707080316030306060905130903050904020c06010801110903070603 76
    0x404100c28080c11f002c0c04940d04d0605020b4035004d484400140c0282d084682100704161102402c000c40150a115a0203590807682d040b644140c1e18003090314124002c1499a022080e2041c825407582c0c091074200d200030014004c29115030022401d10070800040f508103850190100d200401c40d60041403180c862198001e000741440c0c8400c6503a41483e5040ba4859030100816140c0c03070f50794401c2070501d0306101e107480c42c0440c1c81291504155806060400c000e1100442061b200c07030f001c1c801c20010f00d0300d079101d03150004041d80105208050281d2030310190350190900a1400c9480e200d050442d206100e42c0710702c8085038441c000d08058a00c06c1101134011143c0035031280c030b1400200e4882c00c00c0280405003000342011b011b09043c1c43e02074242e500d82e82069080c840000d40608c241c1d1210401042c04234999000441c002840382020b654501c0352400c01e40d0002e00014440850900010b1528101c48442e0000c101444c010070400d0400e005034545107a0540044604012461003030f044680c80d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 386672041 1250 386670791 386670803
    0x305011508091c0908070501020a050714010201150b03040201090911120a020d0c09080f0304150c020f030601060c0c090615050c120a0314060a080705010302161509210e01030504 78
    0x4801d41c03d07446840340d80d006803400010300b1030b440c00d0020342814814000100b00a0005001400c1c0301c0c2d0781c2640758078003800350020306001400c1490441c0c0c800d4211751079481000200f05445a2200c3e641c106550044800741d01040c500d0780c00040e079000703610511641c5002a8074840c20007024056800007800080d01150b14036409201c00e03866105203209910703c6079155110741c040c061812490070308260341540306041542060008010380d4020036070301e18400e0040e203058034000000307100003402c0c0342411842d07640511900001258050b00491081203080c0540020b4030119921320428058940381e0281e24660589040c1c405055401403014091071640785c0180c0b104034528407041192134000c00c0516000a80740e400203000d410488044d2504000141d865180070384c02d02031081d94440c15885010304066000840314913046100d50044985940002051010100c8070700e00401390800b104d044d21000c260040c0010802c0f0f2006c007515078030909440f01c0302131045481c0150000c140040003545c013 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 386673291 1250 386672041 386672053
    0x6031b071403030103050f03090a0506030a020c0718060503010b030c060313060e060a050a05130210050d0e010c080c070b0103061802030a03020d030c05090a031202010e030c0c10030501150809 84
    0x301c11584001450008200540e2a580346003421131600e6403c0c400541c041d0020410240c151310740102c44c005803901076900c940d80f515961315580c001c0c89801c0b9611a24020a5000310b0030b007410022a0b20b403038a0400c41885031a80ba4030400d401c071216035160a81c1342e03114031410020760134000080e5500c500c40c3d50b1210004032140e1035000581d20b41810080c4103411540400c40c07154021310078a5001075019000700400d203081c03060081c1d003881c03958019210788828601c021405200310210740401891103401e0006160209206000e0111000c2d030f4000b040c60b0800040380ca082290a94003503e400003202561646542c444400428000c0720300c22007030024035003400258908005103960b0030300c241c1c0141101300800500404907030070904141c041000411466000d9964010000160b07034014403042e00700814028140d004007c2034824070300d10700000c51008036005000c00c513900b54440980780c2a101812000303045046030400d0183e141c1c0b000201e07621111107482442c95680c80364000084030300c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 386674541 1250 386673291 386673293
    0x19020712050a0b0f0405060703090213140a050702030f071119140a05030105160e04060e011707090903171308040902090a0902030606190e04020d0506010f020c06031b07 74
    0x1140640408299950b502082c103103000c02c0312070f440465001180e02c56449090515503102512a1800341440d020543c40d000003100303658540c0120310b081070780c1050400c41503408030f07041100060221400201c0c149814005090140040201c0340010113908295103880850780c2d5000f400b24440c0d00941c0c01a00480100314003139141b02000c406040700c101d07442c0c10405500304110a8420941015001e40d04100034800d00b41e444858a950b01882c030b0401d054880a2840498010032841d809410b03032051300000010130100400518002482210980b05503903102d01000c81601c4800e0802000281002070b1018490390780b02d120340d040010b44600c2000e403e141e440f040c0c6640c00c0364100c204001d500288029440c0351642c1c0140040010030815401c515280b0000303034182c054400740040358503106c0030b030800e1607218040d5060880c000401c115250150101c0313000042c03008999031800f00b0388010140d1001400040e20344927030744006102615503501c0911000e0800892500082d150505226101c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 386675791 1250 386674541 386674559
    0xa1202010603060c09081b0105180d0c090929010b0a12050a02090a060206040f121e0806040e0f0a030e21010e060c04030807080325030605030f0f03190207 68
    0x5400c04c9072580c8446045081181d49800c100c5802807071442c40e452200d030500581d1f007010540d8500c04003d0303219086112247c012030314a2592040050000a06200218050f40a0b9004000860080c0c051114a40c03822410500081401d81d1496244001c00010005803820500801c1454224904070705169041c4220005452043c4e4501888580100f030400480c24800112001000148028600740c185900c0f101000310310104d000c0c00182400c90b10b0100305006143e800204002100c1c01001034005513401003c2d0003041d200d0520480c10101c00300861400014650314000c40c62001e001d5404041d40c069414102089410703820205480305851100a150041c080390012140003040f0b110003104c140d4140748000381030041100040c0001d00c041401c610989800541c0003c103d40c0c0c030b842d440307000f0039911101c050600c03a5076290103940307425a84c56048401183c905504a8052074010300e049515400f0901003446541d00a0052005c40c990490100c04450b5450040c0c0e0030b5981c44035404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 386677041 1250 386675791 386675801
    0x506031806160315050105040909020a150e032a121207050304030b0105010305071409060403020a03050313050909100902060c01060b040e0106050a09090f0b10030b030c04020c0a120201060306 84
    0x1026008552a1401015054014038a80d0030f4507603111321080d41454000b0344580144e001e0403100e0396492500070110b40301c180991015040da05010035860854510092540d0091581c0c5402401005840c09483c1c48504c54901009000044c000807440010144460000120084c00061080400c641000f0030400c0091003081e01610256a440d400e40c2800d29070040103030b2125040504d46400c1201c1e541d8411154940c0e080040d054542d070340e2540000034038a020340e41004e948443c03001c031700108008001001f01200074030000038808156070740040089005007100c8408190300180403079070381003100344d010041c81807004012508000d2070540b86400c46181d078200d101b031103100150900c00303902e000c540300380100304500c1c3c040c0c40e020b90014014171041740c03441010355143e12495805228910b9070080c41e40c20340c02505100f001c42c46044020042c00500e00064040c1c0610015411141401d000301c2d0860038000c07000b8203440d061951160000c1450040764001c65603281004030000341706000b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 386678291 1250 386677041 386677051
    0x5060715090224070209130b0c0c030903010f020406020f0d080a0e030409020f07050f1c050a020f0a080322110d0317040605040c12030e010e010c02060c0d14130506031806 75
    0xe015154807a17441408000700015129071510701c8003080402c0004d072a04140769100140c1001580c0b92a0606d000e14a5400303420506035140d402c1803e2042c501e01c5a03400f41045607120342c220303601e0310003056400380c4880c00440000006119040041c03215842da42107007009059038401c0f04d2405a64425480481c0c0111a0070062047e0004075002030050800c036074456444804090800700d401c440c0000403c0c1080c15080c1c0c00c2c810082101604036000784030003062880c008050b83c1c215441c038a000f07071990b403086420303980d04038440c01c0d03894004e151169480034065010782035100c2400504200002123584103021401c004285c500c0124150441940b2800745104000101c1c441c02c0900d4181d9003800982c010020712902481464040399105400f4900001e003070034007503400425140100ca0305040140040c1d000200012005840d0b00000340d800e01d041d00d10380d204549500265034140700c03807003025200c64000d40c08403014044c07440c0c074600070750300300c613011102c5e6084c8038554200030b04015003202c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 386679541 1250 386678291 386678359
    0x1d1501090329010609080d08040c0506130f1a040b2b1a0d02060901080907091e0c02070b07290405010c02010b0a0f030b1812070309050607150902 64
    0x702d1041050035140350301602490800e0070100d420901102e5440102d11190300402042c04041401c0c0303d408a030003c05020003900c401c0c3c0d030307070180c4613003041e440158800c02d40d000100b41da0014408603004800542001d0401100740340506e001e1050b2a16000001c0300340d00c0c0c9100000c1400301d5003181451903108410b80002140d0580c82108804070b410004922600408010403404010fa40c1c4104031000040c09081200c00b584a00e5081e525040d100d800c43c09940b85084078038208241c1e00311190703004101c0d0840c140708808560004903125031080c07081c6504810184012000201c0041481c0440060b10703403018a050844c00700301d210f8070402d880c2074a00365940e0302d900400b16820301034800221030603615466140d150019400428540c0d1001900c13601104001c10315840d0481101044680000301300c91041440340541c140036480007100b20302084000c0c078001140d061900c00d5400c007035000307100101c03021080944039001d801d21400880c0d2020600d164480c00105484500c003243c07180d12 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 386680791 1250 386679541 386679593
    0x50f0105070f020d0f0917120a02011406030304030f081b03040b0405010e01090308040512010b03010203040317070f020d11030903070b0a03060902030c0403060b0d0b0f0708011d15010903 82
    0x342000c0d0401100c051080100540040c0b1385c0116500300c2e1040341114078a540740455607140d12941030400c0c1c043c0900c400c0b01e82c4000b459002140d8150480000001e90002e22485502c0702c104141d541d1040780300040c40c0c00001f465240c089071110018102d20310141704012603420048005508680c0103405c640c0c3c40c81c001140500c80e9581c804c00c0c01c081c00c4401c0c20b0181000d800c41d22003d4003400740344a441d110b00c069200795081c000c1300390040a591940130f0001c0d501c0b42002c1c0b402525286900c18045080031a18000401951180080f080d0b00042500038000a100c10041120525040005160244401c01c01141307a92000c006040c0281602600e4030f8481042c80f0340142a10f40b01c0c1d01200c502030044c01441045030200d0120340803254440c0c000501c00d81c1c10004501c0c0070801f0b0001402280c030410401106c890141e081a1080c1c0d0306650381d02300307a80c850054030080088d03070026a241400110000f22010250070580c120a8414145144055903a9988078140041d400c200ae803074825103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 386682041 1250 386680791 386680817
    0x9040b07230442050405041b0f050f03070810080a060507120606120b1804050303060907050a0e310905160503060a050a020f0408012a0e0d050f010507 66
    0xa01162500515200c003041050a0740d1040c0b06510301c880000f20304904445807019140e14001c40844004110142007400030108503041603004180041200c0d020031010328080f08414442d034200c41140e407022031307110304503250b1842c1102e01540091940105240b003410119001c40d04020480740648074800101d89803600610040000e03d50b0024040a00e0030842c0601c061034100c04080c40d940052040000d151400400140e17058980050390200d000208080c0400e0110200c0214481c0382c0a03213100d21140c41d008400ca8940c0318464401d80026a440c4400751589804441d42e2800410349074035443e0040d00d00c8400070104807032098551595070710380031075080210a0100d0000414034200942800345001c000c2922418018128946183c0c0c880010f440d644540d81914410040d4803120758440780c82c0d01c1c100c0d0007403001c4e03810303448008a03048110380c001e18840e40002c40321903143e071401c1c0341100701c0d01800b1844541c082c1c115924081c4071000754a5400c04d02c501e070f12843c144d695031011308441c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 386683291 1250 386682041 386682059
    0x9090a060b030606210703021c0501050f0609010501030902010c050d112103070c0804030f03030515120c040902042003040312060501020d1103190504140f09040b072304 74
    0x390381000d406500144104034065a07511090182c61444480d69049001040b45c2a410400c035900000d510001e07243c1d1217010440c04205020099204200030043e81d140c80c0c00080680c04119200c2e40e01001140040c0b160754401d0300500303042e45c81070510169103c0305641d200c2c04c1000e400c10180000b544248401000d03030003005070080089410340072020b14103a1000c010511b120085c9114240000c000b1050100440f48080718011a002924030ba118030240c54004c02a01043d11540700c1101484c161891300e292400601c02440c80120041c040b03034403508140b00140070784881c1a03078080e907200394580c1e61001844201c0411a01c00c4e000b25500d2920b49006860204201d4055a9040ca410018020b90341c00055581c1c101040d4117219a8a0032485882407951241c1c244024030f1403480d0100780700042c0c0110141050300c0c02e0300414007000d500801842004517030f04c10410352102d000d001090104a0180034aa0800c145140c04586280b9501988070440c1003050900c0003010002801c10001807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 386684541 1250 386683291 386683301
    0x7230d11090903092103030601110f0d02030a0809033f0c071a0108060105060d230411040b090105041a120d02010f05090c12100e010605090a06060801120206040509090a06 75
    0x881003031300c007085c024040c014640d2800b0013402d940c103000c400d950407001f191b400c200c0c0e10030009c00d4104445964010782e100a4480d04599926030100748140003140303001d480801039512007000c0400032021a49001c0d104070f25007540c4560141c190010b00c00d881c030015980c00c20715100e02a0314420694505480c9490103c0c41108a1803001c0804800b0041c0601a4042440d90450340b08440136500c40e260788003264000c102d52110a00120031006091040d10030000b00310340328500480c0c4e46e10840319014144030070303611041c08140d17000006500510461415900010603c404500441c910901e500007007111070400200c4070085078014070130441443e41c2405140d5070001c2c114818425801e10707041c940d540b4241c50101c035109807003d41c01061a08001c100040c0c0e00d01d482841409190090841c15008014502485000e03e00090000340d03803141501810080351290f503114151a032030980c80301c11442c4800f00407603001004020000c0c840d03407111586801031250b40040c20020000f80b401c003003120307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 386685791 1250 386684541 386684569
    0x6030303140f061e01020316060e0c0405010f0b0c01061205100b0d03050a0305191a090903090102070b0f0f04030803191b18080a0303090507230d1109090309 69
    0x2107140b0030400c1a03103410684165078500708041400e00d50304100142e00f1405002c00100364100b02420500600407280c001030b850346039000c16a030325254168180400d80d0001d000b594501d119a034000c001c0b42002074021301c13001032074800001d81c00342c541e00c40c203082c0c4400b0403094400b9442845841e000c400c10744150020150121059000b14489660152040c000d07000403409061751000040c5020441100c1550018a4040100242224403180b102b60382c206891880c0944c01070000101d1b508000000c440043c24140c0090400614083c00e216040d0f102403040c2c80c054006010016010500c0f0000d00b001d14810401d840e00d07880c10400c03402580d221225003100980c105506500740448207402410031034114a003044c2e0451301d2681881c07807041946c0c0074400905c120402582890380c180c0c440c9920500c0760050390b5149541c2c0c06074102401e03e880440c0c59001d5240e000300e46500d030815042c007440380300b260f41c601c1140c10540004c8803c001143c2d094043c2d080001c0c05c092500d8810340d42d00c444 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 386687041 1250 386685791 386685811
    0xa0f0203071a0f070201062103030b0405090607030c1803020f011110020711061305040506040e10020d0516171e18060702032b240f0b030402030a11040605040603030314 74
    0x80303486c0030b203c000060450343c2c2c0350008c60322540022040c140309070002656603c000c2c2003801142410741c1465654807003111010002440c0c0310300341c900c03e0320500303861545411041002c3c0b141402d6800700611408440081414004e98580b5001c0504080c01070950f40f40000c8401a103420280c107060404054901c0301c6403140d001080111b2100719040d907060150740d000e030740010b40c0c0d07695040400e0050080441c10034161280720420030b50103c2c9500245269800800c092110791a07030301d000b1903d18449400070b00070a1010a2440c101d6440c2e83c54a6400f006800d03810810803041554003400a02c1501e800c8d003180790b020071001900c04100100e5800004602c01145800d011542024050790408003008001e0500080c10f4080d0000d500701c1002c06c40300365145a10309001036404101000c25204105445020312f0001818100000139684901d8000d40600302d404581c2d0b9940d600341134440201580103644000100d00c0d80c5861146102844c442e40740000c0200c40044009020b040050074180d007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 386688291 1250 386687041 386687051
    0x51603030e04230c0c030c03040302130c050d02030c07020901060f020615100c110303030f0f1006080f040c030b0a0f0e0a0c1226040e07140a0f0203071a0f070201 71
    0x36034550101d0f83c0041407104090025110001007000170305c900401032220b44000704e14a8203004000c001001103c0c802c8603080000c401d4038003030b02c0c1655140307005030001c03400510a1090041c0f154001310b6005000c0e040491400810740d0009540b01d60a81194001172403542e0035000c940c0d010020113400024908450004456801c0010369580003d1400070400401032185410402560041d22140d40c1c020240c907105d20703007032000103d0144100d800250883c04040414840342e00b0004580a075241a5690003081c2e0300c580c980c007201034000d00104c2d1000d40310301d400000b0480d4119858000c50f0b00ca10b002c070b03840341d0341c0c290342082d9040c450300c0c0c802c150031161013000020b8001202604403401050810b01d03038042820810f5a46130342c00811801556410400d01d40314000c2130040060707407201050300003991580101111089890f03046050b180c001004095161405204013207561001e52040b42c1ca864111742d200c004505c803000702074000381040303800d1109007208482150f40c05031140c402040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 386689541 1250 386688291 386688311
    0x10315050a060c050f0f010b010921080708070c03060b04061a030601030e03040801020708090103110711120304170606010807020d171005060a09030b060103090c03060b0607051603030e04 82
    0x759030301d1184101c1c000d10080901450401c03405101804050150710291121042180d0089018040c2901d54a000549486021810740d88013072580b030801d03d003103003030795000c251030365622810343d010346c105a9102c48240070340d1001074052140070001d0342c41802d0100381070600c101804181d42c01500811502e6111401c18409402c9210950380d018800b40b03000728883d0300ca02905401d6104136040079903154000650841800700d030a0040881800c00ea0341080848001c21035490103000e50640204070046d503c038516201e14098009648005061064910745651040510058008039440150350381180e002c03c652503030490240c5074461203a00103442d2000c003404009284180c02000c000c108000100400c00c8101a900d82d0400703440c0c0584102c2e521415080058105040381c80111800b098503c00142a5407103030080301b08155015113090740c00c07415541d03604080c0c0750341c251058111906010080c0420010801e07590003141c10040c591001303045080003450301911b01042405681000c001c44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 386690647 1106 386689541 386689549
    0x1803150b0d201e210c27010905010506030f09150403051c1505040e030d15080c03010b09010311010c0804230f0a12030903050102030a0b01031505 64
    0x90002d002100c0d0301c24400f50300303440e5089038402c0b10821080c048030701240981518413081c1d455034844080030414400e000061a80720780d01c44150f40c80008041006070b0301610b15140d05110942c140404a00c00e440003904500340710343d4050002e1110401804107560408000803011002d0925050080a0750840b0000e56100f05010000030241031641c410601c802c0308100046203e0303403400c01000000d020b1100c0d940040e01003080441c2c050350b5140310366440c1d03400400842c40418140b841e49460115280c1420340240e1502d414131340595208468113045079805501082e54803c094012580c0c004450300081003a0b5000c43c0105240328a001c3c0d000d40d081101c1140100511030004000303104627000c8030300d5041000c940c002d00102c10032248805105009081c0f145005559603aa0382c01ca034001c40304007001580e03d1461100c1d80d070303150003910251413400101c1d580c2036003440001 = true := by decide +kernel

theorem cover : BRFrame.Cov 386510791 386690647 := by
  have h0 := BRFrame.cov_init 386510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 386510791 ≤ n) (h2 : n < 386690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
