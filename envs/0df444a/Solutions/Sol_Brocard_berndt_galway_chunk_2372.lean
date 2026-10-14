-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2372
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:30:50.446804+00:00
-- url     : https://prove2.me/submissions/f69d8827-2515-40a1-8a36-d3cf7528bf9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 426438848 ≤ n < 426618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 426440098 1250 426438848 426438871
    0xa0e100c30030b0303070602070c0f06092303100c120e011107080913060303091502031c02160512040306050705030108151308031009060801150b07061103 68
    0x2003204100528821150414a09071007008128a8040a18881120124900c00c0603220a40072003e6142402101c1103150817000039541ca02c482e04120b0900c2d01c0600c80c10f0b8010f2a00c1c00d000607044c0c800d45401d0260703010940c11a8580c03d2400c1c04543c90151a0006a41800f40e60b1140b4614a2030384203c51504610362168042100c0c00c1d2218011038a21401548569041040c8036092946180c211440300d0380c0101d02c10340310182c40010410303412040e41c5481840303150410200c21303d07030420070f1142220640c0c0981030304698a404101d03200d00500d000002c0750401d010b41045621026000307080c0411030309203041c6880141d1740301c1c01d280c00740308511030319000400036003481840180c0c0201c560114003801c0080c0b4551500448569400908042388849810080850040e8075850345071142c3c1030308000c9603620703410304007902c44403840305116500c519440d01d4800950301c2030600981c11105001c000e40104186060264540c980c00810202ca15a5540e40a00b0781c160004010318040c2e20070500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 426441348 1250 426440098 426440117
    0x501050901150e0a0507030e0d0302030f060d03080f0c0c1005011e0e041b0302041a100806060a0c0503120709030309060e090604020c01060317090102151b0a0e10 71
    0x111070840351451688484000d405506001a188580009030043c0700d03048006120381c2c9441c4220010030b10b01810480c0b034007802c41200c0400c0c0c0c1c160040c5007e2048011800200d8548500304000301c00c068000501044510b000a4888400d2201c0b446d882003100c2409450030842c62402410030448941280c41c20fa91032005101080c40900c2d5042c0c024550000c4107207450810f030321005030801c0180b00070000107010082c410418181c1b0001802076074090030a0019007034817405095105c2c00304034018092070740003030800c0c4143c0c414040e080c01064060412072a154186400b203071400aa0030082d01c2c184410030030440032034070f08146144518100d0343c0c1c40e0400c07800c500c0c0050038540141e103c07104104a201402500c1c1d035445d40c00c1c0b0380080d02103c0060384c0358184042c2a024214580c0b02604540ea41403a0070782a1b41180d0050400320026800e940308a2892110400614829518000315010f019204014041d200008007900d101c04c0c1080580b4062001c00152807451410911000804004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 426442598 1250 426441348 426441361
    0xf1202121e150105090705030612070506040e07080619061b02030d051b010e0d050c0a0b07030b040b0406081009140307120f11150a02090a0b0403021804030c061a0d050105 75
    0x100c02ca01414040701d521500c0c1c104108001d1180c00040c11a51040303028441d251111502008100001c04e0090700560303c0359960b08888038440000c0b500c82012503081000a802480c003952500c41d03982c4201d0110021a040441c1194401070409025007400d10002c940000341c1d03030800840070510703400ea417210b039185118006010102c039900402c000340ea0402c10b40302c0920300c0206003c0e0a1030024070300140c0340d1b403086910314a020510314001d050403032503805100c1055816041020024801c0e10140006442c0ca03060104840c03180c401c401c05a0042a00e00c6469071403608030380900e0380a004d408104090844810703007107610040d000c40e000c010304150b9104242c0c001c424a0980d56a0f070500d194440511068103440c0c141ea000c10142d2600840b00151609031994141ca40303030746014100a0b0140d864045110081d4000d000c107030311030300d251650010b001003400d8503d8401d6038150ba408020300c03615a111005004940c118a6030081d04a1500000740c0314016151a068040e0002140904101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 426443848 1250 426442598 426442633
    0x6080304060f110c0f18100305010b0d15050a0209030f0607080708151210020c011512021e01050f070503091f17150d030203030f010f1202121e 63
    0x500c0c00d000e01c90071282109a00c5000300780701d042c0c0e0078152600301c60b041e40c01c4001b03040c8000210101c61000c009000380560704a800110200b541c0c8100008c001c2500c4603000c104691040a84c000d10381c0b0b050545c0d4900680480e00160382080000e000075040002c0f4034006414440d00380c10100e001d078000000c00030840d41c02241d403500150701c3c0c20151200e0920030307400d80000241c5035440b402011054030207920003d08001e0fa4070f901034845811909c4180030f0100b180a0524900450080761501802081040b040c0c0d0103040e1103580107000040307150400c002d2030001243d410b00c081c1408000c0c04202120000780c001801c20502c100c1c081c5548000050030010304510005c07800d541d4400c103180c041405900f1018214101c080c000050707450f9510a105000c0002c00c24901d2034010342080c7c020810550000302641c0201d045004988840c2e0f2601d400e0070041c1c51a1254402d072001e40d000d00700143c00c0ca107004811401e01001659110030000e00800010007a0744800c10040d0310207089031007014001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 426445098 1250 426443848 426443867
    0x121701120807080a1139030c33071a150f12070608040314070302070b070318180c1707030e0703060e07090506040c020615130608030406 60
    0x11120664400d0a03140e0640900515038000d000240000d00d044029009002060040080f0011140b40c100719880c0181c8444d0740550040600c088103121440c0e000300c1081d442078a220240c02855040c002c0010490039100102100984141104000000d0300203151a0300f03086040d00000c5590361aa4600315102000340199540c107001c0042c02e2215200344e2010561019074121401e01c2c602088000040b003846c0e440c14035403003a10030880005400f540101c0454030450007074a8075201d0b4045050600403503c5400c2c40200141c0054500b80882c0803440040c0541034081e140058120400301c401e20440c20041d0000007000c5500180c08101040b1800707110301002a6113010020321042d900da4109581004d82898145510340015405116080080e40010341c1c02c402c052284441c0c82c003040d034446019016200c0800e0602002520606080c042c101440880d6802000702d6074a40d4410036240110002c015802001c0c500c0c405a03407040d41c020304002d045407038090350740d4074607154010381841344 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 426446348 1250 426445098 426445109
    0x80105010e030c090601030b0a24111516140d20090d110105090d060605100e090a0c09080102040305031c0501050d030c03030209091303141e0c0703121701 68
    0x2d003d00500b075448207025550800c100b03090110704030010200040c160070144c1c0000515850f40c50340035496038590b421b20440f09040307407210714821908407006921050740c120070444c031100d07c4010901360f441c19140401c90606914002c1822016003001520710b90002d188060065224039040b104200c99400c492401400d0301d0b5010b140050f1a4042040c061519a0103410414003038a0012964000c10442d103038450000c04c440c28240c03051401030020021030042a02030f2144440046419005928010001100500b0035105590f00f0001501614140c0007a03c02c100e070381e00e40011011024000b800185104a0103561902c0c900305150064010072189007030514104001002a43c988400380c070080c540501c2e1280074080f843c1003e6001c2e02ca01c0b0181900040c00000304850505203085a010261095441e81d44c95210701603942d03140c0c0070321103020b040300070740e00c51030380c1d000517030764010400441c3c01801e840520f503480d00ca0700201c0c1e04108007000440c88030111550f541c001042d81743d02600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 426447598 1250 426446348 426446353
    0x5010f060b0304141605010e0a030b01171506060f180901061112180607062408100b28050409051f0207030206010b0306010c0b090d0f020105061c0c15080105010e03 72
    0x44d0f0060045e1700300c4198030405050085155400501e503d0f000100400365400000d50401c03569036a51b070855510502c0415a09402280504c1c000b404000f1001c50184000504050030315070b04007010482544607900741d08003002c0740c0c00f003074030300ea1030f400b2303a0600070056521801d140c508900c41050401d8190006440e8480041015290b0400440612194800143d4015840703030a14540207008000c0b10904002e0b220100e00084c0082c5502c100c00410f0301c6230350017690b0f20311a1022481d41611020510994011b60410804010741022421404503001d12007400c10500da0b1100440c0c11501116030548650b0042d8080310320519042c00d520f410320359405004c52400c407550720700940390078040c000c4d0011100000b02013101d40e0b1050888600003504101040c4190070082c650640d20890003100d000401c0d54003c0100040b801881400d20980c4c02030b198035001c0060100041e409101050f04807080c403803840c80450041ca07011200c0d21045001e842c1d01d80035504000014002c1059503c2c0e291195 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 426448848 1250 426447598 426447613
    0x28090b03070303030207140a0f03120510180b04092012070306021b0f010b04110f030c03041704060c0203071211040b01020c12030d050a060b0f0705010f060b030414 72
    0x6840000c1c945048039090300e030040c0c41d6001071400c1d003c01502140f07215000e01c00c2d00704d20028040031900c40900701d4401c1c1c458480c56980d100609040e268200d0340c5201d04030000c8020044040460041c0103200380c10680002d0010425001038126188a4020744480b05020b099182100d803001202d40345084c115076600c60865031402a039500e2a05000c001d02c080d070040742d00c0301c5099981000320000e400341000e0703409905080110300d00a01740316140a20503401c004808510004203001c582c09201d444103400d2442d6508008143c555202810845070044c90140b888e0358580640080c3c809898165503189a080082c0105413078140103400c1218a1050b4201c0500080c0c1c0381d01c640e4060303100580b00824040d08142c0140d05280800401540080500407200c07945640400148030440b0012000c021035120540c0d01400c1ba0303c0d80c043c2a02e030607010071012041e010408050307c8028810303000070441e0340310404024103840c3e01394040039182002005020400101441c00d42e00601d0203002800d01d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 426450098 1250 426448848 426448871
    0x240e040215070b0a02220e09010f020f09040e160e01150e100c020d02030115061407020901030b0c2217010921020f1c09080705060a1d2809 61
    0x2e00c10b01400309913990340d0010f0440078504100003055079000c20f0404910708150f940000c08040501190400c880b940382c090401c0000246209445500702c24128141c201140c00341404000c000341886412244200020b0f00d40152a074008807002e44101051480c1e154505846145444050f10480d01800f421401c404800c0d1510011040d03c80101c0ca441400074003140003060ba1400f041d500a901035003040304400c07080440d044584203d4119542d401050060410204168001e07030b00300a611580b60380042021682d8168415001032004003080c0c0381c0410402a40c80c2129050b015013040c1e82407070400c0022440001010080300713140b600030f0041821607981c440c1d4400c03142940e800c0400c005525800c6c814801c02800300100b0180045802c014004604030741c0140a10044000044400c1c42c0403038022804a074003411604080c00540c2425860b400550f0003044000c41d680d808080755507003408a0b9500c01c3e10745195060a080903a580c180c00b000fa84014019812690410342000d04a01c00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 426451348 1250 426450098 426450113
    0x11010e0705030f0321040204021c020307270902030c040b0a08040309060314040308150402030a06080607210906090b070e0406090e03071101020a0f05030c01060e09060a240e04021507 80
    0xa1605d4005d24424107503250701c0043c009004458403034818000910040c84100360300d50065004034602e0700d8020140300b212070500c0760034200040414840b8103a130820002d50030550050f542040600c04090b003040c1d1105400c2e0002e80044400b40002246542803005040c2c0224210010340741d02d1400740506065800d0251082c1e501510080801c413010700014007201041464201d44039000300b095590303007481034400303010700796a01803100c082c0180c4001c911964003415058011001c1111100303c010032a1000d07038001c060103c015600e254540101c10001540e04c0c17801442410251034540c4224600000c0c0300441e81542c000480042c6024070000d200c08000041d01c81035607006510403600361481004030b044c04e151800042c820711001840303a080000c040054420305071440001c00005603580c80c9101400c42c00c0d20300f804141c2102c00401e24a01300d030b03003181c0f030340c60b08104010301d616251174540345210085074050022107000405200451900c0190171800f00002c041072410040039444045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 426452598 1250 426451348 426451387
    0x42040e07110d140f2a01020313061104030c060f0305010902130e040204060b030702070801051e06060c1507090302030708010203270a06020d0504020f090702031911010e0705030f03 79
    0x1c3c0040004000d20b0200000126031803440e6600b8042c0d00d41e035810000e108402c01e040d100c2e0040c29070707180240c0c0c2c4144051007a64440c0002c0101e07034400b02550703254035004014024054154076030801011010901e880100310003000c0da07540754114a21003e04c0201102d4042e00003403d128010002c50241c0d042d40c1c00035030203481450b61159915221440010010086540200350120000c001c229866401260703072001ca4a0500c024000c6a4800c48001c0c1602858400c03603040700c080101040b032504080d805488080540da044076134180c0002480c1034005000c071109000216596402d10840c08d0a1102c45c0040404000079801c506040d07424030041c0d1442200241343c1c8140304807003060141d003041010320791600301c1d07011035840114034080805001c086400b6800b86c9104407140015080c200410340c81101950b000d1030924420402d04a500007001c1407103410880207900c1260080028800d02c03203800c50b400000e06040380342c0410b05007844900302803441190014001c55580c1c20685150a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 426453848 1250 426452598 426452623
    0x191209230a051f150b0301090f020d060326030405032b05010807080f01050f0a09020a0b03090309040b03211803011803090e07120c09080123011442040e0711 69
    0x40307079211727000c11080300070702490b64407075156410310000000b4800d000d026110002c4100101c1804031646007034090003440b00392030050085d442001010b1074440041ca1201030300c1c003c0c48411034502d003503582d40e4013030f1a021381103a00c880d00004020006c80d1010842d0300c1c0503010b00c400038050351070818047e400d0b80100602010030161289403400440d0f85640001000e00844141e080d141e0030700b0380b111956a0881500640200c0c50040c2040184c5400540ea100c0d0300c00705244030b0b0380c07418000714070745003034111000514113070b0b0062804c07506554082c0a5050501c0c08000f8000925100d8280103216840781c0c1d000c3e02d1950264130508c9030f1250b201c0e030b65465420710100007041002d800b04d4221901e5525600442141d4606607900352210008252412840524014005c5698a40c4113400442103e10200c607446681a808107282c10784021403e43c1c034011441c82d040050420f500780c120740608000c1840d09400700005c083c490205003210340b981001e00b52804226060301400220f5503070b43c844581c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 426455098 1250 426453848 426453851
    0x30206011202030304080a0b0601020d05040b09040f1808070b0601030b0a03080a14040e090c0a060909090c0b1c0c030603030e09040c0803191209230a051f150b030109 73
    0x15802e5440800841c0c005050610403035007880e466040500310b582043e290076005021b10404149418403400c00e50741030f1144000040c0c90719410204110041c8040b507641d10395241c0b502c00d804082c4100c200d402880c18055001b42d561a0111f00c1c0422268130002d1031a8103052611602204984500007001c05495000c8001e954070b4a0540d02541c6400702000054084d01c00020301040400180340305500690181c400c540c0001da8410802030720000131300403d00000c044540401581c0740c0da8204424460141168810894a030400640e40341d02000f95041b0100305103145800c0886288034503480348000d480c04001142c21940c0c02003040c903040364402c0c402c6000901060038401e0901d030f0040201184030840750340d01301d07a40718521102d1b030b03068203100840c20490580704011010f010b40d01080380e102c0c0c0080c00c81640505110781d800105000064280701d21351890000600811110a030344051602d1a5000d14241c00c0c846c094490361480d030981c00740031107c10851030321401d0569064500c002d90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 426456348 1250 426455098 426455129
    0xc140a020901210b0403020a021905240a0c08130f1d0601050715021911010c0503010803160c08011103061c02010f030531050f071802030727080d0c03020601 69
    0xb8202c8c0f0740044858069400712000a501d8941303140001c400b0202e400070703108440120024503560305080301c2041d44240030300007040740c40701c0b2a00c02c4010002961003811036a0030503804c031081d01c24030401d41c2c01c0004c000303490800c01e0000c206901b0a1140200300801e12104918000380020820f00400400034400020303010300c0c0c803401c0c01640545801000c0441c1c024400300c80144000c19480da10030b1b0b000059481d24108002062284e800c4074162110040114905215100da02004820500e0305403005e2051400c0481c030b05200b030140442c1e44049055990301e1303007002c10400c510007480042c100c0242c0414000b000041c2d030884502100c0c1c1c0701c0745c100041d0b40d40e07500540310542e00706030610034141c027414414008140c80208141c1c100ca4000e004a410800522103659510320581c082e0034860030340301d00c250001c0201c40d0015a8070400ca131034542454810090080c5400404110f00c920070b0002220600454400300481d006410031440d15400b00556910043d484040601400c80440c01c640c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 426457598 1250 426456348 426456353
    0x1207020609040b040912080c040303090506030604020c07080309131406010c06270605070318060e03041a0702010e04050106050f1308121e0702010504150c140a020901210b04 76
    0x602c4403481c000054018001c0a4091818418a880c403603400700105034000c1c082030806048d01c0c00c0c5d40649915032518910707642441700708500303500f00501d4103520680801c00440c00080611100b801080c0c41402542c9500c40c040803c172030a1a41809814000c0c94050311401c880920007605401c02000c3c2030100c0e01151505000014090a4034072b00038916601d4400004a03481c080680715081c000e180030041c9817038071101281564102c42100320740e8400040c80e9004641181e110700440c80c145000c80745065a1144600264003040014a80804d4085400d80555810408a1114440c12a0108a0b643c14004041c12a024800c07800130702c0d88021582c40012103040718000e0240400e03404440b00c9000e0718041b0710f03480d401645095008807070704059281480f1450107403262154141c444030300f820300f041c55442c00e00c580b41a01e0001c0209204038000400c820562042c40000454003600d0714003224014001c01c0360043c2d2203028112605141080701c00001945035a103254407402d1903401d501c907030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 426458848 1250 426457598 426457601
    0x150e1e0f1609031709150c06011e08010501060507060f2708040b180a0609060f0e1807050a090609030f060903091a04030209060d030903170c0f070e09120702060904 72
    0x103400040145602c3c2582d9511134003d540034221150b01151054210441d010b5800600d0141440c5940c207580608014400ca00034025a8015181840c00e01000320399100d01140c20b46000380d04c0304011440014000d002d0080c98060503411600040c030510202c0800007501c95211046a4042050001c440e045030070007424004480040c140500080d484002001c81c0203c1105100941485007505040004249015030300788421140c031511303440340060388018169100d4456580d81350b0301c40e801c0381c4000c181c4070f411520640625032947e20144c80d80301c003281c050180405034100b8014860f08050420008040d4410b4018095019a010400030b02e580740c259002c1e50250460048540403040103820404840080c1044900032580a007003a2104000d01c5901d600501010780012507401007480810001d0312078025a0241403645841c00301310140305400d0104540c20591550030100080014000503040c85800240660280c9001c2c0d00070014a0104d10a01100a006000104510f100c0d580d45 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 426460098 1250 426458848 426458867
    0x306070806041409030a09062309130f0b010f03060f1a04151107050d082a0d110c1c060b01020c0d030c060c1d0402030406150e1e0f16 59
    0x340351120f1503900700143d038540c507504100000c40000d0b144000c00514144a04030960107440c0c004003a403070180b120307409240340d035015004e000e40051000940042a440603c91a0443d250481b000201408000001010704114010403c10542003290500803940f80001e1581111403a01d25a4060f10140308025442c0c00390b075000110a003d41805141402e0300040b921031a41051001c1e20003440e00c403001c000902e0f6001d5009455820103116001714074118402c2c258040072075004100034541075501a52418096502d01400240d10000026400d48200250758200300d0455840558020503d001086040c2640010300659100c100001d0264024003e24400400c0900000c1d02040345003130151070301c44025000c0f160301c0c0c0f0303241b00c0400d4544a402c01c0980b2003181c425540b10188458200030194001400607140c0b1983c40031924082c070409417884001300b100207802c001d20324022000c0d06059035051450501d0484a03000c0000320541022400d5111581020901225500b0705049a18a06 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 426461348 1250 426460098 426460121
    0x7051309021e130302030105010e0901050109020f3c07060b0f150d0e0709020711010c05120c0c0901031a070e240d1103100801111614060a0c0807020a02030607080604 73
    0xb2304000400d21003160741c8803510030704401d4001d1000d13990b10f16041040307129050b4065280e0f1001d0100c403494a0744075001d002142d070000081549684801c10714607a9184640740000a000c00103130344810400c0c5030066400801c400c81c2e104100c038080e400030441c594a1040ca00300c000c0c1e070025403210030034140d41c0300c406c50100400c12a00f029403a0340c80513000b54003118013070f5400198500c2004503503226030010b40c6220f6000c030141130b07003d0320407003170110ba6040300781c511515004500c10400641c0340ca09260707000b1402a480d440e24890071103051010140e0182420040001d90321038000d140d12440d1490704170a003a84001c614808482100c1b81c854090300b00a40921030501c40c80c0e54a041c05035000d14010201e11100840213550f50307028a08840d810a04804a0340040c00640a42e402d00102c024810380911518500120910150381c1005012142c44903e10f540f00040b14800f64840c54403075011040e40002d200c000481d0700002d0707070b902c0001c110300200210f010002c0c10756203550708021030084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 426462598 1250 426461348 426461351
    0xd050702030706050901090201091e1e0e1e01030b071106070c0b07020d020703110d1a0709120b161803030206011401030903051e04050907051309021e1303020301 71
    0x101044000d40740d500c61402030b21034508180124004520612680300f070290305841d00d11005140c55100518150307640c1030481c0c18209003900140e07001c99440172401e0201401d0364044018200304c0c4240500c2e5000c1d003191020745810542000000c5540c0045055075001703051441503030343d032860444514010b01070710303505806150f0910200641280041c81043d2080040160759a100310b0102d81d900011003108005910001c41000410350206110614044c013800100207a520364943e000e50f00700030144c000e0020f100408000191754004040f00141c2500720361001601c2490b01d03100700240000c0c008203074440c00040a0700c0494061408000100050a44050020365030b0901a40b61807003480384140414403078500826070341c2702c3e204010f07034581e054442504141c072542c8680b403100107074802000785482c20000030880c1e58801181e42d1007902d0b540d4940c2c0c3c0d5414280c00c180d180000340d40c80003444c640103011070301c44105e0340702012500400b00c145150f100e0b00705000d070107a80c110941c8007a4155 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 426463848 1250 426462598 426462601
    0x6060e0603130512160c0501020105090a2019080c010c0f020f22090201080a053d092c030307050d0f0501030f02120309010906081801050c090103060501051c0b060d05 73
    0x842e422600c10245c14000d108000c3c480360340b1801a82a61421910941d81c0d0308000040000644003060340ca2482183c0d03030b0381099112460011591000c4d121440070340d6400780d0082005101820851070503801c05c280ba005d00048810750740c5205802102800078898001e40e2820f0845444400b000c200042000c0e2440d18031508046001005101c8814103074005004140040c0209810b400703124010500d200d850800c0d54102843e8016200041108281074a44904007200d80c50030003003540c1c0508801100040e56510305002c01c070b0385604201400c2c1514031040c80d00c051460012054a42c0141c0c0c500745150313201c00e0350301e9200052402c852180c1c0c2580c0b6160010080c460300420002c42c25100380e540c03a61005582840e03a540f4012940341c035000829455040c42411302ca10382154014113401c0c02c0c3d04980e00c0740c2c40c030315003034a200700e61502c0c1d403a03404a1031031559070341350003080c2c014035003070a0a80c03614600303202d0903481c071003441404e1441c3c50f26640504400c2c2c40300d60072200440000282007106 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 426465098 1250 426463848 426463867
    0x61c06090b0f040203060d0f05030403080c01050f25120f0f09050c09101203050702030114040c0b0406271e0317120a0b0303130b040906060e0603130512 67
    0x502090101c82d0003074040d040c00c010182018800c03240980ca005080450b00750f042c0d61042c030a000401c504403102d000a210000000385594041c4c49405552030002c1400e04d00043c845c0d25031840180f22007103620100b0000103c5004401c00701e02d010003240343c4041d00d11034100d0780001600305011700d0b0080350328010500d200700c500340e4040d1948500c12b0045e19060f481070001c02181030000d89084102d103440c12002c01401c40c100100c042b10b0303032007810201d0800410390006403c4840b0580c0301d2910715101e90400003040910740064019200d00b100c2542001d0070400b0040000c41c000c000100c0080c600a00c060005502d08154002400e840d00341c020f0140c0c0c28640c00301c5202d01031004445025412502d81d64840c000811740c0d5070034010824070825582d5502c40301e07001d001c1c190000f68041c001003100d10041203080d1400e002920b5031400c400e075140d162400f00400c0b54800d81c00a400c00060000040099480c00200d81d00104528183c240205490403c542041100c0e032810030302c1035001485610 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 426466348 1250 426465098 426465101
    0x71e030e100e06060a0303090e09011401230402160b09071203090602060109020a050304020409020f1c03082508040812100501020d030b0102030919031502190f080105061c0609 77
    0x7090b01c040382928070700d0b2181da0510134000c4440c0001030114880110900a14a5084100da40a4245d00000c142181003024401038070300d0a0b003102c112440c40c11291f031290b51810448006408090710308528003500d041e1241e025140420006040c044a48040740743c3c40c1c1c0c100324000103072090442c2140030044038078000e8540aa98820f602c05030140c8400082d000c00039100391440d0310101d886040c130b10381c1d5070350800c0000c04100300100c0c3e00050480c03c442032500c03103500c0d10203003007a08414500310750042d003000340452000034104602649030044141c41195000042101c09420b03050007990780c2c95624003e1014000c0303403200f5241804000130000e000020000c00070842d03200381c090394811100d807041101914001e00c1c0ca00d000d40d104100203c564281201e0b0030407041a02012100c0c180c1d203030342c1d40380c000300c2d20116540005900800c50032801d603403424494802005d070b4101401c0d110314883c03000e070800505105480c070842c0c0100d0003a4040d01ca0104149034040c0410341044031949134401c820 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 426467598 1250 426466348 426466361
    0x30e060d0207141f020901020a1a091218010c080c0102030f010e0f09060610030603051906150e070c02040905060708010305061608150604080d0903021503071e030e10 73
    0xd61025081d4000d00c10783d0b401291119600140001d41c107188004440c901c4d0282d4824105141180310300d103044400300301c000c0d00c0341071103880c0301807404014100510118038166544c0d8042140107010802c071948410303401d914404003d028280142428005c5c1040512030180c40344028141d4000002c1002199400312910705a50240f40fa0b8205503c840b046150107100c1142d4070305890344003001242e0700d03103801c244104801b0074514003c0b0741c454481c2d81d91400c180b414049143d10010000300e800c1002014068001c6055038209030b40e040034a005a0001d1921026192505200a1640c4d0009540761b82e0000e0346440d400100b281c0c01410895401408450244415508d5000742d8010400c3c030000c00007510380310b190a80d9015102e427150b550403070562070641d0300c040d440801080300056075281401014281c54181d01c0d070301030340c03490750050042b2000341809100d10454200204101140c0111901c014a034800503c0030416941610980040000d041c400310075100c0ca0034282d001050940012 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 426468848 1250 426467598 426467603
    0x1b120d02090907030908071106090a0305150610020607140904062409060c02060d0603050d0809011a09041b080f16080a02030d11010b060412030e0a140d030e060d0207 73
    0x4102c103a80301c590407401c4848580000f007810108011840200c2c0d103010340d010112400802c03403403900001000080d00209039034070031122500008c1d0124940c01d80855081d50200090316007109058500300c0081d00c400d0000c0000051009405015003080d15010642c3e074054800781040284544070248800c03115041c50a180071454407030754402600303201c2c0303503000c0c01c80e1000d0b10f401c035104041d9401c000080d08000459800c0310394486e030000c0401c00070000043c0c01d96454a49802c0b42c2406c51001d401d503801d16080d0702099045041a121a440710f80209034050b0700000b01030500940070184103540c09455001c0050340c41181ca0710042c2003c00b08410740d25441d00a0594256a41c0b6105183c681010383c0b80030750b01d0340041c03074610758450060b4204200c00c5640c0000103003c04008001480b130790481d030869071110203845455410550490120020414120b0710000d205190000c05200c1b070700600b5034540200754010400c41098043c070202d59030080018026912018203100d018025000441c05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 426470098 1250 426468848 426468859
    0x4030609020f04151715041208010b030108060a0b130f050a0e01050606090103020f0409060e0f0708191a0307090203040209070c080a031a121b010302040b1b120d0209 73
    0x40c90b03540c038007482400c44080000d420007500c0c40c0780007640c80d414a00004c07468164080c0000654801034401c102c1445607100c0d80c0ba0000140c5070345802406100140c101160b0040104014001030000240c0b00717174040103010b03011503007280e440041607001c030744101d4000720142000d40c820060b49c56134011910921281b0010450a0440c41d81d4500780c4000303603880e940141041000c0340d0790754400d800401e001d491948085181a68414100c0701710b034040d03800004030502c5501848100400b40726960380040746c2e40b6003030580e070030700303c013824607100a0f580400405079446911418040312118901000c0c07000070203940c82190b13600503000183d03100702c8e0f0407841002080300213040580a6070007000b200b40c01c5181035040440d400002e0f0001c2c840c0e1440c1035503546011100e47c50503662040185101c20511000d40914404c850346101100d240c10301a074180360052005000d0a0490026110642072500407100c1850603844a5400c02691000781030803140c00041040114a50b40c00801e10303048140c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 426471348 1250 426470098 426470119
    0x11040b03040b190b0f0603100302091303030c0c021f12020a051b0105010e0414150a0c02012a030207080f0a11060723070201030b0619020c030a050d0f050f0403060902 73
    0x5044007202c41c0b080c0c505a005e030711040c0c40422401c00d10080d40e80035022072400d0a40e580c0380c0d0001005460100c58496520705446108010140e1501038494602500c1c1030503030034100e19500140740582003410209000100c030040000b403620a240402c64842c11210841d41c0358425207000740f540d03002e10803111001d4002d001d01e13884401e051041c64120f5a0860051843d9201e81c0d030307a03283d8881c5521810344144600035210559903042c07210b183c0645000c0301d0000c2c03002c42c032000107801d4494154103401e9240785220503800b0301d103106075552001c040900d0010b030340d03510390300c0d0861041c020200c020401c5000400c28034142604480500245956581268032a6444007402c0716020b0300045c40101e0901000454004c01000c1c5020f0080544141001328811140402043c3c03990040e00d00f03003081c4000c6ea402804026018031600402203802e40142c8007036003035520f03055500c40c0ea4181d2107040101440c3c06600c414807400950b00404010803681c2d03075031a541e08282004e840d0000d07050744280200c07030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 426472598 1250 426471348 426471391
    0x3060d080c0120040303081602010f06060305181c050f130816090506030c0114070b151009050f0108061c1a06091b0d1107080d060e04080d11040b03040b 67
    0x3004e41c0c084a52680e81c01c841c80c3e07684e80f9100f00444807194403006564a4102440004100f0301400c0080c01d003540d800039461404003ca240c411402007641c10385504500d041d040792190b0050032084c240f41e10704200c0da031980c0e01c4224120510a901031040f5202c01a040071441440105810001e103e0305001890219110245103084650950710158140d100640c0c1000302d500030301202007000d60340d03450b490a101c1245c54011030300c402140c403840c50580540c200b4981c0d1511007198071040e040e52030800001030600c0d02085031050fa001807541401343c0d403000543c0c0e0395504100c0303400000c200320700000714410354500851650494950b03240c40e85000000624581803000b400c61056141c0030721303115032810410000c51aa448024410029903c580790712000445210007044040e10800c1d000d0b58038601c02d07070030070101e91050300000350300d0424400b40400301d807540003950f80c130140300c032070004424144600101c0c040c850baa000c1080041e001c010401407040002e11144500d403068984000d056410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 426473848 1250 426472598 426472661
    0x103060e12120105240a032703050d020d0e10050703050121061d1f1503080409020d0f0905060601020106050114040b03090a0203010e030307180f030803060d080c01 72
    0x35540740c05403060041080d4603000c030344051385ca4210524112490b00020351096294052070461010a0f03d80c00907412000102044850b080410200d0008400c015075008007071388900c10014880b160089a540d0b000f15080d07110385861649030044410075160401d00c1c102400d012915180828906400058045603100d001c050700c408104031031207903551342e50711500102940c3c000000c10b02c0f002110007a401c10108909401800340c100c43c7c68850f1302c00d810f000c040d1504091026516010b0403000c000040000050320309642c5500030240e228080410608014442da10103104a103003010020b0060040120f43c880c02500b00382d0091060300e499100655040780c1d07108251119401c104000c1006041030405036401c02810010345003108082c0d00082c1c20340d07c012994421640001042c8080c1c00d1700600c02c140c6515200000c07044e00ba02d4070b0360b400c00450203840058007600002001950b02d59504480800c03440d0704c051144d44450701802c0d16402003a20705900c0c1c0041c1c4000615031183c5800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 426475098 1250 426473848 426473857
    0x40305060403033207090305011a130b06070305180d0c14041a040209180c0424051207020102160b1b130303230703050a0f0e0d03140408060103060e12 66
    0x40f03c0d40543c0313030030b50382c0d01540075200014060010041850300100004100303000d69a9407050914000703022980c080c0402a148192031060072704145004ca170480c16031a000203444000782c25040079600c40380242100f91104001d0b130361059014014a040f41c080181141d494802e95100112000090a030032061004490341910b2a000c100e80030340c400802c500c0d058004000350b40001d00401590a48083d901e100d00d6420b0760040024000894144007514100c40f1280595111034a0560340403401c200c00f0f4580e1003515400404802c0140003c0d181d14000d40466100d154a0507440100201c1800c00784101c0c0f01c03d8070aa0781414203040301c0013900304010241c4d824071140524180300c4a20315a4103603038022400f01c0b100029410703281c034044030503200c001428030345020f40c0b151551001c03103503002010700001400c02800d1000e041524046a260b51210452269040c05c0100f541610001c54404900441c2d01271451032050000200c1000119005885400c50440c1119000e0034004980402400f5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 426476348 1250 426475098 426475151
    0x60c0614090a06021620030105060102070f0302090a27030e03010b010503060d020d120207080114241c030302210103050a0809010c0b0103030c031e02070519050604030506040303 78
    0x40402c44041200c0e5801004895201407240c1803401d007a036034110095001695200441c80c0711074146c40c95050030f0003803540c00700b024400780030041d003000384075140c8040c540030180c061124880010b0304032046511110203100c0400303264440840d103400040d154586e880301140020001c0420480f03a043c1400b85d0140080e05850310350440da14030041c0410034052000c1a40e022134140050408a42504030406500c007a690181242c1400c3c140c0da0390a4503000c0a103030440342034100c10041d00900a800303440c0c82c040c01c101400303d041c100c40d0010b503000d1003080c081c2c4000b0f10f00007080310030550143d0082014425488049204010507a548080c042e403d10015000e6041901b00342c0004040c10020068914141801c10103480309484403a83c10009800840100310284000f005240c1c1056040290306580c00b41c07541081c1e50048000e440e0b4640d80300740d078061070510480c40c00034682c0f01c030104083d14000c0c0c21152260382da030030082d940d520b003078809801223403514100000c401b00c62090000c5011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 426477598 1250 426476348 426476353
    0x1020f0309130f090b2d0708070e010201150f0303090504230a150306020d181e0305160305130902070803060105070807050715030b030312010e06030f010501060c061409 74
    0x294580c0700020f0a2541c100e0040566078040850000b00400300c003a008400945201050100b00781220005426107030b0001c150750728580c01c00150aa03c20100d90707000c0920b00c0c00110300a00080140d02602103201d00310400d04810700007280d0215481d081d01c0449000c5d03902c1d203904d540c0e00c44c1031204a910f020510102540301c000a03000f140b4680003450b400007044a40010780d05031289014120507516001114101d400262000454603280100d49039100c04112441e0500d00c1030f980c0041001848503010f064103281d00d140003d141c0218150740e0306403184421001c03007030140d180040207503101e45078070040c09200c0038010036003140340d00c25514180d074040321062031519020019103040c1c12501040343e8028080240e180014410302062004000c00101c000ea0178041040c00f40c1540c0c0f07030581c450700982c01400129403024030070780d080c1d0450f590404644059220340e40402d0401ea501c0805200035820200000f55040d4040d6001d8140340c00b41d50200b25400c00000740e030f103500c0c0c03040d11000d80d2913 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 426478848 1250 426477598 426477619
    0xc03040221060a090c050910170a06050c09030d08071d12100b09060123090d230705090106020d081005100e090a090c0909020102161401020f0309 64
    0x40c20407000502441015001c0103000d0400400c07a02e00e421000c441d40a0b49585810002080044009046024007030440d0324040900d4021900603c1d20031b180304201c1303840781c40010801021001d02440e200c0940100d4140081c2c039041e244031a481c1c2c030a6541d140244a04c0f0303c000c49540c4911072141c0115025030302e0042c4c03450203c2e000c081900519003400c0d805095a802c10850381810401c0502c0c1850001c0d0105103480d10303800300300903403c00802d100d06100c50381150201c400d03125501000480b015990894030b6040010200301c001d0401d407002400c40c0c4803c0d9025050207103000101000100f0f072812101015250304c20700c90300140a11a03a4007591284552040c014040c95415a1000c500100c02441503513030307800115000c0340c0c0340c41c48010620004410010307080c9040d00550086480d4030501091045603200c4102c1e036014440c00c02d07042e076100034520440e03100744116200000c0584000480d25140c0200101c81e01c800014035016104180b204141d40b01c0c08000e45250110090510074503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 426480098 1250 426478848 426478853
    0x3060902091e0a092904030807031a01181d04110612010302120f060a060f0906030507030201050a030b03061905070c0203120c1e030406090b0705071809050a0305030604140c0304 78
    0x80c00c06220116040100100c601d1425441c400005517000b0a410952401d42801e0070301624079100a4188000c05081c00500c410050400600601c2c6003000c0c43c22846445000b1100b140f507a40b20b400c42c00d80d2a401c0c4aa0500c00d1400700c00480c0110300544070b81c003101084d9010402288101c0340320841c03c0c0c07a00740040025151030035250004455541c141c810a241200e0184d04100d41101e4102d1380399900c1c0001c3c0201c500e408500c0c070240030101c800300426800d6450f01a6989c25912000341080000160812070074483d401c10081c40b40090704440043c105001300b22001010000182c4201d4500000030392124854a0102c1425030060090f101401c0765100150f0303507502580c0c654995124005030315555000714010f540004400710051500d45003031000003801d50135954001207041c0811f1003104041103000c216082260b40c4648441280e41800c80c001c00503050813040a81140190000311080c0354100b0011842000119010000003c0340380110840b0003090ba500d01d681c82c0c2c2071001400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 426481348 1250 426480098 426480101
    0x30c181404090503280e01050c0304090e1c2105061f27060e031b04023402091806040204050606090909031c060e1611030403060902091e0a 61
    0x100b2500407419246450a040c038038241c40134000301ea144003070034001c915002c0682d0010480740804002d19210f403900105c1c400096690140340600000c00f55200490200018204400301d203130360703807100080c00740c405698000d801025901044410b5070419020b0186150700b80c410544105001040101401c01c4040591201044c030240c240c140504c45180303050083c0c0e51240e551075000180210301c4060f0600c3c000034401c803000c80142d03000c2e50103a000d500d160810062a030112010030345006823940c40130031040080454680304200c040e2010040806000c03a40c00c521220b05001781c0e041d46290311240c420f28000c4094403100011500300c08003042c01441e05401140c0c2001c0000d04803030038070400000181d00348034180d0f502415036100080800040d0404c03507445a038001d002c40200002864280583d0b0030f950010260f140101d5603a000060003802042010048000101101d854649138038041c1c0080c0405e00e010b030701c5000c0305000a807010f50780c25100134107801504680355441d12030001c2c550 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 426482598 1250 426481348 426481361
    0x80403090f030f11011106040b060609040c03021b07060e2101110403060b010e0d111201051003060e0a020f120102040503060c070b090c10230a030c181404 68
    0x40420410980010750300038a007030300c880a18012081c54410200d0b83c0b400043c4004010300c414103010300600208942000403400560050b002281420203558000009075540314a10403241d1091810f107020041da54154080c001a90451a10300210000c98401590301c041c42e00ca4080040c440382c0c079442d101d0501c3c0050301c003a075200b82e161490041d910b011450030746407441c14154400034081020000e111960003090070443e42801c6c2030421b40082c00100d03100411aa1000d02140700b20111f580c800c0e25000c203004980c9001100800082c02c0c00103a2a24044581c0300a5541c1402d040250700c1805001c0341e0a07414a9000302100040400e42042c4000c0803a0105200060f55090200099076101800510b108500d044001650b840d1740340b5118115040244c50308800d9070000c0c481c041251545900c004003440c15041107030004032211601000105480080d00340c600011a095203042c1e096003003500c0c0203405856a017070300c05200d01c000400c1d14003031050f200e40403441c042c00081c90030b0961050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 426483848 1250 426482598 426482603
    0x504140103120e030106121118040809010815040c0905181e0c04030c03060501230f0105090301181b1e060507110303070b06030c010e0108060906030a0b0406020d0f020403030f0804 79
    0x420400d40c0c0303100403030010020348002d623411980081031050b6807804d43c42d404882103802d00c0c0c0000318107045d19009418050300d84507a0600c0300b0030011485090192195020381000180305101c141100d240003040600e1030305ca003900810303a100e180307121409400c0030207115480d01d074a408002414a46640d400d280c000c1d24000c1221000c120120220716200c2c03100e0040d42c0521400f00e0f20b54505051050610b205125061012560f1503445d100c541d21a582e8901525007460070396103a04075080002d0040400441204040038996082810480d1314810240b20300c0e082c920406500e0394400c1d4005504020810f4481c00d101c00403002d010850290740540891030040603c074040031140008280b9691200303505440d01c03050308007040018901000b00075100c074000e103030005500601800107442c0c0c4030081d00e041e208480740d07400503460707440c1000021050b070342060720500716042c281400402540a030340c4813500315083c0320043c8131184540c02200d0480354190740b01a0345d04020741c001c569804026008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 426485098 1250 426483848 426483851
    0xe0f100911091609050f1c060e01020d0b030609060708130807140a020a08030c0a060908070605070f0801050a0f0501051b0d03020a02010b030703210c020303030f010504140103120e0301 81
    0x510203a11202a914030843c00b4800300c1e9031014503010054007085196210070703c01c00c0400000f9501d07484209050940302056902c00c2400340e1145841006090050f02c01c00541d84042440b00c40b0f400b291700510a840c90540954142785c58000b50a48c40d20400c40d03004020865141c007091148564450030b00c20240a022034505021280d0fa59452003440c1d541e20070780c981d1001416809511346510403030000d01700d1070300661901841224607a00c550004102520b0955551042800d0007403680071103100c1a03000074108454503007440f001e010313a0360042c0701a000070200d000104581c1006401b01003521010b40d017085400b072422004484540c0400341c95040c01e8865010740000101c100410441d08036070340c40150319080200030090845006040f102c1c0b01741e0001d03d0801c003142d500086200c071106040485160785d51050000d44141096140080d0181b0002042010740000c0300d098038180c580c00c440c01e1042c82039160070508541000c1c0030242440082c01e8516201c10b009020207004120040e00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 426486348 1250 426485098 426485123
    0x91d010503070e1f06030501150801060806060a020a0c06210501050109030609031101090b180c0f040c02030c12040302040501060323100503070308030714040303050405010c0809061c0e0f1009 84
    0x142d031513000115030088001c40e0711680103015020004c00a50680400c5203014181c3c1e40c50803800a0004002424250103080c0c0005c0003003c042c82804001050368004a46401480d51288003d0200310070740d003070400c03601c8a4490b4845203141405a54101c40c0140d4440076104c0c110f880c5c0c0303030040204820031014800b10003030308015424280240000180240305080030341c074042011076400030360b20711686000c0d003110440d1710f800d9a50341000e40e62031200f501c0000d8080200307803050307240d4440c40110410340c0c400d0030050900c00750b02800800070f80f07201351030074019a6038900046d000d444a000305c07010f200f2884480045a03006030296281d00c9040300585229241e982c1d00402e040c1007182d003059070460000000c0004080d00300505d29540c24608615602d46840c5d524005c1140c0250302400741002508640300052100807800e451a0020003821a85e442e07540d00020807840a01011041c1c0d49420943d010900000109221201d0200c4402420b400b541c0e08040c08002c3c07400c0a01110b14519042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 426487598 1250 426486348 426486391
    0x4031448030f060f10270e0f0601090b0105030f06042408010504110f010f03020705011e02070303061e05040506040906020a02030408070e0c1c060b0a091d010503070e 73
    0xa90007a20840340b0142002e414030b03096408984500501049100038400c07070810482c20400c406110284500c54020001c02d80321754000094800201800740380d05c2003000d11a0f00c50f034045502c5040700c0300c0c5e10007040a40381c1d050065409000442d04209202c1402c0001141403c241d085101070848002c0043c55518444045144504158120707600c075a5440c4100001c001c03181c1020b130340702d0070201c031411081c00172000000c102c0340c0f1038001203003099000310350201044825000064107004103104200d484400781c40c0340f002234000100a400290510304005810303085002099400c140300d01140040500b414180006048003401d0a900301d1303903c1e68140c000c5103207440a082d45008030b03030186683c0c900d07024040b0700e0110135401000070850310200380142d182020084a440042c1c0c1072201d80f0300c51442d00090018030700e9900000d0b4491000603200b10303455002d0034110546e548a000010017810001114508010034000c803500350344290024010180080030455004a5001c520b0031301078040c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 426488848 1250 426487598 426487603
    0x100f0f0207030b28020f0405011d040c050a030f060b0a1103070210090513020c030714150709090e1f05060307090212071706010e040e070b0403144803 66
    0x110b030300701d00c0030030340b102c42e440c541d8016001c400d640c8000c0181541450842c1c95507190354419441601c9c14020420401e40b150508403c00440540000b0001c002002807c2c3c0e0140c4158403051050740082d00c3c10300e40c040510214403600c0c080c3c40c40d03400e2060506480d0340090712200c80e2029011b90b20b10081c840703200180e8403c2405000c611207644c6001c1c00b02d01c2d1005015808210181010000c1d00620038544003030360000c25107842da50001004540c208203201403600300400c4602c020300745400003080214a41d0400b032070204944d8031076420010f100c0d04c0d55a0b16145c00010061220020640420000c010408d4102d0b54014030020305841983d03a54840c9041240e0001050300700c03800b1410108200150440074810a424414005549034500140000c20025000504d03904c2680e6843c00e000e40310900f00848806403403034101d1266995107e00301071901c100300c003000c01b9041c803840c00c072440072a15190b861058008012480c0840700b83c1d96110100032b05052580244c00394801c0c1008a855404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 426490098 1250 426488848 426488851
    0x1051c02040909021f05071b0e04060e070816050d03200c011b0f02040504060b030a03082401020616031814010525051c1b080105100f0f0207030b 64
    0x700356001804a0b104d2041c40300920000040e41c200030108203c130704005410008458195034003ea441184000300c6072903400604081d0010030844c0242803c000810000f907100b0210068540c040703601499131844169a2422000c1c02d8214041d520030003004181040b44110a01c5482810400d04031000c2640e05441a00c08409481d10b5500182c0b030480d00b0750700024091031024581900c40380d04000c41d21110025486003100a0190b43e454001400f40701703155010032824a4018281c98801c041030400070203044ac2031380c20040885034000700003500030010741c13904030100701038010744000c0d40c03041219428560200c00aa040c15110000786081c444110a800b00c020710074402080035411004480d82100d200400110041c440340c03502060105034410309941e51030203881d0145e510130031460243c80042e0b41941041845040a401c0b003420b403c00c1000d00c0c141d83c030b03641d00c1040b0343e030780c030810020548ac1c08402d0b5404038501c244164181c1d0b11500e90b445230305c101401100c41056681d601d00514280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 426491348 1250 426490098 426490109
    0x9020f120307060e010e0a030f08070e1005090f040c0306211e030309080f180102070b04050607150e070501021c0c02120307120e0310090209280606031a011701030201051c0204 77
    0x41109442742d4064000c0324241e00408145800610901c0c1400401c03030320020707001075006129010980c0425595020344981300704074007610a10901c03404940280180c02c2d5405004400300c1290359140c561601001440380854003c0c9001480b25a02c00c3c0d40b2105c4c0481c41c800b9020940c440002e000814000001042503048244d83c1d59582c645c0c140b0400d40d00180c110045045412805080200d0013240c02a1001e4801c1115040ea483e405440c24003800c0c4086080701880300c1c10211102c03400c45010408000300c031001c0e001e8901002c00504000d080561030410600442ca4250402e40942000b80c1055020000603003100d240c86540d8840c46040e42601c452440040d175400c50401083c02c1c18010140c0f1403145403028820b84403161b0000d00507501c001d0800d100981c0b0002809210848085501c20300a41c0708010000180c8400008000c0c08000b8a5030788281c61003a020801540301e0410804034200144480c9984c1c0d08584c01118141c0c40380e45210304920903100d94414280781840200000d01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 426492598 1250 426491348 426491357
    0x3050f2514010b0901030311010212131101020d050304060f14131416031202010b12010219080118050603120c06040203150405060112030512010909020f120307060e010e0a03 76
    0x4038249031802024020089034801a4103015245040b5222184003505603030380342c100801050000c43c00c250090061040d20f4010148040034441c100500304100344203507000e01424645203031402c0041eaa1520713280703840d5000410800000e00829859889012034042c0754802041070003d000203d00108402e4400940801c3c0f540050401c00c00d5040750440129001805040085030704c100401d9020301c24403010b0300b2458140e00e0394006030b1013940400e050400003451130090301400f9000702e0003500240f912003481c07282c0c5507410030701d140a034490314100d0b0007420800c1a10030052180001070600501240e405101d824181314408210380050310480e0840801403901c0d03e0b0900400d403400d440056002048402d00f014000460b10101d5810306440c00e11924003074022403498104d40e00c0c4034413104600401204000408c45070010341140208500840c0c21074012034800007003169407440340c06c8007002a0710401c1b5803030000d641d60f0822180c031846400001a0254855055810291030070000c40025 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 426493848 1250 426492598 426492667
    0x309083021010e100f0501050d020c010b03121201140d081804050915010b0703080f1e041202010c020c01051804060503010c2304050a120501090c0b040807120f03050f 73
    0x1440c00714560001002d00d002103030324044c40e05002904512409c5100c0040c0b58001a100b40241d1007508060741c00100901102d414000d40c010482583e00400c041026080a40e800018140803440b408907490000400056101c8015525108903511105069100111030655170410365560710450b803003445200041c0c024000d001c2d078441c00c0094141c0060320365250510181004c04e170b00800f074070307804007030507502100340c1c0c0b034a5008030001d100002c4030040c0d24084108000401001c01c080a40201d0681c00038440d00050000584e210f000c00c0e000320740014014041e0206400c0c10125102d40c003030024000140c5035403a080440d095451101d03441005c070301c451001e80c03a180d2640000c4a580f4024105c3d01d81010300b8103001a1000c0d207280318202d0314010003c803000a1100039841501d85907409044900fa090791070b0350340166604a881030300c2d0740c1d000e041000210710003d01c111070102039105142403d955066541034031141c210f40340200030104184640c08506600b540300180456002031200c014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 426495098 1250 426493848 426493861
    0x1e0914061f0f0b040506030720030a1103090d08030a180521041202090414030a09030209010603140a1107120203030105041a0f0f03190309083021010e 66
    0x2070101c40d070301c084800d5142150410542a4250640c0e0944030300f2101c070b555984078414100d40c034245014103211040011603210034881c50000090500141c161100d4203030020038081591a805054aa00e400115000f5448005a0700400650307204000c150006550a02030401007035508403914100c500e503012034041e809004224400300700981b103c601607407905007481000b13002103241e8031001b401840c02501060400440c5051300c0b0448002c81c048a0321100d0b80e10009000660340e06c400c0e402140110004104d8600c01c2c02001603141219640d0340f01c0703441700342b030031030003410840b01e01c0e100104188490000246140282d100001d100d130f0045403a5410581080111070745e0840100101540210b1040030751106010714030004012615415200888400700e41010701351f111490744010382c0b600c10707010140c11050700d8040d5542c100450341040e010a0032418540c41c019040c600005103103000056000420340204546000c40b41c5103200c0740d064461128900c1400c0e00043e000200341410410b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 426496348 1250 426495098 426495151
    0x11b06201e07051203040804031707020109170d180b0406050406020105072604061b02010e0c0315060603070c081b0f0723030304050a090506090a1e091406 68
    0xc1507140700940900d00750b200d503a80342e40c40d40940203203000002c000c8000350610031180183c0d802150071851804880030181c006029503846048200d001c600c2c0690045038003500000c0f611105c4511100405050303220a0099511100340031307c0a90705000c000d40031507100d803d4409007005044a8980980b21803e252000e420f50381c000b42000c04000031031500e40c100c1b060110b150002d803420411100d5541d2524107180003e8000b650007244d6a00254044054442c1d0541c4425250326201c001d4440a901000801d80c659030008420101100c0786d0010400f40e20b0280015034124003181400d03500325201c0e6580d20202d13017040103560b4089041c1c0d1a4030b00201001d01c92202108900b0029040ca036062525025000c146525905d0746040006014146a00c1c02c00844001d0800100321140d800c2e40c40065130050041151600d0180e00a840412120000c0d4003c68143e80c1e0200461402d61041c03950a00003004075280540b00700080d07040b00140500240701c580e0080c0004642e00c0090351000301510b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 426497598 1250 426496348 426496387
    0x40b0c0c0411031b090102100209011211031603090f0605130c0f36020a020c090a0f11031302130b120c09011a030c071716050714011b0620 61
    0x3c1c0580b01040480d070303170f40e034042441501c050011070b0058481c0800d00040320341c4090a06002d0401d4a0600c0b0191361501505c0a140314200180c943c40095691100803400d9170128034000381059020b20700c04001940c15088541e110400d54044000404a600c5d09810344400c4d0f4081d00c11a040428180426546a80060f551003543c44044114521000c20316180544228400c0b407581d0b0f000c10819406c0d403090089a1100500034030307903000c81c200005424001c0a08040c41045d4030302d4000c05000e04a001019603100304000b85c00d00b040c0c0c480396024840c61141d0103416a49140d40c481007180159226101c1e103a030000540010700003580c00c3c0f02400100603045c0c000784030100b0402101d00d00b4960100c2142c0e40b1440c50200b9a444034003d240240888500c2d128032a81c80380c0c081000d8000e13950103200c0203005400ba04c119001c49903540c10903030391401c0141d00c1c240040e0020000c03503c0e0150031100c104a140c818000020b12500114454080034a021004a044d03200003440300d1403001888503d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 426498848 1250 426497598 426497641
    0x5120115030b01050c0312040c05030d05030a0b0a05030d0f1403010303020f0610050f0d05030706020c1f050609040311070b0f0c160b07032a14010f11040b0c0c041103 73
    0x41d403505000f40c022030354078010810340e87d5501001000003010001440d096000816000e02120302c0342840400150442d001145e14820f200e1905200c541c2920388400e0f21805c82d10050080c0801150010081360f03589540c2e0030310300903c00b490900d20050203120b40154000d60081d400381c51300001c2100d000e4148030026280c44d00c1c0c0c0c010401c0038003040d6118991642410412140d90612800e18907112782103016000c1d0152942d0300c041400c1400c034402003181204182d00100080c82d04100080c02d00460b001660001c0e0071103100000030f80000d000c1d04109059120305c0c011690a241d4400c0d8400a940c804a14000000341c0460080c541120401c00d0950f80c1c89200f0300140418180035220105025403c0c000c0c2c1045101007281e80507104850107105003100000140042c1131580c10524000050102003d0196290040f01303c1d51121a110b100308004043c0030707140ca05072400c0069001c0d0341001e481c01ca41405940c81101407a5182d20038101c60701b550740101a01c9281100004001000c03400d0030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 426500098 1250 426498848 426498857
    0x5031f0b0a09090b010e030c060c010e0f0a050601081c0807020102121611030403050d0e0d06050108150906060a05130605090a0f1811010c0609020d140615031b0105120115030b01 78
    0x2149255540410348d0803001340c0a80e10941c039042c4071400176000d8029040e080d079090040201c440701400010070680080340c004d0f000c44030076980c0d0b010510340c1ca070a510400d0800c44056080c61008510900e0341940200640c07001504000611100c003a0211069443d0820b00101c1040fa24807942c0041114a841250401460500d0b1a50b00c500341c5603200d070307003d00301080260300c4030000990320355074204503250700510304110942c0c440924584e100e88840c0613001440c02180011001d44001400034810300005d0030243c0d26a1900007400080e441c01000083c5240c0c5a003800704490305c80101c1d19203d525182e0010544640c000810701c00c680b046146039040070541480c42c0041070740342c484100909002e181015804076a805c0c0b0100a040e400d50080d031000c540e03c507400c1403045c0e07034100000781140c4106940c2103032a00f804c0c1005880403040c03600e825412004a00c3ea40700380d4220900700c080d0703060404902d03000034150340c2140e044007600621440c2d120400158100d641c0340c07080c0c40040e0001c2c02c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 426501348 1250 426500098 426500117
    0x140105040e030924040e0405010204060e0a15120f0f0b12010902010504060c0f02060a020a020f040513020105070c0e0403050a0f080c04150c050102030c210705031f0b0a09090b01 78
    0x108488182428a025041c0385503204c0e108441e00a008844c018450640020700e54180340c900385020350300ca032081400180007500f0100d941c2c81d0100003007003103400c0450700d0400e00b411100c056408905c0354103885200c90340e51030940340141c150700400385428540300c80000e00640050400200304030141d160320150b80740001c20300044c0d07000300440f005d03a0501c3c104410100c004d8a400310580e02e003c07000035000200890f1012100e42c0004000d0380c03003442103c03200f900c0d01640c410306c001c42e8001c680007000b21201084010255010380d004261040c00b510843e64a5512080d41d915005130548089002681c00200f1020552380114107014a01240c50080000d041c00c03280e80c3d50b94000c03401030040c1c5030740c02d010110600307018200d000c01441e8003000030740d10303444c110f6440b00d01c0e9000084014840c41c5082c00760004071000021045c42007130503456a5045440749181c3c040e034032084561080709201201004a45900b0840142400c4400c50761894601407c1040e540180d981c11810641403007400313031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 426502598 1250 426501348 426501367
    0x9020c030a14070c230d0206031f03051204050306010e061e040b1e0a0626090f0307060204140f0114092115010602160e06010e04140105040e03 63
    0x481c1c09056181c9000c040180c60184200381c00d100c3c401d4014009020903400180001c01c80050309003a4003a04a03440164a407901803000010700140000d5022004000241c50920303007042a609855003c00d238903102c1900c03030340c0c0c0c14070304210b9144034104070320702041c2000107240070080c084c05040401310950703142c1400804214074054a2807160f40100c84070346241e4668680d0b500ca40d1190f10000c104509032034400401d89803030f400c140782041c0159042e0b04082840d5019100c980038542c041545220b20102000a00b07100910141c8613042c14042c1080c4100700702d100300040e00b0898020440103980b81e160111080070848005c140501800c10082c0d000710603030700036009050801e100000c5543c4e0b81d42081c00500c0410701d1240c907600600b002d6101c50800032000035140c0c500640c140e40302090387d8039828180d83c0d5200d10030918040c900008801d01c0f02e100c0c0220030780e8001c401810304000080010340041c0523940d00f0b1004034140b6000000402551600d4000c0108451100b0050f600d8882c045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 426503848 1250 426502598 426502603
    0x3180a03020c060a03230a0c0203040303021f020c0a030e091311091506130509100e04110f100c0b0105100203040e13050d050711010503012301021c020705090109020c 73
    0x980c0a80320703d0000c03542501c014000c1d08003900b03d01d508034003801c00214450070090340440076222402d109250807499050203000004907030550360140c00500000c1e1a40044e11500780624103141e00442d020710154a0410003044040c2d5030522a131144103414002405116150380000c104901c0d610b2400d40c90004201c121600c10181f400540e107081c06603803040b030050103c40760074142039000080000d03525076030b004400070b11065440880e407001c542d4991604150303814001e801903000003241c0303402040010b50311301c0ca0201c945070040c22090f030084050b0002125086240240d0020a400b054007004100740d01407428050041102d0326208590340400007541c038011800345200401c5000b002c96240240e07030314a401e120303600c0003c480b03418201c6c44005016400044007101c070014090180e01d03d6601460030b0b40c0c1038404400481c0540785c0c038142d00c2070310040d410510314154000e030000920601c0c0d401b400a41c0140e044e070001c0049074604801d0002d1003605a000c00d0781d85106201d04c5c02109000f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 426505098 1250 426503848 426503863
    0x31e0714030a0906030504110a060f030f02040b040b0c070b1324020c011803050a050313060305060f0d061401090618020f0301050103090512210108010b2d130203180a0302 75
    0x111702c3c001131a5502c51420543d2030b88001d0090b64401400500040d02c0c661010203c18940d02c6a44c00340010303500d601940c0c05034050360140c3e4168102c184018030003404030101800c00c10030410300315148103641d8080383e500350740105046481d1060300c00e070900800d0302c000e0030301024500300f0300c1560f44030450000083d01e071414801030324100550031418041d00c10340a441ca81c0035541190607501c0d4400f0505d070550b5243e005910020310007190041c00100075000344a910300c2400f015145011f800560f20804c9460280000100c404c01d5640c0c02070102003c1700c050f03840c041e01914400088042c10486420442114100c8207d04540104400141c8040703260640c1c0c112682802c0c080340a103081e190050500c890000c00880800c408034040164060141e0b072001180280040030400766240c100c05426030310550fa00e550850b0302c960154403440000324031210f406003402e45030000e002c80c100026030f5051104269503000d03038020082c888a00c59180312240042c14182c000c10b0000e01c59030f006034640c82c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 426506348 1250 426505098 426505109
    0x6042f12070306020414031507140a031803030c0305151507020f030d0503040318260705030106030f12080415050a11030109090309092c031e0714030a09 67
    0xe0265095200c5000c02404024590103201903403669112600040301240c5400d00700d20a100d44003a01140b50b03100a8454051040c1c1e60750340c0d92400d44003c000701d07951b01002c0460201942d441c2a1036881c0303040055810300521079900072901d4505007200500b5207001820b091350580c1c0c0d0101f2600300c2c2d91400e000d9260503540303407001911359031140001400c40c01021603a40e0180601501c1d10f110b164404011031080f4481d80315003441c1048010004400300b0130f40038080e48500058039107080919501094480403500004664600752201c020a0940d4450760003118113a0b612441d1508000321610314048020403450004014601500d0381801201022082d80340603581e0000f00d83d400d001901b00c1d001d240083c180041d52965143e842e540249480300050f0009002810041000c44442c001e403003018803c002e03a8414000d003a0f107521100403201d03204c001e00348001c01805225201c030343c14204500260506594440810b81003200a003046610060215001000703a511101e400000d004140d0301c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 426507598 1250 426506348 426506359
    0xc0e150c0d18091d060f010302150d06150f110c060a1110020301030b0906090f031e0403060504060c110102042411120d14010302031e100e06042f 64
    0x40c032012040c1c00250b081e00703c002c03e94242445143c2010395800e0f0414010000300031100e482d5100e000c8240a4282808001d60041c5070188030040d00182038041c25144a03c524001040c5568040c11710b410448001c104010414100c1062503854001c00c0b19810055980c01070285444070b1030014415100303075100301080c0b1540024081c1c0f501002c0100c11400031448008641d2940c40303080040e140d0034222841c070068800d440008400c071034082140c8841140384170055061691000d641c4a858805801144042c4414880000070410b10301400b80500d0050200081d600303c452001003401408400d402040d038010001008882c9148000034004224141203e2100b085010101e8640d00b124070010301070b10440030340c0600c401c000c034000c160140c1c2c41001007243c004202c401c1d25502009100180d410f4006031003d0f42014001c240d024a033444010558402140c0641080215556443e071000198841e07420007040041a03621030210501c0700c00594104040d13041c03954041d1511040c104d0094 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 426508848 1250 426507598 426507617
    0xc07080105060a090615050a0212070602070c080102120a11360102030301030507140d0812060a05040905070e1b120f0a050408180111010f0203040606170a0602030c0403060c0e150c0d 80
    0x228030a100ac24903024010b48003d076101454200310f0f001c0d4104050a5407000340644c8001443c050502c2220b8210a602c07040c042d0030798520b01204001e00d0043d0300b40000543c00c000c00035110201780150703040000c19032689207a1000d1460a0014144901111410765100304010700c017144000030107100f211040c1d240344200b444100d0204032901c0e09800300410b070740d401040342c040d0b013081450054824201502e00c45d43c5950342d42d007000245e860600340030301103400c000000c1c420900c500c0d14240d881543d00405825280440d82c0005595012005c9412004510b00a124036000e11800c155000640f000050001d4101a2200c0960340706e0074041c1009600040f4900100364003524038017002040c000000c10840c3c81c101c544c1c0010b580112402c8860500d44040458103414a00c040d50b02e0040040041070001c2135955140d009501c00740c50303a061454280000400a8058001d5460342d0748284d40c0c1d20304070b07001881071020101070f5403d6650340800070301500360070910000301c00074400160318010303410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 426510098 1250 426508848 426508867
    0x120c12040528030f06020307020615060a080405030f040305100509150106032408160b070507270203040c03060e070303140913020f190f09090209060c07080105060a09061505 76
    0xc101e41c4002c1c130141080c4404020b1202c568061445040c00750213862055846066442d000c4110359031140d48908244070941c02684a07416035640144588112868030030700c10b0440017103400c20f0f401160356034840c6c410384130032a0b404d00a150700700c2c1c1280d00401c2242e0861407082012841405814200340c0d54000740501112401c0003841419400052000120303111130700180c640014880c904000300940c600014544110b204444040350401d002e840041c1c117012142607090b00c800c420040c1041c5804406480c0000752004601507486001d001249500d10724052040d00e1806414040319080301c0010004030342c0050003030528a002855050f5100d841c800000c40b01700482c417079405420302c0401c0c903050910a2100800c211424001030249503c101e5034120ba0034550009a03900140300e4a104102050254018021022000b0202c0e41061050350740d1600d042c41a0340304000030782d1100706204c1e080c00d20b500c01c400a010124028060769007071524280c4803031550511502000700000c2e007901d8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 426511348 1250 426510098 426510169
    0x28140607060903020618150f070903080c061014090a230f0103030905060c122109060703050c04081510240f050a0806040c11120c120405 60
    0x300e103544888100048046400d00a50b1404121103003860141d004414100c294800926101c07022004555103106550b01c0503001c0d141d61000d0308202c20f11000910100005100c0c1d00904040b07034094008203024580008080c00c08485684130790142d00380d4210481c1d054503006502a40141107040c0841c488401a17181e03621040e10030400c03003908001c04203001d01917001030b601e130341224081d655003c6919214010841d141c81703103000c0052280e102904010b40881524041c04540b0441064090009460003031010795180071100d150301074000c00c04200350141c140c4903040c4c103c1c030241a118149420000060b40e00c07103002c403020502c0d0301c1c01c0c0002020100d000703203254068044800e013018079503003021407546180301940004002c940c3c100c400f2401140302d001943c000c81380d251303101c44143e20740a040c0801400600c1c401801c0202c00030300003c440a040101041400801a2490b60748010105c0181000d01c154aa84000d440401040003145d4400d03212071811b103140c440203151400344405658 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 426512598 1250 426511348 426511357
    0x806010518090624070c0b091c0f08040b0904150f030b15031203070e010216050906030a12020d030b040e03070b0901060905070309050606010f05160c050a0b09281406 73
    0x541c900b02c4e80c140008508110081d008003485480500601e94444a00c0d1500307004501c1b2803600883c0e000d141004450801d4041d108650140e42c81710307290300c042e480740d048552042e00018031440c0001100847d5007420303c6034105407004030306544145c03428001e040c8100c3c400c0b480058402884000480c4e9543d0031007030304491000c0014210703203503028a5440060315030000c90742c500100c2d400c00131520301c0754000300301002d09401c034120300e8013840e08007800c004022001912140d014440c1c2114100000e07614030156000308a0342d002801d100d00b02c00b000406a44002545138015410314550b004480030010556080f2603000c40d21141949d21058482d0041015500c001141820503013403000054165026aa90f58010002e4909030760f9290010b580344250064144002402040f100100020380d91104007020701c600c0c15a405c559403200040c43c00382035604503c03070360340c030008140c1031a240107444c9100c41050701c90030b4903840b000c5021411002d061032240914900280066641c0b5644800464 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 426513848 1250 426512598 426512629
    0x1b061b0b0718080f0a05060a0501080304030f061b08090d0201021305091b070f15051b03150909100c0f02060a090201030b0409140d02030702130903090f0b03040308060105180906 78
    0x80b001078001944c0c0c00d43c0d590414405840a0080364046030308030303d0600501d4141ca40307203002507140926507611403001c44402c0600b5503009907958595038100c2000e44582c002d04259607038589050401d40b030a02d04080f6030100c040e06580c410803848100680f24200442200c4045921080030341d00c0784040d070690012903402000500000419a0400c072030300e01e484038414021407014064110355100c1e841140c1c41901d40100207a201a03d60804111000c02141d00c0a0745001d03010f2040780000c0811342d10002555120181d0300000d0404c0300c02e2045106400500346035281541c49200f0202c000380d22008040d062409160320f88001350f003564080d401c9419411000741080242100d94100f202c103610840d401e15030740f40940d8840c3e00f031051002095618580c1c006100a1a00b084213941c100200708684c400c82c01c1c8040a400001c03030141d00e0a840c4000c04421380b003160b44e80b81921300108100801805641481018000710010300724509600003040303015034a0102c47e07250100052507035010710100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 426515098 1250 426513848 426513853
    0x4020d1a0c130506090306040210140403060b030d1803111807030b010e06091320030108030d0e1212090c03010c02070f08012a0504031b061b0b071808 66
    0x1070000c541c0190005009045007800e08404040d140d03002c2081300c3c401d44000550541c808000714004d460414400c100d9414076060030100c04180422429180c0c20590003a174525075500440d07211418144044d4645044601c2c10ba0301941030340c20341d0100d50369607002c080c050201c03800008100380c6070b550750b42040c800c42d10f004144500c0c242030020042c05c000000180025070389501036005060160964081400041c0000114202000d0440080080500007280c00d81302180c101d50950304013000f54003070b00b0000061a580d030040c82c450010f50b0b00e05082144ca0f0761056411a034100d1101d000e0302d0b83c060504950142c56220070080034545051940e059078554a401e075886045a00080d40a04440d928a4801c101c3c42e0b98900042c00c84604002c02003c120710103219070101240c1c0034003031400f04080d003421350a09840b81c07294580740000200d00101d00c051141c040c0031542e04855001141c0e4001483c0d8259844269100e002c00440031f8080004d001212811030708052442d652007000c0c2440104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 426516348 1250 426515098 426515101
    0x191205010f050f010206040c060c050307020a030b0727121b1e06020118030c050313060905090609091e01180c030605180a08130918020f041404020d1a 66
    0x903052007201d80c860b0900c21072004400040d11350022504034441c50300003c4030721489142200075104440e80450032900ea00042001d02c2c01030782d46450a00c0034501883d481c04451500e20405452202401c1103d000d01e03042083c481d0f280a010345885080d649107441000d8100076501c1c04141000c818025441c11280701080452009800d40318021841d508919081400f96036103001d03401ca6050202c0ca41c030040079541c955000c40d0091f2046180244128102ea181c10f10700d0842ca45516025005500041e59403041000a031425502d2180c21060494441c101810040006a614008800c0000307a2840706e640d0541c1541081d4400c0407002d0030400d00290340e0324035180c2001c03c240703c1e020484000b40b1740004200308601c003980d192409007400c0002d0405107200d480b0301c000398001c00e1030304141981141010880c0000d40c011a25510800c041041002c4004d10412134081400f030170050040c0d01c7c021014050500c1c1034116608a9015120742e4070340180e9041130400e030007503481c080d405500c0680 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 426517598 1250 426516348 426516359
    0x5030d0b1c0f03031b0804230f0609010f0e060f0c161b1409071d0d081206100c080c0c03030310080c030d08071b060f09020406170319120501 62
    0x2148805418071130342e41005603c58030308444e40c0c200100d4410300009a003090000f030006581c04091031142d06801c3c401406802c080031680c1c50081c149160f90621b800038401d005509009014122500d00300103810302044612014036642c1d00d000422401140c8402c03030104103000c1581c41101c10040200d80c40080002d1941404201d1720f50400c50b03061040310014000441071842800a1040e20000300500107540741d0759012035040603444402071074070b00c40345070761a03c1d40c0d03500e85440c2071103106090060700d6030302071b4422361011040200342d50700420581a1401d41150300090004090f54485880ea0716400403190003072420802c805280d8143c8000014000b6404c200390f40031040300d420004031150042d07490241078a402844481e00e01091107500400c4085000350300c00201800c10440785040c2c6041500e40c5015600d8082c01044241da540c0059003c2d4180b900404016004480d0f40304640c00300c0b0202560340c1e10030460949083c02c014988542028170954010900354402e400c14422540c460 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 426518848 1250 426517598 426517613
    0x52e1e050c1305031203010b0d0f050414010c0905010f110a050a032102040302031b030109021003050a0c0e150310120b0a0b040b011709030c150601110a05030d0b1c 72
    0x30401009800c0c102d400103110301c0d00003410001d8020a00c03140c0d040d0b0341b13054035089240d000b444c000381c112a100c1b80f61082c0c82c200c51040501c164040c01884000c441c40800079800c59a41482c180e0820860080910007a608080e0881a1080f40d10700802960030128016003083e107075030001080d40c0034550100b020305d580b00910149c03036041c0c6003054041c050340f208650101c0c4514840290940c00030202c0d20306142150392028200307a00600080340c1c4420aa0018440d11440040900860743d208140030250704140f1511190008608000011080c000001520000000c3c0225050b40f0008000344000b00a0402103004106400b20000c1100b460310b46445402d9040b14a00700492816000c0c003002d1403e8003e040041c0e806848903c9901c00900d0034100000000308210210721081051038007602003000f080c0c1d04054a0b0b440740740141050350004000c00052225201e16a015407024808a40048111340400000010000704007400138003003540d02c00724900c15011121944020018400354 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 426520098 1250 426518848 426518857
    0xf060a0f06050307031106130504050f0f0709030201021e0c060403050102120c041d0a06051305011a04031502090319050d180f0e0901020702060c0a052e1e050c 70
    0x14400c052100a4440050590b207240d1840082c00025004688850605052009043c000840c81406c1e860380d8807100468252401507801c0300c52020326904100403141494450364000540d46405081c95146400007503480c510f80201e10b0041c00080c040050442d020000b05680200c080c01d42d5072240c0e641d0a11741d0007134200a040c8c104150900c00024126108a411101030300d07804c40300c544040000407100001184010b011004256580c4804201c0b651200c401e00340c0e8805c0044081000d40c1464212003072850361803143d03412110140800d100280850724002e104034104400161213503000c03000a40340c00c1c00c0120301c180c1d120409051000b407103008114803e41c0d031101d440b10701c03105909001d000014001b40c407a0b071008440d20342040c403110b0100c513027007074128000c2d00c00941440e4540d0006182544019001030035507000751340c0c0c0c90821130140b012203400c50000b0507000840c0e4800b03182e120078005404c81c4540352640c0b40b421401c03d40f14a00d2144184044100401540c9040f072341818a85c1e01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 426521348 1250 426520098 426520121
    0x20312070318030c05010906151404020a080c0a020a1509031710050f030106090e1609360c03261312020607150f0b06030f04080c0f060a 60
    0x14010002060640030303016a003402000002426103a202d01d40b41240c0303012020b03800710b940e55203032510300c004550940215540160a541c446040c945040e8030b004460b035103100342d60300850041c85004c184a80002e000350b881000e4124080c2d90300d4001e00c0807410141440c10090181040407600343e031010680d0b003c0e8110910989070b0402c810482e6003280e0b00c1c40c2003101c1d90640b0b010808010700c02804c0c0040d00105511b000f800100b00c1c1601c4040c0942a44c8c803188501c40546c0c402d05440ca0050740700c1c1e20f60001814444400c00c1030107d10790f800000403110140e120056410000040382e140742c400d07080889140c01404d0004203940320318060854440002041c0c5064051100354400b41101004030f415118000100c98815881e14800c1c0d01185001d0900baa03005105100145c0411070b0301c2a0810880c0d454440050407404035110700c41102e100c3e000141c055503051040020620500c41c4068001d0340000106072901d210f982300c58a802d0f190311094000380180418043c0304001600401060003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 426522598 1250 426521348 426521377
    0xa030f110a09090b010510030608060108030a020601060801030c05040c1b1a010b1303060c030b03030703030b09070302120708040516060305040b012909150a050a090e0903040608180106060203 84
    0x81c1e0b02d0340424103035a00000d000e46004900d81c0104540e140c1801d600283d80d10fa42408160203649001c00340c01c000302644804119040015100031880d810f0260300d01410b242d040c003400550543d110103d50110340c3c0035440c0100c0e0748542c40c0600a0282d41c050f039003014840d5040b241c003412860043d59919042c981c07515903050900000c900304042005565a00c140800b241c00300b9499178691501400001441a05159440d00c0100b2151400d00003001414000c0c1c4021481c0c1c2003074014000f20400050281c0c2c101881803198001c15044d11501940000d0341d40340912803919141001d9003084613000d0042203030034024000080c016007641100744101c0c01140c090559a90321b21504a40003a02414000c0c0c14980404403080e0141020142c504017801030039429540c40c0034408912990f0280301e403c008101c011905030030700c660080414000d00303682c01103c4910700308049210781e03900680c0100700911545000044041000b100c884283c44e48450007484a55a40d00020792a54848810301b450341 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 426523848 1250 426522598 426522619
    0x100c060e061506070c050616050c0d0c03110f0a230613030b191d0c041e0209040219080106020f0601030f02060a11010c030204050118080a020f0a030f11 67
    0x103a501061030341c0710301500061020705044400c100003880c1d003c0744046410484424003c620391300c41d24080d115007040f003203032a000e030741c01e5081103868070079000402c9218800034258a00011000c1903d0f5003141e51041440d562200c1150003d0440c1d61003201142e00006072401c0040c0451a1420142440031528030140080000609211003449100c1400005403102c0308100700080712441c18503840000d54600700d600d050308461110980300c2c004200350305a00741d1a024004a0b60500040f0200781c001c440400c440d8003241c492032207074800314a030703440340035404134444580d61150707011940d407503e01c0d051000311810410f1020300b58690a002d000014030802d0b10b035609034000014550306a9801801403410710b030407503003000f6203039002081c1203080045084c01f00760501408d004c3e0342c86413040b0751405610349040400040008000341110303550054050001c1002c0e85001c01d2021895070140c4005c5440111507011072880400c642c0028003510fa400303244d00c01e00c00841e00c140039006080301c200344107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 426525098 1250 426523848 426523871
    0x1e020a0e010507080405090403020709050426070b1602030c01020408060411060f041809120201141b270d060212010e010e0601080901151212050c10020c0c100c06 71
    0x443c06100d00052051600300420f100615240c0d62041e4458072030310499015a46414100c07059500030f9030300322002c08031004100c58134551004191901201020880d080182607100d400300310707802805a80200000200d9940c100d0310900072280ca80807090001d5580329074504506d40c2d100c400702c505440713407210188441114a0614101c984441c5a080b80c24182420328035190701e85090442c6400d00e031680c59445500084c0c0c818141c0781440100d80000840d030041b030035061103400c0300410001680e164049603410180d03c6000b96107100718600c010b070780c00019070003a011b4054421040c0a901988441c216400c100141e001425814003211041c5c0e00390343d990400c040300302020b01581103900c442d00002001035110740320960344400400008a03410064040206807a0026001010882d00390705c00003045c001c440c041354071105c0e10f6140180c54802c02700e0720b140d182c02c03c00c0a40580c0c2a0006031036014180200445444000028004001c800085001412100510b03504031201420705a41890 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 426526348 1250 426525098 426525107
    0x1809061e0e10050934030b0906161205090102160b06150c0d2312150301090201050f03060d12020c1c05071208120109062d06050714010903111b060712031e020a0e01 72
    0x4000682c5c0c9a80704bd00001c1da5456000c0c00000f081610250b5080c026100390101d00a100b900c4030380139210710119424281e041c442403802c4560034038080442081084558a40003030b00c2c2a01001c5032501c0d00708516441e108402a21f501d040c50030203e500840c00540280d00451894003841083c40e0b0072042502d48018982654244640680402c00500c07000c10041c0d60b02c0e00450340320a005109a1407540d0513612401248241c01020340140d0106051a2240c10000a2003910750803101c0c080706040415540d10b0360b24a0240200da4640f00c0c1000000100444501601d4040d002c0d2203007541e841da15456500001d00c620701c0761410b034418060455004c1c0b440b5060801c840b901141044003a1801e100c010389090340855011074404803140b0300d0301e01948003031060241080c407079941c680342e00102c183c046190003000c8110301180c240c0280c0c070443c2c0b5501c0c001255070240c3c0c4403c03040c0a90405207070a8004001d00d54030f06a41c079039010401e10f4074561076401091800159114400c022203600011503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 426527598 1250 426526348 426526381
    0xc0807080c03160e1210110c03040b0a1812170703020c0906010e0607050106240804030c0201030902031c12061809061e0e10050934030b0906 62
    0x5150800410102d5841d110041c0c903400d00c2915401c0004c1954401004211058540c0c010310b01190846100d0591190150103040d60829042d4401418255441881d0341c40303101b00d1259a4181c0070000d4a0030300e55000b8903c0410f404240c00880d02d50581d40c2045804101240604907a4400784248030707100c070b04a03601a54801509640100060013102c020b102d401e40000d40054140026024040029920764001b848003510400010a00501d0301c0071001d032404030300d5100c011310040c800d141c5605660014600c1c0d0f002d07400d80f034403903580e48180c00142e00a140c110000794041c007071010446894401ca51084404040350344c0c8d000e0386042c603010490200d812070701588030100580040d45030740301c2c09504101440e80c0100c000242603800c10801843d00020303034000401041d2201c40400051200340000340d161917200e88140100c2c5800c0b0b1140d0b40b142c0e88606094050074450703503034050b9000502c20b9403068088001040042c1a01c0b41852254031804892f5244c840c071520001854076070411a440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 426528848 1250 426527598 426527611
    0x717190803060307211713030602090a05040c1704150c0c050d0318141608070306140105090604200a18240f03020c2b02060103150f09060e010c080708 66
    0x10310a003201c80d501d400040f00302c034491100b10a001d1107c2d0a00c0c407074a01052004600c110001692182d483c1e0a21801c22003940c80a8455490b06200c2d50009800601054020346100011317040b41c0c1d00d51504820780c11850380c1543d25507150940108503a03400094030035949003d5011243c00d00e07040c04045003130340c81e06583da280700094007012400140035501c104040300313490300035250003010142d00186078103501d03072001c002d41c2c1c04011304005101003449588079070702800f04101110b41c108008120903c1028103032901488e0b480300182800c1810b00f4128a100900300f03c010b0751204203440c010403000d04030f400c001d00c2da079255500040201661130341d0a0a003401075400160040d102c0c0c02580d804480070502014146c0811106a0340302d07052008020b500d007003503442001140140041c0e125920200311030170555000f0310040c0080360600f809480302c28039012010901600854240001d0000d0250042010b130401c0d100c03801c481819000001d0220081d611010346989104040355128800e8929 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 426530098 1250 426528848 426528899
    0x120f090c04090203191a07080907060c0f0c06020102130b1305010521091c030c0804110604050402030c030906070512130609080309010606020607030e0717190803060307 74
    0x10101801c203604111240750004095410320004d103611114038480c10501200c90014002d031042502e8070030551242c0101c0103140422240c5482101d0035a120514015081442117030405602081105003490181755408070b1900d4010f0394402010303020350003040d00004900c003d6400418041d0418040c1d40c081c1c0169445500c080d40b412006441c958000120345d8000c500382071501402c980c0c40301605000d0741060005001814111300c0b51000014005501c10415003415003d019065010f6100ba40068002006841c22084480000d0385441079600c072540290002c02000303414401c01e005503100b1000401074500302c2d40e07031440c100c6203442010540d11100b00400045108502e0702c05840c0800343c0f15030000035000d01345489491b40c64200b261402c0850f9141e68003400115814442d0340e4011605007404c1c03241c010125140c3d40c0b514550b01428804801001003d50040390400010006480940c07000c1c1d08092a13080c0340410b5801111254001d101e0750b600010743c03036a100d0301c01034540504c405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 426531348 1250 426530098 426530113
    0x100201140a11121008060907150e010c140f10050103050106050303070f06110706051906050405010b0d020d06050405090307120c1703070201240305060603060709030b07030e070605120f09 82
    0x200090883e8090f10958460110201c04110150100f00907030060980a00410a42d0710380144124505da2546a10007080851790040c4803a9800180009010354032143e4500b03040392034041107140032a80b43d108200e134840c0e4803401500312255800076060b00d002d41c000748a50390300d030402d0590724800d52000904c54500c039114407000c14415444403100c00f0605003180d103010a2a10b0340d005954055580b030428107085401c146603599184903000084c881900d050045624085040031107010f074a00300c10343d507500014106604070540e4444405000001e10421560521408107992904602000c5520310000280c04180380c1c080d0721902c0403907a000c0e00c1c2c0d85078500b03858203032011a0400744c40e88040d0342d280d00300c040384100020381441156041c03040c0c04401030b285080041c900280a86050b000c0c0d0004020711481e940e00108010075a600304051521640700c86108a00500508404140c24002c040740416540d50110003450024500f1003944401e0f221031141d1156400203458002c0c085c1e10114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 426532598 1250 426531348 426531367
    0x30403140c0f0607051803070609090c0c0b0906010303090602010203090d05162f0103050c160203070308030f0703060e092e05010e040b0106020d0804031805100201140a11 75
    0x10020111a00764400761109500498040792030000256603810200300d0101c1c40c010020403a45d102c450b049800ca0007009903619199014214175000e005e8842030544422510107101d000380f1100211580c048046105480c0503020140c60340800c5c00110000307988407000240d01e920500949005240c0c11303010f04070980381c640c02a202c640c0001000f01c0d14451804070180030400c00621b981082091104d0000403507003411903240311841000150381854a0300052051580001c4196a000f5049071030b0300c001c01d4080d000207850034000d5400104039a4001041000c00004101101c0c06400c1ea078805000682d180c421082e400c0740100c0321445594401c00601154000316100c41c0c2c003070b0034440800166400c2e040d40310301c10741d54240c003c08655007141c0244801c01442c02c103480c0c0107007010b00c0130b00084c0300b070b1040c001c20cd003001a1004d4100500314040e10380c001d120380541c0c8014603004010503294030807424041e0290582401c00100403913500000351110710700c0e005640400341e05401242c9805504c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 426533848 1250 426532598 426532637
    0x3100b0306012706090f063e0c1f05091905120c09090304030213050717090c010206090c21070f0b2203080304060216051c080c030403 59
    0x3819107040088405210303042e003031950311401c01a000b40316043e1140b41400d001800b2644a6448841150b003220000c0000c2640045590a06402902d443c020714550007041078012480d50180d01c514030030100a40b854003000215041041c109817482050640c1e0a00e211000f45582ca03c054045102040014914549807040c031703152070b00b0507520700f50701d6488201164810718440c051700c050344c0c441003082da414035110b4203140d404213002c030013917140a0135503000c64103041454a005c48070f1500d40c4081944180502035640c0c10580074449009107260001c007041d5514420b05005015000341000302da49804082400110200d0142c06212200505424400c0e410705808152100b8059004003084410b10b201c3c10400070040035103426122040401e90207000c50b42c001c20070300b8110000c001000003850030f40c15a64000c1d04280300507150f03a0802e07805008031840d400020414080c404000d91182301081d5022409156039983d4009c660b42c690280c174484c031003a100071340865000203c40303102210701e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 426535098 1250 426533848 426533851
    0xa210c0914010903060c02150c0c0a021201090f150b030631020d0c0f2102090601021014010609090b03030409050919030e010e011e08060105070812070206090303100b03 74
    0x103240c800b40d82a9a502c170842122110f80c0300c1030040e00880100090b00d000049802d8010380c010714900e02e0000c0c2090b0b02580e030159100003d00070b50380c5040900e0340c10820b506c0030780c425401c40c000001c203600500e07281c1e0520940f0301d08403500c3ca00d4900b0480b02400e001440604c01c800001c2d480311004001c403000c81c0c20002d10320010310601c45400d804001610f902814580c450300c610900707940e0038200700c078240802c00c444d04026004280c07040000074926501a4814403150180d44000c40307605d950004034204002360326244407450034020050039540400300c005040360420f0b0341d01c0880c182c5408514040e20f103840015540b6500c24401400b40c0d0086900ca1a08044c0407411030307090100940c203030000e03100784140680200380900c4101203256000070030049000400d107441d5010280b00d407420b08815410101c10410840c80c2da00141d4503900820464945e01c0e000030390561200202144240c1c1d540080320136500500840b80402c062100000581c0e006002109101501c5401e01d460240c05400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 426536348 1250 426535098 426535139
    0xc1203090c091a0a03120306060c030c020112110c0c03010c05040b03060f2b111807180b071419120f020a020603090a110a0b04050f0d05030a210c09 65
    0x141005925542d90011300a0046100d150000305003070340450f025040743d81d5a1300480511404d00400340009511076050641d190382400c0c11101d0300047d6100708001c246140500d45040c0000488400d2090001b03025800e41c08214020b1000c4000144116802e005070310440080100600100d20f451501401e00c03411450b0150120500f4400241c84400d00101c1500c4410001483d10842d028071283d010554a41c11054804950129540442e0900190000c200c0c1082010b0103542f850041c4400003a1801052032108a5842e42000d040502310b40032007594080c502e02c510700c8000915000386091403a060b80102d0524150710402c00c1c241c507400121030141e0b0440c05400c1d0b8200040e039401002c0c0d0300502d043c0009221101d103a181210242d14502001845130000781c40800c20140300b00121026a201900c078454100358810125221101c4820020b08a000116185c2c4045510440500021407618840040d0f1803c4c6401c6030b0844099800040c0001d59000b001d2081190030310000c5081c15 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 426537598 1250 426536348 426536381
    0x5130501110415230403150b031f020a0905060409020d0e0105041a0c120c03010303020d0c020321070c090e0d05160221010929090a29070c1203090c09 66
    0x3580c1080c889045c2c2c025007007141c920b2100718004002040c2846441c1020805400800389044c084980d00018803003480c14041c41c43d0000341c10308105102d0f06241c001050064045600c50703032100c0580c0d011350010460450030914190072444111030500989000f02c0e0000d0030242101f5078495844140000142074100071801005400301c070f196992240e511810390348101640b41d5046181c000d082681807001c1d001007082c0300050f40d000da60041564641000070079003002c01d83c0c601c64000c0390b46006000700641350503901680041c5009040c0c00482109400b10192602002050810f075503134080c00011000c5401502c40381c0340103060069411010a913400201c00d503404000e40b4180c20f450071803d04560000c480d02011000d9140c01c0895104040000304410b203d1a02000d029520110f0110140520380d00d0b60b0714061007440c030002410032800300884500d05141505020300001041d03201140c12924081c50300081d01d00ca4410310000550203000344c03426601d09440e00020b8a10010142c1d07051 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 426538848 1250 426537598 426537647
    0xf0b0d21140f0406090e0618060103090203010e0106080607050c030708030c040b160203010b01110307060902041b0e010207230f03010f020403060b09150d06110d05130501110415 78
    0x7008001501a4842a4a440da540c030706003103004000042c598010095482e114041c05059074950590346185042c003010748066030303220b6004070044c00391350b64007a40552900300c090b004000190041d8094407010012200d064480e00d00840f0ba03071084103c00609900107015600020300e0b060000d5410403090003200d412700e521294608165401240540c010000c00c11404c1d046003000c0c021000080070900f03010301c2210745040415203038410100020540303561568042c046688036030209409036660500d20310b400402c820080d1050000d050050301510035500b0018910701010001d07885410380c00100005412502d0a12032080c03480c1c850350368555261034000e03000c0c074081e101500055026040101d040010301c0e003840301c038000150030f0b01800c1e41400d201c800f1503103490b0083e040066019500040c04085821b00418502031601c2c1d03100b50750f040c141171001c50b003080a207956605008800030400f498085490700c6840c421031044207010494031a090800d60f02801485c490a00c00c1030840001c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 426540098 1250 426538848 426538877
    0x3031d1207060504210c05060a0513030509030a06060f09050f1311010903020622080114010b0304060b041a040e010501141c23150105090f0402030a060501090f0b0d21 73
    0x19004170148580000722250000d109105080021325041030840c00f00300901c1c14810010414405120805400e001d000100c1d0015a1010803032a0551500300c6010000c468070313102c9a0310078050301e2150040590900000c520500e461001e660301540f0f842b0b81540c0110702c0d0b41ea5074900915410303842418450300320000805070301c40c20000c00981c00c610204001e090700b10b20060b6030034a5a80c01c4140260324060503031110500318050700741981c04500d1070503240d0783c6a10b08072028100c5429100d41060400039503a04034a840d8402020070700007103e0501c021883c0300619400c9940901c14900c0ea18554803805d120350511011a0300d1448080c0c005040e08010f80c3c07105400000c03000b106000c4c0c0d5000106980c1081c40521400b0f40c0c944250201c00700030b5245c580001e098000c0900012050319220000c542155800c00c003682e01c05a100f601801150b0b0f42e20454401440c0b914102034140e4200312101c3c54501e8444c2c02070302c5103540504801d100000c07400e8031100c5003610b4031401041c040d480962001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 426541348 1250 426540098 426540143
    0x51e071e180807031a1801360209070809030d060312300b0f030f060103110303090d140312041101120b090412050d0903031d1207060504 60
    0x1200002601c50500d1020340d140c1d9050211016070140256820480e414000030ba460f1050602a2a1101d884811602d0700f0700c00c00d040c010340440202c495860f00c4484000b045010502d0161b01003580003008518645982a01442000a8000f98400d40d203034001005680a480307010b03081901c040c00c0340d080021044c0040119400c0790415240d04203030140031211181d004601c140302d031482081142041e5485180c0598030009114175400083d222051018903480d80910340c1132001c0014101c9000b050b14003016521100b00f07000984000c18401518451401e00208682c0300b08005410780b18002069254021007906844c10918540000c0000c0c1c1511641c90f000c003401640698010401425003100140403000c18a0550501d03d0500600b800d013595081174681c0e01a4202c490340c80560100d40c000c4541d4401c141030104403500d003540c1c034010305038550f1224103050100c0340307448001d0769012500350707440c07019070400d450760307a01080f464000640a4001c560410721506d881c0e5510b884000c1d1880 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 426542598 1250 426541348 426541397
    0xa120f0e07030b160c030c170a120e070605071506052205060a0e0c090103110301150914090117030705060403030e0c0904050601060f02071a120a051e07 67
    0x290541d12040c428818040050b15103508600c2c3c0300b500148030741209002811107070b0308040140034407180b000c045080c46014044c10304440040304025540b6940408050840405400c6c1c860752079140103005540d50f080000c40c1e00a6072103d4480e41e0401c841640d484030242040d90304204060f807124000651030711555140b2411006403100d12615032160660701d003c0300d1005080500c640100081005803001d00c441c02500015040f03081542c507050f000042c3d01405440400e00c20360f00c00040005071403d00042c0a400c15412699601142556841080e0000f030500c030807160702005002c0104854540000b440b40c00300b404500b40ca09020312fa80b40c540c1000d108403419001300341c64403003001c3c8110007480400c120180440c0c4100c01da0400d030307c405644450502030304081c8642c002401c10f400d4000c04c0b00c800205030300000d170040c0212801c0b61200503007102801d007072401b03810004140400e5481c020715204400071f03801c400e0980300d1840001166400a0007810610001d810304010460701c110901 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 426543848 1250 426542598 426542621
    0xf0a02070b0a090509070c080a0503060402120f061009080c06130e0408030109141510111c020f0607020a12031e06080708030408060a0c03060509100602100606050a120f 74
    0x303c5002d203804180105134a000341031104010301c00c0103003000105040b0030303034454800c00c0c94050303120b594003008070f07000b0f01c0b40306d003914190f503103c60402c84079180028140d0b100d40015105006080740c508015036040c1c40c94001e141d481d400c0b090706503a00d07050842c050003804c00c141580450315a92240d2400b40d003142900e0580d00f0250000051000c80c0300c0c0c2c000d02c00c035048202403000b0f943c80e0034907903e40c0c0c4412141c82c20b0300c0b0b000084c82900362680f060040c40d00c005058020703181c0c007007860050305d20384411641c0740b0307005409050800d0940a00100c2c4851142a40e0b401816841605540c3d1101024a0100c18014942c0e5602e00017200c481d400960009111000400942c4605220340240741c600c0715400412694000c000500c449100428582d4105400c0c0c035010843e0462007070190040c000d80d03040142c000801c00304010103002c902c003c4030101c88a513026910741d616000682802c0e51030314081c800c041901006505040c5109003640010411650000074201c0300710101c0e402942d00c50601c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 426545098 1250 426543848 426543857
    0x1e150317030a1107021e1314041106030f130602120a0506120304050a0e0606040b07050d030b040606080105011d03010c02070515040501092c070306090506010c080f0a02070b0a 77
    0x30000003142c40d22581c06490031460a01c0e040c070035598002403141c0c200c1c0c1c0c1802c4441440029101d00c94855001201401e0040c20081c01500303549850140010411141652501c1741d03506141c038181803020849010325644818160182d940c9051000d44a011510880b0115400c018909506c070070400e1447c010a8100004181410007508020342a0311881d09500990001c0104010603030740c46042400b114a00160000f0a80d100c4002072030901540c0c2c0543c100303850003e001001c20501160300c0360001000d403000c02146a0090a100854038680500c001142a540c018410340d8001c011140506038510300503400c0e4a0404081790964600900d032070056071100c4400d01c42031074080d0034481c903d621132441038149031811000800115592183d00b120400d41e070b0a00c85488000844449034103200d180c0c079180d6040002004006081c18440c0380691880c3c14080340c015882480300e4900301d50040242c1e4140b0320030058181865000c0308040081d0701c00d1004c002510400c500240000c080d441e01c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 426546348 1250 426545098 426545101
    0xd06030f111e150c1002130f0501020c12010902030114090706020f060109090203031608090906090405060c0a1709010f1b021209010c0b090a02040c031e15031703 71
    0x18010281d18038a09100e1044040502124025a10350315000400408951448036003440b91070b4118248107101582e00c090041207610002d1040a400410810301d9500712040c01c0d650f0b03070b01c0e807200d240b115001d154010380015800e400a480d1103076014011122120001400b826035500003421121090f100030f0f46290450100441d9100902511004021900203041c00074090503a84c0e445050500a00c2e04251b6a031100c1c0e81551010419076102100c4260172083c25001800c10641c2504a40c039814441d504603400640740d401c0c181650380c040c42c1e220006141507112100b4501d82500507a644604125a10300410035001e5070103400f0380540c00c000c1c0000382c0075074964645004e80d01c5450090311f0040c6800321800745a40e000800072a002c8140405688078451100100e0761100d041c000171700400e000b00284064072078041840c2c13041c01c1c0300302e4007003140d200c0101040d010f41d80350150900700000e240b03105030790002098004042950444000c0700140e0f80b01c1ea202040a0080b24403405045c04c00f10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 426547598 1250 426546348 426546353
    0x1090812031015020c1003021201030b1f090614040e150901020d021206040b01030905030a0302030a0f020403140d020712020f120a0819090e0a2016051005040b060105030405030d06030f 81
    0x1000b2000c221b1520702036141c0ba109140b003010040061200074443c001041c0007070042c0000390540c25010a140700e21440440d90b9807003000240482d0300412003258102c1008080b03501d080e00c16840ca0403071481c00b8058110803200440c09050004004c14919502003003011082e01803031005000c244400401104c4c24103000c403e0000300c45d034018109041c90301e00184000483c000206444801c8014507026989070745c1d0b4420303213000c0c1c209030580805903400403074017100b00009000100040b0308044119041048280c4040740d8401d8a4424101d00030441d1403194050308243d00c40ba0b20046c1c0180c01010203280884101d0300e080404171054a032584c0c0841c0100004121403124048a03520307103415034003141800340449407400301504850400e0798603218a890030038101e0714110054070040e1016191041c01e400394030007840010303003110300e80180c85039100060714a11429005a400c8901c0e002c8036507034503005440070381c405002a03505200c103000b641c0356240c1a02031007000c0c61040b601540c04101d0751 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 426548848 1250 426547598 426547609
    0x60f180f021806030406020720012705130b0d0602040f0b070302280c08030a03200a030504051e1005010b0304050d032f04050f01090812031015020c 65
    0x140808503004000402c5504440d09800e0a02c031811550950341381c6862402400034415008010b140f03079105658103028130042c000440303514800f030700d03500c0c402c45c13405035031492101c54002d45c001c031002c07511018005410100c002400101a0701c00005240003248005058101108002c940b440d4001030180302c01c4035030004a5005200356800d0a08058884d94080d480e40b0000da07011580d0041c400c0d646901c400107000c1510101d402a80f0028019100e107003880d01c3e507207c890b1103401309041c2a041040e03c000c1c07030414036560034281111400c140a296080b80588409003094900d4840d4124060400004c281c3c0c0e860b18549240081c091031010160b000207445050388034115089040c400c00c0042100810b001d840d098203450000b41d0345030804c0342103d420382c10b00d0017240010444801404030300e900318001d00035a030007102c0342030003010b0440044401034400c4c05a200c081d0450094164498030400146400619680d03000f40380c0d40d1195082c02c81c10302c0600440005038070202c016092820301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 426550098 1250 426548848 426548861
    0x504060503030414130906090f0201020c01090e0a02130e010821160f0201090b1201030c0e0702150709090207030f201b13020c0a050c24030a060f18 65
    0x680180d41880d103040c40c0910021984c4800c0b9005080f50b08800a03816196840700c1c1c00c40b61701100030444820107061500ca00840582d04034051b1183c1c00c1800d156602a1024a04a8584aa00404940d210160305003c1e4010000e00020802017141c049150385052140c0c601800d450360080903c40009858044140303040c079400305080344100403841003481641d4070001c02c13640060081b00500c035284012120307aa00c43d0b01c84d0113041800300c0c006080c01d102d014610b048a0299022401c0380351540c050700c807080700550f1031102680c0a8124160700f545e0300d103000c940c024000e040c5a140b1541e14a20707941a80c1c40024201d0001e00e1018003083c0007034001104101c2107080c00c191284000c002d202259031101031401c1d00c85180240c4844200580e20040001e04210005500b0354032002904020b44e50741d000840304485500808a8040650030540300f4510541101d03a6050b40080c1003100d05c070b510303034000381200d031155450f4507000c19008008180c120051401403c1c1d15203010031084203c046030710 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 426551348 1250 426550098 426550109
    0x1501050918131a060604030204180204050118050603010204141908151f06200a02040f0b15030601020d030e100531021503100306050403080612010507081f03170301050406 75
    0x50f403041c03080e15100c0030244ca0903a50305590009004074011000b011481c0e8a46009500504000010840c4a440e11661075000503190007030140b03407241d004040c00d0340070b580a0317104e000d0215a512807079403600e9103102035018500842041c0194075145040d052405a070b89955170814070340e0500040c11380d42004d259030040880b0160aa01d0306280000382400300500d2801c814070220610a0006402442032060965005100b08140005400d218014120380d80d24648035000d400b0940a0102d14170080b07d10914050740601460302c480d1900f90020103803035031800c040d40b0508400000c1c101081c451507018561807136030440b00d40403104402c1542a9a244c9215800400d8030080d40140c03500d515481d00d250003001c9151f125591070b03100242c20300c000d910117030010382440244401d0640000201e402000165038014669040060047c240e81c0f040e80c2090004105030001000d40201c018485401034820083c400308130358907200c62100da070106409034181900080100302500e09403050a00400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 426552598 1250 426551348 426551393
    0xd0e0c090f07020604080c03120405102720060706060e0903070537060501050a0b070f03080a0f060e01080c030604030f050c071a0a0e0306150105091813 67
    0x42c00b075600945920000c0e0000748000340115041d07481c2c42c0c1c01e01c142c4403c207007900044122440c10b424026500c081062a00600c5450000034009486000c2c040c40c2c02d440d04e00941c440f000840b0b903078030f509801d190b422442203400e15090841c2242c0d40d140050000360701484010030601c1c20310f190b10a2500c40500030213582e5108000004c0002d00108642d000840054045002d00c03030900071101c0c84d84c4080381280c00f9400101d500404000d020350015050310810b440740b40071103407102d8119581d403144000180c4000b1403550350500081c07151a009900070044007010441250715040003095820640040382d95441d10401401902c2c4100300185034102c04038001d092501b8141c901402035902140c40b1010010005000e422490040003084014a286282d0b2003c141c49070f44000c00307a8100641509c0017607003455034100d4501e0005019805040b84121440d903111081c00150f032661f01501d601c035002400040c01c5029040c048405034821005540348002a100e149404c01d0120f003103603500500708 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 426553848 1250 426552598 426552601
    0x50109060c0b040f1208040302100c120e0c0910080111070f120e0a2607180b04090203010501080105160f020705090711011a10030203060603040f080d0e0c090f 70
    0x5940c0141031559003600401000c8031900c0e2804d050352642c0e42e820000d00354a0b0a04111640d040d8814080d40c82107010f0741c03c1c0c07000540d40300c80c10380c00d0701c03140e82d141000200784051f5080840103941c000c000c140510400c64144d000500041001c8000448001e4030303240070f403c01003118910a01602540c4441c41d00e03128648030b200c2d661141c2c41d082040c0003a1000c1014050306004034011035403481030b660001c085010b21030f5159601d10106040c2d00c10104080d41c041320300782d20107000080030403e58500f142a00980c0040c40c2c0204010021100c0865100d9150214403000d6242841214060890700002141c10301d02400d20103551210003003100200152000c44502c4590b0214006047e144225400038554817171031030484041504010400c0103510303248003401900350b00440410880004d070380d00b8040400e0780070141c0c1240011201c65030402001c00020300051000c944c00f0424900c07901c176103414030307051011142c01c44498001c40d01041c6d200e281c04012502e410304506600c4081e0f401d012000e03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 426555098 1250 426553848 426553859
    0xd03050f04080a02030403170a03140603070303080a06050409080702010201061e03080a1e080412030c020304121e050a0213020408100903050d0e03031006030b010c0311010902040f0e010501050109 86
    0x20032001000a00448000b08001c1c07101e91080c400c4a00a6810580c4900030001429681041c1d030f00ca10701880100740703842403488420019480340d51080324000c01070101c00303140da1000d0340c40800c0200030394041580e816020510780c0e0303503105010041d8050280c603074540d5542d10000e421150180c100c200100003a0208014103190750200000340e0390300c241e0454880366404070a86420810b440c251084107038007280c1c0414983c2c07005c2142e00c80c1d07004061303001000c00f00b00d4082c4d0072513803002000e60043e00704000910071003503003504102c2c400c0d10a90001d0401d60308100c0c10318002100d0f050446250300402403070015860b012030418140c99640c2c0b0300b1440c240c074041800d80d641c64414082e0f001140c613a4240407e05000380c054500100a909040c0700010300d00a40c42e1300da500c112400401c0c944454000310307160384a8818103808610684500212120f5610140c0d00000d2602c40161250b40303504c00c00006881d6809005224007025401250895405e03941d039007504c405030071460420003500030810a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 426556348 1250 426555098 426555121
    0x90b03031902121804050105040b030a0318030206040e010e06010e0a0603200f0705010e0c0f060705011e05040203150403080c0f090d1118360f0d020d0305 68
    0x401c912032401e03200c1021100803040e030a00c2c0d84081d280c4460600800e1440d0340c0c1c0052103a003114503001711010410340e81c80e58100022a000c8410081d01603029086144c0000e010b1004110040070b100e00741c03405c465a130384c0020480d5100d0f801803c0c0302c407000703c0104030303481d21401180e03006482400c2c0303060200d0001d000306a0b4070543d0f00c1018205900e07252200503510300121409000740001880c15910740c80030b8400f00c80c2e40d03c034203800c803015031808103120582800414900c908580003010682429100b108109454100741d4056555551b144405502815a400d07140c014004411000c511890140105410480c0c3e8150b5072613194214030800c40000e40c4040c849510203400109a078813201011059071a502803121003d07000224400c0ca6404d000c3c0c10b500810600204031410701140104480d0403c8800c801d440c03190f15040c81c0c0c000a02c5281001007142184440e100d0003414422891001038500355003110039202a4100c0b002d000301059042c4249a4408401d0038140020f00301543d0050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 426557598 1250 426556348 426556357
    0xe031209070630061403150c0d0504020619021615090b0d060902040803070c05060a1b0809040911040e070b040b07050a0515011806030f02010c02040e1e0106090b0303 73
    0x140000f0403410402421010341d0200281800d01c02082100d261901c000d90150102407a5051103445495540b0070892138801046125100065403241029054141e090261030090001ca80c00142880402d410301255809029000c000b50300905403948001003181102d20150482d43d4900030790260035082135040440102180c0c000d4801507540c00030119043e00501c51a00044116400010001034110000010300007186c02410060343c99560307036040107001d120305036410010440c031140100903022141d203008a240d000343c0600b803515840c0e00c006411100c5515048440740e0b02e5545200c42030409100c2c0c030140160b0701009008450400208405601885c031910038401400905641040414080001080d82c0101101c1035403070380d10500070b06424240180800b10106107400552001d1718098401103e8210b4201c0302d0142c1c141d00110394582182c40240d80158039468010b0040004000501100100540d009856000d000e030780c03400e40e121039100b25074260820001801980e001700444 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 426558848 1250 426557598 426557627
    0x61409060f0d11180105030708010c12090c050916021204140607081306050a020c010c170c2b020f0601051f021c0c021c08040909080702040e0312090706 67
    0x2800490b10310b19000d6030100740401d002c0e400c42c046000030305000998203441410380703504505030342600751140007407030807a152112080000f4101008001202183d503000c4c0006030300800750940c000b510b0f000400e41064098070303441110844150b403499000d030b05000400340c03142c0d80c0c09941d103010300d0240c4480b81c40080e01c201d94420360b800142e0408112400c011601911406050941080c1c0d4801001e491a0008180c96001d40100e5540d170b1125882450f011040c240c1c440d00512a03a600d040c2c60b030340c00d508561040043c0e841342516111142c4407550b0b01c1c402450b81e00d03481001c40005044000d0402d980a20f042401d984011f0040c84942e50f80050258900707081302003042207c940c420203e251450b5501e040d21a11500c091049916030301c402082d812600986500d0300d0f5400c200c500070005a420380001c1c02c0c80d03900380010311110f440c0390050414680075100803800e04002c2e03000078049421b085000141640700043c3d1080409069001540c400c0104001d00310040c90114003800441201549 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 426560098 1250 426558848 426558859
    0x30607030f1803030506010219050709020901050d060f060e040e150606040e0907151d060a26040605160c0201030c030e0a0614090c030703061802090a061409060f 71
    0x208110050692048081d8609818900b05141035410301400814007540c80f1401400303598411f00480341154180030390035602600400c40305280099210082d04800314442c100041040b20111340000d6019810240c003c443c40e90050314a01f05024019400d0400a103014508016050b9042e0b2404a031821461940407403c804c60f981d8003001880c2c0e40311716046071400c154514144900e0100c00a104002c0e10080e840400a11001c0e1000341c42c00c5000e030b218440060000d010489450401c0f80c0908a07003030036401c0400c2141c1202c908180c40e42000c1004600c410035400400040c0070361802101d4001080f0801400342082d010300c003d14400482c54068103240d00c81c5503105005110790302150003150891300792100d880840c9461006404103581d185003403142e00340498013001001c96010003021004004110072407070f51751a03d01414260005202414080740f45c0405610343c081800d1040c00070020000e2843d092690014a000100e44181d01580501d02008120b8892040721402c00340101c40c1e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 426561348 1250 426560098 426560111
    0x50406050f01080c160f0606181a010f11030f0c10060b0414061209060a0b030606010e040914060403021e0105070c020d02031e010204050a1e180213060801060305070e03060703 77
    0xe4850b242d481c08400100303006c20001001090121a62005060302c0b2140460b00866178401d41d2407041e50080c10f04084241140810100d40f90301403c401e5842e0700709400c003200c0c3c06441b81d0641303007150065081e4145d05c0c0800140031075026410701640c80d000b9403400c02002003508200715040b8600803030168034034800f00a020100b80e170365180c0a0300c090500780e10743c1030b115140007040319032034000503690130162a04003c60382085140100d1240d202d5001070303446402c03020704c131030800c0060003458106030360310b51072041140c1c4102024004644154040e40080414101c90002080e610044076440c0041e07914241c280400907034849a1841c00c160103c80c03c840c42c0d9803500011342000845081c0111010b0080c400d600d40310810740140040b50001c490034007100b5540e04080748140d082d41100006801c00c41b0091040c20300e51030f034051140744007060042c10103402c60184d010100254001a011509950041100e141e140c0101755001100380741c902203411480c00880d43e619030150194091545421 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 426562598 1250 426561348 426561367
    0x28031a1012030309080d0903080f0f0c07020109030c03030809062404023006031002040302030c06210a02070c08160603020906070804030804081c08060f06090303030a06050406050f01080c 82
    0xf00404c02c207a81141d08a5521042e4100b1305008200c44202100411202c100103400c03410840e243c00d02c2500d00074a4100a0b0355000d0a000c295031003410100c0c180590800084085150300801030055032098494400d58240300200d00d16041c00123144041c00c0c42d404a84490b4051142401002840e06450150f11249541c0325070851103803041140004801a40c2c07205054000040c6031805408143c05803444d000300941c08809900c1940400b9402d80e10840f03124070075041c85002041100d191046211001c0f4030448201c0c1d2030003041c2d0380c01c41c1840d000f241c04018480002d111800502c80130000702004504910300601c407241a04c2480289540411501a581c40340030445503410f0b44005880d6491b07450f071414054940080c010040e09204214180240f4031004002029014046d2078114503551020100240010000c3d0800e03040441070221041b00e403010005580900542c400c0801c026051030184400c85d03500380e00807403084915805101c000c8c3d03048060301d030300003803440125a074544015 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 426563848 1250 426562598 426562601
    0xc050d030903050d1d0a030b0f0903070f03020a0506132a05030a06020d0b01021609050703020f0a0f110d1205101a030901060b030c0d0b28031a10120303 67
    0x99101030958001d601070020f00b258804417003240e602000030b419502c04449024080e100034903000003040f171507410b80410100550202116030140032141200c0c6808070a550740000c8154114040300941d1042d0b036114104041401081c0d84540045c9d1914403030703e000e485540300340c040e80144805140e80b00b540041100350b0080c28401404003e41112038842a40c941b4500960102d520f40440c14500282200c0644c03001c5841c0d058604420b039504083d40c242519a001000e0180c01e500502d81d00f00000c02d203c20065002d49800304041d22990720b01c1c01001c0000e00080c00f45842c1c2c00094104c8141d04404940203443c9820f06080c1d800c0c00a43e0f990791851058440c54a5082601300f05200079411251100060085201c1c050100c028002d80c0e030b8032501d00c86140410f4400001558003070050040305016a4400306013a4001401e20208031900d004002303642812800b0403241e01d514000034400e04c0f60848407007500551140c0b480301d851500380c03e41410608180503110040d01107100900078188a1b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 426565098 1250 426563848 426563867
    0x1812090927060b120a0b011a03010b0c01060f031a0a0c0f050d0e0a0615060203090a14060d090c08070602030304111c060e0309040506031b040c031404050105040b0c0301030c050d03 79
    0x5044070715000c1c204c10241c0e942d080c1c52541101c40601d108000f0618034a10310f2810355890030482280e09503401c100d031072800ca03080912001200c0d07617100e01c00103035840e00703511101c006d6004030962000140409074111558a009000704019401e00d5075091759168803a80d052000d46080c6001034903a40d8807810342000d040200c0f07c1d11102d1251000080500c042c030b0b80090340160402da84c034181c0581d81c11080e81c40e8080c03c1003566102d500640104080100400380d050310040050000f0300d42407184001000310b946400080e5007800306040140001d1104101410180100340000c500b90b140507aa00723140c4000010225029000e084802c426000d0303410031104a070782e44040180824009884c074140d50b074000102c5a440b481c2000045400b0b400d0106010074043c00c189419108043d00d4400c1c40701811409031034030205652071030054000018a2042802248208004151401c00703044c030100c3d041015050030900302d03080004000044500079000c04503041075030340d040d41c00032508003503902803038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 426566348 1250 426565098 426565121
    0x914010914150705060f0115020c04020d110a180f0e040f05031603050d050c030702030a0e010210060906081002090303030103031101020d0906090c06050a050a080a181209092706 78
    0x501003426801c2104c0443c1080c8140d4407135030a0421680c0c0c038008490340400424007080941c0100b00110300038102500184012a00712401080502c002902002e00d03074850a90500001c00c5540e101c1500300704012100005d04c84a601c2c0c001150915034414110400504000c0440411394a40010000140280d51480e2200180b030340c20f000c0315040c060161f41c004000c2c040801e10302000182c1c8442d8540a503806405e40d41e00075401c0c58010103040d0340442a015201c0c0c1588108031201d0143c8015018001c0508000345002c54401d2504407054030b0044030013600d415940c01407000a6081c2c40000547c1d0460360140b604a50000c020b0002e40e009200703100c40c41017110b060000100034000e9903044580440e00c2600341213070066603440c0880c2d00307019040c14803000450407c143ca8005124030101c07034228280560000d42c0022929600b03850400354501180c08130148030380100c4072a0818282802030075040d01c14016110141000d413035150311013001000c011302d100300440921075603600401c05039a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 426567598 1250 426566348 426566389
    0x12030807020d0f2a1b060f0e06070302151806060603090c01080c2505100b0609100e130606111f0c2006241503091c0c030914010914 58
    0x25407509181e8841122001400d401c0900e1120006c2c04503c20303041c020f50100e0b140e03a5203107103003801c1e401c100c2c460344101d10035811407145004403050403110b14503107409502d2803000700550102180d08503040c094018600d5205480074002c00007800f10100d10701440d181c00b46000c6545549440204d10039014100796007810000440c40183e404100540c3d500d00c49000c2d03402c03a1a0460050300c0e6605131141a140560030135014411035165007404010040ca5041c6810600c420880000102c0c4041c0078042d200c41500e07440c1c034410484141c204080380820600312000c6e011490040c0003100141d58a040b222483c0c0f951605040e641501c02c080303002c1c07002801d248449042540050380d6580c1c4206940e00304120540c0301090742d07040b6100084050840024181080c040c0040b4202c1026400041a003000e6000d2400320840c2c2030b07801e0800310b247e02042d48034142254118100100900c9450304840e112001c21902010ba580c0c01403030100c00c072840b052804071148141008512080b0480281b000440d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 426568848 1250 426567598 426567677
    0x11060a170703090c140a09020a03062111010c12080a0209040c030e371a0f07090501090305032205030d0509040f09080f0304061512030807020d0f 64
    0x755815041811940e004450060034181c581134a09160091444010761000b2020010400003441d42c014041106003400c0019000d586ea03484001c851a0000c910200c80c41041209800c0101840c26036045c05400c0c6010b0340080389560b503052585114941d10800d00c00340b200050a00540c030340440c1c080354400303482440a00003402c8058050035281c10904002d0282035418000455504020106014400070440586820303100440c0b075407030140d009841d500c2c2d00c0c4003103c0f100c41e00d154080e40100350000300034240785070440c00185140082d800842c108010340500b04007240d4008196075458100e05008401207044014801d14061180d01c85905030045203100101c0e0307074100d00070f0b0402c0c04050b2018090810b001a107901202c04800000b0003190082c041c010300901400040d6074003a20400d00000e44082000311402004107a52110204c55600400c110405d90712400782074002226000600c49002000c001409440d054400c440800c508424035642441c25204951030b56060b00d84002480c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 426570098 1250 426568848 426568861
    0x1080f0a11210705031003060203040c09051303080105101e0e030607051c200a03020d140105031e0d051c0c030603140609030a050702180901151211060a17 68
    0x20080b03a2601e0040800710203000403052130250048070b2090340c6c2000000c210600b165034001c0250405032040d01d86092101d0b01080b001118441d444c0550000072201d4947c484034a801082501c0503080240201c10303582c2d502d8201a0816890440c08003d1a01d01c0300c4d405a0100c00c0b582413081d800318551511901061107007494100006021043d4907200000040e00f02c49034002c10703102c3e541c0c0c400214064443c5201c21652906018010341c00e81c074a00580b5003420740d0313100310544041b804c00c084050b440c4001000245020012410100d080c5440203050b43c04030102c0300d848540c107440e20010321800049055014201c00d100c1c5020032003000d0704000008500c132004000f480d86001c22106800c4800c4d0040442c54001101c922a0501c240150729100140340d003268039400106003203800107211140c07002050700040c40e061003064444000243d01d103541030751910030b035400d5003d502d1a2000300e01d00700205030f0075100c9100302130040c1d40301941c030306003a2000c5a044081601044891074846c00b0b1002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 426571348 1250 426570098 426570127
    0xd0524010801060e0c0a0e01022b0e0913060f0b0303030f18070305060a090c08060f0423060604020c0703170a08010b032e271a01080f0a11 61
    0x140c52560008022039a00d405102c0510f07003081d907401400b17020600410700b1203881145240072618040c0706a40e43c9200380c04240349890b440100d01402c0014503100d002d285c1e80c2c85100007640e50412218503240e03050030034810315600d011007406403846441310a00080e0440507000100b40701d002a048980d40e242c01074401200000c144c4008001600b00c0000c0340c02c4580000e40402940d401802500440d15911400d0001b040070207000c581c40400d841c400140c040f824000944180d8417110707083c00a141c40d00c0c00082411034820114095100f113200c860005c2c400147c07195100900707a80c0182d07038404105656181010550004210f6085100d03201e01051030704000e061000c000381c444040690302c4242887c2e250200f1a031004010041c0e901030300c9002104070000c2d0018800008000f1403a454400c8404c51110000c414000310741b240e43d00c000e9102d180e1080030290344040d091542c240e2501c5c0300080000c00050448050311000d400418080c80c801d41c49100d40804002c400c0b0341e1000c1c0902040c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 426572598 1250 426571348 426571351
    0x7060e070b07050109140309030312061f0201020a020c10090306090f080c2104050d030c0609050601080723060702012616030c0c0201270e10030507060309030e0d0524 73
    0x48007182031b0400e450300d01400109031060301600402840c00c00100b803a0307251020000400c41036101b60701d9002121509010001d0035800610b983c00540e4801920724042c0c0b03810950048079004000c0b00e445440e0f00c43d0f11071029010740794007040120f490349990910f030407020405000901a2000040e0104d0034500014500b94a242181503400c80b50188410440c0302d4000ca100c0d03103411510101001d000a0301c02d803c0040003500ca034070005040040350b1186880c4c01c0003600940c5256000e8074003800010030400e02030034101240ea20001ca1903402c400418560b01034490700906021401d0b00003038084182e01300c48510100f020303d4280c2035213440510700e4800c407280a190008240342690000a80748981115600b03c1c1d01a12404c00e41051655001c6006021400d1809610340b8070f040840e2220340d4400d0103004c0c29074440702090882c2141407660070040f2036840407080c1844c0503080340c0084d801080ca4000100c084409508501c2142130640c00d01700520040c8420341c1d1900e001e401c0b402d440d44c0505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 426573848 1250 426572598 426572603
    0xe0103110a11060c120403031107060501030c171216151401090506030615060a1b0807021f0f030c030603060216050105180c1c020a08010504061107030507060e070b07050109 76
    0x1ca0341520742c11503913074151043e85081c0402030303039003000500420300a030081e031042c1201184482c94036110b911200b0850b4000e070400c072800a8044030802c800010340b88143d501000400140007603846007502089281b00b07448258603540e1441c9101d10a0014008400c507255010356000e100c0c10701c0c088445910700109010f4010410302d02800304815080c001b0346c161103680c02200380c1050381c100308200545034112400d66000c100f0b00410b08150035000382c0030404210702c10f6010549410940c41008213400c074110590701074500041d01e00c00c0703495000a854290046505002070042c0e0408001c501400c0c5942018290070b000151030b01c1c802d485c0b220381d8a80f07540900001c020a8a5050000c044018060760001d42d66112840c804c0a40c0750104000c40181da440780d0070300017204580c0c08180d0041075503000c800d459665504200900c085400782010381600350088618020740caa0b800350141c000e00c58003030000f07a95212692100d4000308146c0c00a13204a5049640354007882c60b2036800b070a80350031b04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 426575098 1250 426573848 426573853
    0x120b010512070f18030803070804060621060c0804030804030e06070803090c1504060f110c090903070c0e06090a15081603030201110702090f0a0b130b0f0a0e070e0103110a11 76
    0x220030f40000003103103130003603d030b02443c06403560300c0d6000c04680d2600081c0c8240c91072692034000188000b050706500c403414401114403a0056250308042044440280f00300045c8000c0b01c0401c400240d2040c8080d0303005900d0700b04200648900c03004110b450107110720042901300004140642200006895550f20383c08480d4002c0780d803000306050303010b03004038880d030400300f902009402d00b603902410f4516188610075007100c0803025840002845854244e41c1501c6640001070b0310740503c0120440b1a010b0b02c600a8100014104240401c0740b4603002040750b0101941c1e160040c55001940c412200140141c9040728000104c40c00c003150142018031003240990302e031164164010b404042507546880e00104045080d039141a010010900028400b481c0281c0d50a514952541c5280c200403c0d141420000030b0080c1c058030038010301400601041e881020b2060b020050b010344803507000d500c0401480c01403607072601080181c001d03000c0c1014a034119030001c64240d14540d40200d036489101906401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 426576348 1250 426575098 426575117
    0xd030615020a0b060103090819030603020a080109030509060a0519081e0105030307080a18060e0901091404030e0f150a090605040b1912021204060b10120b010512070f 73
    0xd05a0381c030030000000818030040711001503850760107544a51000742c0188a170b00e203030a540d654007020081c028030030200440d644a0f414419030800000f040041c008410081142441c0c80d00c2c0604079000300c408191240c1c0000032050400c920a50603504082d20041002c4c060001500002e08040c8088a508030b10110040b51504a04104016181220b101802035850710041d6100d942c1d299221104c11000c2c4000c01120050f000110aa001c0060129607602103140c040e010801002043c103038091917a09080c04810b0f0f20382c403116500550400e81c1410460040d4001e540401c03000038000e24a107512950454034000c0740d00701c00c4000d1404a030035a8403001a1512264203480e0b0780614026150126401c2c17114000308812900c0e03083c0780c3c2c0c0ca0742c00c3c41c40000d0794140101c0141e034042803901d4241c050400c24001040b641c0d0003401c4003494201e800c03a19490311245e0040005110000c1e080a8a49811003142264090001c4589080706900580d201d440d01500181a8000c2480b296000890050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 426577598 1250 426576348 426576389
    0x403150c030b040612080d0e0d08040218071b020f0d03110f061605030910020403080d05070e0f090402040b04110a08060d0f030509030106080f01090510020304080405010804050f0d0306 81
    0x120f1303141070b03c10358001d220b0101c100e600c41e403c41d5003100a090b00c94541d5076000140f10b40c030401c807803a640601030340d454410385054414030205016039070488003542d80c05c0d003d1054590b000b414911049408044481c04d044260001513442d45141445070307000741508002d2020705a0250444030001404c0089a9404c480c40e8080f581d1800304581c00e40d20012905400b1484a100f003008540012958084580c05d02171104008101e80c401e03401110305000004007900d282d500d900030310354465403034202090102e030a24045481d00d00c034911307107601c614020800501159207944c031201101c003020700200050400105410807a500800e00e00c004600c03c0f0700002c0302481d0005800c00c58a52108440b80044901d540603160bd03008041030075419500d48901190810040060700064035031080041821070581c02c01c1414800c488030b18019035401001003201107603019080710220b55003031905200795613075802c003a4141981c4000141c21806400c00c0318140580c140c001d0015078403020541d81e071012204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 426578848 1250 426577598 426577601
    0x80417120d0c1b050a0f151505010f021c110a0b150a0905040f030e0102190b070e0405090c150d021216030b0321070602030415150803030a110403150c030b04 69
    0x48001385240d000e1241791000810b0707001101000b6200c2d4001c4580d120640d1003160580300142110150054150401c05c070070b60340220344a004904900240c40c40340d01e1a8070b01a0740017070b54045102400b00743c0b48803001c00c20041105064064018200400a0600030b017040f41c1142c1c41c0d00c2c03051044907a0980403444948a10178240220361010281d0100a00c030b94050303484a44003040c0506600441c0e0011803849403821180540920400762000076141201d00070303041c8500b04800a000d00d10380010804441d00c0000d41107403640c001c4429070201a906240f0b10300724031070405003070042800415035015901c45480881c1c00b41011141c40c10307040d0072900045007250044941e041e4150301417401e0b40c0b4400c1051030500d50303858204400a180c0321650315082c0903039100391005c948200c00700c142e801000300d241c07194044101d4400c1e8a010440d02c0e0590f4540d0342c1c04041c00c0903030f54558402802c0c040c0454141124001c0d94030026605098646008020041414408a00129044c01c000d01c14a103001d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 426580098 1250 426578848 426578897
    0x230d0e0d1404060504091a09070f110705032a060409090b0106210b0301022a060106020d08010b0f071a0f070e101407141e010603080417120d0c 63
    0x360761150b050074036080d07035400608034102c07c8141e20802000000b1540d2a4200102e2048146450718282810078010082002202c1c4115000c5504854010b000c9a0740c003140301400035901041055400002c800694035608400c20700c15440040020300107490019a0002c1c10040e000303904286903a81d03544410784101c8101c8030b445000f12010040070312440202e5018500b4100d01400050420301100c800403900306240d0001420000500d5031544020405c1161328050400d520141c410b02c54070003c007521019041c001c1101c80180802c00e04003500b014030a582c80182c00010440c1028035801104496040c1600d02c0748880b41d500340050341c1d06003d86401040d10101600611460300c064030101d0b07001ca517101000718001000c0060b1004a040c403001c850340c1c481020007400b0440030090200000245014030a0296410100e0400100d44404251004c541d08271103030a80d6070200440b100c0c100106041208005400460305820800b000e41c441d250048034cc1d207440b10080550704004408090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 426581348 1250 426580098 426580109
    0x140f0403060207140d0504180e03070305030403020c030610230f130f1b111911010203090d0b01140a050d06090f05030703052503230d0e0d1404 63
    0x10100810400908564000d1800390b0040440e46401c1850759101c50900701e07203a00f04400900042420b01a41c0712070a00120300420700b16041040400082800b034a030301640c00003509101010001070140f500034802e41c2c51302d401c02400e94600d072914413800c00c000021030003000209004002d9012010b44040882e40075000300034500300700d40c10481d0412488810380c0c402c48a04a456160280c011500c82c050110002c1c4061aa400300e800b000c140107000400312401c100c0a540419800c2a1f521800c3d031740001001d82250f8186c0c3d042c0d500d00300617031a600c0340100302038000c60101d15030030600200a030624142c401c21052a401410700da406c200000300b40340100360b880403c0280780300010b906a0b0115030120701c112100c034011425511002d085400c03c3d01e054010a800041c0402c061508a03c47e4020a045c1562860407105944004054030340d003c8080415001d00c1c0501208180c1203002e4860413484044248040c080b203010036600c03580e40008800c08109044200d0100300c0441090310706869 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 426582598 1250 426581348 426581377
    0xb0f190f120c02060412020c03120703030c050a050301090c0504030b180f0d0203030c03072d200a02010c0312090c050909030f032202131401050603010501050a0c1a130314 75
    0x1140e5071070740c0900c0031b8031609640c154491030111003401d8500340403012107440c003048007540740c0600707041c0503041d42d030300c1c460503810484100040503020b90000f0980341910f2a16500050400c41c00f10300b6a4940318503040070b05420311034410400d00320040c0f568002e80d40d107100c0540e04850310420201e035039040400301c1800540c1082c400604c47d030f840c1300090740e44212245041c3c46000f105554208003041b01d03524490420f072a4030104000325030005e40a00150340226001030b47c110590002c19254402d540009041040d8002d42c5024503200b580301454010340340000704642459454a40d40c2880144a014015500c20300021003030342012040d11a90429017003020724581d90103001500a003640d0483c602101c1d900c280718400360303d98945d20802c808602c01d00080c0c0002901c03001030380b001c05a014521500b0204014051070740d100058a00c841c4031414882d51004441c644a600b4480146542a43d540700d0310400151110b00ac0c040702c0c04074020748800b400c0000c0a07100d1f01d100d00c6520310310b8030f00f02c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 426583848 1250 426582598 426582601
    0x6040306020c3003090106050a0806010609120f03300207020306090f0303040f151d0c040606051c060915030b0717040308061801060201151d010b0f190f120c0206 71
    0x500c803e0011540050b4030f50000a2280c2c907400090039070b10954100400a0340260014040c0a401500c4a0003500d091600b802803603119541d803c213042400c3d40006d00304683c5840c00c820410640034030406006620914101c2d003080343c02c111000b90010001607100f84507480100b660404e001c0707410100b0400b440e015529690711502c644000e000490320444802c0000307102501d41d40c61038403c45446002d03451400317102c51001c50406180500d00d44000348940c0c0340c0175003080000c0e04001203030280d0194000c81c83c81c8a040d248400c00070320140e402090300c1801c280314030340e0003030340504020103491180a8504a03611001021030309001080000c0400700064004540464000d011079544100c004080c194550350846e030000105800380e001c0b40150391180041c0040c03d03880c194180190001611800340c0721140d18919501c0e03101842200d010400000da2103501d54000c80481d001160b2085854020030090b4000a1400000714003420000342c9410313903410030007024020200107005540c02800607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 426585098 1250 426583848 426583933
    0x301090905070b0c010504030806030f151810091a10060c11060705010c080a022502030106030507120308060603090c040f18080d060b040e16050906040306020c 70
    0x240308040055400d441801030002c0e0300000e00004012082d01c0b0b200101d160b0620340350150000c40040e0225120750003004280c8c0c3c0212000410120050f050100e860894a0704540c0c0c8491040708800490203026064032840d480301c8030f07004402040e20551003491292150800d010010782d065981031018840c0c1c0300f04019007845610f007004514003410300709143c441500c0018005031711101c022580340e5101c86003446072540080c0207c0d4001008075056140c1440214481140c0103540888010301480400c03604c2075450942c04100a1a800402c0396000313900c034440141c0d034001c10340d0b08900203141c1d08000350f6141494010359001e2a14600100207100c00c100401014004061940200c03d0b5100011160b80241c0c0c107000325110b010704c4206a40d040d61079020001d55500e9006807c100c0c000f00000c104154585640700c0d400030340c000e0a5190080440821112440740c8000c039680444003007001f0040c050554024001d0035000ea04880c0743c600e880c40e0842d0b400d00110301c0030007114040c6884620 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 426586348 1250 426585098 426585101
    0x3220f0b0601031418070603020c07170f0f0303090105090a021302031f0b0901120e0613080c0303180c040507051605070b0d050612010b0604052206090219080c030109 73
    0x70050740504010401c15200c4000704d200c03460032500c42d800c02071a50501c40c1c440c20240202c1c6c010f400640350541c94000b030000c540d5520900c500c1007620112040d0352050340c020040c49910000b281c0042500d040c4041b000116a40f80c006030b4000407075510301400f0502d0040d001500304090f0b0350181412400c00c00b160043d800035000180b11484603010b00c0802d50540c86a0300384070300070b03003503034551107489008220004280d148942d080140d05458803408a85055001510990111004611014412080c0b401020b40e004022101103244404402c0c000350100d00c8242e9004d10400f903088486030318005082100740c1e403013590000d020480400010102400d00e071420140c2c035014008903800d43d5912141402558014107250a50565500a000e16807419040e00c441c9402000d000307012a08241000030300b503108900ca00d07440340b0018440c891404400410316908011241c44c2041500e68940411010398001d5a01c41d01e440318882da203101560141c44842d00410780c7c801250306580c2400c0a000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 426587598 1250 426586348 426586351
    0x2030a110f04060603020406030f050c040e1b0406020c12031c0b0607140604060b09010f0522090309080106080d021b0402041e1d1e07032003220f0b 65
    0x780c01006070300038507420707455034080c00c4018403407603500503a103500e4010020101c90150143c0396580c0e00b020b092100d80c2090100342e40c241d5008006042c40c40d116030300c0300360944040c10b043c40107040c808a0300003206600032410740c1485105a44815204c00c1511042c0e4692080c44041e000e0103800c22007030b1082071f426910500c05d0800183c1051300d010441d0b02e4042c01e04407000c0401c0c900e40d00c51410401081034600610506001c15105400ba17541000c0071041918058020320303001e561905840800720240d2000c00070440030300201040115004d003001081e0603800d008250031582040c9001811110018604403003d0b6254081c000c0c03540f803003511b02025140098180ea000742c083c8400304480c81900d00c0d605020340094510041c0a1070046a0368260300c5c00400342900f000302004210740440c0090b51100e071a0042110468207944080c0160b0082a45d04665910a40414905044074151000071400788038070079000d80c0c041c202503040c081d0300032840e80b0003810510544907a0000a42c82011203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 426588848 1250 426587598 426587633
    0x1120c0503160e1302030a0b03012702010e06210705090f060d06030605130c151b05120a020a060e06040f020904030e06070c060e01020105101a1e04060f0c02030a 71
    0x20082804960700180240004d1900c42a030300341c1c00010b020760200e0714441d841941c0000d90090195000856501d000400e8940b100c074200102c0e1081c007011a0f1241134a4028035070010200c40c2c540200d003804603401d1072500b00b904401e1555801040c14035010310b042d208a52030007450b604040704010140a895000342c091a010983c40d0740c1c000c000541e07240640391141519141c4008000d80904100031510603076444140360b8401800b070305d03078465481500d204410200500360183ccd541d0700e24095141c044d894403204140c06012031b005031040e501007001b00b9a940201802e2019a4141020603207441050350014a003c02000c01c80005040a1001c0355000c2d019050803000c800b4498013117082580462000c0301d100c0b00d07041050040c1c540154103d01e54040a100821a40c90b0504207070100e503006010301c052000325180d070584085204400c407640c0402c2c0150000010745402101d05003500103009090100d0000c204200c9014403071b0030700c070254580050050141100940380c3ca0502c000702d5070708 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 426590098 1250 426588848 426588857
    0xc010c0b010515070c031b350c031204061101020306090f0601020f070e0609090d230c01061205210d050703060b07050d020d090602033a06030201120c050316 69
    0x300400f003042c0030a405e00450058915030003022a0b001d45160074200d1360080901400390044507451980c00a44408542074450950849031240e0080c40d494a480103c1166040c4101d100c150000076210020b0405c451098842521400c07030f00305030300d00740c1c04111035094000305110002140e4911041840c1d07009803043c015110f610b05a048018108011600070402801c0c5c98030900c181c604280804a031b000040c40f01034202c1c440350b450700030845040426800034a400c092640000004000308984c094134046008004255681c4d410107140c094401060341e00b8028005282c40c4201403210510110640c3e03400c4525040d0510307800c400609020301050300700b6548800225064910703c0c028900340d800b48000f00b017000d0001600030315090404030044104440b04108109007500001035605001c41c8485401500c4071181303c8604d034025081c80088000ca4045100f61a08402d51003403080e00e000380c0c0c0b402d0040485580a40036500002404000224100f0005034103910b010491101100076141 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 426591348 1250 426590098 426590107
    0x20c24030a0e03030406020c0c010f1d040e150a110f030103080c0102040f0605120108210c0c0a06050703020f2a030a080307050901020c180c03070201020d0c050702030c010c0b010515 80
    0x2c032860741e001110100c610a90004090601f02c00800510a03020700910f084510a070a4400c000d201e48092140d00f0910318405004510b543d503160002c900029010049500a454452505550788000d40300d0164483c9810510b071024100d100071142660309460070329246902c1c554071407841fa0300c5200c2404940d50b00340b2012a03105010003850006244c0395485544402d4002400d030003421040c0d00c05541d680c00001110b03030040b81d00c041d120f401d0300400c06140d110285040400c5c202800103640a0307104410300343c003068aa400c1809803202c02e0280d400c98030304d8100c00f40c1569640141505c0c0b00e14441e5090350361080b10070720701c2c400b00c0c403c003003e81070310701d0701c1049c4ea5044141e8100390b8661020640126500d9903959040120312000c1c01c04031240304c3c40d40c90024203652042c5020b0400d1616040000c00500e12038000d404407403481803e03030010000f50701020001401ca8000340c208912030300408514040350741c45034140401c2c06401c1403040030603919000421405a41c50103000e02d01c88000d01c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 426592598 1250 426591348 426591371
    0x606030a0e0a082a1009020d02151b0f060103060e0a020301051014090f040228060c0b070809100b01031e0507020708120304170706090c06020c24030a 66
    0x1107402d040e48140241d90b29480d00820030f0158001c2c500301d400d00c0d01d902501d20701c0c8950000031038075904008218005100c507203a00200e40404112100650407581c901da424407190180f02c02090490904450300c481200c5890b40c0719140c8041c0305d21203007151b00000040c1b0104a50303501180050400c4d0303080b1954011568007080c2510000c4131031680400156108100c100c03020b8000ca20045070071107081d00c2d0791400702000c030354442c00504084d001e10702050251414013000d59141e140110b268841c5118035588050080111350250402c441441d29000851002c500616440380250004405000500c06200c0410700400065003500d04168690040390140840c002e800440c001c80a00041a549080900a0302e40500c80e840901143d108000c9140b00760300910940703822582c80082c816400340680c80e035200c6c0d03000310316014203510301c0d1145000403c41c0341c03903001d8115141a0256500f001c1d0407000c00486070084c410328845c00501c030000d0030454829100070760f03001c2c5003032038005501c0c1041c2c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 426593848 1250 426592598 426592603
    0x402091905180712020904060518070306050a060e010803030403030e01020409020a09080f060f01030f0f06020a0e0102010606050405031510030f1407050d021507031e0e010e06040e0606030a0e 84
    0x7600d50b40051511800446038100e02802144042c258154003002c0441c03180d404140c61a070000d10141029a846001c9030f100901041d040c0d45915046084039516611303410203034010030301520042c90203842d11000161210480007968100d803080c0020b1400d6a64584003074026201d80c190154140d50308000126983c50184042d12442010b135071268003990409118510f4515071004040040c0d0001080220524a444186040d6039019506412000e4a85010140c60000100040006001151910949910607460020520242d00030301481d0384d134040913181032260b4082e1070b4241e040382024041d21001600a80c3e0040b100c8a0403001c550350700d46600c030030380a501c00d08407800c218030181da071074142c01000100c000e402c04640398800c20219500040380b50400740940f03822800003080500506000e110081d031005d0404a001c0200c8902400007030102d480300035010302141d0140300b0240b00341003182c10b40c0c00b55107031600910b906459400403c203240d000200101c1810f62602c3c51070111000a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 426595098 1250 426593848 426593851
    0x1101180509100305121306051308190516061d030a0506090607091a0712021f06210b07080c19050406030518060609060d0206040b04050103050c0a080402091905 70
    0x220a4600020383c114606203081c84001000391650030350620131440042e00700c90202c3c04442581c100f1a58031061030300c40c0c04444145070301c123913a070380a848092409521180f000101191090050f69031031112621008444511800380340c0000e0941d000e200c3e0100304061002a004a004040711400d81c06030355070910384003080343c0b8024680c02c440c0502c1441604218405c020b0150340182d25541100a518100c00b40100c40740502956034000b4005115070080c028100786c008520355074041504243d10040240c10300e84914148151864403c5044428054805d140d159000d2035503002a00c41140440f02c140c000b034083c059030441040141a603480d00c01120001108076241c080e1200e10b0068003070100c03a0300400d45c42031410200b810102075030f070100e00d00f640440c003140c0c02500c0da03c4103404a021205c0c00340c0000d402c501c000070003160308245c0201601c100c6a00341c0e81070086c1d50b1000000b40301b42c0035041c0000081020703030002c10014075002d240c0384d0307210300c58881c0d4111904e40001d164080d03d50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 426596348 1250 426595098 426595111
    0xc0e01111615030c090e070f050c0102190f030605060423090a060f06090b0d110910021f0621020112020712020d0915080a230f01080a1101180509 64
    0x100707038440702022034150040003d41c800034180f005205d45080070b00c01c1780440c02002c40081100004804180c01d01a0040d240d01c40c00b0307500215150000b01c030724100c100745107060740300214400c10f1511510314401d000342010383c1d201a20441c2400d00d020b0004240e0742880301900502036007000075600c1da440f04484c00344200e541c5840401c0305490114902c103010001d80201042001d1003d040c04948094030072102d0301824a5000260400d181d075003c4554010385010603806110184100b0034164005101c0e04a082c5040907102d088074052a41001c441c101e2180c2031441054401c50702d021401c10140d240c0660040c181340c1020406600c10300c08a920504040f030307030546659070410700154104000b8014401e01c2c107005ca0845d051500c03200905200924080c01c212111000440b9031560380c000a11550032004551480107200319400b00c410741c101e405845c0310641c1400000c48140000e0412100d1360862a980f882c09091401124608e000040140c11020007920004080c0c87c1c800b01a0312800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 426597598 1250 426596348 426596369
    0x120f090d0b0406110a0c29010605040807080c10141201271103060411042c150901060f110f030d0e010207020f0607170406050306010e03010c0e011116 66
    0x546443c3c8801150b501a52070092400b060000034845900b00d40d41601c0c41e074001d680c02000940012229400451000c04680c0075503185000080240d0000060000d0380c9884040d01c0c4030540b21000640d41d4044188569442484402440c0c40b440c002c00c1c00040e00301031541401e1a028222192906a010a07808401c2100c046000380302c11030f04001090700105421b007030a121005403a603401c040b5010292006120350303507580c178500b004104002100c0085c0002c6d90710100c5e10108118042c05048158807908002c01e06030001b40003400c400c1d80d00104070034014a0444d850742041e07411680160003800700d60900c6004995400c0e401820000200c081500000031035658054140c05025140d49034942041c3c3e07030060290600503605e0f580c103910400310a0311342a032100c00e1403e02001c821200c480c90030950100140101e01d165200d0021440b41e4400e0700d54000c41c3e14a403052608991035101154002003482001c07982940c41107509004d44007584c1c044615286c05440b40389804030491f80304002c1d40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 426598848 1250 426597598 426597601
    0xe0c0f040303170c070f0602030a06051e03070501050406020a230a0b04060c0507020306040210020a08040303020f060115050d151a0319020408070311010c170d050903030603120f090d0b 81
    0xb8032840f09015071040402c002e031800d02500e595003c42c1045081c2006202075000b00009502c0c2c1100d40c03103003000380401000340708186100440740b00352400443c40c03580240520603004c034265005400301e90440f501540145120301c85922102d1029860781420540d09003a48000941488200481407045003e10720b50112401d0610300801240d21000b02902448410b114600241e5004100c5591098050b1075581840303840349812401d02c040740302c006004030408503003c03060580c00a41600041404c000b00c0d00283d0700c82204078030155007201c5040c00580c04200040341d030187c5d500502d942460740c0300844500741d228250f00104034080008240038900c00f00411800304864500020188841d840441c81e041c00c00c008683c81d010075010150050240c103886110ba64070412194001c10742108e00006040041900e90707000b81d0007900e20440c564284000b0840e8541e010085a01a860090003040c003442d28207003c04441d0016621440200000c0c40340c00000d03114584c0c02203546124030251f03400d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 426600098 1250 426598848 426598877
    0x1e140d1b0201050c0906070501061a030a0507020312040f0f0606080d080a111e0403060c05180a060f0e13020a180b09030c040f0f0608100f0b0a0e0c0f040303 69
    0x205424940400c1160f060400348090411000201c80085d4425210942e031041d190405a000d405103510240104100205000c3c42011510166000d0440c80606204d2521100000c85e81c90044a00c000d1590b0400004107000841d0301a003014280c0c0b14a2040e81c0024842c0c507501d040743d0301940068031603080401c000101984c8820043c1d404041c80c00704204003075240f051220240683c4d48100d080c2a05003012541d01f140f001e050701c0043d0740c01402404001c507642001800360b0060b114a203810303010001c0c40d4409203091108003040c0e99550b91401c0a42c89189000c50b501c44d04030203402d030040c61070f06c11102656918001014008196100c00e08000000400e0446440265204a2519005011000c030581c2c0210709030801140440c2c000c2041d00c0c0400e203180082040302d600303000da14035002000070219000b20744c85140c1d00140c90108010425160200203440b00f1042440d400b031800c01042c00554000d43c40c40ba0003500c01ca488604026107105203d804d503009070010b4002c40d00f124030b841071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 426601348 1250 426600098 426600131
    0x11a302404050a060b0a0b0d1524030c030e030408060103030f0f120203100801050403080417040303050403080a03060e0f09070b1206010e03010b03010614120105071e140d 75
    0x540c049005000c440e603190a442c1d440e210320066a00421854480740d0304850b55403031440a2000d81500300c945943c40640411000c002d1102e108100b100c07215100b00001c0101e002e20807404441007060910301c0d40c400001c01140109036030300b0030900381540da50b1014041003040000d400238081c0c42004284a505506000d0420a88d082440c01000448105100016400060b03400802c6448602603100d4603680468426500150041c433807942c60a0100000d050780007503180d000e0790050014a140201074a902d0005125034040607001c200200020400100c042000b000c0800781c034680080c403591105040150303250b0960b440305e0210301c10b10511000130800c0c48400010140c4038415890705401c0c0c510346188680003030000341804034040030346100c1d807030039000100c04113030041c020001c0580701c4820104a5483c018103e006048076142103800e10814451075000303180c3d40c0c5545c1e520050380580d8510540742038413048100006904500464040c1102501408190f01c20104034944040051007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 426602598 1250 426601348 426601393
    0x10021c06051909050421020615040b15070c0e010303110c010504030f1b0b0a0f020c03030406080f1b0d0b0108060a030c0915150f11011a30 61
    0x910484400c10010140b0701019640c0003220300480003c25036075100c1c202410b01d074100d800c40c04103105559042c0005140d0200714984940e03601c02004001413007841c00e000440f06840d102a0f04119a000c4030000340c81d0190151505034400c1490501c40c80d108e00302102c0c84002030380210f0104140c141d415030088170510440103000400c1c0303041400c0c103255484400c000b00c802c2d880035008108840841c58098405034204016050589206903901c02808009055052004203070006001c0c1c0951080285004000c603001ca176620354030350446407101c2c0300c1c00e805800f0152807200030305064040952580e2440020b0005003215620001e03405981000142802d05d00808083c403a200303852080c8001520701000b0015a03002c54400526028541a04440c5442a4001c81410007020400440c00b5600181103464442c0a0b0340340280380c010b40b441c49003070340d10701e0040c0c000b031600e42100e00c03010303082401d0740311070641c0c040352000d5844d24440c0725034074a54104090302045410503189035110320075040116 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 426603848 1250 426602598 426602609
    0x4060f02070b180904140d02251a0c030d05010b0307031d060c0a0219050a120206071409040204030602030a09060e070803090f01030908030c04080606061606090510021c06 75
    0x11443e240006200400c1c00c400b8505551050140708041030130300042044c0814202d803010100c4034a04022800a0b54410202d001980821300c207010413240c0f440603084210481e50360200c03150454241110301110303500109041c0d44180700a00000741c900d6860b0042314002c01004107072070350300c0c105400c0007000d1719158494a03082d000c074042c44000132a000203107240d216801d0060070341c5903144d0500881c2005032140c10861034070784146c0d0b54000e0140c08500d40c3c051070700c2034814000da0303041001e0598075581c2c12100300000c98a0f242c8201c8051078100300402480034000e0006240c191a5502d101c100d81054500d408a0f507964084401003103d58443c01d000c0384035040040000030324215200ba641e2040c028014058140c00050b0708075a4000d80001c01810381c0406156200d00e400c4603c5441600544119402442008003145150525804550440c243c921044601100b00c1e01c60201811584104a8013032003240c103050300408081c800707890030002d214460004081212000025118a900704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 426605098 1250 426603848 426603869
    0x61206090606021c051606050609060406030b07080405031201060f030c0e101101020403050307050a031806090b0309070b0409060e0a06051c050309030a0606060807020d050301170a0804060f0207 85
    0xc0c0711058000403a00c0280c10b003040d603140404c07005841102ca42c000c1200c0220115450080b582c01c02c04581c00292003000144c1e074090301941c0c0c0c03500300403e0354120710010703220b4180721000c01c403447d100c0c114499000b401003044900e0103049c0000280070312b50907403000d0b0000c1e41e0703480e040b0310256250155411104903440c0038520440c461000401a240c040206401d00410440c0800d05203000e4060b074000316001402d598071204039003003803600e030808240c04500142c440c03184403e1294a002c10b01007601c80079600c405181741059001100b030b40c005400c0042a22a046002660440c070500400c0600007036400030444d1481c01c0c102099983c005000080c1d0541080001d0200b034468101c2070f101740784c602a9004c460b07406410402d04511500410a816025100001c020700c0450307000b482c200c2e01240d07280e480d281e49640e422629114200790380c00c0016810001004081c004c090600f007982c0c0010203403a5045150303a41c00442da480741e0310160205118100300031469406125000c01040c10150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 426606348 1250 426605098 426605111
    0x1207111501031a10060e011107060e0a080d02100b0105160302070f08031c1e0f06030c0b070f03030b0f090a0e150112020d030302090405090c0a050d1509020f03030406120609 76
    0x301003d13050003c2c0100410000c1e040002004c5030302c2203842c40000c85900c0142d90b1100e48407a00102260044540301c3e004102000001444403400541000d54401381d50240c01004e100c165114050192200004c0c104501800b01022070100c0450f03c1241d10b2183e0010030200c0d241c03407541002d0b43c225510264641c3c006003d0981070900803d14052100c1d19103400054603100c00d1f01903000c8030701d14101c1441da10726106848001e00e0641c0c2c41a4103503400b0f044442c91443e9942200000c51044140092251040c25001000a8002c2d000a40881801031016040d101307110701194040308112503c4140d5900d0b19000391f0704030414002010301058035540981250f040c00308140307400241d018002d0007020400c0c15003003814425810384489034401030082c021824080c2c2150360719400d400c009481541c10f40c2000031280303040c1d00c079100b070594007894040f240300c1c490b20340c6801054a0003081c1d0300040b078801610465a000c0c40100301900440c1ca40b000000c0c0c510782c40c8811100f00703070840d5003032074030700791 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 426607598 1250 426606348 426606361
    0xf0501020d051906031a0423010507120603031d040605100201090210030e120f0f07050d12061202060912010213030606060c02010909020d1104060309261207111501031a 74
    0x390500e8104488642030900c6c0e40382e51078001c42002c2c0003020140b442030705c81300f44101e0090640056006016070740d00d40914183c085031038802c80300c0d1407100074046050000803480c0c800f00f43c520103807a050001c0c8001015075540001c0780040700d00d1110500113035034510202d0b045181c220445910026180f42c03c00921000101e50b907541c0c8117550144000c1000484c0080c100303110402183d80c01c20307000d500c2036126401407801c50f50307d10001034441d010804010050812800a1040c84115000a2008418910b6540911000380e1000202d01c0d041006442c0c0c2012640090004141d40b03980d0343c0741403100c40e1440c1000350448203190407002c00c02101030b0b08440980e0b4020100d005840c1300c1180103070350716640ea421800a2003807016400c0149008a40000e90b180c042e840800124040c800b030003800400f841c0c0000c014840702101f50400e05043c442141d81403c1104080d6000074181080ca98082081b00502e1501610300d85070509088904014070400c00b9885094502989615070350009081c407a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 426608848 1250 426607598 426607613
    0x70605150603010b0c030d0603080a0f170c07020a0f06080906070504060512060f0a0b040f0f030c031e0f0c050f030f0604120905060c07080d11030a0c0f0501020d05190603 75
    0x604c105540b020001c42d1401031a0424000c03135071103840100301000815602c0c50172006c04d0b00300b5040c85012400400d03141c402c07540a5130f540c1c403004400c02c2180c10a99100d00c00900b150304102c500f80d80040d1444800300d025900c20203144050201d036202e000c200c1ca00306a0b1203142080043c10741c41003000901042218a800100750380035140b600c1103251440d034400d030104201058131038015612420b003600014016952000800680c0c62495204a5031510b03000400e6454a85100c01800119100420004104807644002010303075840c0380c003001c6c2407040d118040600b10002c1c05881d038075a00300040140c0e01c1c4c80096130300c214100398058104507002050080c0c450000501c043c0000d0303d0752009002d41c0c1e204541c1074001d800700424070b50310b600514401540d20240c41c0551a400e1045a03506500d29006101c0c01141d04444801980b804c0d150803400c03150102c4e801d00840e28410300304514400184280084d10304001c448000280601d824184412120b40d400c08010350a482d0140500125404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 426610098 1250 426608848 426608851
    0x1006020307110f1c030e03070501110601120501020c16090f27020a17241003060f02040528061b08071401020c06040512030f0a0c0c0b010803070605150603 68
    0x8a43c0e08a8004420003c03d0054012030b9003500860300c0c800d80d50041603000784129030b441c07a041c0c00300e4a850f80c64400641300007916501c200c003180e01200040004000b0840840481e0b0b115070000350420303504050151030300c1c5903024003052040300440e051001c1490340c800c400014565030014082c100207034842d031455064000200e00d503507107102002c0c0255121070100000074280b1040d41390a81210000060f150421841b0000d041001785010412048000071001e000f0480c01402d052014556641c1b407000300300000280c54801e400780300c0005c082d0345076040031135601081d40850f10320141c1c20030046401429a003220081c0104403c0d0381c1c0036410b403050805402580038110030748d10402424909400042000d003018250b000080c000340c00d01d4003042060041e88148112001c1c03200d69204190580421280000c001c454900000d0f1829200e030482e44000b081c1e070408080042c8151616500400c0903002000303158400685c401c2081294030825601c5500103440f21105d540c16000240380303100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 426611348 1250 426610098 426610133
    0x304180212150111060709090608010b2107260105070201060f09020d06120501020a090e0712110d060b0c0705120606010806011214040b0a0b012a050303010e1006020307 74
    0x4881902c202a4090301403100c0b801c8805040b90301070b2038840300050405141c0c2c01912a13070f9041040025030100c0c14012100b80c00c500500381106900310b00100080707000343e900346101c2c0b403080a00000e603103911050305884d0701d035101000511040b9010191070035681d000d003140045a14102d42082400350359899041a40c2c2405000740e030740d000c0191004068140d42d049182245c8004251034100401540105a03140c10742c1c5840c03c06c02c0d0740f450300c07040160041700c60b54041400040000311040680c1c0c001d0005015641c01d440c10140301c0540c072030880f000c0e904401c005600c0040c00701d045070030401c4032030000d1004a0b6102d4020500100180c0c581c440030f45507038107204401010400c42c0c0c2c05a105a002c108180307408104491100420f0224240f060f18281ca00340c61020205010038003501808200440c1078490340309449060009103001191000c0c0380e010420422003000000c1e500380000d50007014030550040b0b1034200304405a40070811035105006551041108c40c000986150040d2062034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 426612598 1250 426611348 426611371
    0x6060f0907080f15090a06060206060303041211150c070501020f0313090b030a02030d050406030f0504020306130821010e060a0807141503011d0f01080a020904051e0304180212 77
    0x4603103150310304800c0c0114002c19407280e1710400704050500c13554001001c440d103e80c200e82c401c0d10b41800303154481c4510f0180752410307100e118628001c00d1002003e5544190050900c0501160030140c150643e003042002d41015080508100125a41003000c040707820002d0000d1450025946601c60450742d25203d0200d40c3d03611111300e000d00341c0c0c003401014540340d0003a064a1904400000042a5034028003d039801f09180c4102d81c140701c1418468244500c2d400342c0213000c241c81e43c50f021140c201d0050303000c40320481c00700081400000d01c41d00206c480500015500c1d12541800214035440c0f1000b0100341c000c0c181d038003042044d85c5001840404031409076820111501c201c002280700c215410480b00560940000006441d2007000111000b4a4030b802c08902c103500e444402c90f071200c2083c40755106540c8450705400151030068100303900284510300700d0700c030800aa414002079921428180d8800d800200d0100303c1c018101c004024070103c440e504620f0b01c1c4000031034100424000e021f000324007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 426613848 1250 426612598 426612601
    0xf0708030f090f1b030106210b0a02030103020d0f2307030b090307080a1409031b01020f010b030304230a0e09100209010c0b04020102010e161e05030705010311160506060f0907080f 79
    0x1505d0030740c070481c06054208800f03000700d840c01e00221b600044800c402c031895000c21001801503040d0780f00f900d042e264011f00c90117004d990341d200d404030080700623401d0350b1810f000894994245054000c240e405048440a0400c040c594180030100c0c80000700b103d80241c02c00c121910024440a0494000344224140f90b100c00010706c140d00254082c402e986501403180c6552150804078907840c0d010f800c1026421141070448a150550a950b43c050500741c01d940140810b008145405114041608000d5000c0c4031080c6004d000aa13080340a900113041179910b4418800c1c11001440b60800c0d00700c0090f0300350b20746081500000c0c4442c0062402510f4000d0510109046a00c00c0d08111201010001101c0c032900301d1101610440300700703110714160400700301409050003040e409102c0c112540140985251490b044c01075015000d03d540001d01090f04008514000701c61511840d42d0300d00901c0104803a10305503050000382081c0300010742c800c5499004100b01c46a00c820070175170008003a00c2e0110035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 426615098 1250 426613848 426613903
    0x1e0507051204060b0f011707050a02030702130f18050c061804051602070510021216020904050601090f0608061b040801110c010c1b060c050f0708030f090f 68
    0x940c01040c1c051001006440e09110900c0015000900d400108507201a2004004001958080180c900700484540c00d44006051140103e024009104c41e43c010303131349005c040780d00051891402815506504ea551075230070000351000e100e5006c02c0d0504a8070b40124140b2070319051f944030388002c4111700c619000101210654511519080c0300c00c1e01400a002d1411700100045400c3c0d50350f10a007005100b44000002c0c1840c007160901e12701071003500a07000c1c0701c070500042911944884a03840803003110320000c0005880c0c016000c1d11644c066405402c085d4102101101503551006080048508000c0103002c0260003040d85600700359400225514004d468405500c18000ca5000300c6043d4a400d20116100d80000700805580115a00030045210b03400003d880c801000d40b45202c00c0101d1060100015603030f43d20950690402d400d10750b080442810306002d4640c020344048a06000c048103100040810300c2c1072507000351000703010345280d080c482030b5583c2e100e0940c144040020100141e4602e07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 426616348 1250 426615098 426615107
    0xb041d10091505041109010807180504110f0f0d061a090409060b0604060509090a02251a01141e28030b0901091b03080723100b0f041e0507 61
    0x108000740045c84000e000c200545071a400c2110030380d021130070004c00200c07403611804280000400d04020741001030b0610040c40020035031110760000000d001c10040c100c0003080c01c040c01c001105000340c0e958400400130f66005403203c582c0081200082032040b0711420307a483c0180d031071800c000d550010b072002c0d850602e0b4015282c0c003045240c01000009010a03c5a44140100540b500564003c40181c0b203541805089100e5401d42022801e400005010300c2c3c43c1c3d00310714482190041440c1e010300101b007524800e2440e000e0303104820846116500040d2420912889540310010400c0c0c11241030110010404240101005220390300d18142d11980e54100703a4800702c00355800c500b980c05e0074074004d41c1660003825080c07030903204500324861031038110401401c082d095950085c2e52505150190307883c0801c04882146144288205140401c502d0504020140c9400d18028020921540d02400d2101c040c190183c514015800d011451000c13990a544420001a447c1d000207070950b140740f030458 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 426617598 1250 426616348 426616391
    0x809100c020a020d0809011409030d03110c061303080108030703020714240306040522020402030a140412110d05030c1b0d0809010507030b09041101090f0b041d1009 72
    0x80d44400d0500b00e0134140031844003e4240000282c0b194119032034110f00e030410358040d1003071503513150b030120240394020b47c0309401070b040f0284007485c00c50900308594070f01820841c049860b5800f0b020044088000c1c1540401d1007401008040042c41c903240541d10000d4890f041405189441082025080002e48a1468003440786c41d0180c07640c40086039041c80c0c1e081d190720031303984c0600c524106004103103410040c801c0d040003403c2c01d443d2403080c001c06600b07010103504010203403583e0320345e180d030924a1408881c032090b210702e11900a00c1521340403918043c000b0044902c1e0128603034030070500c1e420795941010441e07800a0f006240e03203031100300c141c60760079103c2d003482d04845142c000e5810800145402c026610701801c1104024409951601c008a0841c0d144851a0741d1040006002c50042800341d40191109034040c9025648642c540c1e45008440c5485e5115a09103940050304000009006441002a12064a04414a042036040311814001034020014641c1c0c0d208511020b100d0000b102d0f8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 426618705 1107 426617598 426617603
    0x3d050d0905070f08160324050a0905011401050f120a06021c2003010b090d0b090c0307050901030c0b0f1905180d0309090f0603050a210809100c020a 65
    0xc0028030801ca00c003030350081f030880e404032840451402a1032042210300c0c0d0100d014045e52409908542c0f02168030414000403200610155031012081c0d81040c3d4101d40d002403000b2080310007402c041c003c2c00e0040c0910710001da00c008040c0800c1c0d0f0202c0e5480b80303a80400c000702c00c3d4069480100c2d400d0103000c08003101000184101c0340088040c0c0a4010054240d26546d91140d8424903101c4003074405090030780c031000184503145020841340d0080c29080e2802c02c0503515580d202c04814040c0d000f00001c0860200f4103121b0844c20101f940c1d2521031291200056140340342010b45550701c14003484441003000240c1401b542000c031840c0500d00c0e070607900c0c0c40034103160500ca10010007820b80c90607012910f170600080450b00030068001c06900544031442e8018403c4030450020841529410501c0300702e20406c000504042400030342e107081160b012070315095581e0120300703140408000 = true := by decide +kernel

theorem cover : BRFrame.Cov 426438848 426618705 := by
  have h0 := BRFrame.cov_init 426438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 426438848 ≤ n) (h2 : n < 426618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
