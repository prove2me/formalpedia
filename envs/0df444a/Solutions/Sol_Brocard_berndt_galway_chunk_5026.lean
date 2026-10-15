-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5026
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:30:20.668012+00:00
-- url     : https://prove2.me/submissions/6d6326d2-8d45-4e7f-b5a6-9b73dd11b420

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 903776978 ≤ n < 903956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 903778228 1250 903776978 903776989
    0xe3307051608281e05030706090308090d1b030e03210405010801091e110c0613050c1e1e030f0c13090b042a031104050c0a2c0402130f05 60
    0xc0786412501e00c040a15140d04c0c2c0c45001c0d50010402c55082c0020482030000035401c0c41a07400b00d50080d501d80503d89000f00c80e043c40c0c1b8103081c000e0f07828041003c58000d4601d06251006003410f91524212000e503221401081c42c002202100010740100c1c00e0020303019044020103807040326001d0ba00c80303140fa660382e500181207501d00c9500541480f00d502400c2c010303002039005120004510507942c1d14000710618528144141524003080400c8000303400e106000c020006a61205003c94581844500140442011040d815042c0b8010120b0300401074456540c1c11051100e44006400c0d11084588100710544a02224031414070603200ba020040f400310301d078810700282c6644a0490b24594a940d02c8440c1e14a44503808004c8821000200c152340c0a20050790030001c0d8803610301c258101034060100710540704014404010190306010034003016900000740c54010303000340e4080000c4500c01340f0704041c000d02c1200b81070b046030000031400000000c0305600002c6403450581c80c4e41090f1a14200036 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 903779478 1250 903778228 903778303
    0x303020f01150803072a0e060f0111101503020a03060b131808032208030403020d0e0f0907031b09090f2016050a030e3307051608 57
    0x220f1070362040c0b211030002040b1602d0950080c960240c14080f1449207481c9610111042e00841109900c3d00113003c005c3c01d09100c949113208090034100d0b964004000c806941d5001d40c0180c802c882d8903603403805211002e501055002d140c0182c807020380c107a200d05203c80a4106a20050700401d050080112003034030a20401100c90781c0c0300300407140203c0a495500071600040c11520188401e10a04003205c45010741c070800c1203210310311460302d034901420064203201d000150801802100580400a50b40d0507413a800207100c00c0303610880540324408205c00400001040045246000d03001c212115000701c80c020448a81c2e11046c082840082e0914003034841d0b0801080161411546107940d115201d4040c000c1c05103096590f420800861b200c003894200b4010b0241c000c0341e19070b046180706080c081c00b00b100b440342005407001e608801840035001ca4040d80e50f2401e40f4040803502908004c401d02040316060003603120080030a031600c1103035880d550350042d541000308107969034003647c0000b001c540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 903780728 1250 903779478 903779489
    0x15030f06010905370e010614071509081b0c0a060504080c01030507050f120a0b041404060c0c1a0132040b04140f04060501060e060708130f0303020f0115 67
    0x80c800c41151141300a84d180180503420940e806110480d40341c0e8010020784010001130440e121030754540036001d01003100c0b03452140fa52440c20000388011030707401c0784003c035000d644040000b5102540c4c28500c0450090801070394601e10000c520214101c000a541c00300b440c42242e210b0ba0441c2e40d540c081e00e10344910701c14070203241c0020340625029806540220380c00061800d00a00e0416484140c500d1035010320360080303014620806000c07442d800b5204d108004c04060700c003000203001e5840002e05214004200a03c0c45448070b5000200a22801c080b180303140d071258820700d041e034a03902c6602071900300f40140300d03058500302308a12140c00c10103140c88003d03c448000c030703400940c4481440090004050b11a4002d5160b507000844c60700e510340000d01c5110141108034150400c0d1400009030f80060f445801000000044900d01f691000c040b0b0b51a01e07400780100e55074681c64400701200500305d601410052080003400004d050f004101c0c0354550b0b0710603000b008142c0c51401c1280d00341c000c0307000e513 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 903781978 1250 903780728 903780739
    0x50c0112090b27060a020d1107030507110604090608011e0623031e0303070e0102060717100905040b0a061a0435010e06092b0306030215030f06010905 66
    0x410140a1100c1014180b0520b12030040d148840c101543e034a044401d607103021590f980040c2c0000c0c40c801e03038440c41c001c030344040007440e180c69855103000b4614090850060103102c0c08222021059541d0011103000b80013542c030600c0340c0b55031801664020075070001d080c0d00141c1c10407100b41c0f20b03040342c0c450102980d903481d025401280c5100a400980380c0124681d0350148548010218102c0c142c500c0c001c8002c0c0841c000b1a030b40d00d0208001046503004030040d0303065501c20f100b0b01241c41c0c1c0004400c0c3c0042505010852143e071809031500041400c2c0e030000915900c2c1105120500c110104501c0c8692030005040c40401c4d42e614503c9202507d15003556100b540c240820700080381d000ca035500b0700ca0544519120f0102000f41d01e00000343d8140d1800300075a41d034903040460030109201061b80004000b002c2c0140e0503084410303a41211200900c0110350f22a6134801164a0007940854007554018001404d845181114568507520554000300e0190b01d20000462a611480c684c0c8143d402c0a0312 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 903783228 1250 903781978 903781981
    0x30e210a1a0c070326160f080c03011e030804260c0108060409020d05120a030e03190c020a0905040308060f0904030e040e0a050f10200403111507050c0112090b 70
    0x1822174042d600d07048404614085068040c07101d2881022040c000c0d600403040c0c2070307108001d400240c262442d0b403480c103040c810540304100e407811418007030f01e0460700e1003075100c0c080780b45100d4280e1400030300b90002080e00d080864049020303d6030a040208044c082108001034501a070f51456440c0301000c90940007440400014001d401c094106032191803000d0406440c031619552600c2c01c10001803c002012000410042070761545406110310400c10032010318075094540f104075482001d181d5003802071084246504046460700700c0d0400007081c249030300f00001e050a140061900b00140c60042c86500c040a44007000d1614030f4000d801540d0585580907490306100030720016081940850095000380840c0d1404282d0500c0306100040e61003000d06820b52020f0851411141070444080d041d410000c070402480c083d002c126401e582e0060707440903001c8032800004d14000c02a010241d1000f0700401d000040101c00a92107501c00e1098036019140b004094494040301c1c142e00780079007168071440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 903784478 1250 903783228 903783233
    0x70b0103081305040e0c010e0109030507151106091006090b0303030a050a020c12190908030d05040c0504110703080708060105090f210d080907030f030e210a1a0c07 72
    0x100810740e0a50030b048604840d03545a00040c2194681c52544180b0781088020364410f40e8814030010500109003001100c00e82103480d06951034069000703208880714542a0503115900440c046000c0202500459045280ca8250300d0b4270f130302c51500010049800c241c00800e840c85240114410300f100070340110304541d0340015a00103042d02411040c102a404c00010082540a0082c070030042c01d00b080c15607680400341580e0f01200e0010010404202180505010800d0040215206041c84400c085401c0c2c613182400c11003c02507070301c041d40c09860000c1c005803690903c000f41c26240d01907111201a0b556001c4182c46501d41182d207a40041c03c20021080f2394a081d0580a06101015180e002c2214904110b4106814808071900d0580c0c0b01d1141880c40617030240076680c0c030002540250643c1442d582d100c100e0319402440c01410f00214880626481c0c40743c80b038a950034800b8425020f0b95280c074880d0252600c8142209651145001101440150305008154043c03200b803088241b4225064 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 903785728 1250 903784478 903784493
    0xc08071505090f10030207170712050a05130303120c0f0905190e0103080301180204060e01112506021b1003020a0215040503090406090513060b0604120b100605070b0103 74
    0x2507070441e03000c400d0080c0c0508584400d85134245410f15910010390342c04160906680710002c0f101c0d81000500200201d1000035080140b450040c04503080c41a00d039039000500ba51180035189132410481000d080c0001810751002304180840e02c01c002c10455054240741c00c442006a41c6005004200201010052030410b00281e403902c915078074500d106543c80b0140d20120000070382c020b0f2584440840107024842d5090080041c00c43e140608529083c505039014003800001c0d0719003414071032a2298140080028000c80d1485091004a5480450740595031101c0ac4160300506e801031040002505c2ea201445a0103000300d01d00414401401c06a0354084000c0d6105aa0643c118010f0400c0c103450301d0025441e81d0701451042010b1a21031444070140f00495801e0b91290150030705003000e0000320503041c0c85042482e41c0051000c2000038108020408512071a44030620703818000300000240140030102c40c0c050295405a807031460b03603d92040b1403a010b502e10103000d29140400400001e00074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 903786978 1250 903785728 903785737
    0xc07030e100c060e0f07080f07092703030e0f070b070b07171305010b010c15050403020f0a030509040c2f070504021206010f1d060912010c0c0c08071505 67
    0x2e00d0100c00307018007a50750b101500c600c110b400e10035600c0746001c0d0111650074480715015003c600010315091812410040d80c0f400c1d1072241d544810340d21900700c3e151102c000403d05a0a05010800e003a100d12450003d00418828168030504c2c014003182c880e818002286090440300ca04a02d1810300c0143d480c0c031078041d00003925010034000c180407261107240c03418020314440d044150b012054413040742401801e41d81540e80042c100500008450006451289201584000d01070300140035522490f05928011880203450098803c2c1d006080070035501c58001c001e504002da60900003402c0300d030303000da45407103100c076100c85043c241060651110340d02007001c40382d070070112088980c504e903100042404c03030380300e490f01200600744801041400c0d40c0150b06500e0032101d03031901019083c644042400419480300325144100000101c03e07520340c0c1c078441c1041d9403854420003002641d0381040050241c43e6000c0c0b085420042d000c01c002202c21012881c07030111014000c4c0d0700380b4400d020200301d40c0b40d0700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 903788228 1250 903786978 903787009
    0x402040b040e0a090c03051f0605060304030f0306210203010e06060303161a07030c1e140c0307140309011b050d08040221030405040b060705070b130b030709030b0c07030e 75
    0x82e44c14004010810500200e0003c0d030181014146041c04204441d00c02070103244c0451205041410030489270300d41000300e0b81c0c4240c15142a400c03860750744008802402c445e07402260740300c40001d00c620384841c64000d4280002e03c220000c000034210070b5441600c403442100c4440e4150428000300c00d803110307000b11071010107109910120700790320005205d5401c80815120b0740c000a03620707103400300450f17003140d4000e140d060131030b014222030256100c1c0206000711504280381d55000200b42580c42010410644422960001241c481d58000003a00c0303549820412546000900d0607031072410b0300d604066020251608000941b0f25410f14200603034050300081d01c200d030444601005030020b1081d10000c0f882444840010b507a40e9488c0000300016110540000d0f031280600308650300001d0030010300e01c0203e40b40010711070f4442c0c01c1910805102180d65000e882c1d080c0000041112444c2d0004020b400d680c8110b074048440e4956140e00c10190103005401070128005841c1030030345c0d24204104154491 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 903789478 1250 903788228 903788231
    0xe0d020d02151b0a0b01120f02060a180b070b0705041d15041505360a180b090106060504050d140f030a030506032e090602041a0909060402040b040e0a 66
    0x440020f209440c075a2805103081032034000650410821101c00030050041c0081150100452880d417602c80780c0303c14408009106240010310160308501584006c2801c021508100c0e80c159540d1940b00c00650100500b10b500c1c104690004000501880076242980c154070b8060b0908500302028070509a03003c0c2001c1846d490f43c1c1042c08803030703841e07024031148407a141d01080300d034604c0d00f0300340008400d0156410042100303049084441c26480410f08504006400f403041940d00c42241d0351004124511044450852000450013400a5202c41c00d0045032510300801c012030b9240700444003805280a2990702104525403a004986442c100900e01ca1042e81074900e0714840145181c81d69101c0e4900d4008680c490042109914050005c2a5055600e44051060322499440360000c00f04001a052103540d0303032040300080c094a503055030302401e011540343d25a4110500f1500e007030303040081300f5441454590001501c0741824003c3e41e00f1103409030845030809083c244080c0f07810000501c0715000d207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 903790728 1250 903789478 903789487
    0xf0b31060f02030c07060f06060f0c020f030d020303040b101a030603011d210306330703080919031b0201030b04090f030f02010c0f110f07060f0e0d020d0215 69
    0x24003644000c1d4020131070204115034440c41032500400343c0341e40d0075809240b503203018002c104040d00100758518040e450b1900aa2a451920008071440c902d004440c3d054800c0c034082140c45500080294002c0340648034500590391002030b14240e0080a0050079144522741c440f11421107189405107411560040004c50b030103081508041c44041c11400070840c5500001c0580c40b000e04051210506508200b401440c524001000c1004402284041c0004583d00c5204c8841c003e51044003004200c001e1000307070350712002400e001780251809e0701c28080d203004034942686200c02d49400c10a034290307da01c544881c0b58154042c1003581c0303d45542a8145030b00c2c0c5c01c1343c4401b5582e52040300b40d454403500c01c0006040c02410010802110071490106580c90040b0109105811100180c40c900d2203142c0903410786003e4400e1401d00402d1000a081072182c0840440c807141c02561070b140075641a030769075850700800c108100c038070301804030042d410a851000c440054203103400010480e0f50440d460314a030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 903791978 1250 903790728 903790751
    0x4020d141e0c0f04060506030402190911190206090d0e040609020403140607090b04030807030e0319020f041a1e09040309031b050f0108040c0801090f0b3106 69
    0x811502031144003690004034041d02c2501e014600024500c0d030a80d4100002820300c2e0119215203c081e1019200f02c1c11030407084100c1035103140795005001070403802c1c440400c6141e114040350308051b0b180c22401503085042401701d071000031007502c0341c03031010000c00604c94050400d403000c10788100b81582180e01d646000c958001c1900041009612502100000ca6401d11a072410000094490010841c3e240010403008038150150f400f586d4226003070903690740c0c04c0d103015101d044c4651061fa03014000d5038080311410701d1036504c810603180240c07191840780415104120485003120282100d40c3c05115074030382c950900010010001d1102c0c1b0350303042c030b21231440c0000e24900001c4800720300007446210240b04101d448120041b01c003400f0000d813080541040000340c004841103078114100300c0080c00240500000309016802443c2010003040944c070b071810244107003640b401e000c0c0c507036a40c05d070042000c1800c03950b0b0544400e0a81d08904d0807404030400a01c0003002d400c0d03410340e0801d8484400103403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 903793228 1250 903791978 903792013
    0x7051009030e06120103060c112e0908130b1911191407080106030c03080310180c110f0a0f0614270c03071703120703150e04020d14 58
    0x191038401113040e030603907241d803a001064a9444803401c08014100c018800100e00000f001340801c1c01070024402c1d601d071000c3c900413a40200c50101a00603007400341306014005007400404028040c02e1400c0c841c0c1d515858808c426200b2240d010030000e4030002080003141c4503041002201c403c0c0710540b65809200341d113240ea40f02d0800000d460440032041d070241c2c480010030401c00100000d90081c0040c520b10b4440e40aa55020f1001038034802c000030004041c81f1a804035040078001e2108950310200403100942e0081c03400003803141c081006488800c41c04480020300050780002800240311050003a41c414040d861062400c82d80780303031192882c40c50384520301020b0348a00509040b074800070344c10480c02c3e030b108002c41158240756004124100c0454030041004e07011f4400a0a90302c0740702200403c902c1c514032400d007180c5480f03551030013406a02d81d07040e004205180d2812400c403548617110000d20044100070760f0000e42c000b0540d41045c1c0060341405041c4440c07200c030010390300382e41d5140d1503424 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 903794478 1250 903793228 903793237
    0x110313170c0303011e050307090f09060606120b09040c050d140f0d140c070b0a140409061a120a09030509030a030e040e0f030301050d02030304050d060506130207051009030e06 77
    0x403054101000610142100035a822030039210241ca007045d0a02e44804a03440395500e000b6514800d80300c1190205441c81c50b004000102c0c1e00c54420082c0951740c640051520a10030707150881c0c03d003808000300d042d28000c40300328015600812807280c110710f010100720000500000890b08403070080c8000062000502c21281441e45a201501c1d4146816100a1808440760307011800a5418004144a5100012054161101c141802d0740c0c41c28840000d503840501096518012100010041142e64103034200100305c440030091409190b010807681e044501921820404041c842d41c009040d607110380e000700c00b0081c00707410110328010301040401e00b040024041035011030140006400700c2d05161150b50002100030b4050400b080c0d00400301500c034441171042c42c1c8183c50168200c0d05541e0140212030080c1702c001e101000c00394240c508040a001c04640d014800c0e003010340c850000070007a000f107401083c1c0c405d0140c2030210f10064044000c0203040e005904014900f10640065107400f001403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 903795728 1250 903794478 903794497
    0x9101a03011d150f01051e090a0609030302030f0a120f1d0304050d0b09120a110d020604030e1309020a180e0c03030306060307050d0213050f0411031317 67
    0x5540da6041054454200c0c81810036450300710284010003d5203074640c80c190040003002c54160501011000049031030b401110045112883e1030810803500c3c40c2200020001e000080d5000101c246ea1a03000340d84441c48e5100c0a00960000c0142e4004402c0c82002004105201c3c14403c501e030f41500003410444d01503840980c0a03a40d0f802800720880c2c0e0080c290300c1c12103903501c011440c3c90304040100d110700000f4607000b0200092a40421070000e0180840f0550440d40040280c46415455004107403130080407203000c1c540034080c1440802403010130240c0c46075405407a00c0300c00515250a00a1458a116218401a544032691401a40c90007008801450404c43c02104800d400d0090422240744030341344006033340700700c143d503e00da00d01000b9280e2010046408945031b50356006d0580d9103128281807660402c0c40050050074001500c0d940c036042c3c8070262490031000160b0802e1108640c0344500c504070380c0307030f040c40000e564101c6050100c210074862250807480300c1400c0e207140129041440c02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 903796978 1250 903795728 903795779
    0x110a32040909030305280f020c010c1e090e07120b0904112704060e070812040603060905240f0301092001020a0b0f04061805010f06080a020f0910 64
    0xb0360207050b41809942d40102d2a040801100d00580030449000340e40c00ca801d1007810f44609000c440d001041d41035402d2038001c50b00a00203142240070080c072024800c070f041c40c5203c2111004500301407081c0c001e20140e4070291005240d07a152408182d581c410070070140010076480d501112151348410302818040c51040c141c1100c02c01c40300d0200140007814050046983c08429010f01380c0c40103d1103207a4016400c00c4d0f0014000140500030350030b00340180c0240300c051040d00392030708160312158020000c4601c0d956080001a8440c001c24040d220140d4007600400211030010410002c264201d4502c0800102445140d4003d5001309080d212080c50640f816562030f030001082e140c2407176015812060902c050007103902d0f540d03985000c000740944412243c3c600240010204202688400c000344110050a0010032151602502819484410b16070450500100049181c000100e4068185d4002d10004030014000c0501620702c0c0c00070060b040401c0020800035120010700d020b01c0d003840c0030156 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 903798228 1250 903796978 903796991
    0x31b05040e100b0a09061b05060c0f0403080705060601030b010f02210409060f090f0c0903170d050a090c05041104030303020d1103070f111501031b0503031804110a320409 75
    0x1b0140c0341c24501c0b00000ca44150445414000a0001c61070396802045014515181d02c482842c001c030b80c0c050b54000400380240000c201d02070000c002a41407040717000742e03000e00440340c1e020700440f030303c00200380039a0150307015000504c84101240c00c030011168823010002d0034147d0f1015440155a2258024825549501c8040c40804401d00401c00c021500b40800d001c11001408024095042440098441d001d078140b24900d181d0004216036061075064014412402d20f40d400310018515408200c9002110010020f02814076019401140c900c43c020a03040ca469924107030040c0d0b0001c80700080c120f90b120303581140c1440c510003540c003485541c2d03104154154298000b6100c0680e000c0b0101c8180d1040075024180802c0b018182d05503a8410290104100050000708101800b50402d65040c0030229040d07550034510708030b0400f0f51270b044509118105000c01e80c54841e115031070380c400010f403404807460b00c0a45131010a4a03003100c2c018404228031131700540c0402a070815080350380032a07203885 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 903799478 1250 903798228 903798239
    0x61b2a01020c030a050d050f120f180c03120d060512210c060a0e0c030601090e160b030f041703040b041502090a03060c2706031b05040e100b0a09 64
    0x10702c4070465001d80c000c0c4190096a1a0b1a582d5041002c50004202000900310010568030007543c1001280046011040c10100d180280100044441c090000002c0c40902c82c10000010041c03c040b03005000790a071200f5040b0303003100d29880507407a480c00c1c0c0d448141c00107003919507050402d90007484401901046121040c05070519028031501a1500000e10004e00840800f10750207402c11844040081c142c0c92996105051104c183c824541c58094100001031296183c1c10a00d4000e4030ba005444441008440030040804d05000320280054180001501000700d0710785144c0083c0102c450310700881c14000c401c1c50a61088404480d0b1051107018030080083c802c949524142d000902541001803002c0443c5140b41984006442030f511040c50f140044c1c080c0d03404d110041400d0540c00502c1d107800790300210103c007900c40c0e040004d2030141d0400ea40d0705440105408441265900d9182501c1c0543c030400000014080c800d59180007100003c40030a03020003451050550b403a40c80c0c4003840c28 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 903800728 1250 903799478 903799483
    0x9011704060b031c1b141e0705060a020c150f0c0d0206061e01120f09081e0403020108010e07030605130b12061603021b010c0207180b061b2a0102 64
    0x1140c0d82e100388404d1028894905400610410850403e50100c10b6980301c1400c2060603540759017181c0080c3c0c0941c2c6440303100448244000c004601c001e03000c032910a46c0e10410320070103100381c0f036000300180c0094001c8209860510480d03241c413030710101c0550030b00442001045450f4040d201004159210307421a01016405002095100008582080b1144c10040540302c0d0220f999804504001100c488440c28068940c8840c0300d100b40302004004000352840d1852a9a02903402205003281c4c1d2546441d4146403081201c0549506944560940c0d283c0b607200038031032402608960902d0780310034000c41c203a2982c076070f6600c080414403801300d11034505030240f140003101040940d503e50050020481039801003020501d41200b6460016503031442074004041c0c11394100c5010449500305401c02d9035145d03002405000f030302e6440d000524103949040300d07401103a2010307000c503811203001d1001005400c200441402121842019211035054a5000845004040d2042241e0010b004450100355904 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 903801978 1250 903800728 903800743
    0x605030117071d09160f050909011107080a0c080d1e050c031305120406036312020d171305071206390509011704060b03 53
    0x7410060440b16003030050f8115901c4081c4124254002d190300418083c90342003080d0340d666406601d05002980c0c441802103c00e01d098400c0394802c61014001c80d0080070107104010714140089a482d180540319690404076070080d2110206000b02d158900c00411844c4004002100c01040005a14406d420701c0c528801141170724103a50901d00b80411511007482030880e60405860b00003844041030a02e01140750021500c581c240202011500050554142c0c004035410f5400740540c7c19841c121150000c04a05c83d401542002044100300310741c080c40d008800300110070086040380c03100c0d00124901044a540c44411100340c103040581550b081d80c180002c292801c0701d46001c610381c68640400381010301c4003400003021a0800083d101c10000100004401801803260030b0b0301c0650103003083c400a12940c0702c0051032044200e40309001041500741800c10f0560703920500008445104100c515070403e84156050103204000c3b41b0201e041b548900c1d204500c00d110109000c002c007410b041c20580d0f03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 903803228 1250 903801978 903802019
    0x1050c072003070512010617010504050120040603020d14160905010f0c02040507050403020d140d0806010f03050901390c0b0c0d090803070c0b0f090c090406021306050301 75
    0x1c1d0440304880c540d0300800c042d812240e080758016042d8030542c0d50640113040310350004002e1189000d501460031410741040340301c0c44c003880003045429850544003000341c00001c000503940c00c0400040c000903019074040e00090018110004400012104001c8614401d42c0d03040a03a02c48203030075000d0680e1040d40c0401918081c603020300c4107841d20f0006401800100302c001c0c803840d120350000b41d41034070802c01d075001581c000307101c02e08400303190409c2d0451818201d01240031b0302071980e01d1202103005400d00e45c0039000696803004070282600003200141005015943d20b0754031154015480c41c001c034000d06200c10701400d4520a280110300036811600b151000800380b240c1c42400310040340340210a940e20006482c04c4c04e650b00c5001088200410000c0d000411011021003440700240c6d00044801d40da500c640125109610b40c0c550040c0d006104540010241c0d1024211000034240b61001941091065402504103050745500180350b0800f41c000100054022004028003103610461155086 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 903804478 1250 903803228 903803273
    0x3090a0f06021002070f0203160e01050f0d060b010c0803010b2106030a03081f0f05040e0c0a050f0114030a1410050607110105090d080405120f0d140c01050c07 70
    0x1440e000780651109003540118a1960f03000c41c000c8203002c030700940c1341142c903170007400d84026046503910b140c8094402e004540740344214a0001c2201c0c10401c228001204000341119003241c903554a0002501d80d4059090411165008810010360b40901a60103855101d411385d03210f115039a219408000003109154040100340b0612040351000301d400f0b0b140c0e940500d010301250b030360311440240001c625801142188010a000a41302c0ca03100d034031106580b0200c4090100080d0100b010340da96404c1202a944680501c134204842c1c0b41210130300c4040a03041c14180c083d4040304031690300300d0700125014034020340c41e0360000c0e840c1e2802a61303a0f40d1210b4842440ba00c502d041001090300e5010702c80c0010141c030310103240c201d585da002e8400e0f40c40f07001005041e04107200080c41d000d07406401c50300c02c04e03005d0441003105200c00b00b004542082c002e9a01d400820341080320444c03c40302c2414104001861100030007080e0100c41080c09039511034030104a0403640c4e03104900c2e11a422184540b12180c824 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 903805728 1250 903804478 903804509
    0x90c010c0b010b0a17040305090a0b0315060c010f020c0703030806090420040f1b030524040c0c0c08060106090f06080a0b0303090d0f020a080a080d05071e0203090a 72
    0x41c05071040e141561149070645444544c03107070302650070140c81c40089140060f03080030403080590240040c008168261190001c041e624015a07025000684120a0106240e40c0c8120359090241c00341c40914400740020409503d1a080d200407640502d03109405078016600138014190032100c02c580002e000c0d01d1500b4030340782c55201d40c144051690340c0d0510502124602c1d11b05a80c0b260000040e11f08144810855040d841b288290403851804034000403c2c00c14000442035000000700e81c400e900317803481c00115a0307540b00410005200010003402449004601e18005c159070b0b100d404003414801004002c15410080c000d8104541c0d03500103c0d402e40e0102051000542c800c008681101d800a40401d00100c204000390030f40c00750841554104003032051110a00003c0c40b0740e5500740d402070f103c030004540c48152a60f120b424000010340300c60320400010780550000d41c040e90740003103c2e1606031074024900e07154020403842d2005440040c0c4c00850303d01e035580750504000e4010200c3d1998810388 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 903806978 1250 903805728 903805733
    0xf0314030a1d030a121101050c040f0308030901060b04080a050705040c0e010f12020c070e060a08062805010e010915081b1f050318030c0a0b06180f090c010c 69
    0x4482c625104005001403800400076a071010480900000d40c000c3c40d251041011410040c903041d00c260180303c9540c20107000c20200500c800880341a540c946001400700d504544907043e2079800070301146550b66a51000144021328500030340040c1085801925405800d03080003131411105800040c0300d07901d00f041302112030750000d0036828280020300b007000001a0600055030111441c1e5030b101500740c0001000c2e442c12001240000a86400100007200ea440b400240582a044c034040c460440e80f00700003142c041c1c0d00303540d680030040c482441d01c5141d04000c04a04403d5a00c2a4480881c1c0004031740140400b020034026030450041140f040041685000402c03503980030319451024100319482d00c078041703035140c50020340c00380540803090b11001c0800071002026603008441001b540115840c078103092920100440740d001c06400c0007407a00003601d4071914075948019160a6014641400505941003c03540e0181303e6441101d01d801d05252001c02242040449004641000b08209c481c000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 903808228 1250 903806978 903806987
    0x10f0e061002010b03010905031e0903031e0408030403050106050906041503030f1107120506070903110103050a0f09110f06070c0b0307020c0a2c06010f180f0f0314030a 74
    0x51100c0201c40600210208010503401401c0d4200c0142e095402d03d130141c000d100c00000141222950899a60b0b5800c40003070140b030440c05441c00c40d03589034004101c8060108402406c88000c4000c2503034507480c3c251f0354800c482c6154001d60003124165100c82003004103180c140201d41d80f10700107031402d019040300071280701c25211403404010140151400240038841c031030b040340c5020000c00e01c2190310300760311445846021200356004880301e01c10b850004155603c2448840c04503503100d00290100d100304401500a443c00420f0920395541c1c03212118500f48241c09811490340c014003c805002070004140030000810003020780c0030714001c210010004a11050920854405501700c0f0b8a83d113503c40200c1c202908256003650002e18008045058403540c2a004820301543c01d08034004035030095207800c0c6010031210740740480c102c580001a944d00038140070007030f8100080d00707105c015200c043c0c13014414080c0d0400300342c20902c1c0f00e05008020002c10001d004124170320065041c481000e40050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 903809478 1250 903808228 903808231
    0x90e0903221701090b0a0209090a051e0a020a0908011104060507080f0408060a0b010906080c03040f05011109040b0a12020d0602040b0d0c1d01020309041d0a0507030506010f0e 77
    0x240c40c0440e64922403440d01e80d1500141c0a0003100c952a0100c4412031042c9020b098181c2054403400d03c408003151000305103200302c8003c1107010b0100d400c40ea0f6103004100050070000c1426030f4603a00c0d0884056130b200450300f0b4522480c1611030040c1c640400300002803840e0140d0700b149000740c5c034000c090318045084000b560102d07075851a105659905618117000381c0d000e051600010700101150110325440081042031180b14000e0007045a09111401110300300308034460100480c445a022942a42c000f03002142c5c042d000b40100d06107054280d03601c40c02c4450649400718504800b040080e440e14150041c0c500080040383d402e5178aa04120141e40c1600c03066000912541c1006c403203104010766134040d18000c24030080c003d0384444c10134090401070202d07041c4440001d101c0303019980d0701444000f0241d4800c08e06900031070801100800740002400b0591a00782c02c900009112041464100070b091031552091014001c001d15614059140000c1038200d0600307151406d42c1481151a1301240c00e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 903810728 1250 903809478 903809497
    0x302062815120b010527060405090c030a1110031a04090c030827040e0714040e33130602181e030606011403130309051807090e0903 58
    0x640500c0e0740d10484080c411039407000203207000b4100110705004546003414122038003658880c1e05940340700410103024070125402501c03110b02001065040c10180c2c01141e0045042040360b40c40e52060002a10b00540150100c0e18044bc0d080842018144035400c903410251905050004020f0391481d99032051600440f10301681d0b40303200500a01c039984180d00b00954000340394668449103800040c480c291041007400b1541040e20745003056040c64860105110980f4010b4207400742407070045000000a100c010398800c6d22940e40e149294800d00002115a00c003102c10b044070342c00c0c040706500c17115001031002405421b00c4c0030415480246c00c40c0c4003a0a6111100503610518060940c00d07140800c6031080d0040da103a045444041c100714203014441d402207046403001e503100401150391059492030009410030034030214a0912442400a5a252180c2007030002c154403180840d03520030dd81030001c503071612142c4c144031084e5004203540d00505096220b544482c5407103480c01d6500d10810008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 903811978 1250 903810728 903810731
    0x30801030b0705040e0c0307030c0e0306040303090303022203060b010813030507230604020a0e0702070506180603040308040c0905060f10021f060905060303090a17150403080403020628 81
    0x903002c500c110b0444c0c001e403694044103d15070404001032030668004a4411010034900714191034207c0c0a090920290b010080043c48181d0700c0c0e0303038101d0180c8910b82080303052640900440c05483c60003203201428041968204110a2070b506203807081c0d5001c06585810b0150710418131425407210003048042a1301401c1c9075070ba88401f0314200626559401044d20780104140c0d0064a01c3d40c0412024040c900844601d02c4440c1c6032500305a802206440c0e03400981c0c8401410080390401601070301c0d54420b10801214209965000f0a402da401200c04600051182e410001080400d007408005014500c400304030310300c1c0c0180440e08491451036040d00c291003101c004008107208000681e400c039640c000e40e8503200d020509440280c45580034201d03203541858001200f60070008161010880024940c03520319140200c0c100b0f860702000d074203400a014039142007906486951401d4000c82c0320f0341d240704291829003030003414244050a81e01d11000d01e007039046141405000862126400002d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 903813228 1250 903811978 903811981
    0x203071e03080a17010905070225140406030203030403050309090108010623060d1127092e2402060601200708160e01050604030f03260906150d030801030b 68
    0x40c0c4d08240c1c1500d101441a41e280000304486c2c8003500064002e460070307001c607071020100210610308005500605184d041890100700480261646038040458005c1c0001a038180c40707801003400c1d82d000d5003003a07845510000d50441d1130300b0700c82c0c0c243d401014408002c0103641e080207510030040d0241c8502c0121034050f16200480c2d83d032520200e800200c1c0851081100149940c400d40f02034100b40c004106c5000441d45003003251640c448540a1520000c2560080e5981d602d081c01036603008029001001118911260207c1c4609a52802901880c00000c11f16666048684880860000213a086410450070b02500341d80002d804496060f460f2481d40000d001d01c04110b142890b168800c1005100d0902d801583e10051002c100641d5455649000135030380303440a0011a12aa1100402d406880024640420300c0752107090b07081d84156450041603112240c05040c1c00e94245e5442242d501701c02d0a00411001829249400c030300195199000070041d9100034281c020140b02c0580700010450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 903814478 1250 903813228 903813247
    0xd02070504051e0406050121031b0f140a15020c10051f0303170a0504021c060209040203150109060f050708131208031f18200c0102070203071e0308 65
    0x1c0395080501c90f071030f03141040d031030507003490b0380684028818041000f8001055100d00d1492100c0d8070308141e01030b218810018050121001c88158040c01507a03c0300c4c40119200004654500030201100300c20000c003210411414403100703560b420320120240d0f174030400024024a00214000da030640144800046a50310300501c0c0903012039103441c22001000c0420013104050301301e04001080340001281d07924564800d00321008036101610042e5010036260055030f040c0300d146181c0b9036490320a60000d400c201054000c078007660402d8800001c070b59000c1140d8032065034020108001010320b0301d0301d440c80d2462004050041d206411002e080040001801413a0140e0340c2ca0501c0202564409901901c850742400c0fa500c1d002904e1450501708205400107000810070002c409981280c5416803d403040f01d19200024001c1040792009000703245024000324030443c0c064000231104900140c1ea03601e0900c109814000319400007510740c0301c05103900d000c0b010824403034400d4a901c080d800703a6404e040c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 903815728 1250 903814478 903814501
    0x90f05280b0106120e030f0a1706180a0222030b0708010b0301051306050306010f080d0f022a0a090606020d0309110f0102031620010806030a03081801090b090f0d0207050405 76
    0x51000406403100090820045007e00300500e0340e001c03196124038999901c0c00250850049c03d8500c00d80c00142c40c80e00140c862403e0b030040b600441c2c8a4070041ca0124180080202c0151a02d486403450480300303010004d00042e240400c0d44680c0724606040158144a40c481c4580418051f45004040c00712920a02100e5a4440700160100034101d030590742c1d480d511010400100c2c003a1030b155000d035902900d101801511016006452900540012614211120b0001322030f1094041003540c0f642d0104080c0e159044180c1c082c0c01c2c11032001c03d0300740c01c001d0003a140260b500a08401c0526203903020700481c0500000070502c80045443c81000012000102d24500035000c2004040da604002042000b0119031a82e4102801d15140031200789088015a50b0300c0044034010381540205400c1130002e031203501010b44c00803036a5032050f20048811340d00f500b194000c850842c2d190400320103000010740c0403c03c4480d5801c0391002400c21030f140d0b24000b0f4844145104880c0581d4950004c01c101301d984 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 903816978 1250 903815728 903815741
    0x8100803030a0902040605010f020322090903120c09030c05120705280501030c0c0b0a06080d02030705120316080703090812040b0c03062101090f05280b010612 70
    0x1200300c03a107a081c801c603881c000f800c02d004200e105620300800080c065000780120340805600390091401e05903040d40c28128000c07510301070400026400c1002c5040c900e94800e40701828025a580100c1000500703120085036410041d01c1c051120b154001c00000d42c80c115514107688041e94a1700301c06c88048940d500d002140c2d001160320048010081030035070708480c011550f0070742c10000740c0d0340c641e500d130015022104503030b10b000f000071412099074001c1600d0804140d0000c0c00400000b60340ca5035101d400d4200411140151f0050b040011b080d01441410400c80d003202e01d10b14513091440c1070103000101041c000d01140000d12600e0070010f41c489010b07030b1001c20140e4010001d181d072090030305a006011441107070101e52008040c0702098850507510143d82c400c4802030141c1200701000c680501f00b424060300403007015902c6003e0740b40010041c080001d81584984000c2c03904101c2d411080324603071111103500c00010701e0810000040b0745c00c80d05050440d0100d0414204406500c0b01c4440500413 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 903818228 1250 903816978 903816989
    0xb0a05120d0e190e072a140a0c06050c010b0307050d030c05070305100603050d0206010303141303021807080912040512030d090503040906080f0d270e1e0907060810 72
    0x20f010000f03404120391043c40d114450700da035a1081c0e001c51703082c0065031004c4040ca6100b46440d00c903450000840e02095070300b08480d031208403406418640e4848500c12442e401007400541c0106512280b61024016480000d50480290524500385004502003403584007014042010f18141c039024420184aa100513542100598408400c900b0820024001c180300c122203e1040403c405081403001c0356480c10b880d4540d807414407003e6200318041e406e0700100d0200c1503920036510000010303603c050036000014051000c01d8261300c4e15840c09802d0b000d005200f64030b290041981c1c05005126501141c041c8e900c104c60000030540c2c604a1546503004071690b00ba1041d00e40001201070100c0000a80212242c2c004284105a00c5440f100d48070390481c130000903158000074035914a980aa08148016410a587c0c58060030600324020f40b004256030003802da01800505100401c501403000c0c0e0504100c071403d00a140c103101000741c0e96000c8500c602d2040003400800f003403142c102e0942000041c40c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 903819478 1250 903818228 903818269
    0x2011a0127030f02120105071e0909050901090c0f0f03150608100501050f0d0854180f06011b1b06020610090902010c060f0b0a05120d0e 60
    0xc2e224641021404003c1c03400342d105103c0e005a0045201c01400740500c01c0466903200081036101004d00940300003064803207014085600f00100d014402886101c0c801c00c2610000b10f8541c00030b040002000c81c050308001091204284107116964403541e203a801c49501201310600d0105208103c4010325094000d50903074050845800d2000f03006400c200d0503110215003081141031048108204191081d000074a029414003178403010361040c2d0f00b45e6201403851464200070b058400a003140b00340c00302803000702040e040401a03010540034810100b180c80d041d10040c1b64050407050001e140080104041d44d150041c4c000101540d101b4450280344901d044444d460010301494011000c46640300f504520703d64046000429074800034240d801048041c000d07800d11800c04081a02900812506a051180304058407000500c5445814030520101303000003401201070b810046e00c6505580004e200741c1a090f000c0b010410003050a000c100380d00e00f89080900124800700f580030181c80404101d02c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 903820728 1250 903819478 903819557
    0x409081210081e340e01050f040b0f0a06020318040603021e18010b1b010b06070f03020a020901090b010e0a24030603170a020d0513120819021c02011a01 67
    0x4130b010182c50740c21890310464401415454031a5516400d000f4482c6507480000b13641409080c0c101075021221032100134044255030100c8001027860f03800580e018500607800000d840707400201e44081000c1050046405000391843c0d500000c0701c2004e914003040300100c1035031113201c2c5540e0780311a0700030007808074401c180c16680d20240f507106508000400b40e0b0070104015070845115042c4225541c4440061049040038259203402c2d00c1e12282a42c11000e501c00e040801015a490708400750080903035080c0820000f2850000418002c0300a200a00410b22400d041c000c04541c04c90443d0480000c040d000c15100c014103044021705115840074140f10301d03560a07000304001c408020199100715400720b0b8082d9403181c6003100c0c18400c030b00120401d1400100c007840066180344801d1001c90154181d40d09128622841c0215000c90185000150303019180c0c0d1003a0400303000319004603d00ea030000b00316580710302041d100d00000c461811030403c400d2030810081e9690301040203200c80c2c1202504400c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 903821978 1250 903820728 903820783
    0x120f190e040608190609080412210503091005090a0c0803040e0c0403080d0207020609040e0601030c06020a15020f070f1104050a1e0504110409081210081e 68
    0x10241080e0350314065410202c000c24014400240c1d01c0ea2140f0300e44400f66241140d40380c0c00d005100300b850403181500f0810001403043ca40c0c41d00e0910f0365004e1030185641c940c44064480040100001300d0040c040c0c240300f000320f030040100d07401604030248030b0301213030507610754803000d003004001213000744441031243c0c000c01c0c3d0880c000050030a440622440c0c5d031280c0c85041902e0f4450083d4480200000010800f0b121210819009072865510242481b03080c2081ca000090607600924074410481e032041d40100180240486201c1c010500d90010b0414030b000303030f12482d041007a8200418031880c3c00158035007a07200303620304441106030001da41c00307040c94283c54810001021580154419400c210105454200a10443d2840699203682d40e0780303004000e00e0b500c0540801032068030381d503048a401503441d450324003908012a1284e40300558401020078100b1280c40c0180c405004e206094105210041d00054030000326050169825001101004068901016808030038804584521070145 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 903823228 1250 903821978 903821987
    0x111070b1611010e0d03050a03060504060e06090612030d0b0f040e060106020c0f0d0b130219090e0c0315090a06020f040303032a111204081e0d02120f19 67
    0x20507201c0c1480d40c01d80c10b8034000464003c40c0c1035409035445604006010002801a0014881900903081c0814082da58400007030031103141d40c2c4424035000d100c504008181c40d101c0c0c1982c0c1e00c20310444842a01c801810b41e80c40d9280100a052400302d81d80b890300400903910300c030024550110084c014459265490025078450701c00b13201301d01c054400c44100e6075080c80e01d9030702a103002c407019200c00e040103c01d07200c42d00f100e68083c1c00c80d08508411400100541c5500e809862001494101440c0c443e1412070142d04130360f200d0a21980580100039024001d45c0c0219560398029034011080d00241c4a0030b00742c5003448040e61000340304510000b40004005860701c054421240213403070400c0010b98940c0039410908001250b200f0f002084178175509401d01030802071602d44504801c45010b120740d41814040e1754000d40045041d0f0f402100520403031100019002156100640544010700070410301070344e41c001d842c80440840780086111032405040009846070481c0700c070410103689401410242 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 903824478 1250 903823228 903823267
    0xa120303020c0d14030a05060d0609061a0406080a0308180a06050f01090c0e040507020304121b0b0f09221d07091416141209160308090111070b 63
    0x83d0003030543c281c100301c0c0130320b458001200007182c0085c41c691340e1039003041c020203005220952181da030141010100302103100d180f0f10144a034200103210303d40011041c031079540041100d4401c504004040c04209804110758502681c98142411191100c020b403105801e4454183d03021841880b40c0300301480b249410aa024402c40b80b110a203d0342c0b14148071060f1401c482400c804140d035410301400c0b03400c00754480c940c400007620507a41041d841d50140741403908080001c0d140140a0b01c07100c15580c03206a1840d0050218100701131520302e002030200c9040c0640b45902e4407628980761035440ea9152030030790754100384610310200010550741004125880034018194514451184045841c5046200b0760000ca00c403140c50110b81c1c1c4d2a04100e490404405216000300507292175103400c04500c550152800330410243c03000d03e441c2c0b01d08910b00c0c02c00c99090340d01076002c070341170108040380f800c00884014070000c4c40e00102e001445a500c070b2070b00089038031036041c0d22000030b14044c40010031071009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 903825728 1250 903824478 903824497
    0xc090412031406060a0f180b040801151a070213140901050702030a1b080705030406021e030a0c080904150909060525081f030f0219030c0b090a12030302 67
    0x8019034941c02e250021251001c460303e0741c211504010000e000b80c05514100c0d0020500e242200030400c80e1070803c64101241c0d031180c05103580214050044050030701500c1d00010001255140c0c2a02e0a4030b0b00d101800d086030181001c040c00515102591141d205c0e0510044180c9400d100d003c0035044070201290b0b0844c0c58140652030807001c16240d900c003208503200000c1950f2003500d00358018061040a8604500884d22444100200c90018000f07101070001442981c025000030f040c0c1980c0c581d100340c0c5034800500320350410014aa20f158020000c00000c0d504000826180e2070100003080060051003104080e0303001d4040000b40703052154026422151044205000c00d0704c9501505580c001340b00c0c1c030310800c030282441f249151441750038401e9102d04190408640000b1030700c1070b003003841b0711504160740414800040106608000d480707141c00d820358240d07030305102b0700e991100100c41a45005132152480b0000e51040603035503c070900c0700030f80440e04400700704206919020b0000e600810b0031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 903826978 1250 903825728 903825731
    0x91f06030501060e0604202a06040c1a072112050108010b040609050108060406180b0903131d0703150e101a0f161e061e0c090b0c0c09041203 62
    0x100c410f040c45881c0d91a501102c0487c0c03541000a1030710614841d0b40c424258050101c0103e400348280030f000c001c0c07140502c0c01402c80803016418459205074500805c20040301c040c0b007c0001c540040d0030f1042c28031003890907191a109900b0009800c4401042c0a008035603510f003044000b28401d9019441201c9004045a00308005560b890007182507031804d101d901403980040c4006804911540c006540800442001440d001340b030707645a4200b081c0c1581c01000d598004224681e0380325203600e01701c0161070400c0721070480724541c292002814030020680020141c0b9061401032699250304140d001c4c00c2d05030a5054076103480c2050303046109292260491409407070b82002002023030b841c2118114100301c5081c62901c010240c4600e400e450000b0119801d441ca031801051400400106100840c072070300c030100d182180780c55200c180c0030316101c041d403c40f4a0080040084ca4002c2c400008640c405403080d80c855035968250741c01c14070100342c0180c0040611041200b041410310001e400d501c80340d00e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 903828228 1250 903826978 903826991
    0xc0403120e031b0609090a090b090d08070c02030d140c120910030504020306011707090501090207021e0f1314070f080906130f0f022107080303091f06030501060e0604 73
    0x80960b0341010f894072160440d030204019601800c00303c0095138045141d50000c6000056030b46c0f00000391108513144003e07078200085d020354503036001d0215500041d10b4039000c0c2c00c08007036400203034985a130342c1c0e0a6400c4c01004240c035499a15180d003518050007913902038030b80c60740030f030425088141d010071991841144003152104105d4000c2c070405c0e001d0351f005401094981c1c209806207013424242c180c000418815400001215001405424040e00d0801c00141e2158140d206021034101080303c502c0d4040320707840302c1080c0c036110b8650403050054101e60505421004840b444001d0a40c12040584070f5200c80400490070381101e090544502a6912a09a640c500500035100c15040d200b59458a0000d410303400458003150078ad0f00301e81d0240300030500800132a80003c0c0c0090044944192085a0028040f00201c041c00003000801551010790314515110a0f00364890145030441820425100403a29429900307500c4480a950301800800405131210181c1c62111802c60300107204506000307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 903829478 1250 903828228 903828253
    0x90b06090903041a0f1602040f140c0901030209031c022116050c031b100c050c0108040f0507230d0c090216150911010f0801030b0c0403120e03 63
    0x100c0c291080d24200041c50415052503900c041c2d18155031000503400340140000070704042140300620755180c4140c4105090240c910500c4180c9030400c44111810780347c00d0070340640d50740036484594400d1165081c036035503440802c0141c009003d0b511509400d03200f0604d0751114019080300c0d02c1d07006520740e02260b603104c500f15040c4820150110003844231340c8050240011041c1c84c020113445882c4500140c50102c001400441e1602d021510108044000c444031401c1900307001c1d07074400d07078291285095030422820b52034940c0d9032000310b282c0504010b94400043d0600c00044e4400348561341c080d00b90343c00076945548482480781004028283c881031500d5002e01440c00c0c030030400100d50300c101020b004610700841d03003009400200e58038400700403606054000031043c072414250181c007a403001031081d070340b030a0504100707926050260601031003a82141620303802005050440381d010340706c81150341d81d11002a05a0081d40d20052804d4815030003440700540121494006500640407180c1060030031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 903830728 1250 903829478 903829489
    0x2010e0d052a030f0a150e010c03060612060509061306032117010302012019050714040603031239030e0327030111130608070302090604060c051f090b06 67
    0x154645001303540005070040001d1998588007074000c9240d0300010745490300200484c02e560043e5800701c0040c0d030701d034400d000c165044034818071032800c0c043c001c1140b542000c01050100201806151017100309500e0340c0960a1140c001c040a103600200c44801d401545031103009a40000e0115000709400300c00c8544c1540303551020301d0480f60142e407003480c03810309241c0c5000c449461025400050040843d810007441c01c1c1030182c55118072940003480d030b051034060b05202c1103801410b860701c29070038440e04001295015804800c50708403c4000601742c1701580010020310340003000c96468000700c081a0345040480e084180000b0348a072400d00102d6645481c46481e0320905170690b403030a0100095841c0142c0e924105e050218000d000082c070031054025516540c0c001d52405113150b00022424010650f00019160f003001d0304d401c00354205080d090016645000e9030184004120780b80d40c504042c80070812480200203000300041c103d1081289000c0d000d408400c02c00d80e04504960007045580c20314 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 903831978 1250 903830728 903830743
    0x2070803100b030412111c0203090102150105090c0c010204150e03010b010903020112180b0a0203041202061605090103024b0702151309050601030c0e01080402010e0d052a03 76
    0x40360a41c800350402c01c401b80c4071403a506d660b0320b482e0310074891040f110080c0d850782ea4081c511950002d5480b4094280024680b000080300910120700c0c2c140108016180c1200310b07a0000c407805007003516806d21082c541e009016960015201350012400306a029400048901d10780400798020701c2030160520064a1032070185c0300007800100d00003240e0a2114540c0d200d14903098969042d0b002c0602182c07181e01e00c1240940d080c44050f0b9000082c40100110010304911034103450001d00b1840c5004203102c0c8240d40d04183e9501400760000b81105203030b05c207504441d070301a00001c03000604840f6549002810480101000d8546200b02d55400302e4203140e03651202150340d0303c1da80d45c50304840343c0c28040220803402249805104c10300c8100040040c01443e4406040000c0c80050145810300004050b150b00005810622284101c050b0251764410600c9a00540a08202c403080d0024008610803c0c1ea507600588107009140b82501d80e00d05c60903807200d000f00d01d101208510300c643e004140c0c96282 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 903833228 1250 903831978 903831983
    0x10212011a210c040905010b0a030c0f0f2006271b130e150406061a0d0b0a150206040c061701062102073e150d02070803100b0304 57
    0x303525480a0701644001d002c0740e00000fa29221030030540e44941980940b402a00b01c400d181c84040f60980110b0790610074a9001941e03458001810894508080d10703886041d078108041211290408080c0903000c403075640c0b5003040200320741e25494811000c091044070644000c440c1c480c000c103c0000c0c0ea030005014048442a25200319030288c416040011040740c144c424035007540c0b1188036191101d0305100d81440040c10404007901071a180c9080000c0350702c1c9401400300f4030209410740d44030044030015035820a44001d00007a04102000c00140c14907103035403004142403040c402e0240260781c0425420b01440c4109107034907000782c4505041d5010446000710307032102c02014004100b85031003000c100055040c100f91010101000710f440c01c0590740503801c180e49c0301020002103000030b00d0322911aa026980d00002079100d54422440d80c482d0a41881c1d06032188003210103182c150b0400c0d130103c520190348440219503580d05803400070140d41003168800039a0410440001d101c80465044911855 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 903834478 1250 903833228 903833257
    0x3040b07020312090f010c020325050a0501020708030412030203040305091c140a0c15050f031003020a0f05100804030e19080703060b09181216242301050d02060c010212011a 76
    0x38005080c1e001482c801000b82c03102d2041c0e40780740020437001e00c01044280e0207002242d6491604d41400c2d082d010001d940702d07013094070400812006c2075000702030384c811040844065420542480c0e8200e65200c881c90050440340d5030516030381e0090307400141e1154213841034040c0100c660303441000f0b15550b1808140080420b104110419500d11024001e66111428880303030780c0c84640760380100302001855001060702c00c00b0024180050b00c3c004001010052003442c00003a14601540c0040aa1020101e03490240c00c00c03c0c2c95200154100e8800340181136540c040304d51207540ea0034a44060f00800d031605004651030b4010400f0f0b041c281d000703039081d90314150003040700305030307400466689034800e07200050203803003070080c5c1d0000500d024a01c880c1c141c40c02c00c4031840c01c104c404800d4221034044001103080401e4240c0b0303202d2028610340391811154125441c0150828030300100e000c51240c1c003010107282d4130004150a8188141202c3e034140c80e0920300c01c2e01001035180400d101031060000c1001e910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 903835728 1250 903834478 903834517
    0x905040f0b0c1306021f180803091905010b0405090610061d041e0507030e10020a020f0a050718090b0a0506010504080304030308041a010b03040b07020312090f010c0203 74
    0x7070800c40145802154002c0c1d26843e25108030348507401e1031002d410082c0141c1003807001003424040c2c901c4001c203042c0c00f4503040001011003032000c2a41990f450000b13051107004800a210b116003401341c00d680f401e21204481031642607150807402894810450382c400d92500011901c200b40c00105148102400245000c9050510f0010307110501c0c45801c0421501c100708442c540d58503030f4040c260303980610b40070715000b10a09550900696000808000c00c040c030749807080030f06182c0004e41e051030603111400140e803480c60314800c9080c4010309808541622030940d0303c00c20000002014400c480c00c401d503110304800f0b00c0300070600f5220742c5d120180c4464950300100701507544030b40c4410740049050600034031b00340d682d00100d821600940d0040e4042889003041005010014070702c01d01c0a02000102e204d158142006d40c946400041c1010f0724a005103000100c82034000c0040310044804220502072a18000740720541d1007641002100741c079400d2409940300940000151852904c1517074104504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 903836978 1250 903835728 903835733
    0xd06090e0f031206030a150e0106080c0a0915030606080d1d06030a0c1e020706090911030103031b0219210c171f0603031107060903060905010b120c01090905040f 71
    0x4404050b010b05e034540101800d600009040007003503200301c15440c03004110710f203e1400321400c440e07443d480182d00303802103101c3c02e0b0300741d4880c840c900903034001c10380005481e40e04242d00c070200991500000c0c81c2c03a01c2d11a0200e02420001a119078010701c035500e80d034070040101c01c043c64050040c11040d41040381400880d10600c095004242480100d24002030410520b4400c1e02401340c80140340405230300b28200074040c06074488003a40c080c2910710001e101e1400c0304014081c06110500c8043c080008610421a24034202c0302ca00c581250020102e0400b0021281450000c410504c00c0103880300100050080c8001c4040440304001e41269078200d6080c9010100c68020036003100c2e400040c0a00d098a0410003072420100d080d0241d2890700158160540c0340140c80a804000c082c0b883d139000440801c13211b648194040c003501c0d03020a0100718000c030341c54442e0240a8808071140c2c08114602018a0400c000070f81c444961003d0b40e442c000156160045800c41d10700750740c007408601500240002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 903838228 1250 903836978 903837007
    0x40b0307050d1406041a0a03141002040803132112050d0609060503160f0b1c0c1701051219050c09040f17030c090415050301020d06090e0f03 62
    0x40c00300d101d040440c50168a0501e4004840c1409903004400d04600c0500141d4200b61051a280075106042804c0c003a41801c0012507840d25440300401c82c0c251004505c1380c50f40c0c00d000d0710301c0d0f21901001c00e42d2543c1d12100c0d07081c0c0f00d0300451103805a48094100024070480c0342040b0904005c41d0030086440d6611544039203001d480302c41c8443e8180b0404000d07542d0381d084139101e007000910b43c40c200000c81c14100810075090501103d0340038800d5030684018015040354160b01d0048070201c1c400180d0b03c0001302c071f140f5900750746812034070011458014106020340d001074514043e50702d0849500c503142e8860040020f154070401d001041544100c8800c001246018400401d280c001e00c11150801c071003000040c007402d4200c42c100c5850442a68200412440e10170440b1000c2c40c0c1d18001e421803425090200c2c0314068101c5e030300c0c800c0340c546040958005c1040079400c068480074009560700e50b0500c00c0c41004d0900c40c810f50b42aa4a4841008003440c0049540d080e0291800d02661030a42c040b00182c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 903839478 1250 903838228 903838231
    0xa060b1233010c2a03060b040c08070e0d02210c0103060b041a0c0a0c08010c0e15131502010c0e12060705030a0e1c1106011809031209030e03071a040b03 67
    0x107079840c4003450244c00f0701d411a10140140c0707841c194000152821413401c030007502e951803807040c0102d082c040b030151415048500d40303511042c940343c400d29010080300050804001e01c1070103508112141500c0f0102d07618040010707050b21000044520b071100b007000450840c0d005100381181e505081c030092254050003612043c80d00c0f25a00005d003040041c494043c2040540030b8101d070030300404201080548401e00500c0200c0303e2901703040d00042d10002c0440c00c413050700b441440f1185d80000d014800e030350050449602800341c408422110078003204008c2d000340050040c29000c9214800702c0d4602c0d01e0310300f20060408510401502e140d444040060b00c0030340018013a00d9086c2c0d262074220f100001c00f08040701f10741194201c0e1b0392440c64400d030040c004100b0703004600c0e1185c010000510048090780303625075096074000c10000e5400d2241c1000c03601c2c00c0500c00c49446260070020503400303040c0d105019610040040341580d94041e615020040c032000c21402d4100091824041042142420000355 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 903840728 1250 903839478 903839483
    0x1080c09030102070515100914040b0702031207020c1c260d0c1709010b01081b0903070f050114180105070f080a09080723090a060b1233010c 62
    0x941003200c030341c3e03645062000403516080030440c00800c00065003081c25687c1c1c000c08041004000d506031a200c60b03d0040070050028144429a0011440e076910800c100d4840400e40d20f800115405c020000130f46510f400350306244500061640818640ae0800e07d00400c282d00240d00c10f400d00040b40208240c04506052900e90303070061243c0308000d802405510502d044039a40c60940e5504400c4031855550080d1220a040c0e140040c002d2160343c00c1182e83d600210701007010003441e42070740d0380d00c1500d109200d070498160195841c00503051031060301030411b0303e509888124490000007103880044c007a0601c0300b030014030114010159940a40c00404966008001c15400c010340c54440018640c00b00c0120400282c5100d000c0010140a00c2500c010301b110300c16441c410505030504030606002450340718420b29642c00410f240c2509603010100501c0401b000646a0b403583c400651100d50440b00c00013030041055485542000c5c92030580c082c0d86030784e6516103d200e030f04001114900d690b031104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 903841978 1250 903840728 903840731
    0x203040905071107060306090c050a081308041508060301050906133005071104020a02030904021b0f03130503121903060b132907020d0515040b15010c0201080c090301 73
    0x1010305051081c49038902410168031302150003232500d62010104d802c107020400802c8824001c07074070b4840d800031204d0303000303007208010070014100750802e03000912485d4003181d48d441e5100003200100d0703041580b0314418181203000b00074a40c1c0b0304600d60b8455204407100400701c00c04000c0a03000a05000c540750783c0510321a0400c920424a001414621414040d84004a20003080020820103580081c0c00c001d2816070b010740c2800c1900f0001f95480c06450201c6104a401140e401d0007050100d10b03008602c0101d00441c1e15592901001513141da0003940d1408a403038820501090500340042c0c2400102c828400d80c9180094031807400a2601c0c0001c00803003016200c06c0009821a4000e010341a181504241c0c1741001c0c0c6407008540760000101c2c8803d00c00030380d50080c80000b40b80c00040d41c0c603098055030320101b86007941c40c240b420201c0a0301c08561030ba20390001e0100740401a400644108074580304041103554120064841060003900203000484003c0003501450810b4054120b02801900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 903843228 1250 903841978 903841997
    0x190804030201020d1505030c0a180c0c0204060f06080a110304201f0201062304020a090f030807061d06071d15030907150f0807090b070f020307060f020304090507 71
    0x640c1c400392205c01c2d9803100428041d040500c2103140034030650322138100c08c541c0c1e041f8040c13500c9005803010428425192026a03606030300c0e501c15025a0ba00c0c601344e07900a000700049a151105420320005d03c1c002c038000110240f0006014101034807401a4070a600c0d90a2829030f5203503904d005c003400d00e52084c510004103580c0601c0c11611040c0b1002568428100105101100010000c0c00c41d4003a074440200d01c0d80e0b0003680b12035140c1502c03191000c03c4060340c0241c0c2d1008aa1000e403105602640300102803504040c1c00400d1000f40d4001d031149521820090201c90404003948441e9410f0a1103143c80c0c3e000800801d840c0d5015201c0f010381551411103c80501030301000080402c040c0a0031440c1762500042000301a034024001040507240319507002d02c1d8102c00700300052542d10700700c8440c0280410500407840c01d034040c0c0714000040084221566550300245090788101000c050124060320480b080480c40e90300840c88842c94821a40c01503042506d000126005428040d0039241804401c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 903844478 1250 903843228 903843247
    0x30807120302041d060907020307030c0f020a1703040819020612220305090406050418080c1608030702010927050a0914070305062a0d1b0c061119080403020102 70
    0x828064203040310f048905000c5c9800800e001282d40f00409440442d081004040c002942000c891002190043c6041d12084854070100344d4603900c80c0c00c0360314119801d1a80040b000700c0003004005454103201038400c048465072001d4550a46c020000f0f51042041c48450017071105000e00551048492940d008026410b4000705200c030380000381600060000510520123040c51301400c00200010745041021000304c100780045c42c030309100300400480d80001c454803038001c200410010011000385003051135a803008200e9903584445c0049010454005002070912807040350301c002ea00c3c1c0c91400718045034401c03607003100900d0b004240c1c105080d0b0707828411010400350420204000800c9000300380550850a0540c07030b100c4001c001c92084010a840340c40400c4460803841426080c003a0b04540742e82c0c100000c031000c0d01a4600c8210221219500548002c0d4065085000c49005a00810540e0124181810070744510b8030220580d10080d8642c60a284c80f820300940d00c2401f0307200041c200072070f91 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 903845728 1250 903844478 903844499
    0xa0e0402032503060f15050406050703020a02100c1b1512020f13181109010c02040b130f14130b220501050412030903021507020304090e061f03080712030204 69
    0x4010600043c2d550348003484405882c00c0f0410150001d91b4010520052040c070040c00d030710460144070b0420a0100340b02c01018020445103000c42d90060840009070101c8900a200010041d41900c0c081404043d456000807880c3c05141900ca07030000300c076110350715036100761094101c8201d10204298200000324130700354140c01512103e0a024818000c0342c0c90701304140205889074071045002480c107031462040481d1101111110402801c0903880101c0f1800040c008084940426400c1501d002144000c0c44040d40560300d0401d61200402044000b450003010304a41110f04240b242a0391140102299450010a0f404003001c0300f0000c25505170582c01d01152101d84045407180e448509201c20447c0b01c0c6c0c0c5640c410b58103032070100100c80280c0c03002036a414650841d01c0c0d02c4904840414400d900c01d00443d80508248142808070b9040703c4405a51349030102c0c1d0300d13041180a20090f20050f40c80d040c405c01100d800c500c442e03040c65265244c074512205001041c00a25508210000b004900c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 903846978 1250 903845728 903845791
    0xe100203071a0601030e0f03070609020a0819030305010f0e0c07080c07090e1005190b12010e150117070b2212020f0a0b040306020702060702061b0f030a0e040203 71
    0xb80381280c0b20508140b000541500c0b1140403045150704180460119100e000041e1046550010b101151480f0326001051804c941500045058024410f05941000c00d1a0684e45198800c3d602040141c0e41c90300d00d0302d41da4155000b109a0074180d04085261603564801510001c1c2c0613060241c034220035071a54074030b407130f520341c2c0004078160304c84010b00d917406c0e0180580c112005460100344110700e411611691056007900801c48201e0350b905a070b98003910b0b80281c0c03d09644015000700301010f05444d1441da10034140210350a0007031180c002080703020b0b514100030300c400c507d0001000c0450804c003041000f5000380305125044d910305d9a00c0c000544001d41c1d4807000740100350810210389a503006002c20000d030012054004c401082c0c040007444645011203080b00c1d0040001030b207840304c0e40700060b02486410070196005c8804100e000c2c41e01c03904000d43c4203002c61001180c00d09800c002425450f0302903001c1a00100e19000712112980c04c1c15001140e20510100c4250a10031100f241555401d10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 903848228 1250 903846978 903847013
    0xe0114041e06030606081302040e0a051b0a090c0c030516081902010506041a040c12020f030105130915050403051201091a03010e060114010c150f0c0e010e10020307 72
    0x4429002c205035501840340070042c00c41864840311919000f004621080101d60000380a40d60311840700561102c03d01c08981c1003540441510800c06001707407038800c018490030340c182c410a0f407401c0010752140c80744180c00300c555070b60b11200c01d42220341d10103860300c1c1c02580e004204509280b04107030024a181c3e005100c003003c4900c00441445242c04024212500204054004c0385402c0c02041940c00349082003491100840b0042407604001800b01c1d042c8588410500d5500d002003040c814072060311000c0e505840c000c0c0c031204041d072915400142903d04000c005003880f0150355400003000210b412055001c0c2c0a81400d514101c000041c0301601c0009074401550a5a00c44007104142174040180600d164220001c1c4403200c6001c24090f00d594040c407603111152040c8500c14030503400340b448000b805800c414081c610071a100364060180844c02d13541c40080d490408000700803401003405241801c0103940e01c6600790402c505103c075034944034040809610040c818100065169403810700b4045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 903849478 1250 903848228 903848279
    0x901020d05011203140d0204081207020319030e10030209060a022d06010e060d0507030606061227020418050a02090615120606120901021e0306010e011404 68
    0x884058190848006030040780ca00f03012a02c103500440d43c4400682083d29150f9a134580e00d42440e030b1514000d2041d50310208803030141c0444c400888080c00c001d491068000c0d016214441d80401111a01502050004020808403c170408103402d0800110f02d0161160030014601244080029010b401004d100310059100800403443c090711040d456030542e0441c019504140800300d50a61a401d050103160072a2517840c00140d020341d50780d00740550080d0000140c499041e1203007042005401c9034003071800442c400c0c400810241d0200d110360b40244201441c540c4504143c0d40b0106a10001450280c1e40507441d8422100d0740c403140003401d42c03440e22410082894107082c1c4144110603400400b15072141c0b0002e41103c031213810000407201080c01d01810b000c410b5440d00005121405642c0b541c009a003445c9041092040e0158010852141c0c1280204103403c101c0c50b050209201c1158403600280e882c0005203c43d5010341030055a550403404502c1c20701d519090b1040072000b100b8080880031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 903850728 1250 903849478 903849487
    0x304050a090917182b03050414030d0f05090a05060c012909040308040312020f1209010b011d130c050a1103160f051005160e190b030603070905090102 66
    0x2042100c010a140303061080c50b800c215084020040c085600052a80900c95a80c41207400084285e59142c1c03459040b0060b03c00b0341e50714100102075070800c1c0030f200490244508140c4481c507000400501121031940ca044891561840442d01d64109441e181c0d0840000c0d407001c192a92114082c000c41c02814000080302611303020b4000c100e204168024222444403450540030707440e0080390550154042c1003668041d2034034501158042c500780d030403481a51011855405410202d0300401854402d992a00101d443e142c030344034200c4046080302c60210b4241c00d0a450580d90303400c2c0f0324101600040000c02c0d070541100d601c2d002d0f030381d0800110000030000608000c001b42c00c000c1d800003410440c00194201810b0b50030a8401201040f030180140c0340003103c034010050f0401082d001e43c41c0c0780b42c003400b8034245030400e00c08458405000c0004180b68000b0614241482d0503900704020814030115841c030314100c031a454030b03440603040c10340500681d007010929180f94098180114620400140d030f4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 903851978 1250 903850728 903850733
    0xf030336282102120a18240318020310020306090f15010509040906150807050d050715020c03030c06040b0a0207020303070311010225050607030b01200304050a0909 72
    0x601180207500040400582544021507264031a40300c0204900404a44840162000b0fa00d0b10390b80752545030000c1380001d0781440301c0f036010661035418040134504461240d121406610400c000d030901c40b00c0444e50640081205100c0d40142c081d00300040714005981c038254000c44c2c101102c10003568006500002400500e04008405542c4010380c4404881d190500410082e004500f450742d050400c50040303890360042e95160302403440c65031310010412003221142610584c510862142110900900742d0010b4941422035141000036800300191144d00e0501c05007006c84a20240c246085115010041895440410043c0f00448003a00205918509131800101400e401030000440500501c10000140c8000041d1425283c0c1418840c5240404680050080c01766a07498404003031290b50544140b0800c145050040d8020f5050b40d01c15520a141581035440101c409400502c903030020307496070003982200b0720000302880203403841c0030780c1c0d4000a00301c1942504220820740c2d0364002c1108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 903853228 1250 903851978 903852013
    0x180f031005190506030d051318050910020a050405042309060f240402031905011d0f060f010f03090c14100215060d061e090c080f030336 60
    0x801e00c0742c07400140180d142120100ba00c450301414200144540810601156804000390f0030290031100c10180542c494400400043c01003a90b003101603008034410311f03001d21101e008644454805c0c1d00c605160618050034800101511035a0540b01090744854004142010100714000c009400080c0454140800c54103501d0710081c0c400b080380001e031201d480b00400c1500110902071400ca40041c2c4036552032202a2010701e0034400410110729001c008070342401c500b64951018101ca04080001d41d0342c05400c03201501d4182c0b0499401103019580e841c180d84201c070645450b00492030045441440759030741c484081000d40040305075505c030140c504032904040d000c00050014a100501085020301c0f00d00201000c007524507801440340107900b1081c4003880d04604d07001e800403107244003101c40e900384d0100100056402100c10017905440020349030380004030241960000d001540c0b5648594070310081704030a00000000320840145421103140c40d60f1a507000f1140b13040050039041805010051 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 903854478 1250 903853228 903853261
    0xf070609050901181b020708070e0910050615030103201e0f01020c1306050a050306090d0302031909030804031101110301032307090b09061203180f031005 68
    0x202000000d00d42044159100e210a60440d41d50b444043e00c40207100c140000941031050328500b01c03140308980d15100c5503000810904540f642c6080d1a1201d844070340645c940001600c001d66158040410010200c00543c40a50041d0b8003c5c44080d03c070005c50164200c40e0000d07070054410700944164420304c00b006001140c8190400c0b90841c030010100865181c1c0d40f000000c11901a0403600c003144907590081243c4684903800500c50b0420f40342c0c60040d80040c0200b40605409081034407000100740c10002206030180c0d8920002d000c10540d41c40e0114002d400040004010120005000324011031a104c0c540e08a0b01941d60001603282500700034200d008603d84c01d0100381e24240280d440050000c0c1070301c1c192a03100e09881d04120451602951542c91140300481c40e02845c42d000500e541180d000090300039044ea95050740342d03101c00820074150311124015400c4e40003001181c40d0466050180d101080b402041d0941104030341d0080b07894101e07150103048009540d81c0a00c06640180c1c48901c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 903855728 1250 903854478 903854489
    0x37060e07120b04061508030d06080f010e120f1e0c01050f011d0604020f030c130602010903090303030b030715020a0311010b0307061808011121010e0114041d0f07 71
    0x181641c0303034503640c0d03098400002040686000c1e900c1d40b40510440c5607601d10001801c02c4000c99803114994003294006000c24400c910103441a00b1144004038018020790306090002c0b006402c0318180500218001c1d48050602881a90f04012034074142000e031071040c0d9007000c5d030761030740d500c5000b00d44c03155085403000360a45900507105001082210280f00e108240020010104081d6880302d20108001c1e00408a20a030340c1f40010007048040c07804d11018000707640040000d00c0006070fa81405034200c58020300301500050340360741c0034804a40660041c0d00e01910150440354503542c0c0c0c4051180d542010f50044c001a0491240351003896440898500741c055007074000c20001d803407140000d903183c64500c03400c400d101c10f07411010180d04022600000400c0f10400034040c584291241d01c0b041c0d480b410420b000c15000d102a09961011300300350505907800b411600003aa428400400b0300c14051554a6234055180c80f80703c0d00464183d1080b02103040d203900240a2180403489890400e0303181d0300607 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 903856978 1250 903855728 903855749
    0x50c0114061804050d0c0f3014180f0d0501290603010302040b0105040305060c03060111010b0f060915040b090f1f1b02100f08130537060e07 62
    0x80c4804a0800705c0d8020300180142403400002c00302d40740c04044010004000741a203a0302c6a185030018000d040481e140544442500f403012a01480503122000032140c241036048084c000b69030541039040d030744000440001c03c0c080d1455802c10003c0e001d08a1904120345594490092411601e00c48c0411490210111030017100e44803042c01250683c041403101a01c22900d554440549902440450b00516040415600c0c686070060400d05150310035a00540020504c030306140501d40180b08816440000400c4010404400b00c200143d0fa0007806289a1000891110849085030075008000900300fa000042d05d07680071404001402c1c805181c1c040c0281414140901c42c44030f01003540306028900c0c24a404422460590b4240c41529440001d40215503800305100d960340010041c40c0144d419a41c4403079568683c050884542542880205613500000d00894a50801c1002c00e580c1c0d0518000300341306540c00c040e10006019220b40230b889482d56008804078009040c8400c1c805405d50254 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 903858228 1250 903856978 903856981
    0x1412100509072a05031e0c03070f030807050903190516090605030709050609190609050406090210030c0c14030d15060905090106120e0f0f010c020601050d02150a050c01140618 77
    0x440507107031b10440d070800d0b001440131610a030b03601d10214203950f440c030a0001107136191183d5280c1030018015600c025000715521400040c40c1a10030320444000348030180140c14544103056500d003041c0c1010340129041e0040720541048004003020b0f03031008104000021a41a18040601d41031040c0742e0064150f080c10301e4200314217902c03000d04403038000d1000554840c4030031442d40100000c0241d5003010206a0604081c0414408190429020302d4021034003c4140036610000341c048641d40321514000c02e40b2107001c10046603005c038401c1020034404056030324111036010090b045986c41043c0c0500b145121a003803007003076440740510025003002d413020714855041c914003030031100d2040d1030f0245c0c0e0340e122060640210703010b000340c40100c501d913001c80701c122054211542c080c180007842080148600b4000041030f00d012007140f041d042e0040c040c44607a0b8032210a089055001c501d5803000c4c008208040300c4620000d2240c00e40310000b200415105003084070402203e05010a10400d500c0740040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 903859478 1250 903858228 903858233
    0x20c0910060f111c0e040524060a05160b01031a010b0f1b0a0309050414010510030b0d0506010b041410020d0e010c020603090109030e011412100509072a 67
    0x8201660001c103403c0810780c0c1c1582c01516850300c02079030340320f82c5004e400002c11001c03070360001900480311504440a00040e960a000c90b00c040d044907104140718103800c840c01384d141c02d015006283c04000c3e46091441c1044603030030040041803c40c41280d03250900401007003440458016954501410468031030780d03500d40502c040c0d035030040c0840c80407100c0700010b0f6200000040900c0030105021a02968200621800d0181c030070005840b451f0b020b5410000501c2c907280344418094103075080202200740b01e0345080000c50061008064081d08110a02d50220206d0010081c05e802010900d400341e41c0ea40c105400054400711801920f40595124100702030034503008900180400358618080d1558034044004132201507580c007019400640c00410f01903022010741000d03c01c24003944404444031081c00c01110b220640440c00b42942c40300388684440c587c02e00c507980e83c11808601014181e280c4540000e028580183c8204006c140e420000640b07503a8038000e0440212000a0b1072007007a10f454 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 903860728 1250 903859478 903859487
    0x212041403042306070515310605150d060203061801060c03030509010605060703020a26040e0a140a020304020117060612090f070f0905011a07030e030c040c020c091006 74
    0x10f8100b480640c0f62010325096600c0e0302c41a107140a4000c01210040300207501350326114442901c00000071001c110801c0c2d0a0080020701600b0868030300c4038110400c503107484443c003c0002801160030364050502c659800e07074030804c1408426001d0440180d4030b0a140d02000035040002e00c0d121102e00c007003001000344030b1b0010344c80701501e509400c000c03455a0303424030f0450040445401807a0322850120310071040c154000340307500c210751182445003028081000b80e040308003040c0c4a0040f20180c104020300003000c2c112241c0750440b41071200810030400300c404d0000500e500311282c0b04003543c00302c1040295130b800b00d04410280340441d002811400c00c0b0010070401d01c0740c110300c0d00d1900c207044041814400200040241050000b096440c55900c07014041c031103803545d01c0fa4410450a040c00410907041040c9144469449810100e183c100d40da079007035684074100c000c0154513002d50000c1020580f1940102c2050f55036030390261540f00186010040d0b0390f40090650300505140780c4040c0b001e80d810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 903861978 1250 903860728 903860759
    0x1b311d010e100b09130902190602160522060302030102071a0a0507120b010e060301060c1a16270f06021504080a200a0c0905010605160201030b040b0301021204140304 73
    0x20f58404040c45c0c51002c000e4042c1416240007500400c0d50841c030110000103100d000180c3da80d030780c00e803000181c1d581c040d450070030031900605600031000036140700c10a20281481100c69114000401e54642e241c00207402c90f0018801665414036001841c8901403122640300e0b0300200444d0100618204280021b009805004280d50f001380d860078041c03003580c0548110b12101c07400401140c1c0c0c0e907031101c100030328007450031400f298130210403e80358818109541c0494400c1c1c140c0c545807814200c094504850258501164130f50054440081038081044c901d82440a40b58120520078035914282009240620003000c900412400000307210004a280045502d0380c1c41c513250900c940011644182d05001d000610840184940f130b43c0c04040248950440d01242c403011401c00c0b00b0382e40d86100751100d10038000340c0c0008101150700c5100541c001da000780410700b0091302c005500c40e0b40c000407900b2a48050210501480000104400c100f03000d09200d070081e80341e801031420145002c4440c84505030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 903863228 1250 903861978 903861997
    0x60612030c0b0a0b060309032215080a0f090f02090604091e0c0e070810050a0302130e010e0f0a0203010c1707051c050a051b311d010e100b 61
    0x40c82d03022030310001c0180c200c6440b808004000960f01d0402e600b01f15503030380c400040034000050301903040d001c6000540100c011603265848180517005603450407121100018064a0825070f200801d03840c00c0c0062003141c036094414442002c1251f021b00412401d090300602d2144182d0818a0050014506640c01d80f46182115003043d809882403174640c80d0315500e9002174850040c1da10400c0b026030740c802c0d0002d001d2404550f141001a440c1c6081c04210000c900010f5008424801101e6141c02a540401c0072280b42d02c0000031881034602031103040c01d8000c04641290383c40201c1840075441c00384a15920004c26082849a000c4a040c1c40c2d40385d040c00030042d00034803c0c042806c074240d50801003500080c3d03c00000030081d503e02081c102d0011f1500766540b81c1606403110074010102e0412007102e007050902d202c130244400080301d001400603442094034950310740501000801c1d402c42004c40314400ea400c4200390180d0b04118074004021002445440074860b081420014035030020210380d810075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 903864478 1250 903863228 903863243
    0x1050f0105100e1c0b04110a060516260c010e01020301150c24021903050c25210206070e0f0906060c060f01140f030c0d0c030c060903060612030c 64
    0x1003c81e000a81c401529084030603512141d010140200103800511a00c00c6105041c800c030b0100b400e10074010360200da07006101c0420304c1085025044080e01114000c1a0711030031001f82250307071000000c00517804004000c05400300c00b0034a00507081080c0644000c1d036189500071811903150030b07208103100100051210500440240110a016552400d05240441c00148540c212900820b400082d84544001c0f0b10302171002c940e15290510038011513024518107101c0d941010813106801c7d012010b041d604484a204402000001035405540c00d880c4410f1455400f400102502002c0d04000008000c48100800e80308900c40a64404680d000c00c04000e58030785240d5903414010400c2c5100d490224801071040300100013a8260b00c1034114181d4040031320060b990704049c1c0502c440510601c0c0c1031585a0001d4002c2d81c100c2c1851a132002c0068004c0b091040882d41c4c0b03882c7d0005c00266600700b07000051001c0010320505c04140a082e0041c250300004070512401034400803c0321910100050911 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 903865728 1250 903864478 903864497
    0x105090705010309050f240c0909010e070918020705010e06040f080f09040f0b01030b0f0a14280501170f06010309020111011118030a080a050c010609061701050f010510 74
    0x142009540304151200007111140d50b51920303010305c0c0c1c410a090141f0030340b51031800240d00301040c000307481c0c0318400a010003c3c244d00340076003240841c00003045803041205803600040c0700700400700741440d0a8100c60006070743c0c82c890b043c52401c2d980400c00c2c01c26a50b00078424880040c903108440c0550340e0b088050207031602d40f400341c031a00320720030442c03000d40c820308008140f4100d5149500600b8600d03000d8030b08024031845042400180110802d40c20384c4120504c0c02017010320b603007a60000d0300c01c0005024680741c01d000e41050310200501d1010040112403410244a20750b0015000c401515289400607032914010444161040c4c2c028212410540c0700c1e16071408590180041741c7c442603800300207000c42c03114a42d880502d504501046116801c09084038101d0342400309900004941109400e45030580b20441903c00754042c01c50340c8115036942000080c09541807052074054071226800031081d4070021000b07420f559000d000c0d5450401018010403030740e520f845000c04a60114100791100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 903866978 1250 903865728 903865733
    0x1e0f0d18090507050f0a0c0b040b0a0b0f030d05030c070f050609011125140d030209150901080402100905031b01030c0e010206130f120f0f0305060904060906020706060905060f030105090705010309 86
    0x1ca0300e0311500070111050388c02804100102009510301c10341c140030b000c100e0f0440076030810003070604d4480303036a8043c2c1041e45094400fa100d20019544052014003e0b071915400c0d6030740341441d04000c01c06403240d401070814000c240c0c500380a899643e070064803041342402008003605a040110b40000d429440c2c00f48000360030003a4012800140354002000d550301c0146a0b08003902035030148940c0b51040b0120000c401c40c8000c0d41c002c2d078800c6d003c103035203401d560758542d401d000401c0c1e0030008807020b000c40a5800034280d601000704540729910302281b08030740d0210f04005000e40d03104181550500c01c54019030001e690740060660380c00f482c600c03214480d030306070750404400040743d04101810a40e0102645100190007294240d1881410b40c2c81c813a050100f02c000b202151010384083d50310280e00e05c045070106a00390000d10195004541c011b1500186555000483d0340c10b070700070541c240d2204100090b51420200107a00c4500560003400030385030403105a07443d821a809040d05051355413038a5030030b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 903868228 1250 903866978 903866987
    0x50a0906080c18040b0d06061e030506040605061c030306030201090e04020d021c020a030c0305210904020708040e0906040b060411120c07021504261e0f0d18090507050f0a 75
    0x6441c5d0024002c2071581500d401c1007405440300d4011403111038601000951848044080c0004481d0804058100c80e21070b0744c2d612000c2c21024200c1a4400d02d60010128130160302c890300349409100f1344002500340d14510001d03280a03420341c405541c102c0114200b00c0507803100c0d41d00100140d0b0458265540c0425000c1c2a221003200581c0a50040c142c12008410003a0031030604060301d0242c07003110030301d01d4009070506182c0c0220803c00d081000c107000c003001038186138014000381440f81c0a070909154543c6000302d0340020803201d07141d4aa21450a200070b101d1200c0c01d05400c0391080e90300b403042102c80403c2e4480e80c411020804002c410b0b4030000751284021000f501c2e14141c1c000c08201c11402043ea0142140d0042e0140d03500d48803040d0945a007955082450700346100424000c1c014498254062407044080d601803641a40204110000f000000b8404460780220740c1e110a515501c2c25100c90a00411641000b01c5241c070744400d02400300d070070106490490783c4c15070045e940c03500f000c002243e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 903869478 1250 903868228 903868241
    0xe010909090501140105030a03050a0e1f050a0807030e0d08061201020a0203031e1005010c05070306290301200705010b0913020111060f0106111903050a0906080c1804 73
    0xc141a241015250400c04190040400891000500185662690704041d20f1b8611002d0081c0032803c1001498001030095682c001003080c000e10444c5015044003040000f0691804000d00007900007802084c01904840340b260020407901d8100070545044598a580f030406004c10824401c442c00060401c0d600c01e21503008c00c001c903000039501d807007900714041d41c0c80c0c20644041000003441c5140803650681820710510070015a145480c100740350500640f140610040140c0301c074000c5000100100c1e14601039401818042584022501030101000303191000c0410858440c0e4103041100100c1c00c8180103104902190541e80e0340e80d10f940d8600140181a02101150000d00c00c00402c400c0c0513540c0c16086402d4005e03200c01082042c624105a201c8400729030041d1081e0800005214081c42a035914030300c0c3c01c2c0a004c0751403d01c840030dc100c11b80c04030501d089000038000254510aa98440c050f070005001380d040c80111070030440d03030301c032214003c450040000c40e604c45034600b181d545030707000707203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 903870728 1250 903869478 903869489
    0x32001020f0d0e0607170c0c0102090907080114092707080f010621021018080601080627030f0d09150515010504050f10110706180905060d030e0109 65
    0x10b5640e030030100303070040541880074039103945010344800640a14041c5440c0541c024440303171140600c2c0c0e110068007586800a010400480d942807091181544510811900a06607501c030100150324080c4415400c07080c90300524040c3c15072205114901d80c030750444508028110359141e03040c4500400c141e1070000540c3c080c041030b00c5207081d00c121240c1f040d4080c00551303212a21006000000b0210428a11100400250082c050400000a03a4456070b0300c3e01c0341e140c94021792428241c1c0c0b098554a844002e800c0300303407181c000d0002d210440f4400d203481003100c086010040b0464440c0c5024036200d00135901200100d00700010340301c113610b107603902610b02e990303000d00c1d100c111640e1020804000c0c00c0468140d00300603c1411103401641c000c8098404498000f08160034040c403034801d001c807100320000404140030900303072600080c15042c4030610290180d50340305009904000f099a855040301ea0040d51401d240005002554590880c9005841e42500b06082c85c40541d000494000c4115440b2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 903871978 1250 903870728 903870757
    0x20901030308060901230d030315030602091c02030601030312200324060d4205010309080f1c0501090e0c1c150b0d060603050f0a03200102 61
    0x1204254000c2c08090080400795100c4416a880b1142694145800c06101603501265644400f03a441d080d4900082288281f5010030304402811180032290b0313440c3c104a601c1034001c55190603a04080c0920088121210b001c0081080c550300460341744c0c901030002070304005203410340c40d20003005c1da00111b1307150381045400072000d47c140010a5094000350345d1581c21154800101142e2043d003c03803090405001844540380c0300d2402e004000801ca2903000c007500c0130000d4900000607050040c2590240e824060a011601400181e20a540503540010341490701e0300f0380010200340148140e0764111500c58000e5541e0f840210142e0001501c001c0c4a0300e403a04140011401110317a4101d02641020501105c40d0f04070302408200c0000381180001e290904100d000502068800e001280c0241244c07400060200c0c00c3d80108400e520391071000e407152610b4036000c00130050100000c46a00004601030880f110003650b008081d0207a1100c06140c0d2030b404400500c1e41e800a6044070240030143c2d03035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 903873228 1250 903871978 903871981
    0xc05011101142701091e0c0801050405010207020a09110304030c03120501081c0509030607031107120e131406281502070b03011d0c0403151b02030f070209070c0209 72
    0x35004000c3c101e00c03684601d051858601210407078014004d9620a586c0094900c90407862641c0e50744505202940903030307441d5549000043c014400780318181c015800b0308009a601c43c80c500500940351810390002e0b01491504141b00a0260b0702801d403500598035283c4082100901c0c28111203e15003500155040c51402000185e00c0340002038490071800c200c208203100c488000070945890041802842c3c154210304002500140304c1c0d4815408014020211421300c0701c503454101381912040e4880340400c50050400c045440e01c2740d01244080700810003400a854116040d458818010340254000c50005401d0211082e80380d0b603005010390381160041c1501c1d80c902d5006011a0410100009809403407808104851038500b203a058a14450a44040e08540b084410384414014102201d514040c08040009800c0004ca44d45169480ca07000c100d0707000380d078210042d51000e40c04070015940200468070031403091b00b054030400c0b0703012140b07c1070643c0e40800a07038040c945030000070340c098113240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 903874478 1250 903873228 903873241
    0x204050603090c030c030312190e250504060602190507080f0606100e090103081317031209010c090315090203030a0c060506030a02011205130206131409040c0501110114 74
    0x42944283c10100c0c211000000f01c902403648030f1050200d0060080310f94000205502d2071b48182043c1c000690100086070740408102c0c50820b181c0100c43c0c024000d210a50707c608200301c5098a024000844040000e06e00e0400b01954451400d03102091480c0040f02680501c0b40c00d200c01c0700180060400e480c1c55064103a1216124134048138070b40e101e0301d0110001411039201d0b5040103100b20020b805c0312510303429a10303000100e030020201c01a01f0500d80501084000c51407a0169104d074480e4000c540b9402c0c101011490824010049105070789804180540035078044005030807070b904500d0108150f03800044102c0540300380b07a0041d41511000480005155011400b505001d01861042000d07450790b40805842c1d09030f0000290000d00000b950064040740360b44441e801c880040c0394440e4a2aa550205059820540140a00042d02003041100d00d4481556005e010340071145004146456681e4408064581c09014104900243c00110300d4400354419a0800d01116001c40030340f9021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 903875728 1250 903874478 903874483
    0x30c09380f03010506131a04090c020f330f0f07020601060c0b0a140901020c010b060403081b160e1519050907050d050103060f05090f0c040f020405060309 68
    0x34684050100c034410940c40031400164207940014038040c00407491a4a8003040107901d8010404804900098131400244546214903c180c102061074129449900d414060000c890362a0b2200066402140c07200301c1c1813102144418907009105101c2c01c1d4250500c006001100caa4955480b070010000c2c10320100404044259104241d100341000385965000c1d82262101c5082c0714020100d134202e00c003917000400d1101e000b40d1008042c10300180036441248142d040070003e6900f0305090354005808402c141081c050203400010a0f11001d2616145a403208540c0c442c1c2c400700349801c81d091101c0303005068288070128581040b40c240c94010b5403502d407030088808054603110358012980c21aa0303441d04125940103680c020021200c0015803400040c0070b90281c0c01448041000010400401800030510139940a1409403400091030524203900b0070465401070144541a40056a00300c2c00d08000a040c007030624042d87c2c0407036151020740e00e4201900907a0419a4000e8000c0100010081c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 903876978 1250 903875728 903875789
    0x90c15030c040906080f120705120d0f092004090206030f090c151306090608040f050705030d09170303010b182409010201110f181801062616030c09 65
    0x706415510980207440d0181f005118034000289907400600107141c0c00301004c00a1310110000340004170300843c7c404004c00c11915a6030f0b04903040c107a42040941c0e004094440611240e4055504011010f91a000200c440c00000e129001c40d0825000142c0000428000d0010380740b005080d56003c2ca079070740c1e00c481b5a500854507954a20004290010746988110004421501c041c0c440030810b4482d604c5201c4085121a0151103e00c0780150004070381c0c80809c010074015009036a800001402c2c40302c41302c0100424142c110325a802030005001d15600d2008403007486000d581c020030000d10b0716010415940c0f08110385071049204401807000160202c004058840e4260700810000821024600c0ea0b4003a0520740c428451301400068881300700d0302442c140d0824002d15030420806026050702010b00260007010000307802408090624002c1c1c8a912008558004451003921344060600c003000c4e4021001020961208089010580a40c0c8000d01030010b4043c1c000500c02c801040c0141e0408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 903878228 1250 903876978 903877003
    0xc0705010c14030a200307050d05060301060602060c0c0106121a0a060f050d062009030d0e06030a1e05040c170a02030c0607020a09020301080a0b090c15030c04090608 73
    0x1c100306410710070320609190000305440300c002410b5464603004080200100140d00070895400340300140b480d45c10201452080e0066512266107402c01c960740c9042c0d513809000b060090303041580a100c4a0740105203640e02c540f501502c10b88400005030071a014006551115043e0416155074605005910703000c1400d5024035150610141c44204030704086905600c030b00c00c0c501d841e4010038892454048200102140501d2000c03854800003800c19550300b0343c000300740035000740c0000d000241d814140180300c4884128140000c2d03e04041c0049283c6100090404601569840601d0242500048411101c142c41c4804110500d814502024503142c18001d50241041500000c5649000040c01c440c620340d000d00500981003800003480303c141c01113113040368021501d61010400101c10300c00f450003440000300420340c1d10010308151400c03600150200455402c00421a101034485050041d042480c451030955070342e4400818805d50f000b00d80255a1035801c20740001024800020000071110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 903879478 1250 903878228 903878231
    0x9030f04080d030c0e09070f0302090a0f15141207120207030305042006040e0c190f0e0109080a0213180501060807050604061209020105040f0602160f060c0b100e0c070501 75
    0x144d40030020b0791810081c03507207983d00001d04000a413606118024540700079210341009400e0485203400942c0007851504035505110304c5010401106104000b00308840100d8101040340c08030340d0044582030306c1482220b80e0026258004541040e102e00180f030545011030301c00315150059890028060902a1816103400c103c06c18082e5802d107084034124540d2800030001032405d890015031000d114401811010145014401c00402050070403000d03012180a60701d0310000c0c51076542c06800009500e00d818100044828180000100012000c4940350129465140c10b0b01c01c0d41c0304009005001e0701c2c404642c4100740d407a002c101c01504084c0a0360543d2080c0c5042a80b1442407000501a0340700b40c1002568040d4240c01c4100140d100070131342c1f801031624928254a44e981700c0400b03c002e92011006a019012082140e641840b28401501c2001d46c1c1d0010285066801007200020010280c140d01100340441c6840b4100e80f0140014401481099402d02e030044c200400c0d80c00c00c107000e840a5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 903880728 1250 903879478 903879491
    0x20705010614010203090405041a0106022415010c060603170a110307050303180c1e0f0109180b06090a060224040b180a1a060109080102030f0f09030f04080d03 70
    0xd0b0400380c0d41c5801001c1a4025402d04c0740c6901040054400a0410350701d400e510855902c132082104c000501800b0540c000b802030015079000d41008002880340c626030200c4413400d02000741d04500c80c211011109280500c801c1c5000d062000007041243c0c0004e00903100a41a950303510005400b13441600b41c545c81d401f821034a00180d540c0c032031084880c0205503400400010b8240c0c0000c2441c00c50040c0d0020031100103103200c0d8046a000125900c010000c941d40500c40c0501e1300c0d09111000b41c01800381f0b00840e81a1421034084509401e0076454400551114205040381c0c0310101910101c05004080d0950b4541d10800651207801b201c400c0000204410240f002494066000300e00403030b0301c20311850803a62105240d8544406265103584135009025035039010501c1311520b20140c4035184030244450600c10000342c202142548035a505900600c10405400b400035441540300401c80312004090b5100ca01c1c0c1d5046224a00410703041c1d54010030040f40d4104006401c80d942146d43c0c400300040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 903881978 1250 903880728 903880739
    0x6201e0f031303020409210e0f120d2106030b101d04081c0507020f0c04200706060e1f0902090f040b01110f300403120e0901090207050106 61
    0x280c0c840c041008034802c0d1055400c20060130240c0c480c0c1005406800741c118150506001ca00021403818001000100c916020340750718600503240c850369080c02c40d4000c000c0710300311050940343c0b550021a0030030b00034004804402e00911800804103090051003c0120136160324084031200829111418015400307440440c42c200701405007551b600d005049280c2c40e07507440e510b41030590303c0400425104403510303c0884511900340202c0b806101242c029000050b981c191451400c222406124442e0703080080609030070058480d00440402e0301c0422036603c200a080203000b4110691001000c406c01d42c08100c1c0c20b000000b10403d00c400105688a00d081d900c409030000c0c0d025030441c403644100c120042c0001c0345400d5001d91905a410b040014648120510880c104085154400c8103600411040246420b0441d0000001000c42034200c0c8244101d40c000c00442c006c0307001c002c00030720003004684200b07405140000782840d001081d05c42c1940c0c48683e10000f0b50450201100c03c1d40c200300d8040741 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 903883228 1250 903881978 903881983
    0xb0a050121030903020a0b120919030e060408030a09081b010806010503040f08030a06030b06030d0c0305031801292202090409060903020f060115050406201e0f 70
    0x1280d0700059101d4003864003410541614401e400304506011888000200584402030070b44024814145890b403120380f034a244640b690320091503a61944c20103402180103103240c00a402e281c98146c508150300d181c000022604034480ea0f001000684404070f0701d032844560081c51042526a80415104595002e011044000307051001c02070114800900060f40e5520a0000c2c550180c094082c0144040c6552140800ca6105580038001951603003018024070110401c03181c1c1085094008041c1c802032080c1c000c2017064030000040402c1000400f00300c503c0448070f03804440d40510402080703440240f100d806100c000e4216070214545039200300388514503042026081d4001c81070901074510a0b505540d9009520400f02581d102c0e90b60b1101001243d032512a480a262003a0000c00760391584a103064503142c1c0503400510400382600c040500320782d200c0180d40c00c03903080b070030280b0100c1c4815204000c0e444002c0c010401d507115800c5c0420040c0c200d803000d41503407880d00090b50310003122030012a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 903884478 1250 903883228 903883231
    0xa050d110c010f050a0216060302030907050603130228090606091e3b0403110316020418021804260f070305040302060307050705070501030b031f11070606030b0a05 72
    0x140410040100c9418060013039000300b880b0b580d14415642d07203100241031810001a01c4d005140025400b004102c92103000300803d6010b06130440e089425860591a4464507a0103940005e0281540d50021801540c022401060a0312108a8540f54070b488440d040c0040c225032040c0c0c80010103082d400a025011440d0042451202c00103440141d4100f1803030b66009600c03001d000d08009050f00d59010061704c611000d40c82c1a81d88031102c4194281410002c201d500740c0f03104980a5003080114a08020035040d01c0258640c1c1640c0100755000340c60741042d4441080742000c0c2d003004910107094902182101c409124601c120003d41c0c2007104000e100c695814844940021803004201ca11901c04e900b030080d0601a1203403078030501d02071b02c035400305a1a8000b5105000070890220301c4000304601400300d400074217400c0c68100f11080c12000040c0d40c0d808440d4989100744410385080e101d46001d6044075243d4205100110f80d241c1047c500325000b840d140c4402e4070525000c1c004a456000ea601816 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 903885728 1250 903884478 903884503
    0x10e0106091a041a04020d1e060b04060305040c05040509031215030a032f03041a090a030b25051c0501030b071101061a091306030b0a0b04020403050a050d11 69
    0x2141c1030403007181404010140350040700000130225000001903600c6000a010082c501480031400402e94607140c031b0100300300780c640042181003041c1402030302112019901103400901d03011416480700e00701080e0300c00d45a040039401c1030820041055442001005042605200490725901d60748c030443d5a0b000c2014092080d40b6822103045100401d128043d040c2440c030342141d0b0311504004002c1c9061000c0c1c183c0300341901d190404202000710030341a082030b2a1000004000620f4032104800003004c005007400010207035550600030840d210342c0c050100c1c2640c0d200c1b510020030043d400f0000341080d00700950b210466140c01e1580b481c400d0880c01801d040b04c2d4000c0d1040c8007078440700c03001d40d0b250083d40304003105596110310001d80070314040f07000540c41408a410583d120345200a100360700030b4a401e100d14007810844200000740036041c9290340b03c401c0d00e000203003c0e00314400150280c4929400640790f4410946c0d00010320401044030a4921100e803a2a16200703480854580c583c150340f80300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 903886978 1250 903885728 903885761
    0x1b080f061f2102130602061b0307080c0c16090b12520608070e010e13021c1401060212250506040b010501020a051c021e010e010609 58
    0x4038a44500404400c0d00782d468000d0100140354032041d110b022600000b80302045250b455104001c00c98040c0021500001c082c9407010510701024202d204a10015200030f0401c030068000911011900c003c2d10aa0000b010540d882c0010780354120a810942e4050035030803038a4041c3c8485c4c985013441451500c4a40c1e1030140020002c0080800000c003581105040320010040c81c03130058601d00600400ca00b1444010300a80a003003925681d5480c8080d0445020701508000b0b001005402542c5401038960910f000e040c0001e04001080303450007a0703000c0340e04035070001c030b001100d903000a4003032002d03808903410820552203880c1031101803940a104610160700881d07103d9442d40b0101c00100403e80c440c00412034041c1501980205201d0001002c0d603c540011080c002000155000d490040000744010501c081c030a855003030301e91450034001d2204030011440616451300038086000d18003014084000a442c1c5010390502a0841110001d1a54a821070106012540d0700c20025212501c00f80e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 903888228 1250 903886978 903887029
    0x6010504090204020c0307030908190b1929040b010c020a0b0f0712030203040c050306010b0d02130f0f03110d081c11030a0c090506070819031b080f06 66
    0xe0000409036640141d0300540c08020740203c4150810003064010300ca9610300941c83d18114507a420114000300e0445e030103074980300800114a8030071002d50404040c510042c0710640c00f111850050040311902c19800445071003082619000c500c0c02d03003e04001f69014030140d1001130044400401c0750340000e502c10526841403103007004000245c03903150468040146455803d8898100b21011103c1c1c603800030b0b80010400081219902e0180020081079009010550400c14109660f00840711107401207030303011540c25603a507812842c2000038000301c2140c0e1005910b40a04d010440c5a5010031b407915140c0c4507a0300c2850401300c4c0c1103443c3c03039045444141011000664000d800f0078041807075680644030003002d48031400c000021802600841c40c00150000e00c084060300c1d900c000d6025034858001800708901140400f0110f40c2104c18217405841c04401006081d0000c0c01b408030040320f40c05201c0c1d00c0c00d9101e900900364500510200c00c10600c0750f41c0710340c20010500c0e0b4200460184840e45c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 903889478 1250 903888228 903888239
    0x10303021903020f030310090e0c090a02070305090a03030509150c0c0f180c04091a10030905120409050103030905100e01030209030118080315030a03080105150c011401081b030601 79
    0x1810308001d034400d106070b07010040480c24803880c640080d500201203070800307103080201502a216203c0e0480c40107010f0240c00400d04001456143c0007031880c0c5050350001440c008041c4500b00320346d24000c0c000c2401d04001d40300d0800811580000405034051500d4654030b00040115005507020340352a00c001b0080010300c9014081c0403680c00110542200c3c1c14401e00603240c1d1100b41c514400d050074031083d600c0e1440e0802c18001d0341c0c1d0600b45002c0c0b10b0640c181c01401500c1d2030301d0000e4070035513606000c074924074030380740080c40d14250102007200844041400700c1c8014032900500d040f07038080e070ba58450383da44843c04c00c2401c000040b4070320049044100031f8402540641c0240c40ea10900070700008804d03294013a214070250305880212248030b80042040102074140d100c06615400035002410155450390b000f410501c0c041c018640b003519404140d00c0c404540c03400b19000540c40d0320007130104000034124200c0b018000e004030705090007042c178101010f40b1280c0c0f80b07416820006000b00416441d0a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 903890728 1250 903889478 903889513
    0x1b020f0703030509060f030f0723070f020d12030905010b041803030c11011821090905040606170c040507050901120506040204080a080310061d2101050a15050901030302 74
    0xb15185c3c00031001e03c564070ba45014140510720945407582022414502071800500e0312250780c0e13000380d061000200300404000100c0c00c2c0d50007940e1000100100048038000500c00117074010380104800600390403180015410f42107892030350700c180f00078000b022030001000290b400345c03003480b031a5240d0b0144140100e4480c0d00128042c46050401f01200712402144034250b80711501b0410034501c0072549030f001c109030765200108100700041741103c0c182c0c1420b0b0003417501080c2d100382031180e610740b030100f014002d045e40548020664501c020a0084012000507200d41142c0d00c0b0342d105510b80000104120f029004654060038161b4030311403504d5215120600500c0054000c98209a0034400811107442c100640030545001c1c042e410b0322454203c444160707103210b40d0020801c02c006030b85900c1885032211032240d45603070100e03656603120021031003180b45001d074442e5060f8158240030a21800805962110300a10704510441421548510900ca1a0002888028016072203000d25a0f004540f5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 903891978 1250 903890728 903890737
    0x1206040c12051801051030030c1e06060503012319060e0a0219110a080f071a09010f11041505040e04030e040f0c0e0405070e131b020f07030305 63
    0x3c0c840c0c0400000403403001402c50f002202e40c07032a0140c01000500c4050741c140050400b00c2c0032064409203418011004a0707885105c0340009040c416007507641c4003040b88034092141d106d182011300c0011519141010380180206101d42c502035440c0c0305422400e8403560b5007000068481e141d810032103407a1007548505c10303e0300c3c0b00110030780d9a60b45c0d00880d00703a0300c0a0015000e610034203009030302da480814010408241401e0402e0a005043d0508880c426010a0180c1031b41c0d00001681e031078802d803003a0095a0701c41c0010040c000d8500c107461010800503613242c40c0c054110480200100d00c03050881074103c500d00c054260816030240010450717050010780c40b51101249141c882c0c10f155544500404c0c0d61400d850840100b4900c11101c4400d0400e440fa18003500140e030740510540c52a40005171440482d00d078143e0203180c40d0f0001502650064140495081014214501502460884600810184074414120300c001a42c03080190701c00501c4414104d40d01d0302420300301d469030b902074505522 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 903893228 1250 903891978 903891991
    0xb060306030d2001061d0f07120c03181520120c0c030c030901080709061d031c0c15051009180c06020a030905100905010e06040314031206040c1205 65
    0x21030511105503c2c0a009100051075030040035250300d60944a03001e0004001048007090b962041c0400007034642c40025000c074411a4500082d00820912003103000e45074929074004032032200e039642c0303040011505545101c040301810401240d60420f10000c040e41c003020045030042010300000715007291300710145402188030409640340102c44019a402c6030000e09200005400108041c072255800420584d0303c015149440c12145007003040c09400da240c5148111050000410680e40b203850801c00100c0306440200c40015003281031000915410020800711804032100d00808403620690050500488010085080d440d08100991004140213003d802025088800b410045a0b42c0040309002e840749501410020320507080203021010b40e0f52066001d58245480078902c41d40c440b1030842911000d103080056501c2480000c1d01902654101070000c2c0d036002d81e101c2000e18000b00401e0302001a44a07940165903090400c03041700d854900040c00b080c0c844a00704c60081d0716a100903070010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 903894478 1250 903893228 903893267
    0x80d1b0f050d0f05011e0e160c0203010603080c0a03021b010e01080a0f050c0d140421020309190e01090e0a080904020c100e010b06190c030c08030f010302040b060306030d 75
    0x1401d4401c043c1654000c0c0d00c4070700180084880c981d081e0b02020003c0300a0002c00c4148402c130304200360012105115880d040041181202196045580030f42080e0000d607006031841d5150301c1c55003c82ca07111242c80320201c016101e01035029030035800c10381b035070007150344142c49610494604c0c038015154004c000f032151010684c0d440340a11b2000c3c1030b1240d9030060345580301607034603081400403201c221489400c0d100c00040d020010000050b0b5080402081d9980042e44110314034542d010a03407a50140003900c030307030121049010b09114166004c0c000b0031070b540c9000d448044e981e5024001c007190b10001043d00030340c03c501c42c2e15001c114484024000058040c000600e4401c2006125041480406040030155141c0d500b000a009090185601c84542180c51900d0f0002c035026181100515076140380512070442030400030725000300b49a01c80150030502e019560701d00b10b2000c5008503002d01040f4480c41c640410302c105170401c0710030b0300d11074100503006000c071200b035440030f517401c002d204606031401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 903895728 1250 903894478 903894491
    0x180a080a05031015090f0501030b09010312030603170705070f0602061f0504090308011a0408150601020109020907020606030610081b04020f070303270503040608150d080d1b0f050d 79
    0x500c0744e0090304ca40071442d50381e00d10707116040845842598429500060406040c02440f0b81584c2e2500c90450440394020a04640d0341d00c40c82042c0c01a01071a400030b0180200c15004034842039901b0005e0803058130030000e8509140d140c040b1014212524081d43c00103030710810000c1c50120481c0a01c03c1c01040280c3c14540382d03a619000942690240c440c02c4000a604a0041207100407030460b10300c5680f440d116907410a410050416901c4c02d030f000c1c9440800c003401000c0f403410f034000e40c4010269078001d07103280035610f0040c101a640d48802d83d00b0602134030611002450915141800e80141c5460700c5c06488070504078203001529580102d88241d10a5080110960882c8213000810708144030382c8010840110b4000b000034400b252044071803110405804031000680040101c03400d4031081c0c24050510340b00c000784000040b080960b00340e0001c400f00300d40302c1406048009044010800740090181300600d5480e0300c106850f403501180410401101e240810f40200c01400703540c02c0202c40003074072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 903896978 1250 903895728 903895739
    0x30703060510031506050306030c19090207051c05090108010509040231050907030f12051c0b09061009060507022b031e0c0b1e01030b180a080a050310 66
    0x120511115a00441e0703982013000925485500004010043d030b00f0050700310f01c0d101010030b407900306404031180f203030100c0b810000506080305041c1c8060310b80e0860454071010280740881ea100706401295425000d007001e0071050510520403180c908806079543c070943d901e0102071101215000c0c108a0b440f40f41d1228034441e82d541c044941d070340ea80c072141d0740900e0780211042000440d0f1002d0b14001458000031800d002282c0a404100d01050740304850b003070303001e84088041781c10340a00781690490301c907001c040c1e0220038071507009013031140402c442214054440c0010060803a0a0ba4840e5003c00c0ca90348080180c0c45c050009807411034005048018445001b9641c54140080749416007031065104c5194028182e002c1e00002000307505140f50810b00c0084a4040c0c450b050070400140580400383c001b0703454128501102c007200e00d03000801300c041d503104d2402c00d18402084840340b1040d008404903c2c0110f200080d100c840759000745002e880e042c041030084903e0340c00280f5640544c481420005903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 903898228 1250 903896978 903896989
    0x310090c0e04140a06050d21020a0c0806070e0f0f1002010209030f151303080112020a080a0b0105011b02060412080c160608100b0319150e090d170703020307030605 72
    0x300c3d4282c00302072180d02e008000c4104483c420b4002c6400390080d5003c0078001180101c6408801940302140c0850b10400310b4200e142104004005040c110050000500940c0005a1601481c1261900742d107030706040c406c0c041001e0450b00d03400d41c4a0b112251451850030044200d08108010344000741c0340c4022080801e1800010a40d03840b0940c2c0480380b641e85280340d510707105070800c0c9500250341440104d0b03100204402c0d0103001314003203299165801021540c501c040c0e40000c08603e415542e001c5201c0c28010000d60003440342a020079010f0404140345e001c003441c00c01355603900900e8141424207003440c00c8048082008100c0d8034031004c005190054104010391220b840c1411458880a82807d000134109880a003880c04105000c0d2f00500612090000b038035807110100c00c030100440c4099242f44003400060325401c3c81800d1200c40810401d6000e107a5a108a010008490422070510b030100c81c0c1d0300e041450580b14241c1702e004249410f1080d0001c40d042401c07860080f85071911140002c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 903899478 1250 903898228 903898241
    0x20f0c070f060c02010203030f0601020a06060605190224040609060e071806050a0b0a02011401090b0117040302030a080a0608010c030507020d110c130e1006080708030310090c0e04 79
    0x9a4940c0304010400100181c80355800140074945407042121041d036002035560700010303201401440d542c100041099108014410100383c0141091040560321840602154003003401e1103a140403602c0030025103400041d11030300395a02d140480e090a00c4000c030130024260043c20803688140c99020030000304140e401401d0040740340402801c2598a0443e941003000d182034452078107241020b008200c02d030b0b520700c1c643c0c00302c0f8001c1d20815580c010f01070040303004107a441d00b1420f411804a001085a0320568041c0301c041c442a21039540311503030700c0301150341820104c40080c010380c0f08004032120207100300d40064204445a0010403250b456608560035104071406801c00130742e603002040744036581000039825540300b40c203180070765034080d9641503221001d40d5100c40c00340c42103002034140f0381d1070381e07120701c030745000c0001070300e031400589102200500340c1881140f405202c3c0120104142c80c000c412280125800e038030075501d461030414400041d12444c241c0c00140300369080c03520581c1c4c40d10b00484 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 903900728 1250 903899478 903899497
    0x4090203100c0807030b0f0906010309150c090608190e030f07030302090f060313061d0f0a05060f131101030905010221010b0a121a030d0305040314090d15020f 70
    0x102c0e2040d40b00d007004240540c0103202908041c107080484a003626403a01d0418030313103001c0c0c908031010b42e105401031b030140c01c0c422030084c152111884010707400a00c5500c201062138090380c0300c0e491140d5074079045404180c10390b007405025031581da0742240803040c0e50003003480034480800d40c0c0c00c2148130866010581c01058081d030209400040da0225441c15030040d61600104403192070660030450200d21002841c2e0320300a0010340d43d12400d032a020100320007420100c5900085600414040c134085850b85241081190701d1b02c52007002c99107802c28688001e11a50682e08101e09400e42c80c0c40320070032000030b0b94035113052503602e00989020600a000a020041d06a841300e02c030400300e04020855050b059000d0b69481c401070006030555035018030010fa401000180104488080d52841404007124515041c0d0500c581c0903a4481c25400d074210300d00ca07030701076142c02a0302d149610606441d4450028150b82c090000e401000025100c840d054640042d0200e0060a0108a1100590303680c411900c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 903901978 1250 903900728 903900731
    0x4030308070e040207111e19050906011106040803040606031a070e0102030301060c0f02120105070f120b010509010c11090c0d0b030a08032205060705210903040b090409020310 77
    0x800100ca90403210a1890b003805030340071441c00d9281c0c0c80e4890400021943c0c00d00c24042810603950507034464101500c041e40080c0070413000c4654907a01d00080703069105980c0110075000c0010200e40c0202c00011846000e14041c08081e6125540d40c03800e07601c001c1049520a550f890b021020900d11342e6101c1e880c40b80702c160154030b03042540c0050b021010581595046500c00c0006000e02c0c6c0d40402c804002a038484504208001284001944580c903596501160740c80d2004100105521010b80550303510380b625040041000f54208205890f00b6289160106a0400c039600c0c2c1548920301a01400b80107251074034414a02c200040c3c01b20030b0a641e0243c1c0c0d440c020428006201c0079100718240850304400030a00100d143d0794032226400700405c1504081c84c2461030045503d00100f0a094041e406002e0707803031030701e805000940150090b000c0c490b01080200102c3d08922074200c0214050b400752002942460318040303034088141d001c001c5094126450b0808140140c400b085016440c4a11000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 903903228 1250 903901978 903901981
    0x1816170f090606030111090105090f0907181703191214090f0106050f2403070305010f14030a060c030e1c021c0c0b041a090f010b04110301140a030804030308 69
    0x70140b40c4040603240c2c91099140100030424200020300301c03015a0400c0c20610345408440300061450341c120180c07640c0002d154010003c000354080700d0054005058161030081d940c0fa040c4181c50030b9500070300b072440781d0300c10010206110248075100000d0380080c604200b41d0b00c000501501650680000d007a00305414078103009500500780280700a440031000201f09152808000856191410b00c036640509805000d115080030880c00d0103507450540740e4159a030b41002038001340102001d10074101006240300001c150411520881810403900800a1845e085c05441d00001428171400b0300041c550b0319604020100d40078000345c03400358441680d10b101c2921086000e401d010302038000540101421310140180c80e00107a003103402681041640750030307a41d03d20380300c00da04e0030403200c0158042036102007112800000403c60701c130030700c441c000b0710484144000384010ba4600070402144035800344014000a03016032588840010018803114003103599445d9a04984c0c0941c2050b00002c02e101c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 903904478 1250 903903228 903903241
    0x18010525050c0f010f1d0604030c06180b0c1b04020c07061701060816030f1512030306050108100909050a120c0c0e130809010c050d020312061816170f 66
    0x900300c603d20401c1c04c0c1500c1c0400c640400804840903c0b980c3c03e6007411075050380845403600401d49014650081516001175103034440940082001a014460744120002c0071503660011410743d9a2104a00c1c0184200030f02c2002180c5100301078502d403500a0f6087c009030481890030452503005200175111842141c2c20b070071400c0b81c40d010581024050201c1740080c0890041803d5010300100000c1ca00082d101c3d5002d01c0110280c080e410081a180c03074004e80204608841a000c5480d0b94400d407002c00816a5460040d03070301000440d0811030304541c0b00001c104110198018016152007003003035410316440c40e6195181c8084085800000601c0319804034100044000341a003e001166007131403003440c00d00b24040340d4121018000f4282d46000c10440d83c917901030042e000c0c5882e40141038038011415400000d542e84c0110b122400b05280980101d083c6051031f250f10880324112180c0e000c0560307994180126181040d107141000c0141d45003030644400b5418401c140500300d80d0b481c0142d10b040c401c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 903905728 1250 903904478 903904489
    0x71a1302040f14090109050c090a0f05040c05040c0f1e020c06130503070b180d0203010b031c030c1b020f0a090608060f01240f1b0803070801080318010525050c 70
    0x100a044107a06d0404450702140b000951090260403c075100c158941e0348508140252010b1004480d0107800c01b400d12040180703001312002600c000b62010441d030030710500c040b6407400c030b0612140c0202d90340c0d03203030065001071440400d8000c03502d50048440e400c9600e80420f40942c008446964240300c141c1051000e4a010720104008204607a04281001000000c0380c3e03000c440480c036680308400c05410701e01152020b40180840c801c0040a4411280c10000c06003600505030415200103460403102c9504540034000110250111851501c0c011150b9800d04c0703078104003880030350380c0110b0030800000d20010a014a030082c256040240400e420402c059825420060300b10340d43c2000302c00c0d60000044840161401c11450502d8014995a050b6006441040c01080307030ba4081c1c01d0a10b0b4090500043c10001c41c020005580c442000d0303030762203550944034040c622544404140c502ca0744a42e0b90303c90009403805001101c0452076245400202000000f9029001c80d0746070041020702d132952230325 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 903906978 1250 903905728 903905731
    0x3230a0c1403030f3411010302090d150902030d0207060909020c030f0301090e0615010e13020412050703020a0501080601080103030e0406152c0a0501051c050403080f090102071a1302040f14 83
    0x4101c17011042006170781e03844039009489100c103410103a010079141e05903a26900035202c8640c2214006e840002112140c3c00030b01002e800c02d038080d10841034060085071000a481045400c181d6801412a0621403010003960042c540380c10984024000564003456402c000d500800c2e48100004018809a2285013486401011035251020b135036012009a6003054200d108181c0c12502010381555003034000c1e00a015642001c2780440300d0b1480300040040000c0d0a0003501e00890f00c0c1214266138000445402d2400c0310700b01d001800220040001a003d0501034500860081000c00c0950b100d102e0840340408004854000446600141c4080c120018040c40ea0301d90440014400703450460128100c40ca0b603100c2d550401800141d1940760705016060741c010321039038150501550030304c1c0c18010180041503408028142003600802e83c101303c1442160004c583c0b049200310111044484114590b4006080e0011300f0b440c2190000140d40300d2040040c0070b00b0f07818000444424003680d009503142d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 903908228 1250 903906978 903907057
    0x1c0309060509090c070c1503020d0f0501060525120f0e0909030906070503160809090f09070501030e030903070e01061d1507030c0b0103230a0c1403030f 67
    0x40420105009464401c5041c4e8440c406118842e991100e9252030302564100768020340c0008480d000c0c400f01554550014114035401030b0042c09890301c00100c404c1107407000c1c450803020650421a044030390840d2040d034103903001800e81e0009810130300e80b1170b042c0716540300d403000d40000c06c01c101034070001340c00013002c030300e042c1040d1880300c1c207860802c503016528420280d070540308800c049256410408104110703280c071b404207131040841007410300d07050710740d80c0220081c1407041d4001f4001541c100c83c940000d030302c0307000044020141e488c50700780103500801c3ea00a500b03400b0b0008204040168030104030500c0108480b0f10080e60b11344c07408000a201c9030115001000e41c2007607a00c41c1000d50344030380b00300d10b2070380c9140783c0a81e1300d1106180c00d032400344400b9030003007103401c80b0310002081c0038662260003250842031a4544160b0402000c0c2c1e03480d6001d103040102a180011418480f030000504400e62000700682168600041155290801d802801c03500803d1842c6464907001601d01211203105c004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 903909478 1250 903908228 903908237
    0x3151403060c220305031b03120112020a0b181e060f16020a030f0c06030905031209010f06080c0a17030313050a02040c18080c0607031d1c030906 64
    0x6018000251141000340c40710030000e8000c00c0072141900c0300d8510f07650240460700050b4515580e85851a2a80c005400c010807405902a07032507089a00401103c07a554050003d2100aa013414400501003203109000da070003c0c4d1801000c18101c006030f00406084c244850003071403082d50300302000312140d5540d03202c00c45441400691590b44e01e0305001d65880400ca03c004039280c1c40740b042d4940080c6103680c40654404e0100304000b050061182d03150108a000e00190541681c49200581c03d41c1d0804800034141d038000c2180d0782d0505442c1e0790080e00200c03010000301c1c01180036007039401a00d603550040e50a507042500300703188504e807492410b4000c01042c078241c2490014480840c0e02c2e404014100003442e444403540000b080810300c4400403056000300208900c0c64a00401403284185003060440078500c03103c08583d02c03000094030001c00d40024000d6140140c150340c103d8800300034815804102d1144004500b0301e41d03d107540d4000010540d0440541d00c0301c1802c0003001800304d60701103024803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 903910728 1250 903909478 903909509
    0x19020a0c0c0e0f0a112502150301060e030303010303051603020c090127050903031810050f0a0c090302030c041d0607020f15042001020f0d02100b09060a050906060d020a0315 76
    0x45070403006e84600c004810102012881e901e07000180103243e046000354400f801d442c6104502c3d417044091810303644540e80e40841d8900c00d80606560b440280000341c0481c0c02444101414000d54040300005880386c4103903050740401c3c10200d240010203070040c0000a610000c12030f00800643c0c0001d42d152800d010a1003036051000c042e030b031a0b12001d002d07401c111002003d00191001d040000c0301d81d10803810800c1120345095060b154000506841c2c3c580040d040c034440c81c1c0410300c079802c2c01040da0380040140032030003100380400c80242103110300740510104522522182040c03c1c0105803007100b4903005400c00f031540310411400c0517002c0c29121079090300d00c001e001c089403010000d0a0070040c041a01203e440c01c0b040140c0c81d000000c5590706003031080e4001c0e494640d501050403801d40e6643c030003e0168003410740402080f0001200d005401585540c41089a0302d410304541e0340001000d0030080c58880e40303808010582c0d100d680c910000c2a1288555410354505c024220020500000d58441a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 903911978 1250 903910728 903910751
    0x3020405060d180b07230306130507020c12010c030c050c0d0c111306080d0c0305120c0906070804061206080c01082e09050c0319020a0c0c0e0f0a 64
    0x2280039031148070054540d00c0f00f03010700c4420446034003200070360051140c454034503140c18014801040703104c060038600c4083d070300e0350380305506079007601e000348802040f4001019002054030004d1a0040000341140b0401e45841410303200e08100998081c000d400214403200c0c0728002805850f880014002042000c100c0a618488086000c1c0005422460042a411310504181040c11100c1c900c1c9944400e12a6a441e0201c00b26030040c01164070602c150740400d0395281e41641c3e0b6420f11074000d00401c8040195030994010f41c00c00715440034450811034140500403020602e5904a0a022501050005030511036a0341026210b486401040030074040e503807c00302e581d0b0b11580e0000700d0505000d40000815104101407d000c010200880c2c861a200e0221407850741d01c400303030b84c0b29100301549000081120082401c0850744070780542c840c85c546610b03001c03c004e8000d41c009007104042049c6045030600083c0c6411070b20005203d031007010b404604180420103981035001d4540038110b46040a102c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 903913228 1250 903911978 903911989
    0x1c080c190f06020703260f0a0e0c010c020a03050d020d08010906050a140109030212030901110c01020d0c0305070b0c07020415060e01120608010203010305240403090302064603020405 80
    0x40301c0e0344000096112202460280d81224a036070b08400e40c10030b99245c00505011456000340b02c0c00d0b2050074940b90392168032020044032147c00344601c594004504048946d4042d41420490f6031000c1d01002110382d6903281d050426000519110040e0400c1d031740c1d0340d1807550140e50680500a501000c22400c0e1a1800041750250940b2980c00b625541c4101d03055240c0c01004650011500985009030449180000c96140d034019a56240405e1070301078074840309a40018029414101a001400441400101a0781c18105130700110100a8200003541c00143c181e8200d60080c04804619a1240e80f14030421003502c00001240425844180e010405681e0004040070f40c80c1c2c0a0800800d4001545485400380c201c0e500400c1d0b00d5800000008200480001c1526032040c5032280560031218403035410035004070968014000494010061015103803400c001d048030a40241400c410b15520815400c00e640c01a5003229251006040004c0440310844413550003580b070b2038114609410840040c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 903914478 1250 903913228 903913253
    0x1051c140f0322180b030a0609080a030f1e1e020a090315090b010b030603160b25030c0b270f010e011e020a0507051b030d081e061c080c19 61
    0x80125841700c1003203801c0e0320144101c50b03510f41c2086082c441103850f800c141c9100c0e480081c0c054002490301240c61007034034039481001142e00e1005031151098250295040141c09840c14200c61510054500c01d2174907a03500c000c10300d01c01c0c1d0741c40e0400b002c0e141d0700300820174810f80c0d48405049420031b002c01002a031f804942c0360640d0034164407a41c070307030f02c1d1880800d2400301c0ca00462140c140141601003500c8000c03c015100b068841c9400c440c038141440c0452051081211001340450011b0051000240c0c400c24862352012468158410a542002e000348506084000c805001c1c0c1050180300040300c020b0003011031130915030001b440028080f0790402c840e80d0035440100c240d1580841c0707034035034640716034125161a9003100844180300203092660031890b100d40041803192007413000e14940c060245841510804d40310707800ca10011080c6615050311840280003942c01044a0b000b607024403403d80c48281428010140c0a403141030382410301c1d1405017040340038a80c100702040f2040011360740501c0803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 903915728 1250 903914478 903914519
    0xc130218011d130e061008030d0c030923280201140d0c0906030e070e012903070309022103040b0c0c0a03120e010801051c140f0322 58
    0x10720361034000ba100c1040c1107030201d0701a032268516140b8200400e85401035031038035000c1c00540b1015103403042c0c103107030106031403181e101c0d9500180198010450b82c0e5101141448041c140070668070810b40e1000f400883c034801031000703a0031180815102e101c0c2040345000c90141c148103184030b18601c14148000c00d10620700207040048070720f14003110a004400f6200403443d2041c0602c070755001280084c0c400083c6008400009241c24030115180d103002034141e0485080c0340014105034280f0b0034106031b88030180d08005c2014885070300c0840035a01c0d680198420445076500003500301d244e10400c000c40c0055040c4003c00c0c501d01c3c81716801c3c0c0101008a03802c640400c2c1d071565a45a10a034201c0c10010194080d51303102c0e41c40c1c00b0000a0043c1014450b46221345a038805203480303c550f005407408007082c01601c1c0c00c5420070101c01803c1c800840312240b1385000f07071901051400c048071000c1c60800d84074240300007a00040342d02d480002040c822011411042c40341c841044d410b11840300030341030941030032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 903916978 1250 903915728 903915737
    0x10902090d0203010f0917070b07030b1c112d0d05072d0915050f0a0302062d0a080604090611031806010902040803071401021303050c13021801 63
    0x1080c0d5034507004200c81055000d4001e100070109601c060009004052041c6d4809a003401507a000210316030480f010b07558017840385131700e548500030101c0042a00000c12900044101c0303d08060341100c0303c0051540788269110425034201c007040c0031540c4000ea015481889081347c1d2030308501080f11034181c0354081a540b4440020207414810701d0040c00c0d510101c49900d94651080c0007450704120500340101140c04510325550303a100040440e034810f0741d060100302140f08203000504d400c0c4040544030704010030840c103854598001580951082c90081c41e402c1d00000d4050900100d0300c0d8100003600c0a41885060511800018240560003003500e441030382d55000807410000c0700e501154481c2e1007518050b0310303071805680d980300b800a4801e5003d46413040b40000102c0400b14001c81e41901c5241016504064003680d42c01030001700c00860124554081c061342001e0001c01802d40300940c0900000e003c1e0f400500240039815450355002007603580100300b403020104540c5100e4624040a180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 903918228 1250 903916978 903916987
    0x109140c0609060f180612070e010503011d0a23180706080a05041e1103072102010c050f0613110105090901420809070e042303070c1503050609010902 66
    0x3d00c0d040c800410780550340d0007000071845e130803c2c844034402523210700d10a441d11151150074a0054490340824070032a030742c1c4000f0036104e4241c540480c0340c00b9001180c41d00041003940300001c840c803505214003900102c5202034030400c403201001c00708803804040098003908141e401d00b98010904c910050a40000c10f1300c5802050400036040841040309140802551108409103040184540c0d2506e04500c81d1044460219170036002e071440240d98000c2503144680362702140d0055440000c00382080c0e440b03000b41010810700070f070b046c081944108061055a25030391483d240100072006a00c810504005080c41070011a484402181e41501e141c0d00840d80424250021440d004c00400540342ca085000c0229a0160104a07461142c20142e174503020b043d0341d0395a0b40a0342e41d44091140d01d24403a0617070041801300e404c003007007207040b00c5110b140708142c0c0c23405000e2545158010300b02181d4050840500b04801d100070050342d8102212481c090106007060f00000d1000001802090411580042c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 903919478 1250 903918228 903918247
    0x6100b270316030b0f060907030c0504030b0c072d0201120219030e0705030606030c06030601110a0c180b01090902161b0e1305151003050109140c0609060f 68
    0x9011088003002821102e9030708601d5a41c6500d890107220495606150b5404a0504032140820905c694409001101150346040b002c80c06010b0820940302032000400012010030f00c0c1807401846a410354001c83d80c0c0f40d1715850400314501c0e100700940051205440e00c88494050020030318155030b024605403c590381141e071300000901c01c3e001150402050803a8500a5a815030020154040c5113819607100d9a1b40d00103140c0c41d050304031041503040d0401007401449140000195400c1007062400404030f4804414846c94450050350550b9502400c0e00d0800c41d51405000055081c201c0f40003d20500900400182c0102068054241000d40104040c1e40e510350384901c80100a4203d00505216064094907440d80c100300d0103040c0c21450040001181a070f01d140403030f49540c0d8440002c004400465400c06444540600050f002400e021000404214240252038100b03001d0b00b035411140d200b03458924502861740320424001c41c0c00f8451203005139079803002d071419022450300300c5a5071114007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 903920728 1250 903919478 903919537
    0x30705070317040b03090109020a05030a0b0c0304060e0f060a0605010e09040320100209030601080105040308010e04170d02130510090e0a0e0106180b0906060301050d1407080c0306100b 81
    0x9810000741384001108202d0003000c15009000e019000ba6800f40615131110103142d00d03125244401751009920030085810198208020f540c0280990340c00515107407004000790500c1c01d0440c400c40d40360300100500611400500c0350200500003400d000450800740c2000c170303d45000042014050045aa035848426810080d801065418020075601c1d050844020035000303400c9249130074080c3c4644000410815814410113004a4140e22840c6082e8605013141c003070820000c00444031010411210301410148401620200500890150b2030700d19600e103c4c0c0f9810f06a074001441801021518104140c01160940c26074001d0742811405540e089010405024082d00303036950b541c600040000d18041b02442e010341071a040310244600e501100030020189000c0e6011640040d0402c0104102d10f001c0e0a035405176403184141c9c00508808440d92410584203a11074001a00f000c84a03a88034501404001d602035081d104114000e8104909411140100c174a1880c1da840e80c408039603442c5448 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 903921978 1250 903920728 903920737
    0x9150a090b0424110c0708011109060a1b030503091b1c240606180b04170c130b12010231081b0f1804170405060723030705070317 57
    0x1144001e110f41c407404035072513080b64410b86004485015000d4089480d610600519a0030116414141e080c00082c0081081c254081c0d461041406900c800c00075101c2c41a210300d04659009031500394403458034080b07140c00c150341000f880c44a51584101c054540d80c4071020380707003817102101c11a4080250f07854002400da14200000c55000600002c51a690005030845019601183d0b9691000c0c1e0700180413850049a60213041007501041c4414484001d034000396000c12803448048803014250000412400416001030710f802544440b000d2010342450816680288400402140340014200c2c0900c1060903100f01022085244216400041c00021511028011140590b0208508065883d04503a000c050040c01074210803030035100ca00d80951107103402d5283c480a80c0071a5502d6481d0b00f1030034000c4501c149081404d100100ba0f54136100c0c060002540306003103100215280a030403000e020441303071700c82c0850b90003041600700003040070074107008485e80700d83d058290b61030049802500340903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 903923228 1250 903921978 903922043
    0x61b051002250b180607050307210e1c02030406090302120106080d030c0e060301030305031611010c050301141c03050906120a242102030a080309150a090b04 69
    0x2d809294810302500c82c407044e002d150040d161502045820205988451080341c246c40800c00a0000424040c020742c11300501023980c02c40c56105448411844c412a2844542c9400725405403c01c19005d011a9060b0402400c2a0000b14141031809000420102090100a0184103a02c1828400344000d40142c0c010340001c005a5071840810038008006044540c40ea800107542800700500f01c0c1450f00440e0f05880e0541d13101031450369042101c4881c450307808401020080e41c10030600c0c00313000a00c2000085178040d6112a56940362009460800c914054190322502d245040d491800200101c0310070000d61509107661108502800507802e030040c419000c14401c032103020013000e400d0307d42c0409078454040d45c50000c0c01103041808410004140900c041040500a01903407140384881e55000d5548002c0450700303074418982c0d80c0101608195015607807a0700c505240c040342d04840c252290b2144c6085810003058032a03484e600b449020242c8040c0003589008a6281c40c15001405101d480d007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 903924478 1250 903923228 903923287
    0x60c070306240902040302090f13150c091e0e09010b09181009020f010c0f0c0b1b010c0206042904050319020a0c0b09060706110301061b051002 63
    0x10780351100c42074141030742c558440c0c8140c801e00c0c0c040f03039010491007500c0c00e5907000b400d40d041a40c0d880c50150382e4250f015084055256101250b1070000d070b5580038210034004800c0000c5581d10107800003809081d403940000e440d00340d03241601c92203945a14281d40c1142d403062190300d89512403000035801421110149a00101800f0420403076842c10045048400c04d04800c645142c0140980042100d004031002940420001d01c0103409601c51070716408024010149002d601e06240d8a40e03600b001d4070750241200034004500c0d4030b100c4001c002c4141d4940c40200007801400c0d602c210094403080300410041c07000c400c9880648042c001c2103100c0b55051b00218180680e400c040c00c0180ea07035004480d485042030190111415014404206e8100b440d9210700c007200075500381b0740541a140c100a52107900a001400380c900401d0a5015005028014000181d929414004000e01000041d06a007000c903c0c0100018001540080c96004e2000102401a21510300340710000002c02414030740503030b01c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 903925728 1250 903924478 903924491
    0x2304031107090614061303060b04020f03040b0708010f1d07111006050406120c090905010209190608011a1206010306051801050a080d02030f07030c32030c0705060c070306 75
    0x582c550180058855144070080c07000340c00c07010003800d403080700e0101401d48480310701000040c2c680d8029080c543c070020000b508108074580d43c14482d4000b02c806817601010741040c0500c054120442a003d480252448001d903424504280d01a91008144075032850364000000c00c02880345c0c103807550f0a4004c1d020703507078081d00200784a0f01401c99070160600c56860300e50700203200710347c3c4030882d00001e030b110040b030955910740030486004160310141a40c2c40e5408220381803241c2c3c0e80071015504e100500c00d804501c40e05200b4001c21081058105000401c000032200885448030010380300307450a44a110300056844000407000740c11a9801503400c9002451134050b407248004c401411707a101600c803951801e54941000d5030313031403201e240940036030020440794028480c040001d100880c040c0c240b440341d0300015921080705641c04007003410080c0e0980400682d480b15560b0f40c07032200c640382001794100140007042e541c403410284141449003100040181d040081800004000e540002d0200880c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 903926978 1250 903925728 903925739
    0x30109020304110603060a2d030c03060b06120a0e0c12010c111b210613050c01030b0f10090e070306050307170a17070b04030e0307092304031107 64
    0x80e40041c2c0d0125229001244062074600f010400e492050400a02401070b092900122056418800c0580740032203c4800105074603d08858182c4000e61161002d00600b43c034504100c0300300c40d12060303c0c0b03110b10020051070740a0141c400d0f6280c0c00074074444002032000b04e41d20040c2d00e04262010403a400a00340a810070b175544042d1f119061032003861700d5032810116400c9200d501d03100e0350144481e0340e000003000200300e41065003001803445140701c0002c2d040704441941034070f07081c000c4805444441c00140d1803402c000042c480b83c02054402c0c20203000610806000495402c804107141d800780c4c0902c070110740c0c8103102d0b04010005254900c0d444c5003c0c03d084c0340013005880346010320fa0281c801d10b800000d4080100b220b03100000c6085001c3d03c8180660f84d5080d040c100703411072201030544288144404138000500d1179000d1071294030303150310404c0c3d0030040c581802116030200b0855460705c01d00e2580028600b968024032100f903d140b020b80da80b07510b07094956000111081c1e06503c20b20b40003060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 903928228 1250 903926978 903926981
    0xe1912062309030a020d11070308130906180b0f0901052808011d0a051f0920130e0601030813080d0207091a0607120e0d03030506040605090f0c1e030109 67
    0x4d89007084d8250b822009a0a109603000001d415030303011107600000040011440c110b000d8051000084118030f0300035901c03000b60040d2045600444982c2c1ca1050b110420124940300c1c0f4000c001f0709503041841003a0960006006900510805009203a03803a0b03248100b001ca416008803044003500810703051912244218000d2816041c080e00c00703000c044039039240044c0051610b440c1584a801003102ca0240d0020010700850f20520044080e140e158200c0098101c01c4980344da17000d12101c440e030301c000d0b610402c0032212420340c02034455850034905140081001c5030441c1900d0b00610344a54458104198000c00c070141d6011507610f00560b9180c24002d5400b08000c000c49031002c1003441300c507014201b00700c50751005641036584200104030035800a2070501020351503180c9800c00c0001ca044a0010609000900000304e0000755100c007000303200d1800d40328920182005441200701468007111003005a0720240c00000030f0750000c244c1d80c1c0c09445080f60f010f00f98100f000805d48030b5950741d56810 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 903929478 1250 903928228 903928237
    0x9121a0f0f04060e120304060c0915090303050f0c070e0f070302030610180b0c01020904141b0f070503070f15090809120f0d0e191206230903 62
    0x10548000440880c4120340200c0da8a806168501e450000ea5251690740030300401c5444c89401c03450103024000c28444086101461061303000b40d1020074945581440245121150703001000790051100300100e0003a0320015502c281e03585410710301e079a206611020103460003000200400fa1044131401318020304031500d024040c1f240e4401c16429510f40180a80c00e83c0000c8410a1300100319680c82420b13107200e2007a81c3c03006021491080000d684480ca00c2010307510200c2c45081a03034000900b862541064801c1e004840b42170007458105082500c210440180120030101c2c2c0c503100810304014078580034040f5916a0f0303204003201d0391903c1501d0400300d00300d2851030540d581d09501c1608003107443c040c06913140d45a40007021514040d40d1104115450310b100014161501c81c18443c1c9448080421040307040e100d61703441e1280d000080303030108105c0000c0c5484816003100c4000d0108180081c8441240c000ca82c4018041505800910000f84001d00c1910b40006251a00180018010048000e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 903930728 1250 903929478 903929513
    0x207060f09030c0311030d080105090c07020d02121c090e07030203070504090603050615030f060403030e1005040b04060c050f1903020d1e0f0204080a0f02010c051509150411010e010912 81
    0x210300c80101031f007065403e80024450380e038100d61840b00052403400010b004008592004108240131551a00410041400100103540c240c3c880e99401c60a40480c0c0d0181c400c40440f4546150020708100c6041d0b440d100107091071040c19004030120300914090020303100a003070107034800c01c0301690b030307040c070698880050b076141c0041c0c03406041101c198103010404290f01803105000f01501c0d140d81e50700310020075060300c4d00001c6000340c0c1c0141d02407410034000d00e0f004d01c2c0140403001e4582050b040020844454005034024040e04201141c003007481a02500c4c60301040233414034030803882040581c003a22402243c81d1081c0d02d407061680e0703d44c0c0303c510010350508011004205000300c2c04a560100e200b03d000b103181039441401c1103400200c600c120b1032242441850304003030158059603079514004010004400903020741d000c1018a03501042001c2c10151400a1b1590341d0410b03880310074420701e0a5090504010700104030164a0f409001c80400501001c821036844514030f0030300001000228410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 903931978 1250 903930728 903930733
    0x33016050c040c1407021e030a03020730080d020f030f041b0f09110f03071d0916081005060d020702191a0706060b1206040e0d0207060f09030c031103 66
    0x4180f06548100000c4d83c0b1250860301c0c141c84c212a81e020000105509640c00b0b004500c60980c0981c113481c144200c031a054826002400303990304081410300420880208001d1010981c60303203641440800b41d2515100340c00030101c42da40d481b108081006803050300c1900310f10f40000002e1203c07035442064400d21450040b804000001c6001d5035901d400540d9101d029101b0701c1b40b82043c80503c600f40c0c0b02c1968444940d0340790780303071500782d00d14254541c00c04c079400070209024a0325035a00100d480240d111100303040302d0542c80e44c9040b10f2144c000c00c908039903070400c0281081c0080c0b0544032a1044602400300102200e03181c10741c2045e100e02950280004a00500a50018102a01d40c40b440482500d2000c1020507c1d02c11248920890b0f800000341960b016881e0000003c48540110051200301c80000344800c0390b1904500344401d58020720101c1e10550b024442c101c542d65070103d00c5401742c4041c3d181c4044101380e006822030f0340c4440b680010b000785e03e00301400000c008500c01c030004000000c2c0c7c103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 903933228 1250 903931978 903931991
    0x307030f1101050108060c0a0918140108060603120f0903160510050906030112021c0b04020913033518010b0d0c2108070c0f05033016050c04 62
    0x110b03090310310a00c100c40590340310002040d400300701c00014040701d1250b80b80a00049a0b01d07514101c071f980310b4414010340103030380e550404080782d1040c0040e80900340201c001c045e5801c00c1004071b0342d203022a6007030044420003c190307660805c4001c011a07204000082c203d4a2401c51810b00026504481c4116449004e80d40f0020781c059000307600b500d4030340d00002c00060450780780c8149080d0712400d030302040340e0100000f00b260030b03000121603650a03440d010309080070043c5050b00c10700075092000b400000d0494443d280003000254812030501841c0901c059503040e003881e80041033003400c0b482010410041c2180200141d4100500100c508100c4100c000d01403d10418240503c0c2070500a02410b1000c0440b402c5c003c80d424900d128007501002d1102e102280d40d1a296603100d60400d200880b44200765060800c41c0501602000c0084c041c124084d240c48940d14104000019040124a1003c038170a80d00c50030020f100c8013614031010101514a0403602d0501e0495111056008418800d9181c40c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 903934478 1250 903933228 903933257
    0x10081213050d301107050a0e04050a0b070203070c05040b09040f14011103100603090c121a0408090f15120402060c0312012d0303030b030109080d06091109180c0c0307030f 75
    0x5d02d502114005845000b52505102150018480051050b035030b610540b4070120002d101c0d8101c00d07200b050741e50302840c2c440c001c1d4a0510888805c95001c01d10407030801d1a440c0301c40d0307a02c040b00c60300143c0c04400100780c4403161400c00180c0303c04880300181546408404214068030900070b52081e040c1c14921007026407030f0700c070540407111745c40b401820001c0309500c2800196410121501c801d4020824900b409102108000600c541182e00b10f515540c0030591079040e0500d001031160000d0202c0b2001c880340c41c1a17481c3d210b180202c1683c03030081640c80000c1025911355004850030b1449480950780d452040c0350b50150035a900384076244c1e00022050414090b904c08910701020380d15110481d680062035514120060301848400c80e40c113560310400302001582080c01429086900c0801140b0285080000c1c1c08490707a0020902e240c1c08100b282d07150658424030991203080358065400c03500e032a14055910580648101804184000a040000d02d17800c40928640e523001c03641e4580c1c1040349034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 903935728 1250 903934478 903934483
    0x2160212060c090108070504031b03140f030f0a1e0305041a040b0a0923100e0703050d1b06020c010911032b0509040510081213050d3011 60
    0x2c580a040d040d200748100200366214501e801e4010401d443d1407800c20742c4903203490160000c0407181010102e201c1600300100007034078a5002445410102070141803410100d420f881e485189054505107200180f5941c1480c001c0c22a8021524820340129041c0a2400f02038002c1c141030728162504181c00f9840c59078a60761340402071240e0341c000d55820503903c0f2008200c02404180000300c0360040000c810118550700b0004101c7c80d054054003c044c900c00d4188180210707100d101c1502100e03080140140081100007545440b14500b40c60400051202080041c0541245100041c03031030b400015901000072054204d514400d01442c5c0200650168408141d521340d800380142e03054401c03151440345000055440180611164100b56190015400010f4102c0d0402c842c032001010044c3d00500100300100b0040000e44800d08030f891a0400ca00700100c2090b10340d1045900ca409030000002c10840d40807902c0f0b640103c0e46184e00d0002030510baa50b2132060511150000140b1207200030302000000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 903936978 1250 903935728 903935731
    0x72d0b03102102040f0920040c0318080f04050a03111009061b2d1101080408070615090f0509061026011803110d02070f150c0203010216021206 63
    0x3482c040406403010ba0a100251045005c0c000c0c0d030b160303200c3e0540042150505000c21301f0f841180341a00c62800131003000100c604184161040502d0309402c0400c140c40d42a00f04c41703807a0400f10f825181c6005c2c41d0048200e1140750000d64211407520390000800031624030003071850b00c044801d00342c0080500380031104002036203d1000041c08001c0d1414504511901031240c41e4022410040c41d5500684843d00d00700084010820a900e0707000f1280503c4008403280d100c0b0102440e10204901f415119004075000d5008050415684d564541101560302d000e05c41c01400410b000340105400075813603000608048070302842d00e004c0d0700002051480074101d48010f0707800b10b007050580030010892150403031302a060041c10035903031a800c000854040114050002c2c0c8260f03940164801d41c0a0064103100c920714001095601488082c40820f0a101c4448103940410196016000b0794440c21140e000f9107080280d015440000d4803c07440b1701d80d07000380d0320b003500903211404084080294039903034080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 903938228 1250 903936978 903937019
    0x810150c14010603061104051306060c12030e0d121404030210020d0207020a0906080f0c01020613050c0904080d150503030a081801140402040506040e072d0b0310 71
    0x5801040000940500100d0307080c00e012100000300306450f0b07aa400111902c84280a0101502107410001c0707140c810045041030301c02c504c0a12000b0314090014040d00403134130000340f610003186660b01c0e0892183d40007603a0308a044040700c2d01d085240d10042c0442c2050781198038505d050114040040f8000b1a00602881d410350050028224400c102c03002900403080c055200c85d000c2066102503a5006000006801c2070100041e00074a814841468001c134440c07a81c003250041c0500c030095a80125145900103215000e00e03081c2107444c0307895400c0014a014144d802a144800d000c20b0107444000351101c2484600e00f00008034100103900705002c2c8a200e42c0c2d502d03030300c104a824070f418491000c143d00303c04c180e0640b0001300310840c425400e5030444440da00380c03607d19a01300800d6103007a01030b803030f0801d005503400c20030382c3c6d42444442c0d144c40c1240180030044039000c2c4802040e4641000030a020202e42e468404510b89407454051035034010b8416402250407120007160000c03140d01082040748 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 903939478 1250 903938228 903938237
    0x5070302010302030c0d06090b0910120803040c09140f130803240a0803120a02030108030a11160314120408100e01140901150f0b040b0f04030210081015 67
    0x5165a0045020b54001040c65481d440180500c02da14079044c05044003602041d100418014031020612080700c00040c4102d0515071801c80c104200300c0e1340d008041c03580b03070810291030741da035114200340d0102c480301da1041c20751901c0c00031040c00c1d001ea42c070020390044000302c614001c20b49480303003481400d41da43c141c050301c0000200081920702c003101905001005544041c00d02c0c0005150011751102c0d0f80340d010340d4481d00700148400441d03425004041e407008011208500355414141d006030749000d1003005400340710b00840b4582c0755007810803011076100750f8050706600b006d449291440d2060065009600b842c441e610310081d44400c90740984041d10001401803000181c10068400075203030b0305080308515569850f03510381a08403440801d120f00507030000820408e4081c40300c04c010b03c1c4103905c0101c041c5442c0c1d5050010b8441c403002c503003c50f02d0015429071907a0880c26030300c07054880c9520080d4427560010030905081d03000081a4400c0c1d0000f814004030995900c40c9281c91600e4402120004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 903940728 1250 903939478 903939493
    0x21e0a020d030f060b03010f080d02030f04181409010207110904020916050d050a0e0d0906050a0507060209030303040c030b150907080405031e03060f010302070f0f14061501030b010c05 81
    0x10b01c2580700341400750361588045076040d0b070f6103811201d5034001e030007080800ca80c010051103118000c0084c0d1300004058802180340500014014040c0d0103540102d8142c03551141c905006640290410350940d0b02d03041c401c1c1014100320382034a0007580a03a030308407401000c1100001d55858400070403841260003030b1080000350b4a66214112503070362072908000b80502440004003070b02443c4a85403007000d0700d0200140c852803d807000f61500444c0031107041000311020050040a5001013500e03c24204c60500c25110280c0e0318180d0003074010017965a403d8880030041000f40b10780340b041e000803207000d000340f48029100d101401400078600310156400600c2c80c0c000c150b242d44521000c0764840d01a2042e282480561190070000d822a981c01140034600841032059925200f01c3e0303011502000d003411490480541d603003e884900e4040c2c0030701302c14408901a0203002002054003606e8095030161401e904d8150960507070103a0182c452800a0b00e0302e0804460707540500385100d0f4054100c0011f1a81 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 903941978 1250 903940728 903940753
    0x14040b06040e04050f160e0f07120209010c05030d150f0e0721050403111e12070305090a0303020d0909060506092826030a05031501170109021e0a02 65
    0x18030140007242d4502c240311052030b417a80140f290040792840202d240c0100d40c540380c2d01c00c03012080980210500880c00d010300403270342d0f00302d400308208506500c0e0260f16100c2c0300c00140e441c002203403005402400f000400781e4448051b030344455503810760f0f00b00032803082e42c80c0e003544120107500d80150b4004403000004908030f03034021884018072195050901142e01c004084420550b40117032001c8011030341010b92800d444030705118621482410401d19004804944011681d610310781c540f10200600000d482814944034500300c558002c40942800f011503542e240080da90030003000c4c04800550280c1010683e0b000d44c0c054402207a000605d0142001d250b132003002080d2421000d450f0410b0010254201603004480d9450000c103440440c059082e042003103034000000c9c0000c0d130b030181500b0070030080100030307041000c3c1c94010441640c842d201d510304500689850506004081c0e80681a0b40000b503e03a109030001e1041403148940c090003502010154141c034003682500341c015030841b40c4a00403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 903943228 1250 903941978 903941999
    0x61b0f07080409020c0307060e06070207050f03030927060402070f030e0f0a15030b18040308040f1a011514030712090b011e0f0513020a02010f0c050414040b0604 71
    0x200c403405050324500e065034075007203002260710641c0c0b540c520b80c0012030180c00740456071046480041400029000b10f18207508001d48550312030007410301c500007a040b0b08920f0b4a04000340c0780400c40140198140300c0040003500304144082c0d02140c1d160b62104005407407400c041c000d45000c0d03030744042d401117001807d40d42503880e0409500d0f03141c0c020400c00701245480d550442554010490545000040c0d400000010150340781410124012513036600e20103010516031548681c0a9054644012591a44d1600603200305025030050700d01421009039540e2404003c400324102c3d2510348084503145100300094940c240951a154070801003800081d12660003003610f26408081e111000800003001d540700b0002071000c0e000a04003045204400c1b891124260f0150f0160403000303043c3ca246454040002c900c00207039044c240e02150045007140119000f500800c1c51403000d02c0d014091114404030007451a00300d4130444681101c4983c0b0b4074154180340c810607100e200c0141000c2d140c02d081090822 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 903944478 1250 903943228 903943237
    0x3100203060f130c0e010905151b01060603140a0c0e120c3303041110031d150711065a0f15040e0d0908061b0f 49
    0x160403419008541c0b80a5452003d0200d200c3c8607110005003000f15070744c0044c099541030080d20b040c402842018040390b80e58521080d03649080c90032040d515000c1703810144d80e41c001c100b18440d540d0b080503030104402c1d0b0550800520018035281c1d0800580c0d80307030034010544082e45c006802048901c20070b10807500b00449415401c507003041c12541000c146034081042d008600a48460302c100304007111124034003906400f42c800882200381810341c1015120a03010010302c8461501c510b40c4442e200da14a4001c1e085000440c030302c24403644640001c01d01c03241d21804082090b44590b1200c0000640c51030140403034902c5040e950000f40380c01e81e03c1881e1180301c4042041016003080b044003d44941000540c14004480740c001c4c0d01084c0019146500300300300d00f880440802c41481101000083c03421a8481644900580c1c05c0780c403c000e505010034000d0505054800705401924260b421301a00701d80c5a0089400043c00c66541d81d80380d40340c2c030740c040c1d00b0074032100301107982004912041781d0600c0103030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 903945728 1250 903944478 903944491
    0xc120a051b0c0105060a1215091e2a06020d0c0215031602151501120b0306070c02010206060909032703031605010e070605030a0903020109020301090b16050903100203 73
    0x256948020034050303030894011580514003603440344d0820245081c10306441005001e041010b140a20381640d80151005c1d03030f651220b0156665409a90901030084042000c1348032030b120700c02036203915043c07a038010b071000e039004068400c0d481c0e00c0d41d000300f4102425070222100c40e4003514080c400200111624048030f9001da920061020600707809012610003503000f9004048440c130034019044000c1e00b4500c2c801041c034000c442160801c601c0c94140305520300c0840d400d18100742041c0c402d207171110081c4a90b2400329050f10a0f401000a400d400003180c445c418001d80031a449070366420104104024112422202a04280084038000000a10000c14071024050030a104039544010a146400c183e0f884070651601c503000e01d06100c001c1c841c3c003144200d0700c405070540e58103200b0090036074800901440c507a960f96a8210050600c01e6104030400c0e0f500500138800400203003000941440181c45c10f00d100443d001100d01d925008038102c032443c80015000e840b44541d003108002c0250001000b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 903946978 1250 903945728 903945751
    0xd0c050607120b1305040209070203180f12010c091a0310090203040f050604080a14190f0207030618060c1b02090421030c12020702060f070206042c0c120a05 69
    0x101003d07956281e0b00c44e12a034403c4040080c60789130900400c134032410040c04050554100b00020304042c4d00c01d00c01c45820140654940c8006a80c120100e80b048101000e68020f07035191012049032175078410600390451707501d0313089500d101e44d42000504503480255003416580200d48002c010182054020b10741c094041c0c0c50500325481152501d5041401c1240c0803608c1c2c000000da604407858104104e0000f11080c0d03042e0506044040340040750079100c6105003012b1290440222032003d1081040c1c2002d154468014004007140172144000c0058205d0100e4038181046044048a4400c003990012207403200e50341000440389800303021091030003074400e40303c1c054903000040300c0c5c070304001641a6540060317034005061000c441000340342420500518a840340100a03030780140c0c1c2e44405079100040d4120016075075410030301c005010f62060b9032240440740c0b2107050000701603403c034240141412008083d62002d0352054915110740c41050741c81c0300d1a50b10304000c1003906466034000740d0301007442a070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 903948228 1250 903946978 903946991
    0x108061504030203030f040303121a0d02060d0e0a111807140f19030606030b03150a020405090705040602011103041e0c1a0a0e0f03061f0b040312020d0c05060712 71
    0x440d0461b401001d400c0b4507414001020420160301107104400303440700080800039050b0285048024041620030640304036010b46401e025940c54104941c29140008020080426659121070300d40c0400b68055440b4103421107e00240c1c1010750400700c07662a180d6100100d9078450740159920341c1c1c120003803a2651000c3c00740c015181c1e03e510060002c8400d21302d04500703001c85090001d05590450304424100b504052107180c007510005501c8181c4a0400c0c0c0d41011030351030310341d80700090003030b40e000903884070241080c0043d6640140042041c0d90155000b0312850900d0340c1040518801690020285085659420301e11000848419101071180088040c00d0782c0d90021120a141151660408400c002429400080e0080440d6591150a40700c80c0609001c0300300094540000502c40c01c1040604c0d817500b01c10307900c440307aa0303006070110380503064440f522414002a10310028150380d003d4410301c021000014052401c084815a00400400c0280d0310070130212188071740d0032480003611341c882d074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 903949478 1250 903948228 903948233
    0x2805010f02030a06090b0406030c061b050115051e010e040218090c041517040b100e0903131e150201060308190212120a0506010905090901050601021b010806150403 72
    0x79401141803841c0404c50a040030740e01ca0440e602d09052a2066180610400024894100344412a91141000e0700c95052041a9843d05412000000c006500e0000b10150721a4414110b40590324141c0355134841c507004441d5100c90511000b03800d4045070356041051601e203801d070002c03d4040c030000c510107003ca0580c0b000c00c0c40900c040d1000710014001007001c2c0b00c080d4514001c50100b800d24070f8035100c188018040301b01205000741001c6c1000d4182d41c000340c00b01ca0048621402400041d540403410700d00702030303203540340d40007200400c1a18411b02e40c00503180c4000b4685000050056550210441c0f40c945c0d0407034003512520303040341903540345d0b40c00001003000d0a004d4070300c410650284503031b13005641c5002820103001070352202c000c15061100c040382c040b14880d00c41e440441c44400085070b465a50050700ca50020b5406158840c5000e0100030802e401034100500135907007a0202c8075040c03101504103007a140d15101c05800109a8400910701e481c0035106001401040c01d0110b250544031b8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 903950728 1250 903949478 903949481
    0xc3717190206010305101104030204150f0603020d05070f02150403110304090603142407022b18150525140606190b0a0233092805010f 59
    0xc080c08000360300503800410900000344524035103c031031840c0401180c010694900300703600031400041d0080741c5d2500500208030a0054070005003103002d0141c17600c1079642e50010040d42c45a00790100d005e041c031000c503d055009916103041000c40c0e07005080821051049a01c240c41c0050082d4100200404070800580051000340060715800401151090035401c14280d000f44010f500b521a030320100c0480d4200c0e50b000c00c02c003654110130486061580320071350100e20300031500803840c00100250b0784241d44105d5450068880111617100c881c032100c4407000380d100c29020351042180d103034400c1006100e003901c140c00401403100001c0820044007134044480ca000c54030100110b5201958030107900440c2d00404c0a56031100b0708507512040300c0307007103d282c1201c02421b10a144880c0004240c000700c4c14020b105207501d09603030f582c0300000c64146c41c5240c05025405040410f00449440100707240c407501254090380040d1580c8448070b50b07080f01c00040e02611854100b994a07540c0c600b215400640740307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 903951978 1250 903950728 903950767
    0x602070c0302150a11060c0412051005070c140606010f050a14160b0112051209010e040509010c030e01050f180307120206060a291606020c3717 63
    0x520498130340840c0c80c0d014003640315507800740c1d0f016484102002419001398088030261514103c01c08401041481c100d445d0400000300390794210705000404c80c100761301c0001c3c0c1c0c0132a4001d0300c000306520000080700360dc1c0d5000f41ccd08a4005911410100320250241c40200010b15461a202403000400c280c1c2030740e541c001d10b41c0c01c02076482c1076006d0000d101d01c140649025011144010000748034564882c0d81e502c880c0105034090074004501d1a6041c1e00070a19940e030180b0192050109107048610a802024181c440a0120385003904051200005200c2d50b4411903c591042544d503c84030386002d95030030000000ca20a100401403640012210704444038224000c1c0c00605560421404015080180c2d0304140c2000d02c1c50310183d0156034a1500302d000c4039002d04100c940d42c02007151603600010850001820031b900001e003a8091a80c0001d40111500356629460701c180d50b011040803007c2c1200f2103400300552064030714004503050364080c902a40051420525020142e04207039100c005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 903953228 1250 903951978 903952009
    0x30c090f0702161202041a09070c120f0801030206032d1012020d060b0f0303160501050705120106050c0a0210031b23030a09140610080303040f0602070c0302 69
    0x6150050009042c0c04010852691182d60381060b441ca040c107400348486080e030007010340f09a0303c070740022031102114030101914280240003c191450180c0d405840c500f6203400407142c0f24584c22450784054440c42d03445150394180d40d200c5000303910b036070208030050b080035080c154450031280800a0354400001c440c4007800d917010500d003403490722201515640b05194000d6548106440302c50700140d5800c402c03001800d074003a00c0000c0d60030240c0b0100b0501031b40341c80080e4140c400054030390b10442d090a003490002e84528000e203e55a03480e80c2c00c40303050203242448001d45408000510403603028001030a5030b01c5e0414121418a03003c0e4001503012610030310300802081c3c0c0d50051542c10b1800305248192090f680c20503080e031600301c04420000c2043c551000b209000003201184403400316400040895801000880300c043c3e0113200280c0303c1000341c400d0920f020061100003000c600c0801903a2103540c011402e045001501e88443e4069031203040c085174900407080340400140e840d140c1602010030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 903954478 1250 903953228 903953251
    0xe04060503010606180b16150b060307090306110901020316061e090b0a0b0609010c0c0b040b030711150a050a0e010606081503010209091303020a080a080415020324030c09 75
    0x80080c2d0034416032070251b400002c6109401c2201c1c5001900c441103125801d680f00e002e50402419001a01c001012a448030b168800800828001c406900806210035a8000c0e802049400030b01d04038034000c0c0c442d07041c609002d42c1040c400000c100e1b00c02502c40500a0180c0380206000c4c08007607002401075056545401466501e50b0314505000743d00c1011540b100300e0742c8007041000c07412000a0114041c544145040101811604c010070a1440d030040c000d009102d01a40c68549441d2191000e40040310600e0000705c0b050044800400006078500d841d40b41030050006036106c0c1e280c520040e100050040320307103581740c5440858100b401d00c00e001c01014203541e1652a406c00580c3d2071881c41418001d40d1080e80103009e40d01540d680d002800c1d80003131510244031041d043c0c1d131605a05080703c800740684032a60210b0b40c2001990000c5859100b544070350800d01c101d03a5618001000c0303002c20b0b6448841d4940e014908038801c00d81e40051081c0103802421103820981c2c1000180b8203890448040702c445 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 903955728 1250 903954478 903954497
    0xd1d070e1b1c050f100b2a070501110a080a0f050421052406040209010c08030907050108010501050703021b0a08011514100522050405070816030608030405010e04060503010606 77
    0x2c10403031041c50b0700102406420b07041424030282104100c4a00d000700310180c20300003850242c0001084401011107814030425000c559001507094503402d5034410f46010516945600c0300548000c60285c2035203911014241c02c100c8880c80881d03031220303000c84540500c00100700102d0b0b060503050305840c04620010740d8582407000b61400d075040101c0000301406094505410301c54141d42c074400694011700a03280141c503103c20500484241c1d100e07840140040b14000144003143d84003080030010349000b0788840200d82d80e80c00046601c3e204160000d00160020400824050b0044000c66281c034802805030341c100307880351042d40c2186c9401d2a6100b8084407803000700403010070b0440c0402c00d8002109c0c94806141d9200d00034245120f00c0166031084040000d141c11032a42526842d000303828040c01c1004a860807101c054081141135075843c0e102c51510001c00001440381c000c6605a5000c00d000d18205460f00c0d005540081c07d580213280e015895190101e5140c800340b0516001b045640d0b1000c030b19 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 903956834 1106 903955728 903955777
    0xc0e19030b040b0a1a01091707030219170a0302060c0a0309050607210c0f050f0d020a030b1003060302031905030c0609030d1d070e1b 59
    0x1501c241c0038001403109684400d0300c181400f030000c2001c000c1519849003400c007130f10492400a444020180448580340007140c51b5000140111644503440b40d0015071034035164080040c0101d442c000030000702c118101c00202000340c402c09480c54013020b0320004d441d140010702052400c480000d000f680b1601c40e9101243c501d4220003603907814141410001d21a040b20000e05900040140c8441d4185406e48601140714070b8a07210540b056140d0f0b00141c0380794002d1140c10300c4504090043c3d085c0d1101318001001108000da8001902c000000d040001c0f085a4134003080c20075150900500c01030301d00040d4080f400c3d00c104113a00c911092450102d11310710824988100d140100300a01090a4001024115825145078180b0954200001803196150010341901d601c0d40700e240304100e45090308100c244c1020381c5139803103d500d0505510b0781801354041e03240c1d2511540e18409920a = true := by decide +kernel

theorem cover : BRFrame.Cov 903776978 903956834 := by
  have h0 := BRFrame.cov_init 903776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 903776978 ≤ n) (h2 : n < 903956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
