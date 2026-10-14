-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1146
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:26:35.186113+00:00
-- url     : https://prove2.me/submissions/be3f24d3-c05c-4773-9211-2a6661ef5218

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 205935251 ≤ n < 206115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 205936501 1250 205935251 205935253
    0xc100c020414090708160312050d06030b06030d0302031519090c0c030f0203090d060b03010204050402071218180213080322050f3a050601051f0203030f07050c120903 73
    0x2000170703400500042501c00c1c01e0740381413100d10691540d034030814028600c43c441d4061140c1402003030450165481814011809516500c0551800300704060034080a20048414944103000f4414400c106562429030b0680c2503400724000c101c0d55540410311003065104014079420301403082c1b000769101c28410702e401e1080e01c400c5000350310a540ad070386a01640081a802100e4041f03490040340143e08041078400002d8001890507481e8008201664040c3d08265000c24914481807a81035006030502c2040e841c0a0b503942c0e046041504980c0070f1303a02030f0f408014503500440c0a00c80b88034440028002818404122070f5102988002c1480141807504c1742d0790482041600090300d400c06030800c00c10301c0030090107442480082c5c40307800240103102d0417100c3c54943e108000010004280c9e009103001c0e02403401007800798540820032107140310750304c481e80040c04460204200107030000103598010040660b00812665004001c0710503014141655a151040d01c0050345100054002000b401d14294 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 205937751 1250 205936501 205936513
    0x12010c020d03052202041107050109020901050603040209040813050a0314100509030a033c05010b070305070b1e0c070b010906030816080f040e011d0403020c100c02041409 75
    0x1c42601103038011030354414080090380083d80c2031841050301d80700c0c03548002c000140e40c03c009088421035800c800012515a0355401400081d407611124190041900b220342034910f140c1b40c1d0110ba402c81c00548020304442001c40e26a00d40440700d010000030b000050200039103a0340d2030505403900d042d1b40c165184140503040341350b040d9840da409424840c03140c03070005500d4501a00030880003481040c00c500151510f5140c4042d4005451442e07c01c0c1c890b203400031070403152951644c08121101a402032043c1c030800c02a00001a401038142c484107604186602910f640b400b600d0320401d45c02003c0c81200c601101304010100640c10302910030b182c0544c500d00c04582e20703030020034200c82d0b0a00014042c240140300303042c00090204100d822040c4560022400d003900f10035401c1c007039009034200b061100b045200602158940e005d030b01c43d15986402c503002e46c0b820180ca0107500c40c0b91803409140500b80301803c508039203010303081d40c024099010384108088a4130410080c06502c065580e204180540c2c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 205939001 1250 205937751 205937773
    0x50d05040e0a050f01120305070503040b0a1103040e0708090c0a151101050408040b1308010e010209040c020a150c03020c060c0306040e06092d24311112010c02 70
    0x40d00c643c500c20114105540402d03403c10841041c0200c44840031000c00400300101400244180701070002800e11341c00345521861150005000d202c02c40510605651003444200521503484108542019690030511030507201c41c0d0403507091000190415402c40c4a0f0b1400085951280c2c020100040c825034403c4d4043c00311003101402d1b50740a480203044142c0c140000d2000d0100c0d0030041c10560029040f9102243e41d030007640d400c4da03041060104840c0d502103080b04050030140120100c90311944080c040d03e05070b40e5150f59000415000c01e1140e1991079042846003400b9a0448980d014504c0480382c491a103141130100b103500440300c4600032400c0122074a11030764000741c51401070018002515542540181c5210386000c11100c0300ca0b4120071a10090b060780c0c09211400d90a841e4008400060b4450040505c0005001c0e1140c064120390907011860105600610282c2000c424043d020607600d9080a29110f1500800300794408601502000c00c840154051640841c842e000e640042c010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 205940251 1250 205939001 205939021
    0xa140310151218051b0d0c06210216030f020c04060b0d1d0a08070507030b040302010f0c090f060e0a05061603031a090114010c06020a0e031006121e050d05040e 70
    0x4001070180d80b206001030045c00d00300c2007984a01c4030180282072000003988071809a0821648098080350307441c5481c480199003459071303020f0090103403801e61034005110701450320302100c00400750030021b2040d440c82c5142c1c401d0004d0071150400400900c80143c64403842c07842c5501c040c0116914074070300030301c0580340c40e1000746601c0c2501a07500231b440d01041c16294102d49500c6500c0c00c8540340138884022002641c40060280580e010758000101d5224588220301100d4002e00030300c06000742088101b08401c4000d010301d00380d441c546044a103841d1004041200c0300207941010f41d21580101d181c825a01c1c0341d46016500390f009590900c050402031206041005030100c140760020520b10040c41250503031070a480000d035042c90640802c0b180340d01c807034080f40c001c03071900e5001401005440103d46002c0012003220101d10f00100f01c000c0c605444900c1400c284d00c0c000f0142c6403440b050502030000200142c40039500802659002d001c6942d0041c0203034814002d030959580d62002003411000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 205941501 1250 205940251 205940291
    0x301050702070b0d0e0712030305090106030b1b1b0307030f03090807120c020d06020c0c0f030d0e0d05030d0f1406100806040906060306050f0108030a1403101512 71
    0x1074018000b6207062080451040d401440c80c440700030707102e00000e5201d22007040164000c22460070307144c00000701494000c0c2078440c054a1014260304060301440400c05d665682030f081000c0c01e02c40c4021030341b4002010010f0141d5104803510a8100582d84004000840100000752182d610820203010641003034040722400d40703016000b08020320004000a0000040c3e0b07401c5003140c205618445c0d001e0b40002d4281c01000c8003100d0340e0f81c01188800700c8103000c000c4205801001c031602303454000c07036070042947c441c83d202c180d01c100112028071809649892200e254a281c04c60142c1c6d07030b5034800341c000101521040900f40712003403900f05c401c00d128829000441c02680020710034001c0e5110600100d64002020b003242d9405660381c40030341c000034038502c10f40004600c03070710000c0703110300d1305044a110080d0705078448016078104011044031168040d21005002503a0401c181d01e80e01c0d070b02600340307868095810905d1541c1401611044e495000200d0f041b5491a201041c030400b4500e0410660768a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 205942751 1250 205941501 205941511
    0x32a06020604060b060c0a0311060c070b0619050603010e0712020f0702010f0e0d060e0105010b0a02030d180609080315011107180b1519081e0414030d06050a05030105 73
    0x78000310085400078800f0b411100b10401d00804090a20700760685450401c0d03600b1904501050600e2442c60f9451070a0001c1540040d01400d050f00b8800652602200480d000f01544d11945000c0b2a18180341000030001c00a072034050a0075480b503850702070003510741000b5514000031600400d2503401c452001d00840318807141303030b0024a0803e1501c2d40192004404400e5460a00c002c050008800752070b10b4004031211b0740a214003140341480305210500f11038049e0440b440da0300c0108071010f0b90540000c110380841c0c01c01c03c000a03100c082e1078280344020003240e01c0240110f06040c007100500071600059401041000c0a001c0008040710040d1840706448052411580020104020000d0040e48010500e03409070000710715650210300050080c11510762140c409023010480e49100600460b010355114414204030406007031480200c0440c01219001380304010041c4006020001d1010b01040d26840303907400c8988900340c800c0300c00042c10150041e140240b13411840000c907807405000b00350081c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 205944001 1250 205942751 205942753
    0x20603460605060d020307030e100603031d150d0209090403030603050c0306190b150a051c1a04020906070f0506090d02010203010b030609060d08040602010b04060803091e19032a0602 80
    0x20441e11303036201000c0d400c010702c2e41c0d040c1359071400910f1142900b8010500c00003904840000d40c07030b0551602500c4903003800c0c24403030006c0d00f6440b51010350f202c91390700d09481c801804030300d5101d480f109120030191080c441c007990090140d205100030990950000b80139a8811419a04900c2c0c42100b8151781e640d0441b018036101112400048000d00369510504103110054518880f041940c1c040c0d0065510070302c0700300b00150000035050304050b50100c0c540e00401d400b12080c00350b01c014046104503182011851031081e41e002074810866918601121252540014180400c8255040458560718201c404031440c1c0140d03500d020644d84103100300c905072812140401c3c00c58862000703000340d8000c002e29090b00020308011010100700a0b00140c4001d03e090342c00801c070a03050b80c0611003a16107541c401145e56200380100700441d55540c05008108540c413107000c3c3c2c0c01e00154001040c00503842032030703030180405400210922500d600c121342110109041c41d0702d1108120107400b001d20b5130380300358801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 205945251 1250 205944001 205944007
    0x301050403020a03030e0a0b01030b070816021c03060e16030c030b131107140105150d02030d0e0402040f080f0d020f19082104060b040507090302060346060506 70
    0x13034000e034030243c0400d0000048501103101540c901034002c03c00c0c0c00c05d5955900100800022541c0000210741c882e17041030481c0210b00c03070510065aa845510404024200301c8030755000c546109501000c0202221886035000b801c29041222800c4c2c040313002d4000090510f1081c000d858080e001d0040c0464026006c000c0100c3c8401003100200769860100031040d000b001948045810942c4a141010822000280c1401c1c81d9400c525404180d5841c580036558003080000542d0b00881c140d8030208a030304003c240b0450100c0050000d200d50b40080c1c003842178515010900c04400600c200252040c042100c6010f802004140c1e034034003000801c41da1652186000421101e8991441c0101901c2048110308050b02c0a5807056000f224020007000d000c07102041209110316070198100c0141c060302c0401890419900c02403248010b404041d00559001001c142c00c0800c1110100c250f160614501c0c28044000c8556050b00200b814184040c41c03c800c0c0c450b9034003400f48100411a4002011189 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 205946501 1250 205945251 205945253
    0x303130504020d1d03040609080d080403030b040f06060207031b051507050c04051e100b04170a0209040b041401020301140f04140f090d140d0905070807030c050405060301050403020a 80
    0x101079030081a0680440f503c1c0d4050f0504800c020820303d0750030320751300701450702e40c0d00b4250010840d2001d170b4880d850700e41c44184c02500d40340d0401d5a25411a41515020500412504c0030030b000e081070070000a901403401c280007442e240d01080000940f4861041e42010031982c40440c91840f01d14080c0d144d00c0b000101700c03c0101c8104800070040b49208401791035007403134030310005003c0f1801141c2c1d41040c40d4403020100e0310b401c90107480c10b900440000076544200e04245503841c0314091400303501d44c40f210581d9107403521103040001003403207940180700600524180c81c2c4500c08001c1924112042641000c408001c0075044c02a05d05a6007030051104500340f0070b10401849021541106401542e40e001521076100e40007002ca00c541c14103101c0d080b40d4280b80d24000d01d031250380d0440703504101d60008403011298484048800182c0744e24404102c40c0418142103091480e41c1e4090b842501c0340c5400001080008030701d110840b902124100016900d0000b0b060980304101e90080c01030304180c0f0244 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 205947751 1250 205946501 205946509
    0xd02100507020109180219030213030318180204060206060a0e06060a0309062309070e061519120b1008040314091005310b21070e0103050603031305 65
    0x21500d00500d00381c3c4c2c1841d90303080f44e4440d000352078440b010410740000c1c0d0080e10401c2440545032901d07552130304603d010300c41200b03000741c540340f400010104004000421003500441d02c0280240c010101d02c069020f05030b410354402076200344146805402a440000d40600d040c003040c8081354106a6481002c0c0e40c0e01c400c00a190340314020036030a140e900c0704903d01113401d40c03044001c4945a20355207132103080040d4004801405c02070246020743d01902c000d105070020070350344e140c10103010740302c100207820031400d00a41801014080d414959140c54888405036016030300b84521140728008109041041c1e00784688030407080c8001010075815030208000034443d03141001c1c504004090a4184403a031b100240c0d1640041c1c104400080c2d021802411240da40108190110030140040500c3c4004451864082c0307010720401e01c03000c0d8042488515070728100c41c100b010100f04c5104030841e20f000040079201c0e407410f00550b80081e15000000c0c0060400104030303448004040c92080c1e42c9032400f8100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 205949001 1250 205947751 205947757
    0x30a0608030a020619110708070611030c0a20030309061e01030b0c070203070b040b040608161b030908060c0c150124051611090f010501050d020703020a02090708070e0d021005 77
    0x5d869425560740b0784900743d2034100050806a407103003103203e6a9044c2414114144c440740d18a030400c0060405c1800700b641c080c00e0032145024203506061302c10450000c181d590384490405000d0190100000700250b1800c0850180c0c403a0143e8202c036042c4454001010b946c848003400000c0000c141e0f100460b00f9190b042c0c02600c41144024100c030301594903210743c02c0154000360710000007071001080a002050700100030310361104466000c5039240c10140f000501d15048503003000030180098401c003003454410020320340a0240002111824142840c04010030ba106402100340d50003600c14441c1c4081c0c2c40c0380814100d40584060001405818001d40e142044c03a508a205000040119188100086440e5040240110701001c40700500c40148185400020102e040b0700350790030014003803603030003c00303582d00c0c410096001a2116658507059141054a40340139600444001c2009020350b0300c1400c103403203644c65645140c02e00002c0c40074010300c0040d0703d400950100c0c0f1210050300030340c80741c809 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 205950251 1250 205949001 205949041
    0x14210106031416051509041407020f0307170a0c0804080c10020109020a06050a030e01051504060f06090303030f0b040e0c030d0c02030c1216090e0106060e010509101e0203030a0608030a0206 83
    0xe606e0140310380005000c40d400a0b40c2013180b00d01c01d90400c902143c0610110240d0011500698a40351495071002d4100c1901000c10314466800300b0301035685440b0351181c2c0c0c1502cac1e01c84d0703102d50364030349544082d035450200d40c01d402c1c841c51010722902c04143c8103000d030011f0a03501a10013866241803e40079a10b6030006052030080556801c2c104107029403d001d01c5008802c581d044910075071622041c4025902641c00010040b284560200156a40600e560046a4043c81c0004a01c10030160400c0500312042240c0d07849810b0001402d0480d1003c10385d1009901c084045480b84000808140e40b0242d191102a40c91303040a00700d03041e141080c014140c5070789103034425204021490350110054810907081400400e030340d038070600201c4500340700760170180a441c1005070a0541040008125101d810880f070700600d43e0b0b00030016041d0060480d40e1641c00c0d440600000c013401e040d0002e540b5081128100342c031074100400014000d00c08000c441e0741c00381980c040e01c4107517103084c54030320603081aa071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 205951501 1250 205950251 205950289
    0xc07020a0320040605030d2a0614010501031506030207020607170a09090e1002030a020c0a080307020111031504090203010b100e09160507030f020c1009090509161421010603141605 79
    0x81c2884100f202304d544500002e1140000042502c21900e40c3c3c41a010142c000f03d05161270490400c0b04e007120a009201140c1c02c91502595404c40b03407006c2100c42c065164000c001c1403c4030801c802c1030900e0030190480f00d1250f0341d20043c807a524114030043c2c44072960303911895002440c55030703032240c3c042c3c0084d9408110090054036042031440c1c8a40f400d09054426160940003000780581c6039828004d4907004a0310341125821820641002e201c41840c01503514481d03550307400c56208645081d00700058404004084a07404941104060954500c021001c0d00c0b610074680010004901300007482c40516040ea145800c1c080255802d451000304400088254861060148a961b1f0b4104804130242c40d10b548600340399140c140c159007034585c0504118000d4109044802000e403000c0181d000700d52031000c0ca0302c075000482d4041115840d40c036080708032440d0b18008580d0003030380c1500070800320703841402480074007040626800d03198074102d030860b011074201c500c0820952074440040540710103602 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 205952751 1250 205951501 205951547
    0x11503060b0408060105011209020f2e090602100522150227030d0c02100e0a1214070e0a050a0621050c06070203030f030c07020a0320040605030d 64
    0x40745071481e90030640c010342e916806a4014002940d015802c0d0000c002c60007014440e001e02a40040d5a5030b410380f0815010342d0614074500441c08140320b40100e856000d20703449001c3c0c0002403004110000c5401900058401c0c40b80d12200c1040a200e258400d043d140b070915030561038100c1880e5980b06103101a91f000c40365170224240346032540f000341803070061944c1c9440c0030b0160215407444500b65040207442500550004540030ba000550619455411a808084204209419111003407091034042d0000242c11022650140c002240d00c8164020b50352861240d0003150341039642c0c0014061802003080b040c011400700720340c94126030f070400ca010780d002c6840741c0c07160304e0000d5a4103401d559100300c0401c2d0100d003080c880b0a1100c2c90810205440c110701d48000354020a41d00d105d0102a0100510300100140c10114548143e40c0c0c04ed90082424000540e2414074400d5030135001c501d03d140c40d050540000c0c844c60184604022203102802919074410b04c2901a503503004603141c00c074520a900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 205954001 1250 205952751 205952759
    0x90603070e090114161d03010216050f06100b07080c1f0506100806010509010809010b0907050403060b0a060e1c0c09150b07030207030b10050303030f0a0b0f060301150306 75
    0x180d03907561040c14038800000720a0202a10081c0c1c0360401307446119021090030349a2105907200f00080900c8181c1d41c0300c08a41815000820700a10a0224510b2804142d01c1c1c44010410007050312034100411904943c0d0a480f40f40c170121411820380316404841c2d00400a02d00060325500180600f21045001c0c0c1b50b01c5510610300c0044102403034110590b450362241080781301d180c030b406200e081900900d0820407074581702c800608544585002d140c14401c0120000d0a400025000500781c0c09016081d0005070918000140c07081c0c206001c00c5a80790f0400310001e446003000b014440031126541d8401c2da0040b0610700b405050041600040d0030002c2c00c1c07003000c01107100510204010200000e00148490144042c0c0415001a4000d040c0198080010f140440c0c1c0c005224010b6941112503807145881e07040400e240e100701507200c6a0540804004c029030906562480e03071246440501c10f0280080030f04c1000000d40303803031b007880b07910000510050108c0e2040c07081c0001c01c00f0f040d040000c0c0403521 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 205955251 1250 205954001 205954019
    0x4080a1b03120903150b0618191511010507021c050c0a200402070c1a0d05040606050a1205100b04020f0f0403030e1c020402161a010302030f150609060307 68
    0x100d00c0102e404a40301c240104100302c0b203d4459485080425010031010030054001144c42c459841d50f084991503115550031250354001c0000e51400a02d01008552a0b560f8030310405003580a222101040d8080000d0300c903c42c0c180110351040c8850350281028032030000080081c3c0d003941c990002000001d008115540b0000c101b0403c04502903582c0c8042e02e06110a00340c186404c1d2003d140c017650050284800003480302e04441d007640c14100618841910042c0d28400301d004070041200300f02d00300400e1200341f111070382c805030503500e09440b5110515200c0b20340c218203504a9500411301e03070040000c06180081a8403984a602c80108094a048401702c0c0c8006c090b02f02c020301c0b00c2d40300000a410030805030400b0301c1c5151040c00f42c0380a0341c0c00e6406050076602010264019006503000921600900c180c0781c15070045550000c07a4841319042c0f0704d128090402c0901040b0f01034842c81914040f40d800002d030a000d180b4284407140b609079543c80600103019009001c3c240c06100303c0c480401d07200c2d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 205956501 1250 205955251 205955273
    0x3160f0f1110050c0a1104020708030c09030c0103090203030a080702011814010e0109030507170d11120106020c10030e070b0a0807270909030c05010507020706120204080a1b03 77
    0x101a0805000c4400208100140701101c200507000f4040b04210100a441c00810111492078002c0c1003a8050341c00300010a02902c04c000c4018038881d00041040a80100103010b404018000e0b011a001f0481c21001074040300e0044401a505a00512156466510600c80c2940c000b42e288004500e42010115549180103440720031184000b00c481c1c01060f0b59001d22407010003042000090115440c0c030748000d001e1b44a410400742200707440c1005901c41e14154022503066440070b003400c0211041c0321000d9003890700580d42c01b0902d01e19074400003400303500c0003e4011000d840184000603130440d50310141d005101c0800488000d005240340040d50001000c0903014080d0a45c40d282554542040300500821710004c0d03c6084096031100011302040d00e1003101c4c15581000400603165a140c201a140c8500320400144650700700020029515400300d081012540d1a03201c500401c41c4690448060740a41d00031103072194801c000302c40c0440e200281e40562221012a07904c0c1c40340d03c03525040309201e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 205957751 1250 205956501 205956503
    0xf0803090913240b01030b0301090f0206030c16060b090609010303051602130213210b0f0a1b03061d060303090103020a1103270613060f05090306010e0a06080601060203160f0f 77
    0x599504c10111a65803d40209080e0035002c030020800c8580315651200c01c29105c0401a01637500400010075511036103045400b0001055540301090103140b1705680600346651010b405224480701091090402c1c0344098141c941c10b440d01d41c2000b99841500c14800c1e4a10b4040e41d10020910380d8000030f09591000704076a080c40210000082e040145908902080141158120030743c00100c0000c04e170580c0216800942441103400743d900d80d21800300c054641a2030b88180d01030301c0143c1c11422905507100e202100c0c01c48000162102118124009590040784e045406400c10811074009610076402006884c565050150b00300d2283c5668a00d543c10800009030f0580d500346201139020802101e1070f28545007119a40c1c682000d2030706c0b41c0c036040c1c0203124241c107002041c86040001ca0041090780c1841202808564107036a541100101103002507619103202494402c000c1034002d00452410706a0340140c00441c50000c900c2400c11889890f02d005544d120940d001000c00600b901440360121 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 205959001 1250 205957751 205957823
    0x5071e050403020436150902040615031508010e0a060507090b030a0902130509030712050d0f0f05090a020604060e01170106030903080f1e090f07080303010f0803090913 74
    0x81d2044544448000da0703190004000c0440c1e045c03070500000d4201c4480040490350030070100b181003061000c90041c0c03819404c960424450a501584c0d4507605a01014600c00c0658a0f081840e82e109400d90803600f14013290101c54008800200c0444d802e60411138110502e40750601d040355481c81181c4045d00143d681111080c2c0390442d0000b58640107a10074418000c0302e00c20030480c1844001c1603641e229000000382140200904141918010416209580c500080a210800f2150390b05030050951482c0d942040d0710b0320012483e21074002540081356940a00702d1403900e410020142c5840180305840c50400c031414048415804280301c1040c000c224603100841c0075241d84ca8043c0025600425044002468200300030341e10081b2400c0249480b00044480e0307003601d0310b0070031505150100a01154502c102500007a220200100a41c12100520303541450282c6400142e5200d1144074110b507844414180031403407401e55440d0248055110701000e2801c611101f00030382d21480000c40040b10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 205960251 1250 205959001 205959041
    0x7090903020f060906010f0e090c1f080c0301030804031506030f03090819050c04090f0803010611070b180112090204050907091d060705090109081504030306080105071e0504030204 79
    0x3442e00c08000040d0800c0410000c1c00041d03042c1103000841414034803c00d1114048040880e084000600c0b511405030009002205840144040403003981d601c911040005101e03a40001c40000c42c0800b52810307244e010030310030300d454515203601d222600100015012581d54030340000000304400b401100f041d00c89c0d110141d107249441c0c01582418685a84c62881c03058517030343e9000141012510141d540740440f00000c101c0b12604058038601642039004004240c000000710300984c02100c042006141c0204450341140c40d818404031a01500c19840880c20700d5030f54000140d802000c014001f988110000031780c0c04d10580001d401d0750710039038190003c0d800c610010b2024a026001c0c50602c441045280c0710411242480d4035511040100817200300704010078400d007260f100b10101e00041c607241c0201e40320b640d600213802080d10310a175400c4010a10b000c4000444403018003c9a1041000d40c85681d03018004000741d80b001030b081c006445c10130008000102c0141c9e0b8510032034901074550328900c45 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 205961501 1250 205960251 205960273
    0x610030e0f1504150b010e13021b0708010b150d0c11100c0f020304050603011802070f05010c083d08070f1517070507021f030506030105060a0605040501110709090302 73
    0x8407a0149040c2d446132603040403440c48850b41c1000b00c00b031803050143c03140d034403903050000500300030f008044124041d182000d16405c0c00c80d40005050307041d1034003080200b04c0085180d041010300031052207e4070300c44009002003491405242d03c621182895030409500b030540c8200d81504290382400b450211341c0e030700d044511080794000c81540da10905800118034190401c000207416000c144170341c201d1a4000d030000b600956043c3c040c1c82407190b2001100000312910b00e0305a010304020100500001c1d01da40000e14100750403000f11108400c00c4901000107902025400d0304c0040520044240c401c1c110000074095404000d19001818510282d00c0101e0803c684d1458518108507043d0030040304c4e400c04c7c0d40c5800c1c1c8107940c0c2e8100c402030404a9440003d80b000c15020001350822007054003e0b600034002c0290513402040c8199800c80c000c01607681d880c020031079100a01d01035500051014002804954014810295165035641c101c0d142c8544d03848104040c0c5544600c11030040e005525100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 205962751 1250 205961501 205961513
    0x143405010506010f0210150503030703080f0604020310030f060e03130f170d050a1b03030506121203150402090a030809090108071503090204020c30030610030e0f1504 73
    0x103030021402d1034860080d03810b04c44000e41c0e9040060100351415030b51503800c040b07a5910002c2500400c00a010340b9242c002038200a4080c01c400c658000f48040c20000082c0300340303001d108482c89070140070f9580f2643c5081d6203c15003030020541d411140d02c1e540300442c4196500800103450088001040d25008605103804d040003002c0a601c80c854283e00030030300d43d42c0d0640c0402c082c00500d580c0d2031f0250700c40040c850203d80c1d0f5440f802d6100b40000c40c0c1402d10301810b41c1900002c0c0300d000280e52a1202070012000d1903a01e5aa10317915100c4100144082404650942c00d841d03002c0d48003c00c00750800b058800045e503262410341c41200c2c541c800144101c5c050602c203090074010f1000d00050800300c3c0c0381640c0c0076080c0300d40e280200100355172a41c9130402c5654a0707050b204a01303440801c548186502c07103e148003847c01c500081140c1c00101c05640d13075030800709040360320030310703000c1c241d00d404c40400d00f01603001d08010b207444015401005500300e50458108652003035001c0e0003200c4150303410a82810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 205964001 1250 205962751 205962761
    0xc0d050a1e090c090b03030d060801020a081509010b090f031509010b0a0f150c061a040b0402070c0b0c0f030711130b0d140115030602040e0f060114340501 68
    0x1c42214181000c0c140464522040304044820a000114080c0c85030b00001303046114008000740c0e4140741c0100450071001c1507018082446480c0c4481c101c540365007500c80c00e081108001035900042001c014007106058402421b011107018040b03504009401002905000b1000043c040d104540c41c20000c03540000d004084001000742c0700c0c007071140e0401c4d01c01e00120071203016420160020780311000d43c8a120384240000c141e0000c0c001c002e81c3d58008841c0790440903100c9000d119501341007589440e1301d020710895010729400b00403e0101403910a09226035044250480c00c41d0290010807180000c09000520384140710f080f013000e08007801401c0050308881e1103520081c0034039208d510542074907401107aa211681140841e4101010300c0581c2e03000d0001c051150103c1004000c0000c1007048640152050350580c0351400159036030280300d202140300c222280f0780000d845000d81845500a00010400035a06288551100e13500e040b110411050340350499000a60324010001440028030403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 205965251 1250 205964001 205964051
    0x108090d110c130f0605120a0f0312020706140108070f090504050f0708031b0601030c030f050a021f021509030304021c0b010303080604050a06030503030606161202010e1b0a06080c0d050a 82
    0x421a0700c5007140034103584088c0c90707100802059540d00e0080074140a80c400440b803040d03c0ca401c0d562205146054806440c100f0350759100c961585c0000314003150081a40001d41c1c0120f000008854600a00d1102600001e80245c409016040400000c008180300c6a03003d42030220040d55604000c1d000408519080400f802243e00900010b1001032150a030717141c11650018801070901406041880c1800440721000794801c0711030044500480c003080c2c60005428040e000d55034441a2050082d204482c02c03207646140e074208200180040c9859605050380070507051808010103203503a501c16a140003030b042038000c610312404001c100c1c5030030b0140540c0702003032140c140030140c80c694401c0d40e070340405001c0314401d82000c03450680601080c2c000900481d004030401e219070400150190081c001c51608003964040c0180ca0054003003034201d007410301440507041f10004c0c4d1070701d981180c0800e80a032009240d100c0400801e04441c0160245030700610f0000d600003070a454030800c45620300c4201c00c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 205966501 1250 205965251 205965259
    0x15090906290603011202040f0c0906030c0e031c1101020d050402040e0f0c1509040f0e07050109150305100503101b030b0d060c0e15070b060108090d110c130f0605 71
    0x40c1d0385140707803034040a590449003291090070700034166100007005407203001101c04010340341c595401002c542c40700a00c403c881c100e4078100310110b60a082101c8461100c288150036031710001010406a22a0300500d410702d54a01d008000c5045041c9014203a0b0301c8003448012003a2a02c01340002c0d0b140a100d4031115044500c000c00c1c100d1040f03060552500003012011344207101200710445020302c440c0807605603e000402c00c0040422040b000c200500d000c0c1d0796500c092080c0180441e96501030300d8001d054030302e4080c2215401d4030842c000c802508005100031082a203850700000c10307442c00c010520b00c1030403050000c074002d500492818032041a94880000709801c1c201621920340303c6801400e40e60f83c000001190200104805980e4552540f50303c54001c40717440c801c1e068490182014088403823003510118102c1d200c0c100115441c2000b0341c0c2c0c0040c19044280102c0c45c1c50300603103418120030b60f01010b482c0340d035100c01c0c00540c00b140300c2c401d4030300e81946485500700c5050b041e101e41400750000319 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 205967751 1250 205966501 205966571
    0x1104090f1a06010906020606010c03030e07090f140c0403080d1803170c030105010c030e0406080a0b0f010b040e0610030605030706030c17010f060c0f020910180e060a15090906 77
    0x140007d5072840003901803414400280344210515100360844401d1001480c100c40308142d9a8542500500031b0714102c0403410f15260340a0828041600f80300d01401e40448a10b05140c110f0703d881429a0180800005255542240c01400b0681128904105000c0d848180e0882c00e4100101428100141380b50402d800810040c0304c6603801429140c480341c0c143ca040c010524081000c50018800e03034000e440540304030b04499082140004100c0e104442900300600c171350342d03618480071950080b4040d00f40e80c2030708400002d000d81440042c81d5810030300c514000c61800e0755440804c1c1400e4950b040a030009407500c554200250300300301c02d4490b1201e011481c0a50350f00d48203006801042600800d0104081108500103006508800e1b90a003034000b0701d000c40b60300700214540c8000c2814800c1a04240f04e800600748400107521406d807802000402400340c0340e440d00c05120040501c00304104004120302c1c00405c8d6003646100750492284603c02c00600d01d445107421810b040c031b900b10521802d0b4051 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 205969001 1250 205967751 205967759
    0x60e03070305120a110f07060f0c0c03030e0f090906060414010506030f19021804051f05060307020a0b040c0e090d02030406051602060d0605090a090f1104090f1a060109 74
    0x905543d0741d01c0301d031004548901c04048101c40500221101c2c4d44035104550701c00605000115600044420a8856141800d081e000035121b080702c242c800740c08222480401c0003c640600301d5010324601c000e01080c0250b00140002e4400c1a09980a2010350302000810802d800c09104001841c41c00c103648101d00c2d0316000000f011031000401008014a011012441c0c1d06a800d100514400201c8008d5484504400d020300ca020a44103010380309500b0440410000710003003000181410500501d1500c00742003038144022075001500e0842184241645c4c800407034907161656019510401c02001c026261004003101400098003200ca030f900101c3d60b0031510781e00041100c00b2110103040150300c5140079003040714041c00440019410000000e103200d801c913074550050f17040d07900c00c4a055995403140924141112070101c40100300030500911600421040e00c240035414070010008036a180d00b960701c0200c0841d00304002c50388019002e8100c0b641e030f05407400840c1c1c01002031034000e1045140c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 205970251 1250 205969001 205969003
    0xd05090a03080c07021c0c080a121d01020c040b0604180f05060f030d030b040b180708070201110d0b060d092612360c03010506060a050703080a1401090501060e03070305 74
    0x64081c00503401070b200012003003000e1b60207c00014003101c0142c0740b80509505011055824501c1030400140442d071001c070152183c460101105101a030003000054540814400207020020911340c0c0007900b84000160402e240901d445080381003e00455201e162580c8202590809044035100d50b42d4201920901d8400268944001d2040c3c07901244500c0c110011400501c1501c0c0348941082e4007124481c002100ca0301150701070b06071980c0710310390381d80e40301c0d0100c0c03c841c0004a4030316100e60803c42c040c062050b41d0441c001021004040e03514010a078141c0300101c60242034111500c1b040c074075529020a0309401e080f100a80b03010380c402d01e0001400e5580c07040080060402d04004542d540c0414007140c02c441504152030b01090030301140c0500c8604d280d98542d54800c840c425820000021303081e040c9417003038400411858071000c0c00c02d02255402c0d101500c0040005c1941950f811082c01300050801d02c0c14004c00044400058950401600614902c412501a40607520002003040004c078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 205971501 1250 205970251 205970269
    0x1d01020a0e1c0803131a0609100602030405060d1107140601090c1b030c0f03020c100207051f0c050a030f0e0105030f0f0618150102160312140d05090a03080c0702 71
    0x50f00045a554a698100310740700461101c2c50003503d1020305c044040c0452201450440c0141d004443c01c0b185aa50003500f481e028200780039100060304103120400c050309004000e40743c0340142c0b400104940070381c04140b66141e00a200300391440c0140500c4440f0129040c0400d6007d040c1c5824284005003845101401d03040c0708801d07043c002d00c0500461000d0612074982d444d0713800d6211403248107210803410000d40d98080c03e0101c2d8403510b90041d0344030903240002124012200043d01e522540c0d00e03900c05040e04180941480811705c0403401805c0002041448081d111505c20380f541c0850324203011b40204005030b20340c520740c14000304000f403044521040d800b0f60782c88109228881d25540da5000840e4106280340d0ec503040180740381c2c060240d8500601c03415103003040e003a8215545102043d0b01e007000c4c6504d601c0042c01d0b10100410004800c1e2003400c2c00004403802442d1036103803001c00071480b03044a40442c5c003c8140d400118056080561084101c1d801c0b1507c1203000e03051150b0b60f000520045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 205972751 1250 205971501 205971503
    0x60f16021c0c060e0102120a06050d02030a0605060f10020f0712031b031b0f050f06060a1401021606021b011d09041b0b04090b0a03030f050903011d01020a0e1c 70
    0x602022110070020680c112414004041c1e0082d5200c403a07c21000e03202182c180c549040f49800d11a0202d102e040486903c1540c0390014000c2604400300d031508401008054006a088499039030304480301e8440c4102c1c0d900440340c0d640144200d00aa1000500300022074000c1d0f02184c042c114118042584400c90590340b002550804c12840c1041c0f9003940c1c00c501400c40142c12510142c01c810174096604d481c4040d05010700c0c00d8451a08800c8501601d500302103d070640d2112010780b00b17000401951401c41c5407040180100c035808105601e01c2490318200e0b90113440142e000c0d46101158540049172800c8aa1007030a04030149100341100d05840c101c4050310300c0c014110900028280310740a10f14080031a0006403424499895425840150b4401d0007030206c502e08100d0010110b05080001c04112901030340c1740050300c984100e003250303c2d40c001c200381e030303815901c2d484500c01100c12050118001d032010000141d480110301400740614000a854a106000c01c40e204890f40c2c404503c03400000d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 205974001 1250 205972751 205972757
    0x15010b03070201062102030c04062601020903060406020316090302060d0c02100c0203040f0b0301050603070e0f042a0302040b091005120a0617060709090509030408060f16021c 77
    0x241c1d60980124018452980403800240001c042082c603020b851001c600c1c4140243c054075001840780c0144420740f84640715070340341e0b5508200d80718902c50070220f55480854070b0400151800900100080c45d04500ba00d003078419036400800c2c0325148544a54113400d0892500308859110f180d900060740b14000c1c48a081440c9450301d0400504074400d2115800c1c0d22880b0404010b1303e035030100300941d039410034007800d400d18070a5000811551016002d9a04075400186010b04e90740d10540200c4881002c0711640e904090022001c2c0c080707503182d014018a040c0346d506200c0b000210250102c512095102d0282c050620420003484a1003000007122540c0500741c0d22a100b160f000c0f40111f40d2403080003c2d002c0480b50071000d1080300340103a00b000041350000400c0d1402e407106c61450546405013900c00c40c01043c0790036010882c04085800c80b40e4000001401d50b0b00b081c0c2d4460145042003011100c0340d6510b4521010064402601d011400546a80c2d10090840c3c4021088424080d4111440c80c814 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 205975251 1250 205974001 205974007
    0x201030b0301140f01090507090b0403120504090207110f010e010912030c0b19110a020607031d01020f030f0f0403021e100f150b1305060f0d060b03160215010b 70
    0x594600750840b40c2c0c0205500c000d4110f41c502040780d08a010340a0140c400e1403401e01d004180500c0c40740c8620019100000e01c558541441c640d03950302c170340701a0550f03041031000c18000050008118405092854040c40703094458241c81c00400180220341a140c0f4140118000b07410903c0e40c0c030503603400c15a211030501d22208030003410140d038812b030504d0004080c1c0e02c40500300070600d604080c02403440b200810061280450070907080b82503005200754400140d000a000039001071181e04002000c0411040c3c0700c002c024110b08a0b800e990040b40c6000f4060000002e01c070380580103c0301c10341d2201c103040c1d0f180d071141041d542c025100d001c500c801410080320003565112600e41070090f10400c2c10707100800c1000103003041e03050303014082207118450310102d801c00c000f03801001c0070100e910304c2099100c8051040c0c1400c04004640c0c000232280b83d8501d90500c42c040144403035126a81c042d02d41d03990100e840c1d00c0c03d4138003024116407400e605811034108900e10240c0a401c4030300300d07064842940752151 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 205976501 1250 205975251 205975271
    0x3181103070e1e0106021c0513090c0c0b0f01030c030323040617180705040c050c0a0812010f030c0504050c07020414060103110f0405120a050109031716020a020103 72
    0x3190080302d0b0407007101580d5200612140406800d52666103d000303200700003041e0707601c50702a40c407800d0b9441c8a80507451080d0740544468403406c004e05240c07007071f00c440c00852901c9003004001c851001281e0303000325403031120032014400032028107940002da840f4103052a42c110303583d1046110003848002c044c0503499207081550514614401e103103510b141c1c8410745507a03841c0c030000c201c038038400d680040807080d250104049050040860b020507401000502200b86441c09100082403d212003400300304040c0001c0c10080002e000c03002d882405001c040b43c8440341d0040100f03410806070b2100c00740e500070860800008100744644000c4a0b0100c9000601c1d9503580c40007252845026002941b241c0790041e5202d100e2004072040340521000c0c0d0f0104400f2542d14180c1d0b100d4030540c250f590382e0441c140001c10840c030308100d1a224425130001599400f8106503140e44c00c0d01c0c040c5804401250340103c917118101c00b24118198071215848812040e4500c1520207034480181d400c020f410580c4600c00e40b6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 205977751 1250 205976501 205976503
    0x9120f09060313060f2007020a0509090f0f0c1c0b04060209060403080304050d030509030c070326040b0a0311030f0615040b0c0102030402030114010b0307050d0f020a0309110103181103 81
    0x18440f0707400c0306060250540809040000704112145113000d08290f0301107442c14280f2200b03030740c80c0d2903015001071443d0741407404008441d68018013241d103d1003840103107100c0e05c601f840420b0200c3d94820040c262002280c00308150406022003802c03440012500700d502007218031503287d40040d042040180e817424076002003125841103420207481ca60b00001880104070740041d00411102c0c00d660200402d4172103400c5151684609049562140d111410a0020410300010180c1000b02d44100d04a244040380d202903130b54125a114400c101800315041017559094041e40c00c000400c1c6569500e185000d4490041c810b2018282c80e002d5010242d0410341500500304440103002c00e40c0c20240c41d0400c01e06a64042c0d8012602240607500f00074443c01c40c4541590110705031490620202d0440d0342c1e15408490300e0b081520a041250386601c450417044110348001c01d58041c081c0d80128010101d810200700d542e21000b401810949400703500100c80700c2150f1903590155001040c04a0400700000003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 205979001 1250 205977751 205977781
    0x91e03080f34090f0e06030d0509030d143106140301090c090902040f14030106030503030105010507030e09010b091008060907050906040f0f08060709120308040f0b09010509120f090603 81
    0x290708030000c64101041c00a005c0700183e119220490440d030310341a49010868a5000f070326030182e0550b0100f40c92240031030096002041d160505059141452400c1501c8004800782403c454904024481002d0f680480b4445580141103142003511206011280200c1d040c4014460308203031a90b80c1119900b080d21076001d600c02016040d03010b44d00c2c0c1340c03a030340701980302240343c460384503000e007105003a080c2800c040c060341013201c0c0c01c0f40185003140c3c07034400103507070070340c01118120b003003004442c2030781155034804500502030004120503903220f080702d03020311100400c00e46529081c440910100080c5030794900c0d44560003460b51804c0c1c0e071a00c00c004003180181c040e0350044450410b00c004042500c1c0c00110b644011500300c0c004807032150b11947d000340c4620505025084a815602d001d600100340274800742c50b002071003440d100c1804402520b0300400e05805440090903651a0400e00103c090100515606030800c1d121031490014071720500321035413080c080e0041c0251404800203064444500d04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 205980251 1250 205979001 205979009
    0xf030a0203010606020304080c01180e0c071a060f040209031c0207030606180b01110d0305100905180c0307120f11030a0602040e010e130204091e03080f3409 69
    0x3e0020f540c403260041d450b90002d001da00010b100b005420342c1c4540c4241300b036007040c9178a4192042c209080045941f08014020809031002108000d0b4800007030500c554802030b00300340d01c00100c8a0074442c3c00c20403c502c000390900d1065005104034000c5d541e000c46c800301c1c00181ea10724880b00640800085e824542d20f603101900081c0f40c0640041d044185c2c010f00d000000c0000340030046041c81a00558070a5150209100d15510140340701181381e029a110340e8104180307094000b0840d03581e040107003e547c000c803450644c600d150130700c0428000b410400c4090071074045000d02640d50600507091403071010301303801505088090314041d00303025034601c400700c1d4403c2c003a01ba114062030358200034000c0e40c003500c62028078120250001a04180150b112030042e4200800c0c00d4265040740c08100c0900f003898400c2e100910042c1d0059101544010650b0a10344070380c568010500e0139480c0b000c0b00b648020308011800c10650948075000513850031524019017242411598480110303022241c642d001c1d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 205981501 1250 205980251 205980253
    0x7030e03070308040b060301050f010e1e0108010c0e0a0605090108180a030504030308090606060d020705070b0319060b04030503031f030b0a0608010b0a05030c010e01020a0b0c03060102060a0e06060f030a0203 91
    0x8941c0c06041c0c1c8000c1483c8524092000303620302d900c03070505050032900102e428402c5240000018401845c90898440d0000c130807005880c4103c0d4881c03021001544280d20802d280da41d030718240c2d902c85400200c2541451000c640c180e80c914035040000d0400e12078040e00ca810441180d00154210800031502030181c2d00b81411101c120031030f4034000e0140c0e23000380802c1d00465043c100080c240750000a0b2a442403401522450410070001d00507030294000801c1112207010b550004540d120036840590722078881c912000030000c103030740c440a080342d865802403407614500f0002440031900000459030841c4803156000260180007100c4c06522080790002456034031860f003132068115150b0450b2041d146007030b00811242c082e071010800c0c410024420300b501500708000100e429070040c1071413034401106004ac0d44c5441603660302e54030341e01012640ca510b00480841400501c0d40d04002d0f03164400b0042600300705c040b90240c102c9695a000604951050001006c05165074a0601c150071800d0340c090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 205982751 1250 205981501 205981507
    0x50f0706051806160507150c050417061006180902040b03040606050111210c03030406020726070f030e060706090b130c090c1e0e190b030f07030e03 65
    0x200d403520240c64292480b072480d4601100c01a20004003080290054000f0300c2804030818113280103564a8200c0001900c08210b0b2003000f010b004124055032110344529a2415a0f860a0910b8440980c800850790401e40c0c3c407490802c40c00050a11080c010ba510310b050401c09010764021181c40c90072103070400e0120030f0022400040550b40c40000d1801244140014080261160011101302d0740b102070f0843c03950f00c518001c0404840d6418414082a006a03180d86004444143c2529541c42503d048485030303030000e0694248101e02c21a440e0000811001c0c0da02c182c42050040c035a401a0080036180b4207829070b9400c1010b00030001da086011000c0c007155280c00d00d600b40240185401c14064684291180009900c8400907030301c81000d0364440f0040c0c11550030003207850002d1408403900424006070b0081581c0c08080600d404016040340c0e07454640f46c01045040c80341c6111803508503152104082e10138441c0070660410340754840c00741c4080300d5043e915000118007802046614501c140000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 205984001 1250 205982751 205982753
    0x1e05130213060315020903030313021315090606020303093703110f030f0d0510030b0408030103170306150705071703040819050613050307170405041a0906010f050f07 73
    0x9421840490340620040d801130320343e500b028001c1e80f14041030b03250315410420009200302058061120b210380007925960b5510841010402220520300380030a00e140c403183d0410092000307004000c09820144065401d50810080c1e1564030b0180c0e100108181071710592079810b60b80030100b1554107121b01ca15901c03080e8075a0a005d0401c050704225101c00d800b41e515024620880001100d00d01e105da04440780c5056a040e50a800612015281079820b2483c480008045040003241c2e5004501581145980c4d502d94a4404110702142048100703c00c400e204101003980c07040c01140440c10304000450341c4510074a001030400f02c007500081441c0407204212081c43c0d038000b0150080e92a02d10032200f003290100e8075803090141040c0c00403c107521285c0019101c00c100d80074910020701c1030301200e04100316907035a91010150605070b2510b808001c902000249880d020f8108040c00343d031809800300c48020042298498011b10300d41c1400010105900c1c544e2050007160240c116904c2050385900c05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 205985251 1250 205984001 205984039
    0x2209050d0e1003050709050d05160801050f0901060501021207080c100605010908060415020c0a080a020a020a140102100506010207030215030406060b030906070c081209010905101e051302 82
    0x1d4800780149400064810003500920030b480c054607071a114102542e1170304081001401505108403584c0c0200c040303500e002d554070035460007d040c070b420011a5074603004440c0d00143c03c00a0481d62140c0c14190100030603600452003560000310344060035502c1c00076050001580c4240072203914240700782e5210010440b0241d008209640099880c1c47c0e4981d9200201559a0010340300035101c4a060341100c400d101080d401804001e07109001d44400080c3d40d01c50b4200c0c0d03000080740383c1c05600a1504a41185003140408024007a030038801e0514008000c0002d41d603859550030022000c1c3e5510116005a00030002c6200840d8024010006124154505000c0303410076a0100d8082c0d040c0340c008121a0103001c15a80320722007080081440c0e9a5403d0300f2291041c000304181d448220401103903d5002404402a00c00d1a1400c0042440c18052811616014080c099490414035000704c07140280c41448107100c41081d841c5000c50241c8031496040002921143c000f036009503214050011040d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 205986501 1250 205985251 205985267
    0x6010c050d0f032d020901030605030a081306050705100518070605041d06010f05030406020d060902030405070b0903031b100617101103040201050310050406080a020f0d022209050d 79
    0x94590b003d0189184103804d11040c80039003011002c00420906040c030140c1100e5001d0045c4074014940030580c0c0d82c4d16004079041841191040c0d50050f0002000e074030165240c48008000d04103407410514160090b2107564441680d0300d84428000d40710320214191008a01150100400400070369071155a568005086039000e03124071005818046035540112520240c13191143c04180c40e0403e5401d024a4100c96a82c4024001c1b44c0e11603007404004d1410b40380744241e9020b021140c0005940e802e25040c00341c500601a80201000d00b4204200314043d200801134411b02c100038207030006e84440594003607040181c502c510300e1203140f030243c000600240312122800c0c0c0c100041c007a02d9828200c9a030000990f1a400b00c410f480010130004140194070450003150300c04c60140201c00007649030000581900c140e0b61040005901c000104e40a51a050303501c0b800344e00040328800380c10702d0158046518041804440e03800c040c03901d4488010103000341c018002040d40041540d001401034030018000903 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 205987751 1250 205986501 205986527
    0x3021804050a090507050907020c0d063b0714060a0306080d020c100906050f1b0f0d17040f08030601050f0706060e07080403090b030603010e030315012601060806010c050d 75
    0x310440000103594280301f011280604000c2e4040c2000440480901c80c018500f0030b000c031602642e0310b2282c04400e007000480001241c040402d0f03580754149004019801c2202480040a90000c039801c2260f000d956082102c1c2403015901d0303c2c0c580780340c000700f50014141c590012030940114142c18115650120301d00340303582001c440c446822003240b181220303036030814065980815800c0200450030841d500107004100d00c0c00700c54004c50703100001101e040048034481c1c4403043d400300c05803101c4160480f010020003d031901e000c617540e1900703440d9000c03100303031074980640300d800d000010403116449142140c1000385c1e4003d00660300d00b29850060018083d51040180414004c00070948243c451584140260f806a0b2030345e07449400c0210080b910340c0040c20149d8159a200c41a94644509101071442085808180c00a040d41030001600c1003e60056000614040d000070740201c50b02c080c1c1c01c03030544032a03141c6035965948040043c1c4d0b84682c00c802c0039045100380d510807c5443c1c1c0c4801024008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 205989001 1250 205987751 205987753
    0x83f12010504060b03010b03040201051602030307050d030606030b0a050d0203150c0a2a061a040606020609010e03041d100905010e0412050405030a02091e09070303110303060109030303021804050a0905 88
    0x40e984d50740000810340070a00502c2d81c51142040810090341c4240060900c25031920030000340c40b40700d41e0009245a00810048426401141c003521a451301440f80300010205400c0611048031000c00081d007507501030044510a03050030110311700b03546041080c540c2c5110201c200c0c240c542495000b40c0d40c19000707098001d0001b0b4000d60148a620740701d40440c00d81c054400c03400b4403409029595803005d040d00c017110740c98142c00c418070407103540d031940251401070040d500603005a05040c0100c6096410542d402d034440e47c0100801c02c444107491545803171480c03002c075150b0117907202d6a61104260143c1e0b44041da1450601c000807448004040d56513005612030100317030030001c05101054440d80160700c1903a034036030408641c400260400c03c81c0e0aa020420740c8558a40d428140340d6900c0150041c0c81d100140d9004910038410190003911b070342c11811101000b14114509800000c0011945000090030540c0106510303000700c0d001c68103400315500090043c0404c0c03400240410003041001415902 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 205990251 1250 205989001 205989011
    0x7090f050d030c020607060b04151d01150809030708190e120304120503070f0b0403080903070c1a12071d040b09010303030e0a0b150a083f12010504 65
    0x1245001c010180c2015419120022103500d180c08000d115042150203440d060349070b1130228000d50380d600c94205085202640d0040315800c05031b0903041c0d10480b176503980742d128064006224a51081c400c4140c044140d2030a03510075642c1100071800c60084060080c0f541c40c0c040b800c849007000c0c1c0460042c0380ca20955035024482e06801c10440c00094402d480702030341e04100020320006e0917003d1400c00050040d41100d140c5455680e49019080c94bc04060b244d03045150309010426078889819900f0035561b000450405400340c58040e2451421310402e01269074101d00c80e0306211000c0291040d44031340700c0b03030036400745403140001c2d00310464010f5980c0e0310040240c00d00100c0c5040d104500b040d80f4040d01c01e480580c25a901600240250b9110458030300c914905c03000010f4030100f24a125420a40018031150502c600780404440d0a40141c00d0540202901c2ca450039100041140021303c5900c0703482014454103d6440308800894110754021b1002a21140c101c19504105040703480c01d80e01040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 205991501 1250 205990251 205990259
    0x60c1724040c0c03031a12010219050307080609070c061b300c03020408030a02070503060c1215010311040e180109021008040507050402030115030509190201050c120307090f 76
    0x1200c0b076036040e480200d19070100b4603021922035407180082041e20302c00f901d00d80b20040300050221841c2c28048109079000038a6070102d19030300d0303980000160541003150442c104802c02500100e07008085901401c49100002c81c06e074494000f0304222900103001300080c580c610031040d08415595410804540084607400400c1c120420450111200d0300c400055240b01d881c140d0042e102001050b41010303000e11000c90440030510003000d402038613800030000149040241801e2070401810b01d480f010003444a0b92020140c0310f40d20354030464070100710840c10000c1c4016802098026194154544003040100c2e40342c050084040c01111002c0380070882040345620b090030ba0320300040c0250020390f115600d02c000f5024501803a00548a04107890382c1640b0b90010400302d810982c41002da09041c003010070441c81d018840c0c1038011480101802c080000c000b084951b0007000c0c0c0b002030412000148038a5203481c01d0040207480c2d80500e00b00ca941e0300f80b070702000300005d10501903010030b94000302d4001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 205992751 1250 205991501 205991509
    0xf0e090307120206090d090f0603020c010e07060c051908030a0b03012c060108061501050a030f021c140402060f0f040504050108060403020d020706020721230705010e0d060c1724 78
    0x14084500c0d01309148039050602004030040d41002004100c1d564840363b079101444402d02c40000548441c0e9150000c440e101d0400070300d0b02608906240c42c08104e04409404507070708408881c0d20841d0240045010503c038004203004040000c1820035140d091009800e00000d11640826901c03202800c0325101d98a4010181d02e80d00c09541d015041c0c070529021107440d501600251507014080d080000b0451001101a03042c0d0340403020380440d4444c541010860002a8415191100e030954480800c625082d0b002c00e03c28410b00c0d000d034804490120380c0103222180d0504540290001030014010380d44d65128042d5601000d540803809801840340300c102c0d6900c005110001c80d40c0b10342c0244151403502e40041140004170050030101c02c50041038201140f1090504440da20342640780b0110000c000303c1007401d021481e0090760400084d0540b07402c7d160388100b8582a0a50400e40016014880e440c05444e4861104240c0c0c1254012031708000e16182c0c02c41111241019800139182c149001a00b04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 205994001 1250 205992751 205992767
    0x10603110c0d0f050d11120106022413150203070314240a0b0c1b01051608031305060412020607090302060307031a0a09061703040f0e090307120206090d 67
    0x8510b58400c2c000c030300040e40300341a14464000d260421038a42044512450141e61015071856040c0e600003035098100480b000300d6900412061010307119000c000703001c400001e0744404021100d016008045490b0b40600800800c50a920011080c604030549440e040079402c00c859000200380b41c80101d060725001914141d1040c032540407000340c1c80b1014007000c0006000d04500f943c00c249150400310300080448010400b20720000002c101044181d4808150703064943c0d0748038100712040c004c42030010725100701c0e46407881c1e02c1007405807a9581c1c12217040c2c850342544006002c521035403007803001340882c15448541090241d4292885d40d5603004043c3c2d1035250b80d100082d0050400c00c0050a0b242c0b0a13401480484540760b503c2c030900c1d41d02c070005448004690021a080c81e0b0b250300070800007030301c01c41980a00200f5405142810b1034040b0041290401c0c0c45002c008041c00000501a8107060044448450380508031121001250304000d6032780c0401c0b00c41280901c00c0c1c4006458140c000d000d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 205995251 1250 205994001 205994017
    0x4020c1506011b030f050706050f04120201111602190f09050903090904020f03010f150603050f0f0c0a090b070f140c06031303110f0a03020601090e03040504112101060311 75
    0x1103003d074040c45640483e8100100508203080100078401803002031024011a8040c0c80c55058082603030902d800c09904032014440d24809681c5030401900c1458540410364640110619001c800b506440c000b0a284000035440c0599121724580c01003031a1001202000c2603c42020040045075075450015a423803103a00c4000e0f41c041800c41c00200103240c82040c03008195009000403610400c080d00b05000e580402c001c0360b4120480f0b01c003c0c003040d5458410701d80e0101c0d011910ad260f905010401c0b00d10043e01400031508100d0000b45120000d010704840300080014000f015034030085070802523900180202c00712403800c012102c0f51004000007541400080c0e00400d10703403440d02e502000040f0000c030040d0441c14420340b150700d2414242e00b4401158501d0b0b0309405043d11201720b11b0001e0030048140c1080303010f40e28002d07085004102c000292419200c082d60000344644030a502070087d402044900c0c06400300d24201010100440e00300241214840d40381031195060700882301c56503000b00b81c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 205996501 1250 205995251 205995287
    0x34080d020a060209061306020309030c1f1817010516210b0f0918010e06070f0f030605091305010b0609011e0903050a0501021e030705030a051504020c150601 69
    0xa5001c08244982c0c001e11240000401503407401100828040c0d140ca403550142e400351304003044402260405020065556504542581802d0700b49103900c0040c074503103115003040100d000d10480c0c0080d003140e041000741210204d403903100f10307414800034082c200c21141c0303621803003440e10140c42c03d030300814058011a024146000fa402492a089802000280174055001400c034440290a8460700006030040c1d5000801c41d11502c01c0307419550075160103a01c0c1298030341c040e00421a07001d601580c01080c80c18070b40741040200c080014102c01400e201c0d0001ca81c403a42c650300744500c0d01d00302c68420201600c1903000703020f220b061504203e01e500904000703d02007044030100300e402000300000c150351190b050502005c159260b40b43e43e45040b1032100e00300da25070360001e40d10450b01c5407120b900d5a0010b040380800e1541c1381c000b2000341580406800c550b60359494901080402c0c0c3d1440000784c0d040c1c0e0180085440300c0903803031055554180c6c0f807a05e281c1c408a61001c928a5481441ca151084440030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 205997751 1250 205996501 205996513
    0x1030c050a090e0d030c0e1302070c08030a05120402031005090a0c150c03030b0301200705060a11071101030b030f2503030e2b0b0a0c021c030e34080d02 67
    0x44c01540035048a106090400803400140485070307803141d411000c500e441c0c060040c0c071401c1600d8409010080d40e080440c1c5580103005003100160b108045030703081c005030082c412194886101003850103030448907a000f480d06040c02c10284200014100c00082e001394181740b001e0303a580490385810a800081d280010702803506000120f4042d4210702000c0b840a4000140d80c01041341c0803000d20b101c42c040d03108423080022902c080c041e04105141e0001c07211a010425001741c5051000c40c0e10401b60000e010116004200300668000d6011014641019095401440032184000d84440500c0c0080301403001004402c8080c1502e40c514005995142d00c403000a25404020010000500000d507000d4041e54514103c158101c0201040980d1189209403698104400380d00c082d07403e0070941030119030102e806203842c0c480d40200c3c42085141c5040006080791050303030345410424100140721040c504c604200c8800035802c94140e500d42c0100082d07501c4a500ca030009515000303034264101c0103901070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 205999001 1250 205997751 205997773
    0x712090e011a041d190506030c0108221b080a1203091401020d0225020a090b030c0303070f0b01051c120c050f010c080106030b061207051201030c050a090e 68
    0x22007070400c2c4000100307801800d0079a07551212006001305050207208105110501203102000d202050743c9116105007403001c0d10308640407995581e021880c0c94100b00400000c5068000703609040040c983c08107100028002c10790030800100c0241c4644614884e4244d400001c400300082050107041e036204000600c6904c0d842c008a000d400720000c21769542d01c40010700d4850400910007440349020124000d038590034450704640c00303020b1120007911074202102030100103270b40304000d60701503c0b40c2600000d99085000b000c60b240c90880307249203801d44000100801444038031b01d1701120180c4141000e84480e81c0382c00500c0720181d40880c10b00c240c7e20451161000190035401035080076080c511f00100e400d91035403a80e9141c042c84c1d2900e1102c9035500d0940c1100651302400e0a8050500da040070312051481d14049000ca2041c001c0882c200c140e42004191054840c10031191110300d0b441c500241541c49041100c50030f81d0b43d100c1d15200b105d40300b1300000c01c080d10f8010013034800e000e0030182a680004c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 206000251 1250 205999001 205999019
    0xf1608011e050a0807030605180a0224070f110d0201122004120c050105040b07150906020f0a11010b0618011e03020c010f0b0d0f0c0e0106050712090e01 67
    0x880710804025000400c020610340c45029004008040c80b8005160b03151035420020300f22280900858950032107115400c640ca03200150510005906940b40314580c2e444c80b140c030010300c00e680c4041c0d0b01420005021400d001918000c00c5d151130048003420007080940c4200000c41e240804c000303010800961082c10346c0c08050340241c508200c16010040c03c00c43c15105900140d005402c11080850031240400600100020400281c0030a09100d8603103802c001d5a98202e000f03004005109018a1240101c17860b1150052860f45511540a6481d030820150700f04007904600041d50005e49003803001910000c0500a640041c4005801c081c60700800b180401220204050128140154225010341c07221151500031804211a0f07401a19491245a503e0950f03001e9800d010285080c01105d803010b9840d00e0820480303c0e40440e12640c1419246840303132000b03100b6400b00300500d4542000168a0b50004020306803140b08484005417003c0098064401d140e941c001d060070742e80214010f00141320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 206001501 1250 206000251 206000279
    0xb1c021306081518090d0309260f07030507120c02130902060c2b09051809250302090a090b01090f0207020307090605211b06160b0f160801 61
    0x96450f00394103d0205440880c3d4188040c0c2c21010401030b2010070070a041c0300501100b00072000500d414010f1102d5516010b060b4200361607aa8405100c8000c1e0b20035060511048580c0c03034149103901501c4002e81c1c10003800a803c07000080e2601120f04604a072014414210490720507401420180001200140440140f8642c3d4040340c0012007088030156299003004400802c11071440300d80403880a04480c1c0c0000d0900909041c2440015401805690340700f40c540100410040e4030f01078580c1d9240880e0b89014850302042e0451107041c032040a500801141c01c0d03090300c0c001e40e440c0c81940c1b01e40b4200d00444100c00005000748001c107005000c2c440c9207400503110303105d0020016050541d00d4000a041c41910b034001d60585a844104200f507007098403881c1915118100c80c0600f004501d04050f0700c038008140f9940208044454606c0556104000d60300c018801010001d0000304914099024010036100f145600810500103078002031071540525880001d80c2d110003150340b0745029030000c0c83c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 206002751 1250 206001501 206001511
    0x6020a080a030f05240a031707050c060310030b011203020a150609020f04030204060909080d0b06070602041706090f0307030e040609180308070309200a030c0b1c02130608 75
    0x562a1070400143c81c03a103009040c01150211201e0b1606008146580c456000358200c6a0152803040c004002261401b0541031185d6800c01c00b01e66181c3c6240350050515409034400d41d0b01110210900c115181c0381010307003042d01e204160300b0440f643c8a14090150036800f042c001c0041e40311302e0603407000408150402c0c03560b1821700400b044d800d444009107400e0f40c00589003105020b5001c201041949482c0c042e00004009550382000f0900564880342c51520402c284c2c0c005d01a103032200c200b1030b920703150100c465103a0080c3c01103440d1500d649403c42d00c0c10000c07401d03e15510074540070800c29400410310011144d1820002d5180c51032076642510a8008000780551287da07400b0300042c550350341c2c00740c1b01510303082c1e90302e44525a07000d20b4081e00709075001c0c1c00c5104241c500b8068400082182d8a9101c103000302c1e01c40b0180d0780540500180c00503200b504001e00c030710100c40b4002541580c0c030003d032102d8100404003071030851000007044100d004034860102e1800280004002d058064450180c100c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 206004001 1250 206002751 206002757
    0x2040503150f060418031805040501060c0203060a060b03063a03080603150a0b011101060303020a020307090b09061c0f060e0d051207050307021606020303010f0b03090c0f190b0c12030106020a080a 86
    0x4623986000060441e0400d07484070010804a10419085240c21302185900c9807040c281008140c0c28164403c0366408028032860040e040ca80c0041000c40000512080c012448000c608440f1075880c40c0e038040031010081100428000c20210b0307090310f0086812080d98a0070901e088080d9608000f4502400c1491101c50601903040c0c0221542c640a0003044003039070207900202810001d903c1132628160080d0b1140741450718081c017218007a83c034800c00315003024085600c0c05011800c20101300d9041b40a0200403d01c00c484d0200c441000303d9a00a40d02062400003503030445030140300c3c01e9605118010b000d440c560240d5002a4a050144010b144c100c030341ca2044030301c0c454003403c071408a8032081c0c000d41302582c8080f0040144280944a050161444d03000d5a8154100841825903c85181058a114640c0342c1104070b00d6481d024082182c1c0ea402c8100903c4055403131000d04210740c045060700d0311030700440d030000b103456030200202d82c101c81c05a40104000389403501e8115650300301002d24810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 206005251 1250 206004001 206004047
    0x5041a041d060f06031005060c011401060216090506150d0f0506040c05040e07110d030510060509060702010309030513090b030f07061409060d020c03090a0e0c0f030a02040503150f06041803 83
    0x107e61600809403140c01d030020000990040321844102d01d074401640050110760088000414946114105500710f40e20144007041d143c0f2100d002541010401802e42448074020603040200c0c0415005607201c600031081c10060303900d0304400e10007502c0780c1039600404a04104030403c0039801680703000e5400071452505101c8035074070074480c0d410008180c101000090321003040c4182840c00c14001001800d290410a240403800000305003107004010300a41070680d548102818940904c0481c2d281d5032203031038919582910b42c810340700286001e4224500030b120b040c04d801616032000504800755982030310f07050f45188440c41280225444096120b401c207034107000480001102d4000b40400314003050155444042079010710600380941c0d80000b4240340400184842e0702e031030307004a0740c801440d0039940b0b0f075070395800c00c41070081d00c19580704070340500c10740d080c00307001000388102540101e00c4005804c5041e04e500c0d00700300550b02140100c26000c02460a00030020740950140d0b903200140d028180c0c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 206006501 1250 206005251 206005259
    0xb0310031403030403020c063a0609021e073309030804032c040914120a180f05010302070213060e18030f0706090305041a041d060f060310 61
    0xa160120003003003141c0e5002100340000c04d6014804001c40300307400e444080c2000f000d00341c82c11400203500380a0400313a010030710010140d4410034011907205107600007403241c80e55801c1c44000075440000d004032101c0d6200b24040002c3c51880c1141d0550350042e24000c266543c40007000c00c0354400c8540d03990904210307880c61410360715500030a5103c0740281c07202c0c80366240134100034222550a41d182440035084038828681000300329524800d20500b40c07400207410f84103150480d00d884c0c8046070030355548112031010101401420091a0f4084644d60303074116a480e03030724402c1840030a401244c4400d0070700c0c0d000780020b503c40c0e80a408114001441810185d451409110071101d154005140c042800d608201e041d09003252030001d05c00035000250318180b041c1724403184601481000824050312814118103051051081d18081e000744000b0414000c100203004810380d01501c0303070341c9401610f1030a0510400c0a080624880d000240c0b0301c0340909000c904220300e990000307042c00a0304240c0d800c003203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 206007751 1250 206006501 206006513
    0x8060d060e07173405090c0d0c050a0203070308040f02100c11010903020901050f010908030c060702370c12050606031b0a030308041e060b100807090b031003 69
    0x305190401c803016022060428050180c510b0022500c07880550104194008203401c503c00030307a030f0030361501440c81026266142001011303110b03400113900c0140c501c02d0150b600d0020006120280c085181003003c401e0016042c1c0755070081d8820500276810500200020a00441c51254414850304a41445500e9640000c040c14070003201440019140d40400041001d40d48401980c03640908000014614650004002e200f05001c1c15000c0d103d034500c086070a0740603940e000007401c0364409507502c0c1d001c0c800c4910b94800c821944d800061082c070f540040000c17001c0d60410b0015000d101080240c0c54003e1391603410400011302180ca0400006002554205500360502494450300180115041250801d031820400f402040070850704020030680035503980f10103500b2203505003071030350f011340e21810209415418155540d642124010001c403c1003400d60107507540d04003c4a4041004400d4102154255000c8a0001c08200501c1301401403400c103002569100b01c0041d051810542c81e9507030310f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 206009001 1250 206007751 206007761
    0xb01121e15020a030f0c09050a14031c0f120b03070501051602060a020d020d0921051203190b03010e0a02090a0f0c0504050907020610061d0a0f0f0806040f03030b18010312030b06180108060d06 84
    0x334006a80c140c1e5140407241c0c00001864610b4042e1000d0040c0795200340042c0c1c880249115803414801e000a0050082c007a108040c201103400a203819151035131301b0401303511121004aa4401800307201c04041d40c032400b40010100b500c641c201156601000011800707041d00003500c003900d4a02ca200b007034418410503480150312400800d82c00950082c6e4000c01072054032580e4205034403a174100400c042c076903c0002044070b58030360125030721840b98968150f003400606884000c61201820700045c0301d000e0f50004018401c13114142c0d0059010344da0503100f00c0c4c4444d02900d40d8104207014900030025544074906036410000142605c2e000300c44d1500c006503291000c2d61240300d50380c00b8420100042850400801e0007000c660000d40150300e0103607500705010320040c400500349580c4006940d240c1d126401182011025225414650358581c244120b4500142c0c41c540002410161078500c141407880595003086009030071503042408503001076485420041000b5080145042c0031401b00c1e07018040d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 206010251 1250 206009001 206009053
    0x90109020406091d0403181203030902010f0201050f0c0901110f010c0e03030f04050409060e0604051e150c030c090316030b01121e15020a030f0c09050a1403 69
    0x4016a52440d00700050800c3c0e42c03540c06841d244218002008040f035604540d158032580c140741039074080c040041601c5503442d01d500b01b09142008040c41b04101a0554400d101490007626542c0c0f070b00013070400c200d0984001300c590040090002000c1103040305860003501202a05040c624109103d0742c440743d203010700103100444c02c1da4548128241d240e41040110505500907000745103088a80107203601e16101d14407881e4002c1e60781d908502e09001d0300c1d074460440c4111040035030348181031900301070b50b640c801000a07100041c0e0380c8010007100500090003020020301c400301040340b076641e4403a0500b1a0030061070325100c0ea0742041982020b40c0c0a104025400f10f20100c0c44000038110b0411103045101600007440c0c00e0001403540c00800e20201d0b500002c400f00141030918020b45151161403078059112565001c1c0c00410198040381e010b8001411100100c0700400c04107407107400450f0b82e000030744101500004406424040d42195080480f1391500160448010014040740c548445071050340c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 206011501 1250 206010251 206010269
    0x3090613030c050a0608070c02040b0d080304032a020405040c0905010602060a051e01090207061b090503120702010807050c19060203090d030c092106060e010f09050f16020c0901 78
    0x100c1402000307034440180b0040c0406554034281d0505042024014080141c140020304c07003440b0407041150380c0c5030809401c2e02c0020f0245c28280703d25142c015400d4000b40c4040300801d20f0142c00201d82030b129500d42d184500c040065414501098084c40010000a0400d4440e581c032044003180c04444c03402000d0013003400398000d003c6031a002c0c201c4000c540300509151003d4154070b505d030b12040054401d607810b4400a034001a540d0b0811700e4030f40000d1060305107840440080711129012290010414800c54400f40c007035820001d82500e00d071000d4403c606000740072920440200d10402e1080014061040c1a5811260740e144018000480803030800c03002c03a5020780000c2013140d4503d080c06202c1004065080600c01082b100c00b010700300500500400702b00031400303192404060070825108110a030080010016a5140c040399840d9100901641020000100000582640e540320ba1032007030300c42c4005860360f034030741d40900c2c0100000715694004502c030306003e005440d50b41e030f070b811402450010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 206012751 1250 206011501 206011537
    0xa24211205030403020f0a02031c0203190206060a090605090c0702060d090f1101031b050a05090d0f020a060c030e040b04020705010c0e030c031609200403050a0516080a020909030906 80
    0x11030b00900e1b1011401c0001d66a401c59001c41d00161000030344040750742c1800b100c08510700ca040c0c0d4101c0ca1400342070b0f1600402000c2d1205a084030b5004110300e030140d0410703581c500c0c1142e112552042a103100e8483c1541085415000490019075403010b01070552004041d9843c00c41ca00303400c0b07030a5806200301640c220071a04c0c5030f20104950b16805420204080c2010b01c41760403855400801d05030002454814448001081450684910304882503014003c1c070801400000b402c14507540000b007101203000d0382031600b020509034000c0c4807081e85c01e607140d592250b090b5803160a101c040d00e0100e4403d50070940a2102c1d8000030b0081c00352030700c1020b0390b5985007806100d2104144c42c0c401e21a2045000c0d41000e21806100000f0f0444901a603020000104000c01180104a11281c00b5050f06152000105000c42080004648a0b010324026000c5411080460400c00e04200304d5220b904140d030310411003100181048058242e020550000340c904203c2d4030801324071a5808034503c1c00180d0703482 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 206014001 1250 206012751 206012753
    0x122004092009130b04030804060204080109050c0307090b06030c070c0906060302030f0709060509191d1602030301050120010b06130611060402010503040b040f0f08030a242112050304 80
    0x10314002c0d40d00c454030041c032001032100342d03c4602c1c0948000c0d00c09010808007400003010f010140e0122001081c945000304041c10850903d982c680400d9141c0c280300b40a000e00c0003d40342e40f43e004409421800800c940d01d161184d082c1403da070703030102c030044401d2141014001080b14207840707410001c041e00d890140e40c0303241501402c042d8480061071706062003001201403100950100940b81146001d8501d481c041c95821205c4030b13102002c4c0d001c0d02a19242a40b06624086aa046a4054410300401240d500c0c1c09060503a1280424080c0e01d002603480383c40c20520058180c1e104204110700b100005081c5280b6000c1002d176480040103c4c03107104862020826150300200c0d050310800100c000d400c80c0d00f03256000802078440607001403d80341315580841c0074003840c0d240044100d580010350b1f07000401c40b89014000d54000300c03401e0a42038584000ca000190120b0620100d4102489514034442d0030510a81c4244560701007031401a030880128200140080380740926081c0f068840c1520f901e45 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 206015251 1250 206014001 206014009
    0x2010201140702060604021c090809180106080408030403030b030706050a0f090f1203050d09201002121608130e0c1603050915160209011220040920 65
    0x2494407071003020403541007040445030b070100b00240c004204035000760740c0707040c04502001150076490140e03800c80e1514000e14204190400100340100d0309840f00701008070340700d0f2a030100300070900c00c41d004202d1150001c0d0004034200015079000c0e1187c1000101014a6000310703203050b20ba41c00080100f100000d01e2084643c1080440101c07442d645804080f490411080c002d1500305840b810300d1000c0d801c980841014018002d03150030040440b81041015024103144115040c0842c04a90801c0140785194250408601131065144180c000b084000c1100c044207416a010300b49890b05000c1c40c425260014403010b00410f28070641200035001c15082c2004001c4811024107000305041082180c00c0d4101051038583c080c60707805050068440380f045000c140e040c4c442c1c004940701414002001c0844460354801c4111450081e01c070010503a03200c180840208a05100250031001581041150a0620580048105c3c0060b102140343d003587ea0b1900f042c400180c103240012001d50480f1011814 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 206016501 1250 206015251 206015261
    0x150601090e10050103063c030206030f040c0906080616021c02030d0c051c020903030904020c0a061d0304030b04050a02060301030b010e070e0109050603100302090a0209152503020f010f020702010201 87
    0x50110700c4644984901c83c028845c47c1034060703024a890781000f4201c0d44030601c00c3c4030700c0b006503009004169640317000d00d601c40c900c51080760201c8440021180210320b800c150302c100e17816560722031700801c1d00d51030f803612070284900140215000c40c807071924444000f40254842500e401c0035600103503158044404480b007aa200981c0c4042001801d000c08001e4010750a0901120288014016031b10300b500d02c00b1904505c40c140d902504240001103d0780a0400003c440500600942041004c10110182032280c0903038281c075401994401e010600100350b075900c001da0000d10402c01c99201048540c0800e40513082680182d071208040e00041004a110908013540b1240c10b00e0007a1840c0d00c84400600002c1c840e00610780240700c017100080b8801003a902040146400500d0003880c0d2911000d1800658003030b2090902955601440c15220f403489800e80302003119903c8000c2e0384560300c420203900008070010590841c4180d41d40000785070700a06c2a500a020144000344c0d0341c403501c0c000642594 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 206017751 1250 206016501 206016509
    0x21020c040b010e1011120705060f04111002010207050d0807180b03150f0301110d060f0533030403020604022805060c07050a0f03020114040305150601090e1005010306 73
    0x1414030203000402d0381d1280748101c10800480f00035980028104044404955480d080800e91048504243c114030408010700319051080080341c485079a0080715400b0010b042d60010300b114240e101c072001c203207042000d5001c00302141c400142050083c0d1180b5261403001d880701804500f100c010b0020711644030078410840c29a2641c140aa039151a100e01304520000300220540d141400385800140d032083e0507020014070080c000e10a40f5212031005d004c0764400140a480240741074800140d0740c141e03004400440710018480c2c05592141461920355403090000c6140f0608a551008041c1082c0005140a00c1c001d1340108100e1516205120604901071400b00900310040c0c800e0101010030a0300c0d100f9520b09440d41034560001544841c98800150040c0340d00c110600780102e07480555850305821a4000da0341c04c03a0407544141c2c0344010344240e000c00b0780560440c00d8140d01051504100c6d0703410a03410316124490036921518010401415150135203010700b001810003d56130b05014a4002e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 206019001 1250 206017751 206017759
    0x140f0f0d06060f0f06091805040309080f010c0315050a0e04080708030a020d0b0f0d14160305210c060a0908040515030711010e070e040213380105030c090d21020c 71
    0x61820601e180300030409540080c0368040c3c41c1d2340000c04151041c92504001e215880407520300030001880c407406800d9622891001900d0414100c03400e4144034800d004950020707000042160038003034140030580000b0300a5420b003200b080311000089038800114421450f04c20300680304c4801800000954004120b000d1046540c1e10302000190744452100c004154081d00c2c00b610035080c070b00301360700301640e00e04000c1010441400010a000c00802c2d002451500b01c40c080c1c4801c02c050186690030b025404501e0880d030711107c0011002200c0d581304500042c0100051401c2a0340c41e0000b4200f07940c6001c0c1d11104040101c1800306403a0030203240221403c80c08024008000d4800c1d800380e848065228090050040c44040380c2135480740b00700f420303d04c022040c05000b8501c0005070333002032100100f0003244485480d00d82c2c14000360804980500160142e6a147c07035a12103a806d0025030304010b01555004250034102e50000d60718cc030140c0e4010021741c14500d408282094003070304000a032548a40a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 206020251 1250 206019001 206019017
    0xd02070605090907020c1509040506060a0903170f04090f2d110903010e0d0f020a1a07020f06040c180506030613030908190b01140f0f0d06060f0f06 65
    0x322030342110503a42c01c00c40584085241d9961080e040b8942040c038804560001541c0e20880d10002003030700100001d032030582d401e00c19034641c44240300c000d20501d10000002817030707a6424800651140f18141280324a883d1a40c1800346443d403850312948964029441386a6803140e0028400040c0150041808207100785490740942115460988114540e040703000c66903235501e0f04040140e1000e440c039200e4041e0081151100528103a5500e0303101d03c0f03c18010410240030f0155075807002074001c02e499070080c1d880d20780e50f00c4a41d510305028809050b1105600800c1c1c2c6d84151a8401c00003244514000d0040d00000386c03501c2078041190012020b5101c10364144400c00c0400d4600041c2281c0101911280003503140a5050441720041d260304060828000c814401c04010344001c29001124020211448140d03a07404158070000011042e0a030030000500d080303c00b6103420440c400359981301500001140c1501e030b444404807081c0e6001999200705030b403011b2090300c500c601024003030300702402c0c041c075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 206021501 1250 206020251 206020259
    0xf070e010e01051309060b03040201020f0d0203040618080a050c0a050a0501020a02130e030c0606040c09030201020a1203060f0603020c01140f04060506040b04050109091a0601050f0c010b120d020d0207 88
    0x4401014000802e061100c00140c900a2441c410180b500401e4420003c108890700c0b42600461540261410380c01482003003418612040301207201c1d945402c4c40d40040d8a842c2c5055001d490403880764402e0500c036920f582000172000070a010f0540c00303034031920180070410505001c01540c21159000030b030250720200302c2404166000690025800d40464105943c0d09070f506500018103800560b03500280804101d110600d01d00040305805440b044509120040d44d203041210221440d10020f80182d1201c1c0c0d59002060701100320f1030030b152803460f000c1a82038440c64036980e5074459506c240000780d0b00042c0d84490410a01c07903214101585551b440035030500c00d0f4a40c4c901e1201800162400b655000031654983d0341d64411075003950040d1050142d5030f55000240010243e42e0002e6a424148040e4200059140c101440c85504140c403403c0c10100841c400c03000341d420034180c0e045590b50314031100a0079a2a500c0341690499584018046041c031050002d003462007403101310095512081d0240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 206022751 1250 206021501 206021507
    0x702061c050f131b0503010606050c0d051323040e0706180311060a0315030f14010903080a0216051603170a09050103090510060906080c2202031f08060f070e01 70
    0x10041c16000313507011880038000c41085a40c0311840d40001d51540c41c03c41e0002d40300d03030044040c0448261050555400f01041101a00c6ca8410040d040140c50300c00c0206004000d14800e1074140121070580321a000711074030000c90100c41e1140404101984092070400c0025071000441700072020f00305507140307442d242d5511a000301081d243c01d42e10925000c100460b81340d22a521941e840c0c0c4110000100c02c540d0380c00e00c180b0698240c07a080d0361030780c003009a203400aa03050150f0010b4a0b810750700e2000c80c0e6980c9110340b0080d0071452466041e031b12441220f00c04114100100040700491001030808140b540c501200d4107042d485010b1910303142031002070300c1da50700411414111482802c3c042183c064603d040d60800c1d50041d8107000992401c11f021490340c19135442001591440c81c122415514040204800e54000b0110503462480b03981c0400b101a03500c0d00a950004544442d04070009920340600b01c000c81d4980080b0703d191301240c1003188171348480060035004881b5041c1030281c1004c4c24002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 206024001 1250 206022751 206022781
    0x2072d15151e09050c0c030316030b040c020c0402093c01020712020d2d0c0812040314010902060c01090c09110318100e0705030f01020f030103060c02030702061c050f 73
    0x400756514030028245c841c00e070781200c4d503540040e82030740d60728605444000c0007001459443e4001178079202d03449107142490b20513481d844070707030750014045640010200b0000e94031143d0a69000710159680c0303550200300c0c04a031031005d8403482c0c001801707115081d005940c0300007104032641194400502005400b030b041102115142d015180e408201445060004600c0395004c1012151129864041c80b80d0751401d4050040c10322601074203ca05a90f1315000742da44134503014107520840100010000580c4e5820903203101c60b050700011481e88a203400090ba9a0403082d000c2c1d910740d4640500c0c1040184c00d06818015000d0030701c08000302440740d05000446d0100404d14001a980180701c840548410441c14181e20340310142404003442d00107483e61510403500ca00d40c02403041031400909988180240c90054065103001402c6a1940d00d450001d0b140c80d0001c4000d600007000603001584585d801006100c05d0880c1c1111a49a030300401c02c04c5550040c40d42c12604c4155080c800d40b10035005030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 206025251 1250 206024001 206024009
    0x60906090103081623070f26010e1203070908060f1603060807080a0204051b0a12060801020a080915060102030f130b070b0702060a02072d15151e 64
    0x5103071520807820302500c01448615002c1c01c9900e41788524014082c80340008000e0500e11010740c1c4940e50b49030b204500b120044e014918030b00e031240c40c1503141c100381404460b44261700c410011454050110056042c2010400003105541000040014180d004255000104000c0c0d009001301d203801420408070304406000b640118103d0482c07a4007880c880e41141010380404000c0e5a040e81d5030340e01d010740c0e40312114403c9000318200000218840c0340c0b9015120f008404036546840c000c608c2d172040360078500408015031450742c0c844010800b84005d1000d0005040180c8a114260034509000d41c60464102c2651941ca15804200902a6030102c02d480a0090007040261280441683d1110001c1c1030f0f0041860900c0c0404c03964248919000864016880d41d000da400513152074960000303903c0f402d40d014000d142c0d1f03904d00549441002075000c1c1502629245010205040e0340c9001d5405090441800c640e0f4840d181c00134a000812401c1c4010881c009403c091051480c1c0c12000180240c0303d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 206026501 1250 206025251 206025263
    0x61e0406091a0a0b15090a030f03091e061403040201020c04020f041206050403091d01230909010c08060a03020108010b18030a08070c05060307120b0109090e0a0506060906090103 78
    0x1c1c4040c20400841404000402c40c01c400325840d00c1d00e200c0840080c0342c940d100d0b6128035a00595003d10f405540115841507201400f40141d40c3c1c11615006000c26a4600460030048040c5002540403200414604443d411002c400c1946242c0000203041401f000b120907420038080040c000182c0e0002561118488151000358075118040480c49003800750394005280c000640c2c0f024410444658007241c1320794840c1d2284040c00c0e48401c14034010700050030340c040d00303590150014460403d200080800c208200b103030142c0345081c1400070503410042900e0034003940e91540501d103101d0703400c10800b0341d05c800d0507031f03000390b4075480c40d00001c1103800d042c4250315800c9000a03488000d907902646040b001180641207503035284144c070300502c13580c0c00800705542e05801c218000c10680342103c12a8000c10495443d034465200c100010b4006007202c18106041c032180010008101c41180215010b00c8010700c00383c503900b0300380e0070150304011740204003901c100108802c00940d1382c0c81290b41d42c15250052 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 206027751 1250 206026501 206026511
    0x15140c0f060609010b1e0904060b030a060b03070f050d021b030903010606030c02430906060305010605090f1206010b0a080f040203031902121b100515150409021803061e0406 76
    0x172006c101031041c09000340c0c2041c10007001040c07a2141000450003040159410800c4580d514150f07540c5000564950001595101000c0859440b1788054120084039078801840c3c0020b0250f081c3c10041c07034482541e01c07500040741c001401d1600303200d41302c000c00e0f15080074016004012802510b6078590503100c0303401c481e650516006111400c40d03290071450840e202000b00000b86a511061070714a201d14030690741803800110340580f21380646412110a6140c45040422080c1005012a690503030b26070484c6465210600090040062034020118012119680c81e42c001005220100041120864041c01414080180c40010031030b0011110301c0315240c844000490128100050015009920b000100d5035411200d002c0511440c0c80070940b04a6201006001c6031a083d01d40440c0e504240746041c609141050502045215800900800c110700e440d880342000c10407a0050500b2024451074506000e505003420804030303811404071b14a0301d02c1c1c072013941c1070340001c03240080000748060f40b62 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 206029001 1250 206027751 206027797
    0x606080d020f07121401060b03041205040e071b0f08030a061205060f09150106030618051b09010302040302041505040606080c03070e0d050d03050906071815140c0f060609010b 77
    0x250110036410b04c0d40c1c41c007d005141d5911084481c0750000c1c0c4041c2e40100c42d07040501e142502880c2160700700c4120052003851a520404c0c1560201a0529440207403c080c05210703000502e5030802280c014840c080711500ca04103d40007a08841c2203030004440c00300200c01000c00b107480081c0e0564480030b82e80140c0c40d15602e0410301410107009074200c1650742110710021039a2034258000c070040d00c0c0000c00901986451a209909032501541c80c541c5030043d0203041c01c44400c2d800000d004100042c14090b280030303540e80c0401e00721841112002165001003c0c103200720700e0f080c0210f000500451030103410a0070920750221880c44054240070078080b050901410a8464005c01c2e03414a80000c1602d0b014440e604001c2c024003821a44c01501d80200300000e070320780c3e010341641c0501504001954506030300740310603181d0700129800180c09000381c600520000303d038120000c24034090407a01812001100200ca10314024024103498811203502005000341502d080c01d4808010a242030001113040c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 206030251 1250 206029001 206029013
    0xa0206090612012405121303030636111204030309020607060203102301030209040b090405030a0e09040b0a23090706080105040605061e0405040204030606080d020f0712 74
    0x600c000c00b12070207061000009008000071301030031840c2a00c654225100c0302c035400490302407142d003040f42e42c400300e03c0c004a800d0700d0301103904481070381c841c3c10b0000c0e40c15103440945020a40c00201e010542d041c0800d0006180404111100d5100d00f4420038000202100f0043c110750044540440c2c40c4141c0e42c0020342414880c1c0c2090300503a0300507001594900d5181010000ba41c811148921000c0c050340b000240c2c0c514400b04000c4051080c8120b4440180c181c004501a5200c5014140c1c003688400441d0200d68a01e41c0707a41c0550701c1a8010340e0f030780c0307035041c00034204018159030340303110b40003030380c10000803424010035541c1c000c0100e003000030419030000c82407481145030039001200001017820442c049900090180556515458800c03081c0c1c0e840c000c01c4140c986502407070f5000300b42404509142681c00b006081240311008000d400c01d51210041422078202d58020750384a5100c0e00e0401c0340b00c800744001080d45295101411100d42e0122a15550700300d1031054080700810307101c1040034450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 206031501 1250 206030251 206030257
    0x72411010f0606030921020c270901020a020d05040b160303091407051806030318010c170a030b06090a0510170a06030c0e010e010620010504030914030109050a02060906 74
    0x28000d90700304a140e45400b001002800701800841d01d030003140300f000c1e180250785002c107012070310307035078024101c031030100d81440f2440c11407003035503207803005030045803c81101c222008522a415420005803161807211000385060300d003500e10402c1c041e0400092000810800c201d178101c42d01d1481c0c0e02416455450210000c2070001e001034030903d80f01c1115881048045208411100103e646011250040c150791131245004d44a06038950700402c809944100440700f00040c0400c141003420347c14640f51655581003c4400d42d50220b4040000c00700003158040c8150b1507421001c0e00d4031810a105e002c013140f0078200a015240c031034000210039000461280e1400d2020065681c0c200d8003c1c113280c00c1103030180c04103000440e001080d0100210b0814055414941200c0c0c400810036075130703440c00c00c05a0721268000c4100b06900352841c03080010880900409014034401d030784520034503150076582c95014026800481c441c0c1d0410131030ba404918002000d904103501220740d5a580d9100b0800501184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 206032751 1250 206031501 206031521
    0x210a12111c060305062d07020c0a060c051006080d080603011806020d05060117040321091a06120312060409060c08010810050112350c07241101 63
    0xa007580600502401c05500140222440750044404540700d6580700007a80c00c6200e5070741c0f4200a0075420384401140568460303040400342c010b6031040e1203a44042020101107402c0311000c10300c2c0c1c00400c001c001d01000b0700d11240b4410344003000301d0350410401c60b440700400b00d000e8041040000204915940a6200e0000350081008000c9203e140386400406501b00024481d011840c01780005c0941d4040c0b010549600c1008812804603074680c1d40598492001c5210125010300300121400042d42511a8101c1c144c05007884c02018005121124801040200f040e4014a03110340c0c040c041c2080001500c11040000080e401a60b6031080800e00601100d1000b420300d6080c402c6100b04190031800d0141a02d4070441070340c038800f8811421a040e50801e20480c401e0409410200001c00c0502c60001200e0744014001401042c8250b15503800b050600840c0740c4008001a14110000d000c100182c010104501c108031800c55280d00500e0b4a40c2c0400302100b03100040380124079070341c2d0a5110000d50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 206034001 1250 206032751 206032777
    0xe0f16051912020a091707030b1b09031b120c010801150201020c0a060c09060e0a0b0c030702040903200105160302030603190302030403020414060d1202030904050108210a1211 77
    0x44d00260000802480140c400c0701c1c1105000c410380c1132080d002044580a130381e000480d04d039094a525104107400703410b03c4142030580c00306100100300750382d06105070088100515440005040c0d0703038003000b102c08442040c9280c0c0341d021550514050340c00c81d42003411a8281e11807906030501c0b0311826400fa00c505801c2103441d000b00300802042182c2a809507800498503940d284102d62580e5068496542030042190300000a0f01c0c00c11134156084020524940c0302e00032360b0300341b09150703000c00c00365002504c044001c00c00c1103407210704000015040e440100704080092100e410300d1514201124482c5080200301600080004c0d12030300c00300615401158000b000500000160800941f65045400b04a01c100d080c03488000000341c808081900400008003000d01501481c1d540802c0403800d1800c0b042980410300034854103030707580d1044500070280c0b0b00240c03808816070011180d250445003e07600c46584144907020905601c6622030240ca000e00c0b0b80040c02c4002c0d801c18086500440401e5400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 206035251 1250 206034001 206034007
    0x5100f0e030c1210050c0f181302070f03030506191a070c06080a11040e060d0606120b0f06041803081e1f050f0d17130e0f1605191202 59
    0x2510000a0a43e040d40684c0d804004548502030100e01c0f912445422039a5420148a101c08003100b6042e84c01d40d010005100502130702102212900340c0e08580d800740c0d60688040d64180c01d00d601805404c2d0701c90b50403107014a100c92811041140d045490080e940c01460588410070b92080200441d0704058011440c141016030b6140000c14190046840fa203180d414024550b005081541c15101500c00f80650301d040c42d51100c06101d100c440004082d50015159a0006003a15000c00f52016460140720344650516001030300540240001c1e0405004c1c1e032500e04044940f24074600ea803071300c4aa252410800703d4803000d1200310f150f02c0e070003040700c1d49803106000c1c0101108055072180c10200e1000b40c203a5000d0f50b403c104211000461009900507207201c40c40f6000644c038108410704c140c411001e80307080086a4660502446298001d280c3d410106018001040c102c58a13aa43c45042540e90680f0160030f200028040d00604c2d26100a0308484001d126015000d044d103000107031211501107403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 206036501 1250 206035251 206035279
    0x290d1103010303090509060d08031306020f07032616021c0e030f06280207060203070206061311070201110316030906180b070f050f0102030f1005100f0e030c 69
    0x1025034000e20003240451040c040c00034103810946c054911410f40204003654400300c0d51180e0340c0e1648010500c43e2080b403102c4100000a0080c8054020220200f407469103500c154540901040040d6030b82c03900408a03124142e85580100704080d6008502e000755502da2602003409a1034202c40b5000421000826141c4442d20b991000350311255100850840d02c54003100440700da101c03c1d00381c42d10845d90725680320301d581850f00242c498100c07606094005281c6190703910f6200807608140d030b20400503003042090044528105198050001d4580d804001041c0d203003218642c180302d440002818091043c22070503e0f010284151240100d0002e10740e03070301a134503141c028507600d05030117800c0204510020040441000401d40b800703490070501494604003c3e512a100b4948a0100894991081c9400390300007030000e00240d4041d641e08902010b01d800c00003440d08010315981c002c03502038075050f00c0030014268010780f20120400141000d0350315078015000719081290042e81d49030070407480d4520328 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 206037751 1250 206036501 206036531
    0x50d0509010207110607050606090c0c100e0105011e062a0f0510140f040c1e031a0f070305250806120d0c0303021809040503090f01020601290d 63
    0x21001c0c0348034040d0032803130015407000c2120b20300403280c1c054406e40c481c00014007241401201142c20041c3c40c06038078240b00c4400001454450031080140c407160704ca80c4000c804210902405026000300040090043c26050004074040704512691080040031844060341c42e901c0242c1e020b00c10b82c2107012180b021424144000500c090007411142c2d40b0640001010001051042811000340030354000216100c1c00c40f02d0041c60405882074580c80345962001a07105c1c640b80480403940c080d0041080034501e0750404444404040c00604e80d0041e40c0000c0241045511100c84e9000c2c100d03040028003a192042100d2051028007058507442c400f8030324208001e40c00101013072203140d0840300c0c4180600c0d459889078032911a0200103011900c01c000c0e000010b8007940180c9507941200c2401e0100740800740009000117002d841c00c0c0c1c0c03d90400103402c1c856085c40701c108000382000380000c0445503d8100040e241301110b0000440c460410b1429010941030321080781d5285040200034091250144441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 206039001 1250 206037751 206037757
    0x120c05130b0309070b04080a06110904020c06010e09010204030c211e020a080703021507081e030702100506030705060a2705031b010c06020304030e15031006050c070b0901050d05090102 81
    0x4203442d20403250300045d000c030008202c40035102610003610100d010741d5100c1c400390440703800004540c0f50078858201d198a491000e0110038050f0b10040065500d04140000301c1203000c0d000d220039034010001440803480c0e00305c0c030000706c0d4140150080b070025848000c1041c500c4080c4000d290382c2481d0b140349885109040302c4110a0f000300c404a40304ca03922175210b5540d880c036120094026241c400e641a54008030b0707000d03240003030049a5591400c0344542d051320006602c03c484011702c60022090214150341001034800300d00d901c002c100120700381000001d990f5415840ba842c492500060b2210541303110340c0e5411039160388054030382840d005402e40030344000c607170b4061103000307100f185400300160f00c0c0c4050100000c2c8041c2c5800072400a10349804003e94030080c415010300100e001207150319151400001000007120b0b4400d5103d0410f148213006904180d0f010b0003c0000c280704007407a8035000f040306000c4602e004c1400780e07580d22801c0140c0e0309024042d4804101450401040351060040d001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 206040251 1250 206039001 206039011
    0x6210c0a0803182806031e02131404060807080703030320070314040503190605060d0c0b071707030203090102120a0c020910171c0906120c05130b03 65
    0x2805101911003400366500d000e038141464012540860f04060b40c00d2001482001ca4601c0007000b001d6090384166204a207082e500c0b03100000d9441d096103901d110900c4000c2d000043c1100c2c20761070700c4c010f81e0815803182c807280580020880348030740707505c0c284d5a5640300200814902c1c0a840d0195900c1c0340e92a11141e040c481900800d0800c002058248080100c50b009244012a000d0404905032402c4510000c51541181d07103610420020920750f804200d141c1036003400101c8012440c0f0145004000d80c0d1010340898000c0300d116140800242c07074980c1080a4030344c0b21500c3e544400d01c44c14440c2c149078401150f40c404203400140101032641c080b008041000d001e808554188442080742c064602c24020000d00080400709480011300c0c2652034560001c08020341400510f8481503208500171480034000ea01d903110200b498000c0c02d81c0080e4410210243c18092030b40c5d49000070181c00f00246610004505540d8000c4e000c4103409081a102c02810581251100c940c0b04d40d4040283d9106442d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 206041501 1250 206040251 206040259
    0x606010e0f0d24020a1407020103060f08010507110c0121020d0c170702150601030b010c060203070c0204060e2701060b070b040b09010e0c040b030a080d05040308240906210c 76
    0x10040407000380c18021540724170460390342d07000c00c1030304c051555205403c1031034200d04041d120030001402c20080c3c2c096001030000c00c40001420700746818060030f1a80394248000c000d17003190010140586c0c100c0c6003000e80d01c0000705100305a445403880d0600a114510030024000e151180c0700c010560f00900400c4002e080d1182841c56440b900001c1ea925030000c485001b100b0285800105154401d4001d6501c021041c141148845101c0d07544900740d8004868020000d620911a1000c1d840c15001c0c1c10014000c86c41d800c50346080010400713003080f80301907080001d050102c0280340104402d5100e5001408521031a9444000900d40706d0032406050f5000ea84c83e40d00c0c07101040e081c00040c4601d0000300c949000400500e0400c5080c030010b080c02c000100d070306010340038410000c11001802481c0492102d40c0000341881c10345800b508801d07000c0c010300604118080c451507114200c007413007102180200c03120b8003e40c0d91000000c15402e500764850ba955580340008090071340780007400819040f0112 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 206042751 1250 206041501 206041553
    0x501050702060a06150c1407060e0a0609050a0306020c0a050a0b07030f0b1f030e0703110418080d050a02040b0703030f0c0c0305041701020f130302040f0b030606010e0f0d 75
    0x350083c01616150f000310603c03940070521014035280540c0800301c41034801c07030f8841d400c801c1c0d0204403410a500c1e0b52082d0007241c82c402440050703207443c89148018100707504007603c031207040c00d0124490b400075000081c402580041e600c070415a040014400705a88131007110303900351262800e8035600d03106039800f0700440d0400078107000a074600e01443c4230818000d17042440c246d0b108202180c02c40c01e0345001da03051590f10700307503103142c070100b4019032000d14014540101c1008820b418001141c600c00401103040c60380c2c4440000003202903040b60004084880042855200d045140c0000c1c80f45078442c502509000507242d00b0190540c1040f0115406270380c08203c012912001036441c0717041043d0050000c0d500300414069049604c0d01d500c0c10180c0c0790300060400101e0840d071170066004421003c03142040000030421407500d409211ba00c0e00024000b0300030000300c2c4010a50329070001d0005030510840b00d034100a42d403100d0020301d40311080208541100300c580d00740251603000c11034400c2c04240d110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 206044001 1250 206042751 206042761
    0x905090a0b030307060b0f030a050604021206070816050d09030804140d05071e0f0c0f06050f0702040203041115040311040c050a0804050304030605010e1f0e19090f050105070206 78
    0x24800c1c49084000034025500d0b1000035503400009003048008294845080d043c1a4400c1e00c1c100544c100682c411801850542041d00400a10b2980c00b480341c0780e01d5200000300101541e02020a540080601a40801c91a080c80c1c0580d0180284403d402c1414030f005094014998001c18550040d4007880f105001c0c091030406044e2a01313903010461000c52070402208000459422103400c5100315068480c80c8a25250b4600f200d030381e410481a0f03400700c9140d00600c01d440d4607011650080545043c42840d103543d0403180d0829008801020744255400302c002030900501e040303400c0c52150020030b03814180c80180e4504200e5045400300b91054402990480d82034149449181c604550340d84400b4103103801000f0031210000028801c0701c09000500c00080054a5402080c1c080e0374030000c02c01151501d40105611345a10203041c400d011843d00c0c04010424140f9003c0ba00b00725542c6040c000614401c504d0b9020301400440180141c0403d008002480010b42c0224080e05240d03003954031503212 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 206045251 1250 206044001 206044021
    0x71e03031e021b0307050301020c0312160905130212010f0f0905010b250803040804090e0a0b01030303020a050c070902130f1d0a0b060a030b010e03030f0301140a15090509 75
    0x4007a28050b9201820301e480c02d94102e4401e00201000408451616131140046800d81e0010300350920190701c0490b25004581d180c4914541c080c510520318110800c20800041207a000c030f106480c01860418070f803208000740390b01154a12540c5409058035943e4804684030010030381e1050010007480c0c1580410075405038016141280d9030443c0032810a5800c445d00044030207854490005030b0325031103040c0000341030078010318411030040e10029125031130102200160381c074018484c885500542203030000240c0042e41c040c1566011b24006807034444103c015101c1d031203038101005946c842c4400c00501115190010b03c03851071000350310050550340f1094480c0c41241ca005001d06201080e54900c580550207510a0f40051490303404181380b80440003054050f4405803080300001d40b2030603681c815580014190500784000e0b002507150001c0c000c03800c5034501040c0a080410b6940d901d000c08035607201c0944a01038000e8441002d10040b40c1d850240480c0c03507610809005080ca9030010b940101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 206046501 1250 206045251 206045297
    0x509010204050618030a050703062c060403180b0c03041d100b030403090b04081e06090703140709110a09080109200a180f0e0102030412050705071e0303 67
    0x9405003ea5003030074074402c40d015489000c103034855010b102d000700410114404200c901e004500035840000e043d00403110b00803c104450081f0b0a954100712025501d10000103100c0c1d500c5074042c509001c3c0c1920018000708810819486009490004590304941440200080c000c46d5002d400c0030491403041840200400b01c03c0b2103c0d142041c052504010b0700e5200c20045912a2192030030721a541d848a0304d44107290820307000210b15a000c402740061811402e0104980e009501004050a26117460b400365201201e006c001c140030710f40154070300c601d6001c101400150440e10f4081c405222105010441c0f900700d244000300143c0d080b400082e90070010303c039180d401034012030600746d51059005500140d481955502d50040071383c0c00002040f044110000c50301640340c55020071900559403c84060310a0383c880214985d00c10020301000403aa119009413520f1039007002c0b9110b10543c100780342001d60300d60142d102440b41e2003a0b42d41d00014810000240c03840b0f903c40300744004000e81d02111101c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 206047751 1250 206046501 206046509
    0x1501020303041b0801050109020c0f1f15050409300801090b0d150b1e130b130204080a0312020c06060f120703060203010e13030e04021c050f0601030509010204 70
    0x60401c00105001c40e18800031560704551100116040703950303401a140c2154000d9119001c081d42c017051010002c034080c085440945c050b84d00400c100c0300c404090110450100804a5a180d07070703a55506006a04140c2103c0100340060080107038107554200030141c0700240052034262110161100c0070814030140d03c5800081680c3c80c0042c5a00304202d000040080c0b90704030740d000320350510080000304140f080c195942d880030400f142b080e480d1002e0004503c41121001098840200500500d840305594144241580b03000880d011080d04040307800001444486003540307000140215541600040d038000d203030721035030b5060000b800000c4094124059081e80c2d50680d0403e01c040750309450312100d03060000350010311101d10048051401490f203003066104455490700032004214282220b240d0a6000340ca100342d03000b410352203940091507811000d803034a101c1e9a01041441d17101c201103c903445014a0907030304001030b040801a40002c0282290b000d40046e041c800041d00400040c020764040f6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 206049001 1250 206047751 206047753
    0x9120a150903030b10090609120503070b1e0c07020a0501110a0f050f03042d1d100504020309061609080d12240906050102010b01090303050306031509010b09150102 72
    0x10390402000401912425000342d08164540002c81141c0d5120141501031840c0d540391940c500303241010241c030798001640007100216802007100085000402200c0002d0b0780081101d42c0c5903540e00b4895103800e040a81010f00d48840810000c21840c590018a18a8000c840004199a46e00300440701c91020009a403459085100b40400142c0200340010b0107a01c200141c540044a1003034043c5141c116500a0710226554400010140400f80228810503055050300c0e20799802c0c0b600400c00002401c0c404030080204100056a0625150289000d014010010355403170600d4804140e449034240c460400c903029a030441180c1501031110082240c1405001e000854550303102a91910013078545500e64541321288807580c0d0340c0c90f60318000400c0540300c09045180c1824044002c035030b025000f0a066a02d00300c4011003a0780c00007096002c0726403510300300e90f80b95035110100c1c1c00c02c0c8052800d003d21910340d0041c040c004506401c51442c201c0c05546049032662217480448903090304071011405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 206050251 1250 206049001 206049023
    0x20c0d080f1c020a020706030b0f010c0305131206050403170105090a0906090501050f01080607030204060e10020307170d0f05010f06050a1704030f08090309030601140f0a0b09120a 79
    0x140e0070010301034041c0281e03140c11011200140140c00b0300343d07485011103a0040e0403a41c424858190144101001d100e01602c951421040000010700303506415617010341408000b08010103000300c8860040c010301041c07034907101e074aa12131038200060401a41e00f1000302c6c40304c0718840d100d40d40d0414460b040301c0008040c40d080e91641c00080d001041c08101c25181e06880302e900f10f002c20024000c190041200c071b502c5040940c50256498140710019114908250040004100042c3c0c800120f41c1c40684c03c4603010244003c0110980c0382d8071030700760000d05094488040d01868240d1002070301028092000501c5800104071034501110f200340554002d54150040031300c43ea600c00d5010381020340441c1001c00011030458a808403540d02120110001105010341000c0d01d0741c050390702a0811540c02c011410300c103180d400662a54014020790548a840ca607680210703070b441c3c40e6004920700020b4001e2070055101c2c40d582c1c0b141d0f401b031941c00c0d0007622100d5001a4a81b400600c030350455030420a8882 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 206051501 1250 206050251 206050267
    0x1090b13051c0c06050c0a020f0a08010903030b03190c1404140f0114010804230115080322120b0606130b030703050a0e070e0c040e090706020c0d08 65
    0x1a250030040042a200c86806404030700c50b121015101c4001c0301100300c06066801a01c0c0540c0d6802d003980000e410803200b03000381c8241050004072510526411280c03015001c69000201d00440c640703501200c038540c20074240b841859099131202c40c0b003610560544d442c13000b4405000b548686080801032202c1c405610421a220300140040100c0c01c004202003130b8900081d84620742054180c0e161100d508005004001c800c09548541000e10710038245444245803a4550101c00203219071298924900501008801002035100203104000c8000c1c00d400d848d1211510b65980c0c2001038207020001e00000315080c03110403814103400300c48001c8074a031040b102d10ba407450f43c103401c0030b04001c0e00050180b110022848030244045c019107199a5030544a15003114001c056440141c481410035141604a0b00001804901c440c141d40300c031a07030741615460340b424450461043da84801080310100d02440f02108000c03560008540e0310b40e00322079655200c8020814a070f410088000c0506408206a071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 206052751 1250 206051501 206051519
    0x3060601090e0a022208151620060702280519030201060504050a090201081006081605090306011214030315040c120906060911071a060307030807051014060109 70
    0x150f40030b8800c070300c00350070191031400b06607050580e400000d42c80c0812400a03c840c640030496107100b548200518001410002490744840d81015000000c2007030100900041b10b540c076158440024884088801614044070021b45480a04c6195900313440185c200215800c00c40c1400b0070100d40000c040c01d1481445030f035220303110303118280c02c800755500e80034002801d45c1c5500c101c501c43c06d425600404c13000c0d0240300050002038010444150310900b058144034a95111504036409000c095044040030b200b030300e098030306025900310664580305034400420180d803400703113a00c0201d10071704030500c05025075180103450340070488000c003105401074800100e40c50150448658884e05007070003080d82c4581d02d4075100707552601600390351642c1c69400400840c002480740800c40070f008848503091000075a204156159040d1120100100e080003145850750140600703002113500c103a032075a96141c14506161110000303134021080c01e207410481d0050803a00c11203140b040a05079102b10308c0c00e00b000380304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 206054001 1250 206052751 206052779
    0x606030e0d0c030c2012010905060a051b0f0a02010c05070302150a0f140402030705100507110303040b0301090b090709030209060d1e08120a090c0e0603010b060d0c0e0306060109 78
    0x643c108240c40d030010003c68400c9420124602c41d00403101d9242803100180324102e0f035442481ca0460b850f102d40300e40421070119180c0e41208070103201085503207443d0502d45402c12a582d4078040359500062180085400c80020201c40d29a90000c0c080040c078944113907142c0c002d41c0350140242c0c20131140b40509154110189510400580001403206e801c00004c80841e2003d00b04428440910000d21056142c200a900000c0508a420042c100d1401e03900a00c0c0d8011700780002e08400d040101c1142c50381d41882924090121765040036141d680d074010b030a010384140769526001d0b1a44101142c1c031588602020401e9070f40140020000d40c90b000b0a1058100f5030361810f80307141d459000d075000902e072500b0103200720300e0080c0c00103074440b42240209036000c880036044400700d614001d42d00c40012540c40010b000c680000c00560320720ba45000120703014005110382ea030303030003000010008842410f9a001c8040c0b4645540d800c480c5103044814141d4600090f074195020410341181006051229680 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 206055251 1250 206054001 206054003
    0x10b010e090a090203280201020c060c0709050a060803031e0c03040b010308070c0510110616020c060d020c1204090c0f080a0207030c17040314010c14070305210108010606030e0d0c 79
    0x4aa1b02c0208001e41500450101101c003400c00c1181070b1140c09541e0b042202d00c10689040b030b40e552074001c1130700c0f43e655a85541c0c0b003014030b2680c540740014403080e01c5a0000d0300800ca11000d5940c0c0c1e240507000010840e1151148440031421322003c41c4d03403031840d001034034800d540c45140441c6c103909580381c15800e9000b6009c03c4070000c1c0402c401203440d4403900c01411401c081da4480070039003600c5104090a15400808840c5c130070302ca01c61071440480d400194201811020394515550b40d25a41540c0041c0c800c410740e0508910401800c0809200104000e10880d0f903c001c00704a10040340c6021185520546804000250200080703071180c4490760041003000d10a040030380c842211a5030720010500d02200030882c00001250030014091140043e4520001c080001c2044800c1000042c210a00882c14030041941c040b546004060180045a507260398071075207500102e4118040d05504a000d00a004483d42405000140f9501a0140d03007122403410002d070154020b144801c80760440040e00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 206056501 1250 206055251 206055253
    0x307020d060902030f0c12010b1c1704080d0e03012d02070215070203074502030405011a01050f0f07032703060c050319150504110705010b010e090a090203 68
    0x28006a80400000d1441d617840d03005000011141e00401000d000c080d00014500d174100300e80c40d20390740d86420107104035150500300d4a81c040701c942001c3c08642e0b1506200c8121010002d00801c103104001454514a200381d945c0c101181c00110905080e0745200d80c107c0c2c0b0030303a960201c0342d00b00081ca0015082d844080c0c00018100502a000540211004203c0e07040540d8002416402e60038180410400307003240c520000480640f001c200115070b1002c03a940403125030260380584007100075504406c103040c0490429522410300d410814000c0080d0460790280c1c40e1040c04505031540500306903041041d00030120f03403c1403c1c01f003501d545070f070150f5001c808016021403140c44001e03003100c444150144002e01c00d04803a0952030418122140014084140f020900401141440604040c6440010210b01103a15074403004440100c0d9065008150f00500784800d0b45020359084000d0074190380507500074006804c1e1f540043d42e14a140561550304680300b100064088901c1d9040740050601c094 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 206057751 1250 206056501 206056511
    0xb18090712021210081204150e0405012d0f030213020f0403030503040b01050a030b151224010e010501020307030f05070206040f030b1609060315030c030606050109080a050307020d06 80
    0x501c41281d00c000035000b42e4811003824032150800d41210325018103280d90041103604a0100b10b816617000380d1140111494a0015400c0040e10400c0000750010014100780000e5840f80e182110000048584581160042080098420400c5000c030111403e02c03110300e0780141103400b4403111116036500951040c1c1c0070001ca00da102d580c0300007400210302954070152a03080510b000c00542c0e01c10381c09644a58901c0e2401d001064030314132240d420514a6100464003034405002c50700203c03400b03d221442d03020301800810100c43c40c50359658074154045002e05141e8070b849001003803410030b004241c0141e105010200c0040e003e500f410045007003505119007482c210380c0c0058400e5005402c50500304000304d404008002c101001e41e9000f001004041e44400f032812401410f0192034400c243c10580c54014003040c1e892400c40300c0001e1a0071410400c0b620340c0303904001014001c0c0344a00e5001401e81c42c8001a0040082008040998008051490300d1065000c100c8542e40000341912a15952 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 206059001 1250 206057751 206057777
    0x81e01140303211603050c0d18020d080c01140118020a110303130303060503010b18060f040219080903040f0303030c030e01180203060106050c0c060703030e060711070b180907 77
    0x903c40c00540c1031000c890b8a41c5600e8281e002c509a83c060301450700074503050009000c1513080030f000340e54280401da0030001d00d00b0301200481104528030403010350420500702040301840380c0e141c01000e008c0d4040c0002c0c003074403071680e003260794204091049400400048109034660000c0d900105544030262a001180c01c0c040c20b80503055034000d441d4004964840d4105504054150145500401c4110003c00a00c200813021410081d256110b030701e80b0007082d000107401651004446040190050011921000300d044e14507041c2e0050b080300400b0410110015415040000841d030503965100a82120145142e034250003070403020009100f8551102d0443d07221120900c281140403042500e01214506240145407c0540c1a000030741000010800304000c600002110041c032070050390b600365240201d0070b0440c0189a202c20815040c0a00c2040c450110b0340008a80d0b040e1a248080d0340440c0d56174500301d08148100701508000c508141441e4043d80f810300d0259a0000b0503045c100d4000480b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 206060251 1250 206059001 206059027
    0xa0b0702010b12060609070f020a1202010e0709020717030105130b04060302060d09030f0311041205030f040b040e0f0609060f030a02090a060f08070501020705100c020303120106081e01140303 84
    0x1d110a0061644c005400c1008526060705a15000003003030400e140c0011034024000e480b0003c003840a0001c002c0c1e204101100340c400d610508103038803100182c40c0002d8441d54a139000e03601c4894140c403a80c2003072441041d09403125044074100c90300207054100b403928074a50b41000d8241034203441c1d803150350380707a0000160300c5507002040c00c0c03031803c000000d0a8400c0c1c43c01800c0641600b05c0c1d4000c143c078064003180441c8110003183c0940e18481ca600d900000300c2e181262541c403c5170807501c0c00103004100081c000130b4410140003a1501d2001c0303100141e8400031072a607041001c5458903030008a010109415003401031496040000150623648510441c2c2c01140092006440c0224180d40d61a020080407010483c184041e001c113501515000e803415000030341d50107080c056140f0403617292290300301d07440c001c400c0b52407016800740540c1d0f2140040c03041034104034001d11400022603441e0700003d803604c605500c24085c010003000c20f00403d0b4201505172010f02c04c1032190642510003040289a0110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 206061501 1250 206060251 206060269
    0x11112071b02040c080f0a15060c0503040510031b0f0503010506090612160f08132a0902040e15090429090105040c050108010b09010c08191716020a0b0702010b 70
    0x1c2a6105d0711180d0070152150f01440100a04095480d45401d85030507141451081500c01c842440c07509213030012590500c58203500c80c0341d00c40765204001104811a0980503042440260060707010f0001c00001e0f150161104103500703036424001075040005004510341200075010404e0042c1c281810114001c1184c200b040d0183c8600c3c0880d580e510101d400140e001032101d4140e000d600c1c107444c49082c80900840c142c0c0b00c4140040c05080711034502c41c3e0b8144a100120f23010400b81428030759069403000f0803402540103002d20034412606000203008020400c1944c082444c02408081c0340f0754841d2650b01020105000001d031070066501c0a03041840c081d6801030260500600000d0320781801d190400e20301c10564845414410725000420824030b00c0000e035060001d003030074140c581540520780051039206441c1c155503007103003098940e0380c115131150702035680031400d51848000c1c1c0c40380c180080c3c0040c41c00601c440182d11214150000404800c82650400803600000c18042050000180008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 206062751 1250 206061501 206061521
    0x906271501080c060c0a0f020411030708070306051f030504020f12030903070e090a0f1a0a0c03110f04060507020d0206030f0f0a1a010c03020717010b03011112071b0204 74
    0x54140041c4480382c01800070f024807078021100c0500d03003000c2013051902c486940001814405503660100150748076500044e0360300c800400c0c010758a2601210180040f1340030307140c04001901c0d08002144608002d803560040c8a0080f464100203101d520007140501740041c022604140c80f450007565680b00c1100e203035148800800959250a126400c0c5498146035911100c01d21800c4000d000b00003901040221a054200c0c000d07000c080c031642800c83c024150000c01500b020081c100708040415540e002c0841b03000d15540c20310096031b01301840d9020740100e03c403042125000304401c0091600800c0100405480505224100484d0780c0010340715410031100d0548030203880e02040300a01c0c540b1a215480948070f1406c01c1140240e041c01100c5001e081da40078103229202c89100c0074035000f0046000200035914150400c00c114802490203081e035003c3c00b5002e03608100c0c600c0071848041055440500000b2040521990384020807a048500092815954408440440f0158549002e410888 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 206064001 1250 206062751 206062783
    0x608060901020c1b0f060a03060305150f0f01060203041710020c161a030c0304060b040606020c0a0501090b0306041d0d020303150423060310051504060b03090627 71
    0x41c1481c00c640505116800040d1303c40c41d0210000000c03150785e00c180420039044207660b001d0b22050426810f5005003015000130b0310030720a803804000001100d6203610720500c1700c0404441503490b000c02d80041c00a080c082e100140e00b00307104c01d100d5041500003455614902c107040781c805210b80c4030701600b284d0210082000c2600581c20740f8032241c0418810074020214403001c401c81c01d083c0c2d82c8004c0c0d00d0101410903c00ea440010209041c0010394000191541006000300005070b074034000030390781d809100340d640c0c000d032401440000c1541c060003e4904865110100368615916a01088020301441001a038080d01d00300712194800e0302008000c044402070340041d6964140100c0c0c600d0b0700c2280c2c1195030311641c00c080d50400321880812111056492011a9035082d8a99100003803c1c04140c2080342c0b0f00701d2a100810005a0100d002200010010f481c10804623443d28012030031840200c46804560381705d84041103140003142c00300c8100080c514880002603007034455860a1a06a00c03010443c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 206065251 1250 206064001 206064007
    0x18060309060f13030c110402071b080f031305090601050c0a033c0c081c0501030b0f04050712080d0212040309061b240204120311060417030406060806090102 69
    0x14030b1104150160414031034180501c001d88540c0c0c00a0020041c003000034105aa0020034800301e4aa50b015075110b107920456400304071070304407c4410a410070344121501d034451200440f4a9172004011901070302d00e004506003030242171209011080f00c024100c141004001c100707904240201b07000091440780720350b554a41500c2c050801403003040501c40c500e03c1c40303420300400c2120007072030030842e0080000d00e0400381c846450500300701c4120300a141c00c1c941302100f00700070102404a0b6a00040c181c0780b080003500f805444501d50040c002c6804c440c010680d0b0702c04070041c00700483c02c0ba00c0c40c0741d42d07100e4030017a0b160510303050103c000d07a007009101800c0e0112080c280001c06400240c3c55025080710314012081c43c440c01000c40103248407500103410582070f42c58010190070748110503541458200c6055684590b100701d1b0010303c07101c01c2015400a480b50320402400000418a1402140c100d03280031030020702803184e403c4560015001b156a80d0340d46030006400c801c24172103548900910400161 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 206066501 1250 206065251 206065261
    0xd0206120f0103170f041413020d0618090f150b1822121b06050108151b04090231150203090603071b05070b09041404030c081806030906 60
    0xe00100d40283c5454200814407000c117084403550245c0d0100d0300c080c0380751200ca122100216051103030459803403c14174000201075000b000ba98025004403030280036980c22a041001a941c101c5040e00801402520102d202c803011410f810304030748001d4014000010840b44100000d500b05d500505031261110f02c9004000d209006040310720121040011008505809036440c0400310056518000901c06004068825041c054403031407210b0f60f101c0010082541c681101d41e649004041f040142c444400001541c50546084901c0c1c2c51803807005030500f003c3c141900c00010b50003042d4036100d541e007203e681c5441448902601807110101e80584003000f800c1038949410003440030705860a40d80b04100381b90103619004100e0340c0c00341551400040f501100d52003000e0030385442c00050000d109400011800210340f400a110f030100c1101d0400c601103103080401c0c0c203610201c0c1d0250200d44040365240215920000400201400d80790841c1c80394031040000722140c10940b000034099000500b040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 206067751 1250 206066501 206066513
    0x21504050607110606030a030f02030705010f06080c01110c0f01030207060203041103100c211b03020310232202070f0507080a020a1502031902030a1416020d0206120f0103 75
    0x43d0204841d50041d140c540b030481302007983c0301d40c500300003420013800a01c0003115510900940301071a901134002d001c19081140f0040103818030b030181500c0d1340580420625151f0003825001d4010781c0e864094045010780c0010414203209807081141896002c000c1d00e000520b030781c801075118500c10003460b044600c20303000307062400b01080f06030078001e45024069442d0503002b0703441000d44803020400c800c18600007404800500b103002c44034602c028a0b811101c051580607000356229440300d0145070705080e924130b81c00d55444e184c128810070802907a10700c050705040c0b043d96124030b1313085103503620403040d11004190b0490340b00c0c803002d5820619032601042040b8050008800030000d503c01401c14496540001c1c8902002d803003051008454218a00f0b5039a000b401901d1074404950302480d940b4495000194a943c0043c9221001820f040c4560701e00e6141c0c0015200360724007403442c90703800a642e6400c0c000051450303001a0f0f0301550610084141e8074040305294811201d0039041480e9514510380b00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 206069001 1250 206067751 206067767
    0x60d0611071506080c04051f06020d0f0f0905090a0912030c0305010801150b07030903020301110a030c021203070c05030904050a09050f1b0d1a040b1005040e070303080601021504050607 81
    0x40441c2810301c2d400300b115013000120380700d50344000c507000511621491011840001d000ba881c207280c050035400011708070f80228500350800f40507110f001010000900889060030340402e90740200324802c000f440a410b00d4010030758024801007000400d030a8075119000030700703402c03100c0c9000203490706030004003654035020715170041403828000e02128443c140d4103003080b44c3d580030b105190400803c80d1402d05101d46181e070000c50300900200000c0030b4208203d1510391004d40d004000c2400e01000c0d84510380700103024050303604030343da03031a0440c8c903142e0b011030394100e0b46503042d580c1f8842402800c503165110310a082c06480c0e1481c00145400301480d00c0d6042088019403050940c019840000c00c401c600c000c03440d400d400c11542d94080c48101d282c603644030000d9070080e035441280d1608220403c109412514005e603050f82c8002801942c2e54104001d90b002040125040c1d0810041080000d0041913441e402c00c10500545419913004130803110042802c40c2c083e1803590064003032010841d046081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 206070251 1250 206069001 206069033
    0x110a11040e01110313020a0f08010902100503040222060305010e01050a060815060d020d06090f0309050d0c0e0c1b0c0a0608070804142d0d0f1403060d061107 69
    0x3c2c03141e5004401c0c00640b43c003000f8040d800030f03c0c1100da2070046660300c460401c0940301014510505944900100b4000c125a400890144510441d500da0003400360003074034400e9038001c041c0034996005000403002d1706021080c0e80c007425140c0e2004000610b0a00508840751b41c0c05000003024075040c21900300346c0e059944500c11030b812a0b0713001c103021002c5e4250145c1c84030094425241003000352021810004c8e032044090b10492501c5184410800705001070304685010b40d403055a91610b0724100f01d504504600300030030104440000704003a01c80d440080d0743c40a14042a241001c108030b00300b070240d8140d003c41380b05075041410050703c2854a101c045019050a03d00102c0701c3c945910301502c00e001c007610182134040d07100800c104902c0100985280800151601d013400c96020220a02108100c0b1480a8a02403c407025001e82c0c4191004200c424041e501c0c0840c03040c2c20321129449078401f40c44582c00010382e00546010035514010340d610f031064510720750303036130340d094144074400000d001c1c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 206071501 1250 206070251 206070253
    0x9070506040e0a020f07060207110109050f03150604270b010902040b030a0209121f060b070206070803090106030f0308090606010206040309140121020702010908060421110a11040e 79
    0x7081c8880c91010300d60701d601c00085079006a40d1003a10b121030a280c050340e00020000350000458104215242c0e5000b88009420b8860428854450080140003800350780080d4140d401012800172082082540582003200039000080801b155508c202499007644d06241e404110400701400300421003a550f401440c86401c21070403d41091404411032001826994402d500801c000000355940002e907201c448100d801c44040d40201c902c002802e02410400c41c242920740300001520001d6501200d25071907005000e80e00d056416501c03801980c001400350350656580c2d03a40840003500b6403d5481c2464040e4540c0e8021780b914180c07191900c40000d01160454010100303010010b03420581d14000d9034080303c482034030a80c071f000c01201e6070f050031540c826900314040703146045071480e94003c1101a000f82e88002c1c07030b182c03508085542c2d01001c0c1c500900c40314a071038041100d82c008050a104991035880e1540e2100c4000700b0755460808130050a64220340091000300c110714240c4610111041444 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 206072751 1250 206071501 206071507
    0x1060e090607090513020c16050117060f0405090f10050604180506040803280902010314040816062c01061e170a0507081506010302030f370509070506 66
    0x412210701442600d001c0d5143c0c0507017450160a9805440308900c8040444000280c9401c90603420552481210f01040c261948455209100c00800d445400b0180400c48280703061810b010040c440100b60300c01328040e2428100d4910b50074001941c01500741440800c2e1810030000308005c0725121130030303c5c50340081c2c150150700242c004a01316601c40d400c0b51015460b542c031503040d04401c40f1010034414010440d03000440003600c6d00da00191606000303a03420007400c0d051410a420010b410749010385568011320805102c82a841000b820713a51180c42c010810016800c5803e0840c4c4401c4610b00324004000449018030009110f5030000f8000c040c0136100c1c1d5001c80205880202c450b0154282c2404601e902c0c144d0b0031010004003800c01d0f4044201c3d0364156560951540381c1b242c3c03200c210300b00407100010412070345c800d0003905c0c0680e000d02c6c00c18180d41c68200d4007407107141a1402c410300440c00313801801c00324480031140c02c951401c4600e01107160304e004041ca80c240b007100e0708101d00c204418 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 206074001 1250 206072751 206072761
    0x21050405060a0f120b1f05130b12010602070b0304140109060203010e33270f07090801020a050a030515060d0c0206090f0a0f050f060109020c0c0a081c031d01060e0906 73
    0x328a0b8031b003460b1501c04000060351100d0320200c455110b5510700881d4000380c41700008241540400502c04502c501c1c01a0880f80d803a20400c07a103461480c860503230148418000314010030200f280e807220030881540001840e00d0706690b1a8180e070426400811200540010015943c9042001c14034845100f180c0b0041140902c50756081c10480305081c60013148005118a168003000080720350700c078141203041a107450214103211711400202e5800300024034440b0000340e488014020341d82e10a000e51a02405d001c49414120010300c0000c2c04504400888504c0c03050329200c4c0c5c4001e240c842d10240003c0380d452801c00001c1e2512802074a0f1549940c40050078400060012400c0341d245607001407048203036019800e0041c0340814450442c421405948000910b0103000e42c010a809411030042e41c1d103940c03100040100d1500c09125041c46a00489649848a00518110040d01d085424000740ba014506100818981c80310300c0d5900c9695205402c0c402c010298107181d070710031600d000800440c900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 206075251 1250 206074001 206074009
    0xf0302010f090b1b010b0616030909090b0601030c0314070504050a050a03020f0906130c05092704060b0a09060906080120180d0203010507020a020a0b0721050405060a0f120b 76
    0x242c100415241000d00421401d0304101b03420080780644c0041425464140300c160300c6c0411103c50008030042101c2c10b400141c1c490060280c46a800d800070348500165642c41c00550281c500800b040e410141c0c3c40b114140b071001000001c0d07016400c5942c1c0d40343c40e18140024495a61001e0700181d115980c82181000103030b49030390f0b1143c402042919140105c1d15010040307003046418011a403441420070304c019101c5680980540442501181d104542415045c18114400030308201d01220000040c00180070512903088801d103250b01502d01c52070075507256800000c44400340c101c40341150b00d0700d804100c945024041c11841e420083c03a2000d100c02414907400c0e031481001140356080070040208001c50f6110b00031501083c3c2c000c4c00903c41481d1510f0001e41f100103d8030124840c420f00e00c3c0100d00c0040c4817068030314042e48030030344e81c0e40400e080b15080c8000d56a00b1941c000c10408000104407901c4900c0540602c0805407684031150540e41030203808060030710f0340100c2e1549015112102d40e030b5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 206076501 1250 206075251 206075257
    0xc1606020c0a050304090b18192f031503010c020a0b04020103020d0603060b0a06020d0e120c06071202011a090601050d060b1303140a1205220f0302010f090b 69
    0x58005001030759154051803950421000007006086400041380c00182c43c451a00321780b10102e41241c00d0030428101c101020382d0710400780c0e900e02c003c41d41e45c907a440c4600041d91001d070aa91010785072500505258040fa0b18a4100c0300a0841402d4088107008011420000c440503880003100207106030201444025030b6a0b11500c4094820360140d001b003000c0d64003070b50464032806003101c0c0c10304c03034140c03a800e182001d03001088607140510f4103800b0009254cc0b022508151901c015030354110340c180a10204101c00114010340c214030700580900410136039901004000c00d904c0ba40705010305d540e501302c02a08450103002c0392900b5588203c00c503446a500c05900039448030702400c00759241c0034006a088014004c58021030082000041d03200c0700d25412109840c02c43e441002141b031801515030301a0b40350051404010400b0300b07406845640030b0b0190000e44910040000784000c2c000d440086000c8208055100e40f0030048600000e0055591101d040d1102c4078090503c0760610f880e00c60150039503c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 206077751 1250 206076501 206076503
    0x9050709140c0708090402031311010f0813080d141e190c030e01060902041a070c090216050105010915050306090d0e0103020c010203040501150806090a0b1005120a02090c16 76
    0x1000000d003450800c03401130f0564035240000382c000c40d1640f0380090b00340c203030804156056405140081121030190310456003111102c0352551030140d145c84104846002003200f604c1100c144406000304e0000440f076104c1c0c80903200c420308403040f640c02c052000c034084480a042a00301140e0207420004100301d0311003900401c04250030001410003840740100d0061140900b410900d5082401c006129805a0003070070980d100024a080350141c80e4090114520540d4802400406a00b03010449200c9a0b800f070b000148440d4000d100c000c816507112401c484003608860809684e6844c014680000c208080703000c0c1005400500745810400b00165503010180440030802501000d801c81e0317a4417940680c0d0000c00f2170341c000d545134101450030901030031080c20707219800c80d024032002441c00c80001e01d050040d0f43d5000a05117802598a40780c3c14440d00410340d110b900b00400c0005520307140c02051405005101c0050285c0448620400100c2c0c00c0c003500c010000e01042c030007101e00c40700072411000c5403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 206079001 1250 206077751 206077771
    0x90303020a02060703350c0a09030807050a020604091e18020405100f030305030f070f050307080c041a07020f19050d05122b05150108040c030b01090905070914 70
    0x1c135800c4c9021105c41c01d40807141000c210b0708221414102d44031401304041c00300d00100180e07681c0e40f240d5040405004988049002031414a000c00c00700c2c0f030004c01001e905001d0340c250b03035100d81c440d004103000e54856404240d4403540d6084210050000c00042508a400b040c1c0c140031603544038003003061a10400d40040c1c03081da502d001040050340e4082c1440005c0541c0446000090b9480c14041c04d680c00444100c81018440000101458442d289100c4070301d00640b00d15055880d404412a00e52900801100c14039004200115402400c8184202642e2260300007582d55103662040c40806002c40da0301da40920801e5604400303800300102007909681040e9820708030056035041c11840c4c030551180130051600000b4020201c0d00b0081c40ca904a1003860031041c0b0486005040042100d5085620f032042401100841906610034103131207411502400490780d415840f51242c0d0078015081c2c0c0001c40c110381e10318070001040000d000c0c9038010309146004101c40c1da0422503260b148074000b0035003144 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 206080251 1250 206079001 206079007
    0x8030c0903070905100515040f0b031506040e2208191205040606060206070507050712061e0c14070209010501030203060303070c0303090302040f020a09050f031f050a0c090303020a0206 81
    0x4a41c03020011a0001c1140b00000e00c00350824510b42e541d990080d024050041c51100403108407058208200d50880702070081a2105525000c0001c0c11030f0000f80c609079841d0030100c00c807121680c50358040c0019211a59003030180c0c6c14601c01200b402d25181d6080b10f60654001400d03000700300340c00d0a60702c010184800014142c00d04c844121118424040721481181c84d01080c401403181c96840f40040e01e9194007110030688a0540541e0039001e0700d04024050780c800501071018a40301403400050622440b808910491001080e0342624614071002c450140d484211252255011240403600440402da491404040781c001c2803840c1014026241455000808910349890400845002c0b503004083c5402d81a200d00e802044102c0070700c000c0e4031541c01c28020140d090414800c484020b02d0540300e0000b254580824850a2401d40030540c0d0b140c040c44e80403000000c005a040720350400500c1000a26150803c00101259032200d6050704010881900340300180d00011858402601180c0d1145c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 206081501 1250 206080251 206080267
    0xc020718060302120105060406061704020f062809050409031205041e050a060c0e0108060f120111041a04060807111f020a08070e0d06050903041502160501030908030c 73
    0x10107800d9942c0000d401030802c3c03820704031071481076003c03a010f004101d6003440a1503481808a41a600b0180103140480f00d880100700185440c030181c0542c1c020140a0508103103000903008909803003001e0b020007c0141d80c3c01d120095a00c010300b440034000480c0c080242c405240c034000d00a00240c5100100300da40d8001080c184403d02c02c180c84140209415554810740c00c1c5456a100d0881100403a004c80c18408000b039401e001c1d41200c201c02c8810380d82d002c4250b075403134100032183c040b41c98100c0c0c20602c05c00360442901d10a0042424160180c100c080e03807545001064125441c00142c0c00c4031010040c0700600095a00019480c2c201101e450f10840b1213001c40909802c0171010f541d1100000d1403c105401d03d512190003801c050707030550b1204283c56594003000d6844c3c034070503019607a02284015104d00041d040b40c0c00182c2080381041200e0810340c68840d40350100d40404160030151f0301040c100c251400880300c054002e08800e290501c02c1c0c3c03d10f9940d041c0c49000181c03143c80c0341c5601040c402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 206082751 1250 206081501 206081549
    0x3010f09110702061b0c011e0806181003140307050d0804080d09151b0807050a02011506080103050f0c01050a030f0f050c13060503010e0c03070c0f050102040e0106030c0207 76
    0x145031181c004180c00c0e620061142e580304040c0c03110742c5d10895030254810b034080307560088500802c1c8820302480f10030180400c4600f15401342c002000b250340449400211114580741140d103d11400581c24a50b8500d8254146841a9a500e5a0130b4010358001c00c0b420300042ca0100b1400308140103400d00ba2a5501c4270314100c182402030525110100707180030031150038402003440540c0c403540c490708108001c4264107110045520304402101c04126034002103515a4420300c000d01758011281b000107011110540714484800261f40014002140c1e000103000b03020090000f06e07048103902006001e82020000080d201d401a5402c00b41415525524103106c1c24080d00451001501c109080010f850006107490b41608400c1601301821055a408070318940144216030584060203d01e842e159500c29504500703031f1005205078200001000b08500142128a04074006417048001507100c505010012034880b105a10000c1014100341d1035205164010421609903a0400020464034131420000303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 206084001 1250 206082751 206082757
    0xa050309120a080f12060402070f021009091a030c0117040f020d050607020708071202060d1a0306070c061505130518120705010b060a080f040201021203040b0403031103010f0911 78
    0x83c0040c000000c80d14a05804100117007040701c04400682e0842e15210103010881c010301030020840028412580050300c3c042d00c14803803040c803500e03040c803401303031500030075003c0c0c0d8444041c512045214038040c075507515051088000700340c000e10b810b503882c50b1040048591820080e001400805100b84110250740352804801c0c80e042d0484d04540b0a42071000d4025a5101e0314070030f45c1954003448002040e0000d0650720845015002000203090050940307502008205600b95000700126000c0d41041944040c00201d00ca02070310b8840c1504022513081c01c80940794200e20f0801000001c4206104585d10101c1d92404501110b07000160740e5100468048601a0003411601d18071406003000710000e40e0000800f40c10740b282c1c0090041034500f2081c45801d000f072107c40d40c04658082d00003072800b40c3e80307048242e2040c0144100c50940903400f1405000394020307581500e00b015110108014580c05014060409000343d100c9131039589000c0b500001e802190007081740b400d40300d0b01900c80b0a00b1100c29 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 206085251 1250 206084001 206084003
    0x61801030f08091806132c0f0607022103070503010e070309050f030406030f0b030c010c060204050d1110110c01030902030c06120423030a0c0204091401020a110a050309120a 76
    0x25100b4000360030211130b5604042244c59612035103443c1c4401e2103800745405410880c0208441c2850309000450307010200e0b07410b851b4600114422941e034020a064100a40f0f80035070714540282000040c0e0202e54080038000303412044440c10b00300107114882e075011080b02d046420030a10aa8152140c11003140949a1158003521034415040c44e2000c4d10f80200040c03084400d65182003142000d04200402600e03e009441541604134800400c0135500507940e11201c2c52003920010f141549800c0040c03607100c8000b00548620485c0101d401850800c03420b0403178281c0f03660400c2c000c4003000c040b00355034440c807109025041548400c3c501c01103403001c021843c2881f1300200310f035488450a03109008a00400c44058a107e031456006952910469411405649116001c0c0d440c00d944003000343c40c00303004010104c3c2c003d13540b41d030791a01150b408445640341d500c03073b000098bd0303d2702c0d80e010003026402000611072054108034181c0700082c10001c1124014002941c141c09503810401a5600307201034104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 206086501 1250 206085251 206085259
    0x3020c061003120c0326071214180f010c030f0b0904202b02030c01080f0f100e090a020102060a0c0917010204030b0f0f332106040209061801030f0809 66
    0x1208086c0000d14040262155120795250940010304e0f10542d0f09455100c1d52400309504d1b842c0120b441010ba940003003131004240000c5858116000c0c40c0d0301d00715070070102240c0000380c0e00c4142c842c1c001610700403c4a065011a541249810103454544100951211400101c1006600d108054448a600079889207081052181c0078144080509540035180f10492090084414032145907000f020080c0c041d0300c1d1900260620798503120645a0b400c4043c0c11010002c0c0016000140549440c40040c812000700001e0580c00340103200180c500321307014040c0c0a81354105090703a10141d50180600080b5040c0f81000e8044003000110640284515000607000314003200c10011078040c0d111015029032902441011560345445401d90320122001c40540070580c82c007242d06c3c01c42d18190380034400c0c0d00010071b8000c010850982006619500c0401c181d0980c00407010001546418280e2950020054a1480011446800a03d04910140001050004844e4801050246050540740c100724054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 206087751 1250 206086501 206086547
    0x1031515180617010c05040e0432010501060504050f01050d09050118051506010c06090c0e09010e12030907060f03140c030f062e11010c03020c061003120c03 69
    0x3001c680d000d854180070703200030074044401c1c40d40c0c91030b414424291988019176031241014240703c0c0c220901d50300544185d407582640c62610f00441c0000c00d184005005000c0d01c1800e8005003c40d1909582050340580700b80141400100280c1d100e4039590b6807040024a051940d0f4918040408001c0c600d090307000d000c031340c80d000d465101d403483c0d213010940c03244c003400c01c0701c5044600362051013612500b1102c040c0080c41c05000e860006603142c0000361030300c1c0300b00c40c80c594850700c81440d415584001c90340202c6607074580c203101c00310a106101c940988405812040d103145082d141c01941c516a5114860401100c194001c410a10a90080d4031802006071400b001d8100920880d90a400a490860702e020203078022078801e03e05a144d13aa600c540401d0401620341c0d00c1e24500100088000c04281400002e8801c0d24480c0401c0c03081e4200003401e514010380321150303001601c0c0362820003007c000402022813814404107080d8400c21624084628000c482e603a030314a02141c0b010000060180d59010070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 206089001 1250 206087751 206087789
    0x105160b0c09031006030503070b04020607151e050c030609040c0e010b09120303040b2802030c04030302150118020a090302100801031104180809030f0a0b16050301031515 75
    0x16a0040c644110214102c4140744d11840c042021220b0750311005103aa4420411000003503c9401d40562044c0010185410132031507484c0d141461007040e030b03100f0b8516a9841d00e54004040644c1401c0404c4203c0c0b01004245040c41d02d6000f07620024103070713612030502c00300040c00300031101003244003070400d500c0708045a5944030404040e54015010082c0b00b19000702e841c1189407000020350384250f80103d40010740d070311540785807450340c4240f010031000c08114118088200c80140000c5004171481e1503060f940d18654100241000d4170042c404e03d94010b814010000f10030035a0401700d00e403c0010005030b80d41880b9000342c503040d0721944001c5d04090008120352103146c0110000b41200e014076102550120f00008200466220101b1801021110101a03010801820280012400182c11151003225480ca0b0616200e01514200e03007a0309500c04200c1001e160389407510100c202810654119410f55548542102d000ca80000c5042e5607034844210701c103007100d4007500a044800d400c0d40d0740700708 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 206090251 1250 206089001 206089021
    0x31e0910050c1b03060a0911030106030f0209150607060b04180506070206010608071d0d0b010803030403020c0402070209070e0a05040e0f0c030c01050910170a0911010801050f0105160b 81
    0x42d40440040340a00307070041c3d8042041c440d0268400314020058003083d075034030084000505d4440c00c213983c15242203080001e0364500344290380145002d42031000c69804c0c00e00c10400000c00c001c1c02d0300009012a80031240310744840c0c2c19200100c1d4007031808075040c9881400f1074010184090f064002c00e025101d031070103019000c107207280510001c0d4280c034403c0c0e8031143c05844040c0d0581d541c000051211401a0103800300182145001100510b005194809521403c0c2000c501717070444040e640002050004041d0100039560b0140d40c291825420031070781e43c001070301182c0000d00032404e000013203264488590381c071507900000c1c0100410800028224103a5540d90b446210f403401c08a1103840d240407400d00d40040c481c0c0038224141c0d180c5250810102c288590302c0340f10105282070000c3e40b20b2260030443c101b51294402c405007040004c00d503000f0b050080c802c440700c0c44994140085140103000343d868400010300150f1003070a016980342040e4000300240201e25602410b40d00d00d01062017083c0030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 206091501 1250 206090251 206090257
    0x5030702030106030b0f06010206071e090519081b0a0e040302011b020607090f050d170403050d210b0a0e0601050f04150207240309080f030a151403031e091005 70
    0x1b21401c1c4041c00d0381c603500103a0707407010700f0b40b080004a141c00c00c40749540150072a9207103018180b440c101d40080c1d030f01c10115280041080440c1e913240c24403003082c000c803039080044101030ba60464000b075803808540d002c9038208260380104a100355040d4001003e03d03000750414001d004580b00000c1d101c04240c4002501ca0405031031a40000b02c030410300140441c40c07007400a0540e90001c0050540842c00e64625100000100084035a4070b8144400000f286080c00b150b060081e26846962802917039002c03242801001400c00982c00c2d00d45070b840115034070741070b42c00c0041d0f4542c0803020002c2c0d1602d000503511409540c44c0c1003640d5000040c046411281810b200604440c290201d452540d11064820b010007840701c8015070000d0340d40c0000045c5840380e008005018007800314985880d0243e40d810302e081c0d00413036001e00101d444102d4101260302148a82001f807141080c04d25000703580d9000641c4074070852903032030340a00101c24080d02200b80181140c158440007016285d42914074030000c1c144d03030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 206092751 1250 206091501 206091511
    0x4230a03030b0f01030e10020a0201090b0708090d030e0a0308060102120d1d06060d0b040f0804060e09070201020408030f030a02040b0a120b0402130611100612110a0302091305030702030106030b 85
    0x1c2039914410f08a9400f0b0b00600a4006540001c2d1084148002484009412103c1e03c00115902c1d03801d120f02044034804041e00030b466503965102c1074985182800c0c580703104900c0c10000c045c0b61084128641101103159454240d06103000c4401340c8480700100d1501101641c111b2401e0000610100902c65540c004821f0f01c0040544403c05400540c0003915008100c900642140b0440c00200006103c86140d40c2e20a100701d1403a04a91a10380799507903160003541240c80031905201d461652440d004a06903070040403480250310345400d00d5100354503801000071182610790044040790100c191038060350003400c0c85a12554403409030320001001c88401880c90050b41d40741815559180c2070900854500c00f402c41c604030401c41c038200e801c503000d114100c1c4855813400b400182891500981c010600240500d2403d00310320a03560030b00e01e4803a2002c1154521514020b6401c00045e103c59040561021001e0100d0b42d203000700d403c01c5400c49c41948002035240d40707401000302c10001d420218500074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 206094001 1250 206092751 206092759
    0x6050a0b070209061005071506091d15360f07050112021e03040201110d02010c0f0201050f0a020a0504090504031706030102031003061107020d050a02010206100b0304230a03030b 78
    0x70351500400d00c0620130842c000d079070002c6c20800c94100443e0300700700c15403da00800c440000740c0640d5180d16a04540b01c100782c040b9101c0070804892800c2d50108840502800843c18103c16410701c01e40f4500b814902d081180007521240210a980114078042021100e0400041d500c4900d4041c004640b94503103805450702080c01360705407203240718040c400d8a03500880e00300700003140300d004007603e01c107a000100f00720f040100034001700c0070828052005140c000344540000c0382c1c103441c0c41c01c0500b224210400000031a85410100028907000f074000ea608455105001a80c3c0d100460b001c8640d441150003d4400301d0926081c841010b50000c0d140e00e4840b070034445540140c0300c2d50105802d0344003d43c2d50300003010074003000780086005903008402c3c45a4140080e03141c040c2c95408140344160290059a107500700444550641d44c0500c156036101010641c191603040c11b0020420560001800140507040d15810300312058500c80311880c138aa8030ba0f000c131099050795150060241c20510302960003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 206095251 1250 206094001 206094019
    0x3070e0907020705420904151205010c270302040e070b0f030907090207020f0f0103320f090703030e0a0e1603060501030b010903030302070c05061c0627020d06050a0b0702 75
    0x70a040e01c10056400422402d446c00da8040104005807081d0400100d506030584000104000201c6260f0f0301c0622035400460f0840d08008040c0620400c3c1c20700e4155040c1c8000f8011651020980302c0c0e00b5240d04440010f0f00a4808a9683c1340c8080c5820040c4c05020016900c1201d0b031003030011b580b1540b1036204a4190341c2c1c550005200f81d0268040080d0400440640101c403854210902e056a00041c03400142c160703428500c080f40b00c00c031540d51100c0702e4020003100800e0401ea049440d40300316805a90a8a414080141a6141c803144005410082d400420500035528004058001c252079103c0c804a41414a07900d02d85010030030050020915017200016a035000340a4541f501c0300584814500502c1e41e14260b0280d400709204680d00344249078003181558406014100c40c280213058000b01e407040b1060b050407626a45c11094948050a00d80349011000442e1044028050fa2002d0b8945c0c9811481a01401c03040d0801688821100130200704030f8400350103000036030300031101000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 206096501 1250 206095251 206095339
    0xb0403021506011715030120070506240d0303020712080906060d080318010e0601030305030f1f27060e07020d0e0d0f020112020304080301150503070e0907020705 71
    0x401d609114440703010b0100b42c000145108244142d55017000d1006400441c0403c11055500606010a40c1c800714520011900c1c0050000401c890381e482031800c03205292034900c0d10300f801c00f00c42c49105510b02c5003508441e14010548650156401e40c0e51100703401024410041000d815040d040717034213111a00c200400203096244c1300d420501d916130401009803440e150700c00328002c034241301201075821390b403500481303070060b141004500c1c0294000e0b92005d4403030602d40f80c1d065152001030001a5403004800700c1030ba000405003550004c4038458045640b0f001c0c005a4200c040d400524140d1200307038542240042d000588029213031090f030107682552482206020180c84c615840345003980c1180300d003030b000800204100d0f040d0b02d20f50300506281403c901014040380c01c2e0791044030112039034100400100450040c81c00c07880709181e5035082180c1107203172520005040c140c3e40000035105440500106041034000c2c0700c3c5c10f001c0c100141c00402081e04450004003070280c4802c881c1e01031034180080715 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 206097751 1250 206096501 206096507
    0x2040c05090a0509130524010816050613090507030b010201050610142d040513110d090c0b04080307050613080a0c080d09030f1806140706090b040302150601 69
    0x280711403002030940444500784824420748900051000c0955160700c9140c4002c29410054001203c0380503414040c4442c0b8a000125060010b900031076181c1e011001002403010401710000a40d64203035540ba0300d030382a43c1394070051310307540da84100d81051a00090004c910750640009901140c01e070000c0c0302c107441e15000c3c001000449030040780001c0361410304c4d8007944030b210700811403410440041c00080e0140d42035841c4506c3d030054820741100d07001034200306d00d00300310312042802c3c034203120100300501c0018501d0003e0720414450007403a90fa00c41d0280e00300b00c002170b00c400140407054240c9889a881d01d0356140d5039072000740c00750f695215000c0055610110008408203403a440060503040403040340080d1080715070740c44110342c480342c180400181103545101d90101071740290381e000282140c01201400d20303101d00035021040b401e0b41109001d51a040b962141d160800b0444031551200706003070660080280400c000c10f206d40c1c00050005055000030709140380700025101c0c03241521024019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 206099001 1250 206097751 206097757
    0x607120311090604060305091509160608040b0a0f0603050f01061706041e060207051f050a0b01021902010504030615030b0f011206020d0b0a0603020a09050f0a1e17060402040c05 78
    0x820f074000020041403002d00e100360080c6801c56034060442e070100c082c0c0304284418500c22a84d42015622040c0c11154440d40507194000819260824089500702500e820200b04c10046c0b41102c8192114224203401c005903000c24000c64000e4150303142c0d110100a064080e01e11446049402228110300c400f0544c00030030090f008540c048640380c8080b41e2440e41c509155a03c80c030560380300d6404c0c0a2000450404e10100a821b25843d43c0020402c0002c11584101ea90140c04c0300c1c480340c40d001c0c0c108016600015204000840000004001e200d1480100c400d44510340008203064281069801d224541c8034580c0c0c02e40344516030008182e520348082d6071203202c0034401c5158078042103020001003040ca1f40101010248900e001c203a24030ba080208034110301ca80d100d03c0020380e000606040e1039602c02c1c01c000150104850981c0f1550060b00015100100c42c00352100040d12207071150141c06003201c0540003010341c01003000d000c5000d0b500ca561140822207003a0b01442c00c0002d40d0349014890381c11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 206100251 1250 206099001 206099017
    0x211a01110a06092102010603210f0809010603201002060405030d02090a03080c060402040522080f0c0601150314070507140c040f0902030705010908120901030b0607120311 75
    0x24081c1d20529110403000d45036103001612034403071085000000d1500243c20444c0070001d40c0001c5003007495450b00075444005615a0990400100d2500e000140d110fa8045200356203450518410713102c43c1c002074010999036000400b081f96a02d49000c0d560590b252008600404a8142c50209012101030b40c4408c400c80d4014201d4004110420245806d5030180040701c2000e0503c425aa840341c1e108003003a0b01c030003444401795011008000851525016159102c0b040826040c0d0007003103020282851001c8a074000c04ea41c0e00412000c0542042409441c040d250b582c0407503125503510160001c003c1c84a46511001074246807069821149508120b400341c825607441c207283c6181521050391005910a21851500030b9500d4410503585a010351341100e01c1042c00018403103042d02c1014584074042d88598103112071044100002070700840c00d103900d0480040c1c01c99441e01514012402014410040740d44180080b5503c0b0900c03202080360414800d4584040100e00d0030182014164011000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 206101501 1250 206100251 206100253
    0x904061e0f06082e0905060a050301110f071b0605071a0709061d030607090f0806070804031d030a08030a1404080d020c01020906040e040201020d110309010c0201211a0111 75
    0x202c1c240401d032140782c1d524582188034502d42000850082075800031540d105d924156240c0d4280711191406008000041004400800000e07560360300d402140d005001e0101d05484010072030005000b4500300504401c14601c240b0b00700113840d0003000c0c00e00d0b0001a010349000c0c00180094442408101c0064000d011903107449200514140c0c084612941400d0f035070380c642c40c0443c40c484894034100b100900501071a16a2a41c1c2803e00341400c0c1c2181c069884003595501c51001e00c940306810000f500e8005130580707086140b01c1c980c1c0c0f20103000c806880c00180d4048c414000941d00748031542000e1030017540f241000b400340060300c3c401007521000c10b40300984a10350410010024260380d500800b818000080090308201030038000920a410540c04480006c2c42801000210b60781400144400c42280c1060109226841d1000b6500c1c0560040107041c000000e00e440156801440c4041d10f01706070302084e1041c1c016154000c000f4040704640c2e0445c00300040f00d0300100350f0250902002040e1410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 206102751 1250 206101501 206101517
    0x5010812030a021e09010f05030412050705190f03030509010b010807200102040807061e0e0f01031103071d420f040e0109020408150702030904061e0f06 67
    0x241000da91603001420040109508000c4402d4601c001d525030680188007640701d50329401490009804686580000810420100b04100c0001c45131454411215010301c0c0403a1244101d1400c145420040619110341010703a44c0804100a503101c51b00c104030307110303a8052100f902e400c00c0f0300b8241d440070250140414100800180650310540b001d0810110326299a90700810801d141405ca0f0303c2500310708040c2d04043c0c2c050044980180858011601c1d804094030488000c0c84010f0140612880f080d1007801a11220300f0560b219401c50340a10680d108900c1c1c0c0da00b0001c40c0074083d01005203400e2307030a9044d00700188582c5001401003480440d10324a20252003480c00a0380c0c41c40351900d00c0d41244180d501c00c480c50320140b490240c5000003028024a0f6070782d042c6048080e05000580c009504280104018041c58401260461100741d07030014001003501c0d140c0f03050307085024803000650000d01d0041c00240c0c500006400413140e00c0d0090442c46031a488010742100e03400e0034000c2c140418044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 206104001 1250 206102751 206102773
    0x50a15080c19230310060b1b07050105040b221206050c0a0203090405060d0803010308120f060a03080715020f090a0518060d03020c0409030908010f090c140d17030702060703050108 79
    0x403840078200f601e004041d03500020000041d503080780e06a070410b0084030000700e102524500d031580c0a01790100500000d100042c900800207040340305601401c1040c0c080071032141401d00ca001180d00e0603003100c00811020340d0700e0b26000840f07040c80d4641500e00b18180800304541c1207180084641000c547d50165140c40d80c0c05043c04040d020103000e498001c50f001c0b41d481c010407510030145019520500103159249900400c5003440e0034050b041e044410032880620010350748100021044070740c01b1504c540c4800290400004803125020701c4183e260000482c040140c409100400c80c000c022681244001d0b1100300340b0041d1072001000400c034030309100100b24107142164011403070074800e104580b1041192004075068070302040c02140030441605081c405070302c081c0540c80000948203070800c00402c03651600d840d181228840c03003584510034545541551200c0b102051381c01d80041c0040102e290212000d106944122101c0005000b808003080760780f4403e000c2c2904035552407000b40040100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 206105251 1250 206104001 206104049
    0x2010f0c1106180409030201020a120506010203031305010b03060702071701111209030c12041d04020a03030f02030903030415020105070c0b19020d180213110d050a15080c19 76
    0xc3c203c0ba0500d040745450311010340d450703014100005200341d0003d40c0b6180c0fa0070024014481412582d54903a08200403c0610b90380002644e41c04144804e1034000c2e1303c4c90381400390042922850b050b070180141e0381080b00c041e0b00084c28000300c1c0d4150b1000000c0003411a074441c200d40c81c10606490046080010100c003241d80417255800402da00162031a0a0a0143d4149010840c5a00c1c1d40c56041c089000c20400801d595045000c81c0311500c003d0191900c0d50000e00390462500004040c000c035541c84850b180d20070419907906650150490303503115120341d00054901d843c40302c98801036082c100000c0520f4840d03010909510f50080f4620215210111145e0340c500c0c1004150440c16428051000c22413000d000d50301d0302441c001c54140a10200340140f2082915125049a503c0d00705440a102800c00e0701c2241d0116244517000a4949c4452041c3d00182803901041101c00404a43c045590200401d20300780b4a8022210486002d4084007180e501c0555841401c580000070011f845030340700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 206106501 1250 206105251 206105257
    0x1a1011120c16031103070902090303070b0709080d08010333020a12050f150108070e09180123070c020a0521060c0a020f0114061201020d0f0902010f0c1106 68
    0x80194280c0d40d2050404141c88002c21641d80241d56000310010105440d05051104501601c3d41603020b43c502842c05022950728429024001c00344000323070001079045441010740030302515900c0b007580d00302d205c0d902c401000590280002d44500b01d0940389d5002c00070304a12443c00c01c1030740c0d10300a400400c152400200a400a0859406025004600d082c10441c207220703851050114840c0074041e0700300404044146442c06d0410f60502a811084c460040e41042000d02e01c0c02049500500d5550766601010300c548289107500d8940d07080980c2c0d00c003a420301c04c1640c4150841030790341d209140c2d00d901c03003103921000c03881020f034201c580e2071414005c0303050140e500c0c00320981da20003c3d071850038200d540a00c2c0c220100c502c01d043c0d03a800300c1e4400c40258141321601c040e1420314024080203a40b4113032a88103030700182109202d480c6401003e420f0040030b4061760303a110341c40c4004121a000025450001d0919108100e00007104480c15000007406158940b030015009604c90704143c440700c0910842d54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 206107751 1250 206106501 206106517
    0x2712021210021b010b090c09040c05090d03020f190b0f06030102161203060b120621010905070f0e1501050d060e0c1e04060519121a101112 61
    0x1005000500060345a10300003425070301d260b854001d4440402c80700c004e084900d07032081326125035188030a001c41100e440040e5006004200c1c0c0010340c7c0100307094107440a10a100344290800481c107405000e0580104011498002802c283c815401800d01c03050306030209828000c01503180c00b0046a940c800c80e142050740104083d00040c54550711061021001440d83e0003203030a802080c09111311190b250003a80000c18080e901d207801d169503418244048100240082e024025140d01c50032051042550000703030304100300003000000d000e41821038031804035010f92000000d443c13034006640d141d078501441c07250325445401207000c0480700044800d54064001700001ca42c40e40300100e810000c0f913085070300810012054503607641c26074070308010712048171108904440081c00204a4907410008071103620f44500300107000c1c000030314425902c18852000c108142071401440d0422403c0c4409103280240003211443c12280150b06c04440004880149451035040083c40029900700c500c0a44015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 206109001 1250 206107751 206107753
    0x150c060902190906080a23031c02040608070f050304140f16150c080d0203100b030c0304050f0606150918070f1701030c1403010f020a27120212 63
    0x10a035540005110080807050080c03502c1c165502044109a544100c1c0001c020207000341c2030302d040c1c58851502d01c5400740e00205400d0410300310304c034514005200312078150125a2008a4009046182d100250410701134017010030358400105500328003403d1512100d803807941d1194651b41e00c96880145140401100000c14440d0307402e00c404980f41400b0003500c840c02c80503032182035403a06035444c401c040c65120b0700c0c0a200e10030941802103144102199945140000c0250b907986030b040c900c84030300c0360030740c449000b50340040b05105050450f4001140203030702030780403203011170101d50b00503844002c02d0b40e40da81c4c0105402900b108190b0584041e2004100c01030500340c181c10207440d81041d00d00122880400102442c1c01141c03d02e4000703003c0f8440d0004401e007010a98156a40e4261505003401507582c501c00340c2100d030103199402d42004100c0c0300d0304402592100c1c41c2c140c2c080c100c15046061107410b80c00e000c60403201c9514401c8407034100d60b0101641002e000082e000d024101032004401038032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 206110251 1250 206109001 206109011
    0x81b0703020301020c30030115020705040c05120a0b0618040f060e041b0e0105010809030c01061401091d0a022a030915120106030c02010b09180606010504150c06 71
    0xd030b502071014058032840310020303114001001d5201150041640c02c0d15a04c140c2c1d100321044031a04420070f90741915884181401014000e02c010f03490558039501917a17005041c0340e00140902c2c0d218000d4070310b5903038011281c841c549840741c242040e10000329526821810502c060200079175065003005101038003800008101c0e150032941015508180c014031401581b036001d1004001ca5228161048900c130802c4c1e0400ca41804034000002e0418420306040203600001308003025824030480380700d6014500204800d541d40c60800c2c2c090103c101001d130109805110004140c045d14000380c00111940040348025139495072650001d403c007102d0a02a0301b01c446000c80d880c000d0800443d00040404010744e01c6c3c4c4c140104210840c2e007810b80c45160000140702c4c3c1510050b00b00f10b41815a00c0c507086c00b1811700ca41d8003003240140400412140c0c4211114280002200007194003d0f880340c0d11015604a0ba44d40401590b40d44554452540d844d501c201180302d10034441e4185021642c401d0b02d02180c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 206111501 1250 206110251 206110253
    0x2040b1305090f07050306040b0604110903030a0e120304060504120f12080105030c0d0b04031121070213061d0a021c0e0708010b0a0303081e07110607030207081b0703 73
    0x840700100c40080300e6903c590840b42101c14200b051000912040b0001c0c0140d24245d40c400c0301d04003000d8800c0d8000d645406e8804010b54142c010744136101c0d0f015013201d413658031142c00205070002d40f80c82e5070301403aa6964154003c0c2c078048200c030291001e51300c80301d103042d01d800c4c0d070010031001e80d95050326029540204540050460380b0b0210b40000c040c2d49005455050a0416090540502c4107034410701281d2410b50018441048a580c419010700700a0000340c802e40c411824a00000448403e841c2560346944004c046075010300807090007a202c903070504401041400441d0300310301a030107405180e482c00c01c140c1c203400c03481745c0ea0110314a032000d03007014400c4016048035840e92a00d07011194455501c42d0300e011041103504010840c4000a00c80e62200e9404243c1242f200c2c0000740400c1a400c1c0000e43d14001c002c0c01d018400d035014244203291400c20310081043d06c00300c40520703140c0100341c0440c00041c868003d48000c00d4020b0340c02484c102d0003141138080407000743d86005c510300550304000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 206112751 1250 206111501 206111539
    0x141002040602061501032a112a0301090b01210b0106091409010b0a0507020409021804050709021201050609030109151e020301031a06030f07080d171302040b 69
    0x4000c01c61500182414241401c602601420414025042519103c0922014000100062450420b110004260700d0503030000325111043d1810540803841480041407021035030740300100340400c01625400c01c4420b0401007600741c2e078000102401500c0840014480050030401c2c0b40c014140465001c003a0203000d81e500120604240d000d86c000c0bc41640d020460400c402c0c01b0011110300480f040a107540c10a600150303140600032024040050114280c4219220369100309480741d0000c0502c0c105800e04400803c2034202228101c4082c00b0700c4100007080501ca000359040c4c0070310398410b51b40c260b08041c00d03c0202e4002040b0240d040d0748641c07484000c20186144c041d84503160010216064070b40c80e003e5059407554454200d00544104010000709050400445a1a01031014050306413141000a45040c21160a00f9001e000d200070006551a00082124800000780c4a48400003514600045460421102040d20030315484144006140940c031415034518000d16441810703903182d07410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 206114001 1250 206112751 206112757
    0x1d061002030c0d081b070302060a02030a0204080604051e071202130603080316020115082a03060c1903060b0306220903110f030a1b08041a13061407141002 68
    0x803008503282801780a2203018212500344a25004500a8a40a1565030080d13403547d0051805c1e0031146d0220100d07400e80c4468040f540244001c004440c094201810700301c0e169200100180b2010984007240003031524045070000481b068100b0210340301c0456020320445100c1c0e407034120942503803008044001015000a11f0054044031000c2d4075020048030081d0071100364160010b03410004000c104001a40020000416241c54642802c0c0d11f880210941d0004000700c0061b0340341c00344504010003400054094040e444418601e80c0702040f0303e44085e41241c03017501a0414010303003080020041e042203a48510110500b02c0c12041184403070010300221042040308900284c56500960125041001803080d0000410f0240d45088100713403018104d0707008810550b10107141c040208051080b03450075900140b6510b01d010028034443e10080242d940258902e10003d842c04002042c00b9200b040101d103018a10b02c8003e2030490039480c0e01480b0110b9007148503103885040700003200c051560000e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 206115107 1106 206114001 206114023
    0xf090905010b09072604030f08040f120e0111030a0203030414100c05030a1b14090a0f0b04030308011203120e0a06060308131d061002030c 61
    0x800d501621080d1011a48000c0100070850300641080841c520441420324014404007200401490140d066a018002820780d00e1096006401502c11641190082c0d44074144078035a40d031180b07103042c0c0d440a00000511307100110009541c12869440c0724455a80145041940c0018002e40e40c0c0402071011300301842c1c40c4144982000f080c1b0000b00103140400007484410905074024203107500540d4409030540c507200380c81044083c40360f01400144103960720001c3d1410b0746010480c107504040c0314242e000495204c0020078140d0b1245c00d6005058620032035446502d18180a0000d040580c00200700080003018500080e030f00c41c00e440039507440044005000d101e10920103103003070820f120082032603250a0010003030056080181105c0300000d0908a4031035100c500d007012041c5140501034a101007100411842d1411420f41c10f0f001c0803e1040328101810044407510344080086 = true := by decide +kernel

theorem cover : BRFrame.Cov 205935251 206115107 := by
  have h0 := BRFrame.cov_init 205935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 205935251 ≤ n) (h2 : n < 206115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
