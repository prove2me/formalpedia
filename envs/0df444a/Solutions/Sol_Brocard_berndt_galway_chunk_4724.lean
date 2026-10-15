-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4724
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:31:40.714024+00:00
-- url     : https://prove2.me/submissions/bc4ab883-d60f-4a67-b972-ad25067f75f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 849460431 ≤ n < 849640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 849461681 1250 849460431 849460457
    0x9140a05091009111908151006120b06032d0405070b031e1009201902010b030709140c070312181a010617100314030f030c040f06020a03 60
    0x394001860705401026002c0030341312035401241c900320308080c00600910a145041c80014000d101000707030032002c1c0001d040107080850700720b200d5810750b03c40c000074421030300b03240c02030521950080010010010b000a0716171906074240103a000790030480260f0341a900040800c005606402d05010700c1d046002016800e040110384400e503800035264500e02c9042084600a407000c03058918407400020920f003042500d0320400f00d05030b0b00701c81103640690000e04441d00c001d2500d0020f5500301d80b04035402d0200b0102c9040141c3c0100f00c0302d00002d0305401038203c0820060308a0f0006550501355559508440d911281407006078000c0120083c00188070700c490303410002181c4c00c40810b079a00216400c4416810360740798081e1100c151844184034036040d0041107850342201c204000f1a015000c8604c40d45480800d111611031036002c000c2c0980d0341c2030729110118104100350f0700403400b4809165940c0c180060302e03809940003841108030a01da000000714440d880864030305d8106038075031110050070f048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 849462931 1250 849461681 849461713
    0x1b050a1401082208040611010515010e0d06051303260c0d0615020a060b0a06090e0c04080f1c2c0f03030a03020705061b0d020f0f0409140a0509 63
    0x1020340b0b1860804105074070f8034404400c4100300c0c4410307032003610380a544074501080903002034401c08030402c0c107914000030009450714103048a90088000d1030100d03a29800340000400500010401411b540e282100308141201c000c1001c3c140c880c000e0300d5a0703071000c9101c40c250355024204080031311541040c10200b203110010002402e0042d00c0d5010204d080c0e52150a05500d001440101c480183c2c0700c07468000505c01c5500c144118108d068403200041808c0c0300d0040c2140c0b0081c4502144240d00c0d0000130030503418402a035001c1c10011040e21411300d191880320340d56400702101c601404a41c1c8075540c1c1d1207400388080d10230241d81c07802c4000403201300c518138035480c1d24690402d6802620808401c0e8940c5c1e0140010030b08010140c4005031101a0760800c1403030120300801480003e04413034810307941303101c00c9404e40e048011140c1c40940d40e01c060540114040c000e00b090b100110f600801c011a00b061143c000f1a4111421801d003556951410141826190140d030503203481d410040c500c410202c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 849464181 1250 849462931 849462947
    0x130501080304170a0b09011a060405032e061d0a0b1005130f0b0c010b0a061b0303060b130914250c022e020309030c2b1b050a1401 57
    0x2009005440c04d0003030030b440d00e4403c03d408544543c1c0a03555034075558101900000d81440000c000d0345c18038145824200800c2e035980200701d40e5000c4030a2003215034a44400c0401c87d1448660904c0b0600203207980b07000f900c0105890703020555403240c0c07620019000030210703c03d24444000060024140000d1003406a0350384c6d12842d45004c0003030342c0081c040f8503400000c0c03040c00100941c80c1c0c2c0039550440d15041a0854030740f291803910900b000241000aa60311187d4800c1d4800e1808419032a1041c0d0f181c00d800418055100d1146140041a01c400c0d0f801d02c030f4000402c90b81c24410034040a80000703c0c5038a13908003158509015820f1030755011100100c018040d1085285040c100810130700c9400180e0b030031000c02c20b030701070508030b10142c0e0f80b040340c1e00ca1242c0b03000f0b00700e40001e50402480c2d500003619810310300304543c02992221443c80c2480942080c00d002c001e0715060050310942c1320300341002030008005200d1030300b07282400c00251500b0020009001c403482c9440411050009500450307450f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 849465431 1250 849464181 849464219
    0x1203020a1e03020712110123010501032d0506011b150507210f0605030a0b01140112020705280c23030f010903020c0a0e040b0405161202130501080304 66
    0x503600344a031380000354401c5880002e0310b006498180e894840b005100d8250744400d107050b003a803241180c100210b03212100c06a81991030900b80032555109860214281d100510180d100101c007030b0900b5113486486621613401403030281d81e079000350b0a080c0090a2862545400200070000d41000d40340750500a51142d41c02404500c1c121f0015606502443c0d0300c1442c00380c2404450b9903c104108880c00039200c0e0100420098020f04400d1900da11905e500c200144100c1c5014614101d03030602d168482c001d40d520544e4040d000315107a0689040c220340d5001156000c01003c0380540300c1a40d020b00310340c2c0700d201032544401d1030040c160821043c080d02c224040986000b01e000102811103942d82409503ca00d10030755400011748036070701c1c1002485e001c0c4e10603560b4014110114103104d0f00d07038408015a03000c1d401c00700055164a8500c0c12030301d06411600c40004400340f0a801007040710000c1c00300c40400740221011007842100440030011540d003031180252950040004100d604103042e4240325003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 849466681 1250 849465431 849465437
    0xa090c180b09091017030309160e0109200f030603070503120d0b04090c0b030a143d0b0c01051501080f0c091305011e15120b0a060302071203020a1e 65
    0x35561781008849565100d0403c1105400100c00c01594101c1000050000016007502c01e0079945800c04e5104040810302850500c035031151130303583c004200c5120700d00c1d0001503a0300c901c3c0e692820326640015038100b40d0316140302c3d00481d0000122840e0004a9150b0030030b0a003400c6103404841c407100c40040c9250320540e038115488031804e00106070440d0214005254000e21159a4948002c041c1d0460b60070307040d040020b19404041c008101d19134101001d4250812010208001b08160b401c04280305944142e80360402582d008a0f044a01e00040d2020a00180003444180c64006031855100b20001d001030004107214001440c050000648079040750888192500d008001e102261060400841101055840d140100f0a42600e0b804942508903c2d0348200c6040b8100700c19001700b07030b03030305541c490410454082c2c41000310903507401030512803002400c1390b80b60366645002070040c2d0018141643c6019000b10f50f521034600038000c4500c00d140070750f40e2041c604514040007d2001c0c841c55a2410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 849467931 1250 849466681 849466711
    0x301090207020f09090c090a0614060f1303031112070b06092e030b090c01020d080c0d020c060103060c050408030703050a0e030307061515020c09040f020a090c180b0909 74
    0x81c1c13282d810050140404a01400c2c00902c01018014030600282c4030009052400b84100180d120424103002d00b0f000807142e030f81d0b4400b60301c4200d000b80c2c0546a5400140f400b01000002099003006d44514602c41240607210031000284400d00b00e40030b0001c0207407801e0f002600013042d13407812402d490381c403544c4003280c96403141507001029400752900540304134070003255070144280b00500c40312560004010008110407202100000d4031814185240e03400c0c88061004124200c40110648003840322580045480b0f4180200d030ba0754501003880103641d841c1c0340901c03822003d0b102d042210250f825903401140f400407940d03011540356004141d150100101d02000203120307a8140001c1c09028000c00001c00c1c501d043c40c54190180c00c843d0300c5499001c2840100b030181d41c2c0c01040701ca164017000c442d11400b590b00c0e820a50503690490340c0003540812501000b10b4441415803150002240a68078840c0010105542801d103160502505c0350b0a04140020794851400d004025070002c261540d00f40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 849469181 1250 849467931 849467959
    0xa020405060904240902090307141e0a05030f0a111c0b13020402041d0106030e0c01030b0f0a08030a030c050a0903241b030f0b01090b030406020c101a03010908030109020702 76
    0x60324540701d0b041703e082d031a00050290f40510f07040104401402c107540c140d2484002110020f903000446410101144c0c1302407800144598815049100401002d4159004000300896003502c45603101400c1b100b0a90003a00c3d8000e40c1031410303803007180031000c8040300107402e019120a50060303002130550b10000c440d0385c00400180c88600180009042918031740d1000c601906802c461044160000c4007010f20307103190b03046004000121b0349a155020b080005800d658100400c01e103913080303a102c1d500070022020010361040700000074040d052055404011050b10010b0803104e510820382e05800043c625030040c000308054601c3c0002c849462300c0809000400555808155901c04d0b4407050601560308030324203115014000d0741c1c04107030b45440c1000a03003100000a0155501c50003203010348100440000c0402003642c2c100d86281c101d000c1250102d031440c81881010b4400746e2040a1072001c54002021241014021a1002c070340c002d01490441e0b0030200c0480017504140d81c01e0360b01c03101d240d05c0a1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 849470431 1250 849469181 849469241
    0x5090916230102011109130204030609030504051005030405060a050c19080a0c03020403050d050313140c0f03011509150b0408010203070e0303031608070c120f080a020405060904 78
    0x40c008011a005052a041c00c55503004250050100300300d065906124403125943c44040444180100450b160122401c03100d050344d000380140d40004002c02e2420012009041d0000090801c8078002c07a0401821050082c04480034002610300424079400308012541c0b18100e0f400455001d030800c01007030300306041d88002c0e408490702e0006c0c40000c1417003c010310813201c84500403011500518182940760a00e9030b594165918079003400f4204010340400881c0030b0380e8001108900d41c6800c03003100e01c4140c00c5d001109072100c00a0700c81e01e1164070383d640100450705044c040d162605100300d00380c0848500d0b00c000c85000e0b0801c26480b4150101c580b402140024103a405003001e001901300040c1c40c0e241c5008040d03c40030b8a603604920075803080c41041040724041d403c0032400c0d845440e01c4034a54603070030019502051001e5000f805002e444140d813403801c3d40004141c1d14407145540d03c04081c0c82d50707141c00040b88958002e02e45c1080040202e00c420303007025000301c600398413100301080524802c3d0001e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 849471681 1250 849470431 849470473
    0x2130b060a1107060c0f0803130b09010221190e193f03021309020307030504030e0909071e03080a09150f09270c020c0a0e01030507050909 61
    0x50010501d01c2440b2440c0034070400c440c40152900341440c02d620138880d1146600c01d064070350020151100000043c1c9241210514000c02d1a4840c0da151118101650315601070b400029000b4020380c5001d00c15100741400070303860350207088020740c0c00440a045410820203882c1c04243c5902500c2110708082d8040501e4640d000100e00490074001d114654002549144505e0f9044201420f050b541080003802c00001c0c61000460608005035a00740e511140501250141d124103001880401005102a003640006119a00c01d40c2c80c480d403282d4800400401d41c9090300c21a110b07a02c20b0000740072404e011a8503280403031034500e46211013a0b481d80e95621a610100601c4001016000200081c081c01000301e50720300e100c1c2c00d0981d0000c40210340281030700454482da28004e90240c84102c18110581510100c0c6070392003a05020030000e01002130342e00c440e40c050b0369009100c503a900003400c14541c1c0107641aa90320130050440c1e14a0130082210000000d01350451301d0050090b0011003551804003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 849472931 1250 849471681 849471697
    0x1200f0f0309032112100503072c160c02031507030902011101050403081603090501060f051203030417030718030b010303111903121401090b0a05180402130b06 70
    0x3160b5502224052604003209845031204020b10040310182e2259580156101032010000d00601382e903602404a0241100754000d42d054000c0391404661b03140a03020140300c5031004a0141d4a25510765080c400f414021100c825082a400707824049080c4141d905040c1c4900060444422001c1006070410070750003078a014000c20b554907017440031542c00c26111007804071964001c000038070701a00d0181444c03030700400c207a1030140d030003d100c04164000d5200c1c0d1074050b000002002102e4072005040c036001caa50203007502c1080e0041c01130b40b21800000031030740b003982c2c465186440400400e2800ea9070344c00207080e40d010f001100c4180030312205800e034420011405036006e50615451802d01030049025081c40803000e41200a04800d182c030b5504900b00f01d640d0602e0210300c807220031070400303004142d00d401009001b07541900006200640d40c0201c0066a800c481401c4c038039a51700700b0402c465040c19004e2644d0701080780020058038018140e0703460740e80710140200d0144600d200240b181c4d481840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 849474181 1250 849472931 849472933
    0xc19030204020d0c08090a050c1c0807140c0a050a0e1e0405070303030b0618010c060609020406110106060c12050d06030b090114010e0106020a14010605030f0d020c03070501200f0f 79
    0x4044d1900b07074484417884d0410309010143c40314841548a03282c50b0800d60f40b0312801040808141109000881002038503203030080041c54550003070780f1703142c2180c900c1d8018034070151040041c025114a002080201111401414800c20503d80f4004150040300184100c80c441041e04107002000d0041f03000d603115600c9640a4602a419441c002d4215240d00602c40e00646051206003032150b44920140540e500909003030b6010900d500d0464083c0160760810704250b4008900000c450b60841130001f086014400203010154550804841085080c880907245034000340300030781407a015200a046110a1000103d0300f29102d880350301107480d00b901d07504800e03075440c9445a0140c02880020340908050b1200600a5162490080d0340303001410005d498612001c0d19580c0d4050309610010040c4400307402d0356a511150b61601f6201c0c0340010300344001d401782501c0c64045242c0410fa009c190f4105844080d1100c2002161381c40d41c40046007024043e200381c6546801886040040c104003003d1a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 849475431 1250 849474181 849474191
    0xc0d0c091d0c0d0f09140c0126061c1a0f090604020109061103040e011e140d060c0201090f0818010804020303030601030506030a140a0c12050c19030204020d 69
    0x9403108002a2011414422640c1c088050107007450307080c0c08640100000c200041200202d280300ba100405202100030039400101c40110f00c400804280701a4220b03090721041404850008001d015540030003031030315211040000140e0314500510b820403907983c1280c08000080c05a5119a006100d24803180c1003031384807070b0410401d2495143e54551001c10940501417508299001078031101203806414103019405c6414440c000d02001524000d1800035441d020b00d5955080081121a03503842c06c1c28600031800c0042480d6400080340c0f0300e112400f415440003056503403620f100420740298108110754071038500f000803414401c0403104407401a000f09075224810001d0b17507000840800c4150600c140c410800016a4020040d81e0340404203003000709055640000181c1000251400207002c041194003000c1b50b644c5c0000e0600c0b1241c1b094a10059440d120b494540030802d03001401062903001c0d1311518142d04007042c4401480c0c00c3c1044d1030400c107840780d00140076a00440001c480481d619 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 849476681 1250 849475431 849475439
    0x30c0f1606051207030f0e060a060504051008060402090408072a0f0f12060b030703030c020f090408072003011a0a0603060b071b120308040204060608070c0b0c0d0c09 73
    0x8151034500805107414018500420b0784050500714000400002c00d250b65420407114018190b040702e440d0300084402d83c0e0ba00d2a0071010030000b84410300400c0c1c0a640f40200103008c4400c0446110241c5260704000c1c40113036226400c00802001c020400c4a840f60203000c0600011040d940806104a20040c000341101c80b13208001940c10720380d23000624910340803904010744200758501d00165401c11000b00d19030942418203201801407008040d03018441e191001051540c00401c104015100b210103460300403c6404028040c5001c0d90003801c5800c00300a8a00000c069483c07940016a84c102800400c000e0f1400083c2114070300d0b80d00940c1254451551407007450030388480c2000d01181c3c00c0401c2080c5c1848843d41903400744070340081413018421a0380203034001001c1204014401e4140c00c4244a25a05d00141804001d940807070089084c0300000c0f420a00610031544a21041d07654001c0024850f01c50b041c8206024003041c070160400c01c0b9041a03044640030300d0700c2c0307500349841d86001e403490 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 849477931 1250 849476681 849476713
    0x43605190203040b060f0405011a07020303041502070f0b1216030f0c020a2102060123030a0309030501200f130e010b041a040b0d020906120405011e181202030c0f 71
    0x40c03c0b80740b030b205602d80300041c0070302110ac401802c401303840300704c2c0242c40f84400c1c80860300e507200b1508003d91003504146201443c81d40010814217540001c01d490b2030841d80c40c00085824011081c040101002140c0060701c60501659410702400251501082c1c0030b40080d0074108035481404542e0050f04461513100c180306a080840d4904081c0c00e202c07140b100c2c4252402511214113004400040182403100108000342060b640c030042001419240c51200300d182c06040300c415440201c0302075003400911840e07058118044946200c0860000e450300301ca105010845610481c5002000303190784801007200d4800b1250305000c3c065480c5595610350400e00c850411071078145101c014094200f0007889102d4200094030500c040703821015031191019400541a1b024000a81072484044d0302000305000054009094400306070802c202009020703180c40e826605031460200700322000c82d44941c00980702c0c0902451100540c81928201071164064070708164403800703251550380c4090b5000c441905 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 849479181 1250 849477931 849477949
    0x51c0f0b01021501031e080d150f0e0402010e01080606070c03080903070f06020d0c03090503061e0c160b090102070f03050a020c0a2403110d02043605190203040b06 72
    0x43e060010040ca50300d1582c1e20007100c400d13404041e00c00c0714110002003c0180110030740d129040c9006d002d101c209015200c05402d402d5600c01c1500b0701c0c82281001a8149840a10900454040e0342d00c1c8041c907821801034130150409409d558101d01c1c10490325000c55285c01d46071000d54031480d1425034440d00303281018a44003186d040f265545692030300c01c01c0390a0b000101042c3c052454141000441c03034a0800ba03c50540503880280c07d0f0140350208101c40800c110700401d08205025521926121200708503010300078a501c0c6071450324402d070741c440810b4000509541c04950700c4000b5140415554420028000112089001c00c0c000304515103200c1d0107000419001600750742d4881c4d41d0340351a040849581140c0c1c8000044007680501000301482504524090364500b42d00640c6d034102d00d244000254454072403c0070400c3c507425401c00480790b003210201840c00300d094a00391800311400d5240103110281c402d080c011008145840c1076906400514842c6010f00ca62075401c0c5401001c0c440f01c94 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 849480431 1250 849479181 849479203
    0x412050a0204050c13210b13120203090d031d03030f0d05010e0f0a020c0c030d170124050d0902090f0a0b0312041505040308030a05090f030a050a051c0f0b0102 70
    0x482804503d200b640c00c15a01c001b00d401800e641d00408120001c28800083c8070207001e03200c50144410019a125942090108035101e54031070600100c84c1c180c100d84074003d40208951014602c00ca44020a101d45040c0170303460a25a05507144400d42c1e4002480c5900c00507484002c18070110743c0c075030380d003400e841028010110703101c1c10101b43c03900c9468800d078414024100c803891a13010640c504201400c20143c0114400501110211080003401a240015107078250b4001d0040c6400070640306210320005500200c803043d10b45541e52003440a0f10150000703070203401d84a54030982d07a409a03480c80d44042c0a40307403080785122030742400c41000d01521191403040380264021000510032015031421a011100300d0404481008003020381207401d03219541c009002c490000c01403191110956112502948940c0121003580d5003007641a41c0303900500c210180400c4040c400e0a11050107880280035201100014019021005640600701c0d54941c45020340741e651541403618039601049508545 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 849481681 1250 849480431 849480451
    0x80f0f010e03030106110309030114091b060304022404031109010603020a08041b090e030901020f070305030d0c11190309120c09110f03010e040309090603050c0409080412050a020405 80
    0x301d425040c0d19528030040c841c840c200700c4030484c4201508000e00603515084002402071000300150010401ca0b8402550100d9450280d0703001040e0042804601d1403860300c2c054021420350340c80d07800b0071450010a0161810740d04100c800081313528614170041025620510145041c070600c5000e20600310b50581190b07061501c100022a0300c10382041d00141d20550000816142090104180a05040c95400026124248007607200500c0010002e00150031017a800c035007048940c54800365880c4010304c00540030303410400110785502500d070007030807100a01d400c0540001e01c4103500903161000c5480c80300c00c1c190480c0c904d24105a0311101e907030003c01a881404031850706903162010110b80394803c51304866a40c820685070710040304140c07041141c1458200c3d84a680d83d1941040d124002c403000c80014001d620301160209a40c8510000c0c1d0342c2020040c803a8504490a200043c000081c0c25201102c09000c0020b408000009200c64240f140015044440c00b40c8140404e40700080d114404c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 849482931 1250 849481681 849481691
    0x4020d17030915071b030320030430030c030b270f10060e1c140f19140c12010606020f030406140d0b090703090b06101d0111010204080f0f01 62
    0x210361121a0013011103203a40c0303178948205185005d0b4000c00c11a241c1c08603028100802c4081a00c80c04040c0d44918000c40000460003100c000300d0f06c001403e0448011a461041e0001e13911601c84d034094804000070b414006505444e00c400940d60b000b01e18403520138550443c80b2038024003001a0090f40004c0302425110703160501c0f94144100000c2400350ba07080251368a4040c1a6543e4980e01c180c02200c2520b20703400c0d040440c18406140c0d002c0c1c0d04400024405d188100ea0110b0002a01c10710302c0e01c2c0d1601c0c0c1800ca5290359209904041c00030403004240c411000c228045a0310380d2103008400040a0000603818a0440040d0500c0340b101c8080c0c0c1c3d40c0c0c00a1100b017100d0380c2c2082c003c17a00180c0c1403586641d80c502d02d0107218028900043c074560042543c10811207800e0709a07000d15500f50090000c10410b644a100700200d0600c0c1490084c002140d6000c10b01400240f038100030302c4601e0504064011000e041c80305400c903042030b88044110740c4501d40c440745202060051051032aa202c0080c08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 849484181 1250 849482931 849482941
    0x7030c080105060313060b060d1b05040b090607050a0501110406091a0a0e0607060207050102070b010b07120f0201020c0a1b0b210606120403030603060e01021e0304020d17030915 78
    0x255404005e040c90302d080407807000c090800210b6480304003c14001800036407591120500d05e0010280041c50301303031256448000c2036445009209450840c7d1802c4a00c5241c03220200500c021a00b000404036058801c42008400103242800303851a24858492801d445910346a801060501c080d40001850b8013400884407480c001c0c0d03021a4510001400c04561883c0c01101060461003185006040c0d03d10108036141001010340007000e2031809040703640700c41d1742ca4180d080d0b51840b820304001d11400740c0020041d10f180c0560845000018240001401c21080060303003800c3c906940d2086405070380d11a40014142c90301d45140001d09100900301d0300388400c0503002c0c0061241c540700c0d42020841031380001c8081e07403250103d44166000a1413641d036803c2915018000e0030340c1c1e0000b16005030501a148141e020140700303a8260020b10400200000d44001d1100038a5001500c180e80000e03040c4100004504071400310304020200e135101565074508807000a04010b2190684510352502405100e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 849485431 1250 849484181 849484189
    0x92d0b0d06020310080d02031306090501051801020c040908041532070606030503090321090915060705030a1e1706120f07031428171207030c080105 65
    0x428664040001a5244c41d13248a440014140c3e50158a45100385a21000c074203902201a0030156100385400034003545951040e5000e02d0301c1c1c02624006141800440304040030b51184801001040c010307103403110001004a0196a00c3c80d005403a0290300060400842c8031b40090104945101d1074020400d4042062400160103020045001d2481185034910f020700c21208031a1aa90320080403c155580c910304181c5a80004404900c01c0c05407184100d800f030540300c50320004062013080d241c50003004404020f138a95000c0c0034004190700c2c40700c440e0f146483c1c0400628006000d6402184c603100d2540300103208070045089038143c2072a40d201005d5403a000014a25a904040742040e41a640d0b000410b5a0881c0101c8601e801d110340980514070000c08900e11050f240030322000d0192081030089165100c4080d01905c4002c030700c030150400e554881500c000303c00c41c4117030440050700c00c00c0c44030756405070005180044144241001d0040107501440780c5000d4020740e05007016203605d030000003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 849486681 1250 849485431 849485449
    0x6010e16210c0e0315190e0a030905030105100609170709060305060402090717011401110d08100e010f05150d02041e0e04121d0a030803012c010b13092d0b 68
    0x2406e401c8070120300c03200701150150807280d0518203c000322412103645050040c560b6140c1d10407a4040c0d480c21010440d141d40300b045000940d000354586001c2c0b5072500030104642e06004028204900545602160301a4580a200700941c0203000421441c01d260041000b05100600b4100901107400710b01485078040701000e504441c40f202540d290100303140b00584607110544011078650141c01c200e00310041d084a802c0340510703141810084940e0f22548074690086080c0600c4040800c05031040242d8546221170904640003000c6480c02c200351610713244c05076081504103100c0c1d40581890343d22409007d407178000050084080d08440788c1800d803100302041c6807805010b000c001d80f02022009182c0341100b000008680076200c801c03101d0f540d04007800660428000e0a1400c1100c403031302182c3c0b00701901140d4440758140c100303441603480c00000440590024140f040244407641000621441c07074441c06600000e41c10900e1559180181e0407110703847c80500721070343d403803234000420b902d07031941201c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 849487931 1250 849486681 849486691
    0xa0e0f0a060e1b040929093c03040f030b0106030b0402040605031f15030608010c050c070611010914010e0d021b09041106161406010e16210c0e0315 65
    0x3000501c0f560034144503590711501c0304210840c91b00f0345884003c909059001c14410004641920f02d60f010100242c004400b10b00e00811400d8510360540115181030100c0e443c010140e84112880c00390368120201c02c80d0b21541c8161240e02c0b640d00104501501406600d44140e400c4070118500f5061010103003a60001800d00c0d05c5a00460300002803801c2500c7c2c1900c041d203900700c11000e0600f82d4180c02000b0306a00d0140b05015401d000305044520700840c2621014205c000180c020036041a0046411440a481d1014259240c485a034042101136034000011400c010012411101c040640361900c0003290780704086612040c0d101c80180b42424545121840407210710f0711644903818101d561070004205140d02c03040015008140c0510b42c1060401d00d4800d040c04a0b5005080300c42c2510f41809201e0718119104031000502070040d9001d4050502d19182001c01e002c5420410f20b4003e028103440d0980b6595844144104190b080009011110b00845c014440d0403126441b1600c0f03c480030342 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 849489181 1250 849487931 849487939
    0x506221b03060e0d0e0a15080903190c020f010804030801090209060702090133020601050904020612010b0a031118120a15051006080417030a0e0f0a060e1b 68
    0x3030018208049014118000c580128090014490365110151203d00c05402903010900700b0880740800d04103034643e1000c4682080802024280120702901c400301c0061208200d07020401028007400d5562001d2881d444490703540c0900c0c4a10361040c030910443c42c0c0b000605000f412010000001e03403051306c140c1915205000582c41c0c042202c089985400350404c001e5100c140e550011a40492000801c00f8101d000401502150240204440c152000e4104d0750016041040180035506148407815001480a0100e0786404550700c44c11503a25800e030013080c9540360000300303514100e07803501921a03e0a402501c446c81c04e900e6809040a0711410040d00313002d120f00781d1111186c01c1b03060140e06003942d0807070030b00099504025001c0005210403543c6464003c03a511010511502c1282c0c0588907940c413150741443c02c65204c140c0c0950750001000448101d0b15110800e05603c3d003800129010026035004040c100241d150800648006800d540c0f00c1e9448205860441c010701d4a0301600d01c1000d072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 849490431 1250 849489181 849489203
    0x6050310031b030c0e09060c131e090207030306090c032d0e10061a0702011209050c0312181f0c081912051b040e0c12070804050622 58
    0x104030030407004410342c005412201c3e130700c8000503030b81c801d034540521075001c290607103080d81c3d1059229403d0b8042d11a54620101c0c56082c14420300d800b04016a0310702d103070f44905000c0315a540c01c040e0103030780c00104203c0010351188801c101c2e2946c28098041d509c21182024400350490200d5005e076039502d40d488500e400c03410320b6000e60b03140641d40903102e102c1c00d000958100985801c8028050003180c410080c480d103042007404200b1035444251500303070b0360503940c01038407102114442d00541111030003a5614020011007204070742e001c11143e0700c21600104069200e0b0001000c02466454064001c5d004850075440405950303002003040021700ca4500b0104801015420300040358007481d0b40241030300c01070880304280107801c60307102070034840e01000602561303071449061114442d46042038006c2030b0b000d1005110404100c651180d00c44040300005041c41c0c69440c410354582401c3d9264004520400240300a005e014465030341d00800303003141e0346c2c0914222403080f06044294100070340004071032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 849491681 1250 849490431 849490463
    0x40603092f040f1b0c1202070605030f0411040c0c020a0f03030c0b0705040905151009060504090b03010e060a1d030a051c0e100203012904090e12071505010605031003 73
    0x690101031303110003840000140c0844c204e40a40500e001e00815600380e80e40d00180d2031418030015001042d145a552018195207807041310780c1c403904005d0070445001c04468001c140300c0e11030b40708481c9045015619440b40d80010b0050005040c10350b00301e40341090310100c1c10300220350040c00d10041c059012001074801d507100c110032607840c0110b400190416041505110001c2c210341001c907000c04080b00c0740440644003074003c0d14280614070404020440c00c1c08100b10341176540d80300705264000a0001b183c0300703003058036a80c20b16004071030b4403800706d0b500c01e826500f6101030402e4402c0000303624029031a00c02c100700c0181640c054140410601212404038280064454100c10140f035020400c40305a02c01095040029400900410040128004114089074583c409000f007414030180c41500e03040c20b00d804440a80790000140881d441083c20b060280d083c50b0b80101036190040e090391030b031b419612098609031a0103a0012003046024001c0c01001c45035081000704803503000c442f170004920340b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 849492931 1250 849491681 849491711
    0xc050705091e0702060402010806030a0c03020f03030d05090102030711070f050616200108150d0f0303020f0a020c0907090e270f03033114010b06040603092f04 70
    0x141011104042841801d010f0203d07000520075010750300c00d882e48013440e954982859070740c804405000d050040e00e941d080025040c80d080c00c0c90f402c1e00c081d0960b1702c4c21011b401401d041e580d0070b45420401c2ea60000800684551000c5c4802021100901524140b0726111002c0c0c00000240540d40c46401d0024140504410094062010a41c0084032071002840341d2000ca50b00e21030b000325076002c6811500083c1c2041130303505010301079260080444548156544035554094800c1c08110700f4150308000c070b44100150440a0103031001a0780c005c06035004100b0900c50300d110003800348000e008003800c00b400b11301514003800d0350002104c1d56580b42c014960031461604c03505800e001066000d1114680c52091000c40114418072010081400c044400030308a40c1100d00784290101d0908660020740000d84420304030340700014148004108001400001a5668000d50005011a68403010b880c100b055440d00300d1460b41d6680c00c4c0c9866021003905c00c2c3c200340d003d003082607c41e96440c10040c0e84c00368 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 849494181 1250 849492931 849492961
    0x80304170c0406031a060616110d050604151b0807030e100606030f1107020d0206220e01080d022e0f020c070314160e07050d090615060c05070509 64
    0x1030051044541c3c1e0304080b40e1105506170485096084140041c0050602204462100103640111506052583c4440d20040105556154403480389101040401c0e0108400c0f40214001c01c0a20464610010011308036000010613000b4031034000703100f40b030080c0c01880e1300b640074019080126103040755100090800c13602c0b29500200320f113030610115149925a0201c00184030b44074040000840070301c4a4a9140076214009601c0502003075640300600b00328010b000044c04900c121120206d6a040a80094035943c1180d41c18800d500010080d0020803c41c030030010800d40094015628501001903140c000003130000e08800c0d0521300c071a0201c402ea481150761405815085488909000e021500d03200079110560744140703140e12070320131248041664044842c0805020945034500100c403078080c0c20040c900e9040c0b00060010154061050140c5002c561050200040400500d000402440100d4001c40100a006039000b00082c100089010076503004543d9061603039207424059160907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 849495431 1250 849494181 849494203
    0x3030804060f0c1d04020405031b0a1203080601030f0c08061005040509040503040f060801061b0303060b0c01050610110303150d1703152e20060f06040608030417 71
    0x161409080e4030702d056001d130b10007100c4800e00c81003a2400c5200c0081000303074010790042c01e45c503030809540b00c480c05011a5424000020140507003006694070701d801100d418080c4410f80c003103213402d01000300d00e40c0d0512034100768160f400030402114080c04001003407604000c201c0307070044e0581840e41981e46e0080303042e58014103005003801b840d4542403505075180d8019103d20003a00903525804a0790900440711103050303500507940d04101807000044450700030000c00c02901410703039984001c10301081b49070050028100f6600042a02d04150040c0800c1d41080c2e80c07250100000003c40c48042000401102d41000000c0d00b048540c022600c005840210454401040c012003d4142200c0d804030101030f500c0340550801c403c241c80201000c2c13110191240c07455000c05111000800072000c01c41d1001d54002046143c9a10f0014002c044121103469001e8090b030f555020030204156482140c1ca001e0740207000b038600303012162410705038540d240664080c108084c2452040d41c2a60310007006602105 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 849496681 1250 849495431 849495461
    0x9150a0c0f1b08030c06091f0216021543050c060a09030606120f0201050d0920090105034909081e030307030c0c06050f010501080906010f0303080406 66
    0x503c1e501d0440640e0380e445602811200d0084500050a1200110701c035140c2201040ca403030707098009501440d0096100c01c01511010f10080300290158031021070a0400700c4041c40696a0356007044400c800c01c0364106014903161801c490011a4007a0000d80c1c0040c800b000c619240116074103262181c201050442c0054100c040413941c884080d80c020311810481e801210200034580c0c943c00d0755041644d0801000e0200a24030500d080194411300003031904d1020b5190002e0017400c1c0e07660308807a1480504039114118050445a80d041ca001020b071401000704600521205d80c0c40b00141c100c3d004078281104400d6954414105201d595803104205c00f002d004640701c038402610b0010b4124074039405080c85034802c00e00000c0d11840c02c094520685281140294196512503030110f001d0209260440204082c01c80c6a0700018414026180145020120010150b0601c80010003088000704820842e174001c10040021603881a5130909030381c0c0502d012112a0307518140003010706204004d0b003100b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 849497931 1250 849496681 849496733
    0x5090c150d1b090f030f031d13020c070503150408371d09160e15040509100f060509060c0a2a030506010506070203010e06090309150a0c0f 61
    0x2140c60500b40115101d400d03101d41c61543d880b804242000740580c00024210101d082140303010074042d014030b2070340701a24031410001044800200b030142c4141c03810101c1345074020034600880e0302c060000030090601580203012002013440c4480a104010b040503080c444005404c050207964407580c859842c0160070b12110807240c500d081030008648801e1791000884000d031000301d80c5512040c0c108581da005000440a495801000b0351060300d0450542c2401141c007503082b1203448075680d42030310301e8805007286d4907070703280030280000210010084250440d444400b8801603012070501800d8844526042c4d468081e10030100d078040c400c00c17500b44007a110b100c0704001000302182c0ca5000b048281003518044a00904603605001130354040104207400800051066080403c0a03002c41800100041080010084034906001041c1c8070300c48070380c20008182d1103a007031503184840326041c03140f0140d1510303c45800c010f151502c502c1c801841203a4007008001030050100640d06014406084001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 849499181 1250 849497931 849497951
    0x30f0b0604050a050112030e03011b0c1a01051507150e030903070915060309150e0f06161b0204061e03140c2220031905090c150d 57
    0x2100604560841c461070400340021031210311402142d0496414440c1d06c0108942c030342e000c0c0c3d0804e01c00011350307030550f42c0c810b90344c00801503182200124032501d1b168501c400b0482d08000103210b0411b940c84c072604032408010880c1d51902d10240d240d40d03080190301a11403c5510300380301148400e40c0c10031401410f020301c07406440f1021008200c815011404c076100700d035036100b1103015159200041448541016010428a8003940002580520940c3d00212280340c980b082011500500e10100302c039171000d03159000410040014a406c400d00941c4045402c0e500c0030000d00415210710004030307810110030441c00f192201d810220182401d0154a1244080c04542c0200800248429140118008880e031b100d0040800c1c88051450050311100c250502d2212480b2146050400191a580c0c5d811280403164458402003e00f02404504155207042240e0041d034038803012450020100d1420042c4541c5000c0001d01d4007028000381d450a00084004801c58943d004034501c034000e090528038020b07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 849500431 1250 849499181 849499193
    0x903090a0f0e0907050a090f020c0d020607080c04081e1f051b090a0b0304080f0301060801032f130609050a0203041406070804020d080d150503060a020f09100306030f 73
    0xd415990310b60480e00c11a40ca03000c1540e51402c03503100b0581c02c0000030400740484245e039000008203901c403a102600c0c0000f4960700525082c15a844400103230052030520400681c00403140b0340041d00d000c403480c205402d05501544440d401e00d10311152820700145a200e8041c14840044d0f20100111800d001c42c0d92902e543d006481304a0301400680380341c180b00c044180b1040f003a07444109028000e04030090800041c0fa055a0020b04150f900349414814801ca0700b0342d004c0218080d19043d5900501545107290565030629984600b84060194050b5035122500701441008060f034211900d1a00080c0780141100400b40354005413011401c02040027007203040c7c0d400031802148a026038140b2041c107440ca046e01e030002074505600040d08100810054a849203400820601800884c1e00d0003400e110308100311005003440e1a01010081010005494144401540300401c0c100551900f0b080d51081d08882c410038084910442070514603044003031103607009070055640320802c094030703c0070380c1450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 849501681 1250 849500431 849500459
    0x1501090503150a1b02190204061e0303081b070609030e03030a030b12010b011407030509220f021e0d06030b0f160915080a0f05010914010509090c090903090a 69
    0x40d9446034100380f904d1142e40119000c4a400f0f0803580e010703041d8401e54044012800324182d500740ea016840354008115207003e483d0480e820f03060800c042c407150389145400341c034500000700106040540348014940034228181200e00e02c5a10400014032444039180075102182180502c40d0140320214018030040c1e0558802d08051404a4a542d002e42c8850007640c280c0700f40b09102c0717000581c01450030b41c00c03450030300140454a11074208681003e2354800441d400b1100180d42d800807030400080c0703989903411880f4a01c100c0610320000d51034440855041c042450060344500340441001135140c036041013650205001c0c1d6070102000700c450515545002580400382e800313980054091030503003c824091402c09088494105c040c80d80e0142035601075445076801060400200d0711607503000011001403143c41c0c043e0500190010341040d031003180355108241600024051811030307092242d0048c1c00038000c14044021034075840d0940e92501894154090344804940005d5001c1010860400700241c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 849502931 1250 849501681 849501691
    0x60a080618010605100525050a03050306130e070b090d0803070e092a071e0302060126060f071e02030910030203060d020f010201091b0302180906150109050315 70
    0x1c3c00700548450030040c00000e00c51010010540402096110406402d0b000e104540d40c441c4824440a0310f45070b0b14104240c1e200218002000003003041400c0c07a180304100101c0c403403000200078110304102ea03155245414043d40e86400000700f6031140e04d590709107180d103403d41d103c41e500c0d880c0e0425030310103071941842c160140e02c5841d006001601c512206450070540c510001d11140490b0100f0280308a02d038400740058403084821034851ba009040202500f0805202e5030086c00d582d0324010a0502da801d844811030803c46d900151046480d50000c1d015412101d140c82e4040540c0300d000064612040707152081501110b041031a042031900403011341600701d0192820b40302440f40c01c40803022031008481e065444034036105240c0c05418031105084030058103000003d04111240c8507010b4540500380c2e51242c010194a0500c06c50400102c00680c1c8040540320014034184540402d4580354003c00d800c41802041008020b280c2c440e0101d80003e0038050182d4040c0066a110440046400c4030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 849504181 1250 849502931 849502933
    0x30e030d02122d0103020d170c211303110103020c120913050106020a0b06060d0f020715020c060112080d0203040506060f100f2106080a1a01030b0f060a080618 70
    0x180c0d540d04407003050f002c0d000700101426966090b038210703400c1140414450b2002d44000079a021800c4071880400020107103a05050010035a89030540c103044081c030740c52040000080001e010080005001c1407592080d2540b0441500c3d0300914940102d0003402001c0580e903a40c800d6403450700c101c4054000078070340300405592510002034404038140556101380320720741c01030f0b0003200c50101042444c50302c1038101c0b5001f0200d43c0b4201c4484000303426206101000242668000340c01c0040240c240300301500075000d2902581018062001c0c2a2140c83c1485540488500f40a08400b0841d0140464010300f011010842d12414141460343e9152411904580036111000d9542c4040c035114089501d0380403556601422590200d80c101d6a1002c15159074150080c01c004405410250b801400054080f0340024580f956007070404921514208002c0d10a03030f0568001480070941144400d680845400942c015a803a80408103042100300d0b0b21410b500e020303480510480ca41d120381300c58501d8130048 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 849505431 1250 849504181 849504211
    0x12032001020f0a0815060703030218030706350708130f11010305090c031207050703050f0d39140601060905030d030e0d030e0a0507030305070606080109030e01030e030d0212 76
    0x100001d20705c1c49540052650020040c0700c0f07900041d109400910344000e8480c8126500d20108003c6841c3c01600d400440102d88220035508440c24101c401c400e414548100f02d0322420f25020000d8070070400a040e0400300004240020407082e0b040a0013502c1940c00900004030f07004c00c0c00d104400b141d200710b4060019007090049000c500b40050301d210500030040142204440300e08925543d503001c000112206d0140d9a800400326400b072200c50305200c0084040c2c0f940320030f84800109420704802c582e015581c012100480051070711540d040391684514a0701ca100c049504002e454a80031300c3d079020f000d22480b000441d0965004d0a010101c0c1c109400312072400c42e8004068098400e5821800f4855100e1751285480c107200785c0202038050a054203071040e900180e103440d41480866001a4003050001a1140412034280300e01c41c003c4c030710302d4003c1049050b130f81d41c0100140d40085840d810142c8526240135800801d2048030034031511001c0c11980c80b02045415003100c0310849040207003040361 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 849506681 1250 849505431 849505441
    0x18061b3a1b200a140f01052a100b0108010303080c070201050705250801020c0303151210020a08070e010c0b07090807120c08030702011205040302120313061512032001020f0a08 77
    0x59043c84990b00d000b028070305c15130001e00044465400400b0108070900b1000c01d4008001506111780303a440440f00041c100206040041b1b500f524180c140c02030401c40600010004658000d80264200040702001a900e4aa50004035584d014030365025201e40a000d01003603900f110716041030705000b0003d1920b25082c0c0c0c0d0303010f028200d00850003080e08036002000007910700d913018442c071894041d004100c8148581c0e2030380202c1c944081b022060148540c0026044103654101440540c131542c5817401403c18400c0b20f000030081104a0700c0204402c03c0352000c00c0c032107400764841e68058a03424044070300155035a1088005100141c0c0242c0304007030018000305a0304001300803102c0031501a140e0030174003903000003c42c0040c01d00400940442c01050b129000c1240304100441c0100c510544180210341c280c00c204048603400c640c0c04119090009040141c1e0828021080201750141804035680220161188981d0a4543c0c40c50040d40700040340c1044c0704404020b0060302d82c80b680c82451503512 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 849507931 1250 849506681 849506699
    0x1309120908030d020c150f0403031503020d0b04030c1b05090c12070c060b0a0b030a0c020601030302101a09040506011502010b01020318061b3a1b200a 66
    0xc0c60092046641041010b545100c0d5103800400348000d5480880340e1914000107010700001043d0794a40c110b43c0314100344005c1c980c0c14007807030020b1501074060440d0760345075600103045000e0500005091400c0000000e082c14010f001c5c51103140e4002c0e01034690120242103030400c8007014007403d4460320f80400840c00c0070101c0d000351820340000388074892160b00c5506095509403102e2800f203072980e8942d5441d040702d841d0885d079403005060303540946d5102c3c20000307510b106480080003210115409100104040ba90000e050700d14420352400c0055038100d81d8402c40542840c248980da0030620300810701080281c00501d00381241c1441a1441e10a011154100d00361442c04c111130740164018003403040c040c140d02008410650008151038170300300e041c2890000104c0d6001103140603802c00303e0000b54108400241e0140c1c0c54103450300c110003d1083d152144541c000c00000d10800000ca505126034180707901d0035150039504105041c0c080350111040110490800503028024034141e000020980a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 849509181 1250 849507931 849507947
    0x6041e06150f050c0a020d2a091139010608030c070f060903021909051e090a080d051e0a0b0301110307080411012007030204060e0c0412050309130912 66
    0x13507003026000c1e10b54a60204208030000b8903007502d03400091040265000503003280802600044400748805920b040610f40c116500982e50000a940800954081014129500341c4404051284e141c00c100a01c40003080303030401070003005040d0703e0242e01040d00c00002001c0d210300c140c20400c03a207400c0d0310f41a1140b51000c4511501c03000c1038a8100c14401468a90b8982d1a90f23902b840000802c95620982d94040d10002c1e03442e203020004d94901044901c03103840002c0d9001491400415880071903550340b0700248903501c0307052205551680810031214802c9880880d1102c0c00c0098000e07401c10106110080500095082c840c0d03103446103e14640065400740c1c0d105400c580c441d8049030340c40e40c647d510303203c03034481d4094108461001d030800e000302ca52218841c4215680f00030440725066105002c119903560b0000451010000100720400700d50300111819100180020044176a4030f14102d4550b0081c030040d90f6001900030006c8684882550105c88414002c1d82c001c403503402020400c2e81c1401b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 849510431 1250 849509181 849509197
    0x61a121005010807110102120708161107050607020307080111040906051c03030e0708060109060602190819020a020a090b010e12060109150503010501080102090a140906041e06150f05 80
    0x1e4800000928007400358000309408517001d4009407500d50120005c00c10403c049900c980032a40784803e000d041240c900b1107602010309410120265802c014017181d0700c0e00c00707100b03862080d040054820300b1510280080c000520790f80d002844401e407203549003d51500a070044002852034550b0020b03803440c2c070003a08080401c103a0856038540e04a034070218040c3c54405405007603441a00070000e4441c50800546001b400d0455001a815007070450090600c8051550352440c5110f007090380c00807a40c10b108481400c6081074105002c074008004c140d0400041003000795000080d80d400151010487d000300b1324842d0240d84100c41c4c40500010002034132245001079400c0e6110000600140340c0c40da008081040480c0310007412203a8a400190956001360000c510030f940111b055000c504200000c400507146000d2074036001740c2c5003400b03d12a5640188068411500d40b4034182c03100d040c04500d140034080005080c0104c4d42c560480c01c5808490b14a030307600203050240c1c1800f1261044041d20042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 849511681 1250 849510431 849510437
    0x181c021f110d0209180a05090c010c0c0512070b0a2a030e040b0102120304060b0108060907051e0405040e01062903010902071109040c060210020a05030712061a12100501 74
    0x10002d07020307281000f5040181e0b0580c1007000001507000c4080003201a920402d00c50401180314500b155005d401c10884282c0503042c010042800310018064040d8142a41c409948440d038008602428900d0b00341c0700c8d40316040c104400906604c041ea0700100c41e60184010410f141c070109000c910704079481c040c00e10040c1c0000e0103e0200c014520303250704403070301c11501441202c4031543c20050342c000c2503005807012185a580c0304007942855801240d070544c885030458105003a1710f05040d0182186c400c2000310701d421251103d42c1500700601c60152800380a0180007006010440300b41a4002c2410340520b2016007480d81e200190040907035918950034081d0a103080c20359203000141d0020307401c060320446e041541e1034440510750300c5900400e07104902550351800300e2450b1a1011742010300042c0341031062070040100341d4009820104480c1c0107409441c00e550014060450f50006100d903070400100e6441240045d84104081c074080c8c104030794440c3c0150843d032107040924400400307900c101404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 849512931 1250 849511681 849511687
    0xb090609010f052a0709060e0408030405012315090c040612090b0c0706050901150302091302030d1809090f2009010b04080f06010e181c021f11 63
    0x5035500c100c1d0a00d49114480c00e010b0b040c1424000303d0003042440c0c2806000301c00300c0c2440f401c0850340400c821001085524010007455040c24042c2225580050003c1d2039841c001011508108003580314024000402124031140c9200a4100c0c1078a4801d4500310003018107880c10845c28600104918010002103286616183c43d140782615102c0c050784060242d0369841c1605004036400d050124820708080d80d041d42d4034000c03403804000311080501901610307854100d100070205082c2c41c0b084296501103440c00c0c400e039980d450349041031401c03520094040c01050040805180c0281409a0030051421a0114607441d6403560048681d1410054400d4040610704001700b815040d003520740314105a0011045201d000114420103821f87c4190fa803190001400c1085640600c907031000c60035184060510303035141c14010340308824050b0200200e2010150340c4130301e4480400c10034459034030801281451040c103150107503c8415659072038a0420001c0002074190000c1e11868002100d5041c2840c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 849514181 1250 849512931 849512947
    0x50709050d05031b01021b0d0c0816050a03110f0c061213080f0405090a050402030616020f0a0c1703210612060406050403110a050a0f061d0c0a0b0906 66
    0x10040d8241d03030291034900041066005410414030925041c040100c000740e556400054000101907085800c4007180c0c00030209050101d5000c2150351013180c1240001c0d0f11000902c1059100e801c144200a2030f070721400d8640300c04c054129100c3c40f148038112059500b124542d0511a40707071042508016800702d810080c5455140e000f08110350881e85104146007045201e540c4d03082d465001c865440c90202000c00c0800841c0741c40c24140e82c0c0080e0040c000c1c0a032b81490b901003036484d800a4460a849403001c1c0c1240e80d114400c110032047d40341c102040310407811907030519858181c240e000f10481250561002d240000b0000212a01004400b01d00003e81108408400b8110380c080c0140b5031003220030008414030395041060f0340c0210700500e0000f80c0b0782803500c2c2c0504a203030b81c811400781642000c0e8140300070440114011602a0b00302d811144102c1d194944480108070f011010901059041d41340045528000392001d0050426560041003945480750070a0034043c500302176520190070000c00e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 849515431 1250 849514181 849514189
    0x503130c03050a2105160201030c05130e0f1506070303090201120606021015080a02060d0b060301150201110426070801020a12060e070e19030c0e06010806010305070905 74
    0x46a140e0088500c0462180c07280e981d141080300071030041e40c142c0011003d01041c0c0ca548500200005028205540307407802081c078030303c2c180f10984030280c107050307654108959a41c01001111310543d0a80c9007100c0f0240c442007003040400041e40d00407005104000062840c1214078018012400b00514450a0103225070f03084000c5c003203a8000b00c0c10030101e001038011401503030240c0000b62109401902d0b403d034580b144481280d084200c02000008111420055000e0100c0d803004100d0701514041e6030b81c6044035840c0081c101d8001040c1d00000c1c00000013982c0002e000074014520116402400801000c41d031200d002d005601454030708002c90080b80c02000800200f0401c1100311105988019075100505400c9030880c413029130100e1681c101c501144440351140c000580007260002c1c07800d041090000b040c0b0004080d500d030003455600052003594100c01307400c00c020b60344042c00854007a11001e58000c09802603803254003048001022510a602901402c0d00c500c2242c3d1700c40e000649050104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 849516681 1250 849515431 849515461
    0xe1005040b1809040b2203081803040308070c06020d030902060307080a0b131506020106080d200d050a090b0316080601120e060103020a170a02010f0915030e0606030d0503 75
    0x110b480311100404605054a40a890381d10803805840042581d1500c21103824100c0d03104449030721711a1403c0d20b00d000007504956519006401c100707960001c1102c060400386103110350b40028111101c00b080e400f0400c111540c1480c2551541e40c25101c1c0400300102c00d07000d0f81d030402c40003035200703d050000807503051242c042594050241280450070400c414046026604000248102c030f64441c4401c01c0350005c41e440220041519200030000726103000e48858890716225010410028119803140c450104048900012039118094a400d8850b403500508903901c0a508580817071032811000070540264000e9910030f1418110000030719002c9041203440c502d00074500d07814000000528030b40d02410b40304c1e13211400c44020003880554114010040329100a0740890800080310b8a095042c11000c548405a644e0a081003401c0340c40140b81a9000e40040d0086040000259550b003403a55064000d2003107410341c032007500c50589402c8189034840e0310310303404580403030410000f0803201c418109030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 849517931 1250 849516681 849516697
    0xa0507090b011218020f10080a05060a03080409020901030b0402390708061e100b07030c080a021f06060207050910050306272b02010e0d03020a0e1005040b 68
    0x15601031000c000507404131150110300704104000c0b06140300843c108403030b91000e204011103e4406207845d0010080484a0040140710b03480e4075040031503100d4694801079409581d00825142d106c0d070301da0040e90025007041c0b9060340028100f9409181ca0b042c6807084079441d884491181300030b000b51103102200b00d802001d1440e517003014100000c0c0034500c1840860b001e01001c5028203e14102520800c0d075030810303485200c074000620f4043c820680074000301e501c100d60f4a111515102c0242d820705a40c51503203c03034050083c6400060010713250b43c1c049803001880b2442d060383c03500702034503c1504003115151b00680e0050ba000007400c0c04249000e80045038480c0c680609903003100e48034400b082c14410306481c1051300106404113060300700100c8006c5102800d0500003044245c80103203d2401405600315a921a040c110811600300343c07003074101c0c038040320f0ba0030221550b80200d0000200250b00c11a5202d00152040c06280490310b403000143c0c40000346560303400d0500741041e030038420550220302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 849519181 1250 849517931 849517937
    0x1b0608042012030d061a030105031c02011401260f070b070f06020a08040c08010c020a021e18070311040f06030b1804080711060307390b1501020a0507090b01 69
    0xb850203068000c10041440060411020800501d48100521420501400348450340c00503c0140203944001845440700294005c019410780850030059004086411100719883c02c003030008039520800b200c1c0c0c01d0511454203088504040f150103a251100090040350140d500f0554040000c20550700107403c9041c0945c003480203001ca6a0340300c1c1f007260300480b514000314240d1800c0105008049604000a10703541c4000d204440b951075009445450b8004000d02c10780d00200c400103a1100c0d1104c00001c070102900c80f1705581600341c04841501d908480807070002c3e0403d070002020030079800036074003100c5021580c3c449903420100c040d00584111211a03402c84105880c001950b010101c103540030303501907084260f0750400c0f800c140c0000c031802d0010b03600400040045c0400b10b0f512140340500c00c12009094a0000010440200c5501803038565945c0d411190019000307000300744a0090284480c1c0200341d4905644c0c00043e40c4600040030090300b5500859410450180c0d44d400c00094204145 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 849520431 1250 849519181 849519199
    0x51206040b242205070c030504030b0a0f18120302070b0c030a022110050d151a0a081b0f1003110d060602010c020106050103060f180b0d1b06080420 65
    0x20020036002240003203811680b424001000040000610890750069800c6c139042c4030460150b10090890720803840020145c0b190200052000d0646502590061103040c0c01407000d090803100a6841004012099440015280c0250b090704d00034800c590900c2d41c080d4815003581e4441210f0852a0401098200640d1f001c10600303050441c0d40341d605100500000405016051445407001811102d400c2640035450340181c55000c43e020003881e18ad5031141c01e401052000303903410f00d00b00b440c400700f4003990090400307840820303081c00116028640e44444860741c07103102e02c0e403402c021b40c0c00034050403182c105480b00e4521203103901c0f139080000b58604024030039141c08080040c4034112030155000c000141d64415151030000e50a00804000700804d103424080281050308105141c1e2451185040e011914022180b910600e42c10000070901c0080200105022604200f010384c0100240040040b03203418011400d580140c0b03a45000c0c2da041200c00d503074950070f250f4513800e40f00b03071852080c0d001041c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 849521681 1250 849520431 849520501
    0x20d0912021219230a021e120d1d1b010305090c01051210051903051608030301150c1a180706050904020c0c121b010503012d0306020f0301051206040b 66
    0xc03c000f000228440c0d80108040c0c2c41c418000c0358083d41e001c40088041d0400441c0c40301043c800c8089e10180c150741c0340c00150780c0b0a206000ca450256400070600f840c05039200d80320700740c181174040320f00d0b02500303803030600059442c04110303a11030708018802c9000c904184402c1c3d100b203800788804c41d808103254440342c01c49506c420002d00601c0c001200343c401c581e2907010910802c6424000c034100321071074510901c00181050302080c0c80c4e000500404c03c0300c0403c1c0d11403803591449840c2110700a03801c107403c0610058000b000364003041044580c45092204983c066201d440c001030903c00301d488903034031780e4100480f0310104000b07075008d200801c169106012150060b5544e4140030203812550200402c0300030003100841c4c0c80c40c0d09113403000b410303c80140010402c049132040d150740b5041581070309041c401d003100ea07004042c28440e00081d110900c0805d03003070841100f000080d4140c607011501c40f04d948014880469684030304072401400800030601003094070106c0030b295484452500281c0c043c400351 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 849522931 1250 849521681 849521747
    0x40804030b0c180607050d0f1202041502070503061003060b04110307020c030c1002030f22060c0606150e04050601050d0e07051e030a0312020d0912021219 68
    0x4240e0705440c5a480000743c0c42c8105442140028550380c090303030711505101090306c0c0c180d15842400700070003c1c8021212105c5a06114082c81055900301c101c4c1151038540f07402590603650460065000540f2441c00042514980080c45622900d40d803c01c0140c0c140c2195103480140c020b20385072907000340e210b0480030600200703800918442d540c1c1d40e006110805d0340d0001c25181c900c107030000324054a0020700100c48c5c1680402141c0c00d003507a141c003043c0d0340c460f86111414444c00d07610f00c005c0c0003020038202041c8507074810045440701e405914240605900c27262000600d88500800c01c002c0b820700c513a0b410050401d900701a03030000c0305041c0345040802daa407402094400101c100c400340e4000132401e2000746401d01c40c1d020400208604180802260404a640c42500c50b01c06424455240c03000c0c60400c5244d011074140300180d20f0188000659403501013401030410b403c0c0c20260003100320309a2818031140640303a003581c694000c4111202e0b0300c0400d444000c81140780d03260320b19581c400d00b060148 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 849524181 1250 849522931 849522953
    0x5090d0e0319030302030f01090b030304030b1807031401050a050f0103260310051903020f060313020a06050c0607030507021f09140c0a060c02030a230105010e01211a04080403 77
    0x3c065100940e807840c0c220072070500510160849180d681c581800c070060394400101340c8083d02d502107142e0845440307913070002030305021101000740c06201d1004044204000c41c0c2c0001546280540207101946640100f18250340c0200ca000124a040c08010804525104818902480301100d606070030441070360740070b415070700852b0451400320b08001c04001e581840916807101c0b00b4803010840859046600141c0c6480c0e100d04aa40315503404130201e02201c07400203044210340d9000b00754400075039407124050116041101800860b00416001414031800703405520b00c1511564050080070005141c469141d040e65804000340b680e6410182000406039000303154824100001400da040000c13082002d21041d54108104010047da080c80060300c000031443c031000e61040f000e501c0a0305010b80552508100c0142d000958280342c00064081d4150305414107950010030410201602000c46201210741b44000400181c01c45010350f03a6403c401e001c20b900688036540151516603240c8500030118 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 849525431 1250 849524181 849524183
    0xd0311120301050a0503030708030609040c080a1101031d060106052a03070203120f030109020d140f060f01050403080f0912030403060516030e150c0f07060e1005090d0e0319 76
    0x314004014429403408107186001008100c4c0110324042d9250380b104e80a00000c0d090030700961042c4042420070040f02c2c1c0050150201c0d03001c80b40d90005908101d50211041500e5a012900d403034115543e81038040c1d079000c60800f404004140342d0f40782440450781648024002128485039a01080d07042c0d20100c4006000c550708002952240658010503040019201000c074040c40d0801a03403400e501914180da0440c0e00c2103200584a80070351081c100605080200c00704001e60340001c1041e0155162940d50244200350f03001100d045806005503103d12541c0009032458001b8800110344900c450000c03d030041c8040c0c203680c042110f40158500d1a0440e42080710f86035259030800480c03c02d40500b203494001186800e001c1d00d020850700d01e84404200140c040caa480000c0001d110409201c110f6010010f08020f6a40e145040c0c1004001045203912140c5140920380700021280210300859008806c080090710507801c01a0054400300040030904d03030940503400581c6003280f2500801004a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 849526681 1250 849525431 849525463
    0x303040f0312060e10170a14120a390b040f0f030504061e1e201b040203060a051905060307030e010f0603170703180303050903120301060206060d0311 66
    0x103090110500e0300e4114981c100c82d8024040340e0106c80484e000144a0101581101444d0900d01c812105e40381480c0103901403984840b00081e00c804520b500058030341ea039609640c24822940112944007882078017404410012016050006011401038500e4680140c803505004400303000c26a01e42d04d108810840a6010a90208080000c3c0b500591610380c070807103001001015000c2c0c00780141400b04503009000d14090001d40019600f8040c0c620541100e07500005c441502072038040c0079a9616685481e040c11656041e1148802d050900079240180380051040c07409608140a02004100c1001d080078400c2c2c410000140903110b1030b0042d40148020358010610341c22990a0300c1c29104884011500d1501e440000c00218a041081c0b140c01c95401002c43c3c0e0b500d800d41012034a1002000c120079918440c19000420503400000a052000e015802c2d07900e5043d103540a41030ba80405d10034000035802281c002075052400c807410f9000c1030700c6400e0601a0005070b104203490710401c0382591100d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 849527931 1250 849526681 849526709
    0x120108010b100e030304170c04050a1b03050f0402090402010219060b040c050703021b0112021210060c15050703020f0703080f0c1c0203071b0b0a05010509090303040f031206 76
    0x450820b41e400c08116181810105071680040001c030b40d4038031952040803a65130b004901007414803018803981e40502002401845941820100880140016006410306030551500c0111043c0a4011341c0c0c41016142d07100720495840b0780078001e844034020412270460080c640300c11029540810f5410f1402d02130200055400f170400309100496a8400ca40801d00005010a0001030340c0042c00c58031b508081540354072500a4080141c0310980032101d68941c05001142e40848181803000d10344c480c075113200c0e5820301c0070b80e5034800750b0300c90258500203401d4188807072416a45103450380010b034000119146c0149084000b58001d07107581c01500c4110001404201403017014140e0503001e0303811641d0151010b10b4005601c58101d50803804400d0f010740e045d0003000044a03d4003d004d0034128070490300050310204000d1400d51000c41084400c4050303d4a070100201c1c19042032504d0398400c08201000794519140c0340c071808804160301c3e0045080201d03003c3c0038080100c9a020741c6000b0715074026444a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 849529181 1250 849527931 849527951
    0xd080f03011202100507110d02010216090905011a0a0911160f120f1d0d0b040b090610030308010b091302040b040602010509010b01020a02011202070b1303201e0312010801 75
    0x980c60b40c4e070040e000030420300340003090208451955409642808464000c071241340c1e0320050b41040f65400382002e200954542c0003c5d0710000d6009a010144200003c000082d000345045403040a600c0c0c800780c00c1042071005104445c0340342d01c5031a01581103414681480141d20400040f2030f094201107420490502180080040740341440740903900e42d040840e910305140c40000e005400c802c540c80303e0038180d1800c000da0f03601c501d10901c141c1c81e001503014407903140c20306118242e031a0a46a03020305100c0e80c800900210031050000c81500e40c1551080026441c019094030306812610006500c0201801d02040b85041440100000c040008805440b41d10380240a401c5590060881600d03904007000855540c1e03001c2405141c051382400c0c4042481c0c03a91761100002c0c007a00c000203002088002c01e00114440c1e07802c1e15400280f0a950b0380c0040c2016400d5001403010041900800303a22100000021800000f02050700340a02030440e070600144031944244440d01707a010406603596001842 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 849530431 1250 849529181 849529189
    0x80a0b091e0f0c09040b0a1a03040506070801030201080f0601121d0c011803020105071a04030c381815250903030e040b0306100f140d020d080f03011202 67
    0x382d4001004900031040303103001500a4003601c18100320034032460740c1c3e81c407540095032100d102e0800f410b006000d82000f4000d0b5480d581095000b0f075419034641c8038180000380014421801281a240d0680d60002c0039182c0140c440c024080180c5035a05000c0420600d00b41109039100e441c0e142d0081459040b102c10840c01c006080841c5414001e040000503200e9244a10540e410041129428600260389544504000342150300d0054151180a560703003d00c4140b43d800342070280c0c1c06000d0036a04103500e030380d90b04c00520b070300303c101018030700c8003084409899200c1c820a1341c55014140650450b0358a4650a02a0400b401c18a4032066680c11a042c040d410300b040c1c03684400b032700d010f1a542d902001100805809038541e844000c040002c1492914013507140c9400c4100350010280840311941841b00c1044a00c414a00030401c1c0b40c4000c2e400000c07240380ea0415442c0000b000750020a030480c0e1070702404a40d100b00c04041d034054904020807000c804c080301c019402440c1d000c16990008130b080c4104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 849531681 1250 849530431 849530491
    0x60b040905100c0e1c0f020d02060c0609070b0a0c030e01050c0d021e0309010507080307120501081e06060d0f06090804080601030302011505010f120621060b03011803080a0b09 77
    0x4d130095448100070f000003d802441500540d801c41040718083c40144000f07101d400c5c000e90005e42040b404102c100d84160000303001405104002d0543e2030f06a120841e03070307216010743c1c6000ca0020fa00001c81c000800e00030681503a00d20010b24000385850f41100758140f41c1404043d0807001a4807400340d5400d4000c603512100d02c0c00301590003070b52520280900080c11801010000f1303080c101e001012400182c054500c80b50382103010071043c8100e41c0d503466110340b51981141c24003a813800503000b0301040391002c20b1042c46580014580c181c9000d19850308d801c1203e01e41c4086415640d15020707100424011009000203200035030050105604603e0000e080d680c12400100d081e4803200002c0c85280c0e0000c0c1c0c0c030529a140c1e03250540c00c800c0f100340800301902c4117501640414900b807a807501d005060303a49410b038081c02041c00b404004a07240606080310003c80c401c24611108496202c0002c4c070400c07803660001529040841d0400c012000a030b07010100303603001012580560700e800e21040300c0200c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 849532931 1250 849531681 849531707
    0x613030806060c0d181802180a03230307051501061e050d020702060904091b0803041805041b0f050103140f01210c090608070f12060b040905100c 64
    0x12003403c0c407039441c030056a582c01a60404080c42440003080d4201114415500c3c01000c920000000c10501c0e2000d8400a6000400450451800c850440c5042c02c2815031101180d40c054100c5d207528001c0c80c1300c0c0d00305c10162040018103010410908000c154104101c0f078001c0112480c15a143d4589038001d055401891400081041051100d071180c58010b01550134100c4298401360340c407011880025014400c10224543c498a00f040c50b109000100c0c00c48460041000f90001c80c07640c460402030b543e0b006030b104450364201051101c07640034043d42c01241d0403a104550400d40c0301e0150565101d0002650014129480340d0401000150781c103010342041e100078409001c07081c0c00d001483c10405641402084541e0360f098030000b01e45087ca600180d10645c000b0210008240c682c41890007500702441100c06a105045c004240d84082094010854411480400e2410b4135a40c07170750043c10309200c400307501542d00c0c82c0b0361001c50400d10000f100341441400001c1e101740c00c0c0710302400f61050780c1d417 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 849534181 1250 849532931 849532939
    0x6091e18080c0312070f05180a080307050105010f060c02030601030f0606080d0f080f04120c03140f0403060f02040e1504020426060a0b060409020d0624020106090c0509060306040603050613030806 86
    0x102d5242800d40000450360003961107000c58120003123030b00c0441c200004da0781c052a010701c40052414244081988040e05a4408022035800d050355800f0443d1500d0b0682d20180d80340e00513500400003e0392a6a1400000b0b10406000c20441e5844800d02d08214602003401d01180c101c04000801e15030000c4901e600110440d80c21360103080c103840e44210b907110b02440d42c007444001c21503c8181405400701c1c496280c6050003656442c2a509403800103a00a03100440f1014107020703a03000c0c1c18640b4000d9500343c54010503022011390321101d451203202c02d04e4140641041c1d003048041070b038200341b8442080038440d2440341c08a100c881c45000f450446c0003030140c41d2191400d000400159036060844003102c5c61001c01580f1007d01544032401031010350b01002200d0a4075080e12010f01404078a51070424140d00200310855071088040d05845041d0114000203104000c0100b8901d0100041c60700031602a000040241e22035031100d1403c0d6056401070035600342c10010398100340d40002101d910843c203403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 849535431 1250 849534181 849534197
    0x21303210e0d080703120f0204120209060904050d050d23062404050118080706080906181e1009030e030106050a05130216080d09030306091e18080c031207 68
    0x910b883c50203000341c2c0030060800c94080c1e003a051000c0c2503048410131a1044404550b2183e071401c81e841d400403c0321040b4090708040000586500c0d00f01d041ea403003103400c0400350040c5100e1179811541c41d07000c0d000b00e695081c5d40e02ca0344145c610380381221001c1041c03816076280840c107210f8100147c002c465182c5003440d0b0343d07000c284944a403048094404407202030a00c1554480c5d20045c601c02900d0079000800c251168810025605034408025409580b44000f074171100d864904444d440040c001e5005142c950004070180310142004d00c0c0c03c204104450151001111b520f520f50064400c281401d400080840032404041c0c60284505001004212103644001c1c0c40c040204013034420141c85500c01c0c2e41c0c00f040c03c14141124031004003c40784d00403a09641d8420f203020b0b90f00101040305040d0006860400b001c138801405200b10702403100c3c0303105041d9101012024080241c4101c620942c0750051810001c0e00042c0c10401401400416071701031030300c650010054045074031000b042c2004104041d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 849536681 1250 849535431 849535433
    0x150e01090519030303020a030e03030a14090d0e21011a0a080a020109090b1507050615090705090d140d03060312081014010207051203030603010c21021303210e0d 71
    0x11402c4801c41c2e41c0b6003009178560385414003d43c020300064000440310701000040048000c810351140e400c08040c2030a141580c1c942e10001a502e00341440d096000ca044000e20b1841803925030300031441041e240310740c9981144001211825110700c0352500c101d150785030309200d030b00f0b281c8155180007401410008001c80c3c405900028500d004030322542c90500c0d41c612048085032994200080e2781c10035854216070341c1d602403602d070b640c40c0012261041071075131003141c1050340d01d046200c1500a030842d549660418035520100982c1344003200c005c81b9040c01a281560446a0620074420051110b440010324546141005024420f001403040100801304080103105100e00d1008070548502c03a0342d200300c403400080181e14084454112a9000b100d080413071202810010086103d89001d80c001c0c003040a40f002c0540d01200c1015540c0103808050791000c14100c000d901806404003d0a6011010f07540c076103e203450700307401d05800d00360690001c2e19a0030583d001911180b401f502074845440c04061 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 849537931 1250 849536681 849536719
    0x206090414180607200102040503150f0a11031501090314070314010e070b0c0709180515060f0f011b0501050f090304050d08030a0f111c0209090a0b01020304150e010905 74
    0x82205d03103220b007414200740461183e0003541664054140076080390070020310640344088001c2e040758100f07800f540880016220071600d000e900318800004d000c0e1400d5071280920f071644000c64048150401014400000224500b200e91000012080000c1e280c80d60860900342c0141032000e0250120780e04004069201c03c170002100400c0303400c0c00f20241d032101402c1140c603051120075404a51010300708020110351141e140302080d5018070403000c030380e014020031030301d404030140888905a1200c0900c650144500300304015001d400b0051400c18941d00c42c44c0308003c3d015803400400d940d241c1d503401c00c00800141c160142508140034030011414545010b000440503100e10500400c03d58010001c07404072440c5810040829000350028410f2070420401410342d6000764a51030036420001c1050349082015108840c01018041d040e09002d964a480070341c06040002d1100b030440c0f0040000103046104070072410104034280c3c1d54120080c156030001810f0b445c1d560482882400101c1403da4002c0c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 849539181 1250 849537931 849537947
    0x14030d030b3106090b040c0e0102070501050d09080408061806090706030c0504090507031b0509011e1e03020406030c090509340c060c050c15040206090414180607 71
    0x602114184002081005a0b20110700101004650300d03050000200e80c0c0e0200d07812004082c0416101040306141400085035107603e4000741d00c1c00340c0c102441c2844154403500041c1000c0240301c80200b40b1444580d1000a80e5216078881112604100705004280184050b03c115a0f0300c3d1000130481401c3c040881d68032110580b00e12018036583d4920168004e00030300c2500c000f491500410040c5103028000a4003400d80050786280000714840c0303540303140d130151040e510300c0b28040c1e5039421144e0000b00182000c40c0f10716011000c0c004451038142d1881d400d110000b1038050316a4015032140d180c0b10300903050f109900600b50034848451418001c903250425425403001c403049005400c2c0c112280a483c80040340307600150850000380b0f5490700590024010a44036104900030000314500d54801c032a9070140c0c0700d200d0707900d0b00000d408601c0070102c281401e8104e40001c120781c1c54003e4080002d022a031208854541c000c0408080103948801c06d460a42100d2a0380040d07d498504031800401d442c0d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 849540431 1250 849539181 849539209
    0x2c040605033f0d0203062b030807050a1d0303070503070309150201090f0b181e1b240f0316110604150c021e010b03100207030801060c031814030d030b 66
    0x1d6000c030004040c2e43c7c0341d038080850b05002c120301d101d060101864804d10040005010742c085a2190007046007070344110100c82d4039044076075034a100031001c441951f00480207942c400d40e25100c2400742c000840c1c002e00051000d1842519014582417a00c0c001c0e8a010401188507400d41e4500300c5064045020030400d04802e0303501c190300003016695041e03134a0383c0100c031642848543c031030002c10110003540d81e408500c016020008950700240300344032403818000c00140103074122041c14120030600c00003410b25024020050303811400c0109110358180142c00c1110740c145000c1c05030050741806500801c00c9010350341c0d90b4025200501d015101c5098064050000d02c03502c0c1e940701a4086114424404480207003404100710b450780400ca00d41e280a40420b08095200e8082c0c08243c04280c0068405c407141c2550544070b01c10140c0c0381c124140c8845a8055042d003c0c0f01454144038400d07c40a141c1d00007400031100c2030709041c0c1a400c14180f80ca003040d040c8c0e10505281c0700000c84503640310102030b2440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 849541681 1250 849540431 849540457
    0x11106010e042307031b1a040b07081b1e0129040e010f06030b010803030709232107090605030c2106070e0306072c040605033f 56
    0x24040d008080c0520f00c4041030355800a0107512008030030031084500e1444030b81501c18855000b151507054548030219214003498002004200802130000901e019029040c0100030b414184070417003810b10802c4e5035105100f20950080e40e178031203050700b00345e40044210040e40b0007040f44c182640d0bd200c03050781416448803240319042c0401710295490750441136284514400031300001d01e09200b503502518160100b1514030740680004500d0200000640f4482c152966480c01c0c1c00b031500c440090030000308503c030500044e4021041c0041c1c7c407191802c039102106121180200103040304503504158441d0846405142440c2c410003c0d03940010f081c2c0b86150702258007240000321200d8103012020791801828842c040c4d10100010a5081005074140f000264203845255894070811200700710000040416403030880c5102408403000c009250341280c016100182a03a04c0380002442c0000d0200d0f01155a801e80d0042071070821002031500f40c9c8802104204801c0800b07000070044ca02500310400d01d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 849542931 1250 849541681 849541703
    0x70309020303041d090606030a050d050304110607050a030915090e09151f050d0803180a140f010b040b01050304080703050f0409060e0906060a060522060e011106010e04 74
    0x40d95020b00072100200310200d044101410000200d03079207510f00702c0d03a0011078050680010b040d814049a040c001c5a0301070050b11a05150810544058001130002e5800c0803114043e04520b4845000905045000310010000c200c07052030002c209075a0b5800c00b036140b42d001410603c4c5103420405003000e4813070030b4038401c210350f5607035541030315100075a0039162128a5003070078081003001c103004e079900b118503415044607020340311414845103031741e00b00c00245102c0c1d04000003107038201401040c1c00705150307400036140140101d44810b51071003a071139030500c032030b400c101d02007085600f00f4480c0c0040c040003550140054449500040d00f07501004201030004540000d1000c1014840c200b05c45600ca8111003041d115900e88854900400013801000390969981001c285040d5001a1041c03041d68010320207400340d0b042a60444913900510140388640003078449584181e08002d0004020f4596552107030700411420000611200b12045811402c0d001100144004903c00290f00c2d403250b013004070040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 849544181 1250 849542931 849542933
    0x3021801142709100501080a050712091a040b09010c1106041704180603020f09151302160605040201023708090409030818011503060507020a1b03050111040e070309 72
    0x2d11540a90982c680c021064010040e0016500e0025401c0d544280d0b00c0b145a6900c2c40810001c03260b003a5100e1000c00c40c0001b140c03402154030f80211401c180f143c8040b010049043c1088592090b059808030780f0160303e502044880d41c0309103d07a4101d10030034500130140c2c0701154481c42e15004080c0001e461520400303030030001141303110f003180d00030020000004801030482c26100010040b80c001284603041400d099a241d1805c421440c0c0a40141d100e80440a8804001c00030013241202440382056000d00500001c3c051414402008038000d540104040c80d003031000a040400c00e039522007048608507c81e0b218480d40880c481d0f13401c01d00307400b02d0b1008070303540c20702c00c2150060b0b02d407a9a0150524003040d04156128000a000e820302c1007171100d0703020391100c1203820307240a041000d4001c0c03510300c401c201140c0745801c5907810001d60f005654499500d500c98001444c0d4900c030f800f1095a062004000b084400d10404012030611038a0905283c108045d19441d0340707020b4012010503484101c010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 849545431 1250 849544181 849544237
    0x510030201320408030711120322050409080c2122262109040209040605151c02070f08070204110a02011a0a030c17030403120302180114 60
    0x2034030034010110b442e6220307607a07044050396aa1150004540c3c0c202a110305164908010b032520071200070040185003400641d4000104840c1504900c040b440410000060161240e1248110301030080d40d280f0b503541d01c1440128540b40b00c0e244410200c440a454400807400c3c14800d4414600340715403800025076100003403144080032a00080c001e12022003500d080045030513074102200c200e00301941c00c450003a00c09800d030f103041d080074a0701d004401c00c11003c040c546079000b041e000c18018800201d46846a0201d810310b0b0002850803034040c400105602d6103401003012404022903135a0652410150742c4e9000000e900010b00101070301c3d40455103000310341d03403500030007440118607000c185c80b00d40e107001c000c1c082d05c80c140c0468070b8000102e1720b150480c10072040b05000d681d080103201c1409442c01d0308821131300c100a00c1c42c2029000500c0080700081200078003810602c0255000360311010442c1000103004108251076050010143e0241e2a1002d03120035a140800c10b0310340c2c80c920304100d80b045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 849546681 1250 849545431 849545507
    0x11521061806080c01090803030109020a020f120901021005010326120906011505070b011502030c0a0305032203090e0a0605030703140706180306020f09130b040510030201 75
    0x40e10004281d49611024070700035601250880e43c8003000c50b545007050b0300055540d98154000d0800c070703410070001070100c0e000c1c1c1c1d001442a80c5061040341d8085080004242c10660301c1c0510710007401c1c0000c3e030f007002580e04001c0e128203820310100c100300d0780d45160381c1c06414206003885103482c1130050505daaa00049079040d1040704901030880009440c0245143d0344440d4240128105c811140288401140c0300390f064400c1c01c0c1c2d01c60070380c00669090546031108081100043c1c1c046210410900784d800105000c0460018425100c2a0312420100c52546500001640d02c40d41c5025002c0d250000c82d034007019000488200384600d0045803903c030900d4001d080260040c0740c05128032140007080154840c0448040f001010a42d444640c0341d074070455068002e9003682c0c20746001004140045181c81c0d00500e0002001e1800c0303844e1030013403c041900e2076a803407403405e1100d55824000f40c960615018544c0c2c45800040060800d5081d6400078184008411400c4203440342682031364080d1b807183c0c0318 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 849547931 1250 849546681 849546689
    0x10050408040b070b040c060e0a0909050c060a0306053a06110a0c021201090512090604091e14060114091309153b0c06030702070e01152106 61
    0x449a50b034030f050070102000c140c2034034125600c0c140000c00113500d5101e241d42e44089840100390b161884e1602407010086d0003080020703100b9004900d041100c5948141c02000104003980b000300c0d060f0b10381420442c070340305003801405a03144100c83c0c0c050801740000710703050443c04504c55000762050505008001380305107040f0f0785801c200010141c00058001030102c0c040e80c4219400d2180b01d0221a80c6030a0f0340440d070000b016507004103103100e00071500c40301a00c081d22000d0205130405a40751440025200080c40034610303000061045001da42c00ca005504a40340301ca8490380d050f08100d0002880d035010410380400c91400030424141079511012802104410140d060121400c682040c031201017240e0352140311340d80f074008101c4200200c030341202c2c82c0c008280800010359000f100c85014460000c0042061402480d0021417103940e050065409044558000c181c0a0b003005a113244111060300000c001c0c1c1c0500381034248071a03001c40054101c480041c2822030000300040e240000e40040c0d04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 849549181 1250 849547931 849547949
    0x40c14180a110406020c240702060d09050106030b04020108061e0f130614011b030905040c0c02281d22080d090c0e06100f0c08040b1b0706021005040804 67
    0x500281316580043c0e03980c201070342220307103024050340403040d00303104550405040710000040c000c071409072402d040548141c481c485000b04241d041a0b4880b4215240b0b50002c45641d5040c00030f101c15540d0044820b80d02800c10741d40c40300c11010500781d210007030380c01c00c0c0b0b841d1048481c400e0014585c0c482c0d142403103400c5080c450600c01c80f42c072406040b4a007040b1108840c00590b440c02090303550421402c2080000e501138488a407124144414440501b071030b40042414096034a01100040c0c4a100800e01c82060260f40800c4d0300c80c4035000444000400e9211783c0010201900d800300440d44030400030f40008143d400b03103c85488030980200030041101e4081e00f035103008074180c800248503410020182d80302d040c00d4150151200142c107824401600e20036004285400c4c0b0300d2143d800342c514146011041d05100c4d1420707070b96030380701d941a600a411241002001041c405d2405180d0040740d11615442005030001e9407c3c0400255922130350b0408143d09600c1e0000704050101034002c40300a040d00076 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 849550431 1250 849549181 849549187
    0x515030f0c0114040608040206030c04120b06013c0c200f040603051e030f0a051803010b06220e0103030e012c060708040914040c14180a11 61
    0x2221181c54000e80401c69001c03503e5280d448020002c81400c5900b554203503162000140c403a602400103c1d00014041c2d2200d110400021074805120208241442d20170120f0908130301c0d0000004007801c4a03980e0450035600041c26000d44800280350303030070000d161440341e116034660701e14049503030b104841809000c04104100f0f880d14032400389c4481d005404166003581040702c424092204942c07580c030000d8450780000452000c044280e8002c1c1c0c3c1c1ca40340c944110b0741810203034a0340042e0b6a04c09100700c004140001181030f40801e40d4030b40d40385191021030003000048030503004904d003072091074003c0c0c0d01d1640e902d07a4111003100ba41d490b030015008881c0e8144c203540e100e10b8080c08100311144c1003404221240b41102512174602d156914185a459246051744a580d003401281d4000100454081c00705000c0440d01c3d0751030744203900c140404094064014145400d0100040c0201e070400d24041d0304480c04825191140740301d8503074035170409a42e04038a90382c0c04007820091808440c1240545000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 849551681 1250 849550431 849550453
    0xe100207150c08010303020706020a0b060f01030915150f03170c070305011a030f0706090b21100e130b0f0402012d03060f050f0603041a04050d0f081504051503 70
    0xc4140181a06c1c0320340c0840302019101c0c442030b0f0b5111120340c0c0c0100980d140b400001c0460800c03020350a00580c1c107043c0403990691315511040058041c10b805c0314040e54803446200364640c042d4000c0c00401150010512040c215110031002203240e02d8881d4082030005460030408000308140740086400100801c1032003108000320640907448a1410b10903c42c3c0c0400250390000071403c0c3e021181941c54101d465890720303409c1c561f20340140c01c0d080c0000c0042d0840c4022291000ca01600c10303c9900d00241c0d081c1c0c2006c1c10124803001c080c046109000c101e4000000240b00100001c0c0c101c0107502c00c13141c2540d6544012280718030032101c0155483c40100303403000147d00d0454427210b48003040c0c400703001c5252210034641c2c01c002280304d40303940104801c1158440303040c02c0d030043d41c005024200300307108101c4154104113040c2050381c2c215001c0d48190303051098198485c2051414000600c0c04c0c0740d083c1030a800181c2030030b00100446103c0c03640c60000c28501d6002078910900f100028054401a00340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 849552931 1250 849551681 849551687
    0xd0609022103090f061305010f0504090608010c021203042a15030c110a020312030406060b04080f011505060d0507051621050306060f030c28120e100207150c 69
    0x20f5682103000d8101307003884d00c031203152580070348a07291000e0708101c2c54540340c4401100c01c091075281c84402d02004201c0420314034103d002e5880039051100021900d1500030000914041004040c00354001051040c03100140100049a81d860300d040403010000465188504001c1400c0d403200311091440315203000c00e1030701608100103900e0300b92102041080030b10704a507210420648003c2d07042e0003003091502c130001c222001c0d580050040d0400500251180842c900d1a0b01a030018015984400c030041701e001401d0080700d41d009542c00c040402180b03030101044e8540a0740b103200b000341d51684001031106200e03a05890203043e04501498182c407003414000d207540c06000d1541f604c40c15100c40c0580d03160081e41228021f440190010340b03044001550040d0681000d44444007080c0c0800c14048481d104000313010300502c8030340241400d842c1104014240c0840d11180d0700c81542000c1e042400d8139000f00740d100703884960760707030150743d0b01020301d82001d60700100d000b21982c491400c0e042584040d8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 849554181 1250 849552931 849552937
    0x2040f1203090e0f0402120f07092406020f060a14010612090203070605091c08030c0313050a0b180703020a05010c0204061d0f0a020c0303010510120c05031f050d0609022103 76
    0x200a03541c03550740b944c7c44402140c986404204082c0942d001d5181000505010f03030000804007840741d03515102ea080c58601c0e07108600c01c0d074000001079000514988580f0300600c111070f007101c0c05100420485158610207519080b05118600900400c3d000743c092003c1c454105a002030344c0102558103c40d207600016003580c0144110b24090307440c03244804c0d01804200d58500c01c1c550050740190550707840d10308401c0b580c0d20080041d0801c801d44403281001903800c001001050340704426000c1140341041140d0091554900c440c0f601d607124450810168881c50f66800903501c00386898100b641c3c6500100f000380c50981c0c01008001481e482c00580640301c00b88480c0036034801714010606031a64070050080e400741982124142d007040004106a19100307402101a11050a2030707180300000084003011540d0790140c00002c20000401c0241c0784918100600c541c0c51050381700c40e0003074245030209165800b401c00007441c081e03554041a0039552003070380c98040d04140c0944611585058044039459070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 849555431 1250 849554181 849554183
    0xe0d080d0525050408030702240c011a030a0201091a040b030a090b0726040f0b040c0602060603030f0301090c051306030b040c14070b07110d0e100302040f1203090e0f04 74
    0x40b030700080c801e442842030048a0885041070011410602c1540030070a2418482038030a00d481480c4400360b000a0b04940540b03006441200000750310840203014101489480d41039900c20b4101010410060f82c1010070402070b9040c100c80c01042c1000c4051100417482507400c03031a2003a10200401550700256000580e065100e07400c0324000303072100082a500d140407910045a813441c68004890007a0a1050072031344680903985c052141c03540c94641104d000d200382d80950354051120804d1010a030100000c5401590560017180b62160700c86182103640018003030498040d0300d40c1000d082c214454016a06c0012502080040860350781e0b20150041c081c0070240c6016a04001d1003030042402003c584000350310091510385401c90903600d0401e010340050400381072081140b1101c040d41e40c20440e00b5001405921241a480d500008101201c0f034482022810540104400d02c040b200301b0308070b070301201e80004d0a03c101000e41d143c25103040c2440d070084680740842c802000079026528441d40d01031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 849556681 1250 849555431 849555481
    0xe0d2030070e010501090902090a05130509070b0a020316021801060f090803030705071103011427062a041a0307030c030902060a200f06040212010603030e0d080d05 72
    0x6680c0ea0b106044403509100f0a03020580818013041070704102c0c6c000700a610002449120455203842c000703240201d008024083d05a92441040800740040140102030202814054181040004000d507030748107211440c488100c190940d40110f4031821461019100e815088104968640341300810b1601d091900ba000201c07001c000150032440401100d005500c03941e41c00d458403025890700ca0309c001e40380150070313003640d03036894250008031036186181d00441e015244220440d2241c40c0b01c04480354415010b0f0800d030000014030400903a81c04c1c5610925510f0060f1480342c00340150700003514040d036400340740d60500329800c2185c0075280030002c44c441c9034140c0f1704100c0013540440032400c50710300ca14000d4001c1c00070442a030f040c90081a81840401044044100c9980c0030184541048403800e500f0341560b00030740900c000c40c03520140341e9251400e500020081503203140c5000306615142d168841c0a45a070350b03001d0741400105800c0f26000d1489601c02e100d2414072060001601456076048210 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 849557931 1250 849556681 849556693
    0x9110a02060703050403020a080f09030109060c020106080303060a090c140a020d030e03090a0311040f06030b01050117100501082e171204050405060d0b0f06010e0d2030 74
    0x402e9000b442038600594056000b004908074590700d40209031702c9500c014100000600084003540d509025050030742c0d01c40c0b40080b496102502c0c0c0030f030940d0703959008415503800c00e00c1040040e07119a0941c000f10381017400c0116243c11044429071306202c240c42c51006444000802d41c3c0241c4c0c002411500504085d64104950090000f80c1034a900440f0149a800308400c1e0040000c500c01906106000000a00c001041001400808100d800079441190a42400001000990f800c8409200d41c54080322028000b817030280400521000c60780156414016081d021641d91140c06031010b94034001a11421004210701c3c20108807102c0740d1107140070304003080e0429524203101050545840d10310321201402c040c1000108805050003c2c0300702e801944404400303002c2016000480e001c3e0000358030010a0381408000140329205035a803040c011480400c269001507901a00c417281c2c4041c5615120100c010200080e41011544840d04100c5648a40d00c3c04c45001543c001d48030841d6100031100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 849559181 1250 849557931 849557941
    0x9030c0f0510210e07080a0c031112101e02031306061e0509060f060307090609080141280b03150703090c242a0c09110a0206 55
    0x30041c0f00e01d002e03180b4400c01030f050780c81d02000035040307070341d01214030010f40d4241e0b51155103403494942501d07810f03036060001030300810500040a00d20904031328151021030307901c0f14003d400d0ba601ca5420306038a51050352444068121214002074403e1030080e1700d01513607241401a8054240600321106031101d03868000005180d204803894280c0314511240c5440c2020301e0b0104005461000800b110b802c031402450680381aa0b400c0002e502c03c405603203442010b1401c00e100101019199082200320f40e240094030101008a0f00250400d4100c0840803000c500fa40d00f0380c2c8141d1003020351b00d0b209a2403c2028403400551462011003003101000303c6004d58209481d12500b922400001290950800c101d55250851245001e5922424a00300800e0f41c0e034140d80c5540801406921455030480000c01e12164040606201c01c41d000d000e182c502c405400080e208648003402c00038a19440d507101c01c0100c1040303007841032400200400b402c100700c4000c0444651880b0362000000c0d00050280c500010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 849560431 1250 849559181 849559187
    0x27040812010312020f07290c010f090b1f150e03010606020705100c020904020103270b0714120c0309010e0f030a080609011a0706021b0705040e010c0e1009030c0f0510 73
    0x81104c0306002c0d0201908207605031f500740480d200510084015003040581c513907080c2401540795101c501f50f0001002c802a003450109008054101c0300c82100030f01c159030507400007441030f00c06e807a800541040c001c1e540200c20b0320000d9031030f0800d50f011750810000003400f60f00071032030b50210707441602c2c101d070203840c070032000c565145404200035070110350071001c500036502c298081c5414100c2c03080100d01a15400368040c1c0e071a5000c04007101d10100d04410084099841800c5282192841444a00346601098500c414540c010510136103040003000280446038250051213101103140161202c0d410941e1190f5281d900442a5071b022400c46004036480c1c0c10006001030484001254100d418842911203011b19803003500c00740d03600c580034011510080c144005980c1c000b4800d000a100ca1b0703140a09000030383c0c8000f000807020381d261010643c0e0264000c2c1c1d40500c0b2070007c4582101034140908141e400d075000782c0000e050a5442800411160030419000382940e038211242c119401110742c0803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 849561681 1250 849560431 849560443
    0x70f02060115050f09011422140d02010c08040f080c030106051206011406071401021e04061d0607052505100e090402030a051b0f27040812010312020f 66
    0x400c100001d1881004c0b110140c0a1450145032081244070102580c0200f03400c55500345009200510541480d4810700402c400102400121603090400e80360016011800406021781804030302101d2008019840302291b02500d84020340100864135480000d542d00c0b0142441400f035840d00001140700c0c64400c01a180092a4600400c905c1c1e08004c03d201c920468001074075003086043c000c0c8000114a807109540c0300e0300d11000140c69000040c9002c01000b100c10386280d407140f0811050048542c000c0300c803035100c0c48604000c0c0e1801d02e903001046962003041d034090414040c108071040c0030902d84030301a04070100b1040e01005991900c04116000f2031980741c4502281c100850040320f401c1554800383d00900040c241ea058560355141c080c106060110b08c235508242c540d404034141d00d04101c0d40300c070f8501c06403030340440041c181015030003910f9000a002e000d4202400000d003040390403811610601c01000081400d5603403898940c851003141c0c107400d0058061480c1440d4061800103c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 849562931 1250 849561681 849561719
    0x31501030534030f030f0c02091612052802030f06010c030e10080703060b070c030f02210705010338030a050109110a0b0a0c0b0618070f020601 63
    0x5402451041e6180500c004081011445105442c800341445500e0265a03140154041c83c811501181e01e40f170000d000c0380c640c440340c109118000004601580714a80410781c4000e000c185001020322803102521840c41112004c0d4130181007a003040b42101c9000f0320039480301c41e000100b900110040c0c1e082d1003a80404c0725503400100c04080003400a41c403c4144070a80c50081c10042526188040070030300d5503450401010108941d2001d10194a5051007a48000d100c80c15545d0b0500e00301d9501c04001d8000d40c0300c06000c0980d000c801405550303d5000c0c0c0d0303100c2c001c41c2100c8400c000f0365501882d00d440c8907202e1180032038904000310702003c0d2500108014405c40c241e441820004046500744c081ea01c555000340c00d441601000710005400f441148051400350200c1305a90700b4800811050001c0c0d80c0000d00803c000744040d00503281c0090001001a600c12180c03819a501e15010403490f50b107410604185100440c14404040d8000051007224021517090380c04603a2202646288424140f0f4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 849564181 1250 849562931 849562933
    0x206060303121b0708031005010807030e12130e0f060913020f09090708070b03040c170d050306030a06050f1f0602031204050715020f06010906060e040c0306150e0315010305 76
    0x20020701c1209500a074400c03a0f100c02c0b5421400c00707503a5180c0000580084070040c0c070403803110f00b040c0003035038102c4440c540c07000365464148544600c0140b02e545030040070f02c1050203c42c01140c0c00e001c1c104c500751403001070400003401040c1c52820301c101c00e100400c02c1e569940512103c0c0e020071600303402c940f182c42800c0e40150840031307600c0c0c2c0803080c0442d41c60300801c990203601500c00003013030364481880540010130764250595240d00b080d041c6420305a030035600245044000070202180080c01040402d22815503081c40e41c1c0781d0b6030b11400f0a081c151603500080c589803802e800c0084520131185c1180c040e001c202e411840c0e00e04000310400d0b43c10703510300611015038428403c0000444101d82003e0b0700c6031140d0252524107076a1340f0a0346002c08032850410150b0884290209155401c0002c240100100f541c144442460107401800e452131840000c2c1c091500c51400404043c0070b500b02100600c81d102d0b00301e0313503c001921300404039101c204801344a4069003e448913005070f2400072906882d0403034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 849565431 1250 849564181 849564217
    0x624070215133003200c0310021e03070c0507030b072709090c08010603080a080c090f011101090b070509032103060f0a120506040308010504020a090314030403060515010206060303 79
    0x946421261040004114100111003034404460768800c201c5c07441c0c1114a10007001603c0605080504210600c400c01100314414012210403055110308640c42a00d4401581d5807900c625800700c40502d204500a0300501c503108000013081a00180544920590b554040c61602d4001e200c0c5c8044514541a100035414030f01c044c40807607601c1d030000b1084c600c00c003008048944d0300c2c050381d4296110741d48191840e9001251051485130001421755201e044041da075450081140d00207441444e41c850014100140118000000780095100011041d00444210780070718010340018115408100b9032802401a80a40b066107a2856082c03170034500311601d0f26041d43c0c3e40c54240440014840504e503409540a240000d003d6003805002503554000e0000d0f00d868a00390a0141031510182d2003680a41c0c410410442c0300c1e0341c00801c0c034098079440541c1c241d880c656129200c0c5140a65040a054a07180405120a804071149030722903100081e000d807540e65560703908140d10790048030b02600307802d4030710 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 849566681 1250 849565431 849565499
    0x1302090f0606120406020405010f05040e0c03361b030a0803060616050303040201031b05030a1104080d09090b030106030c090509010906050c12060306062407021513 72
    0x6000361680118007400e00360902040e926401640070342501c0a680300782c2d0000d414440d40d64444500c0c1625401d508203585806d01d054200350380303a14010070102f400b020200125100c01c00a0002d099103c3c200e80040941010100d500b85001c030105009000381c0c85600700c1e0030307400c854218100144040c000c0c09803185202c182c40f5004958801800a9480030040102102106c0680c4111050303034010001147c0381d02c3d042c400076040328904000c5442e0107003d41824400c4039848401c69034070150000c0d0124040d42c0700d034030f588014011500302e4071a074044c1e051860103180c1e200c450b0400321104c8071000c0c44032003445000d040c02c07140a40405010381a00707485c24420708d000394005c10f03000140c0d0400011090076a443c0d02c4112101540c3c410044031000400102c7e51404031249600b1074812009043c80303040903000070700c1c0c41021500c0c0101caa4410742807808191150700c15a044145c02a104207003503030095000500551010220a0f0124200b500118100c0303071421110260500b8040c4596018030f20b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 849567931 1250 849566681 849566701
    0xf031e140a05160b13060b0405040206180a1a22120201050f0d0203041103060703140711010b0d1406010f050307061202280f080f07211e05130209 64
    0x1901c03070380c5040d0b003000c90f003040055202c590103445040da0315000492446a460110309840f00110b806214500f824203110150717940400725030448040000d410310040007503022480307031041a405100784104101600d40d1040c0c1c01001058007401030743e4406106c40c0e41040684a41c180da010b42c0c01180311101034000154064002411045c0c22410054100000a01108142d074000c84084034a1104040740d51000d00782009415000201c42c1420b004035500708058044401008040c80d0402800700d1004880d588294003015148901800104a5414508140060700210241d12000340710700c0000003610603000010710141c6400402034201c0b43d260090441c2c040c4809080d0b00c48640d030030014041c0b128060400c082104201400c90b44031980041c02c0585034035620103412040c40f90700c41c10058401101050654889402d0a000e0400c00c2003803001000d580c0181001400c052403c4a03d009400c803c3c2480144002114028001c5039a0329101e804c00c7c81514200a40100340300c0041091240307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 849569181 1250 849567931 849567937
    0x61516030c030c080a03020702011403242d0a05150a080a06080615090903130b1b0f0303060a0f0303021f0b040207062f04210f031e140a05 61
    0x4001d141c0981e8000140c2c807541320302e901030b803c54000b00354000740755421960031092440240072250b482c031342140b4240780010390b40c2115680c403ca414400215605c0b40e0f0380e809404d03200056140300c140d20341c1800c01d505064080709c00701c041e5102e04041580060035240591840002007242c901040c03c004d01882c081e100307024058001158180c51359008210900100310141c82249161400c80440741380f0000e004078032101038245500c64008100306010b12040310191400c0b180849a81541e41989503480090620902d1001a90b4020b481d11490700e40c1001000c0c6000d00002c8a06a59031540c403c030484242080384402809030300044600e110241001e01c1640300c90224050210700840e4540c0020101e90011004a0f54250303140d02c0c81740780002e00b03107814100c0d080c5c0000c0e55440c460102d179a026a40100d01c101c00000c03805504060540807111135803219980e0141900120000f04e28020f4120181240c3c41c0406000c0c903801036169510500c120a031800400031136500d0306821501c100c40c071798 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 849570431 1250 849569181 849569183
    0x14071d030703020418030f0e0f2b0804080d020a02180406062409080102040303021f0b0a0b04090e1507110f030409020c1605130f0f050f061516030c 65
    0x80510100080542c0340d40c05002c09002d50710f1030090031001745280151105451428460404c40e0155401034151191010f0f119030708021180a44031310032402403000600414106280ba44400310700c040304110300340380580256524074046d100b001120446c1240c4e5030005220103584402c021090420610f903503241b481e000f41c0181c10100d0318645a0741003004901c5070400c940e0341410405075543c4650fa00412010140500000a502d4140383d0384000b965242207a001c142c41c00c5941641e100941041e030310102510324060039104001b03a85104a9032103030010321980880d039040010700340c072000021a40b603000d205800c0030340c1d0103501c46c001b00b11020242007054800510814800404068007000039100528201d0400b60340d6161600c0c440b41450f695001e00c0f0190381e0703040014403243e40c413854280c0902800322000980a030540d907030704014040310469066103d24080030700c510260848000d030322904042e03411300303000242141e0002180c41420000d0308092444404500041d00ca50981c41c0ca031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 849571681 1250 849570431 849570433
    0x21905030406092f040516050a05040e04061a04090b04140c041e0606110709020a0c1a0115090e0105090603120a02011a090405031902070f0e0a14071d03 67
    0x3103807140d03141182e18040300030160100700100e03916022080f41c05203004c04413205903014002170400c04940c0c001c450203100c6c21001e01c1004181d02c85060301c10401d42c2d0040c03a4807640c0c3e000c0390401d0b0034500002c0c1200c00000307034a42e40310b882840542c01e041c058140200d0b03105030074004942e10b07030715000080342091881c2c01c020b024040403224140e50b6406400d40d800700c6110461034a02008440c2d10880d880365111100f8411455140b110609021884c1d600700c0744280d40169481c112240107c46512500130000d0810110581c0b181e00100c00540340f40c181c45d85685130400f1814500c4040c2d070205007501c56001c806503158010b00807400e1114245400c01009400c8800725480309901484d903811210560005039900c0b2445009601c0600d88040d2a25082d250f058903414191176803034880c0f145801c4210b042a8a1400e000c2c0d0500c01c03c41180100808003000700c105403900c02000c80c01a05a9103200ca5070304107039820100392940301d041c600130222919401d04c600400b080a4840c01616200d00f0340c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 849572931 1250 849571681 849571691
    0x406120c0c061a0d060605030f0a0b0a0e1603080c0d0207050a140a0b030f090c060901050412050a050115060305090d020c24121609030201021f0e030a020c010909021905030406 77
    0x507154518007591185c41054041000e9080c0010726103040031514400c0000e0b849031000e00d0104281510b500c1d0041600c840c0402c007901e510a4080c80d102d00b04400c007002c0e200400e0000b05200041d006044052030000545100d00c2c0e441d50100c1c0d40f00c441d405007950110b0021000c201d00708080b40d1b03400760200c0c0a405062415500e04a224047d00b044030b101016803607500c200604000b06208038154032400300c800c141003082d000c0009013603020300d0240c004145413a60041040c84410041040c01c258400000d010055066a561100143d20712071000840d09110200ba5492004208400c1750b210550051442c4c000d407074104400104c06d801143c0c0007030140f05100f241015940014024990382d006040d20710b085c20655084881c1d0196104400c02c035591009100507a4045102801e080e404800460201c44200c0f1082c021710007030005054a1000150038150603401248030030b0780b07500c00d0329090441503a84000030181c4c4a030089402c1c040c0d0301050140140c600603001395030018012100082c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 849574181 1250 849572931 849572981
    0x807201504030509180f04240914011121060d08040303050a0905010302070203101d0604050a030206010e04122a0b0f090d02030403060207060b030d050406120c0c06 72
    0x403a26055500340d000407000222295131342041005140b50789a03d100e045290b140141c0786a034040805000144102c4801040b416000103102d0418240b004142c0200320308a03061902c09880141c141402c1400c0d401c1c440c03030550050b00d07142550040b90b02e150049101442c1040310600c0408010000e56216242d5038141011480c40000b4101640c400d8480ca83c0e900414480600004580d44c0301030304050042100a00586021840b014486041140458800011600d403001c03144044100903480c4204800c00082c001d000800300000703400ba40a84103a070340c031000d0201d400d241c112406420f580d0b49c0d08441d5203040c800e1a100440584d10140c41810203040c0b40e80419103141c3c044d064a40b500c00000344520010b0012149800c44000401004400c07143c10002e5117a000d030f484041d048940c080307920020721603250403420843e00014181c0348045520f0001400c02d402a0095a0004030031030003024094201d80310340004901c041d00e69540c40c554035a40c034006010002c0301c5424008011000c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 849575431 1250 849574181 849574213
    0x70c0209060a420201021c050c07020108060103020405040f05101e060e0607140f0d030e0a02130209100809010b060403320106080a032d08041110080f07080720 70
    0x2038030041c3d80d0f00250f528080020218100b460b00c54020401528010a03c103049882c40c0460307180035428201405566588001038000313000b60381c445600142004a0910ba11034940d00581c464608403030f0481c40e007500d4000080b540c142c00ba40e03034486a500340d1801d125007805840101d4100748000d2440b403500950b507554111000c0c40c164242201e6000c004424859035041c4104000481d10f4a804c0040b42410b40c1c000d5981c907050b80c1e000c0e0140a82000c130540441c81901207800c4200f01400410f000600e02c000104840d81c116807121680d440c000c0e800003146460406c840807240c116112070300a800c1042119128000c0d030030f071901e025541090030000000280110002044c900024003020605800c014000311406998840ba11816260703c1600302017030f075200750150905245c034400b80c8c0d48526117000c100694000c200d52004480301000203141d84180b000e4803801104080308820740340c4060940d00c4c03610a0318002c2c049801c12081400d030300d000300646207692484d5012541c080d080d81d1030314 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 849576681 1250 849575431 849575549
    0x1602130b012003040312080a0506010f1d030106030501090f0515040b04080309010213140a0f080d0c02010219110a0b070201090b0c0a1a010305060c0f04090903120203070c0209060a 79
    0x1c1d1b004207a030501002049501440f441d0b9200740e003802c21a03003010003520001c2c40107520090300c1028850340313040005103450950141e4051039218008000340c4030941011ba045070308a44040720944200840c9030b01500340c0419590160382d010540760599140d50ba54030b00d070750300020f2103c00700759801c0c0319840c0c4900c00082d40c200140401800d4141c9030314514140070908180790045000d00401d07040c20000300a00082040202c8142d1074860021960f80c40101d007005004101208400c0281c00407009000081d50001844079044504d8184207030380b2240c100741c42c041c041d4040d01140992504004910440004103442d034500000e984000745a039503012568100e201c46c0000b074a0750350b8014400c10108202054100c0d81c594485814210914024031952155010f1880d00b1510741651108040c0151111841c2c04031503070056491b4036002600400031107042d03c0603403040c030280380031401500b002401e000c00e0750f0f54080603510b070032000b1400c1e8000a41079031313041c2540801a540303110420680c0c000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 849577931 1250 849576681 849576713
    0xa1a09160902091c0b0108011107020307150203090a03030504150c030f21060611010e01090203062d010e1006110709020f13080607110c01121a061602130b0120030403 73
    0xd03450846d4149000385086940482c00c032a0704c2c600030814500545e50014903401104d24a0310300e0300c00e803561181d040341180281a50f04e50054032421b4040200f642103030292060300d220000c3d40c0c907070704101c0d4401c40f0b0407a0036040207000703c4c400001c8540d255108841e035015100504600c132101c2d00c100340c45001100d0b445d40c04400018205144010505402e02405001d060540028019000395030006500c500000c1c024021018516940c601c0080d041c000003110321094200254180d13a4503015180c90311b008880325405880051030110700c1d24000c4038088210400c0030300901ca901d060039031443c020740c030400342c00381a1941030041610722403458407024041c2802002414050511020140c00683e080f00c000f04150002000f1104599002c00018108000361a000c204601030001c80c040b41785108000a800500000d81c148802c44001d0304a42d50510a030350060601c0c0e00e445c0c9600403115100d03034040c000b840e0000e820b540b0a2940b5031000108900d041524a02552661215100717281000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 849579181 1250 849577931 849577943
    0x90803040b090f0906031c020c03032b0c081915030c06080108031c091406010324061401030209030709020304210c0203100e0f0a1a09160902091c 64
    0x18104036900b0000d0403440026002d4504d82d0050510300c0011343c640d40300700b4010031529483c91400f04564030070801481d03900d60243c142e0307a45941580040d03045078600c201c2c10300100412200503200d41c000d4400e103207031240340c1e81c0c49420544480d2003078030510000498050f13003a6111000b081c5001c90b116074090003940709011080701e0501d000000b030040081640310140a8109000b080300d664042d8a40342e4200f42c842c000052400300d030b4500300c0d40c00c4960620040c40c500c41c6100100410441c10807610401445400065444608091a8080d5907083c0a0364608101c240c3e903041042d4002d0300600b042d004003c0c1501c944a0311141071100301e810486050b5515075a060190f101c160b2501200840400c2504e1b120780500400c0d00426a5411404d2034040f440d03654003003281c000301082c895500301500711000d8a00340e10030350a0078100181c5114221080d1840940070078114140001d00891541008000f07601c210726203608e02000750001e07031016030410002c528510f0040c1981503003050f110300c248 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 849580431 1250 849579181 849579187
    0x8060d05032205120304090b18090f1c0e1c081201030215040b030402120c0a0b070213050603100515060c1501210209100302040203070c0506060d030507080a090803040b 74
    0x29403414a518a69200b903000714000813440c0c5a124010003114251080408040307a040792a20103e601c042d03c0701051044c0f10103250920041c0c0740d001c9404041d12080b6011078410100f1000d01c014141c041c0700d02c0320046450a110141c0d6403d201141c000306202403a44103180b04219102c0c1c00555004200b00e04a003078400006108601c3c01d007806103030103880d4078035503130404c4d091000c0c0c41900d110281c4040d00c0b40000a0350b00850706006c00207501a45005000790420941e42c1882840725004000221701c01c10b84c02d240180740301c0483c45035a03c140710090040c070211041d400c08d01d005007400b510420003074052032028007a60302c50000030101541000010415400038103e52039106c1030607007050304d8410000c00340d42e221300440d580d41143e05404036042e800d00d440e034402a460400300c50740000e40040c00402006505a0403a52140015004906a0310155a5041041114502c4005c024082803051250f4000710301610040c0080b50814146042c0c09a1184d080d5490764026503c025400b030000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 849581681 1250 849580431 849580477
    0x2707020f0703031d0f12011a090c190e04050c09100201111c091e15021e160510050108010605040908041512050408030a05060d1208060d0503 62
    0x1084400110411036010300391a40c21660010405900080700101d01d03141d01302c1c0031500d41e903102c2d0301e08803050004010381180708418101601070001e050342c03401007180417890050070782080713152644500250041c05240c510070b420b08080000412480e48100700206480d0105034a45e0300c2428010182c200c10241c40714050000c200074200801064811641071884240d5140e0031f0509840340d1a0307062901420b24511408403c00a06401d1000b40602030000407064040e410510659170140c029640d00c0c500154952a81c0140e03c80c044128801c5401d881c502c0108207560380240403141902c0d04801c00d100e007183c0301e96180c0b64500c4101451155107000411484c50240300e00700060009560510510801e900d400066004604c2a17000c4141c000c1003041105e803180030b172940030310204a001c00450070207003801c080580081701c00e120054541030101c0c10707514000c0514640c85512200b0602011941203046420301005042580c101041d424208001031041c005466100200c010040f008603c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 849582931 1250 849581681 849581683
    0x3230607030515030d1d03010e031c1b020c130f3306091e0b0c0304180204030f020d2102030702040510230303160308072a11270702 58
    0x1c1c43c0149100f0341c02003151020b8680c020780c500d501d00080d140d4041551202c0700110780909040c104002180c04001422102c00c142c4444011a980e0b000b04200140c055520000300c81c811290000805640000029441803074001c4222403030590130781011410310b030645188005c0e01c2c0d9107201000341c030184660078402c01860086441c5000106940d060500b8503060020b01042181c0c010686040201c030140b0514021790410800104441e01c4c40c15500c500350340d0030548a402038010000144040e04a150007019135000792400e032a00580050042440f81c0e0170403408505103c0c003215004442a5040b055004140c0885011551a0003660b500d07081481000704480d80201040d0300c0d0343c3d844000340442c0706054040001d00c0d411b40c90b0308403603101c080c0009185015a0365204403502d0425160b004050b8084074160003191591078091508990107400741d110140d50180d0300d000c00315085880e011030201e1074500c81e8260043c0c00c81403c0390624490303440e0303100125000000040010103001855034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 849584181 1250 849582931 849582961
    0xf0304080d05100b09280b04060f050406080a0f0605090a020706060e1512070302060f04091d0d0f0c2001081e04030c14070e090c011404032306070305 66
    0x31440d200350140d410001c1801380360107142e4006006415007043da80c002660030b2103000500c2c60207410040c41d00e60320040390401d540a401000000752108541d14a00f1b030265040c0c2c0d043d00c0c0d45440d162140d07502d51038800f00400321034800d10300d465110b000008107600c0d4000f0680c020b502543c80581c1d902003604001d000c0c0c0322a54030111904003a1002c000c000002c612040c50780709405c9641580042c02c003c4458980040b940010b584404d0004006450380b81c010018401c881000100f0b100b0100b07030700e0400880320600240c050711a040080d003c3c600364441d40e0808483c2455007800d56507100c160b00c541034003900795500f0714000640300e9141c1340c682d80c1010845038002d80b80c00824003402e410041c00755103503d000d00f00400b0f1040301c010441c100160034051800018440d0308407042c40e91f46590038205c03501d041d1003402c0507000e9a4001c02c410352144924480b42228005800c0c917080c0380d95161010b00711a032201c01c400045105a80111810a000c0b1602036010350350082100d080c104689403c1807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 849585431 1250 849584181 849584191
    0x503191103090c030a08070303150b0409020a080105010206100e0c040f120b37021b0705100207080319110a0506070e06030103021f1e020703050705090c031b0f0304080d05 75
    0x61701607040b000000b0241c0c000c494801d90705142c0441c10044e1805590701820954106002c070348004180440c142c0314a83c043d0000c0e4143d555000d030541d0b81d0320016a142e400c03d56910010b4007004d0f40c1440788409100343c4a07081860461810310302503840f03c9001410f90700307070130105003200d40714001000c0c004518902d541211111860103203c09800d814403450094820030349035848400503620040c00031b654181c8100342070100c081d00d900c51031411240d89641550050358412113211800c0c9054074400124201680d044a00035803801000a15030402c070405054400b0822104c0320a40c021090248144c0040301c0c03085d4020030560500030405031002e0a13110743d05020b56001c0c0b00400250b9100d0383c403d00180f8006849114003d0340d504c04442c41142c900c0040345d007405841465144039400030f00a42200c0c050701c1640d02c01c03612802001340d01241a1410800980c06001103244c0d20011500c1218150700c0c00b030301030325020101c141000103400455042da484e0f5404034100d6240e900c240a019400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 849586681 1250 849585431 849585433
    0x140105010f181e2412200706050604110405030d03020c0c03120310060f12020a030906150303080c0f03010e070e040c0e0301050901140a09030c020a030b04021905010f0503191103090c03 81
    0x1901c0700038004001c103101d1111a40c009403190a80b0070a1850b0049240e0f801b10340824242e501c401c0c0e403c1c443c01070b02082e558640541e2030400e502003d054960306031016150000c003d0300d04070510460171400ba402c12142c2100c05d00417a00f00244035541003100056503130140e040e007909c80c907011504208006140d03012809000b41d80080ea4240c0d40c0c442c04200d00c01e80240c00040c0c6a040c0050101c00401c1c8000b0000d0202e4034186000f41248580502c000403030703200c1e50751141c4075510440003945900981c2c511f421071020500040c00343c81c4200400071342c032030070504c3d00d8400c041b14200060107482d45484041b01080f4201c120b02c115050038040e2583c001c1c038441c0240b240819a0300f28500180d001048402c00c10785d80c0d40c9400405109441200216400800c01802c0e15168200401002c500b034904900c02c030a41020502c03000b001e140250100d810584412200150464040c0c815500040030340c20180410050504100d925104002c0c20001660020b502c80c0741a400c12071425805812107446 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 849587931 1250 849586681 849586739
    0x903092d15260609180a1112150c0f0d111305031f11040f0905090c0a270e16050307171b01030902091504140105010f181e 54
    0x10590628032100e030420b00c01d441c01031166070349800803000e0340790342030503108580182d00100003840418990361f40601c2c012500c4003da1004a80b60b25613540d16140b202c101c07840c013003001445170041080900b60014000440720f2401c0c460074034010031149110441040f6140100e030f200310003100e40c6620750141400303500800c00b100d1940c50f04000044119107030190302c0d03140e5131020500d800386002c0c0c0303004110a01c1c820003000d407550013002c0039100489503192584120012210a03191070f1928800f264a40d03040c1e440e03030b801001c00244200304d42c82000682e081d1110410081003004010b4400d0711000030f90840e80c0141045c00301424500e02d64440f01c0680c0100014106412001c242c066140107802080208645d80f840140d020703000502001e503010900710200034a400c100400b90104410031142080700442000707503408402000e000b0a40003444800c20401264021194a00c000c101c60003004070356607407031240100504003003801c681401c1c14071104020042c44071302200404902048081a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 849589181 1250 849587931 849587987
    0xe0703141b0304020f0a0b0c06040b1303270f090902030c03010c0f0c050a0c03030203031b07030507080706090204020f0a081e0f1e07030c0f030903092d15 68
    0x1520b00010740040d200f9014036001c0121036035451502d1000340100b01c60b0f079440300910000700742c40b504112400e95690002d800051603854030b18248007803075079040c0c54901e00c400f80d00c40e042e10346504e0003e002240041a00000c500440403100d44002041d0303082d40031603e00c40c2c91040c94144100e1034000c0c0c0c041d1381001340c5005041c0e0840c0d00c90361040103a14000001c02500e040103440c060007a06c01800018240d88084103140e0702000951051140180ba0114182881555901d512a0038409000200103001020010705044018510306024034008103d01100c0d4000078107d070b10051f1f040d0480c110020303a0524a0344c102c124540d01402d403020b9039a042000096042c08034900400d0101a80703100d000080c88a071035080585048424150b214501c1e00d4181c8014006045d01e14800c0c020035009000c0b14043c07407007402803042c02a416512084124a889160b40450043e4030844890401d0341c0044c850308503c0040d88802450481083c11400016007006482120384c02c1c100309180e03020ba04022 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 849590431 1250 849589181 849589231
    0x5040806010b0918280605100309030f080601120b04091704050f01090b12041b030501050f0105060315010f020f19060e071d040804091a03010f0606080604020f040e070314 75
    0x39500e100b401400108045e96852420003001c080e000380381c0c002c0a0180301c00c40703190325500400140d446a22404515003d00c0b4090f50940b41c2164003070700144602d5031204d02c0700541c1d00400c5040300081c00100e0030002c60f5907000103809018140c68606580482e041005103002e0340b00340c00e903040070308201417440d0422400e21601c0c417419050100098542011504022492010160b5014000c0060311860f07161720305980070b040e084c2c910b5044280305c07400220340303881e00750100c90045144d01084596101c81500540315100d40c82450700a6026041901003a14820f0043c0b00c0e08172050042050004a24036100c0201d5036411200c40941d8070000701404807082e1004200d0851441420102c2d255440d89444005417049804c03500045007408800b074048860b0703400e129100d140071170080c0701482e8001e001e01e04441080c49214000f500002c08110141080e80c001c0000d04100745101e4030306034440e108070302044003c4e580d440001b0740d18002c1c4c401c0000c02c440b50680109440440f1065a4040c10b004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 849591681 1250 849590431 849590461
    0x80a14121806070206090909010e0c0f21030f1206030111070314091c060f110c12090a0b040f0306270308060d051e16030c060f05040806010b0918 64
    0x41402002c00194100039075490384281c0d89208001400040603292040b0a00e000e016900307201c0300b99206a240022081ca050082c50416140103040c1e405040019040301e10301c200100500010f0380020003106241c0d004040041c4884d408015000a8030b040600c10f2500f180d041041c880c480840500c21500000d500c5450030043e5965440040d807102081c8002036500b4519010121f055401c18a01c1d02c1003095039001100c0c05565144100b100c00008508001c0c80e10801d41c0340c0c00c847e00128141090b00c1070300c41c080c3c0440e07900944900751030b68a07242d901c14154844c1e0800611440c10550030400c0044c0c8e1b0107035403036403c154100d40c00300d5507a109000d40c8034490a40d006050007001d6001920302c2d19841d890501c0540c006080b143d080d2914545a0b07221171803203242c038045000341028036040745005041002103a074001d100f1604036203081c2d812110000c41340204c4040010400001402003c2040320b14080c04c6844c03102c030b94038082c503010801e4580c02d900008103000d401108120083c5c82220f80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 849592931 1250 849591681 849591727
    0x1d06040506040308190f0b012304180b0406030308060a06090e1902070501091209080c03060a050c07050706020723010801061116180c02070305030a1206080a1412 71
    0x311450b40c5411001281e220320170080821110300d01895103000044540240001010170307224035905240c04501000c01800d607503070ba0045403030108010041c00c10f1a40c5504000034400000007000a29000028113072a503550090340041c10000c184030302d03841c0005424000f0449801c0c842030080c076007522084119030081950031842c40024401800381d80980488800315030060003000345460300e02c1d01c9407101c80545139880005404860216003100001410110120700600400b102d59030301224402601c0c0c01009000c405801340151400140c2c02c00c0303100064609034024140349418286122002c20b050003030009007154400c100c2100d641c000f0082819140c00d0719184c4d0022817141c0080340b038041d40b5a109001d406402d0303c0000e01c1076010b42031810640d000c500a0100c981c0c0170350200c0c0c3d2010b180c08058231030303001001188a0180248546401f00fa40940c0100f40300d59200211800c050302d0050980702d80801d6405006003150034415044807021910401d420200c1018443d502d081e08605 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 849594181 1250 849592931 849592937
    0xc050c0721050a03110105060f0604090b0d0807030906030c0512061002030c15010f0902030408180f0406060509031c0f110f07081b0427030c02040f1d060405060403 72
    0x8080704452528500381000315800c10b0480310028050b01e401000d0124080300f804240d4a81130100d10a40340171400c165841c5c1c00141024106814405210002d14000003269803040b080303607000380001c08180c054a656402a1208400a85401c4001e0143d0f80051074160402c141009510041d031411800c0942005c0150307102c0030000c4201109a2031403103200440c8107181308421207544103034410540a4145e82d6003604400050b41c9e81c2c001c0c502070340000e44005100c070304107000e5113503809260003d1400d240c200a2505c0c549071030b000081422a80941c110f400085c0e4000351400030b9040400c902e0003c0088214100102009501d004001c0b0324036030b41080c2004603800b50010610710800c80705500c1d107440000d8802d507a07501c0d40c0c03040ea1a0001f02d8050b1180081403000340359454244500e004011050741488105894500413000c10401c006046003401050040d010268640344910200a0403c0800044520030b6a03801c185000740d14402070200c0d0320500c00c00001a5022541e244c21a0b4141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 849595431 1250 849594181 849594209
    0x131121041e0203011401090c140c070509070306030f0c1d012601020c011b02060a020a020a0f020102030d15210809191d011a09030a121403190c050c07 66
    0x702c006800f400d1417801201460a0000c00031030313114a1035105087d480503035103c481140142d649221302e240140440c02030260060001008941405120741d81e00c50709510780051b400351030750355001ca50b00700100203235000c91a520741402404038460041d241442503194100c01c540c50f060030807441140c6583e02400c00b0500204040140d402501038941211610000303000c0004954a4005c60032842c00c0d0900040c4600c02c0820203448851003100e802c0301c205e90180000c41d840b5181d0781c0c00c0782c05d01d100407030440c4000c00980ca900302e80c9114079440040c200d4030f0090614038124000400060f00720a0301600d0a0780d41d079450005034468216001c209007079030715004e203600c080d028884120f590380c0002e000e45078031142d115051051401c0c0da4140d442c030240e4040400c2c400f003190440d6010b0010300a4055114032280408543c09500908418443e45083c100208034074041107031a40090380c554441e0207481d100001c08011b81d00548403584020318009003401415203e460340d070310041c81244582c510503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 849596681 1250 849595431 849595433
    0x2070c063009062729070915030204050a0306092105090301060603091109091e03091e1c031e080a050c090a0e06131121041e 55
    0x90803154200c00079032549038080c540902100005050020380448100b454400f004607100c110301c0c003201e494034030b070841d1a08482160790b460141c1c1c1d01c8850748001a5a0001800c0b2042030400301c0b6a105001d1503507280301403444d000d45a880c201048005034249070061000f441140c40e81c0035210200c1c0e40052010500c0b01d0941029030409150082204031200c181e10880300307030350300f0000034801d201c0294020800240d66807000c400700da030741e800018001c42289107200e125240284111360001c2c1400161488080c078081c003245a10042603007040b140e000071411310140e140407160581c0c50444040003c51500c4400002000043c030301c08088962450b5110710000d041c420b5441000502d03001e8290005048482006818168100c50041310303a0b0030280020088600c200c10740e21000c80190003804080d060030300703000750420010304031038020000700c030f040107030f220240a82000c95065171901070b40e0340d03200d503041070911001c0d240d01540c8558203002c1c0030001d0b011803410900c44016680b0009040d0003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 849597931 1250 849596681 849596717
    0x9082803052a0d020a170108070509010b03060406090c0f12200705030909010905040b0a1b030e0f0a0803041e0203122a070611061005010f02030d02180108060402070c06 74
    0x1a80800e9100f107480480c044400c02e8008281911050301141c03031451607079072450510b0381c81510303010ba503811580c1100104010800000510b4000c0d0700248080ac0b125203602c181ca044403190000d250001c1d5910105804c00c1d50040c0022010100c007000500c2a031407140300110b00c0c2c010042e811107011600081020512406206841c6407440c000c025151a5940d8030440c0c001d06400d03142a104084143c02144402c0c400d8400c10315181c01e0321400e45526401c2e00001d8009203800b00710807049005400c94149054014405207901a115142040e1641014103140f40ca02220030072000b80030503003401c03800c0982d40c005042d4070209a00703a00786a6030100800300030419510031407800740c0d000008454a460a1011540310203642c500e680b0726040c1140505c6a664803401a030b40460480480c0320184003a5116100302c151000d4540100c81c6019165218001207030b01444074031b0f422201e05080c03120503681c002c8101d0340040e422941907003024500d031558030116a2900c16081800b181400d01662200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 849599181 1250 849597931 849597937
    0x319080108070e0705130902031b0307020d180801180302190c030b0a0216061a030312060d11090c0309160b03071110020705061f0803030103080d09082803052a 70
    0x1c80800d06c85155036000b00b001030b4000f035507180e04840140d02e07032085500422080c2d900c1454242d001307000064a81e4429a0f1551a0005001c80030030003803400b02d8004024081e405182100042200040d11203040003400c043d160302e102903031054610300140100380e9a44075802600e401c0720385034515459407201e40e00244280620030b03000440340301115052040c283c0c4076105220240302e1118000c0c03104000c054603407007620384105529803c0b1000c80c1c0c9a061520134152500c0c42811a20a03048403030340007855101c4111150381d1401d600000f08200700200b07100340600441900e00480456082c0441d2000c28040240070408006601c7c1c01041c8812080043c0c00e2600419801156a80c5013801c0c08c07515418200e80c2c15610f1248810504000001c003089901140c42c14000b450460b402d580d540c0d0300c40c0c0d001c1c0e4111244203031545040004194030400a100603a00107174404807618880360b5446042030a018914141840c0808018040391000c0d05a0340031540c44010342c4d5100318010b030341c1c010b80c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 849600431 1250 849599181 849599197
    0x903130b12010b040f0b0706060906170c0114094e0c030d0810030c0b03010305010c031b0e0105070615080f120a120219020319080108070e0705 63
    0x205110400041400980d0010484075035000c010407200d81e03c0b101040c10521643c441c1070b8201301100c1040083c02a244060318045101e440003051580e41c5240b40c20070b44010382c000080d41b40031058880a401f0040203050104102824480740c0e020003440541040d0180e401c4003801030204202100e031800c52000810109568810540e40021950b0a101c0c2c0908015000030410390a07510244c442c114001604500c0344001001050710042c9020200c0302c81c0c00c00b610080d010b141100c0044001010210720f40080c169142c0040d480b5859400d103682941c0d2030351b441c40305162500c0f00d18414111813480b03100c00d10b100e6091058501c904003004803118801d214002e804607103403410170110100c41c4081801292000400c8a90310740e411500e0503107801c104050400003a20400020075401c0c0112414204d0011a02c40107040141d80c07080a50020900e64242006800c00590071200903018404000034225034904001d141d070500f19080d035a4102401509005101000080d640354801c4044514403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 849601681 1250 849600431 849600457
    0x90b0103140f250e043f030f0501050409150218030f01020702031e0a030e041b0207030611070c0e090102091f020601051f080703020409061404060e07080c030903 71
    0x800300c4030032400c0f80180f80e284030b40a0500940b400148003106280f03180c021600030081c41107480d055282c140814040701d003010302c01d5038850300f08503048404504050580380320f0b480102d038424000c80f2407001c540050300218071507031800340a4800304080914881d1104006540142e41d03040f441201d154140d100c6262690500c14020300c2180581c0640141c42d0440c4268101e4a191307695117141c5026400380112006d0ba60300040030031000c2445540066983c3d80060000600d66143c4884501001724882802c009a4080c60042080100c0751242c079044405071195103040154070360782c41c80300780b070544940b45865007000041041001f080d41103d4649600070000008000102c140c03000c1902d2a03110400580206e4000080350b04100440e040400c001d074501078008000024181c58000c3c000d0149001c241d401e00000c2011100c601c108070150208a1078031000b07002000c200030a6450940125009050710801c1c485000c1d04007503003e0b0807000e603080f41501c0b0b0741c400303902c1491401041a40103613 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 849602931 1250 849601681 849601693
    0x50c1e0d15030209060108160c11180f010806011d090c06030421050a0c061a06030702070807090b0609220207080301050102010f09050c060703120213051003090b0103140f 75
    0x5000321103404041100d100f501c0041c95030385e90900564401c40111182483e00400301000b41c6081d04c03955149080f20300c94120001c681e0041008242c07480c0e00d04188010f8507003000180500d0b02030605040340148003803401010198180303161060980c8807403a4445044500300d020400c801070078041c6c1001c2c070102500303098076890103083c4440902c1c641c1c0040968000000d0b0100b00407403184003103c40d010219250100c1140e241d035516002011100744014055686120392100f40d60f40d20003c5000d000140e0040614a0070102800e050684550000711554500303800d90004d0b0b2103103000e0340c0040204030754070304010760100140b54011000c8520081c103a032000420300300700319074000603505840f401e078004c02401d08407940510489803072a00140c001e03801030a6922003450702600805e0490b200f841c004031511803400000c8280d030003030075190413203030403040080c8194100211138503c440c1c042d1030203214469603529081884401030101407e1400d00741b0420703041d03080800c62145641c803d4000c07529 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 849604181 1250 849602931 849602951
    0x711010b0321190203090a0806040b0105090a1d01061406070b010911040807122a090e030d051302100f0f051305130b01140a08010b130f0f03050d03050c1e0d 69
    0x500c980c0b001c80c43c184102c7c0054004941c005000402610440e070024441c48541d0805c0300b0043e60000c000c240847c840d4940b28480d00302030300c0a4a104a1703056160011410b607060001042004000d60606805a007081c4003c501162071680c40c00c1c1110141480003c0380d200c11b02c0083c203607201785d130008043e0b8841d5020000b01000000d402c1040f09004407104c003440700c5101d0f40200c01c03491122a08910304206c140038003060718258400f0011500301030803a4900305003c6145000d80d1404c81d65854440550801c41c8103500308403400492102c014540213a1403207103203101800c104084913201041000100d05901d1038031507070300c541d0050f101c000c028540a0300c1f140c4010f070250039103055036400140421141416140210181c8034011600d0301e81c115a68200541c405107608000c0c0e400340382002250001580d079440c01c4014004d001c082540048040c2103007811403900c203032a000c030350801d4544002c0080070115a403c0d1391031310030902600707444100c031042c4000041c015082d00541d070034034041d4105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 849605431 1250 849604181 849604183
    0xc090c03060d0203070f091407020a03112401090506010e0109030f0c05150a03060906050303120c040e0c0423210715030c09051c030c05030408070e0711010b03211902 73
    0x542187ca1424003030115942c03035800151807141c1541c40602681c010302c1040000b071301410714403000e46000ea04540c03800030041a80f01020000c50400030740d0002080062240b101c641c0070342c41d0300120a013405225160002d00007051078145100c06813041c81c5d5040440100960310170810b00800d2f00412000b40c041e0040c03040727051540000074010204c2d01d0300100140d80500341c09035204940000300914140310700e007440d1403d040c80080c00c000342c400e010000070800c1e40c900303030800f4003920000500503121818130714113000c1000c4120000c2c104e050907600040d0f013907031210100001c0047c5040f0550b9810300d1030fa5180e2070010300c5c0e001006120000441d00031940d605034014a034060a0365120840140d0b1201400321509001f40100b0003941c0850002c1c0c082400340c0c141b40d0030301f446081102d00d05a0f50341c11315820503006030461901e80c0c45003000c0c00b4101c3e9105480c1d44906d036582c002040031040300c4002903914031000e40300380c4c01481c50407000300086100d0030540e0096a4859100080c50302e5a100007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 849606681 1250 849605431 849605459
    0x21e0c0304030b0c0c2e0b0105040503030f04260309100c061b020d0903120c170c0c0f0303090a1401090504090506010f06050301060207180e011505120c090c03060d020307 75
    0x5e2106442034283d000c5200c41c64624540c002443d4043c100041c42004c5e0402018203203010070380341403107010040014030341c40070001000c244409840c85034035175040c441010445100c84c8130760545ca0380f000210484005001c0110366500408894007032401c01c1020b8143c410036809040034100d00d05e0302d4042e1404800022a142c15400c00d0350907203019034003031a4155021402c501024081c000c607071540c4001c050060b84208a0b0074007a0701101d039154059500302015a20041105a640d08403250702c1c0c2c180c0c01e0004800a10314411409141048801c41c013082002c00703e0322540d107441c007005103c0051369001c1d51600001d004054400e01900a05041803a903906007032080ca02d0318401502e00117091442081130720305840960303010307000607443c01c15401070007942440911607103aa2229500601c00c400d00c650f1411800040e40001000c2c81c1900700540c68290104040440e0000603110905580b00003406034070100c00700001d5102e858042c04203240750f850f04c00094062042c40d9020421044c08008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 849607931 1250 849606681 849606697
    0x120c080a15361103010c020a0204110f070c09060b160b06060f04060801210b07050a0917060402040c020106060c170403060507020312090c0f090a1104060e090604021e0c0304030b0c 79
    0x72243c0740c0500e078000e160803500007240398070068119070b107080d005140c9600a030102c4222200814105000b11000000540c01114122a000424102080b014410340078040080c4144540a41800015a19400812149080200040c3c2d1000000f841540d640003903590750302c0c01d5800e254545032201c8014182c14003c1c020940c00c030038071560703a0180c00d00c24007006030b01c00da0110228005458200c800d450383e8002000d40310038070603080c201090ba034090114000c80680030300003e15841c203250043c801260805100d507000c5905101c1c052004c150018020707035080d5030001114280c1d50081617220139500031908020502c07811300d0240700d6060343c00405043c1c4d80002102200c0142c9030400b203240d4450303d01c0d44c0940c1040350100c80d04d00c10314010294642c13020862801140e442030440c4e0100c4035601680003140030404103100041ca0307007040184964010001d50381149001480e5003514203801c0c08544224003018005102d03500c2d5401841070b600115800061500030713080010b41e0030000d0300706200c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 849609181 1250 849607931 849607943
    0xd021c020c0706030b041112070e0904121205250302040902041d090c01120c05070212030a030e010510050d05070f090b15031603020d060f120c080a1536 67
    0x2401c02c5e0380b482e141c4141155020f86007034071450320340044802407000c100249203c092011041042d0443e440782010329101d24420080c8400714400d080c8060301c015146464001c940c0e24050401c1901800e02091100da1f9080901040f00510038490440c0a841a900810002800803400081707244d150050040b0000303181900d994160f4941c0e00060759400100c9049000405034410145070901d581d200e1001c148031490618513001298011808c105480c56900401d64800038150501d1549440345d10100074552000340800d052030040840c1c10501070041e588685951410b0504120302000004d004048120080800c00d0795190510002c007004040c2e035020b0888c5000c00c5103602c48000480784030340421840ca04a82135017080403002074101550440390741d130f9109404603e0101800401c070050030039880c0004000340610789081c2c1c8203a03a50100810750300019203e030004103400d518521017000e0302400100c180c50403070641b1200420403880c146241014403210422040c0d80304a03950035011b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 849610431 1250 849609181 849609191
    0x140607020c12030f090409060c0c02010807170c03090109230d030b06030a0b0402040504020d02030a0c02010606020607050c010b0a090207020901061b1b1e0303230d021c020c070603 79
    0x6018070120290701c400b2a4103640040007000c10b14480100600083d40020340000750b0014641d5480003203c0c00d07140d5503408204503860600c110340c2d1019035180d108003a40760203502c10b509204682d40222024028000c0c110020001079000d401c00d501901c0c0c0745402200078007050540070340c0c0984880400d2058080c902503080013180c0d65019025041c442800540920324596603490014020010080d00642c070035020400024140d440e40080c0600000c0a2801641c0342014440e031002c480d00d00c5101819039040440411200b40c003c200e8a07806030745400c2c11030755250b2041c030036401044840300580c7e00041d68075000c242c80c5001da02809845200703a85940701640c8500d0300741da0255409110314080c030b441401d00d4001501002800803540e114440012a0544455094401120499020340ca69004050810505611401082d9030012080300b54001c44100040c100c814411440941240da4001921582d055001804c460721030b480c03144115107401d1001c0b411074882c6014458000040c0c140703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 849611681 1250 849610431 849610453
    0x80d02011505010c05010906050a2403030203090607060212040b333309031204120b1f06030507031118010e03030d0e010c11030c0705040b03070314060702 68
    0x1480360082904481c01c00c0e01e011031070036004540134a00f101e42221385540f180034003000980a801000d00420920102040810b0f114801d0707282c1c0351015168140034552040e0410100707801104440001c102074610302d556000508180300a40705d0b00009420501c0200100818844415060f50150302d02c00050140c0c0071a14507400c6c0c081800c804803880c0300400764040f04080c40c10302143c0d0061586600d02071130007408003040901240107244064003100e80058004400e14040c00030b0090307880e40d0b190310750415041014220051142d05001406003d01d4008500e5040b030320016950906110f2104003c86038503418014041c000c251444d4001c82d003420b4140c0c1c20f940607401587c8940f0b800503080340070191042d004440b4180d2120340f098160200300f01c81d009210083c000d40107034040c81800403c044070305550052800c03000081d841c000d6041805402150b4401003202412244101c4022a0440103071001a041002d6a80028a4404012246800c15001080c59482854103030243d41c440d002c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 849612931 1250 849611681 849611683
    0x303020601230901170106080f031e04080c010c060216050a03080709050d02061b12070c090903082a070f02040b0f030604060e010227090a060f09092901080d02 70
    0x10807902c60b8000352207401070044040d0011908052100310001084056840b840c05080c40d5040207401d140d41c100207441000e0151440030700300f0061580b0541c44c68149081545622840f440a29034104205140d400c400d1000940548140071680301d040404480c2c0c520f0a15580c0c10001c2c02140803c820100040c0190300410b40dc004442000e00400400441903007045003075072000048281c40b460340c128003484007030100101340c10402103c1040756151814117110702904182e51000034440e00700a01c9400080d0b10600c0d160b0021100e45a00d24081d190f400140c07960912142e02d0220380380c000c1251010310290440801c4100d0003901e040003050f0b0708605100c981c0d801e80d0031a58041e07101002250000d002c0d607000d0071001074818001814840c00b40400c1217000740740000c00d51046e02139641340100e07140c14407102c0c0d04425a0b200030440d4a04e00403011a0020070362050a80b10344c0d4500700d040620900e0781050f0001000c20980c0c20406c0801030385503862800c01c0c0142906446004050201540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 849614181 1250 849612931 849612989
    0x702100b0418020402090303070b040506071e090513092a0e010503060f0907211101030b210a0611030f1501020316050f0607030b040b03010915050408070803010303020601 75
    0x107070340c1c0b03180703a614a20ba03024072000c1d40c80030f01e0301c0b6050702c000c209000100d00240744d5580201e100b540688040e041c802c0b4010841e0541140c07100d10154982510180340b508644141d04841056400002004c0d036081040c0050000e010042d1908074031600c2041e4481c5201c180200391079400e4040036026840b407121246c4c1071402d004481e0980e2040700415504a801d90380c0a6110361803001b20740b00240c03030701410148020312810300000d80b801690000100304c0302100b0001082c2003840c040003150088400510810f01400c0013101e1000d80c610080b552000520001c001c06401c001d044c003844030b01c6240c9020a0703004031000c030706968022001c0b4031041101c40d030140c18810164021405c0c0081203c80c4400c0911000301112144145c0700080c102090a100c802d21074600b41d01d00040031034202c0240402d685000ca031f800c0c400e0345410203800005181419040642858000005150b035651800c04480d02c1280c0c8054141600032000104042d4000350940c107a030041800c104886c00b5070521007100007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 849615431 1250 849614181 849614201
    0x6090510020111030c13030c0806040c06020f060138070605060603010f09050c220501020c0d05120d0b030a0f03090b191d0d1b05090c2209050702100b04 67
    0xb0f80c10000700c2c4559049002505400c0700c0c04601e002c88565a6880788030f0b40205510000f071700d401c030000700300a0000601c0328500828250000c2c1c204010142078486e00d61030140240081c01601400c20b002c606010392014400002c030400322100016003113248485504001001c94a840c1004000b8007681000750549040b10703911040c58121500b001404070150400902581035107205000b506001030b2110b141d81c1c0040344990b0100c0e00d40c2e003000002414070706004800b40c02647c0801c0d9000000700001803060b0680c0a2201da29200d1154113080b0001c2c1c01c0c690680d80c0c0c175100304410340c81401509248511058030a40394081c520b50740c2e0407040d0700d9001d81c1c1401c000d5104c8907801d40307882d140108019801d0382c84003c99403520680c00000968002007001d8203a507951040101400c040c508400e00d40003800301110646d05518050b00c00d4845441044210070a8008a000040c1202c250001c020054842d100701409986080c80c00203543d20211542e10026074103150b42c07042a81000c2c42102100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 849616681 1250 849615431 849615461
    0x4110306031b0333040b0603010e0321090c060304120912020d030318021207140d081b0c0a0e0a05060411042102030604110102101a010c0f060501060905100201 70
    0x40a10052010740c203440441d41c3d01c91800c403451484c141aa58407403107442184501529112400e04000341404c6640030f0210144607441045001d03c2c0180c0c2542100c911903568150340c0c2c0c9995011049401d000321348900c01d40100300401400b04014541d5410001d0040c0b554402183c607540744e001070002c426900c00607421040880c079800c0803074402d0f0016100c42c65000b14548210716550b0204207a260603005050f01504551414810040e080841c1102480110790000d08606940c541d1801ea1081d0084080c001d00030003680f2601d00c00c203016102c1107410081c60400196030f0358616110054040315280704c1c0368a014001202803500740700351103c1c1da80d0802444d0525040ca40c054241c014011840440210310040002c0181c0c6e080144900c140d10500f00c10300905512800a07241c90381e0071460b1000745062840702500803c014940c442020380903e070541e150307400c80c24803d1804550200207490700342040004104190413188810450b8800d4070a190f803149400300480c00c84a1a01c0c1d44921 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 849617931 1250 849616681 849616693
    0x6020a1e021f050705130803040501140304020a090203090a0f0f0c06020d020a080a110a2a1811160302161d1501090824150f1e04110306031b03 63
    0x501189540a61303448640e5050052422a65081c04010014158008074007079100041c14880755034859048000b204074450740c1811400c1950004450f03c40c540268120641e000c00003032107101081141c0e0448603005160640c24420710f0410390b100300f5400409a5819a00705000210140300103421141c2d140558098080044d2a9071000b20a50185c2c0716001044040414141e00311030a00240e060644030b0783c3d1317009505c648045c2294945a40e014044035484412030104025840400e6400c4c4028880d44002580c0d058100c9010302c9004a20784401041213418906040680008095108541c41ca4460200c2a9210145107540080d04104890441580c1c0454100d141a180401928034141864225291551116841c2600c0c1ea602c0d0800910f90300e0040c1c0c1e4800540c0c043c5038010381a941a0003084d0503410106110031120707060a405004031075003c1c4454007402e0b0340c07500030341001001480480102c6034012402e400540d02144240035242c0507a10880d404407100b1070110014002d040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 849619181 1250 849617931 849617983
    0x20712110a0212120d1d0d0f05030c04030804080609122a030d05191803090501080a0b0604080705010e0f15030702250603180206040b090d06020a1e02 66
    0x10680380c000d075010740600c1510b13259201ca02001015200d01240340c000025480149000f0030b20b140c210644504298100d9071200c0c1489610041607494014103041c581c4d0f4a440b10031181205106640c00580300031404607010a40010101d9801c4c01070340d101c401c4841c01c00603800503115500c07c140810240990304032240191a004c0c103409007081d8908002e49003015502d098100603600111104940d0318400085103d201c01c0c1031060101c10b04010a0101d0100056500980f02401c940140c40c10700c1800c000048504955801000c10960050b01a589860f910690140c0e0345030700b80107042c04200100400030607070a01c0b2407822010351000701002c01c0100d25600c94081944041d06031011070284016901c0407061110078000f200518601012509140c4000282183c004003403890b180071102d00803802603590b407400e55099801c400f05003035989111100040300c2c808140c10041190340041000821150000030122030114261103050321200d07640c1040340c4031050130881d6100c500c5001c520325 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 849620431 1250 849619181 849619189
    0x1805090610020a1703040b0115141803100e010b180105010f110114010609050915010513170a110604030b0403050901090e0f0a0f1802040c0201060e0a020712110a02 72
    0x1d1081e161030040e070f0084409074889101c4600b44400000c440b1100206020800c1580c1e1061801441c074840c60084803100f00d5802448407d031408600c40c05400032800944070040c040e050900c031000101120156020184084064820082c409005501e00b00c5002d000d810b01014031240e0300c180044e86040c50f0b082400655070041e1070015101040015001c100e003c000910893b25510340e41100079000f98500340000300844000e80140c1d00422801007400010ba61a0f818081d441c4c00900701280c030303800d8035540c01541510799800801d0041030060001004040410a201864090340c01c10611380d0081052094511540c800140000300040004010903c07030301c00b80000800500d41024280d590740b4640030301c00070070ba424400d400c1101d0188210103815101c0c1f03991260594005200081c13203103803a800400c102c0030b800fa00907a1a180040c006500c01e502080c050a910750507030302c3c24241050f4000081d0000700040311000103000d00c01c0d851038000e070889078070714400100400020001e45c3c280 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 849621681 1250 849620431 849620449
    0xa09120305040f0e04020a0902070305070f020105160c0e0a020c030f07020a171b040b010207030318080d080106020f12041202040b09190525110705030d050a18050906 73
    0x6608104082c000810ba4642e0511004028808440d04c2c079102c1c1003d004100d980441684410741051042109a0000b9041000e642205810007500f02556000d8001a0355920540070344400391a422a07002041000062003d415261250302041c49940d4401c03040c0203d1244070305540c0d1030390051010171103035141e000040038190702c00b41400200550741c0c0c0d0080601e41c03e02d00c410140b40c01c549510301c03d41c0305c012680016240b085805010070000403002030b40780c20300e5000240400c201c014404159240a1a07408010440d0f5812140c82075200c500040c4103810a0013074600502411044080c10000024017160742200b0301e51242c0341501d05030031301640d140341d684204c2e0401c1c2c54000d00304441c2d480103e26881124140000910718504581c440c0403101d00400124030f1302d0320740b2101c40c2d0180c00d00c914680450800c0c00c0000d01e901401c841c0d249000c4c0141c0c0555414071840c0700180400d540040a080000045e40300c00c6001c00044000b660702504900805400801d143e001800b945000310308 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 849622931 1250 849621681 849621683
    0x606030328021c0f0e04060e0604090302010207150e0d0807020303010e060315010f0501030e060c07120c06110a120e0c040209120a2117060907031d0601090f020a0912 73
    0x482d03c0404a0b006640c081c2c00e4481c0c01003022900401803440000d4002900740619181120708002c168101042202c846801605940c00389035200380d14000c040c002d6044607182c90300b180700035000001d460090340140110124604440c0190134048822074000e400017406806c41d078014500310ba00708040c8001c8014010480d507418403540d4188500c0002d5000600d028001c0c440300c0840e02828800090b0503524a07140d00c01e0300f42d0140c0c0c1000b00485214080d140282e51001c2100c1c00300c1c800c80411105550310841c05046549041c3c00168448040710003840e0201c0551140228144001007000c100e0358034413040001c9803c034003140103552800351700070028200300030004e801c3d55440d07070a4140b800982c200100c490701c202001c0c899031540384e481158002c01d01d0f0300e45007a071107140c040150395100014014901800c030100c013103081503000b500300a069692000300030802c1e10400601e00d9a5080a1144c4540140b0b4422403c10303210690007199520105511508882890840d480d1218a00020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 849624181 1250 849622931 849622933
    0x3070c020a030210020c0405010f031a0601031b08040b1806060918030f1e0301080d140702091618050f130605150d2f070201020f060a0e060603032802 66
    0x1d000b0005a4595540c1c8000300744541c0242007918241c0d050008490701a0081c5242003003241040000904425141d8600503040c01105070b0b40d01c0380001600070740a40d08454440b66054608845620f5101ca0900e200b28019034900386280c84401000105108001c036503107264000794001480c50504500301600240080c50345510400000b03440c0d81560400d00307800c0c081c036a00081080c075050840c441075004c2014090940d01e10b525041046545518044010081c80509100c00b2003542c0c040782075506140d0081c000e0100c0303141c00204d4003040650101140081495070990495403920504e00303005446015040d5002101e9020070090990482c5045c1e00140b41c450002040c66202c0c00062692681103108594989142940c91400d94800e0400383c50109031241030050b44203040e07010b610a030048540c40780d907655a5400101e042c070301e4440e007040721841400180b1280c64181e42c000e450480c00c84080d02c0e019100c2c5400c0640f01e1044464502401a0140e101400700c910780302c0d54258408180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 849625431 1250 849624181 849624199
    0x4150e100c020a03110303070504180e1006051c03080105010e2b1416030201110c0d0b01080d02010908030c0c19030302120a1517070509010902040305071a03070c02 72
    0x505800c256003811090600682203c495070f01050b810011451a016209010b1415813a0503e001841d600607445070002c40c81c200ca8900a101b0520f41c04001691241001d441e2041c8400f24054094800c070300c82c560180034019407000000462030030700181c1591565500c00145d00e008011210000143c843c030380d124010140b01c00180001c40400f0740c01400c5681c0d0701c208a00d141c20b007051200d0a0043d42c1000d900103a42e04100807440841d92025217609080c0814500c1c2c1c28074400d4944079101400e9504614040a410140920328040a040300c3e604012500c400326045001c82c2a00c0d60500c0c0201840c2090012510700460100600b00c0700451030700702c42031003076035121f031910340505000141c01003540007a1070034104402404603a4049000a428042e00c20109554940885c05102d0340c41c070034201c502c0c502c0072504103104290040c840108803281c0c07561900107450080d0b0007444122050b218041c800a8001000540008050001040d4078110390700c07218142c80b03001c102d84003264411402d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 849626681 1250 849625431 849625453
    0x12060504060f0603050c031621020a03050402030c01021b0f1804030c050c0a120b18030711040c0c03170c04030204090308070914031f0e0d050706110304150e 69
    0x140708081c01821511001c054051a1500c0907088032405803148400c81c0d0204100a44500c1d8800c3c1280300035120f1502c8c0103020f904000440035510b9029074001d0746400021000b00a50f81078203e00d0046000700d0544a003610003000580c1e6501842003500f6001c983c03501161850715100311000e01a4a0103071403540d906180703101c01942c049048600b2404904e100e014801804400c000d100f29100090310300c0c000131414100b01c090600000c1100078003006407000007a06c0c14914600103001c04034811300300c0340c8507003907490507900c44241540c0082c001c80c0b0780544030556900c20846600b00a415171250f108544025424480d1031100402c00100d070b240800c000001603c403889910000c1d8041c4c0d890501c0390410150050103c6445c0d44001c0810054800f1203082e9a070100306415560394001d40031051000302d4a07a14040d08a102c0c00241d24040c1114043c0310f144c001c0000d104062080d0010811344c90303003200d40ca81d03d01080c0e40c05041c5403c0b8801c00500080e90340d208141c813550090072a0108060 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 849627931 1250 849626681 849626689
    0x9011505091e07080103210503010302061b16080f0c060913060b12180609030d020a090e040303050115020105010807122a180504050d0e061308010b12011a01120605 72
    0x554480f0000782c0d0540041051202d149100300b00610190101510424082402003a40c0810700002e4440c00b0b0014200e0001203140040c00e4240c210381c0150344600c07900e40300d05ea00742101486842e016004116119901080108014000400c020101418021001d042c041801010960401040e03503c40000c2000c0c07811001030f00841c042000002d40310f144ca165039440010000580b00115400300040c0034039008080262241102564001a251204a00d003205e010103030b9446074010144c9801032006140c0d05820190581303204c540d0410752004052000ca00300d030400d115801450f04105c1090218500180e114910240204001a410785425040400c0c0504244503841e0b541c02101c1c013000310007038500c00c00b410340281d04c104000910b000d40307945031a110305004d48002c204a01e6481e03207096a4040544582c045030b006121303205921106c42900038503002214500c07030f005100c4d40a5202105000324800695001e56202018030b018005440f000034154164140302e031130703110104a60311 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 849629181 1250 849627931 849627991
    0x402190c0c230f011b0303110904050a0506030127061d1606081f0b0a051608070201142a010f0c08100617010e09011119080901150509 59
    0x14103444112042c0c50000c010180010140140c1480001a6404820080205948100340e01801c010480e0030b404400300c15140f0441103100d038000e141c001070081025040c3e00140c070aa105400030410f00d5008040c3c4081e003161a02c800704100c03101c401c0075000903c2600001c08600701050741440f5040a15440d60500b481003a811a000d29620001c004090707004040387c1c0c000d1b10302c107152215810ba100e032442010003d03000c0c1c01800940000c1c00c04206100700d0895019000650a1004072136041c0780880c140c0d800000140d00148040941c034401860410458008062070542c0020482c0d18010120680250b05071140c540c2d5660b4103910180041c9000d9001c0800481c1c0e948045464101c8150100c00d0311a0040420840c0b040c11688d0410842d10702c032070554100c105030714a940e80c2c130b00580303025107108446580748030000320b100741440e520a03e0401000840ba100c2c64907545c0c5010000c1e00700c90242080014070b2840e000100321908040301e4443d0401c00d400b00101c5504910301048268034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 849630431 1250 849629181 849629219
    0xe0a06060311150408030d02090d02041e05060603161803050d0c03080903040503031c09060207060f050906070f0c0309050307060906090b0a020601060e12120d0b0402190c0c 76
    0x1103200c0d81580c07061901c0b030f0100303d0006558042c0f40c10302d4180940c0e140c3d00d00849030154582503000405001035626200c5160700c1550080041c04009040000001190207010121b14402d00381008074000b0303d0200c040d213209104000840d017401754200c60440e103050002980c14541849a00c9c0440469010311500411803e642c507aa0022038486c60300410a100041201200707420500080c0800ea13004411510b0310007042d00e030440306603e0103540c01d00800f03c000004160b54800200074003000384941090006445080c3c4c1000103580e01d03129a40c0300e4404444076400030344000c2001002600034400d011000b4042c1c54950050303600ca0003c00d280140c55000714001c0b50f04581c04100860303220113503001a02c0d2540c803031030529490440180d0343d280d0600461040c803040c03070001d41160b03c0ea090030758441002d040842d5000b1030280164001544100c0c400701d03c03981440068201030809000b2243c5255402200d44607280d5980e004803a101d400f00c4c001c962000b001000000c00c0e00e880c0021101007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 849631681 1250 849630431 849630443
    0xf0207120203180405040b18030c030c0c13050618070516050105160f08010e1302130f0606090f090518490c080c0a1a01050a03150e0a060603 62
    0xc45101d180d00b40c051071503c4409100701d003010304000000b146800c0316900715030303124100f8143c2143c0c1854030b41503028203500c444a621010500c540500c200048440f941c200c1a5051200e4222495412050740c0007259050342046050074190714440140301d056901203914a089800d215000401104001043c0800d85450391030b0000d100c0308407611411485500d501c0c1c00e14484001c50340e140039120300f10511031580c034007100c40300007507100c0c0c90f0404104800c0d6000380800780c003192460320040109035034605003640078035000000c501d403406500c2c0c600603110f007291440768051030070315007001030300004140310000101c0b00c001c015005820801d00742041c4603003040510000081c2e0b00320082034403070780c460289500d140e500d1000f0003a828440144070304080c41c1c006828005418200d603588102002c644062040d00c0f241006d00000c0c004441302100e9506004501c3d0f42d0301c4c41003292590700d500029184c0c080740c008a8400c0d00444c0d1002d411003803503605440d00500142c580c0001c80d42c4543c816518 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 849632931 1250 849631681 849631687
    0xc060605181f060c030809240405060709050307090b0d020a030503030a0b0f090106030903020f250f031109041406070c02040b01030c020636011b1d040f0207120203 72
    0xa0300d03285482c4007641ca0040c9045565280c010300034400c1d019540c026041c8084071000c034045560901240742d02c0503403a099a02000c910103501d100c0710400301c0e41907a4501038100822281845514080115a40140141911820000c4800c01002a8503545170b10041c00861100161200c4503078000550182c1c000d5510b91800b5440d40003500c030300d9a40b25109070261031090380350f0381d02c80180c40e041d030340d0500d00010580041e00c2d0030b074941440401001c0d01849659104905040b55a002004030000e0310706900350349640f094030080c9490540801070000039070140781400ca08009034610b03800340c044e102241c00c1c0303124200110300300501540c0e9600050b00840c200019410203010704003c8a8003880c2c1044052140c0e00300030344032040500384600d000501410807405c00d00c8004040c80c1d586019074824810b18550b2030050007000c0b01c0b0b64031500c10f00000c0a403103125000d9600700e1101c1007950f072814210b13500c840410008040d440c5401c20440d60038807100002c82c00100310010299001e80040d80c1e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 849634181 1250 849632931 849632941
    0x3250f120612050a02011e1d1c050c01030605030708030f0c03130608100605031509130b0a060303170c030c03040f05030c0d0311040b040308280207030b071e0c06060518 74
    0x1320f07c2c41c2000d151595142c14803986124950703c81400301c0e01c2c1e000044050200c0840c080044d480614404038031490480280500041c4503012407150901c0c202620104041a5504c003890f440300340c00d00c507400c240c1c1c0083c084480b259002100a0044030074010649141c00f051940c83c0000d10055049440005e8100040121096008026a014001c0c074101281180350105140600024170b6501c0b6004031030580120701c5c0000140d032260a0140d00403903544081c0382c41d0782200700402d9a0710090340010381d40203013102103a4a4401c03550060b0184008145190345002c03140103664005003003150300b008000c1c00350011810a00c003070504000000040c0804015804004003510304c0c88d402069040d008100420900c0303e000b084034103c0340d10811054650312031030500040281c2d007001803081460741641ca0b00d0000e902244140c01e030791044080308811b46814108883e4001d41c0c680100c0f014410000740d0032100d00400d5003011041c031a178808102c0381d840e4808030300c90302440c0c15089504985401805 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 849635431 1250 849634181 849634187
    0x9010207050606330d02040b12011d010e06010c15020d0609110901080c070515090607170c071b06030911180105130f090803250f120612050a0201 64
    0xd5009075048540700c00c104c030004102904560180102d542040d103410b031555600000c98165102844000c030115140d60b41c1b80303000c0040e90b001400c5d19426a0f900c50001c520f1504007861041d0300b03103001145040580c02c24001743c40a03000070304140c0c140184200b51500051921505a030070900c4041d000d0384a05044208a050741d9040d046002403c0c101781a50461880035001d1315900c4c4401d182100041d2150118245c0600c03c107400a0010300a600100d1008040400600d0207062036800b1290140c0d01c601048821000304004c8007054024030700032490a18a10000e05002070150900c03c0c0201c40152418290704403d500907001310f5101c840f08000d00911841e0710f99201d81c00e50300c000e040030b80030075400301c0d0544c140113a5209800c44404180c410341607910410040400001c100410440c1d800c02e140c40d600102c913148000b500c0710356843c5601805040c1401c07110060740f070380031610301c2030141074a84030390201c08107102941c0e440000920507448505904114000d4000d05507402c0ca1b40001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 849636681 1250 849635431 849635443
    0x204060c1b23040b030a03020d03021b010908070515010b07171204060515060301030b060405180706180b07021f0509031209010906090b07080f07120809010507020106030510091a0901020705 83
    0x803e105e0340050320242d0200707070041007026044075249030050707552200b6141110046401c030035154541d0f18040364030003045520b50050030b516005004490007480d6501d0242080c5500340035148203c1c1c0c00740505400601d40c013084003966002c911146080117284c0700d00c6040000d08660544402c0d8449040c40840c0c12011141281c054050780c1003483d66055071501210f1440103001580201d40d00c800060b41e90442083e86410b104054041c2e80a90395145001000c10901500b0b032200c80b01e02d0680050002401d40480381c07003560141c04280d1500062400d00800303c3d040901e0024001c0400c481c0245660501402c21303103100b005400d581343c1c009100010014145500700c0401c0c022008014170005201d50281c2d034206500c4000030ba40c400c003142ca600c00d1401a928014103400401401d210310b01c1e0461100c80c8100d8000008020310fa666910881c00d031051484080c00503041710010910381e202d16040300d040140a030700c5403960064121881100070070100da90031510795000c2008001c000e014806 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 849637931 1250 849636681 849636701
    0x40b01091109060405120f070b0409050a09150504030e03100219090602071a130b22141201060e0f07030e0c0f190902030109021c0204060c1b2304 64
    0x7490429108401203603140c400c5014442c403400010322031941002081041c0000700f0b5407481900c0c810355561910f0302e0950410300400503c40d0070000020205041c0b0312601000c00c0d004aa901c8429012081400c0200800341054040107440480a44152000c1100100c134118810b0010b070354410005200400b00303d008000303c00c01034440e004008440d400034180d0f00351203c00c07200010300c1058154411103842002c000c5612103048000000f81c03588640050074580750060b0048008040740d0341d4060300c2c40c01c5801844030300b40d40e0700214522420216280c0c2d203002c040c1400051400e8842060301c0414000f00e407480c034415400400c00220326414050202c2c10b11103c170041c070781406c5810000d00d425034207129890091000340480c0c1d03c180920840c2c0d40062110314403c40d0707256111f4040c50041d40c000075603042c076105400480443d02c5050710841d4110f520355034460229a00341d5503061001003002c1c5d0780030849802c10f90045030442c8041142100300b1582c05c41d0030450708400090000b600c5600d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 849639181 1250 849637931 849637961
    0xc1e030405030114310b0f0f0711031b030708120117120d180c0305071d090601031e06050106050318010b090c0306011713110607050a08090612040b0109 67
    0x41c0000c24607000c10050054041755602c9440d00110b4001c0f200d1441040c42c0607144403000c50600003010007000749103004000f400c40442217036640b1081524006a41408190f20360f00400c160ba400c650007050300390341c50804000ba40d15102150300c45400c9508504c54900c00b000c00080108500700b00100820f1008480e030b00940a5122552032410076401286200c00c142a00c414024548080c01245020039a501441e0020341503204d040c5580e680c98140100c2000200c0503941440c8402c840b044030384103c0061008010580c03c4d40c1d6034006420852100d1040e031300c9810a5500065020702406000c4e00d034a5681584a103461540d0307959241001c0c962081d56458060200d2494a038801001d42c00040124042d0752915400012a240b4014414046e42c0341e84c508c090052b011038220304254094001c11100a5161192081050074416011f0045c0254444030f10040000c2610f8042c08500e04c0c014161402d2130324500d056a04028201c40c1103c1d8006c50000501c1120441c3c42600002c3c0381c502 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 849640287 1106 849639181 849639221
    0x9180902010806030307321902030705011b23010204180501080c0315070216030302030715110909090709020a050a0e030a170c1e0304050301 62
    0x15012070001ea00480441e07514a00003040e40e440d660404402034030542096001c42c010291420403d010350a034292114403110140404c20341084801d803a03858504041c0704040c1003040c01d800c040d060003086503500210102e62091a24010360080c0da100749006440743c0c610402482a5a06a807580001404580014a203031883e450408000d0207014691722205050b0711101000030b140e8040c0c0c8601915a9003041c038400580e041500c0d40141c450010349480903002055036a00141d015a000250340c104200500c41da240040c2c450340e00800444010318805641880380c0d04c442407040c8407032404900750074400d0001000404840c0c1d01195651203801001d040c07a00302e40c0c100c07800304100041a4036981004154241c40c06d920045094605548628401083d081030541c03640c540b203110205942c40c0c00300311400c1c0c0c02e24503d50007142c440f480d1408050a440c2d107000780d80e4080c0030704 = true := by decide +kernel

theorem cover : BRFrame.Cov 849460431 849640287 := by
  have h0 := BRFrame.cov_init 849460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 849460431 ≤ n) (h2 : n < 849640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
