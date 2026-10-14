-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0415
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:41:57.965218+00:00
-- url     : https://prove2.me/submissions/014e8b98-17cb-4ceb-bf82-c4c65ad05806

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 74460433 ≤ n < 74640289 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 74461683 1250 74460433 74460437
    0xa06021e0c0616150603021f02030d020708070303060e0628050a061e050906040b07050f010518101a010f03020f0f031e040510090f14030a080a1b0e01 66
    0x800c121404240d25030311a07820340c0040071100c0d03c40000c00101205400044c84045002c1000304d085a0204900070340ca1030768450329460003440b030002603200708110741115008560654803007000e4944808282c0103201c00714040b9041c404040381c4985030b0441d5078815840105200480c100030100c803012084417000c400407600c1140c1c1e0205075511aa08213900902c002e56a034410b00849420140619450480c1402040420015200b040e0b031082d0035202076900c1c045540b07540d0b03051460b289203050301e070340ca4454055080000f0401d80120480c100c1d00c2d80a500001c0d6056442c2100542c801c0b10740f11101c14490781c80c104000e14043d4424110310701c0d000e402d401c006107400e0400c0c02001302c43c4c2003030000c0070192400108100302c81010f400003002059007500e41444038103003a030b141c5480f9025091058040ba6446c0681028045548092180107401031a415050b40d641d0418903241c0e4070206242c408582e190000c5082400c0c079120359000c0c01c001392309440301164043e404a40c400d402144440c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 74462933 1250 74461683 74461693
    0x100f0c020312190909090203030403140a0f0b06011101090c0326071101030f1a060d140f010503010507020a260f0d09060605010f02030403080c030f04060203030f01050a06021e 77
    0x82c403585801c010001d1035030400c0444120040c1820090050f08550031001c0954102800080103843c00015101030341d03030004203031001c1056601c01903c0e001ca2404060440312000c0c010303206000e68008003500460b002e80c1d600d0201000c60030340d6820380e0718004000b4401c0c845d0900400211f04862a00310b040c14110900810b070140800301d1444d982c000403000e540383e00c120b0b00729140c00e68252041801918601c10240301880c10b00c4540007207604841c1f41940100030000b88504180b0035580400d400c600c2900c6500c0560600c043c905040c6c2d4800d000e5240070303628000204017924000603000c0c8040c2e5000140f50380d4082c2c40100c90400d603100103800002d10030188142000c100400010300301504004d500040c900805003046001e43e0b0040c0c0c0120706000680581c0c04a15501100312400e0b02d4000389015581d15800c6c84c05851403044c190300f01c10282001c03901080c000e80c003000450140582580801c80350362124200170039080c0620800c009030740000ca055412100200074a0fa204007290280c0d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 74464183 1250 74462933 74462953
    0xe0402060c030f090102070f12170c10050a0b151608090904060903021005100b2a03040f1e0501081003060c05070201020f070b0f070507090c030e0606100f0c0203 71
    0x2032840c0c03ca02d00f01d1030940c0c0c001c11100041d5a04203c801c00500c40c0700241040203203007000400c660060400082c0003204148000048014100b04595403803003c1011681d040b810580d2800c000c180c1511440071040c1015041012481c268580c050b00c99141e0803c0351420588506a0f1a0f05c4c051010445040c8401e000d01ea4860b9100e10340c02e40b24a00071000801c40b40da103840d00a00345440040c1801d5a5480e100500902c0003401e9102802e031400214099030ba04120303842c0313400b503000702124100c0300480e4428000c20b803c00403010b48200e034a51016406c11030b8441c49400080706a40790034035030a0743c161000304200d41c8108030661300400c642034100c080623102c1c2c0300c00e0b0945a0440c681030224100182d10021543e042080031081070071100600b02190410401c0d060900c40d80c400008201d00104107502842400d0142400034000b000c01040315615800c0081c019201c0600344900700d001c1c0c3e100056490400d405c1038150640c8507a110710081010f4802078550400c22a026a01031007500425 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 74465433 1250 74464183 74464207
    0x8160c0513060321080a0c0e030303041214040e04030c06090f050309030d03020316051b031315050306031f060305070314010c0c050a0303020a21090209011203090e040206 75
    0x71072101c0c00d004102103101400c41c20000380c2c404080d09101c40d1103029001c140e03d82a404590260801242d2202050740e607403070300c011101d01c90009215541400008240720070003130154410000a040c6840700d60100191406000d81d60045200354103101c5034050000e0b000a00c00d0700340c8100740d80300d1000010420380c0c0f51240014804010700032205a400010001d00905e41045040042516803605600d140340c0790301400721001040c26081e0a01c000410340041894005d00120103c04440b000c480d111100c008441050b11803e00c0348040c080c05d41005084114071410443c6d2207008003400030190208000008002d0791003d420a80c16655507500100c0041d13401e00100004500544035000142c19000b402e908645e072040c0350405100c4c04000e46030000d0320114208100c85c0d0107080c01a110320800300140d0f4440820415444002030004500844541980c000c80031fa44c002c0e0b901110a0f13803620050001441182e4000c0c000c10f000d03030020001a0380081020b036000e80702500560504002c0050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 74466683 1250 74465433 74465449
    0x35030d0f020a110f0d0e040e03161506050a051509031b100c21020c040f230103210509040e06071e140c0109020406060503150a06050d1503050303160e03070308160c05 73
    0x64001078401003900c48284909104041032f0300c81e10080c2002680e14080004280341e0591007000d00622240c004503200000b200280c0f102804043d00707441c0c110491075103134281c50301503d0010340304d103401d0020480d94500c0384400c0c4480c0c0c4e6009000b030824030801920300b0f10f00e0200e0f61910702144070310050241551201c3c015000b51041c03651000c1622403008041c40c40c66020340d441854240000c5004101040a8070f0a00480403000040d91a0036440300c842122244900c20f00290810b007440d0320f0300144e07440051400d100d61800c3d51910101801e2080c031444a0031803100b02400100624840e01c0207034103042c01003210214000000030401a194081829101c41d60b2122011803004410010041c0c0c1d00100c90a040d80200c1e00c0b80c1d440c904200e40604180038115119120942d40d41c401c400441c036460903040590380107400c8903100d15142d008002180c0c5182550400078202840030201820300003042c00c1a203038800e4982e4203111884080100240700108244d074080c030100400606611881d80f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 74467933 1250 74466683 74466697
    0x1207090608070608061206010e0a020d0203040c06081005010f11030714030c0f010e101d06010803031806010b090103050c0409020703020304050a35030d0f020a110f0d0e040e03 77
    0xc0c0812502c3c254020300003110040c1810b0143e042104001590781c030201c0c406043d640b035100c481c84151514a030900c02070242c8a0500e00c031910000a00c01032081c0c0c414042c0450300075a403040c1c665611043c001c2401012480f03243d0115068004840503103001d41c688070a121801000c8a040c90700310380320510081c0801c0e0100303800e034100045200141c0001e00c092900000b50600038402c40b400c000e40e056889410040000090307a46220380c071000c0f90004c01d501d031904011000c68406503120500e0640f43e91042e2262400540307408440303482e10718003180d000d04841c001c600707107410310440c100150040e140051850060500812020500b4011407015040c102d01a0303008503203031410481804100e1704150041c1c0d40600c00c0100300400400f00c908014075202490440645042c00d08509501d94010024042003903070419021000d040c18a40c0940440d01581c0c0d108800504040141c40e11980c6482140005821005000c00d00740e00540814403004405030000804072003242c81e0720700f0364001031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 74469183 1250 74467933 74467949
    0x21201030c0f0f06050f0a030b06030a050a05060f0a031203090f030e09010605041202040c02010b0a06110c0a061d0a03080304030c060b010e010f080907030606031410050601050912070906 82
    0x156080c00300c41202c0300c210000d882d10040042c10700e0705081000e40b003400f4001d8021301e4140c001030150280d40c403a800c000f812500c05040a5140d0500d600d104000c3c100454080302c0031454100064001e1404070b51501449001070481d000c200c3c203507210482c4500030b402c405414551a503440ca0006120700402e403088078060f5039441c250f01000c8007082183c010680c486000c100e8180403e110012406116007c01981220006491415a00300b640500072541700c0c83d80c050014040010702d0754006100000319030181e010764000801d50b0742042740c00d90003070040e0720006241c01024801106103c409030500e00c40100300d4207143d5541d54812015502c01c0303d0440010b6901000d4404001190081c03047c0000300b420401d604d200f00c0d00000b08500305001c1c0e03000804c0514404075540d14402d0084002950f007000341170100321380300d080901041c131042108050324442c00c0d204045203a075038400d144c02400160368483c0781c41c03031440030400502d004020060312401011000600760000d8498100246003103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 74470433 1250 74469183 74469203
    0x608090606030a0b0f040f060609020d06050904230a02100e1305070e010c030306080709090c0b0406140d0e060f090f030319020a020a050a05160b0903060a020a020102120103 76
    0x42558203042910140c1110301991040c3c8020b0005902d4004a944c480c3c0403141c0e54042e55141d09004409010341c0902900d010700d0040085200c0500e90000c100247c040f00051192a6951050054420040301c020307040b0b420001848804403c440e54441a040d000403c40d00d0002c0d850f00003131410401c41410002082005481d40280d041180c0040c080c403e560404100318901920003074400c00d1104410740c1000343c010302a0b41012b01030383c41280503100200440382040c3e1034180080c010610040c060310000825000060354031401004c0307409442c0280e8130048600707902040045c15400c020550b51215898401e42800000f0800140d4841c01c1c90180341030060814903109809d0900705560304e206a00104100716803002443c0c4400e4034004501401641d41098600881c10504c006000400034080d0304c080d1000c1c0b00340041e05250700c100410344102165502e4031000403d1040d11030054040e0000700c00202c002d1700f00d0340130300f5440c0d50f1800013600e403581c3d409280c0000b6800b60800c46d400303214 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 74471683 1250 74470433 74470441
    0x40819030506151305010509031905030406031104150507081603031509090b130f080406030e06070f02100902031e030c0105060607020d0b040515010305060a051609030314040e010608 80
    0x701140e0909081c03c10201071070100d00d01c08101c89203465001c2c140c140500051400c046131000c0009a051800c120030803602895927241c110340b207910500c00d11000034180018a425198010100c4044034254220078107014a4050107981c2c541200ca42134405420500c4040101c00540080c5030300341d84266130000300d400303008405d11500c1c60140c06c055031a5142000003000074048140080e04509041c4202800c184240f404000310032002d000100850408100080c555801d81c010701c3c0920140030a65001d640c48540440702d1015918042c0010780c82542220304842c4103030b00000321603001800340c4c2c9a2a0703d0100074480321030389151900869000080105000c04280301d2039400000850304103180c090300e600041e5441503001800303800101503202040800c01d0400c80b15150b040b84a914105039a0342c1d0404a80300c907401c0301e000c040710b070400c800641032a40e518180c0015100c5501d9240c1c00c541541c80484e649218043d803942d6001040001066046c2213810709402006103649110a80c64 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 74472933 1250 74471683 74471689
    0x70206060a06031a060d090c1203030b01021b060a0207150512061e0907030905060703060e061519051309020405130e1906020909010303030606090b180405040819030506 74
    0x1d0941c007040800d40390203040e080c2c2c0c00c80500c1c60390410204072019600c0b1152000c14034002c00140e50010142075a288002034110031840c5000741a500035102004850040c000580c1c554965407407520803038800310548556850000041e18811442d84101c07490207840c0c503040c40043c01c4c81d58001e0003140020441091450203403150b154080d80561320f044465044a88030a03403010035019651040450a00140c8068800e41c04034075074942000c1194498144020068010000c0d401500000b0701c00d00002001820001c01600c258402c01640c54170b4141c400c4d1142c03018072040d082a404001d400c10429040994458400c4003412200b0030060340c540c6041d04020030700c4020342070b000e1028201240800080030228502285e225030f445003400076080c528040e0001c2c413603400c2140d405840c00f030001c814158940c0c03004058403801d86992401544640c485c15031400f582c1c00170402d540f090340b0040c0140c2003a4000e80e421510032980b9a0400c140306002e008005000b6480000080d07031181004030510b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 74474183 1250 74472933 74472949
    0xe031e041502010e060a0e15070306031505070c230f06010e06010c03020c090606070b190c0309051e0a080301030302030a03061208070204110d0213170606090112030c080307020606 79
    0x1ca0000300006440c08855a88030758000b00221807503607482411a01d8013106118000320441601d04011145c039010501a000f801e950105640114061060320b000300c8443c801c00740201d15903140c523080c000799503a460030301c1005c0c0e0034144514900c148625000c144200580184403000c0340140041d58101300080b642e0006c01403246042000c1500490042500850101c40044d41070f5a661856518500824440c2c03140910080080300680204403444500c84105041d25801000900840004050072019503110f140d0103400d0303420a41028401458201d240380403903801754259064682c6586800c0f210350000d80c4160056040010000100782e418480c2c003001c0e003403000c0c05035050051500c44112601400b00003d0003150781d200d14070507036200703c8143d03110100c400c1415960351800d4801402c08071402e210b0392107601c0f0480202c0ca100b10004c50858821980a0500f05050780380c860900c01c0000c048009606000c00c005e9520003240c2c1c0a001180b14040c113400030442801d0035014480a2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 74475433 1250 74474183 74474219
    0x902040f0b0a0b0a030225050601140105040b0903010b04050c0301031703040b0c180307061115010302060313060b04090f02090a0c0509040c023c0f0601090e031e04 72
    0x20300c1c40d289800e400d035624035045070240e41443c01c0f1580c0300c188888007a0000d11910500c101710040c5030303602045050f40d540c0740010461040098417503599840c4d002c03207a281d607070300e902c64080340d014030061003048a60806003255050040001c103182240c0b10100d800c9442c107580400c00010000014011700c03034040022200b0041c4000001e14614041d01d03650303c0c248001d096542c18640000c0c148101080315010700003204801026942041d603120000782c030403a10b0700c1c070409050164042c1d00c40301201c920151412a43c0141005141d80d8500540c04042c00f000786040b10300c580d44e0321081d1102e44130340c81921030a43c0f107410900718078111401003000203e0002d002071080b42c240542507444951010607581c044806039004030308107201c0781d4143d04004609144070001c00c07468000e0150503500d002140b00da045180e203482d100c00c4208200640780c282601c3e4403409640010010408944180c1c0004c046070006402e4a0429002d0b000c40710043d645005550b211890208080c8a001290030b2001c0c06 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 74476683 1250 74475433 74475461
    0xb0f0f0f03040215120604021602120d201905101b11010207050d030b01090905090304060809120403030f1b0f05010b0409020a0e0604021e0c0d0f0503040609020a18090204 75
    0x10844101c03605107000400621b801e0241d6004a02c45620668240381903240540c003e0610307400002105406039a00b000942c00d0002401c5c106900e1550014812040c3d4115424405861205510360000038134198580701242c9920601492844c0c11030799100b4980407108042d58100c030341c0c0d03441e44024900e131460f612440040e4410481000082d60000307201e81c4604880c200880d41c80d140200607590884036074007a011803403c1c4000c001c04080040014402e42c2c1890306e90110316120b5803040f641c0c0d0220110204881d600401060010034043c04020600030740c9841d100e00840400e6615044590b070801e012500030180c00404c5040181c280103207404003c05407000c10052035990001000c0480b64491069003641440100d8403903203817a0110391103500c145020f20000c00c0d10f07036801b40c980d5116104540f4140503803481c0750401840b400c0401c881084503990242075440395210350f0700802d160f01c001c0f80d110300030130000240840c00100010702c0500c45080041c5c00406401400306544c03100b005101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 74477933 1250 74476683 74476687
    0x603050705030f130809040207030305010f0b091e0310020414010f140405150c0d020601030b1605090603060109030204110a140405060f0c0f061303020d0e010206010b0f0f0f03040215 80
    0x3c1480000c000080c0d01601152405420f441e150a2840c1740d4400e40188580282c000100f402c28541c15400c0b03641240e840c05080c0728540d503242000d09040c0140d1280d5035000e42100c0761b8115040540800361080880103084c0d03181074641347e081004a134056070054030340c2c1c40c640003905401d41e00040b10f240c1c1c0034410300303164448000740c45040341c00e48690300a541c030034030141c20099040003095060f10111500001216114115400083c1d0303103007000d00c03084403c1480d10380010040110800d10320303c5a0419115141070803c090200b0039130f600018a850f04119825000001580d00ca0103407900a000074444c5541d00c01c070203130300100110f00206080c4000c0c282080200803075101d03041100c400754490300e001c82d01c3d040c0380810a41040300070b0b5210010703407141005010f107031030065002c0701140d4420340840b10052040030094030222a9148581d01580090004110720101000240154165208010b1510a51140107440d64002141441001001008000860400221a007040c03d0084003083c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 74479183 1250 74477933 74477941
    0x60f0b060a1b0206040e01080f0307030c0201110c0d0602040f060306080d23070b0a0c08060f10050c030c160f03150b040b0301020a020610050406031509050304050d0507060305070503 80
    0x18094401c1101c103070100044900000c0050801c81c002e500810ba005082d6a62a0780e1114401400c19080c020150345026613200b186140310300008690420703a05848a28622405400550342c60030001c00c025024042c1c607020726980d41d40c2d01000708146101d1b41c40142c8560500c4084134031200c40b40c0000b002d16107001c0c024451108002002482c0b00742518100201803d940a00d501c1201c0e210214100f00c0b0003c42c9600c10818105070280c480d418036042006550f41d492011039820340160740d4203400052100a501340e40c02e0000c0c903400c00c1d204500700285003540e10050035245510046144c14603401c44580140c00311413400c9041e0003003c440e0124031040742180c60740b031030b640314011000350750a58410211810791150781084903614001802107480f608980c3e806506c40100321001c00f821418503601140030320303007440760800303494001c88520415a44402c1d220000d101410050b038903848180720004040c0e680c2192040c0880c03003840a40b244510b001006416a8405405030081c032000744208 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 74480433 1250 74479183 74479189
    0xc060a1505090a02030606070203070f03060b0a180507110703030903020306010b030c0a031a18040b0603031305060d02190507030206010f1202040b0f0319020a050f030d05031e040609060f0b 83
    0x3480d044100c882c030040e038035106c20b4005865441103800094050040800c00144070003640c40010413280940414460546107800300251480e850049440201c4000601c4650b1402035000540c424482e041031034441070500c110606d082c403554000c0f400031701118003e208505083c4207981c01001d06104450441c1000d88201e90b450089506078001c040c1d90b0740500c40102d141c140d60250942c406007524a074281890350903103140744100d03010b9407070345442004103606040000446440400c4990207c283c1c0341003000300090765004000d40c6401d03507028007100800c129000740c8130220502036161547d64140520700a41403c005a00c1a00f100c140100b0800550700709001007e0b0403030707044034001100c01d603100010308024441c2038169003500c690941c0e1150007400144000699008031040e80000e5a175108010021250116003900340e0480c201511419000b5805903802540201846800c00c40d2040052001c5404603403c0d1905500c2e5440d42050080501c140d522160f100c031801c0c03104019003408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 74481683 1250 74480433 74480449
    0x90b04021603080702030d050703050105040b0d0305090d020a05060c071505041a0c101103100503070803070222021c05070f080103030809120304080c0f24100801020c060a1505 77
    0x8007a09202d00c410010b5602c41c802e204841007030034000420042e505180c9d400a000300fa0900a0718061403a0250401c4280b07000881071904903450303076401c0d1509042c032007484030020741044d081f600302441680108295888030050918009844010a085840c01089551403194000d0000501004010600c90340401c52a048941812000c619594554045546150203404101c50b1582460025083c41098480d0003c5014a075802481c0340c05135290000c2507103d070f20510550f00103034820440039005050000219816078001c001a812140d443d030080026071340044c00c01301442180c100044882d01040c4140342c1c0003c8586000d4010f41d12654010b000008180000b4003803114460000704002030400c100007128141c1e1868684030f041c14070303002009822807074518036240240c0082100241c000a550544160322821014200c12051003801340600301418a45403000440004940702d0402d000500c3c80d6030541e001080d9901e13141c001801195a94035075004a40794060303042105030345680d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 74482933 1250 74481683 74481727
    0x80705040b06070501020a09030c0603020a0503180a14070906090b0105070204111306121a030d0e030709060e0619120305180a0605070b060616120e0415090b0402 71
    0x1500003403502080c1d0000d80c0900a210000b00035600000b12210400c1c0d0040c0300700b0450f40314400d0030003000d0f00c4580c241c040c0d016013101e810002e4020f00001d8070480d020348424001d10626426100001959204d034044143c082a540900340d20144d000c00c80f0703001504c6034000800c03405100300600014417000030b00c94890454040d00c00da0715481f541d80d40100807000c0b05c07442c01281d0200000305607505006400204070003c0003150343c0c6400300358842e030846104405411000203015140702c0e440b507d03041d40c030b4080b601045c9405120720f00c00451554054803846010380206400e031466442c00c81d0400c6401110500403403262036581c14100491000611703417603000c5a2508000c0d8403901c00a0100703028901d52094283e00c1a80c000c000121a608200103003159070107041d0995a5039034010500c061841046c030040641c1c0e0201000c1004036008100000124096290061402094000060645031a90101016840c40c590104904412807041080c00744003500c0550904c1c100e24191035034240d10117 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 74484183 1250 74482933 74482939
    0x10080c0d08070c2105060c040806040f2402030108101505010309110303070809030610050d020d0813260a151e1811010512070e010c02032a0a080705 65
    0x704007601001032a00c3c1c82c50103401500710080031030300108a00d466580364880191028040c910206100340c0002c01268144e50f02180101340d0358545a81c1d903010502d00c40e50540d07400d914107002007000707410680ca070030414408840143e141c1d41010344090038001c01600c1c007800300b4a043e46141100e484c80e400041140c01c03d003400a100c1e1201d080c5130074410182c4122613403501000460f5001c000c8900060003c107901035003181c80f0390345c1d0b50b01060313600703420742c081d496000c85a40e4180005107028031149680c0c910401ca2241402c4040300c008000e040560400c405020700c0200000e203807521442c10420050b0658000e216070714980d103c1c6c0108556006810300f803030351507020808000c0c000c980200e01418240500f00001149072a10340c483c5216680203c41c41c201142508610350f00c20401c0e10030428800082044c141c45035041982e0303d1281c1e5030341341d061115506261026070ba051058180c030b190354843d468825010014010043c06507010414801c100da00f01c18061a840050814140c52050b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 74485433 1250 74484183 74484187
    0x7210c090e0c041103071403010602030d0c111507030c0315030602090d1b05100903051c03060816080d180b070309031401021201151d0a050d0b10080c0d08 68
    0xd984094280b4070000d040c59089401c00060222a00e041c100a500c01c1c03c0700d0b82c0c0d81440c9946041c00c0b56003840f080c440c00005900034041500a000b0742d5000441686081c02c2074a00c800450b8565814010302000b0010410101010480304503014000c1010808451508110318800f286800451144030701001d01401d42c0807170054041e4450303c51003921180c0001c90115030001d0510004000089400b40da4090b10324008914883c80c0128404010350358818013812000f00c0c0071640990303648404a40c50100b503140c11002030401c5080c0142102103040c14910606a4201a100351600050b02610300800c83c07141111585ca403021000c180c1503036101c0a80c2c643e0f80999040850740f2038060b400203003445007149800402c01c0d50560050401c4c25105803044a01d03030365a400d5441c03244c0b403807203084003080c404c868002d0382c2c801c41a031030b41c00607200411042802d074480d4040b072540000c0d141c04844103040b40c002e000c80309003542c14a900900c10440204400c100c59004104052080c00000b8603103500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 74486683 1250 74485433 74485451
    0xc04060807060813051518030f0a0809150a0e15010506040308030c0c06010f0e0a0b0906040b0a090f0c080c0c2d010c0305060a05010809120901140c07210c09 69
    0x2030340320044c40300d070400116201c032000300c0803440c105c042c00ea941294540800e0000c00d60303400c000c4143c0e030a00e0f551407442400c002e030451003a00d03000c000404500141c085e13055640740724881c081d0b199020b44010980024079003250315120349030141090403100c115200c000100590b80d102c00485091b207510250030340e129210b40c0c040103010b009142d40001349010303180000c5000081d04940c14204c403005840c107007a90301d900200e00100d4501003402a007103030403800099500d061540010340056406050021010b030745074000412101c0c0d0000c0b14410b0b03901e4403031a014180e480b292654001820310441c0c1d20345070110821aa03076403000c100039482400c01c0c0180710003040c0703481d00e5001c90300300d440024400028181401401807008135161445404446000716031944640707200b51090724444001c001580203012072400c0e5402c0545440d04021003501c002c03080702d140402178107891603940000c005450170240c580c1481828000c0700741e424032010b04804003244c80301e22900708550884c000001c005074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 74487933 1250 74486683 74486701
    0x703090804170303100605090108041e05011e0606050a0c0b13050f1e0a03020721020a120b0c0f07020d03090b1305120c0607030e040f0c020a03020c040608070608 71
    0x440c0d10010740680c0080400d10040d502000461194680303240c84d0700b07040c0e2940419100e40c0030391003915000544800000e0005000c20a8180c20001d4031740d05180548cc003030342c80c1c2e800d5680c0700d0b20300011003014150f1440c03403c0450050030080c007001d084c100e0420741d001000600c1941001400740032085480e000c00c4160700f80350541f0381c0164110003601d040c0000300c540d403030381e40200c1c1807600c001c00381c0314290343c22040c400b00e8a000b1181d810750107040e83e1850001e82849855440351111440301d00c0400d0703000140d40308030102004000c80d00e910346034a1818148074a0f02c200080149141c110104006a032046640040300c55980d4112141c03075111940381001c64020003c0e800203039012400244111544001c0c040e050100c41c0103d8600744281a21583c1c29190300c000d020321034100d10b0500280c4000327801022031014140020b44002542e100458a000c15540c0b60440304000da002064100305155040c03001010060b4190303802d204030f9290425031940d903a140d228250800c014640400e074846 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 74489183 1250 74487933 74487937
    0x21903030b130e0105100e010b07080c073804030807120917070302030c0a03030203070b13021e0108060a140609040e0616020d020d020601060302280503011a040e07030908 75
    0x10b640c0360040207405040740e4980c0c02000b05886078a01c0c20036021002030035003200a00d0b141030300e90500000d42048050340d10541c0e02d4010300310f446094081c0800c04550036100104000002200401a00c02947c0307003c6900c08032003d60b04046a014000c01052000c16010340884200030303030280d02c0200064811008843c0c015442e00451140d603800081308a0782040060481c0960380210309441d1001da8003810040440598440180581c00c2441030f40f011460644071a40d0144d502c09401d080c0804590020720303000340e464074040018080354007580c12940d100140c281d200100b0303100f0300e8005040800075507824009004044c4175210000700310f00c0307544131a00107000304540f10b01124500d081c40b031014010a1504981400140308041e03880c158a8400a200184c0c41180d8000d407002c1e07405c184003140a0f40c0160728400110140c2d002200b14500741001d141e0440d0090341c6c9840c1ca0b541030030740b01c00300c03101208109000d0110a0005008401d01c6450050b00185142000103020742a4a402e44c1d2034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 74490433 1250 74489183 74489209
    0xe06030a12051c0204080708010501031a07140c032106031c1709011406030d050304110a0e0a0f051303050f031005030307060504060b090136020c030c0706021903030b 73
    0xc4820a003600901845402910030345004000f607e415544821034542203c10134032014006c46829004000720485001382a40c0240b5285402200504418011000c950049526100583c80000c94845001e2105030017400a20031049420042c20715400080d81c0340c2102090005020024410851a6010305082d00c504400d444041c505454001009070003003100d00c409a07a1259100c00180452601040030a040c0c075154407642d040d51119200c03070450350b15040109030000b526550100701d81032041d1207148114019580411140060720311107040c0d031000780c94216074808a001c540c0c0040d80007001d4400482c28203000759103d603507442ca0740c10000307440d522103501400700196250901229030050752003a07000340310a01070416804140710030001c0c244074102e4004d1042d0110b080601d1800e608190540b4403c50070480c440e04004814100d070310240b60000d1a600009419040ca03000f401007000800260004c1c2001c03149c030100e01e040f021400c3e40300604042d034030f201c02d6001342d03502c1d0820010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 74491683 1250 74490433 74490457
    0x5030f0c090a03081e030403080a0f060b0d0c11070515030916080a050601050609131d010204060c0c050402041d0903040f180b09040213090f17070c0e06030a1205 71
    0x2c195203080003031300c0c1d500c5040c0301c219043ca840131400307224a0100c1100d00869061f80d0350349496440140782d20040201100d4000084d4035403c1c00503c1e56560340251413045602c6100050f08036507824054000c60801d2003800e42900000400c00080d55000d03c0a50601d00f440046a52503a40c41e15582c00d0180000c02c1c5641d00102e104041040c500001d0783c010024403407c01c58140740d17222402c00009009951619500c4507140c18284010080e58010400302e04010350040e0f01603114001e09400c2e0f800170f070084000145c28641400c18840351480500061106443c11841c11741810809001448515000c80d500720031100410441141003044800520b1a1004043d0040e1548240c0c1d494407082c1c02007880ca2410140d100070700b407400c4e480c164042c3c3d40c01003410b0401488546560058090284155080c2c40080491000701722415280c00c6d5a80c03010480c20381e582a0752030910b0341000303e40c21110307030310814400b000110b07100003075101d840d02d40240b445020020500401c03103503445405800e041c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 74492933 1250 74491683 74491699
    0x100905031e0f030714060c0c100f021e090a1e1403030f04030b01090c110a12050c060103060b2704030c020a03060c030c02010b0d0206041a0c0d08150405060105030f0c09 74
    0x4117210400c1c40040c0708941041c1685c4643d00e5240c81381c0a5401b4682c6140110742290383e50459068003030344030b80740d010240d140240c10160440701c040040300c15104080754400c0c00064102403440c1080310800030301850341c0c03109443c0c5010210102045014010300000701e4140744840c0303166404006481f08036005e0700d002c3c8e541799181d1400307042c5410207108054140e42030000e462142406040c41c004280c12000003003041000079181c2c0078100961040c00401e0044c1005000000d1800740050741c0a10b00071103004c2601d0100905103c610147c800031001c4684826522850307011850906035001a0140b030414020303482400010310b1480c0d06d5000500c030524102e0001141901a0004081c44900d900200014404007060014404107c1c0c0000e50100003008184000200c20a003146100e48541403035003032207411102c09150428800313514011442e40c0e000c12140c80e824454000a42009807414000c40c1400070018029000207440010715032400000a400f10011310180c070100400244080703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 74494183 1250 74492933 74492947
    0x218090601030603080d090c050a0b030412030f2a050f041206020d090b04020307050102070f0501080c0c07030f06050603010c05070b0601030b0a120302060c090a180b040609020306100905031e0f03 86
    0x200c001c3c42c40c0c17030003200c123054140000a0180b030716501120842c2d0020b21010300d180c1d03a41e03817100b00301e01c4c4c088410020705a5415180400c084c051003a09410346003940c0e442400e24614107680e0690700b020405e4000c0000c01c0103a0500c1115100545084401600c0034600f8441c00d407820002900032031408299181c948140d0406110010407c035000d54001d0742031f240b20b01d0303d4200480c0c591403140600002c07000540e4080155500c59403007154401d620b46489801d0003c81242e03942410420790081d80c824000302242c005010356441105c2c2c016104500801800c00070b140c02401d107000303400c4040d0050220000060045e402600030700031240d001403060311540d403514946021950044400d81c018880c0c040050080c141075000c40d800b0a5000f80b4400b007251030540800c040d00380c500e05184010b619004440b0151301d80e40600006810681005030300e86c50420180840031400e001d4502c00c001c0a500100b100ba100800c800c03110342004280c03e0000f2010b2041c0c036113003054100c0f00b41242c0c032000031030b8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 74495433 1250 74494183 74494207
    0xa0f110106180b010e0f100e01021509010b0a1d04020603041a01090618090b04080913020315040b0301021602090a0212040602071202060408030606071a10050112021809060103060308 80
    0x3c800100005d80b203496048580d50188141a44104629600541440e00400c00d46c0e000712822421544144122207461008142c8c411010808bd94420407d030744850203462146803130081100a0800201d045660340a03001240c40c0b00c08000e00068024503001001c201400f0310108501040409681c980e80b465944000c894014003003071092000006010321000001a0640501148290814450300300e64035961111030030365000c042e000d6801031070341c201c1030424152030024500c51401c51021488402c41d050611007504e03482c0c0b80c1240300c0d0748100401c9151000c4000032920190301925180304603540c00e03001c40c009106d804001c0b00c806490004000c200111600184859442914090f500c03000b090001d03640e0301010b4030000c050080500000340d8034100071000d054254043c03e0001806003640810401a040a80f2018055410924103006a580090076405a40c0080ba82107217400388000c161400b0425440049124046420204060341c1c401e80184000d16000310102ea41c40e00c0610342 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 74496683 1250 74495433 74495441
    0x2030a09081b07060c08070b060102031306081e0403170a0209150d060e0717040c050409050f0f1b010e03030d05190c05070201050d0b0414090a0302010e030a0f11010618 74
    0xc86620302c180080402c03018480d1701a480b000758010050360030f0441310780d5141660f0b80c0080c1143d045100038008d80c0d205550890700203000340842d0300e840400c0c3c20060705072078080c40c0803201086c3c440d09c0c101c00e210000b6031220540b052412404d80c1c08145491b42c0b06410060300c01c0740c1c00154040341e03164140100307421b841d005010000d1002010800c1c00c1d0303030b21502500e04508544103c0442c003048480c06070481c0402095034000e00c1940c0c1c1200d01c0b502c450000341101c808010945040d440822505039500c005c10000b0341021460006000b802e0b4208240b41120400306105030400000107080c44660b2800c2042d510032000301030051000b881c10807a01940c110041d40c0040c9a00e0401108000c0b460107242140c0038107030107035120b0789400300341d1207940054048580c025400c80c2c3d48050141d106c01d20031045900946150340030f04840003807814020b00356550342c0c0c0500600d400070000c03248070715080841080c0649131030400f442c0c0740e00400001401031405521100714101c0d40b403c044281c070000c0d40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 74497933 1250 74496683 74496727
    0x6090501020613120507030309050a060603061a030d050c01110a0c03020d050405030d0c050f0a050115050316030f03110102030a0903031b0c080309191101091e060302030a0908 77
    0x1003110450f83d43c602d0f1011400d2140ca402030004007511180000c0c0511030350041500900a04020816010780e0303595915003202464181e41c115034410341441041118010176541104035164031441000140000341c4551903a964407050110005007040c01c88070a4110701c40c0d02589506e0152124601203018000000e840c000f10014041c07501c15203000c900840640d010790300041d009203001c0b801040d081d1203540300902c090360704e131180c0504801001c208000140166200d4400481c24040340303154501c607019542c00c1144a50040240d070360061600701d01d030300304403074211000031502030302402d0a4550f0380342c04c01222425400001040b50307100c0b092300f20403202440395070b08010042c84004054040c540070700d030b1007000035011003000d00450042c00155070450f0103101a2100b500d801c5040d801c08201224044407a400301040d9404a5a041210000145a0084070b10303117900000340c05090159050155900381640070011030340b04900c0340c0c40806c2580d4070100c034950f034801d4461880c9061240403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 74499183 1250 74497933 74497937
    0x160f050c090618180c040911010212040315021b0102030702010b0a05030f061f03021e0310020301060806010c03021614091308030c0d0908030106050d0b03010b0609040218090c0a020c0102060403320406090501 91
    0x1000e00d094030700c03044bc200d80c2201e402610307884141042c5071b480701c06580014a915038040342c110b40c51940b600288001d500491b4503800001e0184c0e0110140402109558003091107604400c01280d40c0c6040031440719440300089407881c0303001510b031640716101541034001039002840c401180115200181d007003140c1e1001142151b82c0321a690707001d04243d00c401d011301e40000e440b2601003021940107200101c581032090040c2c8050900303500341c2103031320926940950f0125118400c0c004503030510045450f04082c1c8010f0301a0605200d403aa1070b410b10014101400a0f000007850010a4022758090071602d1fa1140e00c165072565103145c018455005025103134692460001c1180c0f041ca0148286414030a01516030390512908808210007904000350001ca0651b45500900d02d507920300115610490b013501185881d5035005200a1401d100d030403580781550b00030014400881d4007c100d446009a5401034a040d94500da00d981c0d0188203020600002e4401c0440c01098458006c0381d000243c903c00c1e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 74500433 1250 74499183 74499193
    0x7080105090610030312060320040e030705070b22090203150a240e06030705040602070801020702010518040f1505030d05031605160f050c090618180c0409110102 71
    0x110070700d8407410140c0b40044102c10702482040060b001703014100c440c8000c40c00c001801c03592901c1d80c590b115005c50503254483c255041084d65440c05105218140b00e15100450030903040341d446995402007070082e4180ba800128507807410681020300d9494050b6428050b414882e0f80300d4008001e50800d03210740000909a4002c0e0619080c698429000c484441c0580104000c0001ea000710755880341028000300131005801064a849000065005100c00d41d01c02c1c0d9620320380b400082c208071503600700320050b2740100406000350380d01500740d400549a0340d211100b0240c4c03040000300100b6410307580201d4582000a030000e0402c1d1040240d040707a009409841a40c0e940c1c4004071500c0c0300440c0c1e00c0c60780358200070f6460740d040e1080018180794000d007000e05406490b25110110012500b04003100d0940c00001000020b05005801d5500890159015020a95000c1100c1101000185020004203000c0d0306004004804c20265890000240081241007028200400f080c81c41e11081c50152041d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 74501683 1250 74500433 74500441
    0x305210903100203071101060f0302040c050a020c0613030f060501030c060c050613020103060803030901020309120301060e0d05010618060e0601050304021804020d0c06020f060a0204060207210f0507080105 90
    0x48085803040c84008010700b20320701000034000000e4102a2011007080240380000c0c12400c001d100750405003007068044900c1c9891481007000391514583d02108010091001400c0540c00040c80c20409074115091a2500340041d072102d0590300c1640b001e8815841c0c0d1208009100b10383d40094180e81c014200f4020051b290f51041d00c0ea1018414000d0580d03000500054206280d2441c0c0c0107468070524000c266690340d500d00500d90340040c0d4011041e40d5001007408a9107104010840c801401c905846085600d0000b0240045c6103d100c100e014002a2440c0c1c02004020b502ca10064610003005400c026180d41c0281e0042007140241c07071510341c1140c0400d6043d0701402c1603d106540c0200040e203141000082c3c51042c0c400034100b01c1c1c1080d2540c08440020708862400300c050a0b05600812000c200c22024034942130380a00711103101e5104110602c1215404200013041c0d5035601c103040c80030f1040846045850740552809082a041c0361000c00070448003080f010202d4640100901060b11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 74502933 1250 74501683 74501743
    0x3020421050a1a041a0903070605060d020904080d0c030c08012702030703060f0515090d0302010b030307150c09080d180f080102090a0f140904020301090c030645021302040305 77
    0x41700342c444648591040c0010780004240d038021541c000c001621408000e42154089000500d040e1411101d000d400720780400381d49180e204d00301840b81a1724041c8401101550040c1c0b40760418022440c10b1078100e088012680c1e0090701c804250f083c0c040701196a46420b04001b80240181c0c022903a941c0c0200200180c01e03c0d010f1140c20f90302c4410a60549006030f40d2003001405203290304214259500c0751841c0d8500e81d030500140849500517444120b104114041c03d0040758032801d040341c1400700d000030512003c040042c1c1500d00c0c400608002d00140b143c4044100700c90303c16480600f44c0c03014160b020a5043c01034000d044560380c00d07211125241d440b540f0003100e802c000c0c05170003820100b02100900ea85000009a6041400580000303407542c02c648540312044219042505e10a44440091800065002100c6201c1c280700441e0300404c2044075590020780003190300c0240b1489095620825946c030280310786070294911004668036030340d0b441c255441c1d040c1c10100840c0d80445010f8012282 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 74504183 1250 74502933 74502983
    0xc0615041a0307090c020f07060804020a0e040321110f070311030313110f0603040b060a14130903020f07030501060f05040903050a0c030302040807060c0b060103020421050a1a04 78
    0x80d00c0140649006410b00c0c0c08103009107041002c005c1144545c031818020080709000b5040a0002a501c80c00da500e020b0043c06200a07003503001d540e07103107041c50400c404650721858160320401c4d1044082200300001d82c01a003c3c20380d10007030b40d245180000740700412040d46002006120b100c3c1c2ca5000c81000c083d03c504d9100d000c11514081d40d102c6550100300020380d801440c2d001918002c0454043d0302c1340d0404160150030403682160f100091200b4480070785000040d00c0024100011201403000083e0080342e031801c1c0d503403404030f941c544a070100b0382058000c1c080a0840e00f00e43d003c0301c0b400c55503400c200d400303010300b4030800704031540040c804a05400c0a018007240e640d015145c140c0792881051044070323160303607110064041560078040861040c4040c000c0000030102940c801c44125504c0c1080c10000201401c82814180304100400c4560100c070440303002090350030100b00c0120010b007022800d0504403240180103d0102103c03e0244030403c1d88540140e002d100700c0c42c400303c14000c60040c55 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 74505433 1250 74504183 74504231
    0x102060408030103082208010c030e03131205030d0c021b0a050d0305090d050f030d0b0a0f0303110a061407020d0206010f12030309140102030f0c0301050f12030c061504 74
    0x441c008100600210355050b000f809520303041e02e1000c00a241c1012849915049a0494070780c0d40d4481644074001a4540107402c170b020000d40c05980350111130032110f112254140700700c4116100d6114a001804005d10681d00d039500240c070300f0302c01d02e5004072009456017015805a03880e00d4604800003101c1c18a44c0305003054a0000e4200406c0b10390688060b03490f50024400c80354800d0740e140f00030700040c4084c0590441c1e10031410045403250070480e4041b0039034011040081c00740b903030b024041041c0e40c080700c01c8001712505420315131481200c032035032a400e1020156011700b04c1c5060500d854070100218405034400c002c96803d841d148000306c4000c0740c6540c403e01c50741403c405900800d001d45010700300b140c41e26070300ca418005501c412507520500595544030714040c0e10303503000c0b0403c242d8a44c48002c840c2d102013a1074a0074695070410340000c65034181d00c3c0340135019124200d40c0040c102c100704100c0e00f502c0450001c0720b80c0d6103440309007081c0e144501d00c401c500450401c0b9181045502c0c5140742120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 74506683 1250 74505433 74505443
    0xf050702040b032e0b010203090a030204090804030f0807110d050a0b0603070e0a0506010810150503040201051204060504110117190204030c0f050301060e01030807020f131404020f01020604 83
    0x25080a580810001c1c1081d07922582e032602803907140000c000000c0060070342c0700d0614000602103102d0000d102040340c43c001c0f031030380c1503410401041c5856a281100d810135260304071000a03d800480c1050000c5000f190001406134121042400a00c0003903030140ca4031798405c09007400b50020307060920011501e040c6006110340d012904420014045400b4150702c4030000e42180d505070340d00d15031100da18101340c911a21955035041400300c039503070040320a9400300702d4000c440030142c0360824095041942c003580384208400800810111781c490f000b10b4610000321595a400d605007820f01000808043c0c1d0100c030403210590300803c0b194020344001091180750500410039554107068841c0507030070030101c03540640e400c00000c40000c02141c0e6050180c606d60030314550040c1010103050840d00c00b074004a400e42450070040001404030011101210303030656440700784d82804404504a8a1090207050340c1c58107007680940150306400805210b68021160004482102001641ca441c0151000b80c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 74507933 1250 74506683 74506687
    0xa1a0c12040609061118090c0306010804030302220602060f0109110711030c0301090f030905190b090a0e07030b04050f0106080403052d0a1106070e010c020d02100504030b070f05 78
    0x421500d070f00c40a441c0d4040c440c0410742502000840c6003a40c4102d1902035404101e04800c48541041c0030390581c0032400c820034a1030360411100180c005140108001c08140e00091042404030300c2e9800f507010801042881c404054540c000a502c1c0c0c00f0071120102000c0346e000c00003035540c3c2c8038010b08103c0b030b405c00f003000d10380725607510382d518104140d82015030035100f02c0b5040e40c0c0031b071000d100b1002d83c640151080746810f00180381c014004d104690140303114821141007000c03c0f40d0300f480b80d001128404043d10b6a1411014046051104158030850100c07000c4804c000050303400d40c2220906079000c5804100c56a1031480c003969208003800b0b448009035048001900190050b001006450741003000918041c2f404102ca0040000c2c85414605903c0081081201ca68102c100062010300440180110340ba252000030540117049070b4803410030910043e42001d40d215002d5408250382c018000e5801c90440719006400c3d03a20610080303c0740c0c83e00c40005503520b442203207000c0e0702204e603940d858 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 74509183 1250 74507933 74507941
    0x40303030c1803120c0f0f0b1006030c05090405060f030a0c08120c060f10170a02040c03051b03060a172b0206061905060307030c020c040605010503180c030a1a0c12 72
    0x855005040b401260b00c1b40c44003421901140d1041d100812040c8200d241046c5841d00f0541d1802e0460302d688031030306140c02c00c00035201d03283e0000280c80301000140c90014896860000040301c0840e90070000d500340c00b46419002c103000300407880c3c20a440304c034001c4501c0e941180030196620311a80310600f903640c0210000c50440300c0c07501305883d0131200062200d183d4548175441800300101001130519564800f0600c10300b1411329005031801d0a0150078204454904202d150420b402c0000d000c0502c6480040040c0c81030352941e01500c00380c00c9a00740741d42006112484142d50f02402c0d4441d0401c1c02d0404c1d84103120603280802465401200e501818650310b0304070500040a0002c0125403221480303d40108a42d2181c80245200d1407465802266000210401074100000440518042c5081140c02d0040b66007120450750020003040c00354a020802e54109402d280340e01002c01d9250042c000341005021080c845941006110800386100703848105030f150306403140c0b2809034807038540c80c400a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 74510433 1250 74509183 74509187
    0x106110c01050d150b0c030408101109010c150c030504050c0d031223070c0201030b1512060301020c0a03050c0f06061e130f090b0a0207210212040303030c180312 71
    0x107812004c86045840035034a60b2031917000743d0404812600698404a0100f00c82c84080110702c20941e98030500b0060f01c44441c0001800d4403400c21042e0600c0f0f40b540c004400c0148444204d10005d08052042085226059005014007003d650a480511500031461400c0c5011101e007119503525888004c40c00f4046a03901c00074020303c0d00403280c4201050700c6181c94a00422009104840b140c0d100003100d001480050203c1e0a4080d5481c082c407a124152154403020200702c5410341140c50100540d40d440c000001d0191042000d80c2045016500610f8101030300507000d841e491180074181d030800030030761000740d950350f50813101141c0c8245c800d103494042680111082003400d1002e03040204000d443e048081c144e4205884003400c45903143c44d071006020f0300c801c004e504009020380a5140c5a42500c40100d6a0740e050b2404d00701019144c4110080d42c000c101010315940110750050712503541c2c0c1005030040c204040500301040d10603107500050444007c4d00310603070703500204240b2100c0d04010b00b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 74511683 1250 74510433 74510441
    0xc0c02010f0507062c0a0203030405041503050307140d111e03070507081c020c09041b030b010b030f01051f0302030c13030c050301060815010302130207080a080106110c01050d 77
    0x1c90a00c42c0401c4160003080c0640244000f0300588820220101621910040806240d01c04214180c018076850f00051750b01004a2b41114002c44000c100510002640001c04046a00050161000043e11001c000c1658031030301510080c1c3d0295901c140c80c1a0058600c0b0540900611807070700030482c0b01c03840c80304c104018000449800d0440c4d081c001c841d41c2e01d41c034080c1c0e182c1159496500240500030a02c0c900c02025180940c9440a0040b400003030f40842c100041c00b81c402092200100346044a00c1d5501294800441e08031603400460750b034070000034945074000d42e0800d00c1d078440030002088600380041003081100044244142a0380b1456044009400103011441c03560801c000b1007500d8111810984040e5000341c00711182ca40ca00b47c105400c6404541c82600190001001c105124200340700f0b10341120b4040c0c0d10150080c1007684080000e100d5600b009005817004646039903d0b9501010050588009849812002840460b80396032524101080c41c0011400c000c000400074507500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 74512933 1250 74511683 74511707
    0x30303020315040903020c0306010605041409041a04030f09050603070519030e010603141005010f090c0306090501030b090f010e0a060b03071d041a060604060e010e04020c0706080a0c0c0201 83
    0x29010180354400b40090142c5003801001c0e07005a0142411160625007030040c140145514140f03d40341920301094a42c803040e120a00611401d08000010144184002a9419828442c580046071700d03180ca00584900149000c200c005010200d01181030700740041143c3c010951a101e00d81001c000d4281c090303201c011965031008041d2224103405184809000c0d410103188540346240c4014210b03c910b601e0300c840c0803d81240319007403400401800703080560440560b42c1e92540451000d8000e88203a0292080f03030b22100e050342c070b004000801d00502181140c001c0d008201030343c003a810700064103401e036419646404265000580c280000901c150b0100c0c001a40183c1510102942c1e003a54240000c800840c03c281244400c0800c020000300c20483c0d1084103100242213134600704000803594500a9001d89018401c1001c1c0c9200380307a0052100e0495444000c000355038a070002c00e00d06481c1c801c0341c0714030b40109003503c021881f17148403401114200c1c0c0e03180d998190300e240381e0380044a04203980c42c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 74514183 1250 74512933 74512951
    0x2f0d020904110a080a0510061a071b0f030618051b0f0301060311030f010c09180f0c0306051528110303040303020403120804030804060b0301060b0d090c0506030c040303030203 77
    0x103900340c4225151002c406008140e120040d0005c01e41c1c90800c03604143c0c400102403105442c01c2d0040c4a50220750001c5165800c1c02c504858842c112031404800c00360b084900d00b031100c007010328001402ca20b90010441900d11600041c040240d2100d450016041200002081900300c05024401103c11500b440d1613084000c1001d80c6500a41d404242101c56030b07001034800c10380c03400c103481241c01c1c10405181101e14080c02080303003104154009060b0f42103030040485849403002c2100b20840281c0160000c6582c3c410b040107841c0d060070780900100107a02c0394600984900c0005140e41c400c17081561a4060030032900d030580304a6212403001c10001200040c28415070030740c096204541000954800c1d40710751001039980d800c40c1099000c98848500207004c00043c1010400002c0e4884a900d401c140d01820105541c041400005c0c05860543c01c81026064003140d881c81100c6242c000c0d01005000d034580803071103a00d51091006d00d00c070840d15086205010082080017911a90003103078010249 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 74515433 1250 74514183 74514203
    0xb0a03020603090102030a06080d080604090f02030105070f020628090201020a0b01171b010f03050a061205011505040207050d08060d080d0b0406050405060d1403090306042f0d020904 80
    0x2a5000600e950803d6507416043c0e94080301304183c03820940304401c041c1440100900004c070380d00703400805251004080301c0c062600c3d81400703c03c01451400c09060554010000d0120f843c00403001001c851a0352a03000040c07042e40082a2a00309481c0f810f03540510301c000c000f800c40c105190140c05400030313030003ca0441c812190310401040000541d107000c0c01c900481c20008808801009180400450040c0395807260040c1d400900d81e00981ca48100481274100802c0960300d50030881d0040155a11840406107022841000c006040d400076901d84200307075505285584a03401d010407401070a0000300b065000141d8400d016010b80c1c081035110900904100c03c030000c03982c90703a01c3e0b0f03000010702244041e29036480203224942801007001606041e9010455813070858006415640100c401800042c8440241e000000d01030040321428a40a42150440d040529100803015002c06038441d00300e15080442101c02d0540041c0c1712850b03402424044803c0e55502040a821005081201c0749140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 74516683 1250 74515433 74515439
    0x1905100b1309110309010c080f04062408030909090703050703020d051603080903010c02060f011505041d04020a0b03070f050d02220801060902030402090c031f0909030906020615040b0a 81
    0x2c03501403055244010910385840e07041c200340603420b680d1080e2103407050202c07003010841806003680e20740380c1c0b1680100020458045c00d06900b4420307024800030003120b401c0070b1004150303d02d0001c0145071100c810f07116485103a132828030b100d40301d220341d0000401c0d5402070304040001d0f14090080c1141d642c085c1c42035896054018500362426156035004070307521600401c14460310701e02882105034007c0c10780080c00d420302c0c081e03841d034160500500a0b5112441503006a1100520420544c1d01404101e0413200401305840c3c651143c0d00004c4a00320300c15080301d140030400d4842d0b4400da074013506158a6001141039522800e503031a4010a4070217144550170b200c0500d000d00320306220001807005021141600e41441d010b5401e45d030341a0002d0b050700b801041800010b855403000307280e0045920030700700e8403615401c0c0192206c6040d10032081482912075008540811590f004031915440b0742c0b0b42c4140c4550f0345101b640c030b540040b40c44801c0d90300c500c1d103001c0c00d40c203154000c041d0b9010014500385400d61 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 74517933 1250 74516683 74516699
    0x2a0405040f08032509060807020f070623030c03060301060b490501140402161202030405090a02250302030d0b0312070501050a0b010905030706260c031905100b13 71
    0x344c0c00c2c0c0941c005020000c04008080e04480707500c0d0440031900c0a418020050f441441d6254014415481004002c1c154161220710703984484284109402e03490317969003400c40c10b40c49590400d07103061303100e5403a0130800104019281c080795444032400e0203500034803043d001c003140342c50b80c005615010541d40090504601c10300108048020f240b0000009465060203180d40071a01d40840480c012441000800c0c0303150581d5001806e99076005002e40d141113910b141c101e0550080d079109642100c0345009000101ca01d58010700382500601c091007500680d00c00d1040e2481040c010050003507007082140040200c1030380c110349a130f4000503007140e4480111a4040070a54410b15056509035900c00034070201071500e0150760380107071007441c10701d1086041074000313512450300d80300b188203101605442c101300054028181901e00709032200d80500c0d01e05142506450303401140e00481c0c903401c00c450100d801410b80301d041e0003244416542603085084c080742e004640e000440c00c2c0000100e42c0c1001510031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 74519183 1250 74517933 74517991
    0x2806050c071208060a09022113031103030f01050f0a080f030717030108033103060207020103050f010f0612020702090411010206010b030411010516052a0405040f0803 73
    0x1201038032000350748034164201440160244201181080118424000d442e0740d050505400c1d10400c1da001607848450007072a840c80c002038581c1c81501480d49040240c07500000622000f0a0300a032110300410041004c0300c0d03280d11044840000b44225880180a14200030340ca401c1c403c1005030a5040e081c1d160030046140c02840700f0090f01c294000901d80040011015104542c00d400c08001400c40d410007141c0764903030040c0d0744007034801480350703444208070b40c5291103410b000241d0500e046129a01c2c0d007031643c0a9840103e00342d0100e0b09060203d000303034899074034040c103e595203a81112070904140046441d01340c01402204940d0f001d00465001d0b990703c00341d0600880c850b0718405600001e02c0b001a0810005074041211110180100b10204071a0000050030380c82c02d01e002551200103180c084044101c80c8000b070054402c20381148004100d00d003021040e503208601601c0040d503c80e00300020340c0c00894004002000702164078002076a03030340c051500039290b20380b2604071b1368007002003000074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 74520433 1250 74519183 74519191
    0x914060d0906050916050f01080601021f02070c0608100608090c040203010b040905010e15010f0908030c010c0801090e070308030604110c24071e030e01020c0a06060801090302280605 80
    0x110343da50140448010300708080c1e02c20000c0d0301c54640007249080e000070108a1452400c0d41401000d00000780e00b68828001141c1c114885c6c450600c0814214500e8402900030002c2241c1784464181d004c503025004031130080c442c45684c00d2250f20142024821244503a01038440c48140c070031032025032a2503a030360004d103028120b0144aa601c0f1441d00c14a4020740e00e042c0c0c49840f84607103403800d12005800741440303070751580c00c00c0c01c2180700c454108800300c43e02e840707545c0120700d1400301051200a18006402c0f035071440035150741c1e5003800d0b41c07070740c601c4000c0319450070a14486900c0034100700009084800074603401300000303100061408442046000942c001207004d84542c102030761040c0e6003448982101411650076000010b2071801d80c2e00a051031004000c0040c4406a0828402070144690403003403004031248025134039600d0f0950102d54485002e20100c034001c2c01d00c0808500c681052148411041e010360050081170840225181c04281d0000e01c040151100a40c0d030f000715415000710340c06 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 74521683 1250 74520433 74520443
    0x12210210090614070f050711300f0309010917010b0d03080108150c03010e06120106080106030c090c020c011b020306240d080d02210103030e10020d0914060d09 70
    0xf084036481c0890400c04004044d82c05019000343c1424a190b401401da4810030390000d1031810725480c04001a0006454500c2d005035210792042c6e07480011510b0503d08804041e01c4100d503404200e1400c0b881d113900481c0c031904d0000750013500402645022440a1030702c0c40b010381c00016510010350110b14071000c80107041e0003051194004005422081107500301b0300d074107062201110304020058102d10710040c402e42410240741c201003a050f41e6802884000c080411008000e40c1d82d842c400507018200d584410341d03400000110010700081d0318011805285241d50152410426082c015540405140780c1485c07144103071b02c000d20040c0c40030130035280181c0d0001c2008030360000f00010040611303004031079107003e41d4030041c501e00010070070400d4035206001102c0240e2140c9040c41c0b0907544010404140d010004444000414181c010f034940e030381e601003603e0300544035150074426690f80100060310f000007200b149041045034010001c0451924005001d9494500c0d10011130f805d84030310310b0701a14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 74522933 1250 74521683 74521691
    0x303050307080f0903070b09010f2901030b0607030c03020a05031219020702030703060c11120403021207030c06080c0403080c010c09050a0605030a02030a02070209071206122102100906 81
    0x1c026400c280019444160400200d001d440c061843c59100d00030100014001e9103014081509480c083d0003042550001d04020000c24480d02c02c1140341e01c040144081e81c04005003500e6070366520034041c000700303d400684520310340341c8655411904683d44550075011070060801c29070001e0310601c000c00001c240324042c000c071403c05c0e0300d81e00b064034072003201114150700c104040c0b0016180403603e4000c80c0e8004400107500107444405480f00f10710300c80a00402e0080c15100b0340110400001f410590b0300940d580180307075840c2091255a40c815000c09400c45640c0c07441008000d1140c0c07a05a40725000f400320604007592035a8821720340d04101c0500005035100c9180c106203075442240741c0000c140c1101c10f1840a40b8001c00600580b0016110700803e0b42c000002031101041d0717404541800b5400740084440b4607100100504903103880342001d4600741003817000504d9503013101032502026000013503598040c840a001d01b080d1440f0410f02e6080d4014140c8442d00d415080c0300340ba2000d401800042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 74524183 1250 74522933 74522941
    0x11b0503040b160c120b040b060105041205010e070504060e04140c04022106011404050118050d0804090501080109170c1e032d0418061211030d090b0901031a030703030503 75
    0x20880054130340081c05c0f040741e01540b40d0f001c03400d01090260007941003620600141c541c44012241c40c40381742c200382c0c00a00c100d0800400c0006c1580321303c1e01000d4070000d6805072500d4004002c2a070780d4038441e89480d52040004600443e02d2403000300c038400da03602c081b11441ca040c0c0c0c000c00c0603600101c0c1d8039441038200d54201d507403010380c983d034842c1d010100b441d0140c02d02d40401d0360410300e40518059141042010304041c4c814600700b102c510050000107001c0c40110540d881c2401e400d92040c010303411010305083c000128484140500d500c0c05038000a58015400d245856036030a401c2585003032200e10a007541c0d4410030500a81646410310074101460f40c1c1c401c4420304411000a28080011006841d14000641c0c0c2091041da0f06480c5004440c1c10040c3c60070758224060301c3c050300005401c00e00c3c403407060200006c0748120345011109800f0355101095403142a0f46084080c0318080c1d0341e0f00100f0003000d1a43c0310341c1c000704c2c0c1d651035441400602c0c82020003007490540030b90003c40104000100744 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 74525433 1250 74524183 74524193
    0x307020a0e09010506010f020714030a020301050c0c1c090b030c0d0c02010b0415231314041106070f030e060705070b09010806030a05070b0f0c0d0207050405070e011b0503040b16 78
    0xd130364080710a08001c4243c0e2a0440c000359110858440e071b290a1841c803113078811595050241e00303881a0014001d00150400c0004e4241c580e01c10780a50b0b80341d128404070001c000e404005540190a46611116211403400300c00705225440100740c0d03802c0c050200180960442188503100091a19130b00010307030105080103000884050b000714210130b502685041216840000540c3c0d15044c51960516820640c103000c00c6004c0f12404001c0743d098104212101c10100b00d4545510075400b9a01c8111104000403d000c110701c1440302c00351500c51001034400200e8041d040e421440180030740b40600d04000358071080e00705000c1e5006030182a00014100509682c0700c011144c012a04074064211104181d4074940d44420070306c142841d19101007172200200507000160380b4030700400415107031071008008009444464a02800d44201d1910b40840c031254030a1405040104040e103070207980c03141c0354211002c0400001011603c80c8000c003c0840c14a213400302504e29008400d015608441a510305 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 74526683 1250 74525433 74525441
    0x207050109030221180d0f02090702210a1718030408030301050a0e0603031b030d050118050a1116080922050109020f12100b0a02071707080a0308090307020a0e0901 72
    0x1005400d5a0610a400d5541001c0c55240b080000c100c0760401d450764146400c030300407c52400003a40c040c000e48200080103401140012030700da06510b84902001c01982140b0b01d50146012000000d0101c690003544040b0715009540c20480106015880461104140d0b1555010b901300040b250004001082142030a004600c080d00580041e58018507159003c070f6607901071140d041080b41300c80a189814070740144220380f030050f9a00d405001e1580c4502c00e820601d11741810f031032401403400d0b0024610300c0c1248620740456951002940c03800c4407101118010940c07401c0255240202004040855600c0b048c0710760700c800304542020b00a4000c06817580403103c059200c81040c0c0d004100d019900466081120b10080140b002103840e0b846401d01d040b4151883d030080c240003000015034882894000844108940790441161006501c080300c007070700d420140c8940000c5034070890800c2c0c0001c0c0a07600560b0f00042305800c0300d0824100703400080c0c1c000c01e03d503c800390301d21038501072120f140c40a0103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 74527933 1250 74526683 74526733
    0xa091a010e1807050d0b06070b0403020607020f0c0f040f150611060907090207110d110f010e090106030203181f0c03090c0b0306040902031209090106080f04110402070501090302 78
    0x16900c44000980c6907a20b064610081c83c50701000000259028803191316030210301c5000c406466261610540d240005010340266000d801512492001508091000840340914581c0c41c0190070098140c0040c03000203a4007100341a4060707114501e2511407086486003400040e10040c00020f150f00c1c00b4006454040154010001740c0c2003038080140c06d03d400a461821034030f00040050f91035000d82480c40340c0290b103239103003540b040301814258107008080303a110007802012103481403032102c910019514540503014040c1c110a00740c004100c40f5020b0381c0903503400100c5401c0b540444404100031804c0c185000e4030400c82d440301d41161a198020b904c1649002059420104602140d40d1211541c01c50948140000104004009401501c4a8000304d00c09507002e02180c0d240407a039200184030f074112000c010300916000c000028110700c00c3c0001740c002e1800441313030707200380c0c9075900c926034084603440d551340d04240c00b00b1002d00040c00901c15040c00700c0c0648e000d018032103000e00c80c402d0603003c809 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 74529183 1250 74527933 74527939
    0xa0c051c0e090702070b030709180606110d081305010e060c030f15130e070f060e09060306060d11010c170c01060e0618090a0f080307030c0810030605060a091a010e 72
    0x30b4104812581c0010b100010b481c5034441540c0c403903546550072a03103240260004203041c810303008882c400200c590400d0058903007645461011811000c030343d554481c64910804c000580c50008580c0f00181d500c80c080b00302d80128008184500344a012520709581519164030041001003001039030800e44415a41042c0703240032115540d817891000030b0440b420306c6c500e007a10070740d0341101120800e410055440140f00005071689115980c001c0900f2403401d00c84054059844600002c0740c038940881c0003480b17184014000d05070744150780c41c0c2c12240c0400b0340d041411700ca504c11900b40892860149081201042d0503019600c1c140c4145441c02d41303a10398080d2550200c2f10090154543c0d840c000c003030000c1103000603241540c0e69840400e1408000d110041d29100b40511290184041400211311030b04094400f409104810310741103c4030101216429008000c0c10070510004441d500500e4015400503e2050b21680303aa00b0b070380407104410700300c401c41860503010840e256000100068900390071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 74530433 1250 74529183 74529199
    0x180901030b040209250e03120903071208040801140402041a030c01052101030501060303090b040b0403170c1f1d030a0806060412030c0b2503020a0c051c0e 68
    0x350352105150280a00b000f4461101c1c000094040c071840841503a61002c0004440084e1480b00e40c050a007600e00042103000340a2001c1040500b900901100d40500c005002040440d10340f41c0000203903080c07048219102c1c0c000308000203038a00c00b402120701e0240e100e01400309a0810388104005c42e40340c00f07075140c9032503000b006203c03140c0d401194040201d1401c4c02e01c0c07551030314000c0c41801003000040c46e408c90446800000310521105601c0502941d102c0d032500c240701500d850b400401c2d40290301c119259288100403e04c0010450051441440c0105880d5801c02d118042201e0a14060424040c00240c4000b074800703c01d401801462549000c030124002110b40c039500381510f911070410340d0b10038028000041800741c0c1328801140c0083c46d80801080718811a441c0050100b080301005544d4640f0b1203000c11500304620381381c51003284942c0c40030340d1a03100340c190540207500101001c50a01003000c49030404901c040c09a1201c101d400758111241c090305120140400c1c0005407a240207400c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 74531683 1250 74530433 74530439
    0x307080906090a0602030c040e0c03010302040e030309070302060706020f030a0902030705040204030302060604021b0712030f09051810050a0305030301050a090b0108070305040804090e030c1b031f090f0305180901 93
    0x10414110035600901c005d640e03543c420540c08a207100d503502080150f4074410400401c0c811603409581230740d200701e400b441080c8000100580e20300055030740b001c450700014402c100624001b0005d10704284280c0000d401c0c121003119031186a003003141d00c01c00041d10b4800b0300c81145001d00408020341822a000c46c00c00b829600c00075034880c001441c0e01e00460340040c1c82c00b11345010114000d205003001d81203803819a01c45d50f2013420080010b4040b40815503035001308840394011801082554009420184d00d00044000c0c03060020020344403071144d03150000301203410b03241c0c8403805015601400003180d80394904410300900078400c1d4000300f0f14078a000303d2882941c0e80702940a80203000c62501184540310303030074404500d1040f540110358013443d240200d0904070001c009429981200d4060381c24910310400b000d20040c1020f12100c0e89a0004101500d100c96036440a05178206135040000d40085c40c2d41d00d11030320000400c004d0300800d502288402050303200301006c0040701402ea590b4201949 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 74532933 1250 74531683 74531701
    0x12030c0309060d060b0304080a030605040501060c03030504030306080f0708061608010e0c0405040915180c17010b030a1115190e010e030a060507020f03040e0109200a050307080906 79
    0x22407019600c41c440016140c0318507111a00b250002d4444041c0e055a41d04044c50700300006e6010302c40325000701e07040c248001014609031040f01c4c102d40b00794541d0381c05410195012401000010000c4080c1981c94001051a9808200440f892529070008000f4903052501580ca032401c02064038000d0340013a0950018a54096002030458941d660f48140c00e89a4075040c00c41800b56401040d00680703822002c030288002c0c500c440000d072801110030040082c1c01007400180400605020303041c40c403841c2d01004450410900c181d8210180c100028101e80d080d80000d04103c520300080d1450b01e00020f5100130b40c90048845900c0d6609441c5a03880d220000c1912200c440c070714040441403014015101e02144d0280e08a220b011600605458508004e890104014a420307559040184207044a1480c84140001110240c483e40080b00c00e041c0e1070101300ea00070381200c0c81c4040016901803050720040076540081c100e01021600d41030346074600744000401c40c0070000c01c64516544050280107041e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 74534183 1250 74532933 74532937
    0x1c0f0308011a0f070311070810090b01060c020906060d0902060d09050d021b010f03020f13180207050a02040b0604080f2107020906010c061104060201050103050f0a0209070e03070b0a05070212030c03 87
    0x76890300b00242d00a442c2c511b006d0402c2c11a07403100107103000788801460b40f1a925413207110f14078458900307000141d80795042102c480d220707508004d401503d8a80070035031928100340a090035510345000400c0c40074159010489940082d000381c84100d440f00c1e056800c001d01806022303d039007600d1000301018450001e600400000340040130b41405280b41581d910a0300c603404840c1c4d69040342c007a583e914801703894450440c07076480c42411826148140480e20094280c022905520f810400070f184041464007000010108140a90b40c012420440010810303024025800d81114001c0540a802440303110040d07a103d4100c040051480b08000d400010f03503400841640250080c64030051a2045290090049c6490750611500000120b0001582541504420705032407284c17055592121184000c0c1f81d07101d02d441e00082d1f00156100000c0c4501d0301c03036078120703000440080480d00000c2d6600304004070356228041e20340c00111300113610341c103506003480c001815610010041d45801401c4504035100c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 74535433 1250 74534183 74534197
    0x501051b0d09061508030702040f151a0405090403081f03020603190f020c0102090310020408030307050c1501091410180b0607150501050a1203080103021c0f0308011a0f 74
    0x70030b5031512240244107042d8000c1050302411951100d03001c0d114904ea99030303504045c2040744030303d0034200350100600721401103600d40070003000c82208443c1040020000130013099440701d0144400d110000e039a039281c41c1001e000364003907129204107040510580081d240d651200d000350146403041000142c41e64001c50341d100303008500150765000d00005a4001d8440c10051a03805400031031010045c0c00103600412071010101d00b1502032080e0204030900b07034000c0b4031640c41160800d20014810602900050801020700c00079aa000c00c20361101104400c4280c001510942d515410355001c54071080c0240d1304001c43d00c8065840c13626010300c0024000a0328076200b11651221914401c03900c030300099910180e40400d003507682c000440d0030003000b000244140792040500d514000b500a0700070907641d0083d40c240d41c4030b40e4a40c1c21a000d004000b0702a805031a541a005004070340898080010108031510a540f002559454100815400b200310180700c503500760300300103607240550100d00311450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 74536683 1250 74535433 74535457
    0x207030c030e0102011b050315030f0709050621160602060f1f0e01030b06090c0708180105250b091b21030a02010b01020106060512040f141002070501051b 68
    0x500c00d40c030b004074003400680c40d203151400800c90740c00d50465000b60245104420503e0130603803c4078103004059842c0101460314460b81c2080800b88003003c003076040725a02082c060002417030303407e03e000116201c1000b1280900c0c01d401c02d480410000300001950002090184024141810a400c0c00e824141c5d0142240c2c0d42003070420303803802d41400190b04040c018103049076003004030b41c5d40e030030008504142214824810851080014210031005080d25901d6070800102c1e0700f010128a003400b841d6042d241a50305001d03060000102c0000c5084001c3e450b500c11561120000b26945407100c000c1d94044d01680268020786c80360351009089841c44005400100c402c8142001034841402c1704d221045602c9420780800600c8180343c5805402002e00c075003003a4000c012035aa40d860488060043c40b14450380801c1d40c0780803601080c4802e007084003480c050307451181d84900c2440b00b1894000b600d4803400120340c012800700c0a03c4000c3c4182e543c42000b4204410000c1d500450b41b4510744504c0b000810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 74537933 1250 74536683 74536697
    0x1b030206160203011b03150807030b040b060d021003200c0a0204110d050126011401050603150301020310060305130803041704270c031505041e0c050301180207030c03 73
    0x10a66500f50001c5442c5c0006004c41740e407044c0b007884000c01402c4540074100c2e0220b000300d4009168180018040300701c03608000b00710350f5621582d44040c3d48070350151070f00f0703806010b0001c0f54002d40e07905040d00c1c54a12558500180150302c0e0340038419280450300e202c2d0070103103040c0b20440da10700300401c2a09150b98101d03000074030340702c03045444415406646010301d42c4520344400800d00c1054080c860070f100490f21a800c1910361809011800c5e2210251000c0210040a00420007414054051504216802d0800d1180c2c00c5a60229089800c00c46401041103040c1c2c0c810001c0b1609442040d03000210701c40090107034040c1d9100c90a0521001e00010100904c6a500102d2030030b2040c1510b0140c0300b00b5121074803414145c40300344481c0715051018164a490544401000b41c000e102300b400b000c0c00d140c04600c8041c80c0c031007044001c00c0c210b4502c50f841c400b020b120720000c2c3c8292088040044180d1111a01e03541010303401b0800c6041d08030240d5516104124080c0402d030085c0307400b01010380c50703d0403072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 74539183 1250 74537933 74537977
    0x90d120e0102070c090207020a09020307050909040312090b1501050f04030209130c0906060f030510030201080603030f0409020712170402060331020907020703080904050a020405060c07031b030206 86
    0x3802031054440190261100134070119030301c50140c000345400b034022640c80d0200c6866403c840e08a104c1615030f20040340d41008062031074140f040020394064080c0c1032043d00c405041011074140d62aa44048840c08071240401000404841101000040c02c1c07a1150514801c10310a600138421400080d22403008000021314000140c0e8010141030303485001043d88990f140c0f52100600f100c2d0181101049580304081e94951092107810300c1a2003e01c040c5000c40d2131a0019944040081c01954060104018440018000030001c10040c450104016500c080d1350905400c120f24001d194000c2002641500e4408062044440e0308207404980d041d5483e1560310341145000301c400300440c1059058170700019200f000031303013400c5c1c418000c0c3c5882e181940c4600302283c480a55000052000c2030a0101902d5070406611640d802051031380c005290644880001d00b568214088420480c0e002210a008000b00c201402c2c010320000ba9807030081c1d41c01d41d40090300d0360003400c03415042480110891 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 74540433 1250 74539183 74539211
    0x501120302070314071a0406080109020903060f0613020a08040c06110303070813021302070303050a05060102071205070e090610080102090a0b09010c080f070b0c03040201050a0c0303110d0204060305090d12 90
    0x1000248040c9039000140c6e4031042001405400500c1000d0108101200010701014036008440d80d03220700501411241e03559548061f1015400b8240c42d42000c114400c0d07428080b0980b00805003400280c86403c400c0c41c003442d10102d60542600142d0070003400b21200b4400340c4002040d41e4000d501410320401e02e44e80c2d070010032258000440f01a520083c9481d030700c03460040e107600515095000741d8003401141d0358540c2c04001da403010703502140140e2010400300304d1101e003940c0c98008075102d1401d8824842d03071034000c42201117040d54950816082030060000c0304080d046d07403500608080009500700034007840025519809807140c1c80f010080000c110761168803e1007000c0d41d441c3d02106480c0c40d040410416034003504004003c54a40d510035011500121100046e01e00c90f40c0e050f510685001c80c048001c54032090401c0701182455241c0c0c2c403410104840802030080c1e01181e00006072214030f4050b005007600c10203080122140c000032541010158401c5440c0e61944010070003040c610f02c0083c072 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 74541683 1250 74540433 74540443
    0x1a100c1202030f04060302121609060f0507020301020a020106060f080402030a080c210d06050111060604091a04080a17100e071202030903093d03060306050906010303030501120302070314 82
    0x541c0700e9000290205d10540c055014104444400f1042241b9a8030225104400c11a4445a80118000c4003080000714850310818110300131602d00340b4240780d075681c082070a9820081c8c142c40580d456034400e220403684a440d24103a04450b24000b012420a500404d40314102128090100c1c0c4001455180e0b0040c10000403031541181c1060015280001714611215003003092a000c8642c00e04100195940c4640b0b49102d9096240000c0c0c51943c035034601b080028081c3d10021074030781120848000d5a4900c0c1e1078400e20440c000c4c5126560fa00f001d030002030620b41801ca03002d1160003001e06218000b6010b0005506442c058640c01c01d19803100300091715504910703d60040694000020070000000c040050b12004405a0f5000c02c440020080c0941040981c2c0f04082403041070040c440101e80014000c140b0300b4450300b00040e03c5c80d01da44800c825518100c400702100e51105004008055051003039900400403d07494600300c10b00d5a50082d01c40c40d0170322019001040c60f5000040007141804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 74542933 1250 74541683 74541697
    0x10b090d0812040b04030206060315240904060b04050c040e070c110d2a06080406021312030c0510051513140907030308090a2a0b0c011a100c120203 65
    0x508208079180c145007407040c1e0582111708138010300031040070031070034200042d100c10614642103401c00d950b5103414a42c00c03003004440b0110350b40320710340344548000d485050700107020b6805100c4c042407041000b400e000940c0d0018091281d0f50340d0401c02005810034460095801c102e0300e1415401100c110300f1f206e0750b040a00f9541d0b0364840c00711504841008034001210b11100700b15004441545003140b081c0310503058a100d5000030401c80307000a00020805e6004000800d40640002078854940d170280066105c0c4071800c80104d504080034006105003041690351190b504203040c01140b4002083c40090600401c03403d01031210000100c51407011908132a00b9400c4d880000c40803460146403541e9913a04511003640850b000e0b1021030507030302c00843c4501d94a5041342e044600d0141c1c0c0b043c0740403003070300101881d240e14101002c0804d40702d600200501403503080000205480b009160740d0440f817a003400c80140701c7d2035401481e507900c540002803080019080181c0c101c0f12a10b40710281d00310b1050035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 74544183 1250 74542933 74542957
    0x9010c05031305130b0102070b0a230d1a130e0c0306130209131a0c090a060f0207060201051902031b031015050705100506010309020310050603060f010b090d08 70
    0x1040b02d4401e51019800b0b10122a002c07910314030343c00244072003501280c150601041c01a004504140000b60380305c001000455141d2910001c40d001d04001c4003100009c0403401c181e102d100040c0c1e0070711840f180c000d580c0d181c0c049a914044aa0f00400014041d44030700c00c1800708661584c018200c280000d128561011901409444c1203241603400b203c085240180c00f24030400d02080402c3c06407000008800c0440c1d801150342c200305c1c40745111011042c100400180003407404100580a645900c10620010400c5440d514908141214064200120394001804580c906810080c0716540420004a0202c0700c01c0016903944940444030002c64907040700156525000040c00146e6080103103003021103d1248e4001c81f61107941c001103e8500c94144d0140050303000c42c504132000b5038030f41d0280d900800c05041c0043c940c2ea25602290800344d684401215040e0b0b0b62017000b20a0506210707c56005a041c4007500440d03060413440245800340100b0680604004492002000300307007811545805800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 74545433 1250 74544183 74544187
    0x7090305071d091c03051302040903020a051b0319020105070803070e10030e0a02120c12240103170a12090b04030915051210050d03090608010f060c0809010c0503 71
    0x1480501c1004032000b80200e0b210202200081d5084a0114103100b41c048004000360401c0701c080400c070068500900361140c0d590309030310a88016652446450032240c030a0700034100d00201824985c7c03c01c0146008596882106420f400103550041244200c20f000208407800303101080c00125030501415200074114000002070100050304100c42022aa50898061003118421241103081d1051001001c04540c80780c0400c500501c0c08194098039004400229681d0449040c001081d4004a26554001d40c000150801c209880c06c004481412040e1445e03080a5140d40d5407080440014000549500404680d41644910601d49181d000c00001000d11200310b0504103003c9405042d81c086000c1a01ca110001d01c140c01c0c0700e141d62810341262145400d22800301c207281200030005003900c0200e40c00c59000310f40e60f59041020008140a03030b42e01c601e000d04100700034016a034184c10a400302e0015410800c5860785c082b0503246a503600c0000c540e2030301c1500d001640d0094498400400ca8040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 74546683 1250 74545433 74545439
    0x40b011704142b09031e020f03030d0b09010f030c0b030a0e100b030f072603041e03020102060f0408031503030712050901120e070501050309031303030206060a051f080709030507 78
    0xd5101541c0d081c0e2040000c0180c40890a4403052190710004000104a106000c000d41e0144e8039024001d00123817140070203040d99030000b030541c0d011205e001c50b410303507074454aa420300342141c90360702406100c910000101c1c256110b010080300644110100d15038008002104030b90150400042443c241040701c80034103008400c0405041e80b1801c0314080d105c2c0104054000e003001550300b044541c420424810200c0c10350355081c04a43c009551000c5200c02c100000c0e0b58030480c4240e480030407511344107a5082c0c2c2548002820f184024001910041e0200c0038032001c034401d0b0044a4002819070802e1000380e4080c00442d00303500031a44c02800c44036914480351622a084401441040402d999030b03402d020703181895004641c00b8000c100f0b1f45500c405004d2190b540a000290381101e40390007140c0c14000308049048045826420840060b000b40702880600d0414500340009000c04483c00a038420078640c9610000107410003001c108299039002c9841d203801943d01802842e00517058a0301151 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 74547933 1250 74546683 74546713
    0x1080304090e03031603020c03040b070803040b0105100e040c2607140a0c02090705070b130201090506180d021c060e0705010302090109061d0d0b040201020c040b01170414 75
    0x12070701c2008601818014032449040e00841244e2191055604140c0d540d80d01c0e1201b10000d400c6460311003130b144010017001c50785c3d05103103000e0f000d024802d42c0141d07900e1a03d03141c004103030344040c0d1045d17004030480c290154100382c101e80324100d141e00a4400045401c0e1a034400c48031220003411002d00040b103441806610341c9400300da103100c2e041e19103030040d41c0701d008800015184a040301c44800900b81d0380c0c0050040c038100400307035044566840d081d8240300054903400d80c2d1000950300034180000002c044821960407a820800611080328011b04000903d030007a0080342c40491918400d41c291865002195162120101121415851009280244d1905100401c8102a00001c900c285400001d40750310a00880c0e1a10606079210880949041c43c1a41c58086a481c581030604207040081c1c8170351542c0100b4100c45008401c04c10050034180006401d02c07480d011942d00a504080c141525a60421020380b101c82262000d0401660355080c00c00c0c203520314251417441c030700a155034808414 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 74549183 1250 74547933 74547937
    0x20c0105061203040302041119020703051c080a02030601121e0501050603040c18090813061b0b011203020c030102040806060a06050a0e0607030e04050c03150a050a1e030605010803 79
    0x4040040200040d44030402000000340c104424811280d0003088103200605054020b401500302d100c0720030742020074455442c0c900700c5182102c0300040c0d11062040041c00000c1011910075a03c0c804644084201d910005081550061002c3d617899000008a5001c1e4414814400051600d83d020000b10514040288030b414030b07401030709512802d00380007080d64035000081324016540102e0360207581d4a4103030362001e84214815852002079880c001c1c9000320741c4400042011454100c07440290380c0c20807a0140070000c000320750281c6081c441d0b40d03910004000303012490665a92080305142c00039549402c80c82c11003000300c4203425500100e00001c0300000010401d009241c201e07500e03105661141c2d02119103024503080a000182104000324850429a00400e02c281c000c0c45c00420031003110001c42c09070b0304199550f050a450010800c00040301710000040e00b00e104a414460581c85c09000404401c0b060086c071030f00c10010300fa0812940303403680310390380250742c40354003030006603590860740307445c0d0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 74550433 1250 74549183 74549197
    0xf060c020f03151005030c06070f03020f15040b0702010207110f15120708010e040b040303090201120c090806060406030c05060d0204080f01060503011404030f0e01120f06031406060604031104060905040602 90
    0x60101c0c4007040d131b0702d40498082c4a00e140505802e0400d5110b89560a85455110302a01035016041c040e030100101440070149000070055100101d040c00e190684040c01c004208034210791062088000140c1c49154254032110101c40b401c80d1084482d0000760300a40c60343d500e50a2146c001011880c0350b58041115228500940f40c83d01242c0ea20102d000801c902154010315640c080320000380028041da200056660061401c2844401c030103041c0c0080311041d202210200d250244100720115042100a0384080103a500f40851481c542e0f03a6240c211140c00760912a07240403503803c00c245400e42c1a00c00408891b0b003150f0000d000186518001c00060003154000e50030305494140302104981401c0c010f681c07507640c111140d841d4800c103c8803607840c1c4110a04010700358035000c00b901443d000340041034410510010301315255151000710ba2030070841d141c0311038101c0410004180c0d100030075141120f41165040700704081400001d4014401c0390440c82606180078280828031209030b000c0c02030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 74551683 1250 74550433 74550451
    0x703031211070804090203040f170c06070e060717090a0e01030303050a02070209190e0d0216050907090e15041b0806090c041a040302030f0d0212040f060c020f0315 72
    0x24641a41c440315800344603007500030f04402e00802003004140055801541d2044c060003206280b5038055891502692101d0701000c00382901180c074040c410740501103190049190304160f8a100b44c04800f0542da4001d00703901620b0500d1780742c20302c100380c1920000c80d840c14500600c0b040e54142c45074034440120381c080c0802d4000034a1703c1c000031180d40b407500c01c0350349442d0014503100090340d070154105440010000c2c00074030b0310345501c1c8003020f0140c03c00050741024070540280404903000f17404171490b084154800341c0704d445030b04c0a00180039080350380802903401010840046556907141740d50701c0441005c109800502d45035800072950ba4001c0340c01e0b2009015981c1807c0341d1248810041c011409440c070004400080000304040151030960401a02c080d04050781060b17a650002401c00401d0800d4143c55040101d0f801c403025414005080a1001200c0da00e040c0741c24400030514a0701140198014084403d80306015942d40341e00c035410030340006048503001c0340c03400e0054611440580f05020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 74552933 1250 74551683 74551691
    0x1806061404050f0909010b090f22020d0212030c0607051306030c08061e03010e0c04110304051902060403060203070905032103041b08060106020a0506060901050f0409030e0307030312 80
    0x150800c5000032101295002414569240d680c4401c004a500c0c01618001e0786640e40c440f10849501d03001e01491007299181a001d082d4940818238100c032424442829280c8840110325400581d64072814688894055030f0000b029200141741a03d540708280f24020b0034440c502c01c0040b620390003002044400c0d042101c1c10521130381c03103800b81c0c10344807403511040128403040005100740c24250b070308128040850003804403568800c8042401c451207000100c0c22600842c0d1124032504080c01180d44140010b10218030314a4280c544548a00c0d0028209101d211440e2040307040d551030b401510081d54020303108542d242461000a000003c1901ca034078000d008402d40c09010345000c2107910071400d5081c000a01c5e60b6260b50324540d03180c00d50149042800d04030355001c940b8074802c000c0342c0d01a000c00e8000f0198175185042a52814000500d818071444040d801801262a5090001449007040d1400b24004500c5c0c0b8041d101000e04905240d018414407100109040e03003c8a0710000100002c4204 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 74554183 1250 74552933 74552957
    0x912060e011a030607121d07030c170a03030c020a02040501171608030f031f0b0301090e0d09060f0e031606030e010b09010510090f030b1e0106080718180606 69
    0x29140e000c000c030b4050b490380110001900c0507000d000d0515041d4040b141c00035140c030325007180d4651000550f0f0781c02c0030341d88203039400d204100028421801900692520300030011040e04190390f200308000c1700030200741d240d41c0e08a42c0540200304500c2244e50003001031019684035469400c0740c04113280601c09901c0f90200c14a20003a12042140a84010781d0295261201c4280311030103d43c0003170191241c2d8008007c9021281c4842d8007840c3c040c10022035015500e52416401c401034400102c1c501c6c9071500801c00c2121300030b0700000c2c0101121814141b55505110707800081d1400d00240011356007500400d00c1050203201508c411500380c1e8016103003000f0b0340080c00d10103800c80780a40074403900004a58010f0000345010010041d00102034074020040585030905e104203041c17a540215440c43e01c443c180495400403d07000c14418041e0403490f4100d6140030001083c2a001802c2003050102ca10004a2100e920210400280031440100303800340d41d106d01000c00900c3d00d48503100008054880e0a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 74555433 1250 74554183 74554211
    0x408090616062a08040506011208040f0803032406030106080c1201080607030e0304031205070212030c06160516060e210c010e12070303050a020d15050f1516030912060e01 75
    0xc0c045c9403c1002441c4a0b0b0034842c0b03807107040d404032200341e0354000107120008001ca0828141070251000002842d00e034144040851030002c0810859a035012114104101984503c010342e81110f0292901c108a502e400c100c61945100d600e600301c0d030808216001281e914000a0a140513400c1076600304100400540c84644034043c42c0802444881070140c160f24061043c00a85200b034001040b240c5d140c00a440c42514661001a281354150080340800010104608072066140481e00f0702a2500b41c00307849184884c90b040714000c01c03c96403004211030000c020850440c44012200c1905507004820300055810703042802051903135820a0509a0041ca0200700c0c86031801e00320768998104100c0d0b5400b6009040010040c5000a41c20711615442c1a01d5010b203c03010300052014180c014104000e201281c0b02c5400603e001d003070103070000010340c00000103ea48040d0700e600300140c0744c3d0041c90112100805540052510a5015100303420310a41d07a1010001500d040002c000580c81c0d0114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 74556683 1250 74555433 74555447
    0x402121b07150b03030c0604050a0b060108040302060f0c09100203030f0108070312080604140c0c0d1e0507080706060608010f0504091509020f060406090f0e0408090616062a 76
    0x4000d011503141d15400000c2c41140d000580d100000800f501e04210074440ea00f45080000c8506580c2e83c0e021004103010b0280a111a603000803083ca0b10b1000c51030984c9010b9510789003c0c1900c1d0300340103804005120b0350611001c0cfc400288005015aa10380c80c9000c00a54a0700140e402035011200c0c0300c000500d600f00020302c1800c0f80d038444d8640810010860f0306640202008100542054903030001c00c0318400c00c01503241c0b1440c0c0c411802d60f22034007190301052034035100380100400e001484c405041103101121303801c68540c4407407401d81d0381d0f000d862828030000d0152100040c10941401c001084090b0010601d45c103030f4102120031704080341c0c2c0d20100426211000f1000d0321084440d42e01c0d10349010700b6001b5504043c0007409800c1915001c50201d00c2943c401d501260005594005c240034030000341d850100100100d60140a00d418551100544c92041381120f501c14a00051110f00010214201000203a00104104483c500700380e10040443c40e100c1013005120100e00220030280d01a00c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 74557933 1250 74556683 74556697
    0x6170703020d030f1707050c061f120606080601080a1502070201050a030b0414010306050a1401081203180a03051809041a06040b0312090f310b0402121b 67
    0xd040e518000c41e2000e13120303900441c01c000200003200d580282d00242d200b4029014212a40d90140d841c0421042d03941048000b03442d042108204440c1c01c040c0c08a03059440060310310710320140a5000715450164000c01e1150b00c4030300280100380000502d680003040c8456198010002c50041d903100200c140101e10400c07000034007040c400d12648042e148030394040451950090000200e185c1912a4450400b030709a00803100c0f00e88820420402d000c1d40d00500440e480744032601c04003035040c06c07075141c0c0315500b05440c5550380c10080f0000f04c55a20824401c005c0017501e00035070f90f5203007085c20028000c0d070180d480001c850320700960400c100d007005d40c4518810f68012100005c04032010f140b1040444d0041d000b00c2e405030b101c1030110b01c181e8043c41039194101e08058a259183c1d8072000f44041c41400b003500901c10103182c0d02e0000500c14512185d00086480031a05041d0340c1c00305402d00c0140400308e00b00785c10920206558408400d039032203d0740908071000c01541c03c5005000e02c02c4403485900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 74559183 1250 74557933 74557939
    0x7060f021c080711010e010914010b1c0807020a06080601020706090819060e030a09050405010509071b0611070807150e030d0906090b0921030c090d1401020d0617070302 74
    0x3908054260b03220710301080d0022460f2a2482d6103030112110903003900e0101c174001360665503d40004d8200055451009800540003009020720469400000d8403400388080c1075000302c02c0310b6240e6082144400458420302d9004054008094a50074002d04000040321a0f50141c0714100c0c0208001f0702882e680f03400c40c0d4400d030040016403030b4040916210b0540d20802c82c0e05c992074412001c0510700c2407000e4182611641c0d100f00f01070380f400d0200710a403041030340040c1c042d01c0001c00f0b000c003d0364002c0c1c0311000b0741e02e450a1300c001400c40e0700d080380c01042600c1c19a8540740c008507200302005481001080801c0c003420b0302c2c1c2894912511620200c41c045501d40950f030f8010021011000c546800a08480d4050fa900060343c8074503403240315404600301c50300b02168000c181c00c180c10b0342c0d032a0222400c0000018400341036180c07411014085101d0340d41c1d01c1d88500300c580800f80c02c00c268030740036400c2c154004c0000e54490740c0104c1a500034013514055940c18465030400000740440009120040769002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 74560433 1250 74559183 74559223
    0x80a1a0904080706060b0a031e02160803090a120804050f06060120031b0c01080a090c0b090402190305100503240612030403030504050a1d041101051b07060f02 70
    0x1d9554000ca650040e01e003150510b445001c0003a2181c86640a030002450300d44020550f0f8141030342d0011814101000340005d580f040c80700e482105803107454009810b0b0302c680b955a40341c40c4d01400f0b51411145002c0102828580d0805030308a0340d102c001103010300e100c2d000312143c119078054601e07140c80045600d50300103248640109010203c01d00044034005030841038078508604072010803045001c1086840081d030081c1c00312251564080280c9601400d500010040c0d00b10384ea4600482203039130310580000e42d40101d600a403590300c541c1182d036884c0820200141d03541ea03c407409406407008986401c00d0711000080011076003004580514603c0c2142c0742d498038080030040c01d20700d01d0005405517400800d401810483e0103001c0005001460098036803507182c0d031030502001440300c00c4d0b820051040c91030580512007088040311158000e681709000810741544640101c61502680440004041920b0250030502602050300c006459542d40d800d8000c220399103050741e0f0b40119034001140c140d8a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 74561683 1250 74560433 74560441
    0x190909140607230702040e150f090703030e0a180905010e0c01050708160210020106300b0411060d0501140402030603100b010e151909081203190507080a1a09 69
    0x80516012903c1c0004141c02c280780c0d40c0200e001c03207070045e0203607a082c0e00c4503c041345070103034044c0d0040d80f1800c00c4011800600e0948002e546139003952000034280f2181c08003501141d6180c00380700e00a002c551810350429144444040083e00307130144d06807415460035070f04074100e41c0c001c200300c0c4107480c2c10717180c840c07401e442176541c4040b07030784545c080035085074900301d003000113a880d00614502402c56500201e41c20b41000b104480102c81c070b030010b5007034040351f084030224200c0d513104205009400070020702441c0e4a50400300c040088124140c3d42c40034000658200c4141d0b01d6010b941600c00004000644c0428401440100d100c182d81c0140e25501101c400036100103e504101070301e00043c9019401d0320300740b40124030205510308001c009108045010303003100d040c00540c018070307820600e0030708603130b0f8a00304519490b0031440307025039001038000001030405400c02c40316544c45510310408100300e2034101ca00030070908007079803d130a8032800c10045004030340d42641200c1d4006001413a07030f06031f612 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 74562933 1250 74561683 74561717
    0x61902160608131115040305030310080109030806010809010609020c0a0510052512090f060c0207151209080708040602071d0609060f30010504050615190909140607 72
    0x4901c1221340c1d100a40034503c00d50000c0501c080c1006500c83c00042d6143d003441119541d2201490700814003da14240000e030110760302c04034441e000f403401e08002e11991141151180549540d42000c080b6600026800d10f00090003d8908401d41c064419112200130340000101907600c140d0720308082c4481034403c042e02500188200c0c0584c0241d04082e62064a410010300a940754094151180c082c0c0d011070764280096801a640300c600d00d880945003150030b11605000c8426950480c80401c01c42e0042c02d109a01d035644030780c6055802c4044262101c0042c44e0900043d4401c0c024000180210030ec0000c2e40c9008883c144841d0b142400407010a54030b10f020301a04000003070040740c0c424130f0401000c9082e1905011440d00300000351804a0502403032030b900c411900c0310480300d49640e252004110104101145107600304446600321941064402e0009010110a111030305c044a070641e1b0006040005074461784c0c21621944c0f204070710440465007951039203401c5422002107154030704042c0301030f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 74564183 1250 74562933 74562953
    0x90a020903190b04020f030c01080f131b03031803080d110918010905070c030c0215040b12010618060806100302160b01050f03240606190216060813 65
    0x4003000d411030714403108040c01020341c802c1a8070251062200c11080c4003e42c10003421440018009038000e00c8007844c08800200427400041000b2042c1c1d8082000c100059a1b00c40c0c0c0c12503c54229550f1154220800c1c16424020003601c000c40128020500120782d0b001403a8001c07041380d40228006007420300c2884000068001c401d1031100c1d500b82000207240c43da032022408100b50782c0840043c581903052074505800c0b01c001a1001c0d081c0400b515200c4002940800114200707a815182d000841c800820358070845d00440d0041c410500001c9000d208a00e188120036040b42d6441d6211500c10710781c102400418041c60003018000786070200000d845041542d020036552000c0d1a00502c1d20b140e46410312a0b02030402030440c1e00259842c0100858501020214107100342207018012144109820741f0214552101c904407190344200001c0d051ba075900181d5008050f42d00c55800e2088040000a48520a8504040741980659404181d151050240512403240014040141c624a4498030008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 74565433 1250 74564183 74564197
    0x403120201060f080f010b0319020f04021204030203071704030c0918020a0b070302011a030613050c060d060303171b070203010f1418010b0303042304060f06030e0606090a02 76
    0x2540d200e41c80069030300d000f40460070080c01d591000d084907414048940c1d0179030f4650150644641d02c26020036001d60030410141980c154100d4400b2104040c0d580410040d000c0e10035560320500390301c41040145500071004103c0184a900d5064804080e01204034050240d400050481c2412550070300c108600d5901c101001c0340510f0f0901000c682542c00540b403410990000c03441e030040480c001003096024000c51003400140e0101c0030300c000070000030039580d41000f420500000b60710403003607081c40424400e01002240141c00b00d0340d01c03880305010f000a003181d403004400007402c0d1a00c941d0038110101c140c5000d80c0d5030345895501132041140c80ca1b440d8008001c241e0789550f880802c520b0500e03071803242d504c401c100b4042c600c051b4a08403444810006030810b820880384d0400440034919540441140d09032400d0b141c01e91750409100c219288181812001d581d005032501c40042486402c608003081102c11030b903814408008500f0b12503031254000da400390741048401c00465074030507150b0050251 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 74566683 1250 74565433 74565437
    0x302070204090b0a150509012313020d022a0604121709060601020c0109140402030a06030b0f06040c091a0307021507050409110301080312090f100b0406090908040312 73
    0x100c4041070f16105070b42203042d80d1000ca03907070383d44150f9080c02ca5503050a0004000c102d03014141985001340351991015005a403050340200b10316001600c0d039580d00c526590705840d520464032480100544402584560050021440c102180c504824a44801280c198900601401403501c40380c0c0c41c4610700c200c080c0100c06002141592040080b5005891445001f50701c00600403400d04000281c1040b0b942031081c0d040003404501404804280815058060000e0b500141d44e03075900c00c2e508000345210340004007100d65142c280001400d56111480c050a8100c030102310060704a101030310030021621071141c83d00c0c62216070244d402d41040142d0fa101140b40144c494040001a2003007005404640040c08144003103000d10a40c20144922100b01d4155000985154140030840d03a80c1c4c0140070050b401281500c000804840c030034441d5010021515084511318419503c9240c0a407490502d02070007a458290001618003250007814803494000c003c0920306070654484210114941a4441c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 74567933 1250 74566683 74566691
    0x708070615090e0705190e0411010210020708090a050f0d03050f0702030109030903050d0203030f0a0203060d02030601080a0b1524071a092a0402160b0703020910020a050a030302070204 81
    0x140460440c002c0c60083c600400c060038682e401c14007082040c00c3c0c2c1004407964480f1114051200354216407402d40c1040c0c2101c00401c070b41ca4079400403031610071240189240c15001181480400180b440a080181000c451042d41a5216028068007a00040c0f50030740c07009241590502003401180103201244d0040360341841d11000760003003400e44142d840b04070005031a40e00104144002807292201000d040c0c8048c62850905041c011000e443c0034003a4100c03c1e9002020402d80d603a94240d4504459019064605560359800b4a940316050040d007075403085101800a14111030440426041a40041c11210000d4000943ea041d620301103501c110b00820800c40301d00495000f1101038104509601000c04a113407140046050040c0103180705242910a43d001117140e04042929072007200640300141ca5100010034071a003546022000382c00346034060184074160342c2c150000d091610080d1030315400700b1241d03c8220ba5440081c400600070750449088580003d100e9001440040d000920101d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 74569183 1250 74567933 74567939
    0xf15040b0403050601030b090c01081b0c06010902040f06030b0306010306090212010f06030611160305130f080307020109050603010602070b130302030f010b010f1704171e18060708070615 82
    0x41820303800368105441c2e83d40900d00400800c10b0507c040c6078080c0c40003010f40300e04906000040c045140c081c1c0404500890b0300107800c3c408100e04156081c0c1b128034000c844095075280700010080d4058003980301850307180c00c400300c1e0715800382c0900f4155441c0a0001c4c507a5030f1031500c0308401049001012603002e08120303080000c000090040780e400300c01641000640e5499450507004441c0030000c110b0800c0014003030900d50445081c0080c000701c3d0103040c4156200d05000c90490b0404041d048580402004100891408000005400264402e0303c5510000b034440003089a076000034441c01c0010707404100240000d0b003080000d0301500040c020204106522580042e00b0064001c00040c46603540d404602003e40e0b10a85030258080141080211038218030301c0704225610040014240350340c100d01a00701c4544890454000c0005c445030103146100704071a00440e58072801d40d4a0000e40007100ba024140f401d082100c04880d80440e06601d40f1516655400c098585010a0000502525400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 74570433 1250 74569183 74569199
    0x150513050a050c010e01030b032a120106030506060603160302070303061a03070909050603030906070f06090b070201051e1609050603070509120d0f1107050d03080106030b03010b0f1504 81
    0x12078200d40c03044000e48000c07008140014001420280c44c0c034100341c04d0000d183c455440103e024441a06800c212080f4020009034440400b20f100c0d040c02d801401e00c121541b0901019441075058038424410384042da10ba000401840340001d495004041034031000c8a00035034025401448030070300c0390074003294855440680c17103582901c06007070352204c100000801c41c00c103601c1450710000d482c0c2101c00308042d05051020940e68021002c0c0c0354010540011076109002c80f94118100b0305034000740c05d2081810390f1503c030070444415200d06004d9800c00f80802d91016070a09050080ca0714100b0060382507440810408151280d061280188080d401c800700d218bc43c0e00d802036120301e50507203600d9500e0303c00740113018546810100100740e50300140c050281499001105012201d000c0c078003a810051020309007820044282d2220b64411048256802017540081e1810b0407100c1d1a01d0802402c000c040605082c0d4040041c0305600010404101900e4076194050600c03c5810008050500c0c0c0c555801c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 74571683 1250 74570433 74570443
    0x12a0602040801050a090804090c03020408010207030f0f0e1c23060106121104050d021f02010b010e030d0905010324030f0b09030a050706090609120e040606020a15051305 75
    0x41518410340000303040c03007642000d00445400041c410700400562403c0c0e00e5205d89070250313001d140c002d1525095601702c0580309405480103088444001c5503216900d00d80940140544ca81030008990800318400078503005660b00e41002001400c10043c0700500304010b2078840100c48100c4180c0e969560207200388652801c071344132040c40d800c002c12455060503005040000390b00d0354000c071541480040300f501980c120944045075000e440b4400303414992b100285002c665a44030141d0400300079680b0311b43e5541508000c16a540030f0306c0780c1103031890502c181502e5481c0312911902140d1442410044d95110740c1c481201c040c0023600241c64805110b10803866903030140d0051320745088102c140000c1c064040380060b0410803550040d0f1511054000241843c003807004e01806490743d41811000340701d0203800c0360000c01d9004031185900e80c0006009454452508603041c042c524203800454401c1c000107100f00026003142818070f00418050f80300b0003520000b001c28034a0240c4804040008000b000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 74572933 1250 74571683 74571767
    0x1e03070f02070b0406140306030f03030f0601090504020f1806130f0f0617041707080f030a0e07080a020f0d08190e06091c020d0c140103050c0c03040501 67
    0x10361440d040002030402842c00045400c40c1c0b0010204000c2006400d4204940f001070481503102070340c482c0d44210000741407418084030b040c02c0b404008100640801c1e0044c05601c608002d880302900291203105000490146c15490500040e0412840850100000140e24012401000340e460529400118040d480607540b221180d820620024411420085050350280440c0d240030080c00c0c102c06406000000d000e40b0180045100310094200f01444004a5400503000702c0f0321541c54010154030800d6038400c41c0c80e450494580b6828102c5402e000c141c2d00201c40f0444020700714107225408010755108038030201940301e15840040c50016042070064020b003002e01030a1812040300d2100a03045201c10400244681e2003004140850782c3c4404814000844212a4024222035480441d459503000390001d01050556440055602d54121300004001400c0ea0b091015803070310b012421540c010800340c6c501c660002d110074400d40d4420314000003c1500d4003102d03001655054500210601059 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 74574183 1250 74572933 74572937
    0x60301091a12010f0b030109050607080a060e01060c11040c1d04020d050103030e03060115090b0703020c0d050102090301151409100902030403030507080c090306041e0212010501060e010908060105061e0307 90
    0x1030301055101030380720305da490b418203030b0003882108810342c0c3d110344800f4020021002d0011000110300b41007171a6220601030000101e10001d0355858990142c24041c1e1a40d080ba40c40c0201c3d00d480850303080500404d20458419140c40403101c0000c691504261040c01c00c042d04540d00348a85080e12005004050003540030b6102e08030345103040c0b410706d0b0034000140c005032845030f0303c2c1c448040401e90100d110400c81e0311440415450340c03924038041342080c0c241020554802d40141c0d40e401804419801003605100490080004442814102c030508403c1d20620f135a5070b00d0b841e05c038034860400780c00300ba03130010f20200400201c03600d8180c408102d80041e82e0a600190343d44040000c8660010401604854000d5865052107032003400a03a6840b0001c00003880c12401441c0c4000010a851000e25aa40c1c01400031280e050640b030003034000e10302403041c000090001001c1141550080301140280d902031005031005a090005211040d8480025644003a60140540055083c20405107004000503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 74575433 1250 74574183 74574191
    0x7050f070f0b0f1f030201030506120a11010207081b0d110d08030405070b0301050d03030f18060207110a0302060d020309070f14030706110a0b0612010e070e090a02060301091a1201 79
    0x99850020788000804403209018130802107481c010a070b40004003102c0e424030303010441c1d648031380204604808207240b5600c1c4c3d03c0b07a03201e038904000c400c008506e0321040a070b08581f0040d56940d20b0315a10710440c40c0c1081d101c1c50b01001c844890805035141e844c060f0062461404881703001011544c0b2540c40030056940700c4000c020f000030040d06100d050300500e0211161801c55040000080301c10f401c00c0301c024145a40d424900c115011035030046003002221000249440005050013400395000c005e044482002480340e6216510300000711005403500030b0403403030401c0c541482540c0207500c00380c17440000d44550300001940c92445601100503241003003030840301e407040700b06051074030003542c00a606000b80d120113145451000076076005115005000d42c0b030319403a04404142c0c41d2440b01c46007449542840d100a00102d80011101c0450349843c02000305035a6000175a91034591803c00203612070f01c1000100081620b1b82c201c5841b50404050b500d003c20a0a00021040c05504509611507516 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 74576683 1250 74575433 74575441
    0x140405180604200307030c0822050708060106020c01030b041406060706020f0d0b0108060d0b06060906040509130b070905030a03030506010e031005100f050619120c020a020a06020d020607050f070f0b 87
    0x1050047c0c0400804138180701500b0f040611100489a09a001c0005600036450601c0e0030b0201c20080c11000b010110181c8540b961141c80003900c440d5070f440624046030601c00300c00001c0c2440e22031040105030250304689251a10400c000b840d90240300c0039904560240003503803143c1d80036001480d4803007520800142e070350700000026060349002407041e4030a446000980001c5045d1156040e441f107811295243e50300144000030b611070140b80c00043d000b903031482c104441810042c0e00342d80a240507003460240c655410400711161300003400f4090f010f0b08280c0f14000042e000b5040705411010505160940980082c0400e25000880780c07400c1d0320030340714403d010b0180100b5585102070513464200c86415820880480c2041c4101d41500d4044411802c0600402d03204029240c1c003c021408244a035103030713040c8025078032070860200303a01c10000104009109400003c0080e90414079802401899980e0030043da882e400c1607946c0603107c901084550006400022640d0a243c0f01d1004500b180c24 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 74577933 1250 74576683 74576687
    0x50907030b010c0224070803091204060c0b07360609060c0b09030405061b060a0203070c110609040207030215180712061515140405180604200307 64
    0x40090205400d041c603048020300c0d240d82c030111164401d9011341d03141515400204962020940c0c500e40114600c40100343c04080005c00d80040d8010368681080700c21a04001095000350312640c400d200c0070410300c055210011300141f0741c8640c028001d04101004110380c0a0a514184902d0803907106c0c4021000d880519188402d0420301130320b402d251100040742040b002500400d00307030802030210706140000500344035041003200d02400340a4151611400040308102000d002c1d00d4040c11a400f5480024107201600e10983c1c1c0304542540e10300228148075207501c1f030031801c1140ca03640c028030708100110460716036000400ca0b0a00c242c0c0200303032082860003a03d2000d50003500a00e942c103250029007007806800544401560180d1545c418030707901d6803411070300918400b14854100850b149001607015084103903956080c01c0c648902c00180c100c898120368910813405016030101e0f80e0100c030359040c041068101d901010291000813400d146089080f980280c0b40c0003500c0e01840001080080c42d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 74579183 1250 74577933 74577949
    0x301090c1e02190816050f01060603020f04180902030303070903020111030903070b0f090a09020a201c020c030604050703021804031b060915020d0b03030403110103110403050105010b030105 83
    0x544150701c03581c9030741d460000b51511018905981e496001121190500c400181105c1440340d25017240c1a00444614105403500c50340181d44815521340701c4009242e900034003c03a0035944182c4001442d05013840c4064000450030410700752030a684000280058030100000c501031403c94030380d01280d030b15510005080700708000c1900115041480b562032140c50000d4080c0580d403070094043d85035806a10104000e00038041000d0780119480380000c0c0b10310f0154003d14401c5219501d588440b500d0070383d466a420080301c802036981d81300070300800c1e151098490303070414a8468410354038141c4020740024a44001a03600350f441c0e80140c5410011403801e00c552240c01d448126203c0510300c2c01e602d0243c0401603000f00c000101c80c0041c25201001016407000031056130290030b92101e1041d000d18a80290484d41a0a0a01d85420341613400c520b4004291012280c0c44141c2010340b6541400440241191611a0301c078600140000301c0020001c1c0149070180c0000c204003500da600d090308000c235407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 74580433 1250 74579183 74579207
    0x210f060a05010507023706051801020f0d08090c060f03091509060a090807141e0106211a07030905061305060601140c031204051002030c1204020a05060301090c 70
    0x10081c00c01030303900140c1780c100810000d2201b00352140f0540c2c415614015110104203000925030304119401304805030068094000d1742a07081200800c02105001680c1d1450b03600e420080310745c000350f00120304034403070000d45911046000588801c4d10602c0003084c1c05030040c40009403d804003108100100100700054241b91059212503043b034289008101e8640741c0141c11010f0007a2501e06130b03070a120500045a020982c0425a098500c0700d140d200b40c1c0740c00107080080c217900c5c26003030316040d4044140182c2c000e4030390200084e58008000810078000980c04581103412520361400c62603401524031b1034501c50f451507240454561201d25103203040010082621700304c0e03100c401c0c8a8012a00000714107030300c48002e0130807084085501803681458054040c1c410400e1200249403001075599124441c0114410300880d000102c102500f401a40802c4a44070300314081800401c1010709809401600140003030050b040385510380d804107030241c5c000d0b00a120b656481d0107070307483d80740d80c0125007100c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 74581683 1250 74580433 74580437
    0x320030a0c08071a090f12030606220906030b090c060f0a0e04090503030a0905060112260c0105070e0f0a0e060f0f0301090309050307060f050f210f060a0501 69
    0x500406000c001c0c0180d1051807018140c404042000030410001e820004025140c0d601030007414074000c500b40d941d944c403241d4041c0c82d03070007240e01000c030801000007600d008010040c422811301d042407c0c1d051080c020001480440a0459400078010100c2e220711400b86000e8111302d010f914042c40c54501c0c02c1440002640180700411054044031118416520060601d02e414202c3c0d900b0480010094484080054a01c0c00000103004101c44290f011401d4a0701c11f0007a540203a0f603a1070708001f0a4590b89024050f00c281402e40018441d1441a05141a00c1c410303907075013400003030b4180d21708444003220900007207816003096001510307206018014141c4103c03207c445041c00d120307a01c04d848201801542c000c055843e18400c0b44c0d52000e034501e55030f06001d4002c2291042c60b003001002a15240b28460190040c1c41001c1612842a05201a40180c54458525001800c075848006a002000c003c0c12142c0c9220548602006114200c0c0038a800300310398460b9007801c00802c05080c81503400941 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 74582933 1250 74581683 74581687
    0x7080106020304051003051504110406020709020f1b03070b150f0f01020a02040b0d0602120105010315031a070306170f010b0d0c0509090a0206030708072303040b09010f09032003 78
    0x30950b20b05c0c8441000003291701d8041090784445000c0109140503840aa43c06800c01030b20590400030744000d00304a0301c15900303d5805a070341e261440124401d4135a011524032041080d00d800b0904800c41030b902070501001c0b01d2034030015854807024950180d900303140c461401d05604006141040032100c4a00d4219501010940b007000041c1d55240c0c1804028001c03503c2d864207850756600c0b00200381c4590b40101c4155520700030310419038108c82c424080d01380440d1030101c0200d000000c000d03214040c1c0381c0c42291040386003d000780540c400e4500520704020151102c0c80451206900c03140c01c4500d020102c014105050000b207910b00f0349504446003070080030126100004941c4030052402114802e0300d000c0c000381c40f14186030b8100004a00d0103504984004144207805070301028641c42031781c15071359118400c003550304003031400c40300c0c0c019050182d01d050002c200825a11120320350441e420300000505140c440060300c090360203c03d002c1d004540b00101615005400d000302c1000300c102100598 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 74584183 1250 74582933 74582939
    0x807030615021506030c030304090f05070309080d0b0f100807090801020c0c27010b03040c1401050d050703060305062a03090307030c0f05100f0c030603050c01030b011b050607080106020304 83
    0xf90382d0b088500295000301203040204096840611a4054003000a015139550fa9100d841c882c1c044c000c182c0303416411914000009130310503c24810800c800303600c03018030b500d020a01100c0c03030098400c51140c1944488000085003041d9034121210501031841c5d114002c2602d05080040c00c0455154442800c07030340100a0860034840110305000d44040841d59145640001800d030031000402c6001944090405400400c11003281005940300b14883e25425030300645031001800f0001520b401d03140030a105009140715900aa0003041c1c0c094414600024090b036039850307240ca801c2c41540c0c030447c4bc02e500c04210203024007041440b40d088085460946c43c0d403c0a02c1c0c0542e9a1058810180c10015104c1d030300e000704080700004d00c1c0e0840c1c00404841211242c00c40c00b8004080c1304e01e0706031203140b07802c07040f40035180640110000c07a0342000161403001c036844011350107400031a036217030f04000441c210707505044914114881e000d4090001428103140c1690b01400d140e5041e0004015940180820 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 74585433 1250 74584183 74584187
    0x3150301050f16110c03030403050c0907030e0705010e0d02040504080a0f05030411010c05032b0e0114010e09100905060906100b040902070c08010504110f01050f040509040206190807030615 83
    0x8022050394513007291036500c000030444c1401c641c1041c00340c0c14040020b00100340140040c0c060031640c0c0c101d42c0341810751a2694203604039803900350940d404c0d402c03156040285601501c011103a18002030603060015290342e00260448100326021a0100000f1880030a0290700a1026608252500301107285051540764001e43d0b001da90499030410101d081d144007000010306c00d403070301071449c54006240c5540f0703040001003c49407102241d003102e1030443c9010b00750b4814000d100d250443c0c0018010030340d0a00700f102c3c500350b00c01003209a0311b10070403441055903081442503280c2a80500c01804003400c10144803800c00781d018001c03600e002803200b424000b1110100454049810a080c0183c0c1c0c1c40c82c80c42c10144c801e40e55400000654600f00401041c441210420b689403501100d0b42ca0340314031300500556050050411600400c0350900c000e201307034105001d0703807030b0040c0c00100b6031420301031448400544d41c002400c075100004c164000b48128103806002d20806000c03046480a40c41215540c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 74586683 1250 74585433 74585461
    0x2060c0d0206220f02040b120a0201260f06040b06040609030b060907050409050405011b02060a0507030216020d05030705030f0403050105010603050601050d090c0f0f0e0609070207050904080d0203150301050f 91
    0x68402c018543c0d81c079086540e251f124945e848009040400101c052500c000d8880c2c0400c21300b45e0108452800c0e00e40380c200140084400803007040d01c0c01c03e441c1c45400c407200c1c002ca001810150466954940002c0e2030340d4150144c40100b440c0d96a980f540390031480c083d0991200500458000c21850701444007882c0c101064406072944114005999616800c00703902500c03185183c414480244001c1c0000c060b070100310f05100702050181400030351240741d4200c1c02c03445001d03402541e14070502041e0b001450000d1325501c0300c3e809442100d0415001e03490780c07420f5501004868174029800542041009000e00419005203607030704082000340751850018046105501d840074202e991101e091040040005101010340245040c000c10390b9111801d140b003101440c010084070520510000c3d01a15101107400d00c2020b40c0d60240c51898034000500142d820054003c40341c01c07005100c0c0110850180c8060b43c4036203401400b802d032609d03084040c1421600080c208004101c41d4a08004000610804c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 74587933 1250 74586683 74586751
    0x6101802130b130509040308180f0c0d0c0801020424020d0504090b1306140109080601031a090f120702040c0f0e091005040509030a0e0a030b0712060302060c0d0206 72
    0x402c0e256a9a10643c450082d0203203a008a0750104c0c1c00000e020516502c180c1841c81854a0010030b4070b0700c851111126074507241942c10b00e50b10f61000311542014103001c440c1503180e911031121008015140c99880b030076030700a40c104061540c104030210010b2a038641007004030002e60b00203030000ca0300d440001041403090340142c070441078640320f441d40543c075a41e03040e1407076691000040000c81c2e103500d076400c40a0301910340940042c00e1400e01144600010411904890f404003641c62008400c5009000b0044000d00304070250013407019128205000303010000c003802410350241e81e12085072040000b210b214852210410031560306405100e070708a01ca40f910203a01722007908035543c030000b04004041280c1c02054209040006225240d60004003030f00d40c50791545c44004109060200f8040f1070300d55880b01070b01c43e51101010a01150046580b00102c9031800f0001c90801e85903004103142c0d9001304444d200603402580016000365050042507001003d100c0c041c000c04012603000021f04038080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 74589183 1250 74587933 74587949
    0xb1608150108060d020d05010515031501030b0c0c0d020307021926071a07050d080601020303150a0f0803030403200703080c03070c0b0a0e01080609011205070302030610180213 77
    0x5000c9440c0d561a038400c0c2c0100f517402031a20100c2401880d10601030130041d18101001c01d1102e00c4590240b50120300d45c0114100213800c60542da1954403500940603000d0225104010200001c0e28410800d00021408407d10f40003546d81c1c0c5101c0c814044009480f000c003042070b4200344810b2081184002c4420441a10701403846a20903503e07071b4441c00c0104c1d07640400c070780090700d108004055003242d018041850090040e10301001c0e000d2000c0d241041c1c00c4507104c2c0140c0003000040d030080c040c110481596031002e44094505500c0d01911407413000950840401d80d0320210800c0b080641c01030303050035000c200c8080901905604032029542d4049070100410140b408500420310540800507034071400c0d085200014010741e9144201c210381c0c420450b0600148001d0408400ba5003d941c41074060f120280c8004a40da107491000c3d0101624070b40c0440d141c4c010150000b0160b5010031043d4080c042c1e02c446200f810340f0b401c2c404d0980128503c072104109005000841584031b5201d40c0000f112030903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 74590433 1250 74589183 74589197
    0x903020f130612060e03040503070302120102040503100f0c020a02030d030e12280206010e0f070201091407140102061b0906040f0315110c0a150f05040b16081501 71
    0x2010001c0d180c0c884a034000018180b0b46071000503c10340d10707211030312002d004440800c0401c03000e45515480f80300fa801156010b0340700100400044c20407410f0740c0d0b07007810000001400c0c241c44600082c20003080d101c40e2828940c4800d1070340d00c2031030940304050001704503000521920640741c0c086034440d5800142c00051550b00c00072005c50580602c608680c040c1c40068840d52014400000b4401c044011000e1070342ca09083c000c0e071070060001442e503040e40c0c8021101150344c1e60740358030049134400c0104414115522012824006204000340c410703015829000f8110003400c2c9030426603904102d8600c41d04541c00101070122140399009030308c2006907440a11075950110f000864450b100396800641c500f0120034001080c040250300c240e140c0c00d2405000d2142d0714040140d0300140c000d2291201c0703160003180e084000900c00c0610301c01074201000000c103107408039222100c210b81080342d00380d5118400f03404108840000848103002c00007903060000c1103084c8040011616246003441606020703078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 74591683 1250 74590433 74590459
    0x90d03020a030e010510030b18030304080a09030204020a030b0312040302091303170a20040303120b011b050a020a0e0c03180c06030403050901020c040b060d050c070c15080a0507090302 81
    0x10030342141690340f42c110002e01590808503021403244010b07101c10b850f10038250000c541c4241420107541010030741c6100540c00d50b03c80361103501c403690280386032405018042c2d1000005860f640058030050515440010700b18500d50141400d01001200300c0c00394020412040c00142d41c0c180140e17400c6010504400e41d00a820b207002e40c1e181514140c0c011003414104104100215150041048030041d64040d142c040039150716001e01d800755010060110382e001c519103900000d1544500000324051510b0101601020580c0000e03001c0d8084c1901c1e81d4106030625020360420507103817002820082c03034800c40b928050038245202e0102600183c0c100141365030785112803404020540c03032404020403031075690410b890050b18a038020340000780540640800c03810386140501c2848403505000c0d03c160f16141c14400e8080042c900107120000d00e45050202d2004a00398218680141c0340d0f12501e0440001c050b10f005d44000f030024400d0417024104410414480c0d80718103100b04072070741035445155500d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 74592933 1250 74591683 74591687
    0x20a0315060f03020d02250c08070608010303080406200903060c0304080f0706020705010c05120f010b030a0e160605030f100312030b040906050709051302190e0d0507090504020a050405090d03020a 86
    0x1307d0f04001c56841d54110003281009045e00205402c5c5074890021645665583c010581d00d40d4218400e01011414040c01000400e0180403241d9000d48194000690494101c03482d2060344250141d0180e09240881c482e202401c040000a401c1102c0b11000703411450903075510400e40c450440060070341c4401041442c1042080e405484606600c0170081c0002e8042d0080188103402a1101200c01c0c09082c001c20703450099840d100c2e0583c1c0440c0c811514654400c520400a4407414184000764411400c10441c0101441041400381c462542c6103a81d0381842c1110301407189000d400c441014a400d00c1c100000307103007484002403d0103941404107099101e107000070010203404802038442820007003003015030b6610400318810b5a4048685220172070b03280029004a0254a076400300c0742c80843c00d002412801060300701d445240060412220004581e5561b003071400d2a80402401525201032008526040c24003501412058a0402081c60044240c2d55a5104d180511042c161b0015581b40464 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 74594183 1250 74592933 74592937
    0x4050f060c07080322050405060310021608030a0e0c0901150c0f0b0f01030201022817070507080304080706030b010c0312020c031605120901020706080601030609050a020a0315060f03020d02 83
    0x3c4059401e072915100482c01d200ca400034060352030308100801202c04180d528141c03044078000c24010700281200f0b4090010b40e0000d60000010a21102042c80402c00140c49040110f00c114010800440d503000f00d82d034054540202c0c81c000d0382c423980c041e0300144030325030340b440c2c1015868580c2d103040603201c603036401d00714113515426a001d410000740d20104100c1c04800a03951781200c2c0b003039085034100c101c240003a00e504541d40000f21040e01034070b888600480c0d4489881c210341e220710b141803413400300d4690741c0910f8004c00b039105225035003000c1000c000140f014051000200080d040511445003001c0c0020044002c003580103081c40b40c00c40c00800d85d20000d506803030300b604403581201d507954050400c601506050a1048446104009038401d00001c00c0b0140e800d16001a00105501404d1030720640380340b0001400d40f0b0400d5611a000100951180205805010111030040c0d96111000380203095800302c0c0b0b03c0d207000010250080041d190f02130aa001c4080007850300603192101301040401074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 74595433 1250 74594183 74594189
    0x507031e0c120507030207140106061b0206160c0911040b04061b020307081f200309150403030504020102060912030114060403060606020d12090b0f04030e040903050901030f0204050f060c07 83
    0x2c240b600b02048249501980204007060040c1203240c1d42d480d8840f50b10b42079031440e01400001841681c11501e49101192040050510080656050450600001600440f029026641002d10703d108001c1c0720814030030340266612401101e031502d0300b409509801440745102d6141040090b0b40d0340c11110405464200540e94001e0076036008c06d98840c001e0703a0700c050000300d02e01e07010784c174075940501000c0364800c02c1d01400c080340c40303000004542e20a18003560002042d40255004403090031a00280c4125014440c500c00d0300c0c0011142403500009181c108000c0c40d02c40c940d8000309030301441003482010340e811075898140b980c0c0741260100209031103020316400204060704048001c02c0003500400c29a4100c205035484101101ca800e80039015181e5402002d80846400404210222551070b08907074028000d0826880044406011070226400518150300141000c2035140b032541e0701d40268a03032420044001d41c04c090810000030b110380203003a00a4481c40000410005038401030000c5002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 74596683 1250 74595433 74595467
    0x40f0f030801090b01030b0f040902131803030c0c020a091109060c010506151602010804080f0a080115050a08010e07090f0b070303111606090503040b04080a060507031e0c 75
    0x1009151502821101c070a0059582c02424020003000319442031203242c087d040b00130b000c443c0208600302804010880500b040e1382004202c1c09030b0507400c100e0700840c0d0040700b8042e400401c0019604000b4106c8254030380c00d008010400c00c100340581c1c0c81500b0300091325407005c000100c0300c0d0070403000d0000748601c0240c01d4001c500410f00744010b5106500503441110181d0799220220030390382500c17410b44150718500314410011070b440c1c0050351182c4855a40184202d90301031070002310051944064010800410008040c0d0006000e0aa0005d107004928015414020308140c4803000241c4072000500034125424420340010300c5c2c1ea0303c140d40240043c000c1e080c0c150300903a00e0311400b05081d40700385401d4021030b041950b0201480c0d40d220444000010f14103000008a806030b48a00142000701000e4905102c10300000c124866800004c1c40140311200003803103614030b117140200a44e4001000e40d02814030700040c4540e44500c1c1650540c100300d80110000d00d02d20381d1031040e15221066150200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 74597933 1250 74596683 74596703
    0x6090415150504030606050306040302060403050306010504120809190f060e130204260a0818030a06021603030e0303060307030b0712060611211b12030a05041a1b03040f 74
    0x12864000000f031040e01d009035814020300b6110010b02d82d0303600c002d85006005a00110000707010134410700140d50080c005150039840c056a81c080303c5100303a0810000d5581c100001180251351611441ca06400040d00224520280c5800320400b50703541d90784900c034184140d5007110b480700c3d941c0500001d040c0d44400011503d480e00e560705a040c4450100441084104005143d1010b48000820b24002540300080c01e140604c4e0340b500700c03041e100c4241e0150301881070305440c038001407003400900125100111810340413039103411b006003031300c000c0c0050300f5058108000703203c81518049101d0064076003010102000fa00d800008442c55801c5108007602c062038001c1c08103d0991000200000d10340040444280401c07018070003045408032034403210200d508224015250361051034090203151203200395016502484d588500e140c3c4200d0b084042180c0c0d0301c04002c10400e20208210a03000d06800c409240c0ca0102907080c2c8844021810b840b9000340400054104070058610334103807030344255201 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 74599183 1250 74597933 74597969
    0x904050601030507090e1b060d0c020105071d0a06050307090e0106020106050f090f0402131518110a05030402010c02120d0c0b01080a030801030609170c030a03140606090415 76
    0x140d12140d00b0b0000700c0d034034014a0340c001400c91050043c1780ca03240c003c8001e0a41e5014100a994807504188032054100c0800e1042081c900110b10a1100c030035442c0d00046107034588080000e10515044900d01e03d00e000b001c00780c4140c1c1d140d100c000307004e8a52030700b00103a40340c43d40308081d03600d070006901000e010313240d070000818969810341100044a03415200c5080740580d9200304490001e0440e02c060042101400060262a182c0c6081a444140340400520211100c80000310500135810480c0c55150600c4170094206546c429549182e401881c0035080c0403415078000d0552001900c040e0400191884803800c0d540c0c0c62807284900c00442c130446041e80500c0b2400340007501082c5040d02c01c039030344000001d074588020614101041e07042c2e42d544190381c00d40ea550b00041040440070361b100c200c160030002c50741803468000d082208002005540b2029400d1004040e65141d038050b8040d00c0c070b0f40d000e100d1951a1358041d982400800c40b0003007000700116511102d0010700d42c2c405515182810310031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 74600433 1250 74599183 74599193
    0x4110406090513050c070209040201140d1a03010603030f030509100606030b15190302030c070c0305060405010f06050d1202010e0d03060302030f030a0e0603070c0b01030c150207080d030207050106050904 89
    0x80c0301102d00554110740a003020b04042400c4407001c440c00c0c0005502002100014a4804041070f803051050411010713481545441040940166401c00c01c0c02ea82d414812088032401e04545070141d10880080c0506810f5943c02070850142414080a16440d200850801403060140d01100d4014540801140f9580c0000a0141140002c0c2d24003485c51034013004082c0c402c0c542200d1880e0709850310b0212005150004500a5000904440f494841800103000003a8080110801140540000d0281e8146800c3c0142100c65024030903540c07901d001410003241d210780b102e9040d0030390400070300c1000170360383c803420f80c0544000b40505140e8003c00107030000032074140e070000c0203880c001e4080318074000180c20000d5881c81007100ca81c0104608501c40e40541c0742c03a00003160700c240545000100a842d42d03136110b01e4441e00780c2045400480c920404c3c010703040c41d8003964007502443c0c401031500c9482e048055854a803018280400c06800041d550706114003500580c00910005c1c14035800791525044c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 74601683 1250 74600433 74600447
    0xa0b0c0708121501090b0405010c1a07020a050d0206010302030a0809030102070b0109050114090105061608070c0e070e0f0a090510051201150602060c03060f01030e030c01090b071b1104110406 84
    0x305484140340d2103e03103140d035224140180c2030f01c0052522500d81800d2800548181c41d061303d04691ba90000c160088150b102d41b0300081c0600195001080300869501c1c0c0182407009081d086070442d4060801040075030760014602405582120450342e5904201c40807d001e8400c0100140c00740108a00000b203000c0745500285c12207a80c207003d00e51010725001000302901d400c0c03080983c81203040c040148100e0044901d100c04600c2031b140d80f0328201803170740c807800050300c168401c82c4a90030041c20014003540081041005440480b0400f9110a6400004180783c00c3d601641030601c4d0744d1000604905048141c400140000500d000c0c0300001040200c0c1c060a104402d8006074030581fa000940039000081301c40c0142c1149188505507a10802031010038480800828100758440d80a4035009805000801d21200d030b000c008140c60809046c14111030801912800c104101031a00345070600311008915107095000d254500340408a0001401805002d01444902d035000500040c0705500210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 74602933 1250 74601683 74601691
    0x301060c02010e2707050403080405060d1506030b09060a05090f22081b0c0102030a11030d0203010e0411060c03070b0405070b19083102040f050a0905010509010e0a0b0c070812 77
    0x144c031403255900441141c07180030340d100c01410903c050005200034513010020f0640c5550858000821100104c40d00361a5039055210074042940c843c126540e5090250340940e04c202c054034000c40c1103181c6004101542002801040d41d00f580e0004107a01d007010020005514441d00217050b00511103007030005880e8000300c40d482c0322a640d04481a0200d20100d881c00400c2ca058028508180400300e0a03140c1c107003030600394545400100000c0c230f0071501c1032000d540070b0980c1485080f0113140518240c00030354070902001d44104401e00a20846440010440d601c0c0d40d40006a0030007504c907860458503010260b086031840d4540443c452246210942c907400c062003542d603810780c061311422440401a032000e01030044911403114860011404d03642d0083c00c06202070000600d405803e90701a0444009880c1000b9050710382c440300007408024000c0603000031044000f040110380c82e07400d803641e41104641c002d1003005260f00243c40e443d05001659004c54004912f166a50541030420304144c50440d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 74604183 1250 74602933 74602999
    0x1d010f0209030f0c0901030f0f0516230307090b0612010306020c101b03020a050c0706020c01030c0806090609070c0605070305040c0e0f04060e0709060806010905010501140301060c02010e 82
    0x1840d800303a0030340c0042e050407480006842405c0607425512408800303000e600041e6a241c40c08140e2000040c000c024441c004822002e190700e0080c180404a02d150002c0a900503a1603220382640d407442c0d9010035038500300c840d09100015100800c00104045000e25894030612500510000003409010340040c050140130710251036440c180104520100c80398441c041e0700000d450b15015a803180254018260b841050400314201300e414803d2515108898105900681020080b680385580601442d0007440d114144007226141c00f4010594121006201c0c9104001003400310303070094082c400042140d070304140c00703200c9803410541c0a40602426101264014800140004c4640540052034002c0c01700d4060040300352034545907100540b240740b000303445600510500041d41100361180f007000741501800f80441d98541464001141c03816801541031102c0c5921a5200c1510501141d055442904041417007803541d000484440741b0380308e85075410400100c900302c55081d9020320f41380c11405113 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 74605433 1250 74604183 74604193
    0x60203060a0e011409071e090302010f020f032205030d050c1902060306100e0a030f060606180b1c0509010912110a0b2512050108150105041d010f020903 67
    0xd04082c00b10750302c2486100311030340b036900c0740d1011494500340c503540004d440c1c9489000d0404261241d11031401649021002c84c3e000c100810071540c0040d807811161720f007800a41b405010f205010703a00d03445010103151180d05c9510703c0c1800f55400e56a110050080982140d05441e641c0c60f020741070303a22150f88035209109550000c480c91500340c05120740d40f503000e4051401c6464050601100d0b00220303c4075814005002150240c03500c0312a03084008500500ca1001c041045017841c0c0200e0f0f030150801d10400c00c14a840d01041c242c040d0003070040b52042c40c1442d68070070102e1001c400ea03245d0307085502900d40c2010140000b40805401c0171f20784c14040d50740c0c1400d9500c3c402c826170342d4822104501413990401e00c0c0ca9400f0800785000150300c01020b040c025092000b5488840c030003900c2e90f1030200441d0307100c1c9803d29802c456100c3e0303d01400d0305000801c80880c00f9103003c586800d0500c01c0324070980c2c580340c254861120340114143c6160000d40288400341c0c2010788417003c2e4006803050390007840340c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 74606683 1250 74605433 74605439
    0xc02031b06100302060711090c07021309030f080a1506050d050603010b130c0203040305030309030c0f070b030a020f1e0306130603020607030e150403050d120504170903010605040207060203060a 85
    0x4688203000d1020b400d1265046440c40d42804101d8120000c181c60080c04c0f10384007030702da850300d50166115144050400d590744003140704000301c1c22035103800c54005601c1c0000c0a0300094000c100c03030003c143c0c0303401e11404c10394404560ba00507003a00075810b05458102d08002407140c0d0080e02030141800c14880c103200560b01c520500d400c84c1c55415440da17000b03144e140300200d551a030343c0c403a502d1060a84152841c043d200d442c0c0300c0c5980d000355105903580c0c0c40000c0410500c03505101201c80e81003080050702c00c45181c403192003114000a4098030b451907001840882020030b1800b12410000c010201590400d030030040700d20160000c40349280580810010014444403911601c03060f82d90040090f81840f02d01e8400b01c400c18483c030041307a0041c001d41c000e001d09443c20000703000103501c2000102000141280001d1030305030030102c5c01c1200c900780800e100008407002003002c014201c040c600c644490390f41000a01400c2641d00c0303180c2062000641c5010b11000f500198450032058524090040c0c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 74607933 1250 74606683 74606737
    0x801150314060f07050a0207090501030f02030115081002130e0405060405060601020d020316031403010909020112020313030e1908030301051504050112020307030f060803030603120a1409060705010c0203 89
    0xb000c4400c1010b1410700b02c0003036a120300900251808540728030403500c00e243c603120f84208841e000c0e00240d51100e00707021400704603d424055134103d801142500d2200c0341c0342c40f100b19943d0381c0980f10380680d160042495074480c41180d0500008000060302e110f8682410304000c0e442c0c840c156000d88850040c0000a0703002d50001032a86103410050340258549601e03440b15681d4924003000407000c10800d01c280d1400e4108a0380618080e04020320002040b82061001500c001411084821114018010000d803c1590400c103280035405003002d03a07401c50200001007074113080d0078070a95084100c010100f05154008083c40c140c0b070307050710140c507107460324858207016008501c5503600042040711511455035040c0c0145800c4451401d012403024044101c001c192910703a0480c6400364000300c2044064a0b0800110b1302c810f04c200c02c82c5103004242c59008002d8480a103d100c0a040d0006401c402ca4884030700322403080c0d40100080110080610000751aa40301c06620768106490300c03240c2d0f40b005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 74609183 1250 74607933 74607943
    0x702070503030a11010b150c070f0b0f0307030b06030a02040503071a1c0b03030a11010f06050310092d020a0f08031801050702040c05041a03041505100801150314 71
    0x200c0c0240210b0403e01204001c841d0582c40100341410355403038007100700e03040e00c6134151585441c0c0304008a0341c860b80c03048001841c0070380c0c9501030b146402c900c032400c009001a04041b140c80c80081c0103c3c9a81e95540c41d01a4007900303000c1c900d00d070000c0b000010000061899406001a07d9003141540d80265481d0004101e07015140c2c44000070840400ca801d81e81e07006007400300c0d5042e11201021030116031070390019003160070907041c41002c0b0b14840c001c5110326200b032107a0384581da003409080241d035042c140802d80e9006d41c0b0500b81121580d0381d0414083c025600c065120f603842c040c25271071140548600b48807115041e524200d0103513060110104070803a25034408002e40b0b6200e4000e6003810b03440740000085154030b0030b14505101c4100080c0001d62294001c0c181d10280d10785038070356540d260544003440c2e00b00301c0c0501114490240140000215031012404100c856028040b945484800000704014525488200c1139841c20740d07000e003c002d0001c00407044038005c100703c406542800c0341d403903150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 74610433 1250 74609183 74609189
    0xf12071d060306060a0c0f0f0302010906050106031a06031e0a0902010f0c0f03080c0712091e050d0b06041103010305060f0a141323010b031606050406080c0706020d0b0306070207 78
    0x12110500449084070300c41c1c6c176104240c034041c11040d01c1a501030b80340d011078204164000d9005035102c5011006002c6103001c0e8070f004068601d400c2084d4098504204c4591868150003403094000001150b29613200c02840c120a030325107050b595060a0040075900200f01541c012404100c011070036070b000074000e00f140b00050b504803060948882e0285c4c1d044032a01e800400c0419000c100f4490300c40442e00d05042410700781640d441d6102481c0c241001c212883c04111900f056488884205000f5516006800c20703482d90301406400d019210100020f01074240c5078081d000502022000005010001070100d014603216240740f51f0030380b05e5482c1d10090302c4110001381924940400843c03100d002c40141140040d02074a48484801040040c50048c0182c0405101580e911055210458a801c0c002d082403071680710710601c0c44c10b1174000040e1032070040e44508400d00c500800003a440300c00020448105c50b51051086648005518840c0300820108204d20301034881d810014203007a000043c1d80080d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 74611683 1250 74610433 74610439
    0x30b010506030c0301170102040b030c070203060f091506060409020705102304030509041d01140c070308060d05010905010c05030708060d210203160308040b09070e0106050f12071d060306 82
    0x4e543c0c01d1030280710a420035910166169982000002171512401002e1402203402000b00d950710b040c01d00400d0300d0018003070135894080d415081400041e4a000545138010040d9804039040c6607100d41c0003880f6809903a10850032140001110010020003195540c0c4607080d500081045808d50000d801c00b1132920302444510f1b00340c48011502180c007820250000c000001d0010682a100041014a186198503c03001d6a9120440c01c501e04e0031a03040507601280d21a640f03410304144c0d4800a00003903016004901075013241800e841448000c0d00010000d6800400034400a1500345d0001d02d141c1c4200d4811001494a0010810501e8051848050160080c180a290050603000031100360b19a40c1e03002c00b544001c000c104410f494242c81c0305e800602903110010b05140c28105403110b10300041039060a078114540030302801200402c203505407045480d01a440c0d0720080034146c41481040002c04c0380904000c10840301660107101841600800c006005000b2000c8041c41014001600c0c100c0e8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 74612933 1250 74611683 74611687
    0x40201020c0105070206070c0803040501030c02150103020f12030711040b040902010e040c0302130305030c4605011b0e01210e010b221506050703180f0906030b010506030c 75
    0x91190312510280030a10f0001b04043d107405240e035a00b01600c403d60703201800e140c00c00b142c00c0001e581c161181d59900203a030f00140c004040042a21440072a050000900c180100c00d0b03411202e84078020000e10117071b03c242c1100c0c2e8414103401c0040c9001d415104d068410341c07d00c50b425005043c0f034003c088a80e40d06860322945041a403007084083c1c88030003501c6c0d0400d0350174020b1141034683c2610030360041d0300a001a41d5580388041c41c4501f0b100101c1c818032340da01580d80d0f0b1040c40710346180324503100e40464850035a18a484000045d60001c3d140d0002d0b0156003000000e202c3e5028919000e100760889803903c00c865590480107454000341c81c40151002d0501850b6015400303400d4101e8200c0c0707011000001420a00000025480c100c013000c0c039030038512a003142d4074651940b03200703010005a00314100702242d2716100b0005d0451040100080804c90240b0001d031a0388140c3c00400040d00e0340d90400c815403900c9846440042c00f07203210a8079421118000001c49080a40440c3c0c001c68007111158 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 74614183 1250 74612933 74612953
    0xf0303020a0b09030c100204051503010b0a1b12020105063109050a0b07020a0b0603160b090d02120309130c0c140f01050103061b0305010501020c010c050109080f03160804020102 78
    0x80b100075070051030740003a8081001742209440080c4003403070701000e0074000162900d080038140003003008154025203416200304010311020040c2002c1d00c1c03848c1150300d031016606074070103241c200c0e4810300c10004143d201c20890114a00d0340642260348946400c2c0c3d040b40e90f4800280c000800d106c00d00c4111a8000e046103041d118103162a001070003454000d000300c0360302c40340595034045281d104850b9480117030001c0b5212410094100a181d400103c200c008043e0307910032003200841440c60b40700d0900d0055000508981c540c840324465262143c0041c0040d0301d074000b440e030716a2030741e10140101c1e10070f819016043c136482080e803059010074500340e51000314069695460803403a5140d01581c000364400d2642c5214507103c24014107010754400c2c600030400b042415100740540d550b003124042854241001405280d03070008140000c981e007480c10740243c200c1800c0003401001d0510006e42045800903030382503c0001c0500841c002c0010113050440010140011600054244c1c1c0003401a00090220 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 74615433 1250 74614183 74614193
    0x10504020109061805060d050f0123010e04090b240a080606010f051e0901032a0302030c040807030f0309060c05030306040f02090603040c061d1c03050906071b0f0303020a 75
    0x440e011500301404513001522840000c00c40d0300000e226469064650b010404280c901101c2c10b80100507083c4404003000d0500d1440e40c8030700110141c20704001c9005943d20403a600c0d0742102c0403a903008104503d580c2032000d0500128000312032240b412481240c55500d02d0300f03001d111401181c511074007905a50b03c41d400115248885030300410100700e4240440c0b4840200d60004000000409002d507966a24500014040c0c0d000b850583d14103586040a0703d03800c00e10041000701e4600c552400507902d0380d80c5519921103000e1b98022940b5849419004001c201401e85c0e224400340c0243c40304414141d031100111015420003800600d1b541050010950384c0c14550018189808414005030400d4201c00c0481c8141d00100c2e41035a170390320301c0ca000300a140e800034940808119114911a85207050902003080300d0100b44d20b100c641c2181d55035100034117104006580c910500280b0704e42d9180304e50b05242c0a071589004040c503401283c4240058600941e850900c1160340c141c004d444451101e40354 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 74616683 1250 74615433 74615447
    0x9020a030e030c010509150108100f0f020f04051305060102071e03020409051f02090a030809040605040612061404020907050c0a0c0f06030e010e0c1905060f03060f0301050402010906 80
    0x200005040c0c071400e41910094040c07000d030242d4189540006010720b00380903030303510300000c1da002d0f8914841c144c401440640c001050784141305008140202d01c000700030b5200781c0101401c005020341c4a10210f00c00c804207a0340f40c02041150412a400c0d098202c42c034641408541080e1081c4d800360740001001c211079400d090031840c1c00c0350000032100c07903a9901e4002c075040d64951300c1d00719220b410a9420b40700780340682110f441940b8524408509040705500070414604150001a21071503020611403510ba4542d01705002601000c1c0c414000f207075071001020070030449400c0456840b410003228020300c001c41050a4426030f0010241c0c106c6448a003010b1729030b03a100000310740950107110405d002040e6640001001818917041040586107051801400c90745212004841c0d031b4101a0050760311701001407090000340313003290010307140c2c59650544a0101c186038003040c0c10a0000c03500707141c05403060002e18440c0700155460340139050300302c0c00c00d402c884080302c0c02404901e800c2c506000386882419 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 74617933 1250 74616683 74616697
    0x14070f0503012715020d020406110d08160c0f06150512010c0c080f09030a08030a0b0306040807030302030702070807080c130c09030605100e09030403050705031207110d0f0501061e0b040902 83
    0x500149404042ca8190301688d10680060000c50880c92080540d00c0c401c0250300018011440e003a000c3c2c1c103080c810940720a1010103500104241701c44c0580c244a2400c0079180300b158064800c0180740400c10500040d4001c40c45114450003003400340d02005c06040c042d442e8040e542e40c0e030384111008150b48a00244c3c101c6502d204c581a0309200081c8140c030104000e070702d2240a54000c0d904c074030301404540c082c0d0f0002d500c0c4900a8205005110003c1c2c0b980702501d803c2945800c000d80c40c0c1d52078000881c50081382c0d0b400b034580c80c403845800140d10355010540e92040b2406841c9181d070041d9041d10101968030000240000404881d82040416002d500c400d40281c560381140440943e25100b80002c280146d0b0007a09a40000400300200041000318000405051b806402da2845e4010b03682d41c00e004155000d4084120504290641c1c0c0d500c0300d840a080381d10010050300d400c69400c104c4d008000c1405401d200f55146030b200251003003207500e01c101b19074541c0e94891401d1b040c510241c0294001807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 74619183 1250 74617933 74617973
    0x6041202152203030b0405090115140a0510030b1005070b07050a0c020d03141803070f0b03070302070204060b1b0c030f0307150213080a0c1208070f14070f05030127 72
    0x1071706540c40760340d00d0294501901c074400c00820451031014400c100e2840c2d543c04541004049405041c0b10b0322004040422603a080b120711001882c1369400340d0241118480329a800480d080881580d15000310107000511301034003000b28541d4403800151041d1103040c894802041140c15414014545501c0b0b210100348a843d2480b80320860755080790b401c0e045441310200080c101c0d501d2240300e083c10414000248040203500036034524008200a4610018110104044d00080c408003992a5600100014600000042da89801804203500580f44642640f00a0300480028101600e000200d40044460007400b952900d0302e0340e900c9101d050a0328030700c030303c0d51502405920340c5040000034032001840702102401d400d401c1803814100050b115000200b01c80d44040b0701901160b1b003c03054501096110151035400c804508150f4503100c0304030070201c2684204800400d10388072200005040b920290700a00c2607086024840001c40b10780701503c240f0710a5001c840c00031032404200da40390a40f0003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 74620433 1250 74619183 74619191
    0x105060f0a1401120507050c0c0d08070209040c031205030603010c18090e0111030a020a080f01031a0402180405030d0e0a0203060a0225030c11010518060d0e0604120215220303 77
    0x13002c0710041d03942c200ca0a81c003060020800d146508800e0148a00c44007088885810b00409692545114010a5000390080c8a0b0b40001000c01c40c0c51031042c40036540200440e1208502c0c484001d00541c001c580300c5000f5402c11032884102406003004c0802c94401502903844103040c6040307a070080c5240f210500342c5648074643d65014042d0100214010030b06d0f54000340c0d88440c0b5900140001c4000b07001c544c9040c81d150300400c08601c0c200c0718401182c080c2420401c10746c0342d50000880c0364840788a25004010017100b40410048000000c052605000c10300780a01400d0031862900c80101d40b03800394150700101d0020764100718a034010008a402c4150b4105249444041103401c1c84448404902103031005680c0c00500c500529044980c0109190861400d400c801c201c2c0c0d1201049805c0f98028034001c40d05842c13156140d00019800303030400040f514145420305044003000c401e080c50b1009405045c000d0b26a11042d02d16461082c880041e46102c3c0594102181c4402080c2c203406604140d51 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 74621683 1250 74620433 74620457
    0x2060c0a051204150c020304140d061112040204050601091229040b070e0409021f02010b180406050603281a01090b100509030705040b0d0210110105060f0a1401 70
    0xd0220b00e005034060141200040c80304a10141164801031520040d58401d0008104a500124001c09420416103880c0d611445074070705400a000c4001d8800c004807004580c8a02400000306a140700318001c407000e01c41e0b611114015160603507103001e86148081c000a18602007030754200a400e40c02828168608510311503207110204590945046409182c00d40500c2001c55024104d8031008408503003c10100c00d00703600244405001841603103441c081e910644495074001e501221490302c1c00b0309030b0b001c40c4100306000302600908403001c80b991480c00000c01c0090500007128560a0310f0701003040086002d40e288031549407c8280120b034030001500800012440c81d000503402000c0d0b41f0008030390800c00c80304202403480c00c00b843c0310400070240410141581c0000d400c20450f0801d403000a00c598542c40824002c4040b200d010390080344410341c9c054032a80c070000d070100d1458200c00030403494444d0010045941c1802000b10340c4555120400c1c00458404486c010681d041410403015a1070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 74622933 1250 74621683 74621707
    0x30a03021b0a1407061d130e071202090f0105010c020607210c030314060102100c02010b04090b1f03080406120b03070303020f070f0b0d051008030c0607090801050702060c0a05 77
    0x5031120455580580f40040e0400740403c103c04c00143c6401e040203900d140c10240c0c07640c0f0804503613043c0d500c03515032801000c4c02c0c10400d9102c1c038003c80b00c03c0266100301d03444556100c02e0410050040380900c407800c0c0001c080c0a40f81c201d1a0607190160741c0c10540090303039001c21800e030300195409c5d180000100889541d103425102400081d40c1c1a44486c10400c440d07080160440780d0700103080429542032410080d4682c5d001c142044041070800380003a090f10f0081c07040340106208001c694019180401c0102480541104240705240c104170410700052008141c001045007484010480c0380c0c1030205000319802044010001c405009001a0203012900000e140180c9680185e01507044500c8101c03001c00140104c0014001c0722001a140e0f9241c2600407030988103180300b40ba0040c0ea6103000c900034050440c201801050b8000440c0e8658144a11054560f1819074080f004181c03115400510102c040c0210761240106030090f14035a40c600c1541c1109520003002002006010020b101e41d0346 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 74624183 1250 74622933 74622943
    0x210f07050709061e0b09010c0b07020f070f080c031204030b07050f0d0f050a0b01052208150a1a090402010e0f03071710020306030718150e07020d050c030a03021b 71
    0x130140703000041c04d040344000c4c203019002c200d0300030441111003040300d40c440d40d801c13565000e86a0343c80400c0300308903500d44501701e040c500000088910350180d1f030000600c00d52401c200320b043d90030080507100800e44150030146e981e071070307010031095019041c402040404c8000303480d581e010131142003252800b80341071080021360b03100c201e122100c207913580c00000c2c00c1131340d074462994400101d0008106501c80c50380040c04901402c0401d0110201e200506501c1c0f400700001c000c0100640f80440300c045019034200040b10a08072001c41c05a0715002c200d0001202c4441070304164030002d0301e0b4641513140c41d001110703001d41d2103000540002101c0e83c680c4d05034400f00044001400d58000005001c5030001c0e02034145902140088100740c014010b0010941e00450400c0449608070384900c901c03640048440003406040c0c41c44121810342007400600c9008058a051103003400f903013a142000040c45c819a5103014001035000c0703550080c46001422402540208000606004240c401c240c03a4681700d8903107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 74625433 1250 74624183 74624189
    0x50f090a0303110c0105090f060c070b13090506090601051801031b020a0501060b03010302031203041502071410060e01060309140a1b0b0a02150705070506090c03210f0705070906 78
    0x1110301c650160303c05070501440d80501c100f4a0020f1800341e107040040d030350f020340c044800d100f1a000100e0881040782041110001d10407520407580300c00c140744903492004001e10403070030550300700310004840d46004e0400ea4880d0030140c5525081c20b407111280250b00f1010071016040c95610541e0744080202c1c000e41e1040345485900800000e1f100340707081c03825190903910942102d13000b8001800140c0d004140b42040c2c503081048280c980d039860500c1f00254025102c0c42400341d2000454170b0600a00180c0700a2000080d022181c0300707148131031038900301c0e40f40e0320410144851507401446500d01c06d8101a00c4a405600101a4050514402d0b03083c001c01e181c0440e140d20410000010300c0e252004044000c007500c1c0f00c00e50500c00d008001039112080c1045200440e051040010b1180e8043d2042c0e400751600402202c90514103031203050350310180744060340d22034802c10342424800e070720b400350300149800c4040d940ea0030a90207140684642c0c012000449050280c1c00300440c83c4180780c800d030380007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 74626683 1250 74625433 74625437
    0xa090b0d1e05070b19020601032a0902070c030c0501050a0e040507020a0602040e072601061b150e010b0d020d0f0302150a050105010f1119020f06040617061f050f090a0303 75
    0x71701e120405940f50f081c5a40d400d99000d54005800401c046030b0132241c002c5507081103606c0707982c4060651100085c0200d181d0418240107102240140034001d40d950040140c0c1e00c0380002c400301c2910340c0e0041d200c038040c01c0145000100c14900b80074090515400458008003c0d00444644000d0b599641059030800e421600c02104004200000954801d130500760400d080d030021148240313030442c0340c80a1a01401003505001d07202c21440f840d420300c0a50a00d00e1500314035151148400d500c00d0001921004200c00055820103c90740d01c1c1d031030306410144c07202d036004000300080b404a0380c58000003420703020140c00f50302a48400c1320000d112000c0d210b2245030b2205000900750705080025000e40c401035503000402c2844120b082da403410000b5644030400403070014180042d0b072440001c0205040000d003d4109801003000a583da810a4014000740010120b5660035910002070108101806589000d00440c000c015000d5901030030040040c01c521040c06403416103036102041c200002c0380c3c01240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 74627933 1250 74626683 74626687
    0x1809080409110c0607090b031506071a060f0f060a20070303080f1311060d09060c0e0a0e0c030c1809010e010503010c140405010e040e070b07020a090b0d1e05070b 71
    0xf42c5007414400e180d8000164140024158140418101c09003c01844160398206614407010f0365980d00ac16104500d13404101920000d000070000701c0c07200410f0740c421f406081180b044001900d07021302090b4542d14098a0503083c249841d10488440303401000400101c000001203845156050203100007650080e11002520f0034020001c0015003402005581c42e05007181d030328000500c80c03c001107180316088950036142c8034a07903419001030001c010020714617803500d41d0210099800c82c80e00460f03480c04640140a05507200306124840320100c40c0e103070104000304005070141001c07501802c00c0c43c040d01c110110700241807000c11460f08082e0030040c1560031031801000f03a413409000d1100568490320700307480c0c007042d500202e00040c00b86010300c03418082040d90303001031900d4a50292482c10b0307204003195045582d580f0b41e1071460741300010580c051141082c0204001d07800d801903d00f4030300098074032109881306494030130851a8500c82c0e10f00820f07101c08200c0110300200601005409a106099 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 74629183 1250 74627933 74627947
    0x108010606080c0f07030c081201030b0a0b1c03080c040312030207060c0509100f02012d060b120109090807050616020606040c080c070305090d0501020901021006180908040911 77
    0x1402d2100c000304941c6011000300041d0480c0c0038800141c030700e8140d00d0f00340342548081c40d01d000900b40c000d030171400204144040001051100c958030050254070804420004000003200307000c48080034080c416000300d1104c24120000f40f052003d56440b16000d2021418507489550790040c011401001e078000a070040f80240c28080c00d07100d03002101c01d0328145985440305d520b0128a110780350848800030f006600d40045e0501c3d00030f400c0100c45094a1850320303004d1200c00b011581ba5690480d0008466152200108840c0c00304d004844a0301c0581c051003810307a192070034801c0a000c1d410011118100709201d914005501041b51501484000e500b0741d040b0200094020b03c0e140340241411f1055083c0908081c03166081441a9080002d0144c1d42c0e41d40c07903207800c1c29111481501d400c25040a620b080020a00c20f066029000e01d9000f6402d40d039803482c024a64609403411400307451808840031420a401c151113500c407002e054480c007452800e0554585144c01103c5141130b03011603440d0009542 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 74630433 1250 74629183 74629187
    0x3140a08070f060c09031a04080c100912080108100903031803020307021201051302040504050c0306010b03011d160f0221040306060801020406080f070903050d20060105131e050108010606 82
    0x3d01c0b20f100c686000c0400d1486e5885001000c150034040389148004030700440d081c0038401341210116609203084030074012060fa498001084038032410354001070307400c0340d10311901e1084101504850001000b01102c4844004050050803142c9040b41410365614040400c01e03040b41c400c080050180c0c02840d150301c5036005000c2c8564540c00400760301e0340750004000da1019880b176a0300840f60142c0d40040e01da52a440d0280c60103c03480092981882420000103004904500030750523140800310310411425004201540600180ca40c8c0c14002005013102216500c070b00c124a41e00c120501c11942c50002e00540c0c0907103070310451141c40620b04001014001d01096001e510002c102c0c2c00000c6161900d4558001c10740b50001e4400354480c0e0065000c603510301d11507500031020b5600502a03450f030fa03c1e030440261101019041e0000d004003a05405a00d5000110300181254000341110203186a584000c2e0000c0c24204c6484002c002e030685501c4102d0b1b80b03807040c1c902a104a2000107459814a140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 74631683 1250 74630433 74630441
    0x80a0e03070303080c090f0405040503030603100504110904061e050703240302040e030f0c0a0209180d0f02010e011d1507090e040c03020619110a03050403140a08070f06 74
    0x86020340d00000e0100b00290388500c600f940000100c44458076100d001002880c811044403032280c1c014204000d00c418000044011401101c3c100c0032112001e010111882c1514070455000c1d0071041c001600b000079013000141075a1161043c1c030001049078018252010040f11030301d003520100e64810800111607054418883e00130103402d01c00c081908030380f1551a00d1101404007c0c012505e03004001c2c49502c04200740d840300c0d2200c540355600c445440005075510070301110141e106020620104005445449084104d18211005400c01110703558081ea0b0394400f64000f04115961004850721844081c41070511414541c103100700040f50305032500b8900500c0c01d00000400300d0584c1482400390308510080100c9d04000d1824400741e4903800d0110b51202250320194000d000060400d442e5441045a45810070054a41c038810300c682c8680b1507558091344070001d0108504010a2003c50b860000007101076a0300070403102d100b01a50380d0454030f500005811160130b642d4900c100304100707203401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 74632933 1250 74631683 74631707
    0xb070207050d080306040e0f07030503070c090507080a05150d03090302040c05091c06022710020c060904020318160e0c21060f04061e14060301170712080a 68
    0xe0384210942c080e00c0d015414070002c0c0c141340c4601c3d940c1002030300e210000d1041c2d440300052003094402055a078289242c44c0c3d400400c04848040c01000046231401c12480b409020b18020f07990001c0c1c07130b540e800201d0010304024000703c000b6440394000c800702d42d4440c2c9030348650030b2003a07031421211031942c070500054490f40000c403001e01506005a01841d03c2d4882070f0301d01810740300e8546880c4040d505010340244142c2203031680c0000400c0b19020307444030a01c00048000d209a900e41d0244d058200300b203841e13402e80740034258482d004000c2c003100f03858207801860300050368105400500412206413407505010448405108103007500c00c110300c18030b54850341c2c1d004040c20304030b40c601194020b494480702c030140c80e180044001c10b00031400c283c0310640c00710700080c4042c10800407140c0b036590341d02008154a011000300c00d076150010035180f0040030404407008000d0545070035039007811018101049401c2102d031407071041000000701111150b41c44850980145c2c04a40d442d421064001d0801c59104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 74634183 1250 74632933 74632939
    0x417010209180417040b1801090803030c400f030305161104050103110f0d2006071a0609010605030405070303030c02010b030114150d0506010603050a020906070b07020705 75
    0x1121400030754580d0145082d201c40b00e465a00107035516490b042420035802204203120341c4000c2030224034246180014024003030700ca400203401c1003035003004403010403440c0658485500148041031a204080000d0000d9820b004540c4003070340c4604076034110402e90710440201020014185d591402001100a1301506586042d0814a421030300c1c050041c0c40345401941840181d640942c0078407000c1c101c044d0881600400c00c0c000d03943e41341030054180506040f04c80c0701d002c0c00000c01810303191000010444641c4040700c03001082101f540259a000031281c0c1d6900607904110030000649040262100409a6210995141820000d020400c3d2050708010140b103020810f100201c1c000003260310499030700d072070003003072002007814101e01401600940c1a019820020109000303680700a88038850451030110f91490031441d0704010114105da14050141c2e080b030b10060049d01d00c40d81000d0b620007000c43e07004d8549103400e40070451031f40c0034000c190750607900071051100039603040c02644000e090803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 74635433 1250 74634183 74634187
    0x207200312040302090402010306050d1109070513031416091a0a0e181f050405210703050903190516090515010e0307080717010b040903080604050406140c04170102 72
    0x1110002070502c03842c04040d00c20396400700040c0c110383c82900442e026080c00f0b01103841c10b807440d20340103042c40034a090252003801c600c0e0020b00d100d4411310990f51f0354088503040703000062a58889a0100c81c40806a24807030164400c080c040030a9000c1e150700410000d10001510801c84a50741d060743c040b0703881940319038020401000f280f101002159008506102e05c10401c2c10004426498078003000f42e1904402503051102025640a5000390320980c0030348181c60340c542c0c1486040b1070039110f210034141240424025800030a10942c045c104c5440040c045603480b40c40071b0f629070750b02000391808551a038895140e504c200088001c018004000107041840503060240d40c0703d4410a4214a1604002d4801e4101149680401c02c01008150b4002613070303541e54481c181c0c4143d1541c0340146412070b60810000e403217142813a00c2103107105030b09940c6103035598a0710002c010142102500039035030716486040501ca07800b441d0985900800c1d9000b016a039803464200e002c1500740d0a03084668183e441 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 74636683 1250 74635433 74635453
    0xf0501180c06020313090f060302100c0302060a090203060711010e071502010c0305060105181c03081006020309090103080a030b130203090706080405030403060504030212210f10141302072003 84
    0x6400825091b5442c0510204282c81409007420081c1510303400a544511807000c01c646281d008811050400d02035403e03521243e5444408109442d0742144c025059030164002074003151196035144510442c1d40e001140030300340d00703600718a45001d540245101207078101c0004100f0345c091154800d60011401d060005143c0900040d00758080c24207074035585406201440560707901d40f043c03d0000b1500c5121080c8001d1281402000c016080320b20700d00b2a40d04100100e0440d0002003550000b510013840c100d00c40c0e0850307650010f4ac1e009405440c0071b250f00c0f0750066902d55501070360503039001018600182c480ca0302034000351500380c440d40644140710390b50b0b060101090000c400c40702038907080000415251a00c0c03030b04903c4c0591000301c000e16410003040341482d801d605805180000100c11200360140c98110b003400304114140c0e42d00340e211410301030801918150000700c0c2c100100088c0090820754045038140140c2c1d0004030115501c1e69008110303132001404600e50086400c00754010400010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 74637933 1250 74636683 74636707
    0x15021c030513021002070f1806170604110f09040b0405012f090a0b0304051c08090309040c09080718050703020a0f0e060f120a0b06160f0f0501180c060203 68
    0xa402d44010b40294208110340125030b008106c0c003401040905030400f103003950b42e4040c01000c803d0500e021000b41c00c00c200010651606800e1241021580c400342805407036a60b01c62080b2002011000d4101024044c0030607150303921402d461146000d1001e100e6185040d1030142d00315a48091900d0105c5280e58402070071404600c52403242206602450346d0f21140b200014580c00c00741d5120080050000040004002010030700804c00c0c00004c0a00980181080054032106011148a4015070062201e0015441c0c1a003054031a1103c0781003150b0400c0c1c88204d02c60030a140c0e500241885000c44c001081400712a20030350740d001210b8a400c5080c460081c0e0010402449003151000b00b0842107040700d0795680d0f84085130b0315803154000c01c07603864501002854002000700c400c0c0310124505a025006801d0500484107503903004000700e1000c921940e41c644d00c1040702c02080d244900650301000001d1001d05c160340d44030901000c40400010140362000e50340e072a50700042c045410600428003001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 74639183 1250 74637933 74637961
    0xc020607020a030c05100908070c0801060303170a09050d170f011a0a020705100e090f01051c0611030405010603140102040b030f06010309051002030613061202060a02030415021c0305 80
    0x160715281035083c1e04c0c403504050f031031320a10208010206181c11202810011024002c042c1c461140d81580780d510783d40c0c41844c1c02c039442c030711003d8042500712080c000c2c20004405116400174031402e0004070b101c042d44078185418a1050ba54010503034541546818801e803681443c6e01071140224503d10390304001c02d4000000e400707402d41118200108403c030380760b8001d10101000d000e000d0011002c5c0040d41c0e200400200b401201300e4040d5400ca8042085090a4020300341a5000070304800c418140102143d81600c0740b490003901c1195940f52100400542c11000b180628010400414494207504100b000d6040c525055a071583c41048200147e0480300c0c2602c0d0300c150b20200050881d40c074040160050001c01030b0080c5a4020582e900702d41041e954050741c022101552802c8941050845074400c0b100e1a010702901e0220442e0a1001440c1c004018682420b55205a1381815540e80807004c40001c1910001c0140e001010354005e1a68009045481121145000d2125040c103000440c001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 74640289 1106 74639183 74639203
    0x11060c1201080c21030409110408010e0303040507051005040b1b010608070501020a0602130b030106030c02011a0108070e0301150f0302030c010e18040c0504060e09010c02060702 78
    0x24200010f40d0001803c80905240030601400280c1809901080c41c1d1030914401040042899405070281c0900c16401ba10901e440d507042081030b03401d40304a901d4040c003e610500401001c501c002861030122001561407103160600e45c1c10846a40c0b080f034000e40025000002e4000040c41403003801240da459007002004903a07210a201501d444961040ea40140d00131703d00000071170038540c002d02e12900030710f282005980d40d07000f5103140303030704260710010219a481c20745c407100540a0090544c03545a032051002116040e8001826110001d4003990801c15441c6111200da1025406400040e041c0b52a0011f60f17a50b4500139034800340c041c0002c038064001c03c60400c440b540214000e400784c0c0d0b0f0040504400214660300026112801002a01c4400380694002059101d5101d058050600c3d000d424800307150900e00f090030740e02100740703481c21540050704000025138041440130b40 = true := by decide +kernel

theorem cover : BRFrame.Cov 74460433 74640289 := by
  have h0 := BRFrame.cov_init 74460433
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74460433 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 74460433 ≤ n) (h2 : n < 74640289) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
