-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0324
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:12:36.083977+00:00
-- url     : https://prove2.me/submissions/696d4078-7895-47e4-a66b-e95fe5682524

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 58093528 ≤ n < 58273384 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 58094778 1250 58093528 58093537
    0x705010e0609041806051014191203020102120a0204170c01020304062001060303020a03140a0503010510030912050316030b030c040c0903140a03030e030702010c0b06010c080c1e03 79
    0x904036500300b951840c1808010f003c004c0c0c10500003010300c2a0400042d003903000d5107215000703c04004844c1442d012090001c0c240d0300c1c0c030441c810500c8a814142c005071000749803088403c100074508d104ca00c1da040a038028412240c0c035643c144c540000300401d8402e540c0081044684840c0300003105041400c8d400d44407903410003454011382042004010503889280c1c1d00700c007100802050024111104411400c5913003544c001c03405038210703090138001d054006e031420b220b400c01c0d001507601d8154541802082071005014448c41b0309103482120038100c0c465030090540c00c1c4e01560311324521600c003401800c940c100b201c50b41e801000c034119980c0ca0500c2401440030700100600149603070b62102041002400c10340c07182e41d0030480380160020109452800ba600e55403080006404280c0c5a0304005043c0c41081c0d407071216551040101c040182d0303020140c402016001703030785044151101d070300407903882043d030f40060700030030300411b4024445501251310505841034140c0b45246c000d00c44600c0f1f450303025 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 58096028 1250 58094778 58094807
    0xc01020a030305060a05060316080601020d21090813030c0b13030803040f0218100f03080a0807120e010b040c020a02180604091502030702010518030f0c0a05010603050609070501 78
    0x110503440c0d00064000d801039500040c00400c41008140c8840124040360002c490303282c18810030008809035950000e80443e007200081c806040a241c3c025806400070303489035440144040c40034030810f181c0c0807d600c440c5007650310040b035a0f078a403111101c4043c0603009010540f080c1c02200707400900b00c01d0b20300071181d00c1c1c03d065000c4142daa2643d01c0d0036809800007070017613419400107180640140d07103000d5034420921500c810442d143c144541107014200054201c501c500a014109201280c456400e0b9000d0781c80502d05003d850fa1089402c0341c81454140344400e0751800c1070740000d181241034110081000c4161000c00c42482034100481c1e4400030280080e42026203071801500d08e0b0003400403a9840040544007040302c6601e9030381d81c92001641810310302025808428443d8039a4280030f00d581107040d00804540000303105d00300b9622071090400500b119000003c40c0b114030321013400380f448182d42220003042401e17a68104103444d900100c600060070301829601040640c003684016a0441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 58097278 1250 58096028 58096033
    0x120f01240c020307050901080303011701050601050d0c0306090507120e03090a030210090305190203010e01050610050d1103040503070c0b0a0516060b0d1b0b03152101050c0a090501020c0102 83
    0x440c40c40d4261069404101c0c2aa0503020344840402c05884004003203000f0940000116070340e40c5010030785000100312101038022641040d042c0101d5a03030000c290380b5031100c55003000812500a0405074010142c980c040035800707003030104205e000781e00000041d0240070a64018017220040506241c3c0301d00c10a60816400015240c0a1000d81032005800a4400700780c24024140e545a44625140c2901501400440c020184030b0f48110b050a02a000800b004d02000b8030103401c0140000e51030980100e01d2200704100450f411700e51040b2600103400f0302191307c6c00c01d43c0e0703801e0900308152680d00034003003903808905070200014184103c200f1111185855550541001c030041079804a900d50144141d500b142c4482444540c0d699071580c10385414030484000511001800c2c500f055503c06600c500300001091040285000b40500300c1c40c01041d044803071194128505120242e10050b51041c03402c191310f010104402c490800b0000e015460140d00e41c1d600039039855004a0340d900c0310000b4540143c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 58098528 1250 58097278 58097339
    0x509061b25230303040b03010b0a110606010903061104030c3302030f130b0c0f060c04050607020607020a0803031311060306011707050d09060b0a0906030b0f07020a0206120f01 77
    0x7003074241c2c0a8881540b00a003941d207071694914801c0c025820a030880b01081900103013621006400c03200d10300c800c00308180640450b241000000c2c164010700d03c809040e82d601c2d0840781481e010010b00301c1d4091540b11010422407a03c921010410550010381580c0480710b81c500802c1d041c1850100c0500c0c0c1905074025440c002071041c40381e4840e001744000d01450072490710007041180420016104210105000388000380e10190341f03518216015080c80c0c44e15000f040b041c03100d81c446100f2102400c0c0c0558089945244c1d03403002c40e000a041d54000c00c000c0c040401840807614496051904150081c0d4242001010721301c1080941c0c032044d01c03414042003a00703103900203108440e004690f106000741041c50910341c16504545c1603d100c0b48041710580d903283d503424945d00e044a0064044d001804040100303030f04564441481c60030143c08100415800000030b00d0700c030310130022440d01981c040c00d51515422001c1004100c0c00003521032594004959001199010103808201403001410750100c104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 58099778 1250 58098528 58098569
    0x207170f0a1202100501030317010e0108031608041a030a0e1c0c0203010b03030a020f1506010c03050313020a1403010f0e06071103040905010303050316030911010509061b25 76
    0x2d0022910702c01c01e5002d82401031126071001d00c24180258081d80715080f640c00010324600e44028140c2190aa81100348018045181c000054078025280002d824690381414204441c2c03c0c05160301c480e003072445008403080e6017402000070354012030400100340b003452100002c2603200c0c03070410340f44d030941481c0003140005a03108003030403c480390000d030002030044c0b40c003c0031a08592081955102580c8a00ea803550490000c10909a2492921402c50310500380f07040028950b607002c02000c1c04002020020410720860580320040e0541d001340b101c6039440d95071070f0300700200f0f03020b554180c4294a000c0c0c5092850342079002d04010520420054540780e86d074a10262400c070078185082c40103200900c400b00307043d03a40f0300c00d640c00fa5000352145620303450414084007900c00c001544101b01414105c41400088000a404498040909100341c5070a0a90080390303040c06142010026850a101046074044001c62002c030500c1107514030305410300d0a600700189040c0c10f40304101032806001140c0c0304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 58101028 1250 58099778 58099793
    0x180903050a0c150501140307061407060203071206080705090703020a080408130803030901090605070903030203030f070c021c020a1a0304120201020c0a03180512061b04080307030207170f0a 83
    0x40c510801c00200c85001c0e0303d01420841d0703026000120b002404900d04a014a42004010300529051030011581080701041888500076941c0041c081c07600400481c80281c020001000400b610f01c0d401c1100ca6038880180d65141c03230500c80d0900500c0740e0004910018840d00844010076a6604c3d106076031b48855480b04421f1340000500055451240030100e030300c2c841030008601a00c01c90001007440e2445007040800c85802500350b20600450b054200000394000c810740c1d0340300e02240100c190650380e008007605c81c859002c01c021340c00100c00716210204032002014031a00c0b4004e0b60600c4220b82ca8035902c1403200c9207801d1200e5807550a00000380003030000701c00061031200520001d81425401c040d510702d04200040c00b140490007041040b010201941c01440050a00b20388003003515a401d90a41c2e121a009440707a092090303503441c0d100b0200c02c02d108460061540d01c1c101e80d6a4000c40c28001d4503180a8066424541040c1d41100340c0140001401c100d020368000c094580548075644050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 58102278 1250 58101028 58101047
    0x301060e010e0406150e5803020d0e1203090d051011040305060708040b010302090711070f050307080304050108010e04031101020403140c01030507080127060807180903050a 76
    0x390f200340c031200042581c0000e4a10800c040d10b0680301c0c03c0c001b803503240c104914900b0720058403030300c480c0360b0b6120300003283e0f840c224000c1b20403070144444c030321032001000b05104031401c04034114840c05441030074205030b030018250740c0569866a0381c07049540c001080280c44a1038000800c01d0354000c1c4405c82d4a4038008090b41c100500c64012103070f841d0f1407920200280e56240c5417004103148046420001e02c00d00b8001c80d41e0100780c034a07041c03480c0d150a6841c0d480c601d0040c0070203801058042e000500e99802241c4a4040c99504403c95103801e542c2c9207070300c40c3c59680340541d074041d01840e00c000070000c60000a440940b41e0586a00210340c0c01c3c4445c0c00d1b00800001c0065042104054000c1d110fa0780078802480035500402a00f0052400b0794800c03440e003440780008038105489d00007000000d660144c43d1a065601e42005003643d4074201001c00048480d010b0a00c4000780340c521f000908910001c2c0780c0c000c80702c4880e14042c030f251a800c6950100d48003c00c014010603410050564994400ea1542d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 58103528 1250 58102278 58102307
    0x50a12020903060703060f06180e13021504050a080a051b0102030f040806102102010e040902040203100e01080601060e010f0c050102070c06080a0903050405090601051b210301060e01 80
    0x1418000c1c41c00000c1d241200c02d880b04800b00e60340316407d00011030061702600c043c2c9030038142a0030071301140da03445541060311300c542000c1100c01c1011032018580c1011002c081900241039054410050a500080d0b500512459104400e00079001440c0c003000b04011841f01d8200d40038042107101c40d0f041a55605c0000d007000d045000801a0441c14802c1002034005003000d000103100d9440c1c00c040313403141c13280c0a4004070000c24880c2c60b501186088216015206942840c00004104041d8042000342591400007540940040100602e001484501d00c0444040400e010706a9a07507410381501c8100030302450b400203807038131103003541540141541002e00d846440d1289030300d4450b8440c0c41c01c981142000315030340c0300c09000800c0800c2c0c0c8215450341041002004008003030381a500900a807083d481050301032120b1000103060f6078024002d80b141d100c45c4441d42c3c0110800e1940c0342c0d40310a801241a0384000c024142069030400810603241a80c446403141c00141954000545480c000d18500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 58104778 1250 58103528 58103531
    0x1a01021207080d06051807030f11091002010f090803090c040903050a030b06090901090f0b04020405060d0b0406150c0b090115030209060a0305010e0309030f0109050c010c080c060106050712020607050a12 89
    0x451b81ca400031340640b140310243d02c1110034185010003c0c1501c0c810083c1030324071410285070401642203c012120700d0300c02203d40c2c080c4c3e40780440c2c050303024080044072040d0031481c246d5000c0610408100030f51284c05114180e074039031303419002004101c2d8102d1201400080b400d005403588180280c0c4a54021100140410704204641c8005600090240c21201c01d541c2c0303030403021451b038185019601a0481c115030560800c0d0400001c0303a4035001307190040104a40b200426841a1206d40c0320303e01a09102c602000895946407019001003128002100d50002d124001040c00c001031003100ba4a8407d801c1d196119840e40c2c080000c00030000d405a90300c0184800000002035091141c416145003400c01346883e0960300d0101820b00d003100d010b00388a41d04121055001400108480500e8140ad00304070b10b401000e82804001400344c1c442c4400c480c800d050001c02d44942000103402518440c5d94040c5c0d01001180c4100c0c0c0f684416500080800c5045c0002e204071801001ca201072103584150 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 58106028 1250 58104778 58104791
    0x40209101802090f091b0f16110a12050606040b210106060906110601120c12060902090606090306010b0c15100f0b161b050907031a01021207080d 64
    0x3010700d1044020826591940e002901040c01c0c20407803042d41c1c40b490304442c04641ca00e00404552116800005da07103c0c030100000f4030407a40d801d803c0c2990900e00001181c0034608103985800a02c6080b0b01c20036a201d5a00c4010000303603c0c1d604c1d00110b072500ea2241c041c0544c0e0329a00144030103010310055aa90040040300d00809000780100c40341a803404000002c24a00e00e040c0d0040c0c03807080d050300f1440410085501c0c103140c00e6800a04641107400010000100b24801d04100303040c3c520300d40284800d640c0a88121050040580060103914002c80e42c4001984508007000060b1060540458040d00030f02d0041111401d110040e00b51400028281c034521044250f507020040c404071286030640880744814003640030320244807006440c21541c03561600c00c6e1382c1d030b004840045400340107100403402014950010302c0c02c41c5d94001024003414403034440c00c081c0ca016024140182c05581003001101000702d080d840083c14032048482c03c400300346441e03499158803c0c964000d05041c10700ba5200c54 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 58107278 1250 58106028 58106039
    0x40c0b0d020702041a130e1e0a1208010e010617040b04060e0d090314032a03040b0414010e1903140a1707030206060904120c03031b020f10020a050304020910 69
    0x35069904440b0f50084036045c21000030070842112500303259200f10b292000308001800c0004101c01d090380c0c3d010081c140d11818500b00c514200c0048030091040b0b0328180b1070f60465400c040300300c5c180d400b1f04074035040c0c41c1c5e201d010032aa003040480c1011890103008000c10080f82081c0c10154116004400105446681140745d034074040c6030030301c03650001d40886001c2080c8800d0410038080d81c2c03020805545031a035103a81a0304040c824a5a0400f508151800105c1b515000c0089a008080b00c0c0f01d060b841e9680d80320b0b0581000e840e414541d003c5010740c00c17010214a00000e034070080705902c0e03803d912618207585840400041c145121a098414004001d01003801c41c8000440780c00c002c135038180d640f160351500908181c406030569005107200402e010005621003920f0076400c006180035521001039007012000b82007075501f1500c6213203800340034402d01507010825074034000d1410100c0d00c041001d003014000700e22034007000e41c0002d041072011500501d0700048442e00f00724402c403407001098454 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 58108528 1250 58107278 58107281
    0x3010312120e030a020111070203070b03220f02010e03060c0a0309030c02031c09302307051206011203030c050705070e01090c0206091e01060e160201060b03040c0b0d02070204 77
    0x9040b458402d51020620b44c03081c83c0c0c24003480b4a0154039030302841c282000c950100340c0d03902c41d9009103406c00c080440000d03512000c0303803621200206a8101c0e4502009a41843c1d450040d88020503400100110304850290a00049590103a1001d00045250844000c0200d00501c25207408a0402841d108801c026a404101015500380c0044007126140c80661014154501c2d41d808501a4491003c0f02c1485003c04034040000550b80141012000100d2a21040301c41400c0c0c002e0664001504045081040000f4035000352802507840310103895807414a6035070790702e0034800c040c2c034800d505c818103000130f109421101c0d000380300e414134908000ca56525a81403100c0390b0002c01291560000402030341051f03000380800502c4500107429070341000e01d121034940300c650011542e078481c0340c2003183d901c210942c811001007081c61000d02c0d40b414420740720111902c0321124240150308101c40803074200110021680030715402064082d03220702c0e04c4119041d640114900440388d95081c0008805a25203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 58109778 1250 58108528 58108541
    0x90c1c110f0c061f060e0d0201050405100e010813050c1201060e0114040b0406030506072010020702090901050601210212040318090c0c0f080f07030801060305010e07050301031212 79
    0x80c8054201c44c94100420300c880c4280314181440108001c1041103215082010000502016076040c15801c00703600040c0c400e48101c0e444070f60030051a0b819501500c0d4010a42c610201c0c0990b14042c2d00d4845544011611981c5c40000d403507604007249000881c680444c0c0c1c42580b02410002288082d5904204010450240c2c00100300c000c01040d859450b1a00384102a148003046800300b041a0844e110550348120081028052015402648543ca08910500c0c40c00118110031120101c00038030a200103034100f0030307049002e4500d55002c9400c0c2041802041e1041406a440c0200220300c06030119003d41110482c8060035800c01c8a011030400820341548106d0003600d41c4441045440140000c94405a201c40c00c25890882520460b07903004407000055030704007103410300040050030540d070f1318880c031180c1309403182d0005440c02c10541c108110b14100c1d2043c0d101000070740c0e40d030404407a049008541100020b8010001480050390a01400000808524012071410900309016084401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 58111028 1250 58109778 58109797
    0xb130e0a02120a030908060103120507020111010c030902040501080f0a080d15030b16030b06040501050a020c04020d060f080d0509040f0e0a05071707150c0222020702090c1c110f 78
    0x203c00c2480503d030704100300d10000c0020000030f0800358950345490f50f031109070390032410801030700040110030741e0b200c0d140c0540d5a82e0040000c00ca5286000000340040c602410304030b0007903080c5400028411004980392400791640c001402c0c038000a0360f540c0c829644803520055440b551080500d490409902d0300f40051846a45820314a0510000016281031070042c0c1d002058100442c40d8003648406080d602280c400b03003802a1224150360040e0708110007e000f05800a1021407404940001034000340700300c2e0b0803100610615038480418036100e840103807222000c14001c22440c00d0750300301036001409142c400440041c0340c001260800b410728000d00003d031070359400080b0510000c0030200c900b1403003500c0e240084c8401454a42c81c0484080c00d00102018408906082e00654440c0d4410800c2d10784503410b0f02d004456100d030604000e400460080e40111a440005007848045a0840e00d595010301005a041c1c5e0002001c0c0015092010300c981c0440d00c20301a201c100502d82028007030314607 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 58112278 1250 58111028 58111033
    0x9031b1203050901090c030312140a0b0111030a14031306050a0b0301060906050a050915102102120a0e0f031804200f0c0304170303070906030b130e0a0212 68
    0x42521800070151a0050501d0a00781d151401c5040050010804101160f44c182840e40000368400d0321600200031302081054400395650402c04460410b03400420048002d8032690200000000429524025441c5690204041132123180038000035138003541d0701100050520740d0045c0269030386019200203607a06000d440d1517103034480a80c0390a001e64006058043c004002032072401c800a14146528882d09025040f5480483d00c40f2100c103201c07183c44000900112501c0e090382c5002004088095042001031090065124407845c0b01d00031030b403550f0003404202610391681402000200300711030760f9101a22442200e011041010320282c4180074a000c04111240840c1061205903010202c850b940041c2110024107940c03002000d484410b50300704041c82e00c0c2e0640e518070a113103105640008241410801c5c400d43d0344c3c90000b00640c403801056599030300d62503803100260705541b00d6000c0943c5c13240da000240051807450794810001c0101d81800c0b103505041c0f80d0081540200c50420201741d54 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 58113528 1250 58112278 58112303
    0x10e09030d090521160204090602040306090f030908060c04090e25051207050102190519060218031606030c1808010203090d0206060109090905030706050907080d031505010309031b 79
    0x151108064030f901000b14404c07440d150091a0300728a260610000901c82c0341c0d180500e501b48091641500d016561100040101e900700b4240710446194044040380054240301c40400c0c68680450140d00a083c0109030a050a0810440c1c42c05004103407030030310040c4101000c05041801c0208905484a85046075281280c1490188103241c01400c41011a6a0000c0402c01c81640d001400c0402807100c20a07043c0111020b20b030050070440d001c5006c500e4421035048100a1115a03402020400040501c1034142507030750042c99200d040f1842c0c8510080c45100040004c18080e070000603120701c00340b81028001062030312504c0710000541081d08181c0d40401040030281c020441c1100340f4595000502540c640748000070040541c0340201d08820b500c5008038010020104150350149521100602041c44d1649039242d4441036803086540511170001d80500725402032003101c44016040880000f214100070042d40506507020044040203080d0a001c80043c0314480d400548522480390405007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 58114778 1250 58113528 58113553
    0x11030d060b0d060501030504020a1413050f070f031802131103040609050d0516080a0e0603090607260103060e07080a06020408070f050d0b09030c0312010e0f0906010e09030d0905 78
    0x443d0b5040e04500d042c14544000e2001507030781d10140e03004603401a1901241200c031000442e070742c00c409100d04403141782082c0c00d2040c0d000c603100c29a4402d595a230f80e070388640c100e0100218291402d1401c2d400140c038030041400b01608000d5418010520584000300d4050801c81440c1c849901c200c4083d112545e46e200d8070740400c003080c00050503000c1c15142890502c0348180e0550b2000d8280c490041c01c0d540300203030b0a00554000c0341c2800c5a207030010540e13600c901c0c0010380503072502d46c2210108001002c10b06100c0444810f40c0c4880b00790309246a541010b682107540e050014142d0350004000d52145240005440204000300c025281c03040c00050380715450004200d00d40044c0d07400c450040c2c400c0364404d000030340b1901003210360a900205d290b1600d80707600d08080d0035803040c3c1080c4401400001002c40c1c111001d20750090480306000400d0409991b590b03d030101e03141d0103640780c0510360020001000341c4202c25108075003082c411400e0342d1034603814000d0101181d840d0181212590082d840200c103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 58116028 1250 58114778 58114781
    0x70204050a06120302030423060409090c0902030114040e010507200c03030703120c1409061e03010803041403030f030112110618040516020d050a090b0403060501150306030c050111030d060b0d 84
    0x400c1c0c00c1100d0181c8050841c1c00127070540694007500301110b070390311004010311070601c6080005100640c801c41d5656111070501c0001c8050100d802d008a040002c03240f0401414410103224a02da540c1e121054400e03221035a1802d0300d9444910701a100e5440c401c4990740d000e2000b03080d204e120b48c032141000307542140404159a66400b071103044c4421426900c40c800881821120f201004a41c0706a0303404619410496007aa12424400e1241021001190210300080108281c031543d00104281c0c807400340805a4901c10160010b0101034144010010f041540b6801100785d4410b84a651600c031506d00800c4c481d4200c004072980c81d07601c0b10500c42d02420305102c1c3d0740d0051002c4034021a4078444420207540c560700c400e4668100500001c01c0b900142c41402c0e0350024003800c0528581c0e940c0c1c0e9080001c0a0002070050000c1e00000e0f078181150b59010b80319080071aa17000403e4140da83c80e003001950742000c54010380c1d8aa00080102140000c6a0304c01d00c0c01528101c0742580d2100d800184600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 58117278 1250 58116028 58116059
    0x60507050d08040c060c031701140f03030702060706090309090207110f01021c05031f08031e03150603040206250b0717010e0c040312030212100605070204050a061203020304 76
    0x81408078030700900c4085148024131000352441030800086002144c641100c50b60401c01669402d105101e0011604d0031520941001c0b0005c201d4203420303481c0d085d404040e180c0c8952500298402e00c1003080e040020340b66008083c5a40c000e050581e41e865803007150505980c01620200c99200e03150b11a41d041e842c01c07101400710b0001c207200804520070805001811030340f6120444c824080c001c000102c125202034404568485072080f00c9240c1b039a1140800d44e690060301021742008003008192a0102201c8182c901c11851082c5140040340c4003400d009180d400904240e82100081103840307070209480074071150303103851607400152042c994100f0005400010300202c04104841b409071148002008903a0b040d81c1e440b86201440f52501500202a4031640c0e0008142141440f00f402c501a0582d020b0401c010003590604119500d10307082d8661a40301d401200045603041c0218409401c7c540d0089a001c0f20048000800319240e03070036241c10400750714003203005900c009024060040c0340c0702c030701 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 58118528 1250 58117278 58117303
    0x406060312141822050901050f0408160c031a09010b03030f0703081e07050d05072d2d030b0402090307031202030d060e0601110a031b080409050106050705 68
    0x40401d85080049840036105040c100103c3c0d00d091111058141c4c1c4e94400c2d021500100c800300d84081000c0c0300c0d1038018002c200c030101e49079440e110000b51185601148603100f20360100e805071401c22050380c070b011800d020304000c0d0390500c1069008030008107152316184a01180700d042c50420300c0d24452031405d41c0e03010312415001740c00910070440c0800400d4286c074035159040c282010b0355501c042201e1100f810340d150010344503901205004442c3d0300203000b051801941e400902c01ca581e0400140d030103240800795005001d0809003440110b4030401170400c00d0403054540780304155118000030240000d454010b86000c018106005400790f01807188020540c810341b42581011003003400a61a04d0072448060040c078a04270000307110510a000301c94170324041340c4003003010580700c0c50102c070001402c0f10711501090100d181d1440500c4001410307520240d040d5079000d410310710740342003010000200400300c0e801c03102071002003041c1d00207009a031701812407580c8060300c80f00c2c9420494500719807400c09 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 58119778 1250 58118528 58118537
    0x20f0909070212160204270c0b04050303040303030e0309031606122702030f030301060f0f0809061f05041a04060b030103080f03180d020708100204051e0301020705060406060312 78
    0x280081c030711a03035040e21260f00d800304050b018804c83e400840c1c09081b144d1341c401002120b0011810408406801c80c41c09903011720707800440381c4d44034031520086100320301600d03a160b0310511041001901c6070f0002d00c0c500c0070356000d490903e50440b000c00e1800314403619403a551181e481007031000a51040503618080c40e1004107010303201000608c5100c05030045000142549021409001d5450400851010407115800c480d542e40e5140c0c0004d001420301601000001c2841180d5018180300d0010710380220381401c05000c0700d80f1062002c5000e03540030030300840001501d24001969507680c1c802e400708002c040c40c1d00300314001d8400411089a40c04d4210141102c41480180003040404003690a040b02d11000d5030f50f2610b0b19003004070540c103521000b10242c401c2188070742e2026404200e1004030341c40002202d04490365450400e00341d000700e024158200081201220030400111540061040c001c2c000506c1c1000c5502c1c2c041c00d26030100c40a0b2452600c0e03030410400c01c560400c40c01e40f18062840d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 58121028 1250 58119778 58119793
    0x305060a03020d0f030311040b13050906090609071806170c0406050307030b01120204140306070f0212030c1b0619020301030809040e0106090204090902031b0607022101020f09090702 80
    0x343c82010b03080320240080300552510004c260007a4441c07a0070101c50b240103500da43da02d28421555500c049480e03c00707907840c03650018040c14251051030154100401ca0f007a00ea4408090140501000704050304000d1011400c485040c880b01041c00a05180d68403040c00c1490060780b05510f540152051190241c200020880c45500c00142c1750080c0603464042030b004031240040b40e50707101740c004450b101480000c0014448081c00100000c0d00406c0c0c0c1640c40b00d5891800540c1d80c00b900c007140002503004014442400200d1100a41c0d00c620780780c55140c20310000c0311004140007400b9242034015030206060101c80810034800461300034284038203500d03542c15651044114001e01200e107007d140c6442110059000a40000380038207203002046480c0c90b51035885038042e103100181030380a8080c3d440c0c40c1c0b8000c41d400c1c1081c10804405000107281c40c0d095400e0140203c110310921840194081c04100740560a0005090b8641140d40d00b9849141d031710104450200e002c2d0103030341550700000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 58122278 1250 58121028 58121033
    0x6020705060f1b0304050301140106030f11040b0d0e060702060403080a0501180504021c030e0406050a08030412080415020d090e06010914010504030816050d050a080a0b0d0803040605070305060a03 86
    0xa0864003003420082014403d0b1582190243c5035003c0c2c1c2d00306940c55400d00c10303d86841c800d880026412144113075028458100d29030624811a20154801d81000804000501980b070288000300b00308112040002086503221400505040b0183c6060300180c000700c05010605510611142c4c0044009804102e0b43d41743c459801d014651000059440e562250005015513940f03921040b03540c08030100b50142883c85250007000c1c0c994165400313110b50301c0c003d008503041c14030a29140560325500c00640c074050804844640c5686609070449070705604000111388245200c01d034171441100f0350018001a100c940c0040c018100c6604a1395000b01e01000300f103800d030b07440091030044070080b5003001c40380e508460040b15184120340016021440010b0505100207201010103055401042a2451800c49190842e6984501010074001940c070740045000340202e0f0384443c1c0c030030500908848040445503a141c4040d04115020b1382c0d101d07500d004014010340c1500903135510003801c80c0c0f02f080c11400c1d80d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 58123528 1250 58122278 58122307
    0x31112010302011407080703030c021009020d020904060b1507051009021c02030709020a180b0a0207170c090a020c01050604110f3403121109060304030c060e070602070506 75
    0x144400390420404c2d0307000303182c004203890031158100e8100310000d0740c4c3d070103d08002d40546505030750800140303c0c01c1c02008c81840c4c82d22884510f6940100400e081001e26001c001c00f84401410503681c4070f64989101d00b09560307024000564003005ca0b21291580180d00f4014100104e581920012078203086030781d40180c1d144182040140d020132501c0002d030b030031400071a284c803d60f40c02044030036200041d03882c0300540144e100b00c5d1201601e00d04412054803140c042d4840d00030600008090783c01100c081c011503030030100ae0302c800d03030301d0703900b02c822080e2000001181000c080c0c0b0740e045071780d6000500d0580d400f020700030103a1009064905005c80c81d160303888007003c0c0c800c034604034941c2c1c100440c00785032801c800d21141809021800740c0b010001100700f4100185400300e503003100403d402c0ba9a5014040a074010b02e030400903000c03111400c0143e814244007440c1d100400407070402191001203000108103200b8454038443e420020701a49080c4100a443c0c002590440c600c510301c2440ba0b00705101c0803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 58124778 1250 58123528 58123531
    0xc1c0804031704150504030c080409090b100b1903020c01050c090405130b160c05011d0f010506010503010b0a030219030b030705010903112709030a17060d0308060315010312031112 79
    0x80351300003e21551241002c0314904251507008083c42c8001038001000d84807a00301748c0016005800c250302c40e8503002c1c000c01c40044d251040c103210b40740911404801d4000c10705d0b51402420203080141c80e00c0e0039000703c103085550440300c2081000011480e0046070070300e80725095124058062820329258980c444456500d401001b40603403504040751058a40d101d03036010a521507101009000302da40c00b1400c074500b0400c1c80e01c1c06c2690b01c01d0030941c1780d8000050240750701485041c5c4078646180d0030301041081c07031b0303001d0390041e410f15800301702090140c40250b0710304c11101c0490764001901c4031040c080600b4242175500c414100601e40005201003880c08203050303d4848100c1e480140400c03140048041c201401c00c0b02010f9512920800c0411407000c0010030701c111555803010003850b18100405841007050f03800301c0d000301c2c821490301e0010703000e68141a04032000504803141004800d0000500d44000d030001c0b04c24000b80c0c8400101c4917054066118201d02182040e414044041540e0302d00450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 58126028 1250 58124778 58124813
    0x912030f0e241606020f040302090f01060e0609060c030c061006031509020c070302030f0f070504050f0f0403090b0a05042c04060b0609100507020909070b0409020c1c0804031704 78
    0x910b0055000d01003c140007050b8801d600f175403100880160f6110641040c8820707801106008001160301d518450000e0507200561500c84803121102b05012a54100b03290f0103402500c1082081c0b1824820009400308035151030041c02c50f403070300d000f16044100c1654010b800381801c108c103918660701180075180139118140741c0181c07601d00038080d852500900d540080d400d03005501c50301e01102404034401400741401021605110380c0c4806010442e42c040740c0031041d0340609404164030342e01c2440e5440d0400c2c001e151003418940c541d4a070a0a96110609450118074001020040c200d541213440317105120104049907215109030f02c00b03d540400620007050180d459078140183c4c1d9454046d0b45043c0c00c043d00c1c0c18070040c8160030160407540101c100740d2042c219840090551070001a1000994154108190416181160312030180d0000e50f01001240210a800307200f40004a20a0454441c16503851045040509000c1c08941c401c5c5900007141c024901008089501314014070550302 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 58127278 1250 58126028 58126099
    0xf051e032205060f0307030b030d080406051009110418110f0703020a06050406090501150305030d020d06050603070906110d020a0b060102010f05010305100b01020a020901030b070912030f0e 83
    0x1449070421868075889402c00c2da4003207004650081148065809184035028585041041080b2002019a200342c030882180c001200c00b000180000d071107401c000c3c1c00c011000400900c2507103d0401e20299403105144502400002c03804220300712040c10740b040e00051000003003201d10076400000c250303403041589910040100181c1081090300c20440081c01c035400060420290030503103041d001078101d5030000e584543c204444103070311481d00401031080b41d0b031050007103241000c11398807172021350001400141c0450380c9030fa00142a407120001103101c1c5070207969068240d400c0c688060000840302918101a038401020070501c903030006000b80060381c0000c03942180d5075a11300100c0c0505000f161100e01c55003010000810040f00080002041019032024084200c04030b00490303642c0ca08400c0a075002566100410100d443d640d211904180b15181490b040c035150003006070701c480c20880031000280c0d843c042c0800c45a200b005016520811505010090948409003c08a840080d07003034109 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 58128528 1250 58127278 58127317
    0x209030d09051c14100f0605010201020a0206060112060f03060209030616230906070302011409160e06030c03160302040b09040201050703030b12010e0c090604140a020708070b040f051e03 82
    0x440303100302c100384c500141c0869001000c010034031406030005480c015041400e207040402e5960040c0242d40e1511807035801032507103540e1f0342c004403000302c504006e0342d03002541c6460200302050f4040111024501034500540d880507600c060600e806002400e0704a00304d10b9099010000b9030103004290008100d00d000794a0111820550ba194803604c000d066120030000380307a204060301908854100d00d6000c0c688545561a602305545624842d4000c190404a0401c18000c00860210343ca0f0031082c064211107940030a030740401c0c40c18204000d801c071840c4400004104600c2c00740111103041d8015240340d074440c28a0342c00603129000303840d0020f0505840f102d0407000c6807200320200c1c54000b032110090000c0e00165000a40320800081424098101380001800d141410f020340140e170f01145c0a12811665451240c1e40250403122007122018010408040810184107805018601418080480c11007920382507150a040c0960030182118440404181d14004000d8445140544401c0f9800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 58129778 1250 58128528 58128533
    0x90305070f08040909050a02100203031b1e0a11060106030b0904021002161203090e0903041e0b2a1f0b01020705090c04080615060306010c030e030a03030209030d09051c 74
    0xf40110303002412580d14142e555420f0080009400445600070703a01c0d40b075038041e281e200302d1b100e100072a40d02d80e03882010016408480c100304004c0446552070082c4028618007010000c09941c0b00124000020b14440c1c5142c0000101b03111590040207182001c21000306001c010640c2010010030192088020078a004001e600030320901e2450100c0c001c008440c0d0351200702c50106000301050542c009180a00c021482c50981d0680e507015941131401942800d2810710006000c42800301d60300d142d0b0b8081030340003940d140700d2806005004001d403011b13040c0301018041d60705291607070b5035801e400740d0000f240c6102c200c1201010124581498501040040c000d10060785081c03820341c0030030f41010440041207503034201b0f40040d2040d1440340c019655551901080b09030100350b007003041a8014000c002142141d070044a0f000c2019100b400e00c10004e400050000c0d04040c1c0100054000c00d0f0000ac0802c240e142c09c1c01014419940380c202115000e04200c0403a05082c10340c0684d02d158034411421805 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 58131028 1250 58129778 58129793
    0x15090c010c052d15100e04050312070e0f06070201090b0912061e100308042105010e0114060a1a09030a080301030321020406081f051c1104090305070f 66
    0x1008400000214081d0302402c62400078108200510000d070080713281a041c4109422116070003408a48100c019650401040341449800604200c0d02444100641d60411120a105a00c240916180d201c1c4808240b01801400c51081101e984216030401003180180e802c4124a02610100781d029500c0c0c18072080030825030040310810701450b00c109020400e6400054070b503440c84540c11209219581c960100312500d09030315000c0141420010b00c001d01165030002da201c0007040d00c0102418081e4019115182102c2c80c04800d054265160207044000b220101e0758903070030a000752002080035140040784005070614003048035095500140e00e840704d5408101c851121034000201781e561303503500e280207441e0300320782d01d103c09450b0324100082c10144098400d0f5030403203c1981355000e266480c5414041996120303508071444062041c8007192903155001031031b1071110101160a0050860b0500c3d5400b0111410303a82c1c8141d040c10340100000ea44407083d2000944e05c880103448641c0e442c90100f030f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 58132278 1250 58131028 58131043
    0xa18051f09090f021803010203060904030807021e060f0f06030706030203040602090a0b070605010503010507171b0408010606090b0403020307050607030c15050103031b1e0606090e01090515090c010c05 88
    0x30141800d1510f42080742030540d0050a94580000f04d4191200108041c5400d0b130104840d1a40c0c0030300080d0005007c64010a203031640800d451068940540340074000291105101058034415032092040000b403902c1486441e0f000700c500010111b80c2d10f002c030000b076507940603030194904050300800480c08010040d0143c07540d4030b500078a0600060b0b25102c1400203504816030954420741800000030b200d0030103204250154101c1c2d0780b40c148403044115440c0c0780050140011012a51240d0340380c2100c0902e078050b0010700712a40003c1005440c0c00710040c0044159000307074601000400c4100010382d0300207202e40440320281d60003030312080241000d0351030060003d00075051444204000342d604250750b0056051328401e48070f03000301520701800401c41c000c801b80700800f01905080701c01c1036030b007580c1d20040d08144034000c08035003c0d0700e8889a0007910400c0180c82e25aa440c2d00304c0000f007150034444503040070042e180321240c80c5055104140d076245821740c0c031814014a615030a09000301070040a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 58133528 1250 58132278 58132289
    0x15020c10020f0d0302030402010e0f12061503010606020303191104150806010813150e0c03011b080108030a0801060e0103020415020706030510050d1106090d080a18051f09 75
    0x40129180e054806929420040d500e07004500404416036042c50291080e28001c0c0e406035506002030b85420180000700f4401c03070100f580403c0758a908241d0361170800c0f9483c42a40040764442842400800789802c2d038000740c010f00c080d9041030007042003d204408242048803081d5002007810594103041044a10441d044115003c45c0106a141550303003180082d40501d00a0380d89003100c1d0b82e0144010f01215206c940240b0000c4d400640c812035800c2c91b0420188203d41d00187c7c0e008c01345210000e0300711004003003c2a084a60282c4100c102c41c0c1002505006180500285181102c2c08400030804c0c0014040d60f0305000300041517500c1c50f442039050740c01900d8010702c0400a150104406560f441c0c240c855540003d09090006902d04020340100040343c90260a00d0513100c990b9035400c1c2403c00e80e219860b002a0180295946541d4212003080309600039103103e903a030403200e40010301c0d064401c08107400c8040110350422041d280c0079405040d22000c400d001490050320841210075055944c40b8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 58134778 1250 58133528 58133539
    0x60512040c031208010e0a0204080a11011803061b0509030303011e030212100515060403020103020d15230109060801060f020106150e04060e0402030a080f04080102040b0a020f070b030115020c 84
    0xa00c06482d0000d500c41e05a40c081b5008001c2a600c0c1c22404041e07120328010b0403805c0c0c102c00c00b0080012840e42031541444014181190140c4107521051100c000543c815113840740c807048140300e2a805003509045105440c540f81d880c0c0012903011036540c1c8410700c1038400c2ca0600c103400d05008107104004ca00a560f005107442140c1110b01a6140c5d91094402811522031a0401054840c5a102a50800c1c400c0c0039099600f0113140d170300103400039004030080c401c0316a25000070421042200304420b010700719010415450030700c0117030b1013010312600030280d40c18400c08120603c400f5401c44883c41c1152101d01c0e180309a004000012409002c1035803100c40b10b030700c0e554248020b89810071402261084152010490156070b9148079441180a43d0301942540000d804280410072000040035024035005000e45082c1d41c030030781542207a2280d84205500e410200d80c0003081d66042c04002e810450f550010b040107030400d07200f020f00e48010300c910f01503201803803001228640284940103030041c00404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 58136028 1250 58134778 58134803
    0x5070f1401110a0e03070f061b0f030f02060c0301050d0f0809191a0f0a030504030c0b0103030f090e090c040b040b030105150907021b040c0318030306030204060f060512040c03 77
    0x80300c0c1070641111403c2c8002ca52000c400e00d500303003000a4400200c41903401d25444191400034190391120070440c0000109074110080e10204a420b50040e040c14401d603a2110701c1c1c1c141080080c2001401307402e4051a1000300f00420981d41c840c80100d01d0142c001240a901000b035141003d00381c4581c149060300040e442c1901380d1000c07000e1650b142181ea6600c031aa6a043c0c040080c0a0340344034102e60300c10104018003440701258800c2c0e000b15400340c400d0078010540b076071546800c015040c09034422000109440c807480c00695114101000918541c5050b003e103050803281183c683c0201c40308036010b141d4030810040a40d0b901d030458030010070003a0007040541001c1a860600641230091300340561007450100300d986100264000c1c003015500c001400c0f540c0d184042001410b802c62000d020942c58036458158120700384c0ba070f03001d094829100000c1041c03841c03040c0005e94115a0040d110317000141410030071150010116070501c0141c016410490703950346441030844403960406030080600c1c0c00b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 58137278 1250 58136028 58136051
    0x405040f050105040c020f03040e07090503030301090509070f060203090f01030f020c010209030c0303090a0605070c03061803020706020105060f0103020f040b1204060608010c0906110708100f0f0203010605070f1401 94
    0x748024181c0d01d060b9000d201c0d12400c60f0003681d607980f540d0b8103002660f10800080000e0030b00c0c036103120b0f004045840d1101a00d992900001d1454000303810950002d5500d106000c202c03041000504010150214401c811a00d4044065182e00403629440d0142e02034174503803640d680c03103680006060141c19208548518050a0090003074100a8686010f441084451500c0d450004144c0d00c4442e001091711401070700b000d00031141500002d10480c0d015007520004030024001d405210000240c89200440040349810001c0c5025a190b0043c429a490700b02804601d84a03110050210002070801513521640c140a10b0f40d42d01c85c6501014104001081002584440c80e001a000341d001d90f01c07e101030341c1c41351850b600701c8020310669400f003801e1420070040580584000c04031502c0c02000d641c00703281e0b280d01003030130f01d501c007480100c505030f031601d05540c200c400303100d0f2a83d1390054190440c00c66060143c007400034411a08007070150003d400c40e000c104070204004100c3e071818600203002080350741 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 58138528 1250 58137278 58137281
    0x20a020301020c0c04050a090c062007090e1911010e060c010504062a020c12010b1203090102011a090106031d030a0801030c0909050a060c030b0604030b0f1f05010302090103020405040f 81
    0x4035084e84a04d0908000c10300700700841c011011410340182d40544214a890303000d942c84c6601105054100c0d0000340f901800707240900a54006101600012481e172808011150070040c021041c0e00941c03000d01c1d54480492660b2094211043d02801c1941007510100e0009415010705c401c812140e44c24070703081000700070716a0440c1c4641510384000c055050b4194049804605801c000b240c0142d005907a684103d1030a480030040075252400001050603d40d0b0100304810540c03c0c945110340c0c800240f011565909101c0c2002021400c0240000c3c00351910000d40149410301c02c60041680b584070f000103100c503911a0441c01840300084036902c1007c207101400d0114244002e03604640c00150000c5d41d20402d01460f507506504c50b01a150303c8105270f9600008011141000c0100345d59088500780980782c40c002440a14000e203d200402e14059200f429120030081000c0c0300e100b151000814901718441980e002d84009090140e180c0d90001d004030000d0040c4c0d0320460744a418543d042c008140306 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 58139778 1250 58138528 58138543
    0x5041221051e060d0302030a0e0d0203010c0801150314010513110a020a02190510030e03040b16020307050f010f080403121e050606030c070209090304050d050f060907050d060507020a020301020c 85
    0x28101140d490f5030ba00ca003005002d5030100005805a0401c11070f400310540f08014401c40c030103004200c584d1800c2d55401080c215240c601030600880c6079040103000d9007141c0d500b00c0342040502e00e428001d00700c2c0c64110880c6400c0610640d0700500c1c03000300040882c1055041603510710b0441c100c580c1c5420040c0c00095560700995800c1e4001e0b42840c401c4081c1d120540300d0542945e801400900040502c541d046004200c0605c075415980002d11020648542a100a00810b8410016000603e8403401054284407030b6901c10380c4250b400c0032403818540d810401c43c020329880c0d804d01d60310b2607071541801d071204140301146510702e40c6002902043c4035241424203031250407040042002c4d41c0d64800740002c0d484180c0d0440745182050040070018a0a03000180d130000e00e103000e4a082550340d10205180130301509048802d034000a18101811208009860344000600000d040c5180340a01059034400080e00203000c90f80c07900c0000e22014003c20080a80d00d9010f4021960703001d81c0366415071640d50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 58141028 1250 58139778 58139821
    0x705070317120c0c10050703020d0e030a09120f05070b0a021606020c0f060d111b0c0f1c0b09060a060503010614010e0109030804030501020306130504122105 69
    0x140c10603440c0d2048408400c0c0c41111800075004042c54585405805260308100d204001c1e503c200e52114850b0034003406100c6c01042641c0b00542c5480c94001e052059403034110080585030b00610031402d9842d44101e8100494a408118000b94841403c001410394030001003d1700e240319035000010941c010310000c00c0140125402e071080300808074207085c24415540b255500580c0081c02138130492620900e1b5a404030750041086203009503862415085d2012243c42c0011040081688401e8032481f8141c000250320342009480c040740781100040d000700e8424100380c010f07919104001d99509102c1c506808603500109024a146000030a031541c0300002c0b1800d2a0f064104030000139075090500440b01500d082c0300c40e100070b0b070400000444289d0300e10180f890401ca0b40f0000000031a94001c020000785000c1c500241c0d49140180038030048400c0030111302030701442e040c20440410161010a50100302d00c0c5892044199101c0c1c018413181807502d17980300c0152603c0140030000c06e0307103031003a0308594 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 58142278 1250 58141028 58141043
    0x6020601091a0f060a0203071502030103050708030a14090a030609050d1e05030412051b100c0503010b0306090c091011060702160e13150b01020c2b020d060207050703 73
    0x10418911078800020002900b03410440c4800c43c55054948480545000c0d4003034030450341450300c103468611040101c0e0340c02d6883c2c03d900000620a01c0750074403850000e0408000114581400b03030034010045101d410074081190800b00e0300c221070359180304050700156084082480b0a128904029446503c010021000300c0e0b089000324196410b003055071210030340140c80c0e0a046540d60303120001841070b18404a803c000081001d5080001c603036082c180038a001c50028940e403e0030380310220441300e8020000003889130902c010007a0503245821a0b600031416242140c40341c8600380c407070440e4000c0396051544801c04482e034a0b0141d60068000880c404000c0c00c0ba019510f4181c016a220702c1d00318843d0820840c680418007a400303889808517000948600352104d5088070392940c03c4220140d600b00310b241615a44804400c0d83d04110f641c4200031f084444480503601c00d0036501d00ca515130704d112001051710401d50001e41d80c444200f0b040180e000705c0290741c1d441c2149005515112075000031039404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 58143528 1250 58142278 58142291
    0xa0e03060105030a080f0c070b030a05090105010e01030f020a1a13090504210c02060406090303170c04171e0604120509031b190e07121b03110409060602060109 70
    0x14580080e0440c101c03000900901500c0036584c844502c0303070740203036035511400e801084160210b0401f0401c1800a011420350a07403282010124002903e50149c031080d000e80c1440e00500c4000141103080d41100d502c800d400e400d8002c1d034030106080c80305aa21408112507803030142c0d42c09400d43c50040c088400d00110301107180c0d07105c540200455600f5100908109189845803412501603024401000344608044100d01700c607a000070714650251308402e00245512100304101070f04580c60740450807810105500c11300d40a0b01002c000d0046118100c002598540355120000b824070441d1040d0b250600e40d28040a1900d03032099480c0d0050741d08446084401c224105031034410000d070b0b40741c0301004010b07092400610200741c10403e198500030341d0204001c01d600040243c5c0805000007050f0080d110495494080800b41103012410360034002c440c2404601e0362803031201226081d080c030107030400282d006031710012884140a5504054201c034a0010007140c0c540e0001103a030b041b50050300c0d00b807196 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 58144778 1250 58143528 58143557
    0x10506010e01080906070e131146051b010e0d0903030509060d0f051905010f0302130f0605130203090d0915030e030d091a0a02030106120f15030501020a 67
    0x1910411a804045034200305c003c104600d100304d1010380300001c020701c0d00c466403601002d21412280079031a85070003010000303401c0d1101c03030004080c092280d07100788131502003107504896224039248d0b0b500404a03080845003035800e401d000f0019036150b05800c0d04240480c0341001512030007000c42e1205007009115078031000b40030a10503440c04080e6079050b5200350030050350500b48609500b041c50501001a00d4507588070300100030780316461244002c0c40c5040307202071044003807008480041c0c0084901c000802c0302440036807510f20560000303080091001410100000391040101856044280e004001c03030318024030340640c0d8001c2c50081c84040103031038015140c42401d441c1c2d180144101c4004c0390031b400450422901a900403035070007020006491808441000314002c036a03100e1402c8480c41e285003030420003c61410401c47e030040349480110316550620034054804a240d0f80c12466068440e020350102d202c0300d4000030490050120b00e40f41d0baa880785070041c081e42107402880005400300d100d0582 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 58146028 1250 58144778 58144787
    0x51312020a1e1205120a030f0c050306031207050f1606030b0607030914040902060d020408060a0c17040302031201030c14010c02100c0c0b0f0301030510060303020705010f110609010506010e01 84
    0x120805080ca01c0c82c40c41c9842c100c0780702103442c11001e5405003e100d800310910b4010b44010b0078022869a00020402c15004160701141c40380318441c400c225042c01000385c90b880c0050b42040701344d03401a195407204130347d2074100d2414400b60001211401203c0ca5002c1d510700e403000384820740310980c500307020300d5840b9000d000d010f0042c104007400184541c0c00401609400c407071000720a18002c2c10100340d40c031103a000b00310241d0100a8403030b0113036400242004014018000907400a803903a6040c0071340c211581005260018107030101007101000008101014001c104442d02c0e080b49441c80a500c0d81d4078140115002c42d54401c50840184002d00c40c82030390710a841da80c3c1a540d00900d01030f114000e10b501140d040000341401c692424150002080800325034001c0d1002400304031415030740e5070540c90140e04200b00301c00e00440342d604003142800005e40104411068036000e180507100364046c62000c5607503081d42214400355004035004c0c8080a00f06401c0345100721000c0e2111101d4044050044a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 58147278 1250 58146028 58146059
    0x11011d06030a020d020903011505010905010207030206190507171e280302160f020411040f030605060112020d060303020c15160602090306090a0309050f030309010e01051312020a 78
    0x16030040080001a100b842154054806a81c1080005041001c0000400c0c02c450048090401e1500068000c2060f03690112545c400b0704400c0c13000d025001d04d1980811050b010b1172000382d40e510b41a904103031400e40300d40b0070b41b10241e03080f04810066200313011204801d81d10016104202c038051a20081511884408a50703003980600070300400d001070034210300310030000c0c8411541015002c02201c2d20f84040219003103030300f03030083c035100c1030083d02403040104a074071039000d400c5270307503010710041008810001030207080702d401c040041003503038800c00103c2c0c01c00422600452018404504000d90701d01a5006405070381c820740032103d4210030b2004001ca8031900003000782c00d1482c10005482c140190b62003001c0d0640c03040c1005400d04014000203400c1050440c0d032401e0030760007071044405140c1c0c040c140d203000784002e0f1643c079901402880400c1e102c0c451110b1442c18405207510038a0b469114008841000000411031840c2940f502041030340f10f42040006d0340708070f0740124041421020f070748191 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 58148528 1250 58147278 58147337
    0xc1b03030d0506010908030f040806070c03050a0c0201020304030b0f0a0606030b060a03090206040e09150c07031b11040c02030c010f05060307031203110a080a0f050702070b071e1101 80
    0x541c145140e1030100c0e0040c00006003024104800841c00140f40c0c00208003800c1c9403400900e030b0701d440e2414841704a26000006082f0010441c0074860782d008250440101c600000e40d61030105400c1429000503842d500c0345510003007840301c0740030400240902c88000140106c101000c24003100c0e81d100e5088003542d01e24a8a0380d8003200403c00700fa1454040d0b4022189076201070070f21402d09640c1c1819820f841411150345500d03412240000408298010210364426200070340316081c02c041da05c00426441c07160100980020800e451030701070052003840702000210082c4180802d51282d04001e4a076009002050700541c20107a03007088120b80c40c01018030680c0082c0040213028503617180c415040e40c04040c900c091680e0f17100c084068940070401480c940c00c0b0381d11110040c1c20501e4440f800c940201b28610b441138030b080240041c0031f60119940c811030f17442c49c4002c1d48801302030070016074111200e041d00480d016401800c00030012103a00c000ca90b100241c0b54029890040394081402e20f50000d0b28 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 58149778 1250 58148528 58148533
    0x110d030b150c01060b030c03090f06010f17030903010c05040f06091202010309021302030f06130903080a020a020309130b0109050306220c0801180501110c0604060f09080d020c1b03 79
    0x1070004654a5406031000c1c400c0e80e00085421503036070040c04c8140e442500c0003200284000200110454200300c81105404101c004104a616085940400d608640927500c40000c407580c01040314071040040d1090f00c00700400801403080070701b5028015034058413503007481e100d408000040990080f010b40c1c2c2100c4208000307a10a1030183c0c01140180800e00c4202d9200307440e840e4448a4505900c05548548060540031040781403840401c02001b20308121481c02c1810301d054000001d0b84041481e8001d1417118001d41c584c207950ba4140d0940c042e10a840e0f401520311007409402e6210360f000350b20007090a80341c80c0c15058a034400e01d91512812100c007101e12601072071400b0b501400000070401180102d01307100940f40c48002071402c2d60100030104141d140c00100c03030010f215083c822500443c0002c4a004c0c075103198402800e07100c10b0300800140c441941c8003d0b833440301ca01500101c190130742c810030310303a0707030311003403020240250068071008040748216582013030381030a07200044000340d000900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 58151028 1250 58149778 58149799
    0x509040e03040f0305070303030f020304050316031b05010f06090b0d11041401060c120806010903030e06070618060c0503060d02041a0604060309031d0616060b10110d030b 75
    0x1800040c00010316088a01d1104020008032142201e603180c010314400c102801c81c05245d410010250380302480070051407441002817000007200081100c00e0b0701d044200307901b1102850706069400c804882c0c2c10460482c3c00520420400c1130640c000702c10b50fa00300b1030400005031148405070464072a03141e410341001804402c1c0300418428102240441d030001c2020400440f00c81150300d280c0c0007a07200a02040010000c0300800c5a050f00d018400030007483c0107042c1d0314015000034081305403448040c0034800400107032070b107e440c1c070002c5440d040d4120406102250380c0c03042c4454600e07840b01c41038841c1442c00d0341c5089818840c40850b80030710b60040420111602e15006c001c000c05101501c4215035001192003092074850380007810041840e62000502640103060141200411492025170215001e1180f00c0c80d0707031a40242d0340a07805400146912840f140f618000400d00911500d82c0a4200b8644884695010043d40c02a220b10010b8803482c5907086015826034410b0b00322194481003000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 58152278 1250 58151028 58151047
    0xa020604062703110f0411030109180501020a090e07030e03030c0c0c03010903020102090f040e0d14070501060b09010f0201020307081807030b0f0901050601090e0c072109080f0106030305 82
    0xc50b50280d0024008050100e14840d007405014050954030131102001405000c401c1450300751010000040c00307a40601000c2d12400c3c0c2c80c01070340300500448514039601c0c3c500b22a01e1000140345455558028003c5581d85030301c100240402c01c1510400694481820000310071034820300584540c1c0f22140c00030340c20754441c1002c644c031300d42184002e50f000b440303030000c181120307502401003240da203020744c00050751400d0f0340c030900040161080c0f10500560901640c0c100035a80003451440d120391502d051070507049409204480da01c920a0050b01c44c1d820027101190030304c0080000d045d07106090b243c0d050060b0f00d12a06a00f40d0100312041e80204840d000001c4002407600c40c1081590380c0035080c1c0d9611912a600c0508101c030035135240701200460700402c95418002d1283e41c2d0007100c03d08020600a10384180364071041801444600c0c28580459403004000004008240c55101c41c0e005842d102d4110708000c00c0120740d4803559800b4441d50447d1540184180301e010140d942580c1d0b064030303050f5000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 58153528 1250 58152278 58152287
    0x110f070b060d0f140d0c05060c030a060503030301060504050102060a090515090f070f050301061202030709111e03040204060e070f05032e06080903030c0702040e0c040e010f05090a02060406 83
    0x20300341900018031203040400142880c20300c007401403140d580c07a1380e1410003207516031030541000300f140284900040004041440050019404241104041d44d00d90300c000c205005801d0b194022038242c80302200200d003090700080500192a42a42190b450b96901c406000a07030b24032034000f80c0650000022040d03902081e404c0c19034010100320031200d18510f9125454607060040d80404030000212501b823240e841d083c06550010401f10390f2001300c044490300000c0d1200818031500c48020f545012051440d9618000ea5441100c08200d560001d505000da17204141c2c400c88040388940d2a000e8041205445035040f540116242c1e5541019800c808030b050324030f41d00162200e41e040907a603800103c100c14441800c00c00c4a94961a066198944040640500c201a0440c01c0b150402d00c1048040c1c9100707400e0341c440d035804850104140e4200d1610a007080310246000d03411030300b4614a183c8580054102a070045001c0008000d03503aa005401070b00c40720841c0000758446800c000800145109 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 58154778 1250 58153528 58153531
    0x804030206070f02060a030914060403050f030a06051906180b03070c06061703070c0b270103020d0f05011409010b16030207120309030b010603020c071502100e0703020301110f070b 79
    0x284207043e20a06840d000100c1e0340d040b0544036400681caa448040800020321200f2101c181c20400078403490800b46d6001c0c2407030288481f5810049000300008600220a800c180001c3c80c01920002e010001e072240101d8010b039901076040890700501c4242090020300218800305c4010302410750554582e020221a042c078607003401d0b01c06d0b50301d541d00400c0c40c02015051207100148103000716030301d0308039150018280c00c580d0720100d90004240006444001d05080300120b4000c29400c1c1162518900c005a0080c040c0301100c044c580d241890f4400e040c00343d40d2066040c1c0c0c207180d682211071104c2d50100700194500340102040c1010500c41c0c2903c46031003040c46d152182c81f90040c1c2c1c01442c1c0300c03000b03d0f08501c0a0030301030780081c40e0000c080051260311100f07140545403a14040d45040505914240e48119034070a00d07200951440c0d101c544c042c0300380401c15a0840d01c583c01c1c04603180442129554905030b0100f81d1081d4a04011000c40002400c21a12410144035032103040c440f5949a41c601e0420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 58156028 1250 58154778 58154783
    0x3070504080f25120b06040603060c030b0a05030304050d110607080307020c0f0411030f0403090b13030501060905010509040803040201020a141c0207061710150215070c080403020607 80
    0x40a00012680c0030302404441c0c460030415004105003c00f240400d01542c0d80c1140d00c1007811009101071240150515000d02250340241841d0200d4584501041c014801903001400d514900005125040da0580100c0300e004d00880d81403628230f40341d00400d0380381c0c4500c3c0700d82603020724000103410000e4140002008507210007441070341081d40b035465030380159000719078210040c0c0000d2040d010600e42000f00c04800841620f0401c4202244a038402c4548006491141c03000c202d07400090401d842181304c5000303440712442d01d985a5000741015409200940405c86065007003040100f1184501d109680c104c1d200100b6144464540d61a0044250700c0504281e0450140d4a2624041062400b08054070040d41004183c094807030542689a0504904000c0454001600070083c00394004440403c1c400c010b4041642600d54071015480103900e6030154900d4540e06620f60702998000c1003000380c10325400d120441c1035507070704002c490386110740a0003400c800040c0001c1c40582849006883e542e071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 58157278 1250 58156028 58156037
    0x60a020c131b030b060d05041511030f04033603020a0b160206280c02090601020109030203090f0406050901030605100602030a09060305040201030b040f0c030e0c0a06080c1e0a0305010501051602060307 88
    0x407070071846c500650b413040301d080d602c82198840020210a00c0c0c4a01c1c483e88040911250071401c000d1001d104500c005400178040042030084480e208405021000e1032586c11031300b0310500050b4078a0702001c0c10a5200991284030480800215643c009003101c0c00769408101039201520550708006940c0c1100703c100c013461070401130308002078441a501411240385500c3d00c03420389030b03039104002c003800005000d18110390501c803683c00003d40000558917880c40403121312000104000125008019a07440a40d016440c1d40001041c0022540418040e0000e101303204800d076100c010907a81c92044407444030024a070312000b040003170300c03d0340f0568006105150220783c2d11701240c0001c054405e00070360703880580d0340d482d05509401e0305441a8091000a4405059020031050000341032485038820942800070301e100049480c02020115076502e0503982c01c07132103c0c54501d4203030300b402d40003039120700042442c01001042c25030240741500e00c449480140c032900b052081d800d2000e0f81c4c0000e0001390500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 58158528 1250 58157278 58157287
    0xd03050a02070b04081b0f0d02040f02070203030712090609060909021c0504050d0e0f0105030c0a09050d06020910050304150c030e0102040b071e02032109060a020c131b030b06 77
    0x52525000802c0103000c071710300801009007194403211041c40350f810b21510542a00b036180728141c88240d4460a1560119400140252103000080181c441c03c0c00095042c000043e00004024000b414401406100c0c2e4407108a103071144401c0e100061240201808241581d204110300302903a001030022840c0c02c210961100140b510321001c0d520162002c48003500100155040e80341c0c41442460000c40440e920140c44c800040013a0041c4000381c030010700e50400085420a080c0982d0759480146809030940041e031a075401c01030004e400440781c0314442e5203a0481c80030414031400c00e59000c0ca0304055580c0146030300045a4000f000c501d007800b010700d620380650f04003003c000c0c40600010280f22100b184d0341c0c1050300d032002614a0509034442400942350881c0d0141c0c5002503080e84428103a00000251015415482c0e001e002d500070165101d080050710700c02d52507010502010681040d84c03000c0d000b01032100800141c807864801c00d40c45801103950740410601c65000b40c201c00c00b0240c001403a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 58159778 1250 58158528 58158539
    0xa030b0a0513140a02030d0503150f0d0c06080f0601020c0f0405042301020c071e05010809120301090209030f0105221b08012a020c01080601050c060f0a11090d03050a0207 75
    0x40f0b02e81562141810340041e1191000d6040900000889500c4c510f0024617500c9e002c0c0003040f440c080c84030050b0080c4a40401007682d0385402200c0c100e103079042864000c07019503801c001021064216042200c059112001c41c0403075000003902640100e009250440440750b042c00d01000700002401603c0c45149034000083c1102001c221400e112600c070b002583d01c0e010760030303102d01c1e101007a440781c400f000380301c644041904040941402030303d0007460484440c0d2640e001072490500b084500721003011001000107062441c990080c1304100b0281c05568544684003040c600b04c8008903810192051140e88200e02c4408a805070146c4070f03c20303034003141c500c00d8042d81c849044440350400030a43c3e542d50b1900341c0404c01440421015000482002110030310f9490007503c1d0a00d04560f641800305003408511982c3c0170714103035040281240708480310307441d0080b00c4844015040c1d401e1792480d032518040c200103443c99000c548442a01800088000409a03002c0b1403a41c00441d890003180201080448c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 58161028 1250 58159778 58159793
    0x90515040e010b240708131701060303120209010c151103040b06010206180307030e010302090319020a1703040b0703020312151503040b060d0618200a030b0a0513 71
    0x1036865000c80001550140601480702c0c5406850880400024813404507808984e500e04454080f60311004d0f0701d4843c0030010201c2055459500001e030301030a8250f500c038000c9015800042164000e58400c9500309050030200f0032031003441e5803940040c2d12413801e800400d4600c000e4903086c160300800013910f000001d06a0782507410554084441340540410b002c41c41d80d0402c80103402c102aa55a20031400051514660303e100741000242030258401c455038050303000358156691884081e055400b11010020400454950f000c001c82c4918505032011a04442c5410100a0010618025413525013171441012030754121842c1113046100411442b1040c07000d115440f40205c101d248900c00744504d01040102c850036122508240e01414020030001c1a60540d0286d041001614600c58400d09400c3c01c1c0003a1a156003000b86003100b1003807040400040c05103110000a0094040051201e040c040000080240c030014000c00c00e103401041280480e80d03c90b60b0000300f00382039440080a1070380c3d2401d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 58162278 1250 58161028 58161041
    0x703060f06080705220b06041212020c010903060b0d0f0c060e090609071b080c0705120307050303040219090f0b090708010503060c16060f06030c06050405060409051504 74
    0x550103919400e0003140509140550006410707400003600c46181482d003c035a9061141c5003118020040c0c0141c081800f001d544100c5146078040c06a03546e0b80d40b26140842c44201c900c004881c1e0361103140c02c000240c0d03c081203941c89104165503440c40c2070326644441e4007800d284001654807148041101c000540c103142c8031309190b48500c101b074000524200c8040c00c10300300c110945004401d982c0c10469681d480120351035001c500d034204100c00300c54000c0c2c100c0ba00092184010240344000a89011860001401c002198402ca54100701104150089601c0307010b42100109140c0c0306001013801480d01c94044074136003c0744082c61141300d030f0f40e80d1624244d40d50000e1207800c00380e403110441e4860508040e034940c4294141080049540f40c680480e548041c0200204140c2c1c0000c038100e80000e02c00e1010a4003c0d400c01003c2c000e4804c0400b27050024026807100f11101c01e04004006a50780c01a001d55045560050540c2e0a2910b04281c6401500000b0304260514904c1d030b12440071980c0c0c0780301d0381c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 58163528 1250 58162278 58162283
    0x181009111023040f090c02031909090b03070b0d1d0111090103050f040f02040e03070606080c03072c06010c0803240a050f0f0a0503060f06040f051618080703 69
    0x121559120200b0661035003400580e2018082c4200301c1804034180d010060000c668158070002825800c840040341140901c041049000e0841140e5200f9203a00ca901c04082e100071a20420104040004059071910244140c8004001c103104440903d11b4540c030850f13043c001301c41c1c841104c00c603c1c020f403401c480000050840042c004603664080c1d5034148525644880c00070f698420074201074030343e15040c44112400a21440c5c90301e0f820a1032001c2841075420081d404101801090785404807640c5580324241001d00901c00c0060001e0644452001c0e40100307180d01c2c01080c804103106c078001d0070b2180c005082034180b0000c8020ba03000256000000c40c45003821808441c2e9410210360358000c2c0070500d10704076102c0e2040f00418856503480b80f104031603030300084071207401e02c01c000c0000c500403003a280d00441d414003031402041a0004009031307451141c203040310b0400002ca420300846013103580c143e80145400c409501800f031201c1c052194034411000555600c000640d0b1110b1a9240c07400341d4108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 58164778 1250 58163528 58163537
    0xe1002090a1a04090b061c050703110706020405030f06160c0f15020a03050604020a0f1808060403170a0c08010e06010314010909050c040c0516060f0204030311061810091110 76
    0x1000300704c0c66403059072801503003118154074141c4103040c50704a481c41503150032406c075501c9022600c10740c000d5010014242c9400d0304c140d01c4940c4c0d810300400941040c0b003098042e01900c4541600c81b10003041041c413405501c0b011080200e00c40c001180c403402550800c841d81741c1c83e005180c000c1030300d607169940014040c080150391107084590007019600042c260501890051002443c565080010ba0211151b00c9c07601280816482c5910f64080c1c641c0c1e401000c0c0c9026500510050552020564444811010186001d03449040300f400859400004100000d500d000050041d001e1052402d40c015805140105902204100c65000c000007130788240f43d0980d036084030321304004051180e03000500c0c04540400c2512000d80c0d02615612480d00000101662444104104002035114160651501c58219103c41d182d14015210007540c10000740144143c2c000608070816480580520f8841500a060a1844105950058040710408503001074951031407046907160711020210003417040e40c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 58166028 1250 58164778 58164787
    0x1080f09070504050a020904201903180302071a070803070503060301091406071209080405090c0c0d02030912010209150f0702090f0106080106020708120a121a130e1002090a1a 77
    0x408c800c40f0311030743c2e140e40c01800c0d03e611444000b1410080d00c14414070f100301c40c41030000d240c1e0101d00401142c6180c81c034103903403a01801d050550000d8908d003943c0b4000c480c921458503585e0381400c00d000c0d0f0309004000a40c1000000d941603c608050350f000b090140010500000380c1d80d0b15036010040310201d030303010751112003003001140c0d100d0720b000c52882085e6000c1110481302d403141809445140540d038003c188850203d9415a01d0307400310385480841009580c4083c0c4580c50083d01d91b80300684141c444c40c20308021400100040c82143d0020030028110814248500d075112001c2d0040201c2401100c014071901000d611142005032041d040034009000030760409a026000c00c0060b08a030085501400c8140008500095858030300142c03441e00a442e0201540301720f9415144803000866241860b0094401c03603407400d01e070141d9102c111600c520b44205400c495048500c00b107000610f5070320000c138030651602103174002c007800d080140c880400fa60311303240d44c203000202c0c0b000c450203c0c120004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 58167278 1250 58166028 58166047
    0x180302010c17270126040305090306010e06130c081902130902040e090a030206010b16060609051504020a14030c0f0a110c1c020402132c0105090601080f09070504050a02 74
    0x301003c500c40e43c00d0038030701100405907546620300c0c911051111500c03070115001c6000d15009800380d9903106001021034140c1e41c2c40d04400c640341300303080e590700740510001079034600201c04038002e0b0200019281d90340e040c0350756014042c0300718100305404810000d0b030030401407001d102052900e0f0013800041e00d0140e0303074514140421820000051208585800030082a8002a0301184c51411122207154940c0c4400207014290310303044010200800e41032a000001544141a4101c11b1003a41c02c03819a00741d503500f5030180310a038414202c0c5080024200043c90100c11240d002039500301c590741440ca41003110021080f080d55005100082c0410790b03c110720f0445100400c10001400010340d8054811111803c4a52202c00d111800920840d0040b0300b4101142c000c070084002021907030750040d80b00c81103501040b04858400d2413800c03000d83e400004511401c0c1a0740c102e0042d803042e501c450403540e904400030501c401c068807071025402400c1c40000d1340e03560380c0150b0b40a0250b410740140d07100843d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 58168528 1250 58167278 58167337
    0x609020a12050f070c03050c010f0509061305030919120302030304020a120b07050702030a20010f0203160303021b030d0f0b010309030806040e12040b0304060c180302010c17 76
    0x14440c4041c214144010020021103981d820390300114181410080c1d041c1619058030140582e1134003600c250b290001e03648103140a60000c5010704036036802c0c1c8040e41c8444c3e03812218980c1058002c0e10380d50003003103100500d0070000b000365003d5007241c101240c440e41b0f40043d000140b03180d010075001640080240820341c0741c10714201000388521981442e220b64995902201280b000300340c28280f1401142603000d64400707000f9406c410b5409508201c4800c100d80c000c410034080403860b1800202c06000d146003a60001084070510804080301403451030355581c0841c00303036200c80f0a1489a202004026061712802c00285c040310f4002403000c28500000e00303100048038841d021403410141401608000b1031341001005801803020340c0e011400c0d40e4511405450070882e40300550000c1030001e4000b0714402a40c0141d4011807144038240200d00841c0c3c1c04a4803c042400101d000b41d00a2030108019030081810710078051189004031070010302d0050860340c0380c01c1b01d0554900440000680540c0c034888 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 58169778 1250 58168528 58168547
    0x50408030718030c05040209010c0605071101050a0c02061501020a05030c03040602010c170411150708030604050a0507050d020717040305010b030f070f1205010e0109050a030e060f180a08010609020a 87
    0x21140c4158a915613112070030010014840c50f405254000345900090340304206840503a0f4110340d05100d54142100004d0404070504504c81039035181501141c1d182c0002d00440050032041d0f4024000c903101e00c00b42d000d0000b41740035051305620801003000c0006009202402d6158111400f454542e498040041c0c21f64040115038001c0205a405808485240d9416a6002600190340d4040c2c5500d41c4080341040303280410004000401062290401040740300a620489040d501408a03072102840c58007070716800da5542021a81c24003031020842265809402880d0160942200d0040c034080d907800c1540c842e4000f50342c66511080055946c0c04c040014420380458a0014010385240c4541d000404200380504103003200b904d5032433000d00100b500802d22480c1e80500800004001c0e00d4807659510078200c046002c58500d5a1581440c0b81c9881903034a0134101c00300040c40e002884410b1118021500446a0300c001d4801e0301090840c1c00f4843c480203003e48681c010b030f503400e2110740a440242c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 58171028 1250 58169778 58169807
    0xa061d070501020105011508060a0b0301140f031c050708160b3301030e0703150b100203030f0a05060d1203020309121e03041a0c040302010306211e05010504080307 72
    0x1004010007d01c1e000341101100c440b1149400346080d100d4500040d082c4c01551311603410030070040000716003c1c01c00c0501c088080c0c8102d49a00f04c40586006060719034100644420102903124440b1440601800040a26611807511a850301d004c20348104c2d02d6112007403003900c11020013800c00c84400722340e0080b40e4807801400f2400000d030914100c444000c0241e524800e04040e00c0d00c0d012034841804100d00c001850307008100031801c006441c0750000070440f060350320303100d800408040321400e4004811a40206102c844103182d540d2094084809014060300381340e0000152401c01e8041440c2c4001901c4a50603a41c0169881c102800c1301440c2005041194250302c401300b103c1400c003450003c42030200600500e0030f60701ea42d6542042c600d522003107083d445401c0c201c803040099800c0c01200800a40340300340c07410081107481d0460380b89900c0d510b601011280403403c0e000c6010684017a0710241c000060040003951a01a0f540d035030035581d040c0d0381141c07007040100500080c543c012550408400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 58172278 1250 58171028 58171031
    0x203040b041e2004060f0801020304020109060c0c0b1605060a050f1602030301030605180f0a030305070c0b0f1909030e10021203040314040b0403030e040b06031b03090a061d0705010201 81
    0x30340b20b48810151000d030302044144080840340b144641e803115004103005254400e10a00543e68540c81c89002c0e5004075400c900241c0501c0c80410400d01520007410403d80001c0032400160400c00d800c0b060342d00c00c95100001c400c04640c59000610204000343c881c0c0c95200d808203c0b414aa0000807207072401a0038214003940e0052012100756000060303904580d0012000300f41500c810321901d20341e4213140041c09040c0141d1420404c210780003c0c0d00421280b10b540c040007295100e500444e00c108510b000100f1980036030000c01c90154240440607000740c00552240c280c81c07280e0960104840c10b494003100810081c0701460070034549000034025a000d42d0024041013000100f040020740300050000782808100441c0038400042002030b18013400750400e0741541c840d1281005040e4100004240f0b120724100007481d0450b0500c0003d0382c0c0940c00e500384015442c0c4591084a1701900018a001c92a224010300000807035468001c0e43d401e41d03c0c030b030081c68601d80000c2d2454104130640c0c00c01d0307042d07a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 58173528 1250 58172278 58172333
    0x20307021e010c06110c0703080a0215061e01030b04061e0e0702030f1b030f03010806181f0f0911100c030c0f02060d0903080603191502070f060203040b04 68
    0x40e600f0012032410680d00c100009880c00502c2c1400382c5900400c00c940601d4415000003004000340c02d001425aa0219000c41314440307000354011a400400716229078110035000d940e0101e001c0c0f00c940020302c4207014100440e0010400f004a4211101980800342d44481d03c41003204102c07800d042d80014028102800380c083c504200d002c1d549104840b40d04c20f100c640021210108001213048c00700e0800e51405070780c1d0351072a1060745882a0020302408031a40a0036002c1030759214002100150f01c00d00102600900031403080820304007280c42c030182030440d00e51100035421030061242c1a03403107219440104450200505000d1080018203506080c031030b5940f20f500100750481d1015280941c00011061540000d101252081c010b410740f5280580c02d0001030020035401c402030318401c2d0720940444059551160301e1201080e0b40c0d1601500a40c290003400f4803100880c0c00515034140078840000401c88c0c0390344c0309000ca0740115400e44000c50383e14144070400501c00484104204e5400480340107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 58174778 1250 58173528 58173589
    0x1407211412060d0f0b0a050414010c0c140f070f030314070f060f0b10030603030e030a08070803070912030206040203070608010b0a2a0f02100512010605130e0702030702 74
    0x18084090012803180340003d04910401144241c000700c1c0f550f00c866005100d05020004502402003038508071038044a442351181903810511400d0040c003caa40d80102c0340c640303074407084030400020610f242980503000c0c04182120080212000801c0e01440e091000c920b1030500511060fa0307003c100c450048200081400b040c2600d405c040110f401400002c3c041d520340b440d41c001010b0500555400a06c080c200058450309640042d0449000c1d8481c07a054084c4182056100e0740c0f1200c000f408648140b0102000c1410003002d10350240d594100200e88549a07030403640200c4803c6021030043c2e01c108100310442c2024800b000040c00942080e2244d9410300d0b820281c01e006402d40d4408109007003404c4a0801255014007080881a003150340d0042c43d9030a01444400d14007000360701400231440303a507407268890402c0301d116460b5076036580c3c1d1503401c00300c0031149c5c3c0d40080e28084440c2d2160b080862000244107903035004820350f4004581d59446407045c410310a003c0354055040e000c5101c0303603000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 58176028 1250 58174778 58174807
    0x60705031b0405090c0309060601080105030a0f060605030313090c05030705160203390d03020706140903060727030206030703020a0c06020408010b032b14072114 71
    0x820810501c0d12400e0715607410a10500e500990b8030080d407100c040f90a0110014289008600a00320207041d94500d98030b9000540f1044400c0c80740a4056000d446100e0101d00744821070052188203003800310743c1030360702c20000e890b5801100c1f1506030348984141c208004c80c4240328610294110b81011400c41c031300034002a209014030501c0948001842c0e03141d600310b40d03051001001c04460050400380d601d414005410041c00f171940e21a80354148aa40000540303064030414607042e5041e8014008182004001c80e400d13004149012510382c002e101d20a160355081c014180700350103580c0c0300c0c3c101e80d13407d0400840791340d010101c2c0c0201490211007400581c6aa40860303500601900700540d40709280f1780d088500c1364452401805141c40440c0200b03003220103411154164004404aa8290b6481c4140c014141c0c02003180c1a4840f403903441d1019078a00400212202c45822038080d0309100d03407a2500c610403814090440700070455020381036440364000c611005c15581002d400c6040c5038500b0540309 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 58177278 1250 58176028 58176031
    0x108070f120203092104080708070e0114010908010c02030304020108061f030b0a0503070e04061d07030b15060310060807050a09050603090c030f0102071e021c03050903010603050a050d0206070503 86
    0xc0c0781980000000701c50f41d0040000d0880e8900c6815490b2542450075a0030031203070450302a0003407078046c8190010302c1040c00510035043c1d80800000300f06507403038800644407190015210034140008048009071421080c4a60342407e5581c1d000345540e032506100052500000402c040d02c10681000885160192401d80d001c08140500740003a02441c00c03800030320007220503840795600d03200d030020200383c06041c0d04000340030310b2259400380b1a0071114103407020218044010706042d40d014440c2040030a1262080701e4219403000381d69107084143c04081001d9034001c480340107d03a050f1131010440107610280c520340c0401e031450000d05026000d00c1c000d054012a1181c0791280c02c000c00415100a800e103c08800c444004040742c0f940403550300c509010b9000804107403410320028010300c800c00c0640d41c4c040611a4010620030034440003074000380100403c2401901044070500810301c40d070301e0900c6620f0103140980002c0905079024076000d854080400141421900721100b807203074090300503041c0c9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 58178528 1250 58177278 58177307
    0x70218190b030c030a030915020102030403050f0a0c06020d09050c030318010818011d1b0d03030903030f0c050903010b0402130b0f0d021303050f010501030507050d050a020d0605060108070f 83
    0x2054140081c1c0020f071a00d42c08140c010340c94020006140d0801d80c101901c582212500b5000401000410009074200e0108440c0500825010024501040303080e00007014030326010308145c1e250814686880080b6002006440142543e4011080600c002001010101c4400f10011450010581d100114403199240701ca414050204007141d40c0a0f2a00006480700110900802400c00350514019011180740b00030302e0140142c0740310f44c02003005a50003400058003d0507200b201d24155404400910b4140d10a804142d650003075045000da5a014900300502d265403103644036070b85202014211802e800c00c10703101d40d20400c03403004500f4249a4010441d0035031150192a54003607142103400344240c1c540401485c0c0700264800c2c45109290260042c4c1f0b008504507440503807207065441c201d0b04280800f401d10382c03112800300280e262448074001c03024400c10903640c50480c5a130210307140031004603048a00f0343d110702c1002015680a46900c1e8000120700d82032210109107600605070701c840c41d002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 58179778 1250 58178528 58178531
    0xb04030215150306161b11100e01091202010f0f02030c0706020705040605010c0b0a02030c22060908010911041802030304090c180b27090405060f0703020c0615041407030207021819 79
    0x4031301400b081f44008180c1e160080c1400140e04003c141c014061440c603500c0c036005c296900e0000c1002c4e4100786030708402c140e042e100c42d803040d43e428806403081c0207503c6146003140710030800301c41042c0c0300f440000c00901043c1c00522181e82000c1c100415100c550f0401030401c8200c844410200b40450300b1903070800c010314070050381c9448070080098688106680c03040204500c22096100f018210601c0b003c0310001c5e51400020340d161507415090361040f1002400010002c401c0c0d0380286499800f2090908110361030b0b00b90754125501090558205900441007540d83d5003d00c6e0f85a6040301c5940505190300c00503502080c280405069036000b1103000340c40d0303a070008812040131708004400a80f600c600804401d5640703820320349181d6822045890f01d1201c1130540c003160701c0501900950706400c0f081005002035948510105240c15041080e00758496201c0002d034108040183d0854003921060383d001d80e03100054018030003c010307668201c6000303140400400c4441d40e80c41c5000400700302c441c00c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 58181028 1250 58179778 58179827
    0x311010c0c030b0402091b0307031109130506090108150a020901140708030405151308030402030a0c1701111312050a02040f0b041b0c0b0403021515030616 68
    0x48611400d94500103096046841001c828031a400707401c3c42c840c51003240c070b243d095941c42441c2c8803250a100d035900d80c0c03101c0c140045601c0500a412220b40b048507000f0180c100709440b00044c1c2e0300e15500c00000c1d2160f0765841400443d04104409c0383c0900340306001085c000c406444d1110442d00c0041408007241c1c0c0c04602940d07180c0c0303d00c200744a0018503162581c3c6031600d9062501c525031090b10100d4180c45944080c08151120490b4540725203e0b6611010f5110710a8880c044107900060040380e00d8000c0507d01e4000031a0001e111001c1c1213103880c9001040c0e04c1c617243c60300316640050480308a00043c0300c100c00d1b4a599019031405da80314460f21a102c40b015103012460165000c1c03000303500030f0034503503a554424030365404980121001c1f503044c058070f41c0c0764500c442c100045043c900d0026a4820b900400724020f500d485030054400d1040b141c02c180440c402e4521034000359008008611800111181c0d8076041045507004654419045826030001d480944440481f49155000140701c0d034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 58182278 1250 58181028 58181063
    0x40b0c010f0207060218090c0a0e010203090303030103030305181c030c0e0301050f152202030405070f0e04031719200d02091203030f0402010c06090816120f050403 72
    0x400000440300030000c19510b8070f8191074044040d401412201e900d01c0d00349103134161700d880c01170341045c043d03160100442d02d00380407070200f2a07080c40307810364190661104102658064804000541c0294040d503400186414000c021004200c1020a100e9550307021041408000001c40840c2a0b00321050900003100d45c0003140607204102c4591002c3d525500e000200440010f00f110054070a8072001d1000001045078800c002c48000c1a900300d92018440700c0b90811014100e030300950f0041e0150013180c1d040b590395602800c6e518640e0f0002100d6a1582040c0402c040c1c1102088222071003459000800d442c006560054448115104100c01c0303482e05044d03080c0010140e810212014416074040d594408454098041e5100c0858203002e104035040d041ca0042000c8107990107040904501c3e8844d0302d590300115000154801c050740c0c10f5555420381e0000070200c81c001c0c0882440c408a06406254504080d80d080d0441d05c1984144410440c02d0300e41160f200080f54184c9500c0444039a00c020a413 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 58183528 1250 58182278 58182281
    0x1140111030a030b040c0f020705060a05070503040803040303020d030501080d120608010c0507050d0206060315060a05040911040b01020601140111070e01270b010509040509011e0906050912040b0c01 87
    0x241010081c08001000102d050781a00180d01182d001c0e01c00303201d080f540c0c0c0c0c0e0484503544011140001a044803001307012a15208009091503011464442d0400c01c00c1d0310303100d0850f40a82c0c0109450b03440000c0800c1050307010300c061061035900c0e084c00c02566241018007a200c1580040110800c56044044607200881e40d00c00c501a06404008200c0c44124080280c5240c0c0300c079000343d51611907401405012131000800501c030b4900034010b0700484a10a5040900c032601404003a400860721402046a84407403080c0314006000d0300c196944007003840241304c02c58944009950440d04201c005001040781c20405584181c000e180c0190030301e44440b031a0b030600007d6003141200075a018000a075400321400400d102074240e22100038000034000078a41151000b86800d030103d003081c403146001c0c3c901980070541c0480a8000481c199080050440100f511600307885900e50383c034036081e41400450710520307034080c8401c0c004182040301c1d1031035040c0a0140e40b2030880d403088000303080215080203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 58184778 1250 58183528 58183547
    0x501050702040e3a020c0904080712030606030e010c0509010c06090f12020607090e01050625080309070e0f060904050708030328020a090302010e04060314070614070b011401 76
    0x50205940c04500a40103800042507030b1a00c0d050b004c40009101e051840720304c00410b4814109070000d04030030780c2031010310100f508018419252840d050189002040d030620040270440d140c0e980000f415400c00c1000fa085440c001286042030785070142d06031041390408100c0356049800d08005846a180d8901107002c0d04000307400500a0361864003800402804090541251215800769001d41e0348000c012a80c0249501c10a04400c004400400c03550070a10003c115480707140c10492186001071030311104444011400b19140d04000042000724841804004d01610304c1d01803189040c200380c458410240307000303040d0794401c045850204003000404c100280c014900b48007030301d8513413402451164000c07180c1441c03100b000c000380c1890a12480c852081b141c0c0319101d03407240c101260468004540108000011a800682d035000100c082a03520050118800e02007008240703650400e00c0007815801c4444124441d41024051100040c0c0c60f00d058905440c100543c19486078a08001200d0f00b41c0d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 58186028 1250 58184778 58184801
    0x80604090503070f02041103090601030f0c080105100303020d030b031522050a030305220b0405030d110d0e0d120209041b050a0305010b091302030621060703110301030b01050105070204 81
    0x3000581100b048020007002402e9030003210304003c01070f5a0131401e034a234841100c9481c01c90b0426401070001924880c003540640d4000d0841c3c1c0c903510b4482c3c14440c21600d040d551a040e0b03880d2490100300309035040004400004c000e240a00c20000f125012036902c1d41e040c2e884030009040800041e28036100c2d07821005400c24042c071204142d80042c201541c8860300604103030700083c203107030004450079540b44200c1602101414180d00021803625941c100040260048555001c10010035916020070f010300c080c01d03014180e070a682c0710002494441101c0000c00442000c0d00300b030f8141009070390003403500c5901c074588500140c0d4510080000034001c25560031041c807014240049034041c141d0110261203012800c3d01c0402031a600c2e00c04071304680c00390f4114254000740e90a00580e1141e019000345402034009888150381e090b111400024030449100b070541d07580d100300c0422003141d9060240d801e0504004410520355410340e210103150700350500510b81030180c002011008c545450380103400054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 58187278 1250 58186028 58186033
    0x20c010c170a0f03060b030f040201080402041d030901020616050f13050a0321090b1605010b0a06050c060a050411090903070f110f030312060d1410060608070f0f0806040905 76
    0x205180001d4030203003070010f500300024980100481c14042c950100c0e4002c020750048100c0310340c0d0719801150181c000400481e0400c7c1c58003c0360b1462401520034600c000e021a02440c2c45000c00800285062002001d41803811503494200e04059080400c45404010501c51b170713592642d0b10010058121440d9000f280c00584030704002003480010a41081d00c05a0821075406000004008a52640039406401c1a42c0d0341080b00d000c001290404204032203108900100c1c3e052070007000a4031810b196800580400c41c0011050003203501449001d44c0440d07042010000c5062a44880c82001d4196503840c1c0100f065030b02040320403400b001603500c425408140d2107060308061a01107020703209244201e000351400d681c110903518010040d50307040c140e100031246042d9100010400718091014095420240089100d11207141c1401a80305441d1b1070344021502610b0050010180c08004054000f00410066070301803541c0e10618111409986141c003000359129400020004c00840300300070300d03d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 58188528 1250 58187278 58187287
    0x209040f0c09021b0109030e010305100512060702010b011d04020f0d09120e03030412020409080906130501080c0702010c060e030f160b0a0603050607030c020c0418120f020c010c17 79
    0x741040d00209500801e014038110703104404000142070320303040c15004001c08c4840700383c0001944283d10103a403060303d00007081d2105a64001040b02400784528003050380e00402c01b0850340b51703024010007180180c2803034440846091040e001c4446001516104d10554002441d174203c601031380c0070384a51701c4070310100b000b03281c0c4185061440101010f800102042041a45d5001c1f850f000c0156000c640340608140070301d841b00d508000051a0b4180100e0b04100d050100103165242c04020f000080fa0102081c91100d06110002d05800001401c00303040740001c004400c0140d1380000c01241065002c80045204022100c081c0c0c1103010300407010000100c041510088032044232040407925009000b00101511441d02050694400d80809002a40004041180c1e28826405402d07000464030581d40a00308150010b81520341d001c1c3c2c01070b1042c610f20b11203000d00c080703130442030021041402c00150b40c4148170f4000e902e90200000307203410f005000628000b4859442c00541c0460701540a03103545 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 58189778 1250 58188528 58188539
    0x120901030603170304061a0a030f050307051509210904020306030703050d03061806051c0303090213090b0906091b0604030602040e01060207080d020a1502090a060f030c020c0d0209040f0c 82
    0x12a04211015078286e400c0181094420342001c40c0c0c61445107020305040c00b0070381103840d000380c83c400f400c074202c031944002c000d80e8000c00c1c0c00b88222072000d0090000850746007003e52141c6d10706007081401c010407044210300e61260b045003030100c0d100844c09450150f265540c1c400040e041011662010381540160034102214540c03642c02107040d1031100700c20524200d0100c920b281156031b1070081507001700c807600d08081e14900d1011501e11591080c500801c01401e02e034082440c600021aa60017815100d001d54010403c01d2250f050b03002d0000d00013440c01d0300d81032602aa8420200d00d10390381c03466054288050380d8a030042150301454000c0f000b0340d07407156207003880d104c5084244501030040c021a440480d04040108110201d010f20f60700400161b4141e4441c0c10319102000b00850700780b42d082002566948a100041c1c1c0200700c41d071a5201d51103042d6a015003503a100715058011500000610603203540c40780340f0aa0019010f40702d00d400c6035075910300a080c007520181c3c090003842d00620001032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 58191028 1250 58189778 58189823
    0x90b21031c060305030307030905190501270c0308030702010b0915150307050403110406180b3307050109300903030206070804020328060b060c120901030603 69
    0xa40010301120704a0820801010201c0340e40b400000c2054004102090845119402494402e0f004405a600c10260300b0b546131000d040c0410708603256511105807101022010340203e107a510201c02d0900f0568042d81c1d0245008140d00004055400c08000300320694400d510003e0410300c0a48002402d040a40c40d2102c900100c1c80750a105901c6145c150b208040c1440646c0d00940941c0c95490815045a480f0f01d242e001a03081c050f0031650301e80d0002140400c9444021a4191200001412044035400d224008003c40e455880d030081043e5022a00b680d43d00c400001322a40011070b0361180542e01c0c0c114090050303010702920b81d103519880904482000741901c1c00021032195207030035503104c42005540000e050300c40075000d6004080010795240c0102c85181d03101e48010700317444000061000c904c1703a4410340c650042d00300c03200c00076400800c02d40f4416560109801c9071401d04140b400070407584e5500041391a101400130200310f4905990081c7c2103c0c0103103503c42440010203020503040107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 58192278 1250 58191028 58191037
    0xb03011113050d030f080901090215030a0501091e02030a0209061b0601050904030c03110f0601080309154303050d050601090f0515040b0a02061f0f090b2103 69
    0x998000080d90001d0b42d0700e04059140c04560b41038a030480705440c0d00c0c0003903c0e00000106031a07120754852144800595500b140d0440e45a941014184c590030711004480c00c6401c160002d030035080c503007211000e000000c0b0811700550049204050b03a01e603507a42040e4040d008054049402030710200d400444481d85441c01d0701c04c8400d50040780c3c40c907a070301c50800c060a0802d86e00a07001c50026000c0700301091049900f0380500840008460720100c86011141c5048026400141e094201280c41e104030f25115800d0346c0d03031070a02401b103424012291240041a80c216480748110403111b4240c04410001c9540210103500619280c01e07028480d0030090702e10350211031036484051804000a482e9030241c1c841109a84070b8151440b10782e4103040038800e0151240031416130142c028400022815031800c010000e0f116140d019002c41e003005020130001081c0c58030700201c0082c02c03c81c21700c449200301d81c3e00021100407040220f000c11544010995260074060000e000c1d440650815849003030020081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 58193528 1250 58192278 58192297
    0xc01110405011e051e09030d09060e01050c0d110a05011103070806090f04060203060f0d120206090d020615010905060307090e061207030b060105190c06050a020c030910030b030111 79
    0x1c0c01c0c5002c2004043d400011510508404034600f4002e00b00011914003060030302810110607146080b890200207850000791030001c0d00026084101449800d500c01c0d03d40305503040a00b0f04508200b082c0c0b1040d40c607911515040c1040242203070b0406000c010401444500c2a0044002c000c820044206031b001503100b110001c001c604203c0115a040c241003007800d108445034461089036445694820001c0c2d44003425256000c03010810441d100d58440780c001104921800d0103080741c40c8503180c007a0400500a0402d002034102040c079100490700840d200b40e0105080305004840400c100050b9441d00d055046540c2000011040202003600040b56500391f07043d4440154042e0344c0c20381000b000d20b4001e843e80002d40c20504040000604250800d0b80041e014101103042c0f00c584102010701c07440802e2000c000a0f40325400d80144086480781a8028200071829440d10b000c92420554a100d440080d90282101551024040c0d06c00d83c401840e0380f20040082c404100340c1c0c504154184c0001c1c080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 58194778 1250 58193528 58193537
    0x807080414090408160809061804050105040507050a0e030a0b01172506120f020c0303040b13032a1707030311030f18010e150405010c08010324020c0111040501 70
    0x320440380b8042d07401c14480d07584624035500c1d24803201205085444070901c101d803c0c0305d052008407001e40c2c1e00400fa24507441503016290300b01038000e007080203840d010303480f150003a4580010b0000b019448801c6401e42c0b02d16082540c070410111003c207182030a605d03005410400b1800012408a582812000840710410110b80307080142200c1315407182000401556a1070440c40304001083c000c40203c4240c000503c00000c0c9505001d42640c10382c0e000d28900c000c170340c000200b00010888843e0000390040c2020f12030340c1501d540b5540c0904001c2d248107424840c14a415882c0502400c003200340d10116610000707409585214451070080c580280d0821800710341040d03088001c1c1038401098070310440d20108042c8081d1102015100c401240b002c4041e0f030383d500c2f82018045902c04200c03003008001c1c08100300e212840c1c68100142100c1e030606460040200f40da00402c045100c2d0124603072840c00400717940003e00441c40e0444001c0c070840d01e48800c1d035424040a41c4024103260050011580d0a0b00d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 58196028 1250 58194778 58194809
    0x20405060a0b18011b06020306030607050304120516050106140f030a11090702030f0a020703060b030102130308031005031603051501181808030f0402030106050a0e040809040908070804 81
    0xc1110703414041c050801082e105015000b031090880c0500801903406040c03003100807202110700717000d00c0d080413819169660008280302c02c07420300b04030301a8408a18038282d030560409507202c942d80c04003003042c0340411501058440d00c0480c000642000583d100e002046840d40d900481010007402d8045544281c00e076010108290a001c108004a1580030394407214034940d04080040c403080c060804030861005110250006240200030448040c2035001005503500d1481d00e5401c1d81d40c54417101d0701a90050020120398421801114143da502007800b98985c0c0d5100641050114198410381e40b40c45008401c07012940d01030a03004c2602c0c020015180c0154400e075411542100031f126800700c0700354030b01d461410602640d002c9890341c1c151480d1104000c0c07050700c0b41511508155412000d8012000c140811072909205100c020f090035600414658941110042c00c1200280040d1020300c000400d0680c0fa5203030750000701030740c2d4411103080d1104101d0030104030b183c03c14000c000c2c040101c0d05 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 58197278 1250 58196028 58196041
    0x91f080108030901120515180f010f05012319091e0509070e0103020f0c06090d0212090d06020d020301030f05010c02070f180e0303130b0604090209010e0709050319020405 75
    0x315070310074206071141c1d80140c60740300a043c01886c0c0141031452248841d0f8000c3c4107940d441440b0711410600803046140303030412110f000102c04040c0d00403c00e440c00da1404000903600311100040c00744440700d07040e41c039484d11010b404c1d1522460755807495269001003c080c546800c070484000307881101c0080241d4501c0f26108041000e03150290587c00040ca40c0003400440c424403401410b0035042c5400750400c0341803d2407503420f8100c02c48000c143d408c04010842505802c11030b20701c180d101031008101000004844822034881c1801c42070082640361004824404250100c4a8552440101f1942c0f9a5070f81040c15001d00041800c4610f5400e013148a6802c07440041c0710000c1e10200540361710602e282c8100349014408100f02074000355110a4800e00084080c009103104003100f0110b034070780c003203245007420001c500106a00e00c181e00d410320384401741c3c88200c400e41c15207000084021458071603407801d86904c00340340c0c0800e034103100f6050366124100300071803141c003103d00c00d81e02030180e0385445 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 58198528 1250 58197278 58197283
    0xb0a03140a0b030c13090807060501052706040c020a0203030408010204240e0f1801080c010315081c020a080703120b04020903060402060a030e0703050706020d050307050409020f091f080108 83
    0x4060143d40359010702818001032600480d241c1c00c0510342c01e00010328126540c0c80c2c460f6500211400d8405903030301e400400503070420b8002400e00300141140f8600d9112100142d144120018001c00d025542c0c1c2d11050031590300801c082541d00f5001421241c44698542506000c0d5026000360086542002000f00104120910269a004c05511001c0d5030407440000d21441200808516511000d581c2c00000004112287c0a0203092040090a4900e03094000901030303403600f00c600711196a40d90010400d030200480c084c60000004020b4851802007084201e00e0710300707100d00103000807a0014200d020507400104122044180013410300030440100700b00700483c060000e903180c16402410004d8018580440208280e4110f4240060f0002204840c24600301890300202c03015440000706012250b010030260341100d80c1c0745401c515519090400a01038092846245106034001c201584002a0780302655107000001e0200854003070b07294400e41718400030074010310100d40b1100020588003000f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 58199778 1250 58198528 58198541
    0x408010507090501110a0201050306040219030b0906030304030f0b06011e02010f0b01080402010e0d06020c030406030e06010503010902060a0305040302070b16060f05011a090a091b17040308010314070b0a03140a 92
    0x140b10150120350807e0f001914280e10080c600341d48240d003080071b000c5d00e5001301400550032007a581d000031090360342000d1001c0e441001d04490b100754414001000001d1803681d82c249502d034006481009034480c0c82c0182c1c2c44001481d000740e41015003c00e016602c0383d055007e40d05a211241060103804084001075920000641c0e002e80080d0481c030306c403c0f1908003982030f0100a440303a030005103000485210740d41103400607001340f40002c0c0c940344100e90f001000c002c8240588000c400800400e2690f42c0040c80c10300c00e0441c1034091640b1500000c05160003400307040d00902c0d0030b090403a641c240c0041d03004441c2c520380340300f120000e15112915a1404042c0714543c1030711441041010100c0d501040c410365504000c001640c800305446c0d01103000070480c0520316245c0c01078414243c9811035207001820b02c460848820181c090001d007084040b9a02404050440780c11140e40c07485a05194105420b001c89900007203106400090f008400961640c004103e032a501c250303aa0094031130024001c01d4606 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 58201028 1250 58199778 58199807
    0x312170c030106050a0e12100605060301060e2b0f0b07080603060105040b0d0602041d070203090105031302030a02180a0f02040f06080c1303050312070f090611120408010507090501 79
    0x1424001800f04078012001000156143d080034413010001a00140b081ca80001c10100c00c0e40041061b00c081d0822401004060841110813a007598140300e4005e0480c003008140340e10400d400788440071407088031221a403011242031051008180745041c50b041e912035950040b00c0040e01100000c8416118030402d40c01440300a01a000c164a45030400c8003428000030320340d902c0140c0d01481d00c0092050f100810080403407541b150384440d0050866001c0480080510003950003c02c043c0c14543c0e40441103075030108070300c0c0d03010749401d9190022900d42070f2200d40007900040c0502c6180d0070f1500c0c1a00b5503100e1072034100c0030f20010082804040a0340071321f120b6041c8000d8014030500a05006190460b80a42a0b601050521a0701c1d05000c46c1105260f105462603000000d801c00400c0405098a40c052501d007007181d00a00e503400b004010400030701c904410450b811001c0481002c0031711100d410004c400056585854a9118841c000d04003603900a0100f0b0460100007000d500991038281d8080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 58202278 1250 58201028 58201051
    0x12030702090403080910020301180606090b0a032d09110312030f22030306030507090501050607060504020a090e160e0702030f0a09030602041410030209030a0206070f020901031217 79
    0x21102c3e5410b45241e140035090214501595080701c0001d90b240c4042c500a0181040d0056080306004000c03003251110341222081005900041c814605024111070b1888154a030015042c110000c100820041042502c1c8046242d03140520b54058503800103507075140074030f0101c1109082c040070147c1c1c4840911000006504c03c1c00081e000e1300f14036058a41c072299644045444140c1a400c460340361034402000c43c0801d80da0341051060000c10404c20001e0142001e08110b95418000018940e004110009003419140c0c00003608544030054448000d02c0038440038000c040500701e43c15180c811a90088003880114903001031045000180130303000301d42d0f640145140c41c28681104e261075205004a8043c042202e00000004201c1d2004100400704400040b5034255220f04210012620000c0e101c20140188144440d55401107034004290f40d040b201140d442030103240580d01000040d40c0607620411240c0000706001421400e800c01541a41c3d440443c800428841d850040043d45e003000502e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 58203528 1250 58202278 58202281
    0x1110106151d0306010312080108030913020a020c060a030b03060901020906070b040302011b03050108010b0a05011e0216080105040b09010203240613030813060507050a06020310030506040b061203070209 89
    0x90081c00c1d180c0340340350300941d8102d02c86400e00100f86030541c00c2e401206d032003016582c140f40e0594000502030260080380080c600d0318000d03400086500604440d80199180e00184005e9154020044403a201001410391030701c90030804030150040a0004041c0d000740502c1c0001084410180f08482000c60002e0505042440d262100e4201920040c411000e541d138038890260310b2050000300003840400344c0c1e0045099810a5034072401e5034000f0b03040d1805030000140074461a85c100c0d1480e03503140a001041c101e0414185800c034609525420f120344401c5503a08041007500064011500ca1400b03000040040c0d12040383c042d00701d10003200c4000070701c0c180203c206d02101845c804540c501400605a6080040c0c280580100b110990b0003221400303c00960b10207108400e142c1178008001d1030800c1400d006041d12129110000c20000420a41d400000038034101000740007070f4041e540040481d0740301c1c58176182082c4010002c0e14014810500c400c07401e22207000000071549001d6015002e43d805 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 58204778 1250 58203528 58203569
    0x10507030b0f0d0203370501050421080a1a0607050a0201090602030301061409120105090106031b0f14040603050d03020703080f150f0f040c0201060513020301080303011a04050904050c01110106 85
    0x980a00c1034400c03a80d408551b000e040c0d101c1c40e07070031008154026000020301c0c1c1010f04e004810340c009101022002d50b40c685500d02e0058000340078590040c150340380800d48114100e0a4016440e9902c1078030303800030b0042000c000340903000a4880c1564400c1e00d0302c00b2080e4a420050760740340004d11487d00041c04007482c2d0200c0f002e182c0040c01d2030380e40c00b030700c500001035074140390030f094079812164003020784e540d0f0b8400c0040c04900781c0750001c06411041000d0500341800701e000031005043c0680542152074141d800c2d919280d60740920000c681000c16210303041c81c940c0d0300074080d50054005500141d4031340041b400d039891100c8076138025420040c0d401d4640300c480d401c0c403440c1c40002c0b40d010303030080c10007900c08070540341c41c0501100312000e80e000187d454200000c01c168017074004404410188184010b02046200004590640303d40c04003414212508401080c41031146070002e0b500304040c081170008110b400160504400742c240c84404605241146007400c03542c1070b2040150503403070706100091 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 58206028 1250 58204778 58204813
    0x60f1d09030717070b0c190e0d02040b150309030307030506010f12051003060204271a0d0c080102041410030b0901090f090803180f1c0f11010507030b0f0d0203 70
    0xf800085400e03060500d0f0250b107842d1042032080300ca07183e8111001519001c150300e040e0400441d40440e0038207400043c15031002c034504401220000b40921754a40311900d250b034504a611030403207002d490032075680c81d003550243d03202d0b0030603511000480c3c2044082041036026071350a40001c2442d6464a1405940c0003c81c005010040c0c808124080b4402010010644c0ba0008001802c1c0c406c0b2040a8211620341e40c001d059098540e04d10020310703040001490311003007451005543c600300d40c0c20102095074105003101103140d52041599603c0041c1c0080e40c03a0441c0400c0f00086400c94501d00b130201c50010a60a07a684040250350041901006004c5803aaaa003d9000d0107001a80040c0d4402e899a0302c03180d0b6807040c1c4018a000118110030500502d080110541e062802c40142941041e40045494441001d0a0f03000c14405140d1000c1d159520960000952840d024000e00090500240103002440341d03583d828010101007a40388280e0a0100c0705590441c1d01400030000c01c007002c401e100e07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 58207278 1250 58206028 58206053
    0x90308150d2909010b01170105060301120309210b010602060403081b07020d081206010c0c12080c01051e060607050705060d110a020601090f05130b0402040f060f1d090307 75
    0x100242c074621001c10855446010a841448004000200c1202da00b00141a07440350400c1c0d070b8002c00c010f200622090b107411080d01d0454265003503603040a403140ca001e90b1205003d801003001c115054580c841c45907003040380300b0034103070140d10f070f081c0c01d41d8a91004a07150081254050086500d000200d42d0840034101d0103060b0782040b02e11f00d42061600d5000403c07151550341c0540340e581010a03c0900304803104441030304032009003490490f103030701c0d1341e900304582d4418420340d84041d0741410300c101030190038411030303c00c070a20070000c01061500307040145500c0304601d81340c001c0c0c3c001200001c00c1d070708108080b9800107421030700402000740b518041084650021020a00301c6856140e01c564036510040641070154254010300619070402000d44104e40a08064105450a11080c0310000d10413940700305141d500140c459a032941d40f8000704010340168101c0c480341c00d15100c800264006110b00c003d00751124842d4400703100d480c00460344170842c000e42e0300004c05d40040121030000b50340b618209 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 58208528 1250 58207278 58207313
    0xb090d150605060a051209010203010302011403060604051f0f020c010504170c1f0206070309030c060203040c0302031002041a091c150c09060e09070806010e03030f0a03090308150d 79
    0x401d2464a030b401041d504d422200800f00458030210f00390040017141c040e0540e0102c202d038000c42c259855500003c00d850300350040d444004030000042405901c80604480240c00041c06d19102030410ba9210301c1e00c1241400a44000341c1d44c0c250806015101140704118800c05964950030709081c40269001811600c218102a1045180110541d00d40d180d40c0490222021000f5080020b55480a420040c0c000e11a208061401913188002900803000d4902d89801800058481c1d440303140012440700315802c0a5810311680c081c00414074440e80041007603900d4200110010f00d038401000c0c149008a041042d44800343d00411010504081301c03040d2a0390180d5100c1c0c40a180c145444021150760b010541c000030b04d02c000510140d508243d6460b5170000a960742c95151400c22401815410040c0606041018664894449650030001e0f22107011002c06425a601000d160103070007040740034000c5012030200c40004808062940039140000c1d13003e40318600a1220740e441c040304501c0304940 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 58209778 1250 58208528 58208531
    0x1091805010f020c190305040303050a11071401020c09010b1b03160b18031305010302030c1c02030103020f12031e0409050709030b180c100201110a050d060b090d15 72
    0x5140412024007854941004101005a030360350307805400c0d030a140001c0b40c0b05e410b07040001074600010b0f80c8401110100c0e601450000d03120200c241c0202c96206682011000500c250300c00410380d03100078105105010826000c54440300c451005000e440c110900c24a0450702003481034800100d2400c181d8040d04020300c1c10f503464141c42d09201d01214014010640d20912030f8820400070b41d800300101001501540300450401103543d40c0340702a40620b0055904141c0c01002158101d84010299501c80d08031001c3c00308002000c4880f400250001d1000303a20030341d0f41003403040490402c01d02000c200218100614506100d40864150744095141450810b6500f0480010340b00d050303209803400307a0056982d404034545035085c800542c460142156040280440200d401c1000000d4000c89091042e284024840d1f26100260f00402110815411840c4000b5011881b5680300b0010b041c480c0080000304144c9850310a00d50303441c09409061a049180c40d030142010505c0d00d0490b00202011010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 58211028 1250 58209778 58209821
    0x30c0d08100b1605070b0f031608090d0c0201020c060406030f0b0103060609031e1505090f0316020121020a0809010e070b0d090c0f080a0c080604050c0607060212010f05040b03010c080109 82
    0x421b554081004020b241d080841400000d203054008540a100d8a00d0640e01d60b0600c040d12a889082c441103150038004d03860031b44400c590007408108801000244a980c44c0c50780e44101501500701c890200c0700841c6420b00701401c0f580288640b000b500d41b40d6071017003000360070341c0d0301c0100c15002c0140740c051009103a11224001100e052860705031600500000c01c036402c2c5068031500e0410810b021000b10b80042c02400511500400d40d00d410710740928045e40c26004409043c3d0117015800d100100d0300d4000901c0400300354016004c2401255004020086c24040802103610364466002c0c3c105401e00410410100550a030070a021142c0a0402000425600e610030400c04100b680311080e03541101000f50305100101300c40d03a0080c1a20300180c029440e03d565400d031211141c1d402c0500c01d980100c2c07504e091125590580e406034101041e0030005585031420b0b07003c4c4140a00c240b62145080101c0341545c2c0c00c041c00340701d48000c07290301c580b00281d007400c038403001620760010340056003100c420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 58212278 1250 58211028 58211039
    0x1504032120030705010614040c11060c07021305010905040b0f01060e0402030a150828020f01210504030207030c080d1d03030702030a0c0509010510080601051605030c0d08100b160507 80
    0x1b080d000100104903080081807400000e00041c4c1e03035050301d204144103614800c41b603001c00200306d075a03003e0802184250303100664400107240d106810100100035190500115440025510031800f0b01e000b101241c0c042d65640b034484a201100340288000106403800881e01400c280e0059904030070051008030b100700c0030041080c2c1e9541c076030380032802c194000b87c102a80100b1001ca000302e5100d540003114100242e03900400c1c1c01c5040240d503941000384124500c1c0301d202d82e02c11026510001d8400c140b10600705824000e41d82c1c03031540402d8800550441000841c000000b80228080c510380c0c4072176600745480d000100d100005d100d04507070140010000341c00107a034280301c50203170140701e11103541c0c3c02402c0c0030074080a418142c000e180180203211885070015001b11a05504c92004d00e00540c1e00c110100407007c1c04624004010000e200208075002070b02d0000c56040301d1040ca40e0b40d0f8280c595110303800c0d5031041c1241c1c81444078003502007000205180c0202c02c050452406001154229540c81 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 58213528 1250 58212278 58212281
    0x303080618070206011a0702010504150c20010206060a0608130201050c07060302041d0702150c090a060e011d0a17010e070b04030510090305090402130302150403212003070501 77
    0x48400c02c00580050005201c503d4214295400196000003205d043c503941c0d900184c0f40b489240a50b044150318072a003454420700c1072640c510710a40c4903440d400383c8202c000700c19401004240e070050160240c0300024101d420000c091004650056541c041e0726100ca900303000b1051608281030341040000c100a11103600d0400c8984010070903603400681c0c45161802d01c0840b546445440741c0110342c160188419143d0004041c828071103100c12690040d00c60541094172072085520141d009881c880340040c0340c542046454100e83c0d002e0f00e540035520716052141c40b24440b068442c6d980b01d2104003003400701e401c0080c0c1e4000904800c07000000c2450080080a02d02031040e03004012100d4000b509208007d802d020036100c0c4440c1c10018002e40c42260380180150059000b250b000315404500d0318517007540520701c42c0040d600640410a484103031104030070700b075015000c16103e01c8141000c60700301d54103085854040007800d0f559684c0c002c19030a022a82e07003200c01d02c0301005100c180039450200d14203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 58214778 1250 58213528 58213531
    0x6090c0c0a140a050c090f0601180801090f0209060f100509030102040906082109030d050703020a0c060908012007030e01090e070909060b0a14030910020706060f17070303080618 78
    0x2c0034028010000e49250051a00c095030b0442c0340524415014800c5070144100070700e8003c002401c22000104d81e44286141c83c0100394040100d543c00c04800c0810720428421661419000307035034140d800e03503a660600004482c10f80140f5048075000c0280c03404188141c010303200801005001500d060b80d07440d205020b5441c1c0f600507081c207401145a0072510301030582000c040c100004003c50614480c0340002e5240d468541500081c07001c0081c100341018428040702c2d442503407044646a84948560000341040313401d018151003076290170360281d003420a0410080200d500c3c160694500f182a60742281c00e04404441c0c5818042d4604000c11142c1150300010301c100425030303505a01e01d00c1c04004000751040c80d413001ca003aa00400c29200c0095110440c2e0100d694114402d0b5502d45992103002d281220a103807203e441c910220f0094100000b40e080349044401c0146050b400585a004d516042e50404e8034411076603000031010400680500c4416900c8000103161078411803110b0000000000c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 58216028 1250 58214778 58214813
    0xb03060103080c01141006081003052e090803061e0904060b010201150e040f080904060308190305010e011503020403080c1e03090d0602030603030417060103060506040506090c0c0a 79
    0x901103406030003c04244903038210b42d1440c600808480c2060800d44858901c0f40c0200820460440001403101102c0703d1100d00a503032000807191001c220b170181c031004003e2100341e249055030400c1040941110750156800d01c2d9006185075203541c0b81d81040181100d1034000c4980d007100389001c508002e5458007103092155000d1140410180302000c0024212581c440303a0307942403204c0e0380b410310182c0704112159520690210300751038100694100282d40e40640c000f401d5005051400c0403040050000142000500f403500c010660804004258291002406031483c1035003102c0040040c41e405d0132002c010040e45003170052404d62282ca94000c140d1241444080c02e40c84001d403d001c084c902d8001d488612a14005542840c0710341303001074058411400b025084540100128030240e07024801c960040a10701540c2e40a00c8c070141d001600c0b0107092100391007580c034040c00100a03081c203000c1d1034481d12006040041d15600c2440b128801c0d08070301c013440b56030f00c15091240001a00c0c80c42000032100e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 58217278 1250 58216028 58216043
    0x307050334030c030321110706050c090603070507030c08040e011805070203030711071806060206070e0a03060906021c0203091009110f01210b010e0301090203060105040f0b03060103 80
    0x20a10040001c0e40003440807000120441c407202080451822400349058aa1500c0d01d010040e010700791480d0f080507070320744000d401481c0620aa21018419000300f030010300c214010700c920350b104c004000c072034099141c0c1d140d0048820000502250701c030310300914500e4442e04041c0741c060b6450b1070f91051600150040c42c071600d10b000041c052010341414040354011018818001440c2c076003802510b9001c09088841886002141d40380110400d10101000d000c0e0320303070f5a110f0b039004104070381c018200600c05c00016025040200f050700e03200705c0722015502c9010304142406451170f6110340007807038072581c161b40e500e50911018000c241c605641c05021100d1030805a281d0030103010075402c03c6000c2c81007440451601503290009902c00c07824091185045584030001646040103940d000610050100548a160a8405100c3c070359444000310300340a0b41c032124400c1c00c95080c18200d414202c80650305502c4400100080d00d41a0050900000394520110b11445001c01080c0b40041c00c0c1c00803107451 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 58218528 1250 58217278 58217323
    0x807051e0a020f0306131106210f180703020108100503010510030b010f030c1415070302030a090501050903100e071814130807060c0314010303081506030c0904020903070503 76
    0x146041e480d11541071404070080d050500703080300141d218000a8000a01f501020b40c2c07100b009075503d030705450441c101c05100700070182da035078134241815100f200c143d0410a501d4000c12910b580c040011800e040c40d10008180c4c150031034006607a0180c00402c418440c03840d0400105082d1402c0c05650f00070b40c03188400d50150744c10340c51300c1422504140c01020180c2c0c200b01c0208049401c00c03c40c401200c410302507007541403106101081c3c42c5ca01d111284c074038900c0005108410958000010320f6445459544c121150f51994011130740c03032051540480c0c0c5a800f10b0381e42010f588082c0e010740c1480d40711500702c405443c0e58a070740f414440030344115800e4a0350b81701840c1060180c49108554013a00b1400075850011032507444032102d0080b0352014242c1a5130741300b000c03ca280a9070206100801c100c5d5034040a607981d1400802080f8200c60407040003000011301c1040c0d0400c0e1007624000e80c103400460b4140503486080c40003d40050400660502c03c03100c0018039030300e060101c003840b15024040000003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 58219778 1250 58218528 58218533
    0x20403120e090a180305071703010b120a0603080a0e0301090210030606080f07092138060603010911070803010602030c071a120a0b100207050f010201180807051e0a 72
    0x50b841d009160f06070386418804540d079901100c40380c400c0682d5140c148140c903102113042c0201d4003070107419016a006800400410008500d101405c1401080400e000150361142348078402d86d070f402d20008041c401c00b8000050454018091210304a10103400010461603580000d00034400380c100c0840402d03a0f406045c07106952005059510010208041c4030b50b080c4100700403e04045841402444405d212210b0600100d40c0d201c070349c01c40c1d00041d00700c090903c0300e045040c4118030404440600d401d03008100c80323010f0040200c0c51040384000d001c0b6085a1800400e1000b402a404010090702d00c10000b507000254030002a5004e1b103401d9004540f2140c03142400f83c580015074110802c0351035032416111001d849030044800d28080380701c021901d41c0b290300000003c2d003001c002d0145c0c0000c56080540c1d42d1640003c041d41290400c40303500d403250300c0080041e82201d200308081d4001c4401103c4070700104102c0d0000f042501d10a0088035110307500e00041c2500300307010424815a80e041211007205 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 58221028 1250 58219778 58219789
    0xc02060d060e100e01050d0b0c0d11040609050306041112010e0109050d020106210602090a080a11040f020c1005040302160305010c0e1206070c0507090603060b240706020904020403120e 81
    0x130341642e1024204950500c3c00082c070085c6019001056000400001076200c1c070600c2c01d54403c164014014045002204c41040d40d541040c040c3c81c00041400340d00244520300010164059500a40c120036540803020912000d000140d00320320f01da40d01c490158441c1d050034860700c1c00041c0100e015020007070030000000c0c00c1d913038190b01010101441400d82c0304107107030700d42c004503078154080001640c4105480110310407080c5030788405154010341050b0000d0150300d1788400000710f4200c40c00c000d00403104c9980000ca0141100c2d01d0b04c568440c000e4849240c1090384401d07000740c020b004650003400440c034444944c441b42d0f042215145d441e03250b08031411b90400340c4c02c00352100031103001401460300d800341e83ea1214000c0c5404208084501e00c882070041c148900000f60050130002e00a058032418404040d000748810540219440c0e03864058800d040680c2501e030f501400b1045182845684412000e500910143c07a4869400c100010010b58580c0c4025440d8070641c6500040d00005c0c1c04000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 58222278 1250 58221028 58221061
    0x31d19050d1e050a030908030115080106020303130602070c090e10060501020312150a080d020102180d08192705010206060301050108120a1e030e1209090103030c02060d060e 76
    0x5003440040b55180b400482915500381c80c0c107401c1e14001d511928480d604602a007582c0b0005007a21f40008000301e0615800c1d0aa0407000c03800d43ca5800107640da030f0702c0403a520b1101303d034070700c9034010740440c22000035000e074004240d02402900c1c1c4184246d00d4000030001c880380103d402c0c501c2e602216000130005c81c02cac0038290003400240090b602f492100880100038034001821003070200e800070803880c410303507690340a840a424200c0071100c09002d00344000c0d00030f600105041e030224010701c00c00040c4d8a4000c4400007425404544070741050540c03001403445e0100821510244002001d003e051115107562082e5000740c0b5684100e6284e28210029040120181ca101e01a9040000501c100740d0009410031030043e506000554030720120004440c0c411034181c8480004c3d801d848031064503a81604042c2c0342100240c25a405088002c1074000c943c41200716180d00100244010030100740158442d24010340058400ca1070420040c0384402100d034290462100ca0f02103d0900c11248480381004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 58223528 1250 58222278 58222303
    0x1602031204030804150201090605040b071d0607060203091e0705090c1206240c0607171b0d0b04050a05040308010503070b04051504080d0903150c0f031d1905 69
    0x1103280509640f20034016205a00524901c04440d494454003140300b580701440d502d801c0760041040c3e040502c0c0000117a003081c2c415a00007440c0c0e91008040303514100701100301c1440204000d142c0400ca903140390203500000d003520300601404141800c0899400c1109107009598409130001c0360406c0c00308014641d000d000104048000d010071040b12944101c5250461000c4031300d0b20300d170a4007283e91002c680b4580d46004841c10007040780b00e0010400501c0d140115016107529100112019141e10801c000311109010300301040c034a442001303080002000003a1600001041c1c0b414050040341c140c41003903801e405555501c6040100f8164000d2010b405003c04030054000240b424804901602940c06914840c1d40c0026008400b01c210b00200c0c0c2c018001103007940c00c40e507120800030303180c0395640c80240e03200e40d1902d40c40d81a90b0410f1143c0c1e280c024072900e0b56a51092404000c4000301040f280940c506160f1a0030610f002408001c14103150024003111299541c0705d1520f0740c10440c0d403c111 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 58224778 1250 58223528 58223563
    0x201180203100906020d15050301060b0901020d08041704030819180504022203080a030e2b031509020901031b0f0804050307061406010806030c030c1e06160203 70
    0x440040c0e41c003050b111448050303a00007003000489410030304000c4c45624800085c241c80c1c040120308020303c45568804130342c42140204800d556a00c440c040c640300720b0742881e0068003e90712003652a070040750510b4009004004103031282e0142c4007a084035904c140c109071800c1c0f80116251181003150302c0812501003882c9801908184040e00300d280c0c00072680a0380340f00340e03004640c560b812149202600040302105040715100c584c0c034100821198800410400000d042a200e460072100008803602c0d58000301440d80c0105036100c20314403000c0c119208200415403504051183c6c107801c0c00405000e401811401a928005040050120ba0f40403c01c0d140314004485150112a0440c1090701010a5414681c0303440c5d480c0c0c0781c00b50540c4220800204203030703c2e10501c1e840e0083d13904101d0340309500a89480246032241010540d035038241c01c0c1020792660140c00024481d080c00000c00000c541e122440b00400c03075605001230034940020324a817010041c0000d10009510f01000000046400e8004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 58226028 1250 58224778 58224821
    0x30a05160c0b0a0f020d06060801030302120301050906010e011101050405011a0a0f0605070201090806010605071401090b0103021003020c0a08090405011e05011b06091103060702010b011b020d021801060201 90
    0x307a100301c01c00c000300a43d600564602152100c5062601100e0a00480f00c0c8200030f0280c480002401243c02070000382c00622a4100307030a2440c4058044906a0300300806501d000d6031500c1c0119110710008c0d103410304020201081c10300d02582400b0b40c034001c51241c0c1c00440e44840800000c42c070350030b11221300f504c00c034040d800800100c42044a40f070280c0d00103146c95580c82280b0300040e0340c910030a5001d940c0a109044c000110181d108001c0d04000b8850301c5d1780401000304584507030a894a13102c0190110900000400062502d1810013031303002d1703035814050304003855892680e003041c00100d0251401c0200081944e150701d0180704650241c00409202d5050003030100032600040d02502985040c440c01d00c401400c0080d01c90511054941d00120a200c1e2281c907281075640c402410400743d010788140b8004c03440850043c000e0f41480329044e0354090022000303010100d07505101301350036608140b446c80039401503100c85d011201010510b00c424002e035454150001d0031140c2118020742940e22446 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 58227278 1250 58226028 58226033
    0x609060614040911040e2a0102060a0b0f010f120c03050f0603011407080c0f04082103010b0a081b0a02060f15010c081c020a030914070f12080c03030a05160c 69
    0xa09445509030161400503408955074803847c80c00c8600b1051000d00b0450003084940d191002a017a00e0a14080c1d081d80c07026100e1500050a80d40c0d11103e00303600249040e401081c65105d984204104107031443c1940000b03244400c00390440325842c606900003504c81040000c2c050b0010f003403d421039001c1d0000c01c810030301606109941600a04080308020911000c1420012000c06407074424950308055a0f0300c070741d035465240d5501e403013281c03504408103040f103800c10f041c503060240d90484121900403032400c003d0f010300321010100203080007a42540e07040304508480d0302d80f010700742215080d00249481c0c201401c0300325a00034002c000d84000e01d602c0010540d240d038440070038100e01e41d00004a90b1280704101c0e50003002c4014500f0f40140610102e4007203080b643c150410440340703014044000d907201e208007505444a095028039122a4929a4108400d040c42d50f40201d10328081c1554508000b00290030600310307403044d6400d48a01d0745480500980d00031056820b402c8489038140040d403200d259 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 58228528 1250 58227278 58227293
    0x403050717070e0a0e1506030d030c0207050409020301020f0409150b0702030d03020307121a0a080601050907140f070f1502030601120b0a0503030c030408010e16150c06090606140409 80
    0x90040e599004030103c041070714208141c00081c6040c0760300043d030304118045025036002c800c0444603a4440e220314406038508900034401c000c5410310340d6024249440c1080180005041e0040040342c0542d420880c04c0602c14800700644041e000f2000302107400c818001c000d0440c4105900300c0d074100241080200e00581d400644d0058050013801d001d038407075a4110098402608120051040c281000c03400d81b29804d15045001502c00300325004100241c9a100450f0360b0402406120341240506002c41c503541d02841c0d0a04000120ba0540c40c548000904000540d8000c0c400c11104c01a486010b141004044120601d10701c1440300c1c11170843c507000c0d0000740649941c4449031a01c50781c400075420281c0b10a6106400b4200207400c4940d6200280d0340f40307569900510500c00994030380345c80441c65040106d59000b4911001140014031420403003000000003900303103080280700d5009941000a03d660282240d49802400c0c0003030540e1074040134000714419103c8103445586840725080014000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 58229778 1250 58228528 58228543
    0x2d191d1005071103030405010506011206050a12050a0c2723040507090603200102010902030a03030e0115061106090303060a12020d0f050f25090f150b0403050717 71
    0x48200418103880c0c0c40300030b8611010f102c1d46105140000030411050200542006004810a0740c40030341c0b080c41030103a04200c403568091503512101044c0e0404c10607544c07065500c0d45902400956503a07141d107035643e89155030345a01c0f510712404030480c1540c20303002c8650b104100c5c00312100c0511017000000d600c42403082800100e842c807030310404003040922104200d0040a41500001040610389904020b105038002000c05810b00340e50714807401e980e510600034601e031154060000c0c80e03058001d507400c0d00074103903c5c42148410341d80c895590781441d01206103000180501d45801e640d10340c0380c603045410030304000c4c00004c0710387c020014000c0507241c0321001001c43d20100b0004099490610008107a40d444160143c101208081e00e6414441c01007994081c40c0004001c544401c1c184032424a40f030340641403c1080d0f00c0d00d00304204020040c94100d440fa01d00e81c841c00240d601910b000f20503d0140c1e54201003a08a000300c4e0a1041110030081c00002d8207401e0041c049081200e9801a03460780f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 58231028 1250 58229778 58229803
    0x40f0603090528060f0c050307110a120504080609161e080102120609010603060308090405060103090b091b0103060302060a03020c1009080d11070302062d191d 70
    0x2964081c01052200c2440540c0c802d1007039007220007440c1100c0c4000c026141e0840300c1034840c0e600d401e07004030b80c0324003900c00c4441c08089074a51908650310000c043d03a0064446a15034043d0141071002000102e070411202007424403900d80a841b01c0c18005902e1074903000a0403400587c1c806840f81c15a00e100040e5842141c17800c04002c005009a80081c030004d10266010f41d5030303980045001d8000e82c0b4204613440c4508021740d100e00320740e0b9803444e048098070b005100141000c00c040043c0c403d5030506412a6501c0407040c100483d8404544e51601c02c0890102c03442841600304c19141085030343c00c180c6800650b0390901c0c082c4000350450300042e4840c440e6031042010f2641c001201d400f01141401104601210380d0001c1000c443c103030501d4407442d4005c0c0c1070f07161203500d001d00803219003010300d041d16261a0075500400c030b542d998034400c0400c1d01102c000c0050002502d641c42c1c00c0b085020318400e1242c404492506003980c400d4110f1000d0b80c9080041500301a11000341c0c09004e40006000e161508 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 58232278 1250 58231028 58231031
    0x1305070308030702070b030c04090b0102070f0909080c06090d02011a13021305030d0309030824041e0f0605040605030a03020a0b06040902060403030806010e040b0612090309060403030809070605040f0603 89
    0x4840ea54143c0c45c1c5201079002601401020007040100f240960103481113580590007030100c0b0000e03100498607401d46004a07082d01d100f10b0414014011030ba809041c21601ca40c2840d441c2030f00300410180b4001003150100300c2980001d00092030954203018030200c2c138010550810320f8040d648001040c0540b0046028006540800c40c05010502c0000b04002000085c044d10040e80c07480400a01410640005070702060007000072942404103400c8281c44107004183d240004c05080d010030000d060b5850782428007400c24207109448031054420412030541c004400180b0501d0030060009555140e03000510030380116081001180d00480c0d8850a9030b0700c000714109640c0e0308070014000b00b004040281d04800046404020540c0280c000c90040000341c80c0d071004441c200e01004240c6e041c0160058110740140081020400340001c0e144c0c010a0b4281903d0901818801260752904154810b07400650b1103014448442d1051020b00043c1c1964500b244c6001d0920003100c806006510400c0c0400d17 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 58233528 1250 58232278 58232281
    0x80a020108060d0f0b0a0e0607080411010e04060f051815090907120c0303020c040b060d0c020a060908120c03070503010302100203120c0c010b030f0709180501050a090605130507030803 81
    0x3e5944104850a03141c0c00400c41d810a6040e0420303042d002d10031140030000c5c80c604211410086070014099200d083c1c0c555a120185d69159207030070030081d00310742840c103100b4440070900711540c5600a80c00940290365800804625040c200311820030303840f45801c18041d0340700c1031001e840b410681c0301000c0315058440009645810b84030074500b5541e41d2100c04074050b0202d204003040414824031301240e000358212000324030810200411601c0040c0d005500c20340c20071041d6584509500f140d0171b94600ca0040d120700d40c0c80c6440d80e00540e42005411204240009010a914400b04048641040710341d46010708501e0f04000c007418510042c08040d01c034030080f01000d0080791080040302c420200e02459000300c0e0504600d200210b41081c07801c100e0a508004030540d8506000445034401d190901c01081070a2034549800001c10321401e00e0103140368602010000b00758240602409003030b900c8030002e03002920b410000203c420140848070008a807410000100c2d41c002480000d50340c0054450390749 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 58234778 1250 58233528 58233541
    0xf111b1c080a0e031e0a060b1801170c090a020c150c040e06040902060705010605090c090d120203130602070e0f010e07030506040e0f0a020a0f0612052a030a060b0301080a020108 78
    0x42205904031000005e0034828104c5071020080341c228030003441080b080c054034440e17004219444c500700e43c10240403040e80d801004400101d42000901e0306411050b5868006a000403c5040b01c0c1141c980d4511900081c1c20600100100131030501105285100382040c2050451034080780709520038051f07400c0d102808100281c0c1c45602074128203500400031035691251785403e5020745500d1041c0da106100d51000648502c658500f2102020700c02001c05200c08110341e102c22000426858280841c40107212000b052400300c844103018203035079001001018a0842c074025690b85c000c20240c00c14050100400440240c9030b503560f000300f003900700400c49988640100700101501a01c044162190308801c4034100c034041040e454080c003d41c1e070408a00c2c1c640d4618440000a0322401000682c41c2c1c6a001d00f0001a5005642002c60428107060050307030081101e00c41010042c803074801400000a11a110615100740001010b440c0fa005086614080b1001c4c2c40b80441240a81401219000900c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 58236028 1250 58234778 58234783
    0x6060f03090203150f09060105040501210c0e0403180f0513020702030a08031f08030c0c0d17040605120a060b040603020f0405060403060507081003020a060f111b1c080a0e03 76
    0x20400d202d85811325a10f801520700060b000262a1000c0600400001185a04240c015581607500030011488010500a600c50502400302401d440350217000c02c02203503111011804502072800703648c41415560a803420419800c106901c0b00c0c07603144010740d040090f601c51122403441070500080042e140c051500120382000607034030008000c4540042000a4440722402e480e0b078444900c5202d01405403a01d10b440d0f50b80c071800c05d001c0c41c81da200c2640340240c1e241101814803401d00c600d4608103000d00700c94080001b03401c130790000404a1400305000c14413400d82035540d580031441c031000380111440d19802c84400c7c40382d070007150100754001030403000500742e100c102d13002000007a1510381e0352642c030309000009000031365440c4000703500c420102c0e030004030025107501600c0d001094007002d90703d403200544102c51680f40120600900f000c020024000600c84c510115645900140c00341380720104024518000e00401042c6040b03100c0f603600411020800d03102034081c18245052502d070000d00103031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 58237278 1250 58236028 58236043
    0xb03090c0307151404051c0c030b070309021e0109090209011b0501050106031d0613060b04021603080c1e0904060807080d080f07020307060f020904060f080d0306060f03090203 77
    0x340c1601ca4030200045001c401d0f01c41003d084000d946551a028280c11035642d07600c00d070b03c50300e94450f000000411000540c51186074245210352035542d40c5503901d40c3c1d07000c010700c011141c40000c0381e0f0356542403056017845052443c40c1c2d462083c180c40b481e824000041e00d11071180c022410b000f83c0c0840e0a0059900681500710440e04001e80700300b88184a183c401d0180c8000d02580380007c4c2804820b11a0002500c04140b01802800c05040643e8030000120120b11050505403100c41e04c41c64140260b45035071009040c04201d100f03c180e01c8103201e090140440750083c01503000c074681000311400440407005c90b4816400d148810313981d13604800c8001405040030317401c1402d0b503005071940000c061200180034070703600b450750b116160309070b84030b0400c00d0280c8400c56075600980c00420103100011220741c0070649080c81c01c0401800c05210001140071241c2a8008505034848460305102c4007508220a000c80b44092406004107801d01c2e00040c0380c8866802e1803000d05480b000b156085640a02140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 58238528 1250 58237278 58237303
    0x604060c151d010204031106031306020310120609020f010203030907030b04050f0609060f1b07030302091f0e0f03010c020a12020a1e12080702030a2703081903050403090b0309 77
    0x10308070100c2c40200e503000354007074481110070680c007004180503424100143c91080d4513050b224607404086440f0080690700041088054821840020a4820a0051001886000b1040010710b11f0a45c8123001007041c185158506540c8140100210360500084a0007030340c0d4006c4904115446620f410703440c1c00094088034400e4091441001750012001600611981404503030030541c2d12400c000e00400c40300244100c40700c4c0010026403003c240030750000c0c541c080d00501040040200f0100c0d601020014010640005507900314030b500c14601810001510f9208400030002c1010081000c0e6840c2c01c05600205226800001400c4a5000340411941c1c0d54001e150341522003042004001295442c11040341d41c001c06074819001300d8890703075a062092105030029444e1076400309090711818441c0c01780704210708a000e1060081381c80c0d100c20398011440f811600d40c5030f50388010741c81c0e013540720600c407103080514110030040461760000c0040d0840c0c000700c5086643c1d8840e0302004c0d0800400c6041c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 58239778 1250 58238528 58238561
    0x1c05100f020316050306010c0b090a0501111801030b060a11030c010203270f15100512010b01090e0906040303050c07050114010e070e031b06090a060302090307050604060c15 76
    0x800003003103503600258030680c544007669403103500e90380064646000994183d40003501d400110300004980c41c0400303030004225000c0700c007281e039290741e03003800e507098803102c2e156201c1c000c40c1c40c1a00e15640b000b071070040a02428280004440b20340402e8290003640c12a408002c0c50000c41c142104061048441140a0400941d5a13251035046041280088060b001c1c4003203140c440e08145241c049000f00201c8001030141610348003200d03050110407405003c0d000820a07100300050a60b50b103500040000f8410b800224681040100151410700142e00880120542c40d00f04120944081200f65005506080c0040c2c95180c2007008a094000e03078030002c20541c40e0280d0f1400540101010b02d040321450a050222603940d07020840d5150404050700d038065110f408400c0002a02171409042d101024064506001c4008006000201c1c10351101021950000f881100c9003003c2c08050040c15003030312032615151911800410314405028040c1100400718000700f400122504228130419003c1c02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 58241028 1250 58239778 58239791
    0x9040c0f0906030c060e060a030b03030c0a06150801060605190e040c0201020c250e04060912050a020f03030f0a050405070e16120b0f0108041506030f061404021c0510 73
    0x2008009050b94001940c085030080b030001072140c0300e11041806020003404540c10f2114080054014240414950390b0500040c0007000003902d0800c85000d0483c020b000208601c0341102c008120085160802d40c5164141602448001d422404032505041034a2101d9031226070003c048468068a07040160310a0904010394281d5605402503c401a220801d031410b00c0c0100c40303401d07001303400800d440d00c0e016030545080000e02d10039a0001d034802d02801e008111200d542d41e41802a40c900041580400c101140d20150f05504003d039094003407041006501e10f0070041e442c503001e442d00520140079030751510001000c100c03080c05054003c001440c021546070034680442040f04295618440024480d00c030007280300034103070040c0b001b1a180980400b030f0f040249001143d500c04001c0041d0b413a44050a0712540169091080074001d500440d10101d49070030b586040001c3d034074501c10800c0c100c5400018400946e8840c88101c01144080028454685041c036086042c004a56408aa824500503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 58242278 1250 58241028 58241039
    0xf110c03070603060e070905030c0402070303020903030304030f0206130b0a09050102090a0b0406121e050702071e050103050f090c01050903010f1e05010501020a1502090111030703110c0102010b030c09040c0f 91
    0x803c6401074401611740100c190391060b03411074032544c4502c0b4103130b41640543c5401010342401c0c3d004142c454000e14001d0f00e003c2203040401d15641c82940e00301c00140303003d51a0a46183d041c40103c5e00114803805135013210040743c4503003d100c200544544000e958402140003017000c254116444000040c0c00b4481860f034802c485402a0042e00c1403002240e02c0301c0c0e810303800d40368520504020450101d221501002005042001084002d200500f54403900f44080740c00150720042a4504802c1d40b6800002820032000400b41e40b00500302184c0b041e142024025114004504840c0480080c68003c0d25043c0c403c1c0000c6c050407a09002c000701d40d103490340400b0101500001c0762400d205044041c421644e8a00049030358031f100844c0640140381c0104036811800d410340040098190500d000c00c002d0001030880343c11940036403030407000709158070000851000d05024204000c9802d0000f0001a81d52101007511850007c0b1710702c3c42040b0160005042000289100000d42008201e40d602c1d140c075003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 58243528 1250 58242278 58242281
    0x702061f0810060f06020c091518090105160305151003021905040302100c020a0314070308030c0c010501061b08130e010305150a0908070f05120f041403060402010f110c03070603 78
    0x1401249a20041c105005c1005400060701c0c50001d03030003426094540e034a002c100d5044403803034400c481e48003801c1008000d091810b031080c00e00442c000c400000c1c0605000c0d4074101401d005c0f050120900d4101010881e490f00d442d00c8580719404151240000720603c4038046001b03118988503200180d0696a41696080d030000141059a2085d1034500c00035402050640c3d0305020250021340c0451010414400188070940f40d4140302070010032250041d481380d50307540352508200c4151405001c0451264110380003401500e00515403418082202281300c40500105024100c000d481a940080d014210128608155004003a20341c1c400744103503101c1c034001c0e89607444c4001c49900221010003040c882d440903c200840e20b50304c04c02c2240390582d1035980c030100c62440c01c0c0903207003400341801901c0c96400c600010300f460a44000c01aa4807400c1c10404d120600200480d140698840410000180d800c0640480141030324100346a40301500381c2100d2800d040b9183c0d030340c0c05000791840040c240382c25 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 58244778 1250 58243528 58243541
    0x7031125060507020f060108160506070519080d140c03060409021201090b07090906080303160c0c0e090d05040b0d1d0d0f0e010503070905011101060302041406030607080702061f0810 80
    0x105020341b025a41c0e10249950b450b803003d0710070140c0403003600e01002103241460060080d140314100361010348a0030880301e00c24418801040d11007002c00a1200d86203082e5108001c800181008628514207228aa0300d540740001882e0794041c550b500054000d540c0d40c1284171040081e90030082c000403045203040b202c40041614000003003411128007180d006090301801043e2845440118216556101d00380c0d4072280302842c02c8240301504402170003041c40c1e0f42c0032501514500c0c11180080c1810601d00e4508803140345100200001880148440e01025049a141c00c0484d180410081440514098490780f00e603420403040c0319808442c503085410580b049050171140d107030388009041020054855200032100040003030400c6209105035801003042a100040c424000a1241e40340d074003090841300031600741d40301003c0000404c00b640c0350800400b9130041d003515105060341407041c0080d540303001c040e004079a1048402c001010018101861000806003042124540120180040000e004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 58246028 1250 58244778 58244803
    0x1090b07061a0904030f050702270601020d020c0a091a0904030c0309090504080306010c08040b1305100327051903080901050903040f03082d0409050703112506050702 73
    0x2801040c4203051400034400f600c02d81d0540c0b05e030000000d00c0710040702c02d9032107010220b030300000040a4000d5a440030704508101d1540b00409403240c14100700192812100120720001c5604c803050007a800d0720342d0000401120840600400e2000c0144000034030701003402100758010081d8020041410360040c030301c0e0005402501e55524442c1c0718100c44054131401c480140070b5101c10008a03080394850015101c880340503a4400c0d050135210000c1d02c2c6158840c81c1003840070221000103222078a040b00c0c0c84c104038003550408110a941200760340400c0217606c0d0a603020000040f801101340402071103c1d4010201580010f20301c9521031801409880701039403048502c1d864440011003011780041101d0a5070107101c5860105031440d41c801d402030f0302c1130071001049110701180d01103058181d8181042002c14040d519100e40c00e1403031200444200501d07030402c260034214403e100103404001c0351008025407903000013000e20240350841000d0a0300c0001d11007403600c02001402079000c1802d112905 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 58247278 1250 58246028 58246061
    0x8040611010207030e10020c03120a0314011401050a0207030503030a09060c090b0d0b01020106031403030106020d031109010e0612040c17120d050709030c030605010e06010c0302100b01090b0706 85
    0x1500c502a0600300d0050403c02408600200d41300c0500b40383ca0740703501c40c00005600c11a05880403600100c1e0a0a04010041248e49000304070040c0c841d80500030b00b0041e0816081150043d85015602e0480e48620004d8605203c400510303004224801c1c840d40026640100449070399050000301e0700001c200420040d25080e00e09145021500d10448035041114240c0f01030a06205800d080030004000c0034140c1c9041d50b40c5c450000000a00222511801c5405a4050364480d8034216029040c0301000c800d8004051405452000d2004011f00f0f03a2803581003864090344681000b4081a454440c103421000b00045040400c0b00300b000c07a00c441c409980c402c540c4000001650307140d0750f54035540760700b8492030080b00b03014100c03c59007941c1c0000c0c1e00c01141c0c604988005c4c1e5a85075892022041d0700159800368031500148441c9001901942e00300c1c40138600108180e1079505c0094441c2000b540600015842c0c0500c00070302da10400508010304040c1010325510006d40c50b0680c014904000c41e41e0015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 58248528 1250 58247278 58247297
    0x2060918090a060b0d02030601141c0f050d0801030807080d02160606030203071203050301050d03091203050c150708160e030708030c070603090b010e061504060f09050303041d090a050109080406 85
    0x2402d01d17660070403900c1e40c094001c0c4440d9081c0010145400080840c2d20307080b079064403a90891030760440c6006020780c0034885040700741c0118109142003080000068003031001c0d0400403c0080c07541022642d6158002105980310565007a44070041d00c590340d80d011155040d0329410b0241708890b401101244d100310b04981340ea030351701d825141035020300d01000b5001c40c034140010442420480302c0380c142c851080c03402107046ca40754522040f03404000300c1c094001600209828103054820442c04c0c0f880c0350b40d419000018681400010240c2d00000d040315074914483c1c407a01501030003182c08025141004090310031458079880700641c0ca812150021040b40720318800040c00c0d41c0030b0300c1414070240c0c11025000d4a0703070909070180504407003c0c00031a048901862884400d0040c640a00f01914032540c0c0c000d440300c03482400400c6101150440c0340710340c200308420072080c2409031204030400b1480316203491558484008904260125030f01a066500340b458407002c102d00f1000520540d40c16440d8000507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 58249778 1250 58248528 58248551
    0x4030e010f02120406030f0608030a082406090409060e060c0c060105060901140a12110901080603060f130f050a030e030d1107030f0809100504090b040b09010302060918090a06 77
    0x44a60f4810218110181040180130640c801d030000300c00c900c0c6007080030138001e54032074900d03107168400344030800040e8030380c810b2045810a01010400802500c4400d888020701c003000140701e44641c4008520496952075000100a000d820080018245609941e410703c0d0003451461181d010310104800340c0034600000c5403500e0854140d410b00181a50b480c000040301c1070004e41e16611100e20402401000200400321485901556010302814200a622112007000140c080100a040b45100b50003800c00c11042801041071980d000740c40800210000c0100c1c10600000c43c2e2007003000d805130080e01521410b05070040c40f640b20000c000c0d4215000c14800e40d1040340c2c9119a8001300740c25400080003003010818028040b001e0324021041035250005010000c2da402e40074421110200f40c0200b020000c50f10144180220040140c600b8010320001da80040c03007820050000078030560f03021270140066145c90101d1118414450050423881c205100c0107996200301480c01c94200d414241108030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 58251028 1250 58249778 58249783
    0x40c030501031a07050c0601060f0807020c0d02090604020f030c07020f030a0302030703230a08040605010501050405030304090518060421210914030403081806090a09090f0b04030e010f02 82
    0x40b41d400811014080740e84081c8088052005411541000030070710080841140c00e0240c10b00034402a04d603d01c08041c0400c3c06030000000a2800095401c840c81000840c1c40e4010119000756046aa000c45595507200183c001d01441200030701c2d040011080142c2072621800a05030b140c0211280c0410138901802c01d95150212040100160401d210100000e13014035120041c0e82d44650075061804003015610f801ca1b003009501d8000501c4450a10040c0401e41c400c450142000307190851509080c400862b0b17492003240300700c100c0c00d80d407040000c071241c0100401d5121000700c101a80e03840d082c01d007020f58a5906a030200d480b01142c01c0c20506465014040c613a002a03a0000c403200c2091174000064010841d1410aa441d090030a260b6240d85d0424070060002c1c510920740b07103886400100625080d1007040303400318001e42e0100041c04866403100049000c0715484000481c101041e4501090040884a0000d10b05001c08050004150304505550030480d420380c3c4a0608405015040303a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 58252278 1250 58251028 58251031
    0x11e050912010e0a06050a1d160506042304090f080a0f03090209040308100902031f05060a02190807020a03030906020f0604020f010c0f0b07050901090b09130921050306040c0305 78
    0x1220350014007110001009a00100d50100c42d081f000a0b840200689030821181240360140168001600040002c010054042d002d850150b4000e400e060400b029412549035240d4001840301e070032203000c4802c1c2e0b106d801c80492654040760b0030340350030400d1a040009410030120790021403184a00b10360340700d101e03104040c3c03ca0303001895291141c40d41d4405582c915030140604210316080000440c1e4480b2a00040d405500503a24540c40c1903c058030080b4103003410f4001c01d100d50020840c00302c50a90024500403010300c0001b070305040400364a040403151045580c000d4006002803070001c14107400110381c8041b02c4070394090701e00304044064182d442e1f40085038003d600410010912251354070604080000c680300d00b440c24000c1c03843d51205080c910003100d031400007410002e00c0c540d42c0c2d640709844100807c0c001890b5410700e1007400028060020302d0f20940c60480d6034041040a1007840f8402065150f070703120020b083d114064030020031691040302d200c0d0165003003140140d801403103441582d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 58253528 1250 58252278 58252301
    0x50403020310050712270c05010f0e0303030406020c16030b060108010506031b0a1106010e04110603040c0605070314030a050117030405150c010e1204030213180f02011e05091201 78
    0x28605221041285001803401c1d00c040c00d10074500d1604209520b9101c80485c546c2030003000d0406210345800d00060a4403802034140742000f0004881070400c1c2c03030010959070040c0e0b21500258480d4510302d5110314001d003491800540b42914000001481201444603010340000e0740d038466240e0b210005d00c80c540c0300c00d9a180f0413403902452904c201c1443c44020700f500103070a251081142000c001910700d8a10203800c0024000140701c02d20040002c6110b4012410070203541c00380c218a4503031100c0d4080702d03107031064005000300040c050b42010301c907000d95609442c9a4940544a05042c803601000b45002d0141c0040300042500061202000206072001c07650010301e1003403182400340c420582604980c10100307441d1340313803030030503040303d20078007081030b0f0b103110806500d4980746140100a080440a03805000c3c99250500c0a030842c0d42c2460690f0703107103821413000344800d0703401d200486030302c42c00c10b0002e00b20b964080d401d80902c55028004007115142101d8000d00000c1d540083c40c00c803083d64010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 58254778 1250 58253528 58253537
    0x20c090903090906011404090e011b200304030215090307080f0a020103020d0e010501030506040605060604060c030c031709030703090b0901080f090705040219021b0a1211100504030203100507 84
    0x22412910301407460310750101301031604a4140348900f21080a41c1c201740c2041110b651521b0100c42950803d1007494401312030000707010401d8800030000350800180561014032002d10036100102010100200c9000719805000990044008020580b80341c01c441c2a26120303005440c0001400a00001e00c220070003040c8000c2c0900c0d03991640107500a5100c80d0221510725180d14100342c0381c09081c46014000c600540c040d0100b8601407034103e046401c0200745a204032028081400311a502134481d000c1907905091505660314581010b0396a03000303207550101004401d20800c044050040058242c66100e51204040c03980c682e02d620007207010b190007150008204d1400610f20101c10248950024501b01c01d43e13000710b4885001c83c00ba030b4442c2000250055070031b030328031808580c10010200000344d030ba9802c400f5201d04400090b0b1406a038411503460301c40c488011401d100f0118000081030740c00400082c802c0c0e0049a01402d50381007403000b0391181c080c1c041400030030146405481d00c9001659503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 58256028 1250 58254778 58254787
    0x606090e0f100209030a060e010506030d080c0901030509010212042301090b06151c0207020909060405070e06030c0406080637020706110d060503061005090c0a0c0503041203020c090903 81
    0x100b00300a40100e014150b241c0f03c0ea090301004a0114400d20b503054440500201c2c4500e400300625250002e0440e00c4010848001c041040c0340040009461071003a00740380105840d21041002030180c010100090403500c0c043e8103010401202044040c5601d28411841041040240115080f80e41d2a500601002d40390000901c1a02e40002410b155000340245942413624098101c0e13880002034900080c8164001040f02c03d5141800499030301200b250000d26040c505544d6042c0ca60529106500016000c10041403140e034050001c00c84581c0050010401c80d0b84e2208440e64981064078420401217403082088100307030760340d001c40040c082a44041d01841c82551081c0f80203610944003a200c242c0e44001ca602007080c940010704c0304e0704c4191400304129081804060506102900d4500c4840009000708182d4603845802e84d8800c803003002e00d6031035101e0340d80180c410443c8141c2c0140a80800100425810701810964032400d001c0d900300c50381c10a040041c020043c006a85800d201c1e4410301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 58257278 1250 58256028 58256053
    0x12090609040e030712020106050102070b1603030c0e060a1d060c060f0606070602030c030601030608010e0703060b03100203010b130621051803030a09051204060c02090a09050a0606090e0f 82
    0x40242c10b005001e41c0c1241d04d05072894075410300c00304a949001005175101d640c1040650317410081240586242074841e890901e6500b0001030b454040d020003400c1c55210303200d8840700e03406400e0080c500040135241c195962070b03210f0700505142007109840c00500441c0c0c000b60742801d00c84e060760150142c14008040903181c005160070020b20042c0010b90001d030402416000ae07400380080c60040000c80489612420180b0015080d290346400c541c00ca68501241c520499a0014100b07045030340008002500320f0403000843d0901405c0c001d0070140034000800002e01c410b03003000a0140d2200c1e8110310340f0050711210211480c0210b0019440d205a1908540e2130610a0703610664001d85038842102c00c501c11603a1782411a00115a42c803119941d507a076040520809024030000c040f0301e240ba01c1e1509081c40700c084c24000820601034010800f90b0700040c404a5507030f20882d0115084021601c07592007074075200000d40382601070074a181e81401c1400f40c2103a00050024250304040340580350645198 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 58258528 1250 58257278 58257281
    0x1080c090411100819050c0f160203070e0403120608100e0a050d0207090e030f031503240402040614010c080a0201110c0a05071e03030f050f1207021209060904 70
    0x303003090302c2d80c40301104040780315902d41240440c1e100d602c0d2a000c0140c0380c03028443d100288050940b0f20454101001c000400520700e0481d5440c5110f6141e007510340c0690824400010407217030001350188592400800c5001040d8201e911a500c0b9503504200300001c00711000c15100a4070505080d1f40c41607001c001441c1c0207822419000c003082c011074035400c88030384800345000203480312100942c002d65804d014503500b0b802240d1a0ba4903e900851070320402c8036503011140700080c03a80d15820351030701e011307026558240b01c801d0b80c01c0c051034891504050100e642e010000016181240300b0317450300000150b5141d4150088580c040140c40e80700d14019217850b6205c10340d02100c14482155038480c0311150b41303c208006014400c209400a21000c4520310b00320b407070013072035130080108a11007800d540d00c049098080e88003901c0e41403414901c0080171040a45850003000640301e40c5034408500852484400032003140708070a598201e8500d08003040000807144200451190400300070401c454050805 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 58259778 1250 58258528 58258531
    0x1204020906040f090c030302060601090e04110d050f0c130606020c090a110705010b12070e0109020d060b070602070210090b16020d050d0203040306060e01121101020c13020901030f020301080c09 85
    0x740c408906140042d00f01c004a603800e000803203110044071070134010706604000084c1d11a10070b0801d0075002c1c0c10240d1480400a0082c402041805080f427000c409440d903203003201c9244e600c071081718045a5104c01c42d603100d0940758941d5002d8a006210305154038264013591007111100e402401001860070144240c403680103041d001c19036140c074407260b031900c02c51008200c01c0780100c00010350401c40307030704204408680801d030122070b5120a03418002081e400c030105044406021005079602818003405010344002c0e4040e070305c0000c0100f0f1000500c40da903002000c02c5803084400c01054240320000340c071000351601620f9109801406035203100e4070086a5891202e0008248105140003a6202031a18100c05c541c040140c201280810400c075041c058980685440030142c8071a60500c8501a402c0c00d4088001e40501e50b9402078842a900902c2080c801c0100a0715802c0d881554142c42c1010b980507040c0a8002864400560803001c00c034403d07641a1801c0801424621280b0001c001d0038240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 58261028 1250 58259778 58259791
    0x30709060c11031b01120531020904030f02100c0503070302090102161706090309030303040308071107030c150503040c03020909030d05040f11010c02010906080c09030109150e0312040209 82
    0x2c072402840362a035010400c45144034400d00c42041d10491020005180114038401c10001030b0500d0107101070020120302e80c1550000701413101c1251b08c0d204e003541c0003440700f604d030294214030f9500c02d20043c107a0051240a03011840e4084aa944145104210031100c4c00a00c00d000104240085440b1602c25001031500e000d0510482d010484101c042541c101d040c0d40c040b11200c0001c10909544080611481e44c5c402a4035001d1801c00d010314001c07a8480c44000c20050800150740c00003601103004a0445043c61240f0040f195251f032a45803183c9005014011441913801c4018202d030326908c10000c681c81282d1025114058030700d0355007440200c810180401c0c07001d001c240b00d4080c014100c0d1140e9481540113456009030303001c0d9414800200341710282628100000d03d06d2107000360340c2041d0000c2c00c0b1a1b0f18506401d561341c1e90f803588a4980145c070300203a4103500f010030345400d03c020011b101d00888aa054200000c0d070703c02c1c0b07002e40e61740706601c400b044994030903000a000d40340585000303910a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 58262278 1250 58261028 58261043
    0x1a01090e1e1008011d1b0406030b07020d091509090c03060b07030207093605010b0d0c031e0b070809070f030b0a0c0503060609060f0d0c090e0705030709060c 69
    0x107066584001040908803891115200e0001d070400403803609000f40c4d200c601901c1a0901c001140c040055198960004004401c01070311008444c56280c2e81d024a0043d5004000c00120b8100140025250a000180d42d000110b415201141c0400e4040389042c2110082d1140c280b060710b055072010140a030400901c0c2419a1b455001a400c000700004150f0940300f0340c05444d401703080c400403a0807107030b0300303030400c03ca0803011070021131a140f1400c1c03003232542c2c0070311150403442c0f41592410074094208101042c0c9c00490920349802000b820000c0c00051764450288900031900054114600b14524240540426028400b0030748090090705a550048400029603030119110480016070a007698800c4036806840c41c100071140c411403250320808502c034500305185003491000507600780201c558842c0318240010b100d441035403443c41291120a4180802d10070031000100142c191410f45c0b0490780814002d100061001d44100c00703c910074440c03515508040c505000084074880c680e40c408036101b8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 58263528 1250 58262278 58262311
    0x7090e0a020909010b0c06010e0c030127020a090302090c0c0c060703090f0e0a0b01021606110a020901080105060a080a03021b061303060506130911061303060c020c041a01090e 77
    0x140c983e009100d019010000005584000c5e0f0304050346007030016480280d0f050514024000c218440808aa0440d043c0961700701c6401e582540c3d02a0301c8403050101e0500302d100143c6160f001c2c1d04400d0000c1102c0c001c9600d034020b030365007141600c0c0310f10407480700d041183c101c1490a552450000302a00d4903d0207803a081d51000c0d04c41200f50368190f003a400c41307403250000400304284000c00c0d004803032004400b032002e441d852804010140b5152031a0280d03105201d44544003513104002042003100283c1c00a003004007a5940e030807001d000b02016160a4001c0b81c41450210f08003800080340c000680d032580c000d2112180d44d0108081000382c41d608581c0c407110400104550041142039080074500a0f00c000416060400070000103a4016140d010054200a6108081440503c1c80c2011410984003550f4034910400d03240c900001c190801045030380b900d8480c80e40b203030380050145008641920100801403000d07a031160000aa46105da00144540005009a070301881c2c082d034100d8101c80440420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 58264778 1250 58263528 58263547
    0xb040203090d1b0602160b09010c0c02150903060a0f050106081306050601030207050303070e0a0f0501020a080d0204030c030b060a050609030309010c0212011a03070905041203050910050423030307090e0a02 90
    0x41c3da00c450582c40241b00011000b030144801c2640c40d540110040000300620f030307141d040140800402400191240c80b106070501865003003c42111180d01d4001d00b03980321481c00800710401040705560041e181494040081030a40c01441c92030702462072800c41ca00301c96180d07660340c4054000240090f04054003407086e400000d00c200041c41c0200060340350400004880e0301840130501542c0c1c070508101017081c40400ca50b036000310702d681405400c082d5035a0341c1c4d280741c5d07410700283c0300b40e510003048408040707030010a00c40754035451030180004417281b40300a035490040201d24050100c6650380364004100105407580940d40c0822040e00c0075018503c00c00754032468508440c9030540d88400c0c11502414100d140c0390a01c4581c0140142c04030400190815441c0c070380500702c0794443c442c141a5544003084402100304a030b4006601e90a00030322035490140b134860565151694212a40024030568944d03204020003620700c148615541c036009a80f81c10401c004501020b04624005507017001000c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 58266028 1250 58264778 58264781
    0xf120103080705061005011b020a0509010806070f02030406050414130e010b0102010f020304030207030219080a080a030c0e01021207030905062a070806040b06190e06040b040203090d1b06 82
    0x31406200c003541c4401041c100703a81048401418109a601249411300031a038100103050001d040c0303503e03d0314500ca0309101050070040139801681d0700103100350000030030003000070ba41441384440d580c603400100000c0000f80c0c2c1c0d078091405840c0100d4424031060144540c80110320981c07400007020644800380501507001203031491818408165141c5204001e156024002c0c0b03202c80c5840d407811865458035880c025121900c03804000d11540c00540d91404c11b107075884100014160b410152081c040051038000826031241c1c120030701007814030a402c0c2ea900c0c007520140444400c10b17009494068400382c0c2480c0e682d40003e40c21014420441d10214041e16140040d00ca070340d0b0444400821a03141e008120f040c07180071540b5a840c0d600c8414144060400801e0080d0050b900030003c01709074442d0710010301e02c440c810341c68010b441c098040024102c9040142c66020714030541d001c1051a072154244401c2e480211580b40070380c8e0001601002e190b1050300004008040240401c20102450741d0701d40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 58267278 1250 58266028 58266031
    0x1200c13020d0501060f03060e060d02040c0507050f06010914060901090c090801020c0303010f0f1a030601120504050604110312030c0d02070c08030702150a0e010f26010e070906050f0f12 82
    0x800061121200486c0715800d44a144090812424500030500e4410f0000d4440b6440c010020300641e1a080b101e4061802041946d82d1540c2c801c058807120559250821743d00d410911400003c1403d00780371502000d16424002d010784401350500502da800c00341d00078083c1055050001c100301e00408001511002032020b048000c80040145682c0d51400036002081905d5030003d403880407010301c0802190340a0100304046501010306244c90390b484c071005807602d0310080e4000c10f80ca8149030800c0304002001c6501403003580b040740206085e0b04403405045e03a072072a8440060f521032081010501409207000a00070640c1001d070054900345460382c4680705103000398029038107540086044411454002e2550254a107007503c400d0504860002c000d0528400840040c18031101c480d4000d41c503481a00150240d407078001c0804025020132240c01040c00c000d00c1505d04819542e030110b5032851041e01a0021170b403607541c2d0f05040200c080c0c180d110940c88502178280d006d00c104010906004044c8140313 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 58268528 1250 58267278 58267289
    0xa02042007060518030306330f0d0e12040603110702030a0b0f060f0a09091b06021b0906090c03103f05030426060a0b01200c13020d0501 60
    0x10943c0c1c14403606400312100b12084e0740c110360700b0a0003000031030b4860400c1100000f90403807100b007100b001c003480034200300307002d41800611340000a16019036a480d0001400c00f804504010044076140f2111562100041218132124541c01c0004101882c031036007144502e0301c000e280f20b52405c0a2640064504007402c442107501c240f1180800402064803205168010b80a580d1480640d402600003911010a07001e0070794840c0d07560000c98203110a086510140144500030041d58545460f40699124208110300c10076900310a0324201740c0c1000341496010b648041c01620349611240c4000c0f43da508010701149440315002d5001818000c06042c0c00b01a40e01a0a00100400c2c903010214501c00c142040040c481c101c0c0707440700c1c00a00004100e0301150000802c4a80040074001d5000c01c04030002142852803044800703001e06540c41354043d5403424808d80300c0607900c0d03072405450082a1040300902d403c40d04200d442c1c0a00381042040c13071500000034880145004540c0c101101140c90a8120303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 58269778 1250 58268528 58268531
    0x1061706010815130b0702010902040c0e040c05070507090e1002070b1608040309050f0123030a05060a030f0b040602070204050412030f06050a1a130b03060f04050403020a0204200706 80
    0x40002c96828408800010403000080e9058a003c410220289544c10f1004000006880c001861070f03200303510a1054540c000c2c01802607041e02c41005040f16454048684214642070070108014022422548895440000707042554904034003500142402c1c0c494000d5030260382c008c040b21003194401484a40c1c4a050400e0442c14500701070109960301218900c00d100c01c0c1c0d800d210110390000c2c01c2d0400c40b8000c80b45401c803c90420300480c0c410698880b2441040d210700c2501000020303070005148140c5c03503124100102c1e50b5a808106044260b484040d10740c0d030b03c0346c41107404a40342700c4c400b41e882801140050303d0460140e010804840d82290160b030b20a580d480d500064030341c980141c0260245907141070101d80d00306000074251400507c52156400c0512602241e40c01130801a51480030605030f0903603c0360f5441e0f1080c0c0c1c5070391084506038410561000040d20034a402d200781c90040d40c0680c010180500300b503003072200405240c0c001200c100382400100140a856000415800b40b141e40c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 58271028 1250 58269778 58269781
    0xf060509071a190c020d020409020f03030a02030c010506030a0f0b070513030f02040506030303010f0e190608071703040303051215030607030e0105060406050d170f03070f0f0207030c1701061706 85
    0x792100c10b180100e0500402510340300c80d5016039034880a843c05142c0450700002d5150b152b1001405c007402407444203405020104014138155004005800101d0b0204007d001c0f0b80d44038030406407a8020540001c050b12550380c1400c000c034100c00344850b802035060411901c2c00900c01e0144c20041400d81c800c60b8a1810307907014104500f058001e8981080c801c0e00250300751750401d00c0010b03400c10280228030071841c20b000001c81c5490b00c0007c03c2d000004100701041032584810106450300e680d8000c003202503200c2ca03c64007621030000100c0d81181d80642e1110304004002014920030391018085483d901e00c60010b01d0201d96082c805180505103648000030682961307030380f19007510030081c24540304034a0264100102e0b218031691880743c9034031010308144805011003004150050580045151310040208405607800c140c42c00d11010392521a003c000c48041c400b00ea5074505804014046040c07160304115950700300e940064a007030719400200f2160b0b241c0c410107070b02e110b40c00785640c4030350b1080b0b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 58272278 1250 58271028 58271047
    0x40c2706121a06090c070201030902040608070302090c07030509040b040f110d1103060604050d030504080109030c03080108191e0803150901051206070e18041b060302070f060509071a 80
    0x8280408031401003107242d03520f400000a0340c03140c030007000d00180c2d403000a041011a071295204400310760b8000c20410245448002440d951621400704a00559149000c01c7c60101034070140c1c8c2c00719503d541c070146400098024032024003012417407550019100c1300350001a8860740912101344da002c01520351222000c0d41c141c01a660700130703010f00701e081007007003400841e4568200f01e0701070783d00070b45e000d01031a040c1e0b142c00c6805209507448400c003540f07840c511100b0194411181c0d80068020740e00d40c1c49030b0743ca07010019100d0101c9415403070310440614404001502060b0900f60280c001d40001c0c0340410541c5842e4183e510455107440441c1c01c0044660b41e42c900010b005000d0302c0140c405e0a03001c00281d1600f541d550b0041c103002e050103803410041b400f651714400c58014015490324120003e00300392412a07400c001141c209402070f03500b010007044541c400d10984500c0ca42020200c3d0003a08107488140c02001c2c041d10912150142c07190120b818890000c400100e074002c1546a50782c5c43d102c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 58273384 1106 58272278 58272293
    0x906042114030306010215070e0907120606091d04050a060506040b0d03030f06170a0318150c05010b03070b0910090e090c01030e06040c270612 63
    0x14003407018000c40200256004039020f030212007150000100b501001c01040301c2c0000000d40341c844801c61440c2949109804c401c05050845d0000c0081c010f44098a0315a0001004282840410841100703045502000703040c540f42c01d840d10781400d80d1050b4070340503031702d40203404541c645020400d141c0e695032100c0130480000704010380110092401070050301107a161402450318005001411041e4a6442c3c0b040f07081704000f4090010141d50243c80207030001600c0320001d5094180803600c0b001c044031a60400d40507454014809034070749441802d5512010303d1705e000760884e501c1002030703000c2c00c81a074040d050201c2d50301403804500c5904441180950303000c0c41080c28484e05010840c1d0010a030500c01030f800b0ba03420311240111070342a59640c0410f0700c1c0108200607c0e50104181d10356141c03100000280528101b0520710a59132180940b111500103c001d24550705c2d404041150302d = true := by decide +kernel

theorem cover : BRFrame.Cov 58093528 58273384 := by
  have h0 := BRFrame.cov_init 58093528
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58093528 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 58093528 ≤ n) (h2 : n < 58273384) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
