-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2370
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:30:30.288262+00:00
-- url     : https://prove2.me/submissions/626f866d-92ce-45c7-8b2a-7e77a41f2c0c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 426079136 ≤ n < 426258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 426080386 1250 426079136 426079139
    0x4031509050c09010609030609051006030305121609030f0c1502010608160807060f02010e0102070b01180e0309010c0203030f04080a02090c0f0906090d0210020610090504110603061306 81
    0x69008104800040d5001c0c01294210341940c5800b00450381211282c0d40c2c2d09070030600310f441d1301000302a0701e00120344912540200006210090007082c00650194440a4075442da500314440706483c0208902c1705109103151158900342c01508840540307030014162040d640551402607074080c1a90030000c0d0203900740a44405442e415040903090383c010409644001654bc0341c4206a00c1e01800b07078030b0180d00118403e10a5505c9808003030040c1500740f001042e0b00c901c5041c1c281c00c980c020242642c9290888005000c401a1546500410302c1329120030450700c2e4400707011540740d00135124801d041040a80380e0809640d41041507580041c65101400d59456a038280c4603034900462030304074050b800040000380322034100f8041da2a1140e589001c1890240c101c07041003c580d2200e02600c1e4482d02b0744500101684590301d820b05a07c0260f001040b80d07091100030000c0d60300e2580d0080a94a0400041000107031840a041004103015600951641c64047c001130003101c203540c060546a1034141c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 426081636 1250 426080386 426080423
    0x30309040f0b0a05030a022b08030a0606200a1403070b0a0501090c02190303090f0605070906031802010c1203061203030222030308130203120406050d1a1509060403 72
    0x1040424010889908036960354841c181741d140d0400ea40041c0d40410000d02c50100035540404080b1205c42d207400000418030030b41d5030407495070425106200c02a540d4101804000d400417141c440c080d0b50010740d120441c1d8449141d0f59140c508000003000d91140543d84130002208000ba42c10440e80410501c0c0c242c645030744424010502441a140290b0900c214070110a00119440009001c040b0f500b080c1c00d0195103081d009800c8443c421a450312030b013641c0b0700115030b0900c58135018681682e5481840c0f440d241d00142500e0070301c4083c001c1011044211401070707030010070a0380700380d611034504421245e0800003a401001c05500520340300880b40d4240c2c00700b6070b0641c020440d491001007640d118400c4105040c041548602000740454407810100f400302501020924070107200404507400e5600d02c1542c1c28030341d005035103c000860702c0403801003180c040600070141e0f101809202c020003c0c1d003031070000d40d100030610019200399000107046020f81e2105400c6a0142d41c00041030b0200010585 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 426082886 1250 426081636 426081641
    0x80d0c08130305030c21030103110a0e0703020d1b0215060f0319060f0510062139020606011809050f04060b040506060d230106021608060c041202030309040f 69
    0x1299039170280594601c00740075591500001e0840703200c0c0003c3c2c03415a82035035104142d50a041c4102c2c4c0d84401d010030000b034540901200d0501c1203519aa01580307900f05103000009460101700d441c1d13445d40140c80f14070011640015003018400844480400f04d0b201d880210342d001e1003200314550103001da203a01e4540c043e07510000192052150108003c6039003003030461021540140c400c8964601031100801041d44509466040c103425104d9458682c00010220001c6400720003004040324140001004d580c08100c461010783c01024602d1420624840c000a440384001030415060054041900341c081d44e21411010142552410030415030400c907100c1070b1f65000496080b50a6414409582201c0c103207405454010701021300140d04000361f003121000507141d0140c61040c41011800100a06d03520031400741e0007440306801821441300c0160f181000940103401c2101e45030300180502c00d1851502040310100d4440f0303651100c10106600c0001d0441c42280142d07580030342070500c8801242d8165 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 426084136 1250 426082886 426082897
    0xa030b0103050f06061008040213060e1009051306090f05010509100c05090a05090c12100302030616020714011e0f09050a030c0302060702040e060403050304060c0801080d0c0813030503 81
    0x16403c40e1034005021441e10359548003210619042140585407800950150600076001440100904a600400744105044559640c003100302c034108032041c07010b0842c0c40c4200d1300190981140500140c40e00381c2060414250b940001028a503031140741c981403007540200e10303200b154043c009104c9800c069aa85565800000800070941e203410005041c0c0350049086400b030b0507018004c210810f1504081100c844e000074030700c1120807001c02ca502058402c0c0c00807030b0b110f50742d0188071800c1c00d819801032502d0100010543c1c410300101a418529003500082caa404541013114009903040404004030b910110944c04481010f03582c03041d0506064101c1c0d206100c10140342d444c044020f507540e0410004020620025080143e0300a0a0000d1b05080000303110290000d840441c8036400c26540f60702c0c3c0700003180c0c268001800032050104000d1540150312484806141074030b400c0d41440e84094580c0c42810640c014000c0b4a017461040000703030700c00d0322081540b041d800f022260392800c00603140d9125 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 426085386 1250 426084136 426084143
    0x2030a051608092d09042303190305101226092d0121020c0c09010303020a15020a05040b1b01050118050a0509030403260414030f150a0209010e0a030b0103 68
    0x590b210f59220781817248103280310380e4101c000c074068050364031034241464080109101c0c1c079000170041d003280038981e6408c400500015640004441c9415820f0000c3c000c055001034080c001080c2032302c00422120141d22111030189040d415040c3c03c0041e51070858815850000c4c1c02c0a6910010303400d813240c40703641011448018081c071002040420046400c070319400c200d83c0c40340015811003080d058081c0c0c040c00880c03100c4000c46004c0a003201c0000d40d00c131026401140140e0100c243e0a00b040f231400041486201e60000650502c0c41c80b2030003038618047c50141000c20fa40214802e40c04443c40f0312003c040c035614030003c102c156100e480026010043c44041c203421810000455210b4181c0d10a01c3d2041c840d4901841c01e10341581d4034a2081c20b50300d0700311640c050002c0703030070400361002c2c00c028401424100c0d0319078000120002070504103101c07084c40341880e810803610600c610f203141c602075501c908040070040e501c0c8602e03001070b10740000060700e058200003025404001c01c880b4000232070503a0300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 426086636 1250 426085386 426085459
    0x90f020306090609040528080d0605010f030c090b0919030b0702010c0207080c0910090606021b0103150504020c0a08040305030909101a071e0c0906050102030a05160809 74
    0x111881841071450058500603c2d542c09580840c00030107c101e0310b4400c1c59a2958086130b904a60b031205001604071810105520303544950800032980c2102c1c1041c4000b11604003030005401d012005091580c007449081c0010800003000f50b540c1d0340350051403052a4940358000307080345d16402d100c46682f000305e1b41e0318055840c0000703400c642400043c08030212541d01e4001c003902601001800a0030102401e480c512496440303000c58000340c503024540141030b0710f070b008016003004103507180723003241c0101c00700c605061400819018101c5004007002c290780040d034000d690344103212521441c1c0052080e0180c14007a002c03c000c400c114004c00100f8041d1011945004152105100d070361072003170684500480300710305000c0c01102009903000f80861500030500b80780001c0001c3d210102145c4e07251011a50f81030403100604c403800b16481120f026010038402541410283c40010301030780715440003007400c1c40d10a80e002003040b80400c12100480d030003074281c0350308000d9a16002148030f400400e0010800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 426087886 1250 426086636 426086641
    0x30314160501061a094c09050a0605160c09090c03060f0e03040e070c0f030224160302070f02180f0a0b010c030e0a0b16110d05031b0106090f02030609 66
    0x42c56800c1d176a0740d6000500748440100c0800c0c0c15800f681e00030040c040c80014031034401160708414034032981051101c065410b0f046820700001001441650021481601c00c0c11042c00250f174840295400000700d0b4035000e9041c1d10b00d0510003503d4038140d2001c407560f03003014156410005000f4010085910a950038000350844c803008100f0303100c815642da00c056005220803c15041100300850704002c85080c1040540e145403600249109407803401d41c0035134001845848081d0507141041d0420014480c241e802c0d09180c48848080c030754038050b460400d032f00820042c06006c880015000720940c0101f0601c1d49203100980e140300300000b00c030f90f070603102c5c00ca0b00012401c000d030380903005102c00e050392a0302c10700040b6601507400300e400c0050140c1003c440b0340003192040194005107010034001c0c5070180709610b1403806032680c03991021400d004071901400c000020b0000002e55a1501c3c2c50601108400f030079640c07442c01410746c1ea011580300e608012203521505440d030300450043e102070b61201c1495 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 426089136 1250 426087886 426087929
    0x1b0302220b0f1f05042c0f0106081308210601020d0912150f0e030c01060807050a03032006010617150f1011031c0b030604080403031416050106 63
    0x2803681e6002d1900580c03c0c6801e0241c1244041d078082003004541000ca003404d03150a000c0003810341000029503091200c1e00c15082281c0f00541071540301e65080100860f960500c030009002ca40040c242e01e40f400f205c1d4408108105c0d1100a480c180400e50201c402c8044004000407140001902d199015009503002d000c02284204151000e69012050100c0001442d9503a40b06602ca0300304582d80700703503a61042e2490382001d030145100d2020002c0003942c858088240c1e81d400c44406500c00c04141d0300c00c103030803c00c41d140c0f28420000c0303030b400d814110190108054050344c52060040100c206010350000400c040350401000e4842d03000707003108142c0302d6030ba001c61810080c0c0081e14a0b6031084040c0c80c0c000a502e0007094081d0018417a113001c80a0340000c45a0500d0f54018591a0b00c2059000000c4102139401e0700c59549000000c5004004900300717a110012240b0440c0405410013101c000c24010b208280320403650003900101011010040a0520500030412030160401341444d000100b54103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 426090386 1250 426089136 426089149
    0x506010f06140919090e0705040b10120c090302030609060708150d021210060e1824041106070f120809070504050a111207080901090f1b0302220b 64
    0x2e256481d4889481d02c030504040000958074041165009140000003181c00c1000d40510301d0b240080000a00b415800c22007000305503501c11214a00400c403540481e0384d0a9400005c01c0401d0203506000a0411b00d214000c450342c14580d00040e406110743ca00b4041c0d64100080c0540c030030300d401c0e40c1c2c0300e43c00d4507560510002c0e003015074030407030341b01d0900456200589081400d85000d00b5081040f161046000061002911055030001445100603010049441c5107071f0140c06000d4202c1010b460382c84161401c0d0308035800e1036540e141701248001d00050030054841d90702c50100800038820341d292019841c00980d00803a40000300d440002c152400c0010f5130003080741d0390240695201070305140b428041400000d11004103031f120419122003801e86641141d500030b02c044014050401c19500d01550041c2c94541e01030070100c026807400591101013000108007550856004a50205508891017100000c0030560006944412901e4858004084e24080b4010441d0300450078441d4407401c9080081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 426091636 1250 426090386 426090407
    0x30a03091d04031421010803040302010201060803040e010e0c09130f0e0606090604020703031e0207031107061d030a120806010e060304080f0c03040f0306050103170702030a021003180506010f06 85
    0x421000c1c50204404c0c0240f201a1542c140c500000c10385040040010311000c40003a4800002034000082c18820341d42c1c28041d8030007603c03030300004610741403030491040c0d407152051003100a00c80206002c00c02d44c00f0381200b01c5a41d09401000480041e10701e002c107200901301d004c203100240380707042c030540808180461010b120703010080440c20300350b4134101800080c3d80a550110304059a038040031414510103101007036101000000142c9515051801500e51503845000016583c81001c02304403181d84101c0041d00c480c04802040220406200031a00d40300d1940e03401011156a0128042402d6120f40858400c0350240e0300c107540042c0e00020700031240301c15580a4401c10341000300901f903404940007070010350311360780489142640c3d0300600c00504940790421a4003d8032800100f05000c071800354030051400c0c031202d803841c3c03210550002381d0700d101c43c1e0002030041c12010740c80b180030750003680b189041802c0e60b51085c405900510700b4603200d00090007010405100c403400800c00611a4100a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 426092886 1250 426091636 426091643
    0x605010210051b0f190e013e0a0b0421050c0304150908010f1407030207030203070b060109121202010510080307032a0f05120903031204080403020604080c03011b020d0e040b030a03091d04 82
    0x1200985031080c03508400e01c1508c1203425072007181c0c1780300005a98900d03228403581c00381106019019000c1d05008070190b500081c10b040000900402c90b240d54003004079803c03100701c42c0c080b03002090102010345040c0601c1d40080401c1d480c120101419115940000102c00d141c410140c603103986a400c190100d005060b0050016481881786200080c450780125030408814102035940aa45c0d01385141c11012007031049034022800b01ca0440202e40900032690810031200e42c40c00300318203050050f0741d070303000b07140f009801c110000788011813880f20082865640814035a4141000d070740703418005204561080211303254400ca404050075006c41100b6180e044038014041c1d0b14010385003600100c04100640300391001c0004200c0040144e407401c00800040c150b1001810304001400201030841b502c0c0e401600d182c803165003216048aa0100b2843c00504660070301048494440001c60300400c90000004e03003603c2610070050626401c00000c502321a00300030444028943d05504404644003a10000d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 426094136 1250 426092886 426092957
    0x12070c1a0309071a0d11040305010501061107050d0210030207060b10020102180613030b0405011b09080d09030201022a1509190f03200a03060605010210051b0f190e01 73
    0x2c4105020750000c4646d1010302555504150310781d100d05085801c2a03000f800410544030f0248000c08d020301100c002070108607680302240c10a0340110712040b0001c407544040542c00103041c000c01080e41e0012441c0c0c107003d44501260006544043d0007540086011006490302c6012440a89808400c4548080001288540144c80e65840401c2010007801c115055500c0700c00711003100c408040c039500c0503605695030500f041d140c10706d06424003035141003100030000d00c1380003840541d0b00024240070459000f03008001e4180c080700a086200c0c14603255640c026075802800c5026030004014103040d8008030341c1010380070146006120344000700e10030010b80c030008038002c01c04110804441c80044126484c480500c3c0710020000e250180160800c4620342c0c0d46032010f0200d541c0c1000520707095007086404001900385440d080980785072120740b641d5030f0f1500190b204007819003401642c1000511040521280140c000040c200c20066100c00e0300142e10740900760003101c41c1c0851041c0150501f00784 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 426095386 1250 426094136 426094147
    0x1022107060213090903080a050601080601210608120d0b010809100c0c150c03050a020703080402040e1606051c110a0f0e0a0b09040e0303040512070c1a0309071a 71
    0x800c0003a42290303e4034100396200781400143c401c00383c00741c1540188260b907080c0580c6818440441102c0c0c000c0d117014108100d1004101031a42c2000e2110440401902c9030811210f885a1f0340d03000d480d02c2e820070540d902920034840350f00a0010060980e6410410003072103c50104001100c1c070110803101d0340b409510251490240708416030080d04240c00d5403500c4050701e11580c0b96000941400303030800d40480d41d03d641e00a0026807501c00c0d01e40105400d202549081e03c01e440007400c445004d48080d1040ba9244142c0011200410182d0b40341803140160600703096071418003604d203400c40010004000d48001c01d0f0200300e401032040c41c1d441c218a08545042107100d01040b5a8980c07520301c11402e00030700e808112200d41d25441038100400c01968440d40c2c82d00050180420f40300c00c50180849a402070040c000040c03c040380f002601c10410700041e46440031801d00405030000c5d58008a0059031041070079101400400007180308003150011210700e1a60b80e07a141e08100840b4480641d4800103122 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 426096636 1250 426095386 426095393
    0x10c0807050f1201081605030d0c02040b0a08011814030901081602010f1104030c2312150f0106110601080c01030e0106090f091709010903060b19031101022107 70
    0x1d040110705000c0b01a0030480202c6400b0303101d40003a0065102503208000e0440340078034004502024100a0300035290b2810a0b10020700180580d00d0020b00ca151a44203011050701c2d400d201c0e00c001e28254000307000d03912110014085940c0079034070a0f10384081245030041003040000460301c9004047e91440800d0740ca68015001601001031000115501c1d00d44058030200c05020721220707519907000641c2c4d21451407601d084590090341c00813001d005845282d9810b641c040f41d140016000950302c200e03108418829450812096084d00c810400e069400d105c2c2d02c0d100c05003114103840c1a078503842001400c10b80701076502c88091280072200c2d4400d6144910725442900711034110102880049010707074485040c2d00545825041e00c4d045d07566030f0b13013600d410310843c254079013005025a40194501040380340020803081ca0390101402443e121a034142e8240c50b000c10140c10340c1b00100050301e181c1d450385080c0c004444050b069500500c900446a805017495a54240796084104001440d1040075134 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 426097886 1250 426096636 426096647
    0x10606080c16140304060f020106030206040314070906030606030201080f040c0510050f0705010f0b1207030204020a140a0306090f0e1b01030e0d02060603070909050c090a0b0a081b03010c0807 84
    0x224600c0c14151030b001c15001441c3c0500708a07080101c00c0140da161800e00f0001412000e2142030030b411681400d00400140e1a000220780030703a0740003106102043c00030301480303240c81d20302d81c07103002c00b07500d00140002803081c298409020340e0310176030303814030755443e00e28038002c2c481e60545000d0319118007948100024501038960400d2605d0a0a0090038241070710030000c2550007030041641c059445213079a407040c01d0707544155540341d94200d41800c0c1900f40c18a52070303034841c01404000e0140381c0c0002c1c401d00c0303280105488052050f0840300030359107080480c0b0060141c02c2a02c11021218180000c165441025000d80d0300c3c100d01c908001c140340703c140c83c0d0304029158140032940c1031580d02c0000100040080c00000d11040d0180c00070a450f007070800600d45040d05c540d110714400d030f16012040002880214031000c80e12412141003000f51921102d04000301038200f41a50302c40001d9a0024810201180c0a10b00c1c6502944aa041ba111102418265955522254002005a07001491050040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 426099136 1250 426097886 426097897
    0x605030105062704060b1c14030f03040308060105090a06030b030601052d120601061706010c1e03140301080d11190b0a09050a08070605180c060901020f0601090b0909010606080c 78
    0x50343c1c0468228800c1002c47e21060383e500c026000b110a107100003043c003d10702004038911060b034004500d0914583d60041c503034040548001c1c200400d00b8080b44582e0300c20810f8559a510040c100e551072641d0f40e501500030f0082c0010382e030080c019100002480d2402e80f10309080710f11403100320700c81d01800b0500305035048140a60036078022901034004e00f0103001000301501070401c940b601c0504401422040000c44001065141044402580b0300005551000c0940c2d5600c88100307441c0804e40c6070306d42a5610707074481e0000c1e5005240440000b41c00c02000580207400585c64407070085088a01c0035141d15440d00302c2e03e83c080714442d05000c2c0b0014182c4080b907640840c1c295000030320701803555135542c00e10601c02c0046c3c1c1c4540d0081400d80511096102d001c0c0c22000c3d846610b15080b460841c0c090315814108000c1c2e01c1880003190218040c2d0084c0b00c240c002e01011010b031000756840360050802811074803480b50040541500050460005214010545160392100044d40d40c2d12100580e199022 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 426100386 1250 426099136 426099143
    0xa05040302120f130f05030f01020a0504150e0301090804090b0303070b0c071703040f0201110d080712380603010b03060f04020f07050606030c0a050a0506070516090605030105062704 80
    0x800490300c100700440541406850b482030105c1c40c552606c0109843c2c8400300c4091405a481041074951007500002181c0032582c03514051610600006003d071600d080300321070290154242082c15003040111030040007940c460340810800303800160141956401280c0f002000a9600c1c00446d40e01a03000010b045103521440f4084280f404442c00041d954000303507802c41c0ca0354120500d1804560300507030036504200300d2900400b2481c0008000504c1607402411450610100c4515130420040c0c3d83c00026011414281085921101840700c00c01c034410f44044030503c5074100c644480303e207448400c8a048541d2070840c1380c11360302c501007001900e00703030341e0390b0f440e4007990806c0740080e01400227002d440401c2c002e00c090304052034804103050912030100d040911405c4005401c0c40395075640c0e1216000c0c0c1c0c109844542d15401545002c0d440c09203080b091000313841c202100018007403031681010040c1c0307909a00078840c640b0303100c0500c012101100300100b07918000d043ca00d61210300c9090b4040d4040d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 426101636 1250 426100386 426100417
    0x3091e0902131a09181905150d0c050901050315010e0c190c020922151413150c08060f041e0e010e060c0306191805040b0a0504030212 59
    0x160380c80c0584104642c000d07883c0d142e8a004c034090700b85180401c9203503584d800a001030384844c9088810070f80325416007428100095074900100e620405050207081c0b5a0101608900e240099814144143c1e0f61510600e40300b4140301c80046204e0401090b6902151002d030010341d050303401c00c2c220400c921001010003406400138441e22030b20410407140b10850040645428040603c10b0050046200005050003c11504c0140d80c030700e00103021a1019286400c0b0400310410314080b24078601800002403d040f610340d261040c020104450b50000015510074802c220352050b4a44440040d03a803410308803000b203021000043d074541014400c0e25503519006000040c00760b801105070b0314100040c1182c2c02c11658410458000c03107802d2007042d02480b075280080c1039a2805c410883c01c2c074400204818007420388580f012843d110b28004031800b509441d10b01001c818490015103009000c2101c0544802381100302150540c5220301c01d0034045c0d0b0b01640a4a168210402d0b404800e9008031841c190b0b80d02c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 426102886 1250 426101636 426101639
    0x9012a230705120d08070e030d05042603040915080f06090f0c1807180b04060f0203090f0f0303042c070c0b06060a02030c07031b1d1306020412060903091e090213 71
    0x103500340109d40145185441d0f4036111801c2c081d8140c49800d480200c024032100c450340d88140c0e0700000003030b6000c0310003a0802040c001e200c203411100d83d941c140c0c4112024468580b01810068001c01d51130300c540400c01c119150841401da06960740c1c1c2540403095001b0742030750f1021141a543c01d40701e5034021340900b401c0319440905c8005109035055030380500034035a00420180b00190b400401e60b0b6030204188020750904030386c04d000414010800003440d00c14400c0080c0c020b9561810700580300240078408040c1d10741d22404030b088141a5041d601041c08155400c00140380c54010041080742d160406420303d21665500b09100c4c440d0300c560840401c3d031000703100740f6088032000c228107009103110f001e00010b003c40c6a10424803c200ca81c10200e0341403a014074201c22080d41c01c04040d4000884850090140141d045c038400900c255040b03240c3c25210f044030070050119036040440468400c0c2d83d615070a590710f201004001c181e00130449030400c1080b000b00410080c0b80c01070301101900d40c05814a05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 426104136 1250 426102886 426102889
    0x14130b06181f080a0c120c03050706080109061a09090405100c2607020d03090204150b0310080f0316050705030f15060609012a230705120d08070e 64
    0x40d4400c036001d030400034441d101c440814404001502c01005150014500d5101d20380e160000c80c00c190103070b2403440c2a007183d44400d100f0b41840b010001d54004041d1000e141d1074180041c00502e00740280080c0c14200b28000030444c0c7e4000f03280036988118010300b420034490741c0c1040922a00a030050301d02d03100e00da8000d1001003842c429211410500d4a801034040715001c02038400e442d1150b400043c1c0c01c240f00400031415000704984000d40018500001c078060584009030042480022500c014403004002061340340d42103000f1409a101500c1003072007da500e5404550354040186120b0f10303508188584c0c0c40b440e52000c004202c0c144070304140c6807240c2e210008070f4601551502c04266540c440705840c901c61a424008580014051b602c1915145900b000a89001048401d14414501513511401d04000030641e8102070380d8085c1c000005008040d04072400d042d00000351035818012880005801e1030940c04144030741c0c900801800c1484040305064840c01002841c103002e111529500d00703010b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 426105386 1250 426104136 426104179
    0x70c050913080c0109020108220f08120106120f0b030c010c0204020409021204020108070c0f0311030d1a03100501031a0402030a0b07021b091e0a0609020c0d020114130b06 75
    0x10300c3c1d18240001100d00d9140001400114080d2550451864070b00c0c000b03612880b5080c080780243d0300440e880548032130601d0543c2c400e00c00c0d4400d41e2000c1e04400004506290700442d01a0122002202400380242d98002c2e41e00711074002c515282c0c10341c49261800003d5018003021602e050004200604059441e03406c141030b82c2c00051480515940c0da000c01007190f03003103d001508a40d0b0b501d050b40392480160b0795003c07a100c00c1032000d020300c00c518181c00c180030b0080003101d0415001070414001d03844d0301050200f207400c584d000c5501c40c0c020482d4100c201000d07071150030b0407a60403100d1000001d60f038000c00401d010b8098001d9804d4000c582c425008101010401400f45ca555401811403424101011039501c01c5103991900c1685440705002102c600c1e40e115580b029095004c04100d0f842e04d00c5c00e500241483c1e400040014004903442d114204042008982134846070024413040803400200384030000100c80b9051800a0025900003061018401551248021f04600b0b010f00000d050110f8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 426106636 1250 426105386 426105397
    0x11a130b03121308030f0304020f0609030d020703060f0b0102030d09140303040c150c050312060f031005040c0e0105011d0301060506071202070501020c01020a140a0b09071703070c05091308 83
    0x41411002503200f02140803001e207140284249000740d420900441c0d0000744511029201070300c5022410800c035059075400d011178400c000b0040c01c4030340d9440052006515682c03144070581d00103260002800e03140c1e030140240616404c0590282d460315143c0d0841c17400038601c2540039510360b01032144101d0690001c00c0118081d60041030102c4c8003500d004bc403038081c80003061501d0204503c1078480c0c00001d40000c10380da005241002405007075692003010614098a0034822a03061084000503c5200d803550b000c0da010300c0c000c13144640480c1e1203180d00e00d1910f20a00c01c00c1d000448040b04041c00c0d500950307400c00c2007100207002007909030b5268002071481c1c1107007900f62a081c000c075940d11005a01000350b02d005180070f002034190203521a00107522402450400340003040e1000c02028508010300403000c2031a803101000c2c100b810b198101c0f650300e40c56401041d100981c8003600030140301c40001a540d03401e038042d803241c4400b41000144502c0b09000b401244082400c6440b50001800c842e01403d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 426107886 1250 426106636 426106663
    0x9122102072907081b1b0307090510030b041b031101020f2b0309080703173403232d0703020c15011e0503011a130b03 52
    0x55042c028180091051210040306410700181614400003a40065030446070300203500c02c0e01d800159854183c0b002d200494402e407406690080000003c3d031200c100742c0040107500315001e045e02e41000c182183c03801d9462400b980d280400c10800071b00f2510031b1691045c0f040148217011058943d01192400080d081203407051002003410007a541e0411589000351011001410800c00032a020035904240c0042c901100b4001e8140c1040305000c0d400030b084059110548517a5140682070003044030102c0a40030000760440ba0200c0c20752028a501c440c40382614515416a0280c22001c3d440c84003030502240d01455210044400802d1041c8000c070000184001002110703e000f10068490800c9801188508a5913402c2228401c1c4a1200542e1251690034016624242103400601d413071110718240c08480c1074800041104030306018402101c2841c0840c0703402c103030f444c3e0b010142030346c28a0031203400b102d120841186d8603141c4041c0c3d20102e40701d1000c0000d0f043c0072000101e8101800c000d00e61 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 426109136 1250 426107886 426107893
    0x60901201330050a02042405040b06090a170105100b0931061e061706220204030501060501030e0a06200403063c020706061d0a11040609122102 63
    0x44c00350305050103100e62150803450004425090401070b4900d510380d0b801801d000b036550341d00106580d1a80400c071104000010092100d00c1c2c0e0700c40e48241c40100302d5501c04415400c000c04203040316001100c8030241c45100e0303651070400d01c1c07003000d000417060032800b2020803040d14034000501c40240031b602980e00f103089801140ea5418400c405d18410303180d4484000030a0203540030000070758008e10382041c000104015420507207441000600c00c80210705c90182414032940c103018021764560060080300e02c9030000740030203950352006401722400340c1c00321209a000301216030002410f0307512130344111040814100811110400030031325500650802c80e07103650b8900000d11088200590000001140714807079001601c50741c00c1910f00d0030071324010315407560007242c40c00400402d40c100f00302900c00001c84104503c0030102c3c540c041e40c01611420703809031400003050402c10200080301d003640c0d202e0711040203080ca040502072214568070010b5400d80401d003505079154a4201e1494200c0131b499004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 426110386 1250 426109136 426109153
    0x90a030605130308150102070504050a0605060c0304080c0a03080d0207030c200f030309010522030203030720010c0b1b1207180816050f030c0306090120133005 70
    0x21382a0207000e01030741d1070040781158022107a0ba0000e030750025214141e0b001700c0c0584070340350640301403c4690031442e44100c0c042a2059100d90010161044400b51000c595000b4a50004c0c007181c00140d0102074010300e0100070040c0c80082d02c2d002485450303c60701d850150b0300c030581c40320704c024140c01c1180c41540071040710382041c43c07400c03210b503440304041240a90310704401000003078082c0c4541c0542075401740034074240b50440c2402c024100001c5401605036540e0740390618017080c3c038150701425124140180c0700d80b00c0f0700c0d5106420009100340e1001440c41e064941e10f6024034901d0b002c03000c075280d10004104144804402c0d00580d40601441c0c1c13034400390b100a541500c00220b020350442d000301d50014000810310940004160304070340c4140c0b5103440548801d404242040480300f81550188148c20502242e01380c1503114803040d89119030000f01520714040850410b1041503608540129040c000388160203a8000602c0480c019030005200d001c90350003281994004d00e1001c0c1c80d140c001d002d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 426111636 1250 426110386 426110393
    0x13030c1a19050f0604090c0803030108070603060e150909100e063c060f0607110109080c0123071e150c230c011503020f24090a03060513 60
    0x3106065088140802d2000d4035000c41c00218000740202154840e42d11468070310148889900c02c0000b51401070143c0765070b0740e101e03109143e07964901c0c8a0900004e240c0600080c3c60049864614040c1032070400c1e1054141c402005c000785484050034000785402031200b44105c110981c4904581c46018030042c1000c0d00d0813400c940d50500090501045c040000c40c0c00703221020246d0a52140102080030580b0203440701004144c204010740f05040e0031100014007442072100b0300d20104811002641c60300103442c3c9948e4001c5e1034818107102680414507406000341c00c60013200d844031a40c110a50f04904001043c4c941c204414182441031415151040c9464180504400080d09174609250180941c1a08420081440780ca15003148105101d80040301091615002100c10f82c1800a000340001009000c000c2e003110510b200403449660f00340c00914503814965121956121500300b00c00d0240400702c008100b90740014162035000c1030b003050210003d9041e1141501038035082040e241c0c0302c02e0b2880d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 426112886 1250 426111636 426111661
    0x102270a14011209081b0115210b06190b0c0601050402030408070b330315010303020303070815100c031b0b01090c030e34080613030c1a 60
    0x3080900d480d48a050203440c5039800c04150385189200680000d241c52850500360317140d002c1c5000c450007040c40a05207500701d0805400808d80c08061688900d1541d665201d000f070001e0014038a140005880850b00c1c1c046080711000c03603809074014005d04800c182260754204107100301c0d0000c402d840400f09400705080010403989001d000190b90451031810f107030311000003500501a0090407940e40300b000491a00d100012801c450180c03a128241410420b11001941da0000a14034043e104500324003048407200e14405048a8154000c0d6195440302c0c4030454641200405001c00708100d8140c3d03800c00d8503050107034114049035070395003200700c80b49180c010700e85141c658070030b900c030f80c50500305c48040744074251a141190b041c4140000c2004d070300c00080d8094140300483d4040c038003030942a0940150008858154002401550194154001d08020301d03080d05014040840d4071490002d205e40860308e1a51640350300074240452182240e0b581d221104501c0d40581000d102100248a044250385 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 426114136 1250 426112886 426112889
    0x3060203100f081f2a02010b0f091503030c0d0206010f09020910031d0604050d0e03060702150601140a03090c090c1202070c030210030e0c01080103120c03020102270a 73
    0xb40e0001c881c0515207142103594030300d0540040c0c0003204005000140c4000c0c0e90001001c41d2100c401c800c00394110740c40c0c040300f21020308905000355080000000c507500d050b00e14450a4200103004440a8480003500d03c2c140b0281c0b07115540510003003240401403002040301409001017a401009550b0400002480200056000440440c014071130f4062030b80d5500d22136642c0800500c3c0000d030b91220491280c11000118040030114002e180170b0000307110000c80c10030348000c40c0d44c0fa100d2142e12050103041e683c02c000c849020040c0c000b125001c4200207a01319954201805142010f10880c1044904034a60311121b02000860390340e50602d0f0800612450b42c400520380d240d01009031078210342c4090f203c1800701a02403069a4002040c008008003500b988001c0c60300584010240009031101a008040031030005105100d802901382c0c00707612136400c46060f25400206049210458002a207000031241c004134150b54003801036502c10300d01a100d460301d03030b03208965a14000445805100e24403925 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 426115386 1250 426114136 426114149
    0xa11010903021807090510050306030606090f0703092108100911041707120807061505130f062102043e040305010903090302030d0c021c030c08040306020310 69
    0x400240c3d0700c441041c0154035420401c2501961075200440e64070040350026139001403000388154030a64006d01030f6108140a40859000341c40744c0d02040600b080440391140042c07040000148007038482e811006006200c2e00050031b603240c00800c2003412140e500040301c00107031408200310780d00e05110f502c1801003590701800c10204268140b002000e01c9540500d10302c07116031002d00340501104102000042500e60302c04a40c1003820310780f1010a5000b064162425420000f1001d4100002c103607500893b41c1c02042d1410300c501200710280a4120300150a480d5039496400090001c03000454503c070000d0508030f0000034184d0b20402044504010721000900205240c010305000d01e11040c0c042c00c0c000071843c0e400ea480703d142c150036034840c81c1c000509650a29002404050300035000d64140c9200300c0c03c3e182c0400c40582c08a402c104507910103944071514013003821284c0300900050101601134507010190505644440900fa4042c0e4001c4030350700c1d80001004510b8141c402d10030040c004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 426116636 1250 426115386 426115397
    0x708070810060c020f0a03050114070e100f0e0306040b010518010e01060507020a0f091505010f0801050405090c0307080309011e090612060504150504110901090902091c050a1101 78
    0x42552904034003032541d001d42c5080c44510560001550f076030b40d0010300b04841c018a41e500c01c503200d02d0514080c2c0701c0701c0545e1810000003008650024040c03c100340c0c2d150720280008841d00c101034000c8801668a04601c1c0602640360f1102c0c0c205d45050050303900c11030140c03180403903a5141109100d4901e20404000d17a818031410014000d00181c034003c175045440ca840c205845c3c101030300000c0c1c408141a403151245080141c1300058555194110365000d00105100401841e960001521000031303001e03950b03001130507180041c88a4505980040d4102564100322003d081c8214042403803c3c5007034000500641c40842d02d070005683c08040704080100000760120b00030310381c2c0005400f2450340d00500703043c0300458800c94503d1981c1e6008800400009009101c441504050602d1402590013060700032030410944241804d600380441d002c505042e0f4a9400003860412660002c0d002a22103540c0400704c0e580340300507100d400d01d40d0403407235010b80060800c1c1d031030710f01d0450440d28180035072605201 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 426117886 1250 426116636 426116641
    0xc070501170a0c0309140a031412060d0203011401030b06010905010c11130b041811040606050301030605060d02090c0307080106030213031b050919050f0f18072c06030a11060715021207080708 84
    0x20030ad914061740010043d98a800a022913100090140032140524000c45500380b00001c28400040381c5c15005001c03c0e00c1e00c503240394a490046502100e21100500100c409007042c0c10941040162074001c2900e1882c00143c440481000800b582c4076a260132450266035601a01400002d0f0310104103420110780c10440f540c035040018240740414800600080c1d5204000f890300d48540c8a02c500c83c582c0180075960616141200320101d1300251030510004182000120303200340a442201c030040d100446509585186681d07401942460b03c0e94045900410940018141c80312001e0354001c60000d0741c0741084103e80d03513904c0211075006014074490f0103443c0501c10210322082007907070000250989100184a0100303202d2034003005a110107100d030381c241200c1c3c608900381d81800101c0c0000001d202c03c9502c0d04820507a0f5801c2540001d0000200384402a071207151a400410310148103070261404021054905400c83c0c00051410007003200400070002d00c540c1c07000866507c5019800c2000250 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 426119136 1250 426117886 426117907
    0xd0e01020a021f0e0106030c0303170403080c0a050705060f011a030f190216110310050c0a18090e1509060f160c0b0405030c070501170a0c0309140a0314 67
    0x1c1d07014a5407214004500101e038482d8485940060440155104c024454266645401000b4407600d12050740001c0c1410b070100440c040c080f00d1180160303010781d6045056101c6440c0c00406611840e100ca05024040000b000010401c0c4141c41c4150501e0100347d4156140162000d40400414643c03007411104104101e103c0310341c1034800e07820640d0601812386071150108070030020f1190240d07448c1c204403040051380410401581c0f03001d07540300583c19a0035244004108105903030054450700c0b1006002d00c102c5031211711410421000007110928409566a61800601241e41040321481c0640000c0c034641400501c2602241d00092103000400d01403401d004400d0659002800710040d011050500789070b0b1501c9010341044140e0011081c0316203080070f24040d99a60303c200e0070200d2a00600000242d550301074070700140244c030044d2401280e90303140308801009240c290190820716959036456800700395916455502c0041c4600103120440ca0350902070040702d0198000e41d40746c1c10410000021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 426120386 1250 426119136 426119143
    0x236070e1216052413090504060f110f120603071502070602011505031c020c0402040608010807080303130305130b0a0807170106050702120a0b040c03060506010c080702240c030d0e01020a02 83
    0x914402004d015120002c001c0c0030001d5507030320350200050341d0501040c80148091548000801c2c00d40d0641000400e100d03c2e100107040c05520300801c0103200502100030907401311519180c0c425401410b681c42d90f62180c003c0c0110001000342c5000507441008140b081e2502485070029101d2035083d1200018a484006075454a041c035180c0e528604241c0c4c070b102d060303000f0845400703842d034010b1055486680f80c2200601d032110034441c0e0a00340c0308003a00020416008000c59015459031212031303854410300d480c256a554852216100300c80c0781000300040b2070611001802e50700c03105555405841c1880710340101580724900043c0c51050031503004000b0700790440c0858645a83c160303041d103155095a000c050501c12020740c06004100100200010804114403402c150780c815402003140341c80705401101c4078910400014440841000100058030b44500004040307203100700400e144000c03a111080468014000201260340003041e0180303480f8260241a5106007880001c5081c1610003400954 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 426121636 1250 426120386 426120439
    0x41508060f0607060609180201140306030c0114091e040c0806010203041a040b0f04150201140123150c010c140304030e0607060603050a0236070e121605 67
    0x8070b08000907a40003040815040007008003842e01c01040b0803400d01c42c2480103540003d4089000800140c5c0c0e19100614020540303000d41006070003013002c840980c1c01550f0b0405049044c5680f180f0a00890425a0300e05000c00d0009401242c0c14100103524801d002c180c50484c111136043c0403d01d0304000669a00002f5142102c407401c4420b00100840401c6078424412a001860b41030360024640c1600400031000b00100d130b614180c4c07940e0300012030b5002c03402ca502c640300795a104203070341c0c0c010400e04071a1000c0d801409002208441080c88103070014503500300c00d102000980102098202142000b0b01c654120f24155050001601e20f01558581081c400100002d05111040c40785240e1030300c41c10b0076200703d141e114a040066940300d05043c2d41e54032925604038400d0b05016080000e0302c1c0841810500c0300c0d10605440410f1400b40c03001303810040000c0c08a003c0007508040c2c140195203540d40e044a2449000140c505c55080d15103c00d40302000360019402814907951003081030902c0075104a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 426122886 1250 426121636 426121639
    0x9050c0d0b060c25350f030a052b1e0c0c15060b0c1501090e0a110301150e01090c26090c0424090b060d090602070209010308041508060f 60
    0x4842a00071428101c4100b0542000003040003840c4841050000110300000020300b888614464180345040f0b2955001d006c4010403064101b880034011f024003a0002d00700c440d500b68915020f080d000044400c040035092201ca00c4151178680c505480002031a8034004501e00302414825040c008034040e00030494108002e0140301411107510b1243c11079807010002e0903444008641da4a400c1d0640c955444800d100c03410050b1020000090310740b00d911800c80d040701e0400c060481e002080e1202144600d02c848042e4055407554880319101c100524088090601d6254040280d41094805021030310030005100a001070100c14030f0300c511420840c5803000c0c0c032004110456079105078100e8200704503014280d0b00b080c14400880c050b070f218541542d80400c0041401c822160303840c0d820071b095500d94004550000020050446001c955420506c1050b01940c2c02614007195540402d5005c4801d0f8003c0c0c541c258041824001d00110002442c0c1c0f242840c5842c204a040220011304403010684059 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 426124136 1250 426122886 426122923
    0x16030c0206070524060d0b19110f040305070812040b13080a030801030b06010c021509151b060a1103061c061a130207050c010507050709050c0d0b060c 66
    0x1a08550703a00c01140c00e140c2e0303c00c003039072102e03010300c480f20030740030910740a2062104040740000c0f010706000814818007034100500c1505502c1d0b400002c0030070362900014200b6540c848005c0103614103808010000c2c00d5103034050544e641d1860078503508044c0c1d030741c0000c0302ca50824650075175a0402c150948003030f030741c0d540d0b00d4960780ca0803007440d0345882d822a400070840c1c3c00348816030300030302da00544101d040342d01400c9001c004e070f6200401100c809810403c001d500944c2080416100d861042c06130261400280420a00429604100f080d98101000343c030400742004940310800c2e1014842c080d04042c01840038000940300902c181040d0000408260069600e440c080e0003410000303a80204968100d04200f0101040f030780c1a00c000c0c044926541d014402c049801c0701ca144140c42103c410a800a010b4501d001e1404011a00d65112100c290342601c1742c90341c0490480124480c80b4002c519410009688148901040003035a250070310300c40c0720f20310500883c00b160301c000c1a01c41c481003079031021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 426125386 1250 426124136 426124157
    0x6040809040c141e0d06121a040b2202030f030403030207061b020103051003021e0a17030702040b0d14030310050a0e040308040201050d1118030601032006070b0703090212031603 78
    0x1070080da005e10f5544060103800d100c00000c0132000745071074a07002402813055101100d659076542c2116030342610002d0040d03482c2c81c0010442c0d5141c08083c0c00840380c130700515103204059000a817400e43d49035803450781500001400c00c20035404002980c010320072410510200514540201c404030084c0030043d05040d2202c00007450b00c15074807151005036a0003041041004080c0c4c446102494103211000d0082110f00c00100700d40c2c20000b0a44005007401008514094075030342408064a001d150380ea800024060401c400100910b200108207811000255128500118405032410641e40954080d0000d42c00070311807414081d99031a8001d42506141c3c0a079103903880100c03100d11950306003409a9141c00c041440c10420303440108840440070540503030400c40c0400b00344c2c817540c0070310008110034140300ea030030100440a00c42c0058014020912420420541c54040352002c040750000006540c940c800c00c1185083c0e000c4c0070000c40d45a00035410109900c541c3c5c440400801e001a0600c0303c040b00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 426126636 1250 426125386 426125437
    0xd140c0a0f0504050a06051b06100302151608070507060c1208060102101505010206010f0806070c0f060c0816030606050d091103150f13080405060304050a0506040809040c14 76
    0x110f4008140180646105590700c280051450304140110520040f042c292440582400116103000e68600e01c000450700b0720751f03030800c03040007a44648901100002d0040358000040f000d191500a80a91541c41c2c0d0b8241c00d152107410b052a03038001c00e0034040c0141e0800b01145100d081c1250f2551141040011074842a005034a007514580528100c281090450040c1910004102086640a03001c0354070f1a40c80d444e02403203440311405014003a520040000320340c903110320348520b405402960048010400c3b511074805a0b921009140f0108080304248900b021070355000703850314192442c0411203d41403600045c0b07244151070030890705c80e80700d0a50400380894030340c400c0b105000c0102140c0c2e00c031100c00c00d0f8061540c412200f450a0782071800008000e21001c1100c40354203580409581d02e001d050004000c1d403604003400940d00f610400c00b074440080e0041148900807801050040d440c3d8010804100940307098120a40070054000780c0340f00c2c61100c030800d40b4107444441c01c040c141c0414108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 426127886 1250 426126636 426126647
    0xb01080d140910200f0f01020c0316022704120f09090b1203040312090506040609030602130801020703030e0c0307080a0209060105070b0703060603060905011811090a060201020d140c0a0f 82
    0xc480503807140304040b20b130400303c00090345a40100d000f41c1038540010303410340703150308038040c0301640c0880744c00400c4604520252001564980da10040800910201c0c503078020811301d1408030080c0c1200891007d1009020284001142440c1035282180754010341c980c00800881161240c0c0c0340d152b07156181c0203107594808030b0441c4c1c0c020f41c034070441ea11196242440c2200c00c5000804602044040c04041041d0a200e012030301501c0035a1074014a552440c1c2d40c0800a5010b000308200845421038041885a030038001440017900a980114080c51060051420101c01880240c4258811041040552004202d03803100580440300507140303668040058a40b0301c20078900529120a00c000c102c3c070260198414000e1740ea00e6071b400c01003141c807505000c0842d1002e014451920100c8090240034841c2500300c401c1e41809400070f582000d404030007080c56129582c0041000d40d4012900d840a8085841038144410a54840314058185001020020700c16020310724208054000c40754480360180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 426129136 1250 426127886 426127907
    0x5070b04050f0312060405060d02030a0b0c07060204060203030a1a131e0501080d0e060403030e1c060612060b04110a05160b0f0a050702070605041809020d0b01080d140910 75
    0x21800d0f00c0c0d903248141e640c200c000b0b1088840300c2c891072030032022541d503081208003449810340c09001020b00f0100743d03d840d000c90308010f0170703e48008410040c1c4000655280040c000600d16a001940c403070401d200000191050307220349801a025a100700320580ea07484200400c1c5041c084d0001602442d107021016880c18508200440c19050000019913440d0010701c2221000c1c0c0e642d41d001c440b0648004005003032081e4480603000407290031003440c0b0f910b80151604ca52510030080819036807000d40d584c0d0141d600d140d0103002a04c007400210340c00d01c05180a42c4440403c1150108044010b40320f05104901130b680031041000404214500d541c0d0454148900c41d80d0064070101d550b00e0700d11000c0e04904030489103040514141800b10340c2007030001074547c064640b15211181001c3c1001042425094050000010301d51500d4800c005600c031308003e640308a024140e00325080d030514400d0707403070303c542403a2040410041140e0384001d0200481502e18070300048610408152400d1411034405240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 426130386 1250 426129136 426129163
    0xa050402160f12020706020d0e0909030c010f0617031e0f0d06081c0201090c03080310090e060601111207030513180e01180f021201110d060504180305070b0405 70
    0x78281c014050089208001c48080156130132a4191602c0d00b004a883d00c8024105802082082c0110700702303483c0081c00c06600000d440200d030b041561030b909507801c0d901c4400d41707021459507480040c489001020088000d2212000046140800110141e005c45426070840718545c403002c00c3c012203a0300040d00700c0d00d02e07000c003500900a068554451329125803003200814541d5800c100500503990042c003600c2c03045a0040325600d46c0d545542c40b800301c00d50004001200c0b000d040c00300810108a81d202e21403050301400d00826a0f8a0440005410303034100d240b09007440da0208814042202d9900100d0300c02c150b0600e80325494200c0c02c00b140d00004401d800c40c541448480c2c00801a00066500400c1e40c0301c1041d009014810000e20f0f01c036001a2498005400384a0101d80746d0090308010b096059806c402c100002440380e801d8100340065000906642400c9440300c00402036440c00b8081e0b5121203101ca4114114080a9034020b40707a0310602800914820b520303c0020140882400700c219102c1c034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 426131636 1250 426130386 426130403
    0xb030610140a11010b0a060206310809090a0e030316021c02071505040e150301090804180f0b0f0f0a0f06050703080a020a0c030e0a0b0d020403060e0c01020d0c05010b10111005060a05040216 83
    0x562411410701d4101d505480cdc0030f0300c1d8150003c2c48403072850042c80700c07100d900006546180c0324403600f5218005030305540300a5200303822112030300d02000c46850708820010b42c040c001882c04d003440001031011640c48002000f070b05010902c503204541704448d42007d80d80c69500001d41450000c03c1c05800350380005450201d001c5000900d0400c510b03002c086040e01070030f00700181203542603d081110304d04085503420003408a01d051280c2490750300c0ba0f180b0400105103003a09a41c8000304c042d41e030310380e400c441c1c001580400e6440400d03802c410303401d07080920780b4819410101000d00040004110100c06420024031143d80350254070f07602030010180409403112580c0702907405010021f94460f02c4101c0b110380c40c02e040000000300c08903080e248003030141d024160b244410300701102c00c00d107080415140380d5a102c50040c22580c0c2e010110716030404507200e815007044c8074646079040841c000300c1c801160b4100030400c240c699422a241d8250303801102c0050700c424540e0050112100e00540c0203102c0007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 426132886 1250 426131636 426131731
    0x80702070302060a0806121b0f0a0f120b07030207031407060e0610150206090709020318010e150601030504050606151e070b010f0b030610140a11010b0a060206 70
    0x80d0f00c49102d9115120a4902e500c141942c00b00080d603404030118281c11034000414581018070380327004181d41d43e000040c44200714544609100c4180ba032079510642d490050507041804100c547c00a895010501781421420304400d80c50140c8500f0724800c2c2011080340000740f482c2004a135501c203031050b0805030b0407910f2a14050119000040070303800790603500440785452070000f9200013000f40c030680d10320010f008164034010001001e034001400001000358100c01d0b03004416070910411150070209002000f181180040406a02102030103071410107003801e0800c80842c0c0300082080c3c126070241ca19800c580c0445698a20358004d100596040c400c0319480c0c5d5200d01503041c0038114080c01002212181d990300d0407030303100e8001c4038070036a002e1100510014956103030521818020403842e040010f050344036145103c5e00380e0b03c0000742c50040764126042d0303803100703109119008590800b03035900d00070a030a00f0000b941e2114020718002d120a064484180c103000c600014034402c400200f040078011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 426134136 1250 426132886 426132907
    0x1f03141003020d022814040c200316030e0a050d120c0c090e03040e0f100308070501021201030819031118041103040b180c3601080304081207021008070207030206 71
    0x2107169105206d1004a109512800d929080c465440724200d03507210401d80c80101d03801c1e011240a000c420110a000034402c610500c01840c2c604407506110380e65042c125007c4204002d40c0b0701e0f081c2c0006004400100c680780000c0c00454198001034061700b400d1052140c07a1070404041c03a030315040328405074140302c4600c05000000014100307035205040100840d64805941e400d80d004100c810a02ca40407909003000815181802070485500800c0050b1a2040c0302680d900311107004e9004071018000099520090141c50025401003a0f40349800d0044004010036212107010700094004000036014072542c0650b103031b030700c0540294041c65102d5164070b0241400502004100c40c4d00e954107154040b005442c00b00450f01000344180106000346e608456241c80380b03004011031243c150350b4102201001d826080c04c013054001c010003c010741d5680d007081e68441c148031444030ba60054072400c1c001c410040c0d130b41140380102d008142c03505101503910700008034509115503102a401c00c00000b0400c21a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 426135386 1250 426134136 426134209
    0xe04090c03062315031c0504081b01020c030619020c0703050607030207050f01060e07110f0a151107150b0319030906030e0c031b0105091f03141003020d02 68
    0x1d40e002102031040564130010030444011002142d0b80e0315810503802d62a10401e2040d07105e11200c003030b02e400b909058980d00c0c0c1078504045002100700d100304181c3d10311001d40e8100301000d07da0f10f081d8040c01850406054a43e03541100200804206401003100c0201401c104440c1004542281c01c840140c20604d40142c002d501081d010390340c6001e141400c00710300005006540c00c03283c000c1090a07041e560b24000b250a440341c29008005070041c001001940e860804c004514980070f54241061105541268411900015089840c1c1a020301082d8040345504030390002c04c5620740300c0441e505c0e0100300040e0404c4601c101c3c005e80000c80140c0441415030021408081e244261801c00c909000303010300580d101007220070180d0503840205110842002d001d51341441070018100142880303016800152502c500000104029a10480e518804c6602d400745d15600341c80321900703d2440c2010341034803c0201640c000640200c2c003aa03061011502c0701ca5540c28900c2d03c07030b40d40a082e22003400d2423408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 426136636 1250 426135386 426135431
    0x2060c03130b100911030c04230d0507090c020c1e0111030d09060b011b021044060307060305040804030c1214010203150d0f080f0d1b0e04090c0306 65
    0x50817498417022040201100c3c003240d00903003e542000d03040c617280c101e100d40e11200c00447c01505000150b40c0c0d42042d1a0300b40715582c0130788100081c000490038102c003001220842c020741001c5501002c0d0295681c1c940303072000440c2c580c4040026441c806a00010780340c1038001004242548000151803040c003070698440000548211800c1c008050b00100440715054006100c0d10074401404480e40145041860110401058144925400946880d5050710b000390340d0040c0790b81240c031440e4510341440840c0007480420100681520f070405001003555009940a0303442070680d035201080601200000340d600459000403104007054030341001181f0442031000481d8044403091094544070011b0007540c1c407503015249a559a102101c04121140b000305c0016110000700118440110303c0c28002085c0920b0a400c10581e40c2846071090012250107039040203e10044a900c1d00b0300d01d03840f100d12000c1c2c440c110b4010400304010b06040710740a00700c1c0c2c0300420851411200d06030820003401405c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 426137886 1250 426136636 426136649
    0x20604030f08010e010501030b030a050601081b04090c06120204050a0f05090609040b060f01051213021804240219020601080120040515070606080c0a080a0302060c03130b10 76
    0x40d00c00700d590301d05460145082c0910440c03104584c0040c00154443e604c42854090004c089503084c240d0b03500d9860902ba000c4c1c100d4451900110941000c21429940041e900101900c0401400609461b8413034001c64900079041082601c00b00d10705031840300e4050700d0142600606120b40786540e06909030410748548101c0340503185401c0050f0942c6802c0c0b107843c1c0303d1074001c00f0b400001d07956403080001007140c0d802c1d50b41c1030203028490f04180380b8111030624822490003485801041442c0100501c0c101510a02001c020180040100042d2100850001500c1a9035180d4410400c032101002900681c03082d07540070703402000c1c54806c0784d900286541c1203a4060000304101300a900c010200c034060b0720050030000c08100010080303418a501d01200d19086403070114280300341a5a5481903503c20380c005241ca43c0060110100c0d0303d1320703030301d04002061094024120644030f550081e444080050040440d4a404030002d20700c2d207459005c1e080207513030101400c400c03481c0c48140217103a43e5141c064131 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 426139136 1250 426137886 426137897
    0x6151511060c0901090e0a020c0610031208060a080307230316150213080120091804140304060908010e010902010801090504020402071e05010c05211f0602060403 71
    0x241049030250122102412400e40a0681c595451101d1a1a41d01c40c645690420001420000e074040c0001412802241c0221002d42d9600111904600e441009041560340200c9400304000094540c040070400e907101e070030030003803a58540d400210a980b442c1d10010300b43c000002cae800304024800080c402283c089850700f00c1400c0c01c458207140d0700e00840e100b0f5040321482804250104004110401c41103041410152508000341e03900d038000001a881280c182c1c7d19480441252212403064851085030b060b0014200014280061484407090004081d405074110103c2d0034401c001c0480041d42d2840c0701100d0355035940b0340000b40f03021180e01c290203040d41380030141150b0b218103001c3e814040303405945500c141c0e401c100360ba50007080003a00072603001e03500b04803400010b04440404580240d501e00d071a15040c1403402e1581c2074070094650300e804c105d4104240e00709a070f480100c00d9050f01922031b6603445945e680e0881814000b03c00030410302203d003d840000c2581c6c0c0010301c0da2145100fa40d95 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 426140386 1250 426139136 426139169
    0x9051801050106090504020f0c0102132408060f040b06030c0a090b2a16060302030402010e0a0f140d050303090c01090b1315050d1b090b040b07020603090a0615 70
    0x858229070082c091000003d120b00003c00151400b50083c001c0300c0c2504546501c0c1c030b150001e42d91308a0340100030000440c50000000c01c41030344001540d104541c1c14150011403954440320040c1a09402482c2d284241180b440440d40d9864a85c0031510344140070b0515545c80c00d050661001c5900b2a000740c80002e207503201d0109010500400303aa1405140d9440c0c90001c0160360044d800c0130314043c807500c2852150041c61300304404191300c814010042d03900c0059890900c0d00004041c100254050780c0035a00c0404100501107254031558100c400004001c2c0c00580e1020001d0a03190581c0000b40c03c512000c014024a100d022034001010300e000d0301c48152182d510f600000c0349018942c1c81605503840ca25003000745202c40b04145100041c9890315a00d801c1d9005108000c03103c98007612900c61501c0d0026001c956044120600a0400c10002905244c900001801d1074451298000e02814000c004280701202c104640c3c2c81d5180d01800c03d01c4201c3c9800c107490300380003003071082441d1441c0c1c0460 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 426141636 1250 426140386 426140431
    0x30219050912031911150c070b010b0c0a02100e040f0501050f101211070f05060708010f0807050609010e1203030f0601030507270b040803180411041707030c0905 71
    0x440304c80e0030314203c150f0b60a1901c24001d031111000090b80368198040e01c00b40c1001c02c0b0040c11028404c0400041c0700e40c0b6113950741071203000120141c0111407003c41c2001609140315002480303050966040720504000703028120f0460742401e050b5400b0780c01c90b040c5405d9200b43c184540081d416070340c05480040c080304944003004941000903105c90080703408107422160038402c0e50803c0300403034151180149040107560b540394001c81c4480c401d40311a0044070078800203690041d0b150b0b00500d1040380c400c49007420000d005171030310068881d652040c2400640b01c5540d9010300030441c509040100045807040c0103c0c112501d0303a101b11104c0501403040c0c00010710707541c02842031602404907a590b240d14450003821040c59213900442804481c0070a03900050014000401080038001c26000703992100740e00295070100c0040114204d20032402c0c0740c00341c0d001c0c0307001c2e01c291011155121061204010711000031410840c0640001e003007440c040d2000703d4058001c0d004a070241c0c101e88580b1604421000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 426142886 1250 426141636 426141643
    0x4140f0402030c0304060903020a080c061509011a0d06080102190f0302030f04060911041b020f01020301142842030c0302310602120316030219050912 66
    0x943c0a49400d07010710103e00400c02e180d105a00103072203401103426076007168407a451180c01003410282160b01070b070200040e4000003008484441c00540302a00e495040204e44240c0450003040d080d000d01020400f8071142c01140c21140040040c1e4008550301c1e23083c2a04030030210000710606021444009200c0e00b406c5c82403080f40c1c400d025820010b6155151070352008040d00d80028203a50030a14104a07025542c0c0c0c5200b10300c5000164500301d04103042c0751030040c0c24100710002c201026441400108542d20300358a0161b4443c1d0201e0f0010002d104d00840018410490103508007034071501c810200314801402e0700748028507955042d4141040b510140700303040000c0c0700303045261941800c1c03c11807140e01035049841e056490b03040150a1402404203241d103512419103402414222000b0b0f17040c10f034822a00c800c0500117501c0542281104140050418030011f042e195007a001034600c4565144258150ba5080a502d003100661001041c0001e21039044128080e2103a0740c02503403214000e6000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 426144136 1250 426142886 426142891
    0x1e0c060414030906310816080c0a090c020f0102030415060b0c0a06021813020a08070c2427050709020a1715030a05030a0e0111060a0518010204140f040203 68
    0x4201c5850a600e103c1c0c411012204021904c020101d17103d0345c0306030001e6580030713000500016001001e08a00b61007000302128050762100301180c001c04191001038480784407901c1903513000c0c400030505021140e812498854944940171a6500c0402800308014407944255500caa0203402880040c4d140d49075405948505201d000d01076210107911400100c240d0051701040580322450301d005140580801c4d00c0da0410303482e42c10501d50001d80c114103941c01040d0f0340e401a003945408050181c6583c0c64001d8000c20080c3c04035880301d0100340382800606038200c224080001c0d01070b6204042c2d214100032140081d280c044601e0300a10320f011501810718826030740c1069980ea1101004809108031000002000e42440201c120144040c0307020784003003003e03c9410b441500115070310b60513030380c00410500c001c094542c1080070007a0741c0800c03d00300149503034100e00804030005036034440d59400c0740040c00b07881c00229554000315001448001400e2405142c4105503510700181900204000492008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 426145386 1250 426144136 426144139
    0x806060105091e040b0a1409010f12141207030206090c060c15040203030f0c0d1101060b0913090212030705240403050f09030601090905010b03070510051e0c0604140309 74
    0x210740900080303d001144038041d10700003a1002440e090310784040b0b145154141c0010810205070440c4a840c1d00b4155100c50040c104004854984d07400c000300d0100103228100003a05d030704c8072840d0101a401003440301514111031001031035601d240070b28019441d0170044036010620f0280c03401d002e000781411001c0f00e942101500c080c00c1140c540d05030100340c180c03019009076010b100510004139480035150007000b008204c1001002a0f180800c0b000f00928140c02c4411611390400808100104014095440b9446c04070703810348401e0403694401d8010440c4040103035210510401050000d400400140200c500420541ea503a210030519954030b6022120240240300c003400005000c60b1089016206556006000c640380c01036090000786020340a0700310818682c1e88200c160204202482a070380802c41c19030281901d507103000002030009203002034440520400080741c01c030620707000c0070704424500740345105d80d2513080c2d80d520340341e0f62002145c0407a41000d10056400d001d4000009a8041000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 426146636 1250 426145386 426145399
    0x501121104170c0d0b10140904031b02041a190e06150c01020c0102130909030f0e0402040306050406020901080708042a09020a020c0109150503010b0c07051306080606010509 76
    0x1811480706014080d01c0450022401100203050081e5603690580c00c04c14001e1400d0612810401d81400e88140c659100e2030411004801e012041e403501c000c0241d1040c0c150400124010509000842e82c4182007130003944980b07020702202805400980300764444101382c44042072047c1a0344010b56104181c01004c40c64104a40087da161400d400b04c200c420f545248000c1c1092201c00388582641c100c510900290f9401083c02011427000032a070780300926058005218031055074601406000383c0002c00401c210700e803000964070b078407240c046400a6500610412040c5414244100250800d0800d40c2c0013690f12000f0442d01072003080c506000f01c0d000f4101203000c50111400c0000c0b61030000821048003445074000032000c1c414809020241c1090300174248030589000010588141030700000902c0108e210301c11206039102090b00d041d11400402e0654481e2032036441031400c1d0050b0b101d01d500c5220300244501401030b070307007005080303070b0204048412a48856006480c24014004401d400c00d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 426147886 1250 426146636 426146639
    0xa030b011205150403030903020c10080f0a33050f030304120302070317072f120a05010222060801050117040606030b0112050f01020306280b03040c0501121104 70
    0x241800c80001c64810012100ca1000d000c50b1030503100340403030f01540844e60f40d01c511028980c0511050034441d00c126030002c2f00c241059009483c881c0301038401c103110b1000d180052107070080ba038010800c20a184148807103000005070340155504034280e0210b2640010600040c1d541030903200d01840f450020301443c2030500745101c20900501e041e0061b8114400c4203000004268041050100b9807502401c1c55901d0405003000591b5032400407600440f516110901c8403513220024060b00d06c0c1101711500000b0b03403e844003491410300c401002600c1342d4070009840240e5805038010402001521a80084803565a00c040d600c007482446000d010405115644a42c1182c2c0c01c0917036409449101c000849076200d88a5031420842608042d0381003460032180342c14010100901d49100382c01c0d6000b94990310304070300400c00420703988010402c000c40d8034101411000401c0713008000343c560f5086041d12307460581007101100081c0d1007006c0c04140380000700910400a8002e004400f8501c1e29540d2409 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 426149136 1250 426147886 426147899
    0x31a0603160c0c063507050706020403051c020d0201060b07080702040219083301050a1b0302011406030c010e06030912071208090a0b0c0a050c0f010603110a030b01 72
    0x1104042607000410402500940000d1207202c1c0103800b400407541c0725031105a801c13605400c140036000c6101001040d040a980b101e074144046036034806103e00d07003070340c0310762651030410b01034002c035040201030303015034a9850020100b15052001580c0c0e59030844903003a6850200780c0c00c86205000394a06c401c010800300d03010500103001040298400f40c40189410101c0e03000300c400c1c0602c600c0b850b0000d4041400d0009031000030040c80b580d620400040d0f81c1d030003000c90b0144e051408181945060000c0441c1c1010020301030000e01c0c1c06464485500804040d00b890000e00800034207410b403640c0200080031444606000407a44500701c01a142e038098041c04800300b00d4240c00042004c0d4061160320070340140c0d225202c02914a4521412003641e14030340041c00a440900c00600c612284d0340640e0140010503982c10038a13070000031030243c00e0f80e40c0386030f0082151184503045049100d44511007149a48800540c85481201d0086500c200001d203800100300c800130741e900c0f02400b000602d00061180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 426150386 1250 426149136 426149161
    0xa120818010912240209011205090a0b01030506090d0905030606040b12010f0212010b0a050d180b0106080f090f0304030b0606070b04120201060b120403030c0c02030f0d031a0603 78
    0x940c9414104142c41c01e40e5080030002040d203515049640c00802d00508003d0b1041d80f40301110400861025405c101107030703000070140e00e940b048028140e900e41c0041210742a00340030448a03c1e17045001a200ca40e100d0031300c13036558541070b130b500c1702240b0403143c40c00f40503403280c03a0040a540d0018090000c0d91140c0c1c0800014002d03c5800d02c2c7c4c0f00c0303080b2814a40180b0240319480c41c200780010013585900e02404a01c98490059000c107030403240c100940600d00d648441198800c14201e20005135100c0303800030b2400c8448034a0001070081420030b00201e00d00350041c100c0b51180940b1400000d45d03542d40c109503074517207000ca0440a11680107120502c0050121a0355980c820000f0344601d0030300485840701d8044107000c0c1c1701600c4a41d40102d621b64061f9081c044d40700600030903c481440c103031041104c0803d41000610240406681b41c2c0c2e00c0601910803080611641d400408460b0605000200d66498050b82e84402000c82d00d841c22030020b07010100300200e9010001042d0070b0070360381e440a400d0071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 426151636 1250 426150386 426150427
    0xa110a060f0c020307081006031104020a05070b100306020f0306030613020f210313150206060f0d0206090405040b01050f091603021608040915090506030601150e0904110a1208 77
    0x70305000f0248040743d201d01c100406c440c51f1340c2210f0040380d010301d1800c2a46540c1014805580940d00400101ea0f0164100007101d440c070380d11040f01c80700f40c2e03145c0b02c1341d514020301900003c0c0214000510030004103005406035026000807001c1d81d4080c0c13581c030005030081441072402074100601c06450700142c030303101d25140c000c4c3c07601034403012001d00f03044e0b40e00b803c690180d5401c8484a070000001e00294040c010030524280180c0010506814000c0c00030302e89800b0800b506110b0384926841c407085468000a40f00c1103400544103000c2800c0600d05248110801d0203180e001b10a100c4203206a481c100410300e00400fa075450a0010881c10141100698040100791910308403a800b2100020001c90090000b03210321200020701e1503030804095804800c940c8840000303402c150038440c1680d004907450f811914071a41042d40030361131500558400d421110103d0f4024a110100001d11100b100003110500c0c2c1101e2a5020580700c0119102d440565007000e80344007020b100f040c0740c004c00c8680c05c61 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 426152886 1250 426151636 426151639
    0x30e040e120d0609060f0306060e09100213030209100513021608031510030614010804030f1101181118070207090e0a02060a02030a080105100c11040f0e0a110a060f0c02 74
    0x10f107072925109543c09440d0350ba4811607503a00400e10070001c0c0141480b50b070005c0c01d092013030080142007100d05580e80d1810850502c0c1a107500040101c910400140460000d5501400303418040c641560383c402180c0d4140319080c0210900800c0c515501d0540c800c5075041d01e4001c454100400503520f034107807640c06c02050400c02c1e0a145406102d00d40c0c944404240602c030540e404140349050034642e8800700181900507042c01401c80c14000060b400482e008080b41c01c52030b04001607004a0020307800340c0135114580721820030607035aa2003032008030750701c0b180f036400d060720300b03802288030b80c41003001e0340d43c0841300700005800c8450203003c0c07110b2942120300540758850480c1d9114a2503000034216900c9240f000001d43d1000036941c456a400414560040a00725403002c035850320000d024109808000d0700a28003180d8000e000c8140d03640303900c202c0300076491400410105462640107652010700c504240ca078a1185141035482d417410b2000355003500e0803a91204482502d203002603030908000d0b03404031b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 426154136 1250 426152886 426152891
    0x60303120a0917030403020f0703020a050607061e0905010b0d020105030606030c04051e010f02070302031e03130312090f120f02030a21090608091513080304060603030e040e120d 78
    0x5000300740103031002e00e14074030b001c2103d03a581d0a01d8540a8a00032510a0010040c1c004400400140c1e480180e07030f0003100c90580b051a0b4070301c0c06140a100a009003441ca02e181000c080803035582000d213a001801c0c0a22440081002041400030424801c83e17510009001039820000610942030400246800540b505081401d05450754005a0000e655041d0142c0040e1840007000d01980c0c00404500f1010340c1c0d0000d04541425600425241d0b801460300c140d0b8580000d402001d045401c001b220079010310600c842c0d80050326841c100c410500408007910000c1c0e040c90303000c01c0c40c402d03074000001161440384000c258114255500d044c1e05c50040c00582e410301500d10f4420100720701c00d400080307103640b403090f44801c0820b5000103441c040c8560003001c05c1125100c01c101c01028002107400402200309494555661003400c003a42034284000c2c01000c001010003031004001d032a80180c010380b803090f210441c0300d0125409010441e41c04100c0342026178441807a444108590400501c064421030401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 426155386 1250 426154136 426154151
    0xa0b07030912210503041a151314090610060311071b05090c090102060414070b0a050c1c0503070c020a08010e060a0b180103080a09090614100206060303120a 69
    0x100b49400030300c01c8090360700120ba2007500f400b1241e50100c40c2c10182060030f1507400d41c200f98460200003c04040e07600448011a00440c43d103d0300346c54000e141c0807000f032501e0707030152080300814040c00c3c2c1d511510003922044408500343d034074003080841c452083c050780807202c1490014100c0103402180f02031003100341c0030041c17100814540d0700321190320660920040302d05031810041c03141340640144081414801030000b41c019a80c00b00344123411580040f511100c201c1510f00007410010240d0215141d070303e00040c0820030310b40000241410b10809410303202c1003259140010304442403120702500080081000810a5005140b05940507002400400030191610625800c40705c0300640c0a0860348014100f000350102c82c092600c81130310a0720081007041030300c00c08202072003040c0002072013428007246909015214003144c10040100c11814003206540c2d1114a40070541c04c01007600072100d0380c01c00301450703000003601400384034080d004626020303040000454804010381403c15550301e03240c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 426156636 1250 426155386 426155399
    0x302030d0c050d0216020f04021318020c160815010b04031b0807080c040506060c070e09010b090a051e040302030a140c03040b0405011d0f0607060f1109011205060a0b070309 76
    0x540842d0380070318245c944062482c0108205008003083c460b00c00d0b40104031806c00c042c600003002c8121030301c00c0200040c210903600007c0180c001c800d00e10045208045059032551208030340314046420103000e480004600785000301780c04000f40212587c0340c804000c200005207150080800c96009141415450f503100d20550341071008960040f483e642c07003410040c5003868103114460304094212080d618026050805545503c1d1038812810070007031310000038620742403c1d0400070b0702820040031070400b0301d00f0321881001030034169051020b40164041c000c030803482c1d001c00d41c0c2c09039070590011400d09990050455060700040c8100d20007003020b00a0000350b4030104044c00141c450091003a448900b003178001051242000260784503525100000c090340e8944200c0461040c405450311031f074902c0c00d82412030107498000c2003031060034500742c2e010042a4003003002c1c142c504000da0300e0007480080b1450304400c4e10382c1501d07802d52041c404d980422880441c5001429214400c1c200060525034616 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 426157886 1250 426156636 426156641
    0x30c0e0d060b280b031509060102070b0705010c080105030313031e02030a060c020d02030a0806010309080c030705070e1014090a15150f050726040902160b0907030302030d0c050d 78
    0x181810541030000810740003d81c20510202c004d410510b50b0342e400d510f40b0b046040f042c403200309884c5002d8290980410702d141d10074080f607406002c40c004480d035244032a10303003d4002c0c0303a01030b022800181c0b401c001041c14034020045070140404010417036261401c503220060f82d01d50001c040c900c02c5840450bd0001618180500f9035079502680300054544003203030000c0c0c100740b1840c0c0010700310f4104020300b004d4507822400c3ca41c2c100d80d0a00c0d000460600600e0541d040d07200302d00240036207202c0402c0901c10824009400425518591070200168592a48000d6440d0543c050503004080ca010000941d040241d105940234a81c1c2c1c10209014240b20700c1c05a00701c00d03d03001414800030300b5513040d104680101c42985080b26078503000f440c1c1310403078440c82c00141141849100754200c815201e05a0000c038000d40c0d001d044014001c5541c0c4c000b0003a160b000f0304903500100c500c0004000080c5072000b01041c140d040f0307a01a009186000d26802c050801026051300c0c0805104052001b11800301140c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 426159136 1250 426157886 426157909
    0x130b09010f0e0f06150d0308060103020d140402101107030605060d1a0708091618060e0a021215180a0e011a120105152205041a0106030c0e0d060b 64
    0x10340a010f070800381c1c45103907007800360081c40c0c80c1c0e00940f22268a50142c49040e103001419405150124041d00c6120040700a0b00c50424001091070425400c41c81d548124030265025138030071600c00034040980f42007668104080c041d00380464001d00b1042000c20a41e421a5902c4039008002c05500d80700c0d50b13102c2003d4001645086030041c5883d0801c01d0721500615038980203120340300101105600c0d801803d4501c4528015010000216100081034a10540000300540100030780c0c01407a00d401c1c0c1050300250000382800741405900c0c0c010944c0d189882c3d42071140f40c4000b070203e1590100b4062040c0d003050000e00345404043e038400b082d007412075003031003071050102000b0300076024840a841040b00072449240f8068407a4075002c00e03c510512501000c1080110541d02080c40690100c111280f083e20464401c5c401800c0c041008201300ea801c82030205054000003105041e62a540214100d0748080f0146000c2108003010300400d01e04255180119803054402044182e1b00401060001502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 426160386 1250 426159136 426159161
    0x4090b090303041505041101032307030b030c0d08030106210606020307060b01170f070908030d0603032c0120010f0b010f030b060d020a110307050c010215130b09010f 73
    0x4000d03c002c12aa1655a04402c54403031003d00003410181c170b030220f16481e56442d0302e05241c1c0d10000508007040354120020142140804200e0303034a82450081e025001708905e03135120b4000c2500729107807881c14480c81c0002a07048180b190850b82003220170784851002e2006102d200081030020011a4a10f0040201500c0303203078051030725851075113006000c1e6060251040c0c10b0160190074894042d078000c0629500041190742ca8206884100040d910a910354100c00001c0c040003500c501c4c41c0c0307aa034000b101141d01c00d9a0f54008110b003082c40082000c6040e40e032040140207250508030310341c41402c448080e0503850b80c1540c12111040821400c6610002c5007000541d190554501d040d070f000b08d074095506034681028030040200b07500280c118814241a4400141c1c082104041580306004100c4030f05081400c0341c0d80c4481e82d00301995224112428540148103031006910400b20314443c05000350507008259140c42c0c0c141d0b45400602e00c000700000c119640c0e0f080041c00c292264014110882078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 426161636 1250 426160386 426160393
    0xd26060d02101d0f0f041119030615050403031e1b05060403030b04060602030d110705060711070f0509070f030b031603021f020d050c070e0f07030c09080304050f04090b09 75
    0x43c400640200c4001456802c0d00c42e07852014000c849440d0402c005521520454001402071445285003c45000e084080440d0720226110258003a1705580700500b6650030740100311510904c0703c4c0c210344a21030340c0401000602600140d00810740280118000103089041210060001030411000740141c0a01507030a075000c80c0a000a049d090302c54508140e40c150360500c00d81d810540060360364800c412039840440c1ea100a0308154008140607500026481019107880c2c1c1010400200030040078450b41415000e08000015030640c0d41c0039807812644094070135a001e0b81d031010280c1e04144900c5083c41403584400e402d04040d80c042c4802d125030404040d80650160560050224140000500c0070b0b40480d00c65100500d140c0004000c50318101d54502559500042c0c0c42103410310b84075510509090500f0f03010f018059040019046c803a44150360f080011010b4200c084500750814400c01c021500100410312480c00d2101c03c1c41076060021304046107515460b40e60002d0400105c0c1d410f0314540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 426162886 1250 426161636 426161657
    0x304080d15061409010509150403140a03080115260a0b03010905151f0e24090703020d0b090c19090e06091023030d26060d0210 56
    0x428500c18071650300c81801101820350300b0100e01400e40011440798894040c0e001c81c0c50301c00e40c0c3c414822103413040b4000d414224062030611514615400c10f02048400320803100d10400d0340c0800207544000309805643d5070b00b2076440c24090340000c100f03001200003000b0103c243d51501098503a000703e0700d58142c5c40350f09600c0c50100000d00c111042080810300c2a41481602004aa000215001c2c2c1c0f0340006110145a02c8104020180034004000c68004400618000540f0b0401202c1c1c03904c158601d1070320100e0340050700d240f4158070001050483c1d10248d143c012401c41f9109901421491100c44c034009041c00e0404000744400904850701642c68000003502910410344040d100340100c4a400c200b20000d003000c80d181e20b046030003003019010341000e070001661b980c1380c00a0300c0001d000910417200b40ca04c040c0300380c0080d20307078140c56103009128404460824611402025000e21300181c00c15084600e541c0041043c03080190540341c3c8201d07000d0390500980e41e040c59503003240368113480c0e003004034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 426164136 1250 426162886 426162907
    0x3020c030c210c070b090102070e1306051e130204020d0e0708070806010f0b09011e05120c0a02100b150309070f05030303060105090f0d2001020705030d0e1509030102030408 76
    0x4940c1c642c501d4000460074020241c3c1c68000289a6080d54907164100ba215001440101e1500020341d02c00c54a00c182e200030b0242103c40d8080c000b03181405010148402e41d01d01c0c540c040d107102c00c0c641c2c01c20b00c1200f000000d081c0419142400020520007040940703001c2c5c00325038542c1500c40345101c0301c96a402c03c01c1c0c10000194108550401401c03410050311056142403101030040d44a40b03e0020515800920300f44940e100e08540d486200c080301700d818802c541100300904030b400910480600c2d44041011582c0c0c405a1b10503240d04000c2031340141103000800c0101000380c1040c1c1000754118180c400542e036140c0148001d5417064819000400020b4a0500609598034065000034041c5d0410020f200381079901c182200e045540c03d487e02c6540d24005008104000d50407100034004940c03100c00019018912806201c10320300913400c864119880e40101a1541d140e846250045030001fa80300209080035a02001c4001345e0817002c1d81400c4c03d54000c030382680c0c401c5400300c440210014486492 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 426165386 1250 426164136 426164173
    0x80312010308030a1d07140f01020a0b090f030d052a1c18050d022109101110021b191b03060c02060604060b2b06050a0b030a0b0603090a1203020c030c 66
    0x3071400232190b10304410b005030700113500c0d180107640242c402d000c410300044411204005034000c0d100c0d42000c40e03945020014106e001400107407030502100800a0b400d00445803407040507200112200c01451070300c10762113550324607a04c900003d0166603496185c512800d00105216450403800382c07001c1c0204640c042002802c01c1c80e00310341642003c0342c00d1405c1c0010a1454103441e1106c3c0181e401e0078201e0203c1d2415561048268400800c921880170590601481e90b0049c1103401701880c1130034807074005e4210840d107610a50070158403000d440d44103c004269400303016504003428460202c2a50340702d4454000750740d00c41c107840c40580e001100784401c0f402c291040400070843d410f01c072410403420700129031042005001e840c40800c11075070b8034010508558000d00051000801e4100d4444d0760b0088a01d160300119900c42c54107190071880f10003030904208032031103101c085000d4802068280d890f0084024004040713401c141c1d0030300080307851a03c1000203000d8881c3c140c000b040d0845e4501505c250 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 426166636 1250 426165386 426165419
    0xb1c030f08060102070f1d130c031101030209040507020a03410c06010303181211040906150e0a0c02031e07030c0b0f09060912070b061c1407080312010308030a1d07 72
    0x702050070762292301007070b81c2050000541358000b81141f01c01002d540100d019020701082ca550007840c250600134241c1d000941d14030402c2c4030381c49840400d0048150b0450340c4c04120303850b000c03e50180c402a910603203142403101e60986000212810202175000c0d161404409801c101c000ca0909442e5545114020445500034000301804089101840d0303039403803040000c10041030217591070314045010005980c101603507100981c0b40ca01c2500766580c6a68101c544199207000c01030380713040c0e001041c082c40807040302d0301038001d0f03d204590800d0322184074465600121040d030070412000303c000005010109441e004442c8154241118100005464102030300640500c0669000d0308850541d038150341e0070364181d075410040c0c18402d55148000725240446001c80d204041411010113002c02c0248518510341111032000c0710300b01c68a425030b0903070f82e100c1c1071340800c0101c0385040100009070003c801542e10200c41a404605000500804c1d5405c000d81c02481280f500001014802402c0025410340d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 426167886 1250 426166636 426166651
    0xc01021b030c0106290315060309011508060f010605070321090303050601090e0610121508120309100b031906060602100b130203280b1c030f08060102070f1d 69
    0x6014020004100c031900000300381040fa01c0b010000484542c51f00387c00d02031611000d40190383c1c034940600800d0003001107410384810f0790281031010504440014106114119950190140e40d0030080b064030f06400030681101040111403240e18691704c42c5050461143c050f10010880c1d01441c40d000c1c0c1500c200804090412401040410900c00e00350382c15601304409039021581c0d01240c034012200c03c4010813a881240d0b05100c100c141801000590a00700e40c1c0400039165526a851082c03611844143e550003200c2c0d101c1c1600142083c2158031240c0d98a000400300c5e00325010a082902da00700d0001f6090340c8859544004000c00ca405001c1c8011582512804000159100b0001350b0b54100700504600010382c08070000740b42c1c0c0b00f651250701005003000c0c244240f0054000008014001c1540c00b41c2c0200e000302080c51100e0194821a1100c07981a02ca81d8401d038001c4504031140d4600801590442c802d068001914102580e641030142c0075042c009072200603618116814980d0280a80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 426169136 1250 426167886 426167909
    0x17120c0a0e010f020304080304031b0807080a0201050310150306080613050307080c01060b0c10110f0a1d0d110f0a0b120a02120702210406020c060c01021b030c0106 72
    0x80c044560300004a41c1055400d0820031050f4165450403481c2d0300650300000424440020003100f4025050480302d046404040001c6060b5110603c59072100b0147c03240c240140d116040c8030006601840245034009080c1c3c143c9510140e0701c102c0ca0b0032080380f10b03030b480b40800c0d80e0b03007030500c4152407c1c0442070380202001c5119100252582d90707580c3d80c1c8545500900a12000b10f50441b84100c03e4001900402d0f078541c0454484011850440d154125501c20511b09403601c040c0009a01c002010307603030034070048810306044c800d09050641e080485010400840c066450983c11181c4e02c50848002d0b02c0d0140e09881d03041c4e000711040c03080035280340090900c20f5007090000c102d901da4490894900d102c41c4a10b1060548442145202038040c203141c010207402613008000410f0760000e440b8521030400c041c0116403c401080c0c4070010b1040703000e00c07001600183c00b03151544c1013580003024110008070005241075030240c41020a82864010141e2580000404241850b0240585000780c000404134 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 426170386 1250 426169136 426169147
    0x206090a060921110f0d090909110411090405062e0e0d081809061302160f0f0210080903090f030a0c0602011e1107140a17120c 56
    0x26655840c0c249a004003142e8030b4581d108100080f02441104128840c1040720041c060090007510384101800d01180798442c01d00c0070a8082000034600f2031321000f80e120b2900e04c60a18903424050b21440ca014ac80395201150880d44d1521107201c0c010446000500d000d8031000c00380200310039a03a001d443d072403082c03850724500311604070100407110124081c2c0c2c44658022924100c191000902140c00682c044404100c2c1f50a0003098401004000400e0454466101d07820b02046007941d02505c900342c0040360750040b00680d0180398014002c1d41d505103044811007409a5841ca00c3d0a1043c0b02212a41040e2241d1021420300505c1c50170151454204058140741025143e81d40780684a542c1c0d109107039070303203e4811680341446051101c5400040d6050115162600079020f0030007540340c081080c140e8000c00320380c18000c0c400c8004001440245c0c03071502001c2d0b01e0b03000f0150403445a088603805400b1860000500144661414000c900750040c0c80c1c5140f2032641c1c0c1581c01c024032119204008000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 426171636 1250 426170386 426170401
    0x1e100908060a180503031e0c03090d0305060301150b0702010305180a02040b1f08010f0f0608040b04080f120105010e04050121080d1109041b02071205120304120e010206 74
    0x1051035102d412030000180001c581078002804030510640034200d80000000d00400e8403014000304821030600d42042d04517140d85840060a100450b012121a001a045925100d01c29004550006001000859568031840340c5d128a9540c2d540103402202d0002004011540c050080d075074003146100c01c48443e40700b4400c1d00e68840c0486ca200a00c2103170741d610307009100c1d52038800c0a00d00d0011500702a011208140c0080c20000c401e000700e5040003044140044c02016461004091710342c540d0340c0c1072075a1599502c0d032100b028040c3c81143c804405200010720140325401a000602e0000f91081c1c944d49020000740151540c403034954009c07401c040042c44220158414908401c5925580d0500003002d41000c1000307005400000100e203062000003074400600b8005800240001ca40402c10814498012510510b400c0d040c1c40142c0c204034420010803415070302115005010317409940e42200c644810000561046408541c1d07039110b04040c0300c2c102e170f02c000009041c003428001824141013012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 426172886 1250 426171636 426171643
    0x203010b03060417070503190201090b01170d08060a12031d0d2102120a022d070b0a03020405180f09010903081501031508030309060c030105010503060402181e100908 73
    0x1e041c03014603500095010030080c0c10008c44441300ca20b0a100000141ca10500034040e100038441a101046000d0001c10751a001c00d2015480301d1034000140320b001000d01b41500c00c0360780108156030003424650002592406641442801446540d800c0443c2d010149008400182c0e20780450142440c0c6001c400003032401c026103103101c0100c1d403c03120001141c00b012440c0400c0d03419004103103031022409680d615000201040d500028581d080445400b200f101c80c1f440d100315103600d03501e90000e20200241011040180420381184c5805454240c0b01c401080c0d8800700d00812204002c41c80e81000400140214001c0e044440400207205401041e10b008008180150541400140301c003200042603000307501659004581c0406164084c0da80c241d52030300c0341c01c1221b614002d4000c443c0000c140d10141c03411a4107941c01615440d007551200c0080c400203420040b060100c48104017660f0f0520750300d0460794201040c4142501c2d282442c0c031014070809240c1700091400303001d0045000d001141011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 426174136 1250 426172886 426172913
    0x10b04060e3d030b0a090507021c05130b090a050907210501080c0a061407150e010f0b060906040e060303070218071b05060f040c1e030203010b030604 66
    0x145003544040d01020005906032075031a480c05441c1d40c2c6418003003900c00320b071045a41d40c000c9014286800b5602e0711401d406545803805216070200b9241c00a011001e11036110740e800c0803803481141c0b44400750308030084904070303074019000c0405c0d000f0801103040c605011900d0701500c1100c2c00703541060b40383c202194944d110380c003a640c07007082c940c0d0006e50b116114010078411282103903080822440105c3e030b620000c1c002800f03044100c1c003d80c01880014100801908100c07405503a5440558401c00607101c035903001030b03108640a540504402d1107100341c0c2d000381507450074260000140c07200d61030080812240c120150034012902400401d480c2e54840d4143c8084a411b004206034503030347c5000007070031807240f080029441401848100042200c20400078400c011589402049510403035104000c4001da5400a16550181c400261010188005180c10078030501e03003408900d4480607041140316210005140d01d03c040c81081003546024050565110410f50103060282007d455041054050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 426175386 1250 426174136 426174149
    0xf1803080406052d0103120525080904061403070906140409110604180624030c020f121e1305010c030e03010f051602120306100c0803180601080105010b04 68
    0x48400203824628410301903d04c80100b008400042c200380021340c8500341080c0010340e840280c484d0400d500c28002d9080311201402c8440d501c880000200349151071038144002103c02c541c041c40507104507102c0d070003400013400094202841d4444100149072900c0f4083e4001401031703080800070480801e4031a20505030070700960f804901c0034071300c2c1403508180c0109024980c00c0302000400262a00b8008000a800c02001d0300c01d00800f40d48641e00c002801044041140890b0780c2c1c488410158000c0d44002040b040500560710032401144040341001400c0d01d00c0d07c20b48600080a03200b6010340600507040c0c000407541c00d4102040350710360060100d50ba01501d81030210329841030080c18000d80c280c40300740c00010000d001c8a8010b02054002d09010340c0c150f40307030340c2d03003050104c14045c00414032609401145031081e040d580c0704003c00001c481800756050500503a00040404a0708500055115a00800d18001c410b001c225038545404016403001100d13915002c018000f11694408940c2245c50 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 426176636 1250 426175386 426175391
    0x103051c0e1e0a080c031e03030112020f040606030b040b010504121403070507060c110103091a0c04090603050a0b010e09060402090c0903030304030f0f021506090a090b07030f1803080406 82
    0x5001c080c2c58014110101c41c2980301050000c0060320110000d0400d03444038080d0203548624181080c0020110703d55142041c1c82e0300144014810105514401c4080c11700007020091203900440100d004c0300c209801083c0060307104c484031591403d06000f0301410170428a403140c903107480e1120409104001c13010042020101700d400358505031003081030307c0b507840c2c1013000d03102d459545940251160284507021522060080323450f08280d0b0082c03058050064210f50310842c00e41603007240c0810441c0050035190204400d200c0465401000d1040802030352003a8020a50104981029100300c50140d000c4400c404540381001061800402c686d03421960568042c0c0960b21182112203444c0111122190140f00102c100028035900c615a185c02d50b115071035a0b1880d0700215030480c0c803440d108501d214200c0845020454a0030030027802903104039859800583c0c55400d40d01c8035800803094841e140000d2f1292072070405e58034203210380d00ca9049180c2039140e4486640c0e030045c2c200c03d001000605101d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 426177886 1250 426176636 426176659
    0xc09050d05070801180203030d0c110714030c040221060301020f0423060c030a120204150507020414060a050d060e0304030f0c080d0e0103020304051c030c0305010e010308042d09050103051c0e 84
    0x500076055040bc1680b58010303a030081e43c03607a9481010320b2505005070301c0380c0b00b9403810003941d040c14400c403884012102d00b519080b05c10034030b50f2465845c024103840c2d0950750800448051a44071300140001d020034003420b4030306610340d1100d000350b84c40b119403c40c4203003400c00c40e101e110000081221a129098140103423000c503036110b408001c0c02680c1c00201c1410005484406451b400070041c18060f10844040242c28031014140082c2081201e03015000400d012091010780f60810102425900c01d107800b240c5010202005401cad80c1140d44111001c2c0303040f0001f02d0401401090240c0501100c03001080c4000c0d881c64014401c8040200940c103166000002c034090182c14422021144a40c006084040c10202c2c0300070b0040825032402000a0320300b50011039004001445e05040365001602c3c035040c1800e16180080c100034512001e02020071a4205800f9000f034110513100a0194400014040d803440c20441e080050f83d80b6192500580352148040c82134100420501c2c0d0300044d40c4910218 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 426179136 1250 426177886 426177911
    0x109062d0801090b091e060c071502220602010507140708090909100e0708030f0a23120708042d05060a0e010e0d120c09050d05070801180203030d 64
    0x4103107801c805195420003080c40148201a103280d4051281e01040f071300000d0701125000a0601c0b0721150346002d170800d0002c1200c0c03410b508068002da034040c1080041c0b4941a0020300c3c2280d210100c540c100c0385003400e0340b02030408440a008020501750009024a28044000800300e0b50307695111450700001281c40c200f40a140000c2d60140003002d8104201e41c00e02e015070b1030380c4040d04000d03034000508200300580d074050302180345002c40d007030300b030065090094140b84440702c0c2d0021072010007007200c002e5408900400c0d00c0d116880b00040c0990b159070302c403003604512084040007802d5500713100d48981400005a540d250f200e00f00d00440c8001284031400d8858807848030035520020f01648220b00c1806024071503584800d4404a41000801c802d8034000c808540781c0b988481104046a12018442c4180c075958024000b165420f15044e000345880d400095128022803905552680c0804414000d0002c02d21400c40440c7c00005451200d220540c00266a03120b0301c22a900c1c82500c03203000500340e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 426180386 1250 426179136 426179219
    0xc030705071506031403070309051e19050102100c1d0f060409020c06070912110120010e0706031107110f060304080d061202090112141c0305010906 65
    0x1555842129a810782e4585a08034000d03040a000a65181036401c00d10500114000111044940d00d520358403c20307441e1000f0841d4140d03000d02c00ca000a034604d0b55840e40d990720780c6100c0805181140d0f0210090381010002403402e01c2c00082d4014403860300c0441c404681d004445c000c1039080d00c454040d42d902ca128003241d04554090b040c29000400410045580026600a0400405803d007281e145694a0781d04075041d06132842190441c040d45010800030660310825075030102818188050170f0443c0801d241e240030303000d1413071301041d035510261014150420f002d600000c04151a080c04602c0d800d001401e4607200e1110020100501034040c01b81c3e0351210903520b407401c0b6006001c5030f03c0c2d2074103042c0120181d0085103041c440d10b20f0420003041c801c40044482020f40d4014288852503030070481150355008034141d040c0c40740392a070703c490004003d040001c07030815035844ea060b00d241012a00302805490060704840c00d11400c0990512103007405081f606c44241592404c00c41c040010391490f01d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 426181636 1250 426180386 426180397
    0x3010e01050a0b1201140112050a05030304110f100f031a09010906030b09060709030204050a1404030e030706050415200d090f23040e12030a14060a0b030c030705 71
    0x5a509220801202c04126486094684819201c084020b240510320342d003200c01e03440e03d04107081c11080040c040710340c1c602e50807914948141c040343e0708600c481e141c291071500304550446d2001c0c0003920028081c18180c000009001003a16030b2340401c000c0c44005082c88401e01c1e9824101031b55400d01d90080881d060f541002c02a01a040255550b1142901e01c0030b01103a010599410825001158080c400001c0e110300c00e0134140c1e43d10910768119400c1001408015211510480d100c03282d650854413a082d10a0180c0c0c8261030340b40412543c40b043c10700300a20ba900c007405218040c4010064401c0e00360001041c0c1070075280190a0000e07603888030020719280c0c9294a0a4825407155218940c2c001243d442a1031f0120503146046584e0400c80460f40d440340401900922501800445410641c01c8424540301600c1690303115001c000e0442c4140d0011548000f010b41c40300c0128900c8001101c04c290040419a0030b44400c505201e80c0703580030f10000d04550844000040041c2540748184155034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 426182886 1250 426181636 426181661
    0x9020406030b01060f020f030a0c0201120c0e09010b0901021b0a08060928031e031d06011d040506130828030b0a050312090a05120a06050c160f020301 66
    0x1000c0d80d00c82c240740506110900881000c14100070104d084140005004034880c071410700150724000305054212070302c454201c0f04a06000c503a0000116448841c003400c1c40103a110742d80c50200300100000c10031041c00c1070b031110380070041c00c10501403980d9010880d030b108080c3c00030000c8155000720010514001080e40910b240d40141000d11031852004680b80c0c030300d607880c3c148085118100e05040089244040c1c4010041120a1200303c183c3c0b0358070b0342e003c92003815400c00048500d80549400d100c10810701b0454400c1d0080b44c010f01000b420000d000c00081c0325100442c9807460259901f642d1800007400d046804030700300c0302c10010881c0e440c00710382d20b00b468110840030310840444458008414168442c0100f030a06030120001e080600c0c4040898070b00400070103000c6003541c9010840d0707108010854204900d42404115500c2d00003041004600d2600100103000d00390030217104984024100c0185800d00b0400c5048800d02c1e03180144100c5e0300602c0c1d118000142d803000074014402c00081c07a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 426184136 1250 426182886 426182891
    0x41a0f0c010507120b0a0e04030804030216060917060c0702090c070f0602071a0f01140d1a0412090f0303080a180302070807060305010b0d0b0d05070b0915161104090204 74
    0x401140d501c130f0041408013410b480d013031120351200001c010451a40d0300803d0060015900040d000c64404e02400d82c02a00030700690f0303e400c0c0424000e19480c0c000e40c1108000c680c1c81c07072080112144000309154844241009172000d4140b040001e1041c3c800e40c040070303105207214030110716101010740072940c000b0380c020210f060309c10b2940307002000b94015034020350391107015248060600044900c602d02c56007c0d2a071904285c1c2c00d007c1c0081c40c20a5601aa86d04426180795540c000751100080890515020194001600d0186030246208040089640030012115810400004001c66207001d076945410440503550f1419110300080c40000103107000d040703070304203400145034010943c44180c0c0d82030800d880c1e007661074003400d40039103800388640c01c0800760400441c0c0419110768804002904001c0894450440c952206481d00c0038a07006240580000190f6601d24645900e403c44240c014408540c00c106c4951189000b49500d031001520720341000d003154000b07a0300c0b940401d24071580103004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 426185386 1250 426184136 426184141
    0x80303160c171318021207080901090218011a040b04050904030c020607060b0a05032b180e0f180a020112020415030e010b030601080a030507030207090609020c0d05041a0f0c0105 78
    0x1c2241e0160f10b0b10420802a581c0d00036400401c41e540211040c019004140c0700c0d00340c8881108907001d4034028842943c55580d416460f005940d400d0700c02d4001d01000c2161243c039414030700210aa401d8600d20300030703202e00800c01000780003683e90680d4202c83d41221410582d980301d040c00e69071a0420318000758024000580e000c20402c00350321079140c480003502e500c225283c5034014075958440341c10010403944096000740842502000e0001411030740341c03800c1019596001c1002140007156001702c032820b0034202c00c20844036400700800c0c3c0e1040c030100f40c11110f5860b0b03414035501e40049507006410058114081e0b01c070720f2641c3e01141d00400031030f0900814640c2400d002002449a12000704244d42010300079405440c00050741e0b41070f2a040c00150048254590701511250b1140c2c0f02142036014601c40020368084610030400208500440541c1d6594041441400e000801441109000c0140410b01454164280512140d41c800f800c0d1a51112145500c00a600402618031920f6082408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 426186636 1250 426185386 426185407
    0xf090512010e01140c07060e07150206160c0b01060518060c01020c060f01030203120d0908030a0c020c1f11070e04080a090f0510030513020301060b04050109080303160c17 75
    0x10841c41c4144100802404c142050f40c243c01d8442501c010000c0c038014800103006c12141e90002d213507001800121014941c0d0350f02c03510141908003142e5000358202c80700304005803030619a070020500491030000b405000c151744034040fa2a045c0944420400c0c04183c20100ae0394204810b0105000105000d03280c000c258201c9020b54011034424072140070b8000825415001c852103141600d034024050070058207a802456800e421400780410302d00d07110011040411280c0e002180515001e15011446080c1c0d4000a0b00c1c00070480c80490041d03403c0c85965030300134100c0c0d000101901580c81d080145000c80150340340703040751642143c41c0000090040c40100042940280341e031031070035151035003460b0b522000102201890b00c2a250485450182141058402d600c40c0758040700c0c41102c000b00c00040c1d004203007122030039001301d0000840010180000d68001010000401d420300013586503242c07849030641445d580601850a009140081a00700000c0100d8030450702d1001203031684501980700d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 426187886 1250 426186636 426186641
    0x60c18080706090608090c0d020616050109031d0a0e1513050906070f080f04080c061e16020c0d02031e07061412042301061409070206040309060f09051201 68
    0x10410003c00c2e0700b00e0000608a0090014900c280960030281c0020400c805c20700860505c9035200302d82c80f0804008200c48503074200161580907010324000207414016140c0030f003100906840d4048588203200491055540b03001c102000e035105501c900201d03869140011801d0021018644d5200d003000305a5600745950381e000310301c0b8401a004480c05500d843d9020341d1188092020000010ba80200090b038444600d04240d8205210b81600d610b0610702c008150308004040d50700c0e030700588181d5000e0200c0342c03004136815001490800240a103040898020b5550244050f101340521285040c1505654091100c1c46141020760610602c141000001503100d040b58050103010a00301091406480400001e94810902d800c051441580305c0b911400c035030b03c004800c504503005080d41c015603403c0c4203010303030700c0140001104100100d042e1020070960300001000c0764210742c440410440420380c41011032048403498100380807030801984040b00c00302d4003a00000d8005a81c0001d81e4070040c01503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 426189136 1250 426187886 426187889
    0x10e120d1104030803341806050306060405041d010e060f24010518060a120b04020309190804050d030e04050a0b0307180209031501080f010207050307060c180807 71
    0x580c003002000e400004040c400c1c007950202030294070051001071480c038404103900d00e00c0c40b95130654041c105108407403003400c6001911040b0025261003c501545141c95032400060171040c20000d0440c901355000c964076000b1441a28030a5445d0083c00f5500c0c2418403100010854440080c00ba525400070207568844050390304e01d0004c1300c2500040c8c0c00c104c00004500d28848180704100380040031000446090b002040043e1b030004040e144400140c1e5424002c289078065038a41c14600d10321030100b001100d9180707510074081e034010030400862801c0400c400544082c001c0040301160307900c0c144099280034903048181c009111500e00c4042c19000180070544845c200da091080b1742c1d03040c0c09802500c85a05003207070103501c5000305008031559031314902c8125688010040c00c0164510020380b81c1100140c0550a42c810900140003d01c010b008802412030b03590700075882d08255a07103d60f9688104500501000c3e0fa6008112141d403007240401c014412429181040c0fa40b540d1580d80c030b40405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 426190386 1250 426189136 426189157
    0x90b0306090a0201080726040c08010614031908040803040e06040c030b03061603090501110c0c0306010b0301140d0609030e030c010c08120901061a04030c06090308090f03010e12 78
    0x2140001110000001185040b055060703443c1495a00d030040144d40ca61008003800541c1c101c044400440312a0350310400b84124010281c0542c5140b40c0039649003103c00d0354001e80580600851019000c2d01d00040344440c68000c50700320031800b07000d410125414022600311800741e0100207000a8056408420395000d410f0840c0c0820002d40403000a908440a405600d40c0507000f00700002c20341c5ca0390550b06090b846583c100401d00d01840e6541c20308454541c01c61528000340070030308400e455070400038007880b00001c0c1c0042000f5410031183c81141e000500c02e143c80441c00204900d455103070941e02155043d4445010b00c900c9081d0f14002c1d20a506440300c8601a11540603207030005d40c86000c2e4154590f41085d0b6a82c41e000b40ea0800e2038204c1c02c0140620358079904c84030b00041c0101008080281c00040c14a682d03201ca0640c6800a50f50b6429400802080320b540010f201041e5a4801ca880e036140c01c43e0310070020014900840d024003401e030481402d5016180c0741c0342400c004040103040c800341c2e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 426191636 1250 426190386 426190393
    0x7080406031109130b010e0d0302071a0301030b150112050c07021807050d0b1c03080106030507031514460b0a0c050c100f0e0a061409060f04090b03 65
    0x5502c007904220701074400100d5001e04c4c81c00c1c00c8a080485a80200301800040c036110543e582c4040100e9200049044110010fa21284003040300b005a61112003028a446160700d02d594519116980b0320070024000c0c070b082c3c4100c1c400c8009640e02440d080320320140c0c0301c1d005220510309200040e00b283c0200b0400e90213100002d0312081c507100300d0030402e44581c419072251400c02040c20201002803603101c02080d000002d0b844034140b1034403038031002180e4a01c203651b40b03031180d070500700300a040d150041c20403420f03d0f0610b202c0402c104881d10455040d03071000e00407000c0110b6507000240079202c42c000240f500982e2490103025107207040c9007004c43c401c1c3e0b40303103038640720000b008114868403500d215981201c5014040710321401e10a0754800e00c41e0f40035008072291505d0010000e807a480715481c61001266070ba500c041509504005112948041110051121450040c024190156108407c0110f100005104900750360308010b49145080c501d003007607152a00c2c4e8614400a01220724218401e12 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 426192886 1250 426191636 426191651
    0x810030215091002010e060a0207060e0708010603031806021b0d060f0501090e0316020d02060f0c011b0305060d020411120103050d140a1205070302040512060114010203090607080a03110708040603 86
    0x207005008401d1506d50142c001d0034141c1c1d901829800035046844110f581c3e6132a01d270070f403020b1101007003001c2c0a0103c440000940030b240d440c0c083c04100203000c184060140300c1e002040000c1e00171902d90f12420040270b241d0480f07058140000c80c0c00414541c0113109500c1c1c2680300b0494603280d400341d41a0ba110050400010b0b60340302d201c0e907590003407c0d00d0007030441321191074100505203140386181403803003d04018141281190b81c0a5607401a502e60f00c030507951504070f500b08011588580440c007095050810041c03c240d00811040180b803400a4080c907101c00c121703681407004030210b0705c010387c4860140381c0a50b12403070002c0d00c4840f00701400e0300141800c071001d803916204008403030318114142c03100c618807620391440f600600710007881e090901d9401d0000040703a0b00c88052107601300d800000a41465810180384108021000d206141158800d00c00a0b100c0e80f03403242241c18640e00945000c1e240d02c0ca5510481c040d000c80d056480014002044150403c9050406002580c0c2d507520280803d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 426194136 1250 426192886 426192919
    0x20105090709090b01090e010e031602010e0d030509120316080c01060605090a0915050a0306021e0306060f0702040e0a121106071e17010b270907081003021509 70
    0x2070f001444050802d07101c810040107100c1850344002c0d07140850200116818085164003401d54010706580c00c03620710181d141c0400c5683c04013500e10302600454407040004ca807034800508602400c031a490162006d0455110a00f00420544a84112401d213400c040700051030803040a40010340980b14546c200301c0007040450140d42a5400180f000d045a00c83c14980f0055034007400425180000020319280c010030991188102640954052840586d960407548500d0074a912004050350401c2400d00510540e541c503032080755004440d0410940d1200b6650001400400303040c0307107080c0180704000e884020401100130320b590001040d10740340094000e42c0307182900c840c02110f1040000e1b045855500c908440070140d03c55218551a00756056a56030341f84020801017a003011202d01408a840b4215907272542400c04801c0d00310046585424440010820207a0042c1901d0140900348000805610709050300f000116002051703650020301846550b813441c0d00c010407450164580d5454401903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 426195386 1250 426194136 426194141
    0x2041404050a0803040f0b070c1104050705040b071103010c180609260f0706051806130b091f03060603060803031603020a110109050303012108030714070210020105090709 75
    0xca411801420002120790742d580329580c03000340b04448644007003201902294250b90114420b03450341d06c500d4080142410a420603e51030200c1c02d100741c0c100810010030702d030b10005940848a88048032905c400d200d240400b103040100400319007540c600714000c001d0580c000300d041c00801c0000140313886107840d40011942160301b8007404101441407502004950031304501000c05034031a005440c0b810403100c1e051400c014155003c03000091020600409542c0a01c88448c014541200c08074a00100a07600d042042594440c0c0e100713101010400240c20385885107848414030008440480402e80402c2c0940140000d002d2500060f141000121300b515000003104e0041e00c0310440440c00710140305084010394409c80c041000c00400081c1c107104420f0034061903007454850340103961a0f40c1010f40c00c042c1004000e02c1c0003020309400a4140c00300e50054122900840c15182844041410b100c088a6901c91018001c3d00541290070400070954191b01c82e6015411000c00d80701016a80d5050a0a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 426196636 1250 426195386 426195391
    0x509040e16080a1e0c030b04050a02010246080f030f070309030c1b151707050313120306030b0414010506061c050414010606021b190e06040902031603020414 69
    0x4401500d186000d892641900e207213544140c1101d280d09480355103014510320140c400701c507030b03510180c0305008668042c41803039a20035500e1500c0d06090050481d8041e0071016403038404040070003c0f520704820180c1c01c50042d005801c50151981c90710150307500b8109d6441120350710741142c0744c20701040700705209020312940b0716010340c0c411801d54100d03125000c84040c0705009848410041e0800245440c00a00351301059031961a8100c00d01c000c525201a145802414441003020802c1001034001800c882003183c1e5401c15402880041c1d03410044d0010f000c3d580001c2d20b0100d8010400040148003d400c04034540c1840080c84540c469000740501c90140800040b06054181c0c00f0b05481c0146600440d030003030080c403d07030010000200c2c985e070840340f1540104d13005800990700da00515400a40085e03c0c488140e64011110035602810003200000c0e0040c4548403910302c0100d0340560b625080601480d80090548079281d80703661150801c2d03101c074841240228281032660006d40c01c402045407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 426197886 1250 426196636 426196643
    0x4030c0b03150a05180604060e0910061406030705130e042f0a05040f061502010e210d0f0207060e06060a060c0c0501050a0212161e1505070509040e16080a 68
    0x103424074804499017000d81c4010101c4e03800c50b51300d020002d1064480d030181800303000b600b406014058142d8441c541912055007000311548810040f80742d19460301803c80390300c1a2107103070864541d0000c1290f00d614003401e074400d0780102a02c40a000500130030348045200c00c040c0358800c8201380c01e0b02c80e511070b820800500075075020311180c2082000d400c02d034201900d500c500941c0081d40680311042c141881c00c200140c240181c0d500c4001518025042094506245100102d406080000e60707504840740715140c01d0f0103004e51101e5035809580c082d6010b450305142c2c403100034800340046e00070160380c2e01401c0360614410a400040050228040c40308041010f40001060382218140001900d2a40c0094451341c114441c451195100c0d40c000b80140561905c010400b950011841c00d0186c80c940c1d04000840801050a0030b4100080c00d40e65490a000e4441c540402d041da00c10501b5101b50041c152425000b80c10300001600700b00012980c08a040303043c0c7d101c82c480545506d00700b035440e0341900c0000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 426199136 1250 426197886 426197899
    0x1e05010305161409061c0e010b031906021b0a0f0606050109050310050c040e040f02040b101b17040905010e090d050403031425020111010c020706080402030304030c0b03150a05 77
    0x10f00384103480010200c4c0c5102624203841d00c0c04e10440000a140e16001c2c0012031552001c114401c41d40a005505030b00d00c040300280704280940d001013a0b003102c032031030040c100c41d400100c200000141800c00300f403040024080d5800c4110038285a54024040a400c40d034040c9081000700780d40d03018030a410181c650141c0140f0348403061040d404014100a4000548002d0a000000340100d104c0180c0c1d20552140c003103400242d0b214814030040da1040c1100c944502a006045c4010540c0402c90b43d5034480214240d400040007410300302c440490311103401380b1703004002401080d25001508440d040342d8030b0203000b40b1203554481e007141e12514005088030000e5401c00041011a220b6407102c801400d81e040c5c01490449085909604502006025454040442141800c0d0340e0004884e84000010070024001031406a000030740700da00c1406844240400c0d1408903095480c1041a1400b4685c01544094040e807a44101800c54100316002c403100540a01c0a403107034203154000104440c3d014009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 426200386 1250 426199136 426199157
    0x1518180a0b0a080304030f080903061003060c03050402060d05070c1209030308060a05060a050c032b05060a03050c0d0602251b060807031a04050f100e06030304030209040201091e0501030516 83
    0x16144c0c070304181f000540345404288400c0c40e4940d0300b8040b0601442c42502c811500b207185141907001d40b604004d210b414180341134100300250b1280e404407251409400c0001036250f0300c0071410380700380b00e11120191201c04040e60b14002c040e005021075095074041d840d5080241c0d2180c0c02c0083c0c9200a000f25070300028107100d0a5459401440900f08058040d410350f400d00980440382900034810b11101d080310a400102c038000110301d481a583c00c00c406070780c002c48140c1143c4030a80d650141201c2c0c140a0955040b000301030000c00c0d0f05481e100402819561040c601d460b175641c004201100080d200703510006840b251440301c1001c41004c0f54030a44520510340c0d00c0c0350041d0b0007040e0040bc240d015070301108804c40660b070785120769486551010002c0e403150802892800365a02560000083e41c40071605100d1195000130694013101e6041f01c2c6112b0039683c3e032004850a0142c0c1d0b10944900c070201e20801070350604981510180c45c001c0c0d80c20002681d0b10301c1c544508014800103100419401c2c0c12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 426201636 1250 426200386 426200393
    0x190614040207030908100c0f020105060d021509060c0c090915220501020c0d080a0c02061909020a08010603151a010f090f090203160c021518180a0b0a08030403 70
    0x1c2c00314540241440001a955070180340c0c18000c0c0120013800071591000021950360b0004000d030452500d40c80200407500c3c05402281e42420a0b050107445041c031000703c0241e145949040b20740303040d00a0040341d11444042403503a039811f49001003030300c50389030030740081d1100d48000360801d41d00007038076180d42e0b41e921285038014400c42c540c1c449000d0b9502d210404404a6000d00044c01e0025141008190440004c0c0c4001d04804018001900803810440960f1510398001601c680003c04910401122211560303480000e10310400c00a4001c0d0308030000013143c02c0c06620001c200c80c0115250540344400d1300c1c41c607003210304c582140b0341c3c00300100b41d450000307501c24000d03079072072040c5410421101381c0c40308070a00c0e00c160503a020348207090300041005503010050202051a236550f00b000040f840003540042d4909000c0002c00400d18004102949102043c1c4859010500d0280c070306071100540700d00103481814210b440342112800c003030145c40c1505094140004480c1990007540c1024107555 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 426202886 1250 426201636 426201641
    0xd0b0c0c070911091011030a08100807080f0601050d0b01091a06030a0c12020307230f030106050405091311040209010201021312031101020a050d0c032319061404 71
    0x248001241d1184440100d118800d6200356803000540004041d210340310b1804020303204200007030744030410020b017820b41400c5c0c0c4004123a0b060480e060401c2d980d165038454400608106507072011403d4840c1000000750810007044210780180e001081d02c010340c0c5c813041480001c1f0101c2100505400142004010060305a030103446c000250050241052124200140c1141c10a44200008903500c6210545403504141440070b92065103400f58194500448080c002c0f140d1440302d980350340c2c541c408a01071403400008942014000c1200c10740c5a50b1614402000798000c0d0084500510504010400b50041c82c0300303040e003150f0301c0741001d4503106484003070001075004007880c1410b6640900c0f00030100320303444901501420600d43c1403100ca084504001780400e44004100715180d10412400d1240ea510404a4040035918000460200c451f12404c030014841505441281c24035241e0304591403540320a464020440f40c00400c94086007204c002040725868031411815207103174001c1124074101758 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 426204136 1250 426202886 426202897
    0x606010c02010f12050414210301050d0c08010203160e06070c06050f0702090f072a080306010917070609060e1c060213180f050c0702120705131a0d0b0c 67
    0x10301e01068040e9810341c3c050180c42041c1e60481d49890040d007c0c4044940406c6280000801c2c0100c0720151102c1003000c0c000c0b44818003565001c0c903007a030b1a50091141c06801a0014804040215030341d1400c6d0898050710410500d14200003000c44040354410314003841528042c0b50001111512036140c030005452661124034100b4142105001c82e0001d42d031184181c40c80390f80d00790102d091525040c04004c00e10560502900b00e02c91184040724100041c00b500c0795050f07980116141d40c4c0703454140040c1c038a40390560240b1403000300d5002c440a00d40f40440c0d802d08a80342d81d00d81d41481030700c80d0404c0c1c600201496425801c010040d070810706030b070720600b282c07e0b195000301c10041c034024060020340040541600f180940110300007041d40b000030640f003000d49900c081e90703040100c2e05012030240c0310345c0303d00040a4455680d074102d4404c0494148404c0f002808003e1002e428000140540c0e0701500c08502c1090031510401051641410308030113036081c003035001003264071603626080d803448941c010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 426205386 1250 426204136 426204167
    0x120b031006080304091d1902010c0c03050d0f0201020307020309040504061104120c0f0b030726070903020a0e010b07020d030e130501080624060c0f0d090e090606010c0201 75
    0xd22118004000e03203482500d001d032034400040c56440c1d05200c011000d072103082c1d140103228806144140c0d900d100100d00300c4500c0e02a100408440c03011800102c2e241c06407410081c20b1264807807800010010005260030b00400181c81d04c080c500804401070f07080b804206c6d040070250300304200d007008502d01640a0703a4880e01c101d400040015134843e17804601c0d0480d801401012420107412418452030300d2100d0002d140554800c60180e04102c928521800060041814403c0d0420054141e100c1c1695503440c0410141d152400c5203080403000304800d820384803da01404d01c8020120b85407007680005070507190105000d614043c0340380d0034400c040185070b809030108031225144030103951302d060103188080c079180c01c08a900c0d41030070145c03801d120024000c04846d002000265011303841000e48c0c0e001521048841c7c649a8807148800750400d008408451114000c060b01d0503111908415100195181402d444000740d41e045a9540e07201015a043c82c0484ea1184550006605c140c46a1624440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 426206636 1250 426205386 426205393
    0x5040b18030d02030702030c120403020d0602070809032d24070507050d0306150e0d06110702041107030207050312220e090a1e0308220b0f0601080f0106120b03 70
    0x600714242d4126002998150300503040068840c0300000100140120b003c541800589450300c0d40d40040e92062503036000070289034020407407006104501d0281c0c0c110410142c160b07501401c0d031608004d120000380c640e58940c040804407000590340005100402c0f0043c0c06800d0902d03c2d6030000d92050b0754801404181000010460000050400e10240140c1d020503180800d501e4203005205540c101c2007203c0c10b04101d244040390446540d041d4040c221a0b80201e00021840074044203001c080c85100710186d0400c0c00e0020500c01c05100b00000c05601e8000d6094a103640d880d402010b894201c06204007022a40900c010106e08881e0300103440e2100d91000800f408076039850a08191840485645401c0c0d08000c4200d03003488001b0440c100030088030408074284010380c2e40c018250600c09407a582c03d0810510507041004040d5800200d216001011403c01c0c0c682000308189922080352101e0000d080d032004250507000400352107041e6091500c44001e100b0030514a000203084d02c07019143e0520 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 426207886 1250 426206636 426206647
    0x901020702060c01060e1b0a080417042304140c132304060b0c0d030e070b040b0c010b04091110020a0213020a09140d080d0b04060e041505040b1803 65
    0x2d41d10700060a40355103040021a0184c500b12819181000003407101c0c100e10b0b070050000f8140c584420444000520318103151074191034074100600788104008101d03507884000180400c0d041704450040f00311840e914500107815031520240401d80b50341d95001100a00c0320b80106030400c4042003d00019190510b42d9203003a580d4859001004440400030461802501003440850516004000151005100786450801481c0740c3ea90303190240b940410403d9611403c500c81c0641c2407040b080100312900c0050f403110344903551546035a0000e070320645a50701c0c0c205258050309041c003890951541003090308851a480c10f0038001c0c402c00b1510008110b0180300b40000059451001001c0c80c0945000b00503210031100070081c5c0308031100e40206c82001c0c8190ba40404541c0c400d050056040d51148489880d80c1e01c1d024044050800300c440c80c1e13480740c202500419112040e00d42c0134800c6010310307071070f248481120301144102e65081d0303000f500d1301c0240760000340d99160912040300e82e400c0c40c00c101da1822 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 426209136 1250 426207886 426207889
    0xf260a1a040f0206030103030807030b0a0f180603050708030c07080106081902030c04060b03070f0c050a02060f0d051302091f0b0906070602180f0306010b040e070c080706091518020402030901020702 87
    0x345e0098204401266801c001d1100036607061180088a60003035515090342c41c00c0c4002c001d8081d0a500c9007803240120180d40c082e0610341c0d83c0050004540c0003007120305840d1a951016241c1d041a0a0720880d1700c90304400003041c0d1b10502170311046840c80000703450084041c88000c54841645001613815108105081c44151154854513004000d1400b1454603030622090041c56010302c000e80e4410030040385110b0020640100b80603401941c101d0349107130b44a890390001d420358060050f80c804000d103070004210130517002850507c401d500c02c41c1c220405613181254102003494607640d084080307200c000c0a1005d0606040102030f8081c00138101c6007850050b030760ba030050b0f034000003407540071801d0080c1901c2d45060044c410060304408402800315581002c442440340d0150740f040c80141407000011400d002c0c0503000c4d84c0c04080e042080c85a0700d007031905224021b01850002120140e1003c11030803008041c40c030406505256192540c0000400c0d030f000c10000e5000500400f2455508210b800f006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 426210386 1250 426209136 426209149
    0x30f11030709030303050603030a02070915080d0504050102070b1810030204120c030b060a0510030506012016080c0d06020d3903050c1b070f260a1a040f02 68
    0xc0d4000340da4040605040d4139000b000c0d9a000341c402c9000354421720030105240d4021070340d0000c0e240ca4110019800220721110203091080354054140303800f40c85401030700d09902000030170642d40c00380c00300d52015581ba4200301d01ca20980785000007210a0101c0c03140300d4a08041100c1110075140b03030150604e902c0c1d100100030a2800f50044174182880c10b820010800d10040c46c0350701010444503082d40310729003c00300b1018501401e03140c0405a0b035200007800b581c014010030000d224280006044441140a1540e8400c185601285158850603000030042c4002036070494955024080007402c0c00141c0e41d96000e50058a28070404907100e40504010700d440300b0509040502140c440359030000404610100110359110340b0003050304020400205d5031070390048540c2e901042e840c0000c030b0103407611001c1c200452608102034100844800107040010304100e04a1243d18420500c0030b0001418800d82d40c010301c07100108004030b0711130030f201c00b010142c98043c0d119004d40f1609001d02032580c0000c2c103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 426211636 1250 426210386 426210391
    0x9050d0212011d011109060906070c0902070303020a080a0c050921030708070c0803130509130210020303160c0b0f10121505070c0b0a02090f040f141f06030f1103 71
    0x14200c0c0c400030508121001d010b410008a07550f11260f06d4220010301058080c400d90000a001d5000000d02c6400c200408000d04010a444041103440f10114507005001c0e600c020a0100000d4013040424460800791141d07003003850250b2201c5103464001410b1041c0ca5a95003005e00b1261110381000c03000030f2040c0010038000e4804e2800aa460010f860039455070000c542107100994814021a25400b4028902109031001210011800d668552001000b801c03070305e8000350000c44034081d5040380c0e6000406140207070400d140b1403901103c0c3e60f01c11103e802220f90090074150081021414500010200f250001005017040f0000e50301c804e101c1c0c001d0a0700503411140b5115076546890355110b1882900c3c1c2142d918071340211107140f15125082d000d9405061002c42c5c2e0380c0001c207050707103582c0c48511111001d400f80003442070f030107000b0081009006045c1a00040c00c80040003614100c900755140380325083d11110400320505140085009040e002000c152140d40d0b0380c09500d0285c0103501552 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 426212886 1250 426211636 426211661
    0x130f06080a110909070f1a0c01150f050f06031801090f05030c0c01050f0702010e01180b09040b0301090f1407032012030f040303081909140613020109050d021201 71
    0x41c1c0398042c030b200303102d08010000d150541c0c64014900501c0840904c61902080340c0a0005090f41019a504211180c0c03142c8038030454250710f099424000800031111840c1201d041c0e419004042c0d60f20400c0c884c400e02c00cbd00800b60302c540704000184034641e500d806081c0141c446800011000d03001c4d0340700350003800801c4003501c29078000b180342c010701c080030408070b140704801b86005800c128050284104600031000c0003410310080304a00b1507607902c03401c60884580c1500041845103a40c40c59412500d5000885c89801241003402140d05400c050080146c42c66001203020000c580c283c440c0c10103200155170b142c80b40d0203005000000f080d521184030300703c9004804640000f102540400c19044401924424282c209000e200c40c404c0e03001050300c4c1107a406080034841175075448480c1341d1124642100283c3c0914245002080c4100305007820241100c1d241210303035546071200907100140d40c2c02802400140380450621180c104039040b101b01c1132010b0902034640c84009402801e44680341a0b04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 426214136 1250 426212886 426212903
    0xf07022b0515010602070b03010605071a10061404051807020703050a06020a02010b09010e01060509060403080c0102070b010618062d0e0a0915260102070308180c130f06080a 76
    0x1200d070700401c007031450f005200600041040500c4c16019034a280030521494051000116900090042d10200c00079540c00c1c2c481c50100070700d4400c080c800544414006d0000044143d50b24090074650401120265200104100c403002c04000e54809003031002803d200860141680010010b1020040c105040d440b80c14090b0301c4180e2a4802030843e11000e41e0240300e40e11200040114664200256040d20482e180c201c4d0341c0c500910224100c0c1c4110361004001003800903c0540ca05410b41c045c3c01d900c1d1045203c01000e90741e92320210782d0402c038410202044040a90b04110244c0542d003040401d5002454201c582c50803810010122441009040041002000c4240701d600d8032020481c080d2400500c100494071071120780810070b40190240a030003644402c2c440c1c039181c1150303403083d155103089002995207a81c0b61a004021a4007914039100d00141a8015200c4c060041013941100790003801000b80b2031409081c0c00c1c06428044079481c3c20070383e035120119100200340254079615010b070606 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 426215386 1250 426214136 426214153
    0x18050307031202150f01140d02010e100c0b1f0b0708090405072f0706180e040c080a03050a030513020d1b08010612050f0c150c1c0c060f020f07022b05 66
    0xb0816000140307c250f100d420107800281c0141c0e0490095100a1002c2e1440710708a1100403050301c58429001018041192580c100274101c04254034054203599400c84185440d60744410712a040e000700e90000302840c0041c031021406040c00d41c0101e601a610f03240c9040242040011280c0c07400d460001b4501c0b402590051310015241007020741c0080c8000d00d0300c41e21151080007840c603a0b2a240c0918000d200410340031409024820328004090b1a525054031400201c80c40d006e0007030351090786100042810f020000e050302c800c204012601c11b4010b4840c2c0c10002c0300b6607840010340141000b0850001020b84040398107182489404041c0900f141d00c02d06040003410058500902006000850307441340759a40c00b103844015031000c100702c0c6c03a10318030b44452141242d2402c1401d420740e5a00c010b58080080c0501a43c400b124141c2c06024880401c1081250000319003a1320580c24907140c035813810040c00c001402c009144801c2020815400e004482a0040d00d942c8203500f01c07000c0da80ca0340900d51 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 426216636 1250 426215386 426215399
    0x411060d0f0c0e1806040209150c070b1611010309060f0603051203040f031409040c03050106181a09030715091d070905011202090d1218050307031202150f01 69
    0x1442584101d9410302419a09651000804013070710354080010070400c080100d03400b0388664041c1c91180f80c004003042c1c81b40c003080c24155100c1c0c0140c5000700f1144900e4200240000c03000c0101d0b0354821101003030f0060303110103444820001c000c800e8a103041640c3d544144c808201d4a2080e0410001c0466010a0651550900760b10f003246248140810103c10414040010f50580c1d81c260003580c14148100d0101d8003415218850092003102c1d034109040031000c66405500d544503c0c140c40f401c0d01c0f212400030404030805007514450203040e2a40945600560700800c0010251180250081c120351415889110000840100840b400003003041c1c04800e10494001c545e100245160800082caa24502440c008040c2c03450b51060720705200700c0c4500502c610225070110744010002a180d6070b20382500b03262081e0f039805444500f10000c1d007842400070122003011030080c111078004004155a900307684074031400c1203d032104c0c07109510504003d003414940b0340c0c80303040c0f040c3c9030310003820756640c500036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 426217886 1250 426216636 426216641
    0xd050a050a1b0906150c1a010305010f0e0105040209040201030b0a1d090d0c050706030b0f0d0302150a09020307150309050609010b190608042003030c06150904050a08030411060d0f 79
    0xc1010b21103509285041c0112180d05100711782c144018503000c40403c10318103050400d0111082880040d806500000c42442815003104c003035201c1440c4100205007903210024204c460a80f0001c3d400085440410302640c4290004500c1d0100181036118560352110851402169074103489101c0e00781d0b104002141c1c00074031003100c0b41c082d24100400b10b094a69910340c0c880000c2d00a8509041d614122400703039440d600306407a80f182014005003407015440c00e02039600c010101c00c0052500006000864520301030241144069014000704021414900e101d81002150940001010740d1409644045001004502e0061890900004801c002882030203401140b400420f03400180740c1e80c0030001c107580280d80640c400d40200e07801d0f6020f4540c107010801c1d00522070400e81c0c94480426641c43e0403101080c110f0240c00c0003500d10310040081428030002540842d8050300c550002242040450082002194441d02c940c042116112241000070700641084101080807a0ba82486038071842d540e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 426219136 1250 426217886 426217889
    0x40803060d0618030c1e020604090e070b04030b1504061508060402091008090705060f03010b0a0e0405070207090609090b0c0c1606200c090c18030106060c0c06110c0d050a050a1b 78
    0xc2c511b0406c08046402084107481980320710740d0b4091341c03080961160b020600001c40608102c03c1c0443d582c0d0ba480c20540440c280640e8140d0101d410302040e8070307031450148540012118101551892400001c0050342c2e140c82c024252500143c08000c129075030355925840702800380c00d81d1168581d90401c6003440340b51100c1c2e070708202d01450302080308140b4103081d901943e0440f50b0075002c240d0764201e0700c81304441c6a11038113640d41c3c01900340410b001c0440e802082003001d0340c4200008018041d6030f07100002c1a82d03600c070780203046d0381e80c503002180342141c0d48001012208070840880c8c00d001126502030406d410035501500002e291003d60010b00c450b01400060020b040c40010402c408554000604e0b8803406019030b4100701001501c44c080c42c4403607410f40c40e0800000c00030004981e0b80c02001e00452000c0380219240c2c0c103400d5020030400c0c01110450001203282c40108044034144081c8400407203510400c0d6400d1144d85001000160108012400780b44124079a42c0d908811000d2903001109030f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 426220386 1250 426219136 426219173
    0x90706080702151f090b12070f090b0a12050715020d0905060903010e030408060106021c050406030f06080d031b1407061a09070f0f08040803060d0618030c 68
    0x82050180c07403540054108030305100d43c807141030300b51150840305400d00ba80741c2038070400c0c40300c1640002e04405154010303010004255041010500d41c1074000d0345800d11070040b81500c4100c1c0307000b4490f090240d4000d5014a5000d444204203582f0f03040c55440c25030349080100c440d40c1c0018024071034510f15600402c4050601e00090142100c2040041c111085070b0150038042c000c04602035102e42d40940101443e002c45c007090302e0390b96440303400c081d44483d400d00a40c0054440c140075522040e000fa0f80ca0a10310507035960301030620303050600071005408081c42200542d41c40c1e03100814a86001c3c0021544800a6100003c112441100400e20740440056076800d100c02d000351080e020b40000101c61703465900c148001650201c00044007010032400d94000d41181241c1c0c2048417158106d841c000c88904d540d102e60b180222440700482e8a505c0c1190010321a0308103002141c840d0030300c003010180d001c1c40362602148039541d07071303075083e030545e981e04001da00062500d0b21103418071411403a91441d40b1030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 426221636 1250 426220386 426220397
    0x3030f020f09011103160b060a0602060136020c0c04060806100302040e0312090a0b0a0501050a03030309050703171c021908070c0b0106050a03142a070804030605090706 74
    0x640c0e03001c07052a0196101c22410b0003000e005060004500b0b10448659500c0d41000300c2404401d400e051041c5501200d04601609000c04042051400050b10504880744001c0c0c0c000e01d18800c0380280812502c0b05100b0344c0f01e4a002c46000170080322400501402e00c0100001c0000b034130540204002d4603882d80c13280c41c858214906011401d0a10302008050300d4050350701040e10740351169a00d00e54450003e07554514090301c8284150707038001140300d05015018482100c03c94407075101000c125a028032a0301c0e401050942e0410010b4040d82004034594000c20545003060f0f0781c3d480c4e2460300341c060295601c0380c0000141c020492580c1840d003020000071003208600301074080007070442d050b07000c60b03440c024000d800700000c0b000c621904c0344920184d0302c0000c0c5801c5595881c0d02500c0c80d00403140203c00302c2d003400010050124030030302d481d101c1c45c1901e861034414040d90348074900054245804003c144400c03c66040419240c40c010f00041d407092100285515103d0015030400884d07402480c02c202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 426222886 1250 426221636 426221647
    0x6050d150305060a0902060d051005010f05131a12010605040807140303030c1c14060a050f010e04020a030b120c270f070903060509010e06070c1a07030e100903030f02 73
    0x41d4002800e40d40034071a0341300002d01c84854000500180110102801c205003000108070310481c01c1039010342120b10a80310320b00b80641c1008103039020b0045c803152944d14010900c00f0881d40c009101c501491964000b0308078640a828105002003c009070022004a0380000301004168401c205280c024500b40c0500000c3d03038542000241c80707120241c0b03100140c10f400f0070b008203203e40e41c03102c2005c60301081c1010010030308280c0341c0704400501150164462100e00c84000754030704000540b1800403105070355031000ba80801e000c01000350040b02c00d0800701039a8607010306881d101c40b070606e54804981320060284000c030200300045107203c001040641c1401c0c4203e0001443d6400c600c582004108c0c0000d846580c445408581d1880640d00240601d070815060054401c011b5000e11540c51150003a50510390721007030195070344100020014842015444a03001c0c0d02c961f0301001d50010349604d008100c0301003041d01103150001040c00107004694640d04c00040580500c03c4004041c1403400660519 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 426224136 1250 426222886 426222893
    0x90a02040807290a080601080606030408032e0b030406060b0f070f080906030403030f060510020c06030603010b10021006050a120308040501060b04080705042003161806050d1503 78
    0x154018841d43c002040042548400c2ca1640c0002c910000c074140c0010382c81d40e0740030000134040306040d5421404100000d001c036810f41407050403640f0481d0440440d0b480d6450f02d100340300105040c114a89401e031030741c1c06404403000502d41084010446003c81944904050500358200c0d40107a010b4080c4500402c405c0242042401c25200d02580200b90160400c0450070048040c0c400c010602ea80320740c0010401040640503440340080c010740d200c0c10811988c503442030000c010142002403000d40d10540706424580b50210013150b20240c0500045911413640c000704109071515121b0714050381101048800c521a0b62007a140144000c54101e1200d5151030100030346800541c03405420865a8000901440402d401000091072089009995655501d80c456140c0103e0b0082901c00c034245003900d1554144035040505030160014610720319140d202440c9601516980901c05120440441c95143e81d002c5101c82d0040900e03840f41c0355904801500d5104403502c800121074400c45400d01400030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 426225386 1250 426224136 426224143
    0x60c03071505040314130b0307120b030606030712080c0a030f0f031a011103090a080c0a0f03020a0b1b01020d0f0e0f060a050a110d0e060c0f0a05030a020702040c0e090a020408 77
    0x44407022445079a886d00440c40d01c01c181c207075400140b1003031000020f00005644c000c528181c0d91200b6501009a8104c50080540b82e00083c0c416640c1035000d1001030240c8241c3c8001c1d40c0c10320388200c00b02c3e031902401080b11801c0c980101c10030b802181000005200c055000701020029445502c2c00300002d1142c40311408103500c01c01401030400c00402981c0501e1003040044600c0d200c0300800c01104699141d24150360f032543c1e0300d0f150703002d100707045400240300c0560740021050740d0340141914142070404042c44003e0b040702740d5001c10306081c1514607001308428801084460100c10300410640d1003c079614040c0c1d0700c50070710107440c2d41c4000c1e01c1d043e07040f070003007a195088200180b0124003622000c3c1e882c00508416402815841c00c006507180d00005c00790310a14a2a51403000d0741c906540d9424020700a001d903500500302c440003042061001c40c4107c0040da800301c01c0b40c000504200c1d80c0d40218040724460342c0403101144a01c0c1c01d8256902c0e043da10264410081542135142c2070410015545 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 426226636 1250 426225386 426225407
    0xf1c060209091e0c070c080a0b040302010f0c08181207080304050601050f010206060f040e0f0105010314120f030613050c03040501051b09010815030f06161e120b060c030715050403 79
    0x70344e86000c03e040701089010780c0c1080081581070115010007045082c131204559007501c00324055071030006103203040c0b2294082c075070340f498158990b0151903803081e0140d007401c02d050a00d4800c40c010700821840384842500505900b0340240700da1501c916203450720500d4800182c0002d4403c040d094204a0141c2c0d0015074640d02100c1650346400281c545404a4040c1c641c80e0028001400f9284809807090307015403029040300e0149143d031030020013560f04140c4444034010503a6502c0d00400580156a02e614011030300145d001d0210492041c1c2052020111030060fa10b0b961651000002c1c002480750900079642c010007892000040380142004259503440b44000140c180311002d40012a01c60700b0740410304a83e1000f405540395042c4e00595191210411120081d00045460040035010b114050203076205248001301c0401456101c0151000085040e5040c1d200781c540c42030081c50b48450707014000d510701c000c0003552610280e180440c5010500301e42e611020345080100b1010a03445107a40c003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 426227886 1250 426226636 426226651
    0x115090b090402070f1e1a07080f040309050603070c14062211040f020309060c0c07090518070b0a021504051c02030c072318060f1c060209091e 63
    0x16695601171900d00404121654041c002c1442040190605201b003452400b030360744104111070300507135090805590100300351181000260030000103100301e00b00e0000d042d0440d000e828442c050954400c0020002c1e401180c0c100001083c3c0c2c103009003005120400700c246110b0342405440a844d00d01502c5502c0f0703d400380c40301c04a00c0e03414002024409901e10310422004013410030f1108814440b42c1d6000380d4425101c0300501d200303180014a14003214002c0e101140e0700c1d08040c05100b0324000109001d090301920841003961542031900a000040180c01c00424901000300d89400c400c01010341401d541e6941e443c402c1800c1010040018000302d402e801d0081c2c0780210500b0100c0c1c1c1e0030220701e10f000321410340140f03201d201c0012640c001c40c2c41c00c8000c07806800020b0030800020200703011451103519841303c2c00f01080340100722681750181034032510590142052103480801c1c0d10740c072200040b440d820f80b07000b68002003036001c0b41408602160b10446507040e84403115000f543c1a4103910005040c007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 426229136 1250 426227886 426227891
    0x10b09120312151203030a151203020319030e03030a05180f070510051b0a060f0c0203030a0b0f0409060b09010b0703020319051c0e010e010c020d110a080a02060115090b0904 76
    0x24402a982d00d1542110b13500c40408507034617481c064110f072004000d140003660b584100c41c0d5001a0745190940004084da41c035602443c00e12040f00403550302201c0c042213007030030b01d621010101d040540400c0079501c50001d90790042080c1c100000c00400c034455001e034401c40d80d00038041c0300e40546000100030041300c0d000e031855500c9103142d4004440b9402105010008000d41282c586010440014140c0445000e00010010100e030101e1481c1164401020200035130024000155030705044e03484610703603400242c490601d403400e040000d800c4803a110400c0b90081d0340d401c040034690418050490240c039034258240c1c03030582c254801941d00c0c0201c3c02d10130440c43c4d07124100b2102038841e40543d148503800c120018841a41c1500c2440a00340c007a400b405958a403691145101105004030510b1003840d40261202003a00c02c0100c6204000e07005881462103860745040c005003080000f402d01d1300c2c056014007000d5061141c5002c00b10204420301c400c0150361541403148420007c00c4424504049900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 426230386 1250 426229136 426229171
    0x130503010c141b031303030306090513020d0201120c0521010302150f091c0501181502250f02240a1209023109110108040f0506010b09120312 62
    0x681c920040701c406200c10307408045581c0b200305e00b44000c11030540348252400d00000e503e0702ca4a00441e202110141d681c42103450111002d0f080840c4000040fa0040c909500c08280b40250300c001c0d01e41c0140300780d001130380c0001d84120520760410001c220030f03030302c40e445902d55256800054104003045c090340280c2c480000c00c152100186012940030460103454880c00c511100e4030344000034a10766007600e00e1350804d44158079081f01c0c0b500145070164009166100241695902ca00942211443e0721141c8150f034013003000c021140c01006038082c441e00313044480c200144180400e003014032085601070000e034184c41e9040e1100109a60700c1ca4030310b18140c03c80d003685030710101c05001d880e035010350042449040c0010703071058002400e0742417010020121001c1107000310782c4100c07090040f0142c0b80c0c807400c0c2d210040940c451242036400c18058080e00c10602070507110385050032002c4e40510301c4a4000681d41590742040615400d0460080c0091800c1510800c1d422a1059000b0300d050000e00041e800c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 426231636 1250 426230386 426230407
    0x9022e050f12061f03020301061716050c07090f0c02011409030304060c09231509010c0b0406110f1804022a030d06121703060d030e15030c130503010c14 67
    0x2010380000c034034000d540350411340030b80000d0020f5000380145800200742c0c030102c41c059282e8009003030246480104842c4030805802c2c00301c0302c03900690040b0b103003402040d0300010350034024000c0b21420b02d1800c0001458600440c0c0217401c554104652002c07203100366041090b00750000c400d481c0e01a8020501140390031034924115030b0b034801c0e500320301c01c001d6030381d1908079251a40d40028608507000380c03442c00e40021030034a59821340c05000d1003c0d0010314034191032000521302c018081d41086c8522000314155800401c90351543c1c000b00300c245ca17501c0001c224950764010000c880131400c442030340c0c01c501d01400180d500fa02e122019800c1e0714032408031401001d20180c104204d80900200ba0800c101d400c0c1c6500c201c151009950744242d43c0c103074054881c9220207a83c1001c50340201d00051a50200c1581e41d0380a8400038644130046501090046209510341e0110b40111f100d081c41410b21950b8102c004007000c0100030a030007207400f80c2c0c50044a003000a4002c0910541281e546403400c1e00c9a00050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 426232886 1250 426231636 426231649
    0x15060f240302161209060e150c0c030715020d230a18060c02030c10021c020c0a03030504051201060302011d042304020108090d080103030309030309022e050f1206 71
    0x144040d0350040e1025003c800d200d41c1203440c0410a58694640320303c0c4e0381d194030854a074041820100d5100d05000c90000c0c3c59072601c1c0007410101720b900150f41c50704c01c840c4000780c282074180c0e0000c03222982035880c908580343d0510290200307503510308048070807411488c2425249a0741151180340100c5c001041d90425000f0300c5003444584200d29040400f60325008020142e490310702049000c1d109006070403040f80b0b03001d00c0f0754038039003010b81c014401d401c1c841d241138903100522208102580034034070302d03c219511403414407005503000740c4a0a5641e458001403090360781c010210701c41507914011003400141e0740207222004480e00c60110903041c920543c0007500400c44642d04034920740d1403901c02d01150a5074684c8910460013621240156600c4c0d41d000d94032142c41d0308560300040e610b07000510000b80a035004020236030107480c0029050200e036011070230414100c120020114088801541c20300d4842c5541d04088034181340c00c4e4203044581d40408140c0c010740800045400c103a00005095440e02d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 426234136 1250 426232886 426232897
    0x80f0a150207021f032a0c0201050c1b012706081806040b09010b0307060c030813080d0b030705040e070308031f06050a0f030b030a02040e12040315060f240302 70
    0x242188503144204400b1880c03510400c00d1030303012a01b032800d00b00764421241045140c11042c00c003441013030810301c94101d0f144a20724404a040c4136091044400c3d00c4010000307800050034801011011030500800506200d843c0384110000c1007030700460000300c1d40e8402c01d00d07084401d0340c03d243c50316884111113802107040302d5415000c81d1095500704024001301c502a00d0041c40e022000f0400c001c260401c2c59101e00704c40c040d4401080340025203c0c00a40b0540c600d40e13115810041303540010b241a03a0314000d40e40324140f410b0b01a40c41e900401c00a29040c4109001408100d0f0100040c0034419280d41e1990100c3c4405050040b0110025019001148607207040183d00c4d2000d2155503220440980190461015000017402032955002c0f5203009100725000d06034028014410002d41d40d0170040a05001408410140110301204c47d4941112001c0c1c0060340c1705540a42110ba0601107250032103130a41d000d205188032041c0700f000f4020072540c8100392030740c0c900d100800450b00810305a010f803090 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 426235386 1250 426234136 426234139
    0xa080d0e130f0204031106030603030301030b060d0807030c0506010902250501020d020406020706090905060a2607060906120203101703120a140906070e06070201110304090510080f0a15020702 84
    0x10b0280030842601540d004000340c13441051314409104005082c803055001c12202e6a4142e84100014008100f0007642c199208000418041d0140301940e144521074001d208110041000001c3c500204201408110702600d90100700718101102e81140d2522528604d81c40c44080c0340c000b0707840003030180c290122982c407289400203650307803990b41900039030328243e51140000281810b0400300300e48885010740350042b00000c00d551420390401c18802c8038801084040840000042e081c4080e402e4140f04100081c8802e440d0003080030303d000e001501d55180e00388c6d0400768a02c10002c100c0c0040703d00d0002015201400f41c180075401c100e45100d49140305801c036440d10b0301043c2c41000081b005640208140e0034000d45501601d0f242c27101d12940c9c40000b581c0b0b030b8010666880d0550014100b030005000030500500d0940503102414a0b2182140c0c4103401151703240352200c080003c101c146180717450081107890020b0011220f61001261140c90030b0a00800b20202c26139820050f08030381d01550f4440781c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 426236636 1250 426235386 426235391
    0x120d0507021e062d181b010f050a0314070203030105030f19030c15050c1306051608030a06090e010b03160315050a0204080d090602060108030a0c080a0c150203010303030b0a080d0e13 80
    0x180b80100c09086411100d0000c000d20075043c100340f801542850300044103c6c103840c0c007403502e20302ca00c06072010742090170700d202055130360024540d0410710100b089000754502c0d000b40d952541048181802e00e00c201c00c20508560041030100e00303070030702d4122041c156901407801644101c41b42c6403000c84201401c1a403052107051009004c0a40c2c04200182500700c0c0c2c40454044c40d0340e41c2c5405603801d0144410304a5044014101080440c02160013941d0100d4042c20001c4c2c0303203456004000840b034520017803250a0399038003481c0c200c0d41410800d907868454821100d401c031514564502d0f03401145010750070002d944036404102a00c4d0a5016900588171000980b903c1d40701520000b40105000c0c8201c00c0140715071000098010310101c103c8070030300042d9442c3c1d4502c4140e61225051580041d08060401400250a0001c40c1007600e1001d1358082c0507101580d69459810002d0a40c1d0500130442e10a034281d20041140001c000f0305100079082038103000400f522400000388000a026029039100e60 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 426237886 1250 426236636 426236641
    0x30b040201110312014403091509040e060c030c090a050a061106160f03181b03050f010c0c0312090c0b25020d080c120d0507021e062d 59
    0x21032140c8441e06950b0650b41502a2080708246d0702e88200a003090103024044c0c81c8820701030403249610300141811444100da20b0701c16080003084500b600400144248800844c6450007843c19002e13003521540e0020061006040c00e441007401803102070300090754650700160090143d158a5000d40082c4030050845000c2d654400001e0850300c610140400e01d800391800181e4106a851584002414660fa61110500400005500901c0c0c2c40c0c504aa42c0c82c0d61045410000307910484500b444541004469241443c514020380360494118a4035402d07414140040d52640c0d024007240c080c203030145400d600c2044070410313580007440c0002000c3d050a81ca09030114001034110700501c0a01c4200070040c440d4403817443d80b241e404070030042c02503000031007100380c40c01f0071101006007102c211072401343c9118400101e076482c3c031544203501340c44441d80c07500c040210450f0180200c280b0100103a420142c3d01440711001c42d2101001840e1030703005203c0358804030124203030000d030000700794000005040d00d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 426239136 1250 426237886 426237907
    0x30c03040f0506040803070f021519060807090c0f09050906040504020f030607110c0a0b030406051e190e01020a121a061215010c0804031e1e060c18030b0402011103 72
    0x3584111004400300e230b1801c1482c004c1c903100141c40744828170700034418511600c4601c0320908143c5081e4140d0841a294000852a11018440da5000f0320b0400c5001403000701c2d80d64060001d6600074030030024000d9402040010303880307800310355605c00011200010300f5502c910000e18020058030200f5054400d5404001c0b905800c1100801d4540804080340c6516aa02c02088815242405003a80d4060240007040015070306400c0b00d81c2055440680703004900070501d201011100485280d08112078013604031101007814032a0031080602d95000b9883e103406180c015001360a0300300004078041d40d600003000e444000b014042d02c454070040405955141d06a080480039000350b40751082c0d03401c22415806158021303210079001071345c440e046a0903e450742e11010801c10400300306608a05a1100101c0092108080807a00300310902d0a100c0d1071001e41480e10882d10b4000c8048140101100d601000d6680384642d40200c90b4400d024050607625440100d640440c103800f50003041c030020800d1880d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 426240386 1250 426239136 426239153
    0x6030f06050103020108091612050106050d0c0f0b0406020a02100201061e170a0203061303090e04200303090a1a0702090103050d0f050f09090907051905030c15030c03040f050604 78
    0x103d038000d0340c0f60101620740208280d11801100904115400825001c0149004540c2c181ea2200d01030000012200e980d10041882c070f044030001100c0344038403003405102680003000c0d01c0c400361002d4803416040c10304044000c0c0d0f0792440000040d12074114a1000d1200078401d4028002401701402111900b5200200c4542c0800c00c50141e4800c203002d25000e80003a4900150302c1c90b00c503130000c00814058035403403504104420441415010054403682c0480c0141054148600462084005200b501c050200310064261030a650b503100e40c1040250a94580e01c1340303c0314040d03421b032855281030460300c1c0310760000d6880389071f070001e400400c03440000044c00004114090094441c2d20340003043e60034460201d440b071140b12180d03401408103000511f9a42050310b0340d00d500085000494200d1503ea100088020313446c6020070300301196081d000e003d00e081c1403029000c41c0409440c06030805580c40c010b04214080245098040c000110000e001e020f00384a0400c91160013100751a0b8a0410b41022400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 426241636 1250 426240386 426240389
    0x41b050c10020f07020d060b0409081206010f02071a0c07030317010b0a0c0b0901230117030c03030103060c21060e06010c0c05120a1e02011e020309011206030f060501 73
    0x1580500c0e949828581e00a00885003214140106249815615406c00c641d07160409000c2d900c07503a031a0034003151501c851049444042c003800304c0c9034482c1c00c140c2c07006221503401000207040001c1d4000c4600c03459000107001d01603420380101d0700803800c1301c4a56011320f4010004ca1811500c11010000103045d003000c82c2c88503140041030700300b140b80e07210b0380304104038402c0504640001c1c107554500c1c004952207003101900b020561001140c01192540e9094004d00d84126280064038100c0c01040710b0b4441038031100d5070200c00c001840c1019080040982c03280014807002d02040d486201191101c0d00c19480c07003010101e00d800c0e09187c00c410180d488010401c90060210002d03409011681640c00303918080222030f030048250303a0890801e018404a42c20101c00704ea00e03441050010310001c0e005104010443c3c1e602c810703401da6206607000041280a2000b00c004209a0a000c11180d85902004403a0740c1c403c20300f07006800b5400707190103070700a0902d40d00140610030002200302c20004150030560 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 426242886 1250 426241636 426241657
    0x5280b0415050a0206060f060403050105040c0504060603090b0408070201110607020726030a0f0306050607050c0306060402210709090f1d01060605070f020414330915041b05 76
    0x40750900c02405880e144140801d07280940c0c0b1a0780041c0709458021540310110030060000c5041135039954802d070070350302c040d101210381c103180f00c81c188558205031003410000e0680f45814403244032039440b00003403000c0152000d02040c00c0000c040c400d41e40a05803061201400508546130b519107808000c0d10707035142c2c0c001c1c82450340a01c541e513890b801c1144440410a8603c82c0654504140268203440a1400c10020802e25448010000da1a0307520005031025500a0010b40b00c0302020b00f00305810510001c0c0810703c0b0324810302c4880d040001e44448070040e400001072003851522080d04c10340d00100280e01004080c0d0420524000c0b590b016080304840c404c0140500c1c043c080240d0040b8243c800c1402141d00007401031022b0000326a50894050a00340080c100040b4a144c072207008550150842d002c161300190f0110079240c820150f40304000e210303400b0007071003031013440300000480d605800342075102018000c048502584c0c4e0385900c04008000d000104980b104d6a440313001e0850340040704c0c1034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 426244136 1250 426242886 426242909
    0x20303041b0302010509040f1401141f0c140307080f121005010f0528030209130b0303040b07020111010e0c030705010305010e01050d031e0c0c0b1305280b04 69
    0x210510700240020505a0b0341c1615198141900c80c414400140451004a00c1c0f0700e0701d45850f03010511400d01c03414080c020040f0242c50505a0310188103441d40745141c100408050215aa40c190f54031100c40c00361180d11640c00d9408080e0000414a54040c008014000711000502c2181010030781000740b140c4501034a020505682d03068039814080c10620940340855890300011000742c0c40b45000304070441e00202d0751f0340b00303c60361070034401d0060700300901c00d020950008104180d03207000f184102e000d4a004000744010381d0920f01207601c9008074496800c1201c0042440400c581c00760081e9403049801400801120850403151b07540c0f802101d039114040e008000700800d0a5200740a46030603111400c01e110708691a0030306000c2c9080600c2d100354204410420400c90082041c94006100301c8203595001d42d410003810041c91070380c0c2a0340000160001040440302c140600c80b03d0306c045890489040f40c1d2102000d80307050303958031065018510031060110200f4680c00c031354041d00c282d0b074400c1c0700d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 426245386 1250 426244136 426244163
    0xf050a0806041205210c070b060616031202090405040b0601030c020307051c0509090a051014370b04080c0406061b0c031a04060f0c050403020105071e0302030304 71
    0x305403985820765002d0401110894070018a90040c0c004002c0d100c400460240d07408282130715035030001030603183c90600b40301c00a105c00038081082c2e00c581d007140c1c01300d60041c54418511060b410310641c085008051080707609010001030380d80d605a402000c8050000e02942ca0945042850100704407510782c082464004245503007813000085d240c030964014010240503465200030155000d011001c42c007000401c001c0d601d170540b12030303a141d402038260342d01c046594248460044442e0a40c2c1e00a80b048003825a0704000d00d9503843c05401d10103002c56180d800d25407482c0b6070f17500c000301944440700b20182003901c0040c1c0751103140010411152428281c8030000350341c808210550398244100e200103000c5150a5000107808025a14004d11410b035844a09503640e0f1a200007241c9580d00c1e0140c00000300c1000103121490103042007a46011000300218940f5041c00340c90303405207000180c100038022818104101850181080c0c0f44020b66003010240341d40d10380250340398000c40f02181c481a07150f54 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 426246636 1250 426245386 426245399
    0x80616032a2304091104050301021303060501050609090c0a140f041805040b070f0c05100e1011041401020a0204022208030702240904240f050a0303110a0506010f050a 73
    0xc1201c00d05055141e03240b400d0302d050044c8010341240702c549010f026041100003110b603400d200400c5800103100760070000e40d20b582072940032070340e050348100e010340b20030094901c3c2d694960443c103600402007070031561200490388c01210a135150110451b401d07000000e4820b030045480b0094421502c030090b0364851110741180a5003503560544004100100c0c120105800e00e0140c01d40704450401890000c01c030f01d001d030300c03490b01e00320620003400b20342582c0d0500c0711031000b0144507414100302c180341c05004128001c0c0c4a0503062040703201d10707012605c840300790030066842403140d4084240c0040c001d64850400310903929150f0381143e040c0290b03103102e03800003840f00808003e03a213840303800400341d546960b4020714180000c0f10801c4210195502008a0705030340e50b451140691540c0c410701036070000a482031514012070025042502981d42c404410003a0703036502140d14050380c2d85407402c0002c03039100b004018649a0010401007190185000110351000d10741130b644c048550860b010a03240d13035940c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 426247886 1250 426246636 426246677
    0x30601170c040905121c0f1a010c030801031b030b040c152a03210603020f040608060103110607051c030f0203010503031209100608010209040b03010501080616032a 72
    0x480040154002d0000c00c12082c2c40305d80034260000c6174142141900b41e80000361003c075000300c2c41b14001e550361200f0790451800c4801d95090921002e080c1151440c03015100540310b514144170082110321440d403040c07214000e41c15220020340d80050080040c1c00d00c0c0c40d08146284c1b5070b0003100c2a81c400807041d958818841c942c1d40440c02c0101d030190480d01c0a2403807180300c043d420181502071100361400e1621600c50041c94040100f0840310000c2c58600314410441d40741d00000d07003248078606002e01801050004202070381140d521000095070001a007010070014000c4130380152160050200725051500d40030788954624145940c2041091800c540b0b2508900080c00b815030194820711036824282034030b00006400490f41000ca903035400c00c0300c98203400c2e940f154204400300d1b5004140760026060502a500d0062822002070042d581003940c00d036a1090010300310020f1488456424250354000c1d4001407840c8060a8454004032040348455940d6844132509800070300407580031141e10704141e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 426249136 1250 426247886 426247901
    0x50c04051942030902101d04020c0c060d110a090608012702030603010e030a1d0d050a030804060f050c0c10151e0902070b040b241e030601170c04 64
    0x101141c96129082c04541409804040c4981c051655a5007010b000d80d031910411400d00d141580c600d50b240748507803040001c4079000055140550f00600000f138181c0404941c030743e0700000c260b81c010f1301c0e61242901140030388010030541c2168040000c064a280d540195164191081da0312904451303640e4031068480030740c03d0b803580c84655180d60202d4000148940085411141c0100046041010f00f8200c074110390040d803440d03020a909502440c0e2800440b03010f5414044200c900c00303104411912220b40300e2609400003403c0000400015081205135401103d505a48003403c11440c942003c0d040c8040c6e00001844d541486050250703171101c5070078051401a490861481c0d403e0500d01305100c0380c071107203062450000810300d460108045c417461025251541c001c101d144060306007810910003a803000351911001140d50412128540c6e200440c0d048100390175100703206c03000b02d1200451094450003820316490301840c8000200f140c90304900c078041030f04e14010740d00e20305042e208200845040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 426250386 1250 426249136 426249209
    0xa080a030206150f040b012007090b03010b15030c0f030403080121171e1602010306050d0816020f040c020f06060d03080a110906030709181e050c040519 67
    0xe51380c4456414540c21450345c65806040c42403100c4040e2241020051200001039015846a442040700354004c2c01021000e480a400820080d403d07003001c00c0301d1910305404c00c85107441c0000403031120039408c0d0403034048980b40d007001034890401c1d140003003412100b842507221110541540380000075050710314240740c0d9071000310451480e5151070115025080520099401444041500d210504120040281c060022110300c070030303002880090304980d000e41225018107044644031b00090000b0007228055014001c0032822900c0c0f5100107141c902d4401b0025810a0420800c9181103400080071703004524820306850700369a80c0c00900090311407450010700000c0c010400729601e640340e17a11145064840c4124039140c05a600b020600395401500c2c40b50010b84112810855059941c070a100c01440740d5106200c144c442550800043c401a00b01007441c5c0e64400211700403600010442d0000e20000d042c04400441181010b05e1180e854441c2c00389000c04001400710180360950201c500b410bc = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 426251636 1250 426250386 426250399
    0x60809061303021903021c0302120f040606090c030507030609020903070611030d090302060103031806080a15050307060e090f3c0c030702100525020c0a080a03020615 73
    0x607030300c2024941c1c00044500b94158007411514000e518001c00d59510b00b2030180e0000d0261522907040e100311130a040c80c005080610611101c0c02c2401103072800d81e080070380c140e5445540d484e9424920001c0c610355214000851074086c3c24907005406030806442040180c8080103d199a074101105030710440a2541e403507084030a09003e104e0149a4050780c40701032108807810031545000c0d90041328180d942c250003680c8100b004004140c0d02c888070465a00c9104003098403c3d00e02034020300b448101030260480c281c3c9500c06403d0031282d44034490008d200050440320400e54a4002070142125000140c4c080d00e03009002841a606420003907009510b01d514443e01081d0302c084000c07a00b00004542c0d00d040002c03000da40c00c508442035001e40284034070354140343d803810503100113841c01b1426940b000c0d80c68181001c010248810105003005030b98990644160002014012810700c1c2d402d11b581d9902c03019540000c1400311000650041c0d00d4404d40803107100740c8450301c8080c40000303e82c00c41c81c0e0040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 426252886 1250 426251636 426251641
    0x106030b06040216020a091e0605030d0507060e060708101406030406090203030d05040b150405270c03060a06030519320105041208130c0b0f090d0501050403030606080906 75
    0x341039001303010540e03082c040311804152590014444054552040340f2290721218503100c4500c0441040003134600090040010601d0400484d81381c0003140a100d0521a01044900a11045405c2040e15084080540701c032440c244001a140240640d0071010a010102011540007002d030394407500120020710340c07400c503541c0303aa5000103400038500c100d0b05400103010a60304005039014442c061441107140c01603d241c080c8003208050b1503078107800e228500300800d0117071a00d522103110b07002d203800c0740611890541d48012146405400600103426203e4101000084c244550003002541d00c902d0030ba501d415120303410b21241c1d0034840006000810400035900801031042c034091580c4a001d248811041220b00c1a41e003158000c07074056407503000c1c1c442c0e10304100f507204607a0759200c00c1130380141c580c00d4510b40f540c8207450014002c0079890000080c034140e10209000c1665460f244c01884069038a1342850170034040c2c40152030031400300e070603c2c5000c59414001c0000360b00c50034070b41000f05001d2303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 426254136 1250 426252886 426252889
    0x25170309010c32180303030106030203041a0112021005040f030804090f0c1b0303060e0106080a05070918150506130326250b0c0a1101020c03191b0606050906030106030b06 75
    0x1380c0c0488500d104e0300c066a03910103405c0c0c030144080c1d40201a02d07280140c40307152506054030042036580894440d00c034100010300030202042c0114040d2078054030000f100d501810b2040d03c1074030540d0401000c0750595100001000354010052040d12100202030201e601d000380c8081c280c602005c8030300007180b0302501c045108008114442e811502915010451942c0c071040160a0300d0282c010f100003038028420040b0700e40c140c3c00b600d50420503900d0315689091a00d01c504080f01c070b0311454401070703d480354618484524542c0c0440041c02c030007045035641d60408007031240300c500b0510049955410520051002510140d100710041c400e0608240c81e200d5900382d01c1a100001540603800b0043c0407089030b02248800942a2162100345900382d52103da02601030009140680ca980b40e076801013000c1010f0180102c2036411b010445890106040c21805082c1c68040c902c920b09800811031621000c103005194002c001141c90a031490b030103503111001407509842c65404064484440640480c016 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 426255386 1250 426254136 426254237
    0x30901080c070303060b1801020d0804030504090b030709180b0a090f0b09010f1e0b1c08030601110d0c020a0510022d03040815010b25170309010c 64
    0x24911910300000c2c810745031b00f0401c2c4241c0000281b40510301a100300c00e031007540c04100c07008001d0000d080c002c0d860b04d45960014039078880e07805040461030b00c6c0c40340c6e0030050300c2c10040f44004e082d42c007005001c40d80781130303050701c080d104200b1003900c3c42c40811000ca03800070214801d60003055049004019481055150358803c0740b0081c00b07480c825035a8100c9080550103920a4107000120b0500c00381092040d100700c4400d0740e40415110b88100040112400e0030484151018103255114800c181c6a40d1140c00503610303113565003080e002600401c0d0104010607404522190101e1007140d0028603107840f081442008a00740c034440c405640321480815a04440301d50081d40520748a4150000a400e507100c00e04541080c1e2000d0b449a1115800c0302034030ba0100916400340c01d4032002182894400c0484580070400f0384900404609208400310a009804201405c101b21080c10700d079890409106042c0280720b15544000001e80e60343c0c81c074505503180864904403040d411105c0d000c2120b90500f8001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 426256636 1250 426255386 426255397
    0xb061204020d0c09050f0103030807090b160501060b0a0c060501150c0f2306010e090a03020a170d060311030d02120a180905010f08010506010e010c1509051b030c03030901080c 77
    0x4002048820001d00d0130361390700900d842010600112101545075207000760884030090170b001c0c10700054580c180035030018001518800c03800d02108615888581c14254010300300381c0c1101e001040000b41c05220650401c0035444014410b980820044e079072851580520000c150303001000502c0004001d0110354039501075040703c0c1c0500c0800703c0f1148003034548030b910b030320100b00564180c00c842e00410030103a007109515072102c0a031015205031005650002e40321a500705009040a0400443d610501c4002061b034021110b40c0b07404002c40d50320f81c24031181800c02070440328802c0c450b180000c551f061000c02c000d0045121010040d0403c0c0604009495403000341d0038900300079203c602c000800f00800d020707150003000c240c10309114103400d0421090a448002340b0150502005d0100104543d900441c0442090b40001240f050000451984c001034000c0d500058141c1c86040d08902030004040901408a01d0442c00c036003d03070111a09240e00d9000c0c000809021481410002c0c848001c0c1600415 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 426257886 1250 426256636 426256643
    0x5010c05070b0c0d02160f06210606030b190e062202030a0207020a12020a0b032e0603060f0b07110627010e0402181309050709020703030b061204020d 66
    0x60225884550b07804142c0c001d050016001d80c01081000c0702c594051100b2010980042200074645040c600108550782c0c00c3e104800401862504074a070000074411001d40881c502c081c14070440355241001800b0704030a0248038440c0040e1ba07542808584c80d000941c0c212000d00c031f40a1203d0303894000700031100070400d0400405842c10014a41c14103c2d43c802144940f02e81280140c44040b00d0041c010709440c3c5c4d03000040d00c00c069410321000b60303541c10804030031142e8030b00c0890303940c0d41e410f000711544190b658580052004012041901260b417050490280c0c0d169076070401c01c3e5030351610020411143ca10403041c9403041001004042042990304d426030020107401c1c0b43c030b410f011001a120030040c4070010440c280d4503001c040820340c0d0100421030b848000706d40075820f0455000c0a07242c810040d40312725100302000b508114040c000e6420604d0311070742002c140d80c2c83d2585c559540c0d01079480034404a0000c5e282c05d507410028075051041e1062072800707001c2c2040a030344950a00070f0010390740300e068 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 426258992 1106 426257886 426257893
    0xb1801180b06040203061f020d0206060105071a060604051306142205090c0d1421041505040e070509030d020f0a110a0305010c1115010e0105010c05 65
    0x142e801880884005030349031106400035071102d02e010104181c050000f82e410b5019600461810380c410304075000e440c0e0a68502e80111040c0c0b284807001400c481c1003160000c4410b0381c80c1600d540c0600c0140c1882d1509445000048500711040890625030361182014403105142074503144103608155508034040390096501e040390340e642100305c0c9503e0340e107000060016608000010b040880507103c2d107400c0840c0d040048040c001c03907583e007030f9510480f13200e0316081c0e81c2002c803122180320400095041600307040c2940600141e114210302000000c0c00081000c0506441c00d03406444152911555040c04000385820a002c44500700f007590001c031122030901c140882c215000d40d0b40990306c03080c91a0303000c1c00520350a480303410281056180c840b01d130030303001e80000b00080c80d6401c42c4100d600701e011083c6090413040e402d02526812508400040120754011140222480c3c841c1d01034 = true := by decide +kernel

theorem cover : BRFrame.Cov 426079136 426258992 := by
  have h0 := BRFrame.cov_init 426079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 426079136 ≤ n) (h2 : n < 426258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
