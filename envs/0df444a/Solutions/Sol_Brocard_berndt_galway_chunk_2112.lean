-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2112
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:40:27.503256+00:00
-- url     : https://prove2.me/submissions/fbc23f73-e236-4611-b0fe-ae14f472bc52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 379676258 ≤ n < 379856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 379677508 1250 379676258 379676273
    0x403050105060f0607050307030c031e200d08040f0503040e0406090b180c0f0315010b0301080c0306010b0702040515060318011a0f1c020a0b0406020f150705090d020904 74
    0x82000303e9421030754070040302c01c00189108030900105103420610040000900406111881d2442400c045924070b030703c40900c1032801583c01001000944040503021034610015841440d55001c03409010b0fa5901c07031308083c080c3d1002810051194808bc035800c0305119040c81954040c0180500319913003408e05040680c081c001702d50085d00e11080340400f082c2c02504000092801c29242001f4000f1a45241c2c100300c0d43d8604030a80b1905802200302480904041d40702e0307913010f4454002007549950600d02503606c1c0413010303503115000f607201c6030044c026110711000f540d1039641d0469000c6015035811a1019070110180e090a401c00030100500030f410032200240d0b900640000000c10048102d804240e5418102c1940c0e07680010031100940650700f000e40d84107000d00c001d102e804807800741682c0460001d0496038445002d28601080034080c00f07a0502a130170168280900825403220000e003c42c26007007024044505001d80083d803174103140c480d2803024018a4000703240b0302c0341d4035140c00c1c00c81 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 379678758 1250 379677508 379677511
    0x204180504050f070f170a0206040b0714071a0a0e10110c0102010b1804020a1805060f0102031e090406090603050102040e0c1602040f020c0f0d140a210605060403050105 74
    0x42d11401045075041003100c00054103030844400c1c80c0f19480741845c1c90302c03160041604001443d0540142c2120390090b03210000100003d1400016003079840d489824100780215039200c42c2c41ca0b58101001c1027003000e285061401c0040c00c0c0803c035954404c81a44256000c0c090b0700d04494125058000310300260743c1008030f502220944030140c5140b2400b00004900300c43d070803031055038003211030ba04039200406028001507205102804080c0110344403040704120050308440004456100e108120441c20b18007209403020343c081c00190304200030030480784142003590898280c0310b0400305401c456941c640d008140206100319041002e40e44a080c41c5002c0d40c01801907040280d1010007241c0303041e035110102c500c0300c40c60074160b05040080d80d0800000e01050600000c17035540134402110301000030f01948400302040002403100000c07649000e000c0200356855500d10210600c5160340d2160480450784006a144407a029285280032011004115540280b07410847c04035000c010000158030a030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 379680008 1250 379678758 379678763
    0x518040c080907150c14011503151503020102031204020a051201020c0c01020c2b0b0c090405010b031303030905030408060420060405010c081305091315050907060f030204180504 78
    0x15010b543d2500229041c5500513104d400029511145110100d005000034100d0065544000b00b1000070006000c030b1412070f1600140e0b00c16005147d20901003031a842141001442010300843c8545190000307900c0c0d000b00040c40c1000c0c440000010110354401780d50401400c1e00602c252108646000c034036000b900440399000c6a8842c4031403121440d80001a002c2e200c000040ca0011010880d000c0070f800d02980388201c4810301d034840d00c200e0021701c0c41c0040f940b00707801004e01c80707440d41102e0302000700f589c178107a00c0290f4034a010018000003e41c0380910b50307074541d0103040114005155160003440c602c2507511041d094020072f002c0c0f004101c2151000b001288801424200c0741e03000d001004414803a0f4400d6501042c031340074100001404c00009403680d0707203549000c041540d5540c4003240803100c0464000c0d480f401c0344441d40717082042e01800b001c01110075620400903450b1141e5851765504081c0105424800060b00404c1c10921070f4041343c01800c0340000b0307218000c200480c03501c040c10058504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 379681258 1250 379680008 379680013
    0x30102040803071b0302090c0a02010b100c060507140316020c10020c190609030311101a01030f0b090a180f060903170f010504021b030301080a02150a0c02010518040c0809 75
    0x44002541050000701306884e0000d1a000305034035000043c10320741c0d11260300603056548840e0050000d0b41ca00e03084180d01300e490b8070303202c8030710040d46010f0086620080c0f94800780850105150070000348041900d0f84007030351007006a100c0c1083c0100380d281070502080d06600a03a40c001c00c04d07045074042244540201d0a8440c071a0294090315154040030640c024400001d040b05810030200344124142c501290621003502e003110515041c1100f40c901d040d10021070705296040d002d406503414469003c0180f810b0a04110480328000042c82c40c8102030302e0085815100c00441c44400c8190080241c101d44c049100600c020700e074a00b040c0913000203e016404641c04840054513445007803c6a0b1107804056042c2d160b682c20003040000a4100400000c0202051322858140050400007140680014001080080c00e10310411041c1c005580071000250b00038410f440da0340350008110040c0340d509013451038a92001e60411700c4900c40081e17040d5405404c00346902009a0002090343c002d5428606 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 379682508 1250 379681258 379681283
    0x201060825060f05030a051003050607020f06060d1505040204060e090c13020f1209030c031324050d2a030504060c030b3f07060201180b01051e03010204080307 70
    0x2c0c240c1e21000c00b0415040414803c200007103491540780d11207035110483d04040d07a0a0f81d180e88640d0b180080441c0d030500942d20141840c1d200b00317002c002059025108940c4600c516046a44100965410090411516440780046811940c950f0865405071030440140c6000c0d203000c03602e0075516413046c10103078042c00a100c0c107004000e00070b000320b071645080602c1c00b6140400da000d110842c00c1000301505014002400000d82604d0240001d002030085009441c000ca42400c0504860b81100d211030600d1036040300c240f0700d0154101d400c0c0c8001040e00100001c900a0700303482121107613a00e40c0d07e001c6d403542200040d5000c64159020350b009a0040c00100401c548080c82a811a11801c40c11035010100c0058a440d4001800d00306403150340341c0d0801d0704240860701c0c85c041c107504c40c40700265007600301c040d05100041d4244254840c10740c0c840b15507100e0344055101c811030f180701030241074001e1401b80b0260340b080c805601006074007140038008655542d43c51800540b0b035000702c94100e90141d0883c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 379683758 1250 379682508 379682519
    0x2a051201050411030402060d0b10050406090e07140c010609110c010c11060a1d06070801030215040b190e12030406120506030606010813050105090d0801080610090c0201060825 77
    0x20580080702820f540f0a49035499980030001150000741007070040c162111a81407554070307240760303500120351591501070300e071824580c000c0c02158294111111550982c1c04000740c50354003081e4104003c1c00d0503195903452080c02151805400079411045185080203910b004c1040200d008040c0010360200810608080c040116015900c00055215030b92100002ca031300780701e456100b0600c8010515001015540d180203d03405e00b48211284c401041401004009505020203025003100b22014101d20341810228001e0140c010040705007440c01c040130f000542180106000310400b178005101c41c52460300010807a640c0d078842d00446000480104c000d110704c80c01802400d000720303001805400c25580b150011100e103d00104400b1107503c400000c940807035820720a030390045021101801000c4207000317000e014594181d002d000305070b2007d005c000c41e0326400d644520996503c0300c1e0100b04000600320490240215403c0300d43c00d40211151841070107000f60f038103001000250309441d5415a10b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 379685008 1250 379683758 379683761
    0x30b01151815020c040e01020c010e0a0807060b06090d0507170f03090402070f0f03050403120801080c0f03010204090f02091f0504060e2d03070f08070302042a0512010504 75
    0x4070300c0041100c503000414404205041145040507849104035603010190b00006000d4407604648400c05941c00164442030302e2007070140019410381d9000030070b41701c035159580244601c00c00f803010302800d0307aa00041070f241d03581808a918030070000380001c01d801054100303980c4403041d52252410680d0107002e10040844049891580d40d40c941c00654242021401484040e40c00100d0450380d4845007040a40010840090300580034000c0d82c0d150380310350075441c5c0602480076403543c5000341f196410042011b05400114001d030710400340d6000d601305036201d000c640a401181c11421455060510000120036940d0203030000004c200c911419441d40440071070100340e480454680021802c11007442040e006808040f20403101800c0c0c007050459031031103103520290640d0a82c000c0f285920003890b80c1e10b4100803c6014141c18030038855140d10301074649aa50a5a01c0020300490301c1d40709504d40c990f400321400080035004e04602c905c0d030440b0500245a03900040040040c14100c100225050509 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 379686258 1250 379685008 379685027
    0x306010e220f020d020c0a0302060a0b060912010902091311060c070509130c03060c12050907120303060e040308100b090306070302090d0c0b0c0106050d050a060b0118030b0115 77
    0x40a0280500980d59501d54007510b038010489864035001c00040b0032140c0280700030001b000d1564003810f00301c40d440c90f0080c01c050010704210300a500740781d000220355039460202c4510460459a1010080f00f0700c6001e4098100e02d1806540b1a00702d01c104144450801c403519580f911410105200e0010081001141d000b00c0c00c0030812540041030901403410407000158000c031403000c40c3c3c0785410300c5546a8456a089400450b0000d454096052109801c041003c010100d801010b11252600c4c4043d15900c800310f04c81e60480c52540c450700002e05000c1d5004c0c0000d0300718400c9c0e4650f18607140c1030241241600f6980d03d1200c2d0505880002c8064060b0305545680000901901880c7c0380d401085002c0c4d04203c9206500c00324402c402c0001a40713083d8071000500340c1c94069030300d890480507000e00312012940024094407084e4040307000140082252549603511101c0064940500401210f40201403642d00356043d0100e00c003c41032000c407569042c1200c650080e201c00c2410b100d5400c650200c107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 379687508 1250 379686258 379686289
    0xe1008160501081f141509010f030b0f0402041d090d1b060f0f0902270a0207080f0a080402040c11210d0204140907020d050f09010903020904080306010e 67
    0xd22201884150300c03465820750020035024101c604070908200c118204500c90b4025101498200300140700f42c141041c2d0902454180c00b045403c0220800010b0400c1420020701420180d0303c06111640d55540d540c3c00d030b594040507200315115a204c3d800c04c2150200c056110035107244c50300000303030705404c0004c0190f40b00c0c0c1107940301c01150802c0d402000603d0f1130440100c45113500e4031690181212a40b042864503101d1074804926a81c0ca4014031a0303503803030712039490944203050340d81001049011440d550050281600180e944c601800c000e081070250850017041850b000810210070b41c0d000c03007524002c5008942c100125801e41c04190340c402d124100401c0d068000d206801400348504030590f00840c10070000714608041c0c0413148007241d020381c0144103001d4040d1944403142c18045000e81d0b00011600040c4214200703090017802d180641d01c1c0780c0030007640c0024508074030392183c0d00d002d00640e4042c0074102c090400d85040c0380e1907001101d01500041c21500390425501d40890b04605004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 379688758 1250 379687508 379687543
    0x114011a03070e04050403020a033b040905030f0d0509030304170a0e150c1501080a02060a0e180603010c0c080d090501110403030c03120e0c060c10060e1008 69
    0x90349010121150304000c2c010014840d031407041005544660050500c560b12035405807442914502c1c1c041c0405020382c4400200d41c050014088403e03080c03522103904040082d000350000c140140001c0d001c0c18050070300520038000420040201c0360000b0281c4600300901000784100d0341c9039030f0505d42d2800102c4029219040c00c00720000010400c10080c0450041c40c54135611040c1c014001c0b9011154107040301441b00c0001840c1035582c4c000340306920717405980c0818140d503075150140c601d555180080d00a4402c0030005071040e905400340d06108039645000c1c003500007c1003501581c035011041200c03003e003e5400d0040311a80d5030301c079203120b00340c0300c2d8803801c250700300423501c0700ca03070000c1001ca1030881d0380359a507034800b01d040c0e000d07070f0b010348001c5100382c0d00c0032898415880d008040e04643d5090019107401e0103120041c4080115a040c4103040540b51540c9448060a00710300d4014002c5540443d1880d040c1c000c102c01c03c203050305600c6076503800e00e42e00c8119a01c41d00301e6030f640d54428440b40142e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 379690008 1250 379688758 379688789
    0x20706170f04110301060b0a1205090c120307050d0201060f0e040b04150603080705011d070e040303050403030b120a0209090d050d09081b0c1005161103030f0406030608011401 77
    0x2100105409402c14028040d10420f60703250b0001c2400c4030403d80000f8103454000c100014001c0c0e120446000e490300211040c0903501b4820000c942e2004c83c44550340c8110403640305010040020420340e5507807900401282c10081c0c039040042e0091046014141c1c104290740800714810540d100c41600469120300e2090140d40c0d90785400c900c404c0a017800103d0075440781c50001c04149000c000d84507143c00351000107104c0305c11840c00207103070100407011160f6410145c4200400c07098071174105c3c1d0140c0c06040218490390b8a2900318000e100039240e840e8000105100c400d1000c0c0000303403d408240c402ea80d50050703512096100e075681d000100c1d185001441c00c021060b44030105410150100e40304008990501410707001d0b00315030316241c4075039a409610146804c0c1252034440d807064600f002d9410554a80b11500c036040d00c68460401019041d01781100550146460070421183d007031f02e003024200c1d1166120003008029001c5489800361a600b081c00307810522400c024194100c034404240c85005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 379691258 1250 379690008 379690021
    0xe060f071107030804180b0102061617040b09071a0906090a0b070b091207031710050603090d09050301023609040f02010215040c051c0609050d02070617 67
    0x8405004000d041000002100807049007010880c0c60302451240026a85650902610600203e11844a418000d0911100c40c4181e600403807001d0b00100d0031203000345155030008003629601c03035100304281780640c0001000701340040781c7e141d43c0c051190b50055614459982c08075600b0140c0c100d0000380c0352030040141515515119005103d409400341076407020030394410b00c001d000e82014400381c078440d004004002c2c0c806418030060003500c1032071000a0501483c0c0d20000d000000c000d483e2440540044045008242c40c0e56101006140007405a07940703203003540301151250320808562022480c03100d004200c80c80c2c18001e030386011118030200b020305440c04006500344220303110000a024002030020400d034903801c10300d51045000d01c4684c2e00c0b040291000900d8503000813203142500c0d43c020107006c00202440202411144115510900e030034010a900e08502c41610005100a2824440408000010460407426090340e001e440b210360355a5000c0e5030302480082c40403407021259001801d0f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 379692508 1250 379691258 379691281
    0x3111c0b0414072d05030103050d0906020304050f06090406090c0e030609101d060405010209010801090b1e130212010504060b0408072709050c03010c030b0a0b07080715140a0e06 78
    0x3c0700c9180c41091305440c070151161090b81d458001681c00030f00b0020040c42403010420406400072510b02d0915006458800c0c02500e0b805140640c9208500021040c03031140c0d20b040684003001d100a0041180c60b03515900d08c0b00030400c01c180c200109030450189080c07841c000c03414502c03503a18840607002d281001c410040003040030a002000717066103e200b40303803030120800c80c0602c01c034410000140d4415501002611080d0164007858106080500203442601d4403600f81000d407596140f0490946614070002d50260b00c8143c041e1a464804528400c1c20994494031a049400030b580c204045d9803075000c0030b40c841c4102d010b00d1210760b0114504218103103224401036884e81011085800001c54200c01005480c00d070300381500c1c1035101d02c1780070500c1d14003032041c013441d60b840341400c0003081c20f00008102c0c10305241c8581180800d010483e030080c0f144450071503a016501c400e04115141801c5d03004401000d0720200480441400702c00100c95095511690140400c02c2005060315130b0790980d03090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 379693758 1250 379692508 379692527
    0xc010c12141801021207081f0b0715061806090c03060506030c07030e0a12050d0f0e0f0a0509090303090c030a2a0807090f050603010c1e03111c0b041407 67
    0x428030f42d8200900e02d1074109004810740110301c65035410506003407905011241040b4004030a4088815079820044000071030100c0307500a91140030900c220203061080d400801da0303580152202c0402c9990502240e03c80c1d0310110a90b8003059080080d42c0d17001324114200c070f806028164121500300041080000c80350301801e8064405c2c508039450030300410100701210000d03803021240b0003084d242042040024411561940d8032840d0204d1485440c1c600103045403840054075010721195005010340d40ca640540710060400a401210241418001e6517525441140c850342c0e10b0040d001450014507001c2144809030340c2241940380c0301c00e0324124040102519044081c1c90b19034008001594610600143d03000340900c5100098000d0b80300e5182090300c0000704030501c02d0345401c4101d01d04603002001a641d0b03e03200284100c25810140c01030b8003c0c00061550085810041100a003900701c50150811991184500b0700c0b800f440c52003800150307030030203401e000d03003101c01d40c0043e40f0184240c02c0d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 379695008 1250 379693758 379693801
    0xa0204140c0406120f06090207020405090f0c040f1803090f0e0402090f060d0f06050615040503030d0c020a2004140f060f18181c0801210204020c010c1214 68
    0x40c0e00c2685d502c9038800c6410300e0b4807a4041503001305201041d80f800c3e00c11346900c84070320300250101e4059032a84589074051030586900c40c0f650713261058100d1103140d01c52025412500b50a20040d0305504024001040078421847e407000d060402148102810180d24029a8054080d01e101d44440d9101e41c03071090010082c075040240043c5c0040402c02d0386840c001d00034011000002d00e81008400e02c1002c440c201c07200700d5245003c2104004e0303510004129604208030403c001140b4598071012400d00e650301002901c030345001c140c0c2c11510040c030100c0b03040481c3d04407403c0001e00b081d00e0000582a5080741c0b40c511117450b5400092003800d200d080310b0642080140380280a003610b8140c900490801d682c140c01103c0e024a04846c01401080337805c42444080c4405110b02e40d650b03c00429201e0140030310402e07600f00d91017400045010b81c41c5031089a0f4010002c1d901c0c3c80360301100e9802050400070324400541e40314214003500c0300034403640f0086a60042d030141c19941c5d110b9107000407078001490b03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 379696258 1250 379695008 379695011
    0xf120406050d0e032b0e0309060904060e0c0408010c08040807020909010213030c0302100804150903020c0607060e250b130305030a11010f0204240908010501080a0204140c040612 78
    0x70303201c1040a1000380300d004100302040d05c644074250401141d802c40340300d842101c070345040007520f20554000240c0b00c442c041115000d03a03581c0000c4c045800341c0010ba10451301254104288040035500801030015156410020480c0c1d81500000f2a82042c06079009031540c03104020410240c140061841c0d48a030302c01e0005807401d03610921009080c88542c0c02595004028030003401149040c0a081300b41b0303200d602d00b1824604103902c410f80061140c00003d0355640d42c0d0362410302050700074044a000303003500900554480b003450802d40043c1c680d03900101d8490040d0383e0001451a5510640d4001200e00d43c00c0304030484c03c0c695072a8070307a40030810100590811820000015000b000104000c0c502d0b940c8a20000c0120f07449142500c48070035503d68494010310080c04448010b26281c03640540c0d62803120000062440203442000c1541c01035030300f55081c00e0011a84040018101d0310144c400e0710100511101311100d180c07805c5040da0103203040d17082084100850b920480401003130032001c130300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 379697508 1250 379696258 379696271
    0x110c090406021e0d1a0405010509010b03040302010f1b0201050f0108031c090c152604030e011e180503010905030a031d01090302010b011d0d06050703020d05010b0c0f120406050d 78
    0x64a0f4141c126010700fa00094071040248007840e800013070012032400581c2d0500c02d550610740001d409840500881f0010341d40440080d0515100b5000040d49601458040003c20341c4c2d8110500d5041e01c09900002643c00c16001c25800400c0c1c14030103040300c0003180558245402d80078021010548a400d6400c03003901c40c00e120011407283d1400000400c0700c0b4000d4200d043c0c8a082c06803034003c10983c0207980c041c24020031540ca00d107141e4010b0340660b041c42c20124036180d030b20058404491150707482d58824525001d0103078494100d000b2a04800d00701c6500100036030740d20f00f0142600c1039a440108190818400b0700d00702802030b004004003911044400300b032040c907075000c20708403020201c055005079120318010903d5600102c03c0c2d41c070000c105201340c400030794910201e00380a01c0c0980c0100041c0d1380b840000c0c1c8040c40780e810386000019920041c0300d82d5070344001c1c219180e045883c0d2a0034a010f010084802800300207080c144001c0011151824145422030540f000c4d084a05881c00880d01c582d0f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 379698758 1250 379697508 379697557
    0x307170108100e160b03041703240301090206180604031a0f010f0528051e15072a03080d0213060e01050412110603070f110c09040602 59
    0x100d000e001490020215010300c1030703500068811255a581d101c0d00113081c14444800c1d80c1800105a40d101d184540d034036240c0b450b1440c950b9040b4140501552404005e0184140803150807040030100c003000e40c07004000090800d070032101214002903110108118610542c2c100f5000100003c60050010f801c2a541761641c0c01204600312900c161000160200200001111510782c0036085c0d0b6160795461900f0800403603080c90b008155803521241c0e4042c0c0071100b28100040030003610340613080c405440d2000d081c4400e000b960f0000184101002c0324021242a00070059818054001ca4440c82c1601100501c0c05c80c0498000c1e0300c2541c500c039510110104240000400d640b0000107001a0340b8010490304210108458101100304081d903105250280c2e44581a50245d40d022284c0b00540380c054908070b40e4015107009025000a03020040260a64000102d98648046074550b06403000300e0481e02034403070fa004c0c080030707500c141c503080403c0109403158081c11810030520010002c651780385 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 379700008 1250 379698758 379698797
    0x140415030b3c0106050d091b030201090e0f04020904060209040c09210c0501120f050c030615040807060305040221060a060801050f06060a02030d0f06050a0b16080307 73
    0x40b0751590041156411030110b1203600c024040702040c1100000b10b20100790004070300351450610900d0304200c40499404a4084140d01990380198007445180800254201d01071001d202444160f0210f505105d0000d080111074030414801c1d011010001c4040d5200e500b040a810006003013034822541c03c2c00b05a415444501c9100a000c0054a8400401e854036107060b44002021410fa8001d81c1e001e480c10002404a04510042d14000d08100111204051503800144080316a0210319800d010622000801010046000300404d44030a1200d03407000400002c5486588548440381d4040c403810041a48203a200c40c0d00907100134500003c00f24865014070111180140489068212000b0703c4201e002034800c0380c0052015030300034000f034070340810a031104450061506014000c0081c00031000c0784240100c4102100210080040350400c0f000c13100140220b002d83c2c1c6c010b00741414003080e1625000d054401800c003484603518544920b03904d482017504064840303000d00c0a02d1100c41c0420010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 379701258 1250 379700008 379700011
    0x80d09080c091308120f010518240411040f060c0506060904030e1801050405161d060f1305240a27080f0c0a050603130309090e1c020106140415030b 65
    0x450303032002091b06044000c0401e001042e40305510903010320841802d030111400342c03a80d105083d010b03007038000a401c3ea1042d182426200050341c3c4145407416010a03a818200600709551406c0048041c0302d841d050191009890705a0140a580c00100002c02c80d1918006407941301e4070034500b515151440030003060308a800c003042c40995928400050191307013030a103c0c056005403200c00705615030583e108007400700c081c50100460360b030354011202410303525168101c0b20f082d600e00307600a58035425401c032001401c43d02d0040300d104034102c22001405211010108400265182d045460b10010080a8480000c00c0030010030811a001580f82d940358103519170001450b0b28405040c58110040c040c500f400c80511540748211003210b024401c40d151001038070b80c000c10b003d044010078015814250f541c1d180b59030005020a05114048500090118007186040800b41100038410000d074003d03801d950180c0904d10b00c00c200d0301c05c25585440c09030040800c03a00e081c051014910344984403045407140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 379702508 1250 379701258 379701277
    0x118020a140406031e050d091a0c0c1f110111030a09060f020d09020f0402070c0b22140915130c0e0301091a0f0106050909090c0d0c080d09080c091308 66
    0x2900c40741c0500205100c7c4a003904a280703415400c00d4100320f9030800209480149240d20b840200394003546600c108902800080c001b0400c2400c10785800034650540c882c0e450300000920318021040340b61605024211415811809403819643c9058000000b051955419521181c949924000035085440204465220302102040081540c01448031502c10160b405000b5441004110007040359500301001751003001c00401c2e030f0381c400140c005404242444940b56406000c240c0001c600c00d4031420401001d0064804038800d5070f40d88803412044078022810f540012000f20070810b40d89060b44000103214950a01d1980c4500d00c07401319003110900702c0300308c404e60414800c410000e81c0c035841c42075108006840c480541e40c140107004200d070203262041ca000398841c002241c88142c00303108514180101620048011105042c031900c424400c2c0b05800c228040d524164043c0e604c184a10320540720028010700060184c04148090400014940700d48641040c019800266504008084070035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 379703758 1250 379702508 379702553
    0x31a01030c1e180506070503070f03091814070806031e0109081605190302030f09060906030406090c1a0415050c060a06030b01052b06020d0f06080118020a14040603 72
    0x195081883c2c070050031600b01611415051241000003107000041710300320350b403100d1442407251044c90151461b05540c1c04c08010f0300a042000107540d0802e5004013010b80c5249d060745180d4031100c2c0c05a425450a03102c86805030412a210341070640b0580003694825249000044c194140752982c091903000700031001c0d568072000e80c42c5401d12000300180f00c01405505552003d1941c01c2c0d40c041d6481c8940e150030000d044020644040d5075a0f02000e03260050005400305540385050f10f032204c0109040007044444003080d0b18003003100300c1c21410450028101020191078076080800d18042e151450302d00e00100041040008018501803005a004020280000c500e240c214501481c141505801c83c0b4090000c01c00400c0c40324042c00907069039400c0c8170100481d402260f08069000e4401c1d16900102c082c00c01c50085807107809075210781c00322541100204080910907051085204080c1d10107907000745144000d00c4030502e010480401da0000400000e5156560368030f500f4401c0c02d44031290b5025 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 379705008 1250 379703758 379703777
    0xc020609100e150f0412030c080c060a05090102091503190c0c0512190f1101020406090f1703090928050a0e0705130b030c12030415031a01030c1e 64
    0x103061207008180d0300c820f0692810f0a192903401c418445010701d1107140040b481405c0108141801601014405500310020550b1149800d525507501d41c03003600d4450009280c480059010380c07041c03007513031a18000209102da02804101ca9142d0940000e00515030400c11030040d407500c1080c9204411600c406600e0320100240541441401c110100f01c10002e0120300300100d0740c194542c4100790710188524144094010740c0044100c1d4035011000303400140d507200040100e003180d0030104100883d824900c180034025195800d00002e50780c548043c0140d0790080c04050824580010340311361044445403417160100b00300c91b0f4411f845691800d40c14007140d594040c424004102e0284201d140080b00c028a0b00b103141c81c002c98481c002c038282d5415841d664a03144041c0da42c4c180101c1541f0140141840ea088004100e41a00d9901c188280d0b401684018131507051140070703014010b202c040c0070381550704080c0801c00550141810300100c0042100704031403c0001d018840c41a50008059501d400d0705 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 379706258 1250 379705008 379705037
    0x52a010c02190b010302010f03020c1005060312040e043c020103050a0504120809010209060304120906020a0f1509080304060507080603070b0403060c031b0201020913050105100c02060910 82
    0x203003402c0c1a000c262401c25141d1400c0810025a9402e0440b942031070800319140c426041203000b802002c00c2d0036014000d402c191007814145812840c01160204c043d070710319030045900f452081c4501e100308220249080b002802180000351509042080c4000c1210307a444003501040c03880d000b81c2c50329800c8200c125510425540d061051561150416600300401c0c1010784444e0211400300710400c0400c407007100058400082901034070103684000d0122a200d040c1443c0c00cc20303100c40c051041d40040e16403032000071100d2000035041085508094107107a001c0d00d6403078000f00303513941c800c000d12025113175950303600000c1c80ca5001b50702c6180900d20000b050700b41b076080101048da002e403201d482075110070700030f11065240704103d80449a2040c000610008180005e03006049036040201c20340d002107040e080401c5d01034008008c0030314100c442035044204403800c003040384d000b8000c00b60001d9600c010303109014000c042107540b6074002003281c3d00386140a4005848503448060000c001030b41070352074204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 379707508 1250 379706258 379706263
    0x6050a08150102030910052104030804020d060204270f0510060507021c140705031c0c050f070303080106080a020315010e130f14130218070509041a030d0207030201020706052a010c02 80
    0x1190032311a0071089690030240c80007060b0040c0504003911070610500d84000b00001d5504580040c2000c001c17103461388100c0f2052203103410121001d40c64603070400e41c54141c080001d204451241042d1588003070b0550500704c0407661a000500200e81106442184500300c00c2001402c505481c86120164180c100303a4045a041101e80d60209002c0d82c41901c0400a0300781400e4041108000e6180a0b0020041e50405c035181500041c048101801048404024590300c0500d2034141c03520340c0c0f200d0405440e400400c40c102d00c0101c03104200036017002d090441d6584602c4512070602001008103210685c0702002c0c908442d0208200c50810740d07a8400110b65040c1414810f9103c001112083c00301c1c42d154001c181c010301030319041e452500b802e1000520441c0150251041e080014104100100d000d05510452400c01032032603100f842080e840301d25a51000034a0000da03036040c0d010f13110b40361900000340c079147c0011400c2ca8000180036401003410b5031002c1000036041c4044004202a003103904040e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 379708758 1250 379707508 379707547
    0x16090e0c010c03090504110f0703020d0f0e0603010302010c030201150902130b0909010b0306280303090b13090c02070302030319030c1e08040f0b090a020a06050a0815010203091005 79
    0x2418040b5440384000880e4001c000ca0003201c4c4203079400301e0013807800303509006940b040202030045820080752902c10b00d03a00280c20900fa010715224504840408541540d8440000f44d920f40d004504100510055101d15000314517207110380008907802041c207484040707804850b04401c00b841c1d0b02065403080800741000d00801418403291207454002003602003418854140502000040000003040c01500d0740c45055001c0c400b075100190760100c104803c1c0e0300010003403000741d0006202c082c0c00315044210808407a50202403480d5101006d1509008801600540100c1e03019030240c1c01002002d40c0f81800103200d1171045032120074951003992005411114807910060800600003251b04103070b10016102c0a421155042440d13040d522440c00c0e400c10b400361f9000400207079010050000040c000244190708510803103002980381e1712045c3c12142d80c0034004091000030400e00214800b554040c64a40c03000406105403450b08032035102003855825401740d00ca000407000610010b01170007800000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 379710008 1250 379708758 379708783
    0x150b04140711120a0e1212040f0306060b0a0e040c112b05130905270607020d110309010804110a0b0c0c010c12082502030405030c0a061403040516090e 66
    0x3c0d041a455850040a0300d44919203031703019019940b10302408440400280e40030092618001380c2e220344820700444807613a144012600c2c2807e10002080c840ca000702511105282e40c1d0b00c0350012080728040002820078032440c041404107a10200da8010f806220114210310b03d020303960106041450206051071100703400e4010050240000405503421100341012242080004507040c2c64100c4001c00f90701010854840d0b1440c0100e0f94651400c0104078284191200d07001e46004201080d0b0a543c034030749003030404c8415001000b24030000d60003484129001805280202e01c0c2908400203d8802e500607000800103503c0072039401080c4070104203282d1062020301e0626160f4015507a0200404461628034092052800015503128148541c0701c1c59000c5046144c50790001c52a0042d460f5800780c02010b000e80200d0800c24241c1c06e18805500c01c40d0b500750f40f80c1c86482502e001c2c042d495080a40111002c0c054500c2210f8100d01546440740030300b420000000d2040c1e44855542d242106c402c070320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 379711258 1250 379710008 379710043
    0x11e080705060f0c120d09030305090106050a15090806070801050306090c0901031211160501020d05031303080417070c051f020c0105090402120c030406050c07150b04140711 76
    0x1800300340c0b2180291203021a1203010141c5503182c2016107800d1950f108000c12001e9004203040c01d000c0825041580c0e0540a43c801300025100d0f2007000c1d00342c6181d4040c103500584110360030028082003006a13840e51444d0300d070040b2001d0b04c91900c40e08095003600d10000050641c0c1c0144030601d0b0030302c0b02c550015184030080007203034013500104440000500c0050b09003000101040c1406005003c10b0b20b0480c10403041e201d0b4a80e019070707200c40090184c000c10b80113204010300b08050900034401c5900801c002580c82940c05000c3d5012680c2c0f00008100326801d000c4070280c50303443c00c403800250500c644260000002c00f4104028848a00c041e2403210010303c00b03540f07402c16021340101c0d0582c0101d90a1030000c0c0d07100419408074029105a05003920340c88d0f801001c02078140b03140f034041c5000c1d030b1040078148a2034403982c1705a0518010031a000e00241c10b09451510055616400030010707031405840840e480061803103450b5001800c580307800115812051004141c0e4041c4810210195480b55 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 379712508 1250 379711258 379711273
    0x2070b0912012c150f0a0905030d05010305190309050409020a030f0606062d0c290604230f0703060e07050a0e0603150d051c11070602030909060f0f030303011e08 71
    0x100b0404e0401602c0d6000034850070002c0341d1602000c0c4c000070581038010b0122503458003030b40005802000b00b44804c0d540c1c0c1c013440c20104103109a09000c081540d80682d160300155040c1802c002c01480054412a80702018001c004000f61800580c00e0856010f4a000200c2034a00900940402d0741c08034018002003444040d05441d88520182600d40242032030110403018081c6090111807901e0b5010070314000044144980c2980fa000f201486031a05440078010000e08070080c0248107142d03540080400f50850004d045012004181d40d407001c4949004180b280d03559800b10100e4500fa10034000140000034a0500720ba08040182101001070315403030702e1032804242c032171122400829118030031580114448144001000702c01c80103421080e402c400046c101700083c1c406510f614114074140598030300081e031a40040281e90240c0c00251459001e50765240422601001418286600061001c850316040d2400c00c0a58061f1014a000301e400381c505040f070141ea1841c0703900075001907000c00e5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 379713758 1250 379712508 379712533
    0x921120409180201120b01020c03012c03070b070809030f0d0b0108060d0b1522140a050408030703020f1606020306012304030f0f0f0302030304021f02070b0912012c 72
    0x15a17040b44a4210305000982030b0307107100102d0406203020040741c2d0560914040c8101c801401a9005441001d0b001c40110b0020001074140c6902a08001401582c00800041d0303140e4040c03400f15a1010503c81a41d00c0c0c0505016034912070380021014469203030781c1e121600780d25604003c0389030300072a040b6840c014802c04ca950b4009130000003001c90002084204c0c440c007450301d0b500089035040c40d0028002c004815104540d10003069100c1d10f02c080102000c001ca65002a64444d07035011700d070003c00c403a00e19074400c0403d802a51000343e0709140b41508000941d0607800400900f010345100701805a601e080c4040010005960585840c1201400404d224081521042203c0449031b210462156200302400d0201440100f2400a13007a040282e10300d41c10594003000940c41503200302c2d084115011881007491444550a400c0b0b4003590001c03400b03110881c001c002400b4980c9006012a581409602e81d06096409a40c00b0101094444001c0303100c100d40c00900603103118040c2c1c01000720b10140c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 379715008 1250 379713758 379713767
    0x190207050a02040b04150801050406050c070b0103020d0f050114100b13051c15060e07030204051c0203100c030f14070f0e060403080c06040203060115050921120409180201 75
    0x504000b4441c9607074000400b281d0311107402005620407154940c0c0c07000707561140b21f0760191404071001c840c01e83c500f500042491208a055540d41a002404505968255401d210003407481c09820354021040710710b4200000d80902a203450100710460203009820208122502e2001c107400560b1300700d10a01010340c2909060f00004100c403412240d01c0c101001203101c02401081c0060060842a016211003503030000c0d60308100f048510403078034494070759203000c0101c0c100e000341e0190380d9004103c50350703410720001041c0118101600003000d032100042d0341c4034490b044621142408000c2078445410190045907841850f05210f51034101f031500e86040100108110540600002030040c40341c032020003929a28180c070081c5034450150344d40d980701d6060080d0f44800498081b44070748503075400480c0c01130b50030b692041e4031005a107500303045c070300070310204218030707510511524200301d6101480d154188100800c09501440b4a40315956a0804040c0402d071201803030400f0229070143c05540050f40c0c070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 379716258 1250 379715008 379715023
    0x6160c080d120b06070501090308092e0203090f030a03090519080412150204030b011e080613050a020a03032d080105040f0e07260105040203062208030106050319020705 74
    0x2041c2c0000c1c1d010314000002e41d1406401d40c00352296103458596820140c010a02600888072001100d0900c6500140500030102d192492103081c401c84400b40c558011a4018580200306031058602105c1c100100301e2458001c0c8101c1c0001036211070720710341800030030b001c0350002c03211610500c00e80131200d131034120051042e8400c1415030603240d040031003880040d1140060129107080c081d50307039a0741c2e0705040e16807000c00e002ea103100c14890302819090798183d0700c0c0c03c82211010f10180580e95141010000c0d01a603901301501c50780100e02070000160303207000480300594800e0310740065590f080b03c01020000d8903480300c66070000c11662403611854010300c1060441d10100c4000c24102055a0410301070f101c4c03d1b014400600c01c80c8408130b05481890580152540307001596180070002080140c00e81e070080e18080e405400900200b050008095a2019101103100764071260300707515501c008003540240e102a000600120611401002e030f181032802141c504101541482c3c440d07100c0c19103a908 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 379717508 1250 379716258 379716287
    0x902131e0207020f2107030c0608010519030b150604090912020607020606090a090b1305010e03041a0904061205010207050115060e101803050c030f0610030f0c030206160c080d 77
    0xe004084012945e02c04a600c21a480054103503810350707582e1300d172103807451101e80600c3d00400d83d40707400441e460400703800702c0411044aa485155591950701d645120381c0010303004004080d00c00790041403903210540140003c0040382d1001504c04041c0c100a10f01c022401d0340841150002018007118550010f0460f420001c111219070040d100c138a041d600400e012003000f00610480e03020040d00503916010064424002e40027071007010800c124103612449240903500034020078007800c10000d00090040c04e00580c000e40001400c6458420a0400d0318010310304403640c2e90009144000c000003070003110000040c102c9410301c0582015400f400b211000304280780907046001585101718400c0300003450b01d5201070521420140ca07070a01c940c403400c94803002c6000e8071580d040d6003103540300040c126210b08042030200454609682d240c01d50a906480190380030341100c007003c00565203c0c0020102803406d00f194146111039494049081c1e04a80c0c88141d041c0c2090350803600320f58000400400300b00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 379718758 1250 379717508 379717519
    0xa14040203060f0705070b0103050d0909020f0a05070c0909200604050108010501050d0b09070c060e06270c060a1e0806150d1104061106010e060d060509010902131e0207020f 76
    0x4d07540b0364121803034020104d0103842c410313000000100f405030210721004d0901440e80c0724800c0c81e46640310502640310710f28800f500b48000300800c0c1d080301e02c1000030b0803419224800752180b4a07659800201601c0c1106400e50740c640d0040003024800754440a041c18440c01230b51040d0806141c200041e0508105100762418440001010312180c84613030300142411000034050700e440e051080000b080c2c1d90a5080444030140781c004c00c0c0142e454009085441800c800d051440100403458640e0005446010203d00300c1c4a41c0200701625078840b8050b003c1c03203500340e8400f0518200702c16240090141c50852201348209001032003400c0c1c8070140e513031040100c1c402915640d1190000180004c200400b400d030700c0944003040105400e0f0f4001c41240741d0102141c01c03201aa40ca881c41c0a80060003500c070a40e00c0489251045c00290054214503800590700c80001101a02600451043c8010300c1058080c0c50740c81c8114807818110108031104c000d030340b8034214148441c40e400f041d42000302c0b20115100d80c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 379720008 1250 379718758 379718761
    0x81c021b031f1805010b01021b10050f0403050105090c0a05010c0515130614150108130308041103030a030c110703020d0b180a08030906010b120406270b0a14040203060f 74
    0x20381050b0070490301a8404000340780c181d60740381131060081011200d55030060052140032807240c04501520308113503d0051949032000c130010420b442a0388404800107803a142400f00001240003072065511505002028140c480d619504009030305440303400940c18040c104404102140e07000074010340d079801c4040c140419448050030441d1880c94400020101400d000180524001c0d070002c160083d0410b21004079400d0780c00300150356009044804000b40490880102c02103882801110303005800303003411401c030100d0300c0c0119045070f012510320408030303448100702c08182c0e600c00075101034031245a000c0d1603e1411640005c05800c0070301c202401c00b941c1600072649007080c1c007040e980041c000404980b4007080501c0c1c00401d54008030f6100e4141d0013520000100c4c9000003007107603104502d002c1d0301180c543ea56580e410007000300c03426150441343c12a1901014011400040038160b0040c9402d003481d2409810203000d0398585041c20001601c0b290a120068074001540d641000403082c1d1040103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 379721258 1250 379720008 379720063
    0x7091b0306180c270905060d030813110a240f050405010c080c0102030709210215030901090b0117010f1107020603072703060b090903030106030b0109081c021b03 71
    0x48800e10413000c13001030306a41441c00303100e807102071070111000490140001c2e56144100243c0506266000d0f000c40d0f00c075000540701c4070000380162141d9204075607100030700c04107001159524405030000d8130020500030380700d45110008240e50720b1080551421240d00e000f43c150041960145200e000c1c10312104101c0e0f1800c001026051b1a180e09210340215180c0c81c1c0060014401e001500c940f4000080084401c07807401d07c02c1400581c80c40d0054920708806005000c1600c1951000b00071a41c00c1d56034810f140d0010f04280c100c80e000300707a560301000f2001e08818a00e17007194040c0380e014800d185041d144006540c1000c00352803003140c0440d04946c030399a03030348815100004000c400701d04404881381808004120f416205080c0c1c5d001c4c40040000103003040501000c075500343c5502a0300c0c3d0051004011242c80794008030403c40f0706140400403140d0321540c4620380700b0021840003500d00600800c0e03501030b038104048200c18420000c0c6940340d09510011030f484124602811443c41c2036030941c0401c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 379722508 1250 379721258 379721267
    0x1101200f040806090606150408030f03091c0f02070905150105070302030c030d090b060f010c080f0708030a090506060319060506040b0303070b04060c0504080c0d0f0507091b0306180c 80
    0xb85090819140c1c41c0c80c0645000341c54140c03c4810030b2140040040441514012409890681c1c05500c01107107000c140e0303e0704003d60707040141310a1180c13107001841d07c0e00d10000a10301c072040d261601c42d030461a845920103400d003015600712100152509007004160398440301c618008030300a0034401e40d03515050508a045209203465075000c2c3c03200161f4003404001030b0303114821039409450b04506546400d002c01030741c846000101c50001d0a0a4100c1000c11250b0000302102885d21450500d0305841d07a03a0078072290800c9a4841c92a503880783c42e80700f803040c10700442d80e20401c11405018214140c900c1144881c0031703140090f10056441c0d00050030707074480358412190740a000f41242c3d03e4000616100c060310804880441c1c0042c06c1100c07885506015400351001d440041e03014080c01c01e0100e042c0480e0b080500b20680b6458a03482c0084086003040c0603040c00b90810110101d04034a441c18414001003d901640c1c00f0580f2304001004140d01904d80b240305d4159501010400700c00441c03040743c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 379723758 1250 379722508 379722517
    0x10302240d18120e09061e090601090f03050a021302040e040204111e03151c0b07020703080301090903181a03040c033503060d020f010e03011b1407020d0210110d050a1101200f 77
    0x1102c5c40393342100071060082c0010513031100742c400c50350000b0801d8a145020107030701a81c0b240d50030402c0c416000c1001480e1503080303000d0f40d40b9504002c90030408000c0c0340c00c03420200c02c01210034032070b800000e0013080403000301212120b0380c042ea070f41042c0041516030000c07601001c104c00b0b4442190400400d011510903c00301d0015900700040c25169611845003a00800d203080e000c4012600190080c1110382c010014541200c580d0f1070304001082c201170351200036900081040700e0f6500309420220001e0f00424107a00302c0075082d095480204401601036001c1082041c1c41c2c0d03100c8200b44208a556030341d0303850301310440d9819030310740115102010058601c058502600c590550800c0d040c00c000c0340442803200002121170362441030301c41001c1c01400c100e100c0c1c800d01a401c002c1c001d00d00c4026040c0912051803c07102880d02405003108058102d080402e0704280100040e00010210211a40009903000540b0f515000304030701c0400320030700e25012000c45000ca103c00408598a040010f500054a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 379725008 1250 379723758 379723769
    0x110f030a141207050a03050f010602030307050a030b030a050c030609120906211614030c0d0c260103060b190e06190905010302240d18120e09061e09060109 68
    0x29940d0f05040c540503016801a14007900024605800219050315400340c0b94101c1301190080d52850f103868104542c0e9511142c0b2a0061544610480002e07460420850a00e203000d103004d404c6048682c8101400c00201500031002980500700140c6c20840590880c1c100074002c8a0240d81c82d01c101b184100305107019000c1c0c24400001008100c000d008a0041e0660100103542d051925030008540000a000030740e280724034800705206000c407010b420b47c0070120400c01c9060001c240c59400350030f1403030054040c1e20032404562080041042000ca030180340c04455089807139401d8258a00c140300d209886d580301d415190300c212804981c1e2500d5403184054003000c51130241d62078584bd140c0c805d001e00800c2c0700072070041803500701100c81ea040350a02015000656241c9601e850604030000010b03102c00d454401000490384445000030780086e40540109105031220344030750810000b040504000200028016840301d001c51299180140d00803403122001c40302c132209034640400488031804d064008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 379726258 1250 379725008 379725037
    0x11240901200a0b09070603140f070c1401020a02070506040311040911060403080915030415050403021204081606030209030c041a0312071101090302361006110f030a14 73
    0x100801d00400e8403c5610440d07182080f20b850a6444600f10105c4402c074602d00301505100000c10a6800c0c1c260030710382c10480700d181044129038192a5007454112404486007e07071741c001603c84056406005140040070b0803540a41003c0c5140c035800c2c40d0300750700d503a2107110326038444c00700003040a0391296006540020f0044c03910f0710f8592405041c983d00c91000c4611902901c204102c0028202040b079106544c0b00b5400140524807030301c0c20018000c068400c4040d8010003082008400440c4007401c0109020303c01801400310000d0038003131410454000c6070406004000100d9245c038001218000e41e00140c4000550310f180d41da40300351a200304c400203685030144c807803804071000c0c0402c050803a0300c1c01900c00c903940414900056035002c4003444000d41260416a00e103540f07000710030000b001c2c4a100100b942108002d410611400c65046400c003918015201c028088654030454003c858520032008103000103803035016540d2800303140401410003028651040c0400e500c00150740d002c00d145880c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 379727508 1250 379726258 379726273
    0x9080c37060518070b0a0306090203040c030b07020c100504060f020606010518030304090c0504030c0b0903060105040b040e01060608010f27020906040e090c090a1407030b01020115031124090120 85
    0x4017071154880d03512900040d06020300452101414801c40340925803003126003100a01d190785d51400b4003401400c442c01e41c007669941d034109480300a1030740030041c61b03542c8040e40c1d181800400741411003080c09400440d800f2204020060741c000301100c145458070368103080c4071440f407070020b03107144503d800060650f0f040070030696100e1f400002800949100d030602108003a180c0c8203040c03642c040c00108941c1540b00d140100308506040d8024100d41c0c901420200c1d008415909060075205141e03c04000601404010446100001004000b50072046040d00e480c0321008601c0c0007950075000c003804520750001e2520030301da591800720350082c404142d0081e00c1d03182007018161281c0e40220424015000310b800035501d404284075020704468224800c0003582c40d480c0c0e00b100105603a0303524074107640d41e40b001004008940001d2000a511400a00741c0520070340041c80744854450481d54800380c104000301081c68821004d4450320082031801c06044800e50012200020b440b40510305035006250 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 379728758 1250 379727508 379727519
    0x260705060108070512070302010e1c0f140d091a070b0108100b1005030a05070509041404050f1c052a010203040606050604050d0b04020409080c3706051807 68
    0x546a040342c1d000400d07541e5a540d1a030511064900000c480022a0440d42c010710066004400880f14880c0142007140b01107081c440910306090961070681d503442c00c0c244007404010300b07092070600c4003c40001401110401c488013034501c01503800350b08030004291011004291444c1709954295401c003110800070750391044215101c0f0381524031540540c0c24510a4074650510504038030054429030307180d40c556030f200b2070000000c06010740341c501088010444003015640b680100460a0f11211500203542040c0c40c01501e001511501500c403504400c643c0000803020050b2030050010b142015682c03101c1c0c80d506c0e60343e20700c1081000d072005501b00304940503004e01507002c1c42c80b60703200301020406135840340100b0019010300e00c40c0030b030722071408080c0e10002410351900c142c1062001d800402c851203950b8614807a500f0251420680d603101e6440d6010381c4402c0081641c001c0440d40030035030011948011110503151500000d0030f444d40360800b00d1443d07032031100d1990301000c00c0c00545110700d8950 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 379730008 1250 379728758 379728763
    0xd06062f150c0c121201060e0406080304080d02010501050406030206030105090406090b28050c0f0a090305031603090b030405100e25050a060e030604062a0305040b070f0c260705 78
    0x100c08208403841920b00b13525090850030b00310b9200020307801000165a20f00002112180c3e40d0b000050742240d1140f0b40003d48610420240c805171800034081c09842c00c034050000e0071204142c0c0207611503400c1020400c007503203030441202d05440080d2207007021640c0314240107000e402411001070030300080360200150442c2d10315601d00075243c40c00000030805031030115a03064560682e05a05114820001200c070005060010004202241004414103540f915044d0840e00f040d00245c04100c40310003001c041503846510310000d0043d81d03900904509154461030b5484100a0041702c1c869030301c42c24940007040c01c0050410403070281c041c000d01d0150208001031155020321130140520000031010030840e0160002a11104000d03004058aa0396512440050103501d500141c001d0b425102c400414075502041d8000300c1c400b0703200400d55040034a8800100c4e00010046810404821200c1807959403150040c1c03085a0440f280c0080246500b140e4010380c0100310024500200018400b0700f0003202 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 379731258 1250 379730008 379730017
    0x150406050f0a0c2f010609020a020601050607080f09180a1a0d0506040b1b030a020307021207030507020906150c010905060709030201080f040c0504050403050d06062f150c 75
    0x58002601c840c0c8500004000b0b443d594405200881d41114010b0394250002c40c02c03107404440001d602101200001016003111810b4214407081d41d00000c00b521416010440300c0d00505c4250340440c581112621a0282130140c2e801d22204004005203038a41580c5002e8202c1454503950f00c080d4440c1412181c0400400362002491340d844e10000d0040d48510306148242904d6400c2405040c13559110398840c1802c101c01404a03095020050040d00c41d12aa880518401d03810100e00582d03030300308031030080c0c64000300f04200e0300f41107820402400001c0d4404141c5408a40c10748907540c05894440019891031025002011084008103259020040540002031180d00820603514941c6802c401225440d02d0760101034007003a410004150310b0201e080c034141c1d20500645030480c0d07564690000034240c0303105a81c10303000280e0201d9411907214079482180c00a021509041040c04054082c1f0246103940903500d6004484d654048074014905005445444025041155403441c1c4604850700a810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 379732508 1250 379731258 379731271
    0x405060c010f0b0f0d02040905010e0316030215041101181e171c050c010b0d0b010e0f070e01050703050c01020307090305120c0c060711030a0606090c08040c140315040605 75
    0x140340c000740300d0f402d1484040a0b03130b19003d058900080c08603000d12019000b20001210103650700d03d6861170014003403014200145100201128920071820003c3c940013010600c4c032400c501c5402440001020340720750074004802800c0c0000e03903641511078101c00607059406000d00a03281c0c001148012242c001100540c0c10306012400b511444820b160303139810184d040705040c10b0784005100d802e070f8011800b402000e22034070004203501c0e01c1c05021034440301c3c40c01c0c0d013200c2c98400c41d00148a18011840a0380d44034441180545031031070108402400301624081560504c0303800a00d400a15205030111041180880000c0d0740c1c0f41070511004003499150b20066031103000b0a128041540da40070211800c2592000042800402072030406c00b0562104c07604485042c07860781c442965840a01140900703501400e00040c09514158044040e20031088401c2c003080103e404000004088000d94400c3e9240403400b4080c583c08080806d15140c0c2c00c41d19600c449a00008020410215070400341c400c18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 379733758 1250 379732508 379732511
    0x917030d0903050910030608030409110d060b04090e030a080c1605060c22120209061305090d18050303032e03050a031e0503130201050904020c06060a0f0b040306110405060c010f 78
    0x2104a05c08801711f50450181940031b400400040051916941200402170100c2000710300e0149140304a0003198032541c008a0310020215040008201c81d1150b103410f40f1581d0069441d00d403080500030300c1440b008002032420013010074048006091100c00c00e0030141d01000b1a05c1908120803141016040001550007051000700381e800020042a18201100e8200700848101802917003084500800240941c0c1c2025a08040100744030660142c107008200140c0a804e00c1d02d00a20001c02100c1c60038000c000310444900c0c02c214a0b20000100d07940070190080c9104034911510814010b01d220400f0389400f0300c032180d008414030802041140c1d4051103034440114000c0324105001400301c040c0301410104000340002103207500e65003c5070350003501c149420382c68841c1020000f0101e8008990002495010804100c40c608018200002514103203000202041c940114850f05101c0c0c0d010080c520b507103aa07620b41100401200799009460010304054413280c8550360b0b28001d102140b000510350303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 379735008 1250 379733758 379733779
    0xa0f050f03031905210c1803060606120a02070f0302070906060f080a0902120105180f0c030606130603020d0812160f0e06040306050901150e070917030d09030509 71
    0x249070010071104022100c0d1039680b203182c1c0c00101503074242c009042c007030010320f030300840400070a54030a28648200701c00b135189625140101e00921007203040c0700720603020303074444810f0202d0780d40c500050740c0d90100400403601c01d0b50b840441703510290154010060490308080484030070190007003000002d503801c1d08002c110f802c0d500c0c00100c0c1c80992888030040842c08030800315405201d1500941c0c6094000303046032446980c44411142150402c41d24400c59807030201244440c01d01c01d01c5910091003564005203142011400000e86982d405850580718507444141c103428412640c1003030004603001400c062800e106410010342551001f041140070310504d4001400404600610b5100142c5a0307441c1510010714010070fa401e14400041d903a4050400e000000c00508030f030182c0c82c400e424900c00481c0b40400c01000f4050024a5040901e08105030000c204120f07a200c020403044918080a1102c4110003045660541c0714400400208508009101050541040c001c20740c590041c1c42d00c0629 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 379736258 1250 379735008 379735039
    0x60c080f0f0c0708130605040602100b030607031e020d09021c0f030f02070b070507030302060106080c030a0b01091508090f030a0c1506080a030e03010b0103061d150a0f05 75
    0x1510100c0e001d1980c0714444021901448042d009440d68910030b034841890b00070040d000b400c0c420350702c1c1d000e2800110001004c0c030030b1035810f02c05080c001c01d8402003408913580c491700007600c554005081408043e41c0300c0c95111b1030380d42851100011900404119541c0d103210344007001800b04084d050b4001c031815600c0c00e170007041002c002c0000b140c000d03844e452030000a42d011211001280a80d004610a210700412410404001014414031850052903c00d195207000390400105030710944c18440131104000507244d501e02102e501c200c0051000960b02103260060312903807083c0c2c0141e280c5020108a10301c4c0141c0101140c1d0103000003208503950301d41d041407426600d200348007812000509055a80c3c0000d0b8001035004441c000b11480403c41917250120149444950101030300080c1513129040b582d0b090a10901d04205400c0c0380900c4428201403040c012200d05420005044540c0b42c005404035100094181c490078005082c420010fa83d400140744403050f40c0074603481001402c09400c40b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 379737508 1250 379736258 379736281
    0x220317100e041704050a080a0210110a12141b0715050a050c0a142407091206090b180f0109021008071101050f0a0516020c0d1a0103060c08 61
    0x101e460700005a419550340d540c41454802d010180000c103140c2c1480007250aa1345d094000000e422490300030300345404180100f0401c50100c41c200424003003980980080e1200210300f841d501c6420010f405002c041c40841107668800c41c0910102d8032a0100344140d0711618100d000c0c408040300f8049031901c035101d28800f42c400f2460704581c80400c904100e40340b41c07503004001030054100b00c502510f01326885910b0f204496640d290320b8078107541001e814a4070b8800000b140c45c11022a95071007a00d14500703100301800c012031500130604071205000041e400c00415420030365140d0343c041000b604900703003511151007400154059840c140a050080446600d0520030000c009800507d10340c0700200500d802d80e105540039110404100310f030700c811014002c00740109402104500980036441c90418110011100007400c020304001481400f40d5805500042940403460308a408008420003454000b15440080c030003401c8a07075850000005000c001c0e8080d1340c01d041c482d12200c909a5a5002104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 379738758 1250 379737508 379737541
    0x210091e03021008090c0f120109030305060a0f0311010c050f120a120b06040e04020d060c020a0b130c0303080907050a03081801090b040b18040525020d02070e220317 73
    0x21001e81c0314401c0740060b40350099500c480400c001d400301c8c850221392000c003030950b103a070328094020230349500622140c2c1c20600418002032134015040300902d4110383e9007541c04810200210b040184185168007030000c140252585607215400f1030319204034140c42481c1680102d1580c3d80460f00d14070704540710100703a024514802d20000c020074030b400d052950141c290800944141c1c5c00603406c1194400080b0140b10b842443c000b83d8004241c1202246081010018010b00400e1002032a801138800078600b04020015039506040c43c0200360b441400309485d01d2043e5000e150712005491000050084210040c0340b0307000f441440c0b210000c4050019201961948503140000070108020007400032507001034448a4200e5400103034131803005000800383e540580700a80441d00b118000e071403044500e00c80c070118244600240003020f0342e00f4030207034070b803280d03403055a10f40c0d41c0c1c1d80700060780010342500d40140803c2211a20302c03404018240107120340f10491309851803805280103c0e50403001000d160703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 379740008 1250 379738758 379738771
    0x11505160c05132a03060509040b0a050604060302030615120d1106010602030906071101050706090602090405090c2b0204150806071403040320300a0c0210091e03021008 74
    0x1034038100305000100d541c0f4106013051040595070800840c50f551014041402180120349011403418000211421100d002d0140e600c201c2c5000030420068a001c81d0703159214500719400d000c0a02d603e00403580c41603a580c080c8846020760304448180580140c012800908190304032640c0703a8079401c0980e074a1044021443d0702903800d0040e400050350140d11a1500c507018900076041500e0f0b961000c0680e0107000c4101c804580125079202c003810640700d031a034010304000050030803203298404128203111114105c6114144948a001c0c0741c1d02d0042c00b8820240e0140040005083c095910302604586024040b00d9018501c04070306003610a64029412182c445001850358641d43d900385d0340c00c2c100e982e83d0036510154090000b140002804034480d45650906074100000b079407800d20707407900c5200115182c441000d00898076010362005030780b0003c1e07905513002449082d54103401d4945185a500078901c0065100c880c401c0c4132100b440383c41c101ca10070b80e98041c400c1450750040d40c4148040740c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 379741258 1250 379740008 379740041
    0x10e01061403060f18030d14090109020f0f0402041503050f130b160c02031522050307031b120e0f012607050906120411060a0206011505160c0513 64
    0x10130070740b2034a258025004040c80ca40c00105185900d940c50460308030345c90040c4041d40d80c11420702c04506034480709034420803400080210300d440b42e002030038100601d4152400b07462250400c00083d2204d40c101c401601000e01824506103907500020701611044481032040a00701e000b00d00c62080d142c840540160f8441000140e0369203800c2a010035184d0031103100208504a051840507071414040a400088002e544288914040c280c1d0000d28040d0741a1400c540074207440d84d40030590107c15a0705075545032401c10000c0740012291509802d4454000d060300c0070043c46500c0454010a00000000c010303907208001503e11320055176240c48003100320000083ca030300e4111200c0c2c410141c032a40070301541845400e00c0544030101d48036412100c8991180780300c0a091006003c02d51294440010045a07164945145444d000703440c0c40c810b105440d80e05812103449001640030b08241c0c0c2c3c4d200b100e20328505215190f4101040f60144ca441814061002c100d0511105991400b0702031190100f07224 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 379742508 1250 379741258 379741261
    0xb0306070e0f06030a06033507020f061204030201180804090c030605120a020906010e010e01080601022406120102070c092f0a032403030e0d12080a0e010603020109030204020c01090b0108010e0106140306 89
    0x3500d003142d50002004903805181144402c0556450b5003740c01c03a402030750b801c8425440c092034003074216140b151001c90300b8841c1117404800248950101c40582d49007040c040b400c00171001d0141d001e00610727080729a0003019125420800d01f00007409482c003500840d050020394489100550795458004c4040c0e0028540445244855000e04421a00000c040c4100c2c1d80940342c001c0410401e5200302c0100070520640c9003801240e15200e510102041d00802c021450100c0c65034071120007110510031160007a88841101540b001d044c04102c050420207180b11802208200b403915207640503030b94407070200c0d00e40811110220386409030848640720244d5056022411910305903050340faa032116a41c00502203010b4000150074400c0052249041e8440c940071b0306011207a00142c0e5410000080240e150000400140c3c2e4011a2001160b4055400503910891041d40c240909070340e82c0d024044d508858000129980150f00200c030380780e0024000c21840317031202007070311491407151141a4075610080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 379743758 1250 379742508 379742603
    0x10f0504090e1c09090e2b020c0d060b0103051f05010c060b100c0302070b120f0402120a03020d0909060b090402132114010b0306070e0f06030a0603 65
    0x14040007421003540121040c1d0880708401460200440c16070400003150040100400516800361004c819000006019a4010b0b2076040034121f06201d0b100c1c0c0c1203c2da004200c51151b00074441011f0715200a002020b2003c910f04066001d03104040072180041e00c0d03c4002011301c60400d0b10900000101c0501003519440c10f401110704241c0010180c40741503441914809568460840841902c00c580b1203180301d004074100603007041c1c006d50040100340402c10400c3c1000703141c54003840d440000003590340c00d562290f00104a940c01ca400c01e83d0060311402890307806150300042c071021040d01941e0342014a0741c45003002001e4402921400c07900720300600a280345403605401400c0641e8aa040555240703a650710004201d64400c0c0440030b0712544078130301c0700a0007010f01407500780c0741d420402805020b50380d0000c00c0e078070440200558100320a0400d2541a60b0300c03e60240308400000f00130645906110480c90010030040c401250361910039074030311003842c00083c01200030703e4515948020000000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 379745008 1250 379743758 379743761
    0x813050f391e13050105030105090307050616120f1401050a03050304051c1b081b0d03111e0106093b0a0c030803100f0f03080715110a030b010f050409 66
    0x1a0070b02c014094001c00c039100d10b88a014034050481c40c2c507100400e480d45010305250071550050601036080d081005100b0100d81c000801a42100c6a40c000c1000b001461b00111170341061240c403004143c1c2007110304408a1116000940250221a4600041c1e680c0300300b0084600c0300c0740300040007500306000400641c50100d840f200b15410000588908207081e13902c9880e0201c080d10030210142030b690301884040d500300481f0000c40001d007081804160b20400054882c25101d03c02000c200301c1c642e0025a0040a020419038045035910018810500301c0d100c601903c0e8501521021518045449442c00154200c02a0713010300e250175001001242041c5e400c4040b141501d160442c07045c0030240001840c245079580c010350040103069141d04241c0c06100d0060001d51240b09005800345c0144440b90781d859502080b207034014000c40d9038080d9882d100d4080da05030b0584c03250082c90301c0c4040000243c1c1200400b200005030b034040007914240300043d03500720050000c080010300280800d0140b8800d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 379746258 1250 379745008 379745029
    0x170c010f0e033a1d0108060d0b18010c0f02060a1b2d050a031b0207050111190c050109080613060e0313060e030d0201050112030813050f39 61
    0xa101a4010030b010760403821803180aa6803401c00050390a20f118400446010131030356540070300f40380a104508000b000694490484039004d03140811100104090103a02d0303811307400c0c407070785000240b040d81f4a146000d0070000003400c1420260049c4000900800320501c207400c1203142c03850290611201d810412141e0b008003162650b890348071000b2a0b4140c000d030342407544c0c1c901201e035146540c034880d90350024180c4661840105040712b41d05110031420740c02140c11403c1d2513080c030780440c0944250b443c09140c050340c03e400303c1411083c0e410150034031200410150075a002070302d61741d94095036583c0e803c0c1d50369000ca40400c0603074020b10103040080d4036174118403c4200f4403011a420028101c461140c0307c00130703a00c8400840d580900c1c0102c40d0409000f180c0f4200350701e000130807503503160502c00104900c8802c0c0060400407070f000060343c07065040004900070fa81240403140420350990314079940ea490b04c0050503940041502a80e101405440b50032842c207400c40146050383e03441014050300482 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 379747508 1250 379746258 379746313
    0xc18120307110a0f0b09270a1e0908090102060610020a0308060a0305030c07170f070504020d020f0406050d0f09080901080a020412050a0209011e0b030709170c010f0e03 74
    0x3c0b011400590390116161a101429201d10b03581c0d500d02110042140e0100841949900020030941c402c00a0280220141c3e0011070100c0c007281c1c03411100a0301e0680c42013125406d6a00b40b90a4201061161980c00342c2040c840a800320b4007640c88010802c030140380801252030059004080010000f0307c036070782d030b9904560040c2551b49000d4881da03803141140c2000415040652005030208041d8480001c10400c4404000181074011114008141c603640369000340e83c081e54001404228004103541156605c6110520403901d590f00c880c4002d2856014040e002000c909040300c0c1403103203803d482200c0c4100d9111036164a4503210300015190700e0002040340740b40642c28013000036008202c07141103c48601ca24054100c85800c0e1040055081040c2c2216035001480010011400040c81e030312070641340010041790f141c0e9500c5804489003038054104ca088440201c800c4d0f00035a200094040b502c0c1001d032204c00020401a01c02c5070514400e9500e554075a220302e20101062208101290007102d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 379748758 1250 379747508 379747519
    0xc0d0c021f031e0c0e1909050f040629010323010b0a081006050f070606030606060302070203011a060a0e150307020708070e0709140112050c1812030711 67
    0x14640340748010103014644031401281d1500300c460540400752159038142448510204100c0000f24001841050300b07000042c0104856145940a00701d4428100010040180148401c0c81c0080034000e050205843c1140c02d60306200d101b0760003d85038406860004102900d0910982c02a00110040d00c01051a4081c00743c3d01207400710b54001c5400d450340a020f50b050441d60300c0920400041003c80010300501c04504010004d104440c0c0c4842250315000514100030b0712803c05041c5140240700b6a48018140341c070740702c0c1c0060025010f801510009000310020841e100301102c25080340344003600119400343c404c0080850850107000340c00c1c17a400c0050600252118041d85400440c1e209a0b40e542c0540d1180d1810083c51808114110160125502e1803601c1d0a00c0c84000c3e01288070340c084d40c000340d203e20080c02c0030b03a44149403001601e140194180003500b007100400c04c1035030188503410b14411054001c2140d5003080000460381e068504000d520b0034841da00d0381c3c42e02044810006a100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 379750008 1250 379748758 379748779
    0x90d02120609030c1e0607052101060f030b03010b03060402090c07020409061506140406050d0209030d0903030e0d0213090f0b0a0c08010e010e0f0907090f0b04060b0c0d0c02 76
    0x3550800c0540e104088000c003d607511802084203502d0300803003804075407031102c4e0f2101c05c5000070404503000e40c120304541401915413440b41c52000e21401605845440b484800000282e040c2c1e02410717004049106407020411109550306150070703a4242d26000360180d02c490003103401030600001c080d0b8040392440e030140c02c2102542c000fa055030074850f01aa96162241c0c2c80000c0d0442c0f43c05a00b0013801d440c20400001d4260010041d064021803103002c0074041c010501280f160155011101039002c020107030b400d1b000034014054080303c10b500040e40003c90f00d00300b116203401c0141030201e405400401d00824803405984070006402d4410040741c00e411b14052082c0051340f400f0159000300920f0030f02080b98946884010080c5034140d00030a40e00c44403e004000307240c9071501c10b5403c20640a5042159a00c52080d02e1400c2d01503440502ca00d490900d00740800032160b03104605d42c681c00c40d000c0c0a4a641c4642c00d50740c0d8001c25005c0e400b117421505880b010a07000795103c855091020340b00c0d4154 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 379751258 1250 379750008 379750039
    0xf02070807060503180705090406150306050414011401052206050306070809010c020c0d02060a090302030f011e0203060105160312060e07030e120301230306090f0f01060b090d02 78
    0x10516903a002e0b002181011081c03056003108241741c0508014000018014140341c00000781a080004c0c0025028603550903145110745080b0290002941d08500240520f0030f143c540718030301d046040c0002105500c3c0ca500f00381c251405980090480324000d1619842401d8401c00c0b040b20010b002c085030f0341075a1180c0c0001d4940341844240d00c261003070344401c2c2c007500d800c45034942900c07203100d11001150088441c444c983c1d600c041030100e45070b0301911b00a071588003403081030342c010816410183d418456200f20b00d400329015007003821740d08080020000a441418140c01c01da0100f070f516140856402c0c0412200001c42900c0a501c06001c0d180a243c1c080124010900300c6020741c000245c041100f200708071459415000b10285940108001d1101c1045151940c4c110701040c00750006109540c103911000c9889290068984031000f42580c3c06410134140055071503548880c0e0104a01469036000c00030b4030123106030011107100500040c90071540800b00800e1322003070482240d101c00031005181c1e2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 379752508 1250 379751258 379751263
    0x402070c09050610032c030c010504060c02010b0d050a2a03151a01120507030603051002071e0c0614040b13050306180c060307020c03030d05340f020708 67
    0xc00c2a407000041034108001804100c104c00c841803014103080c6460b00d1801c1001c1101e0f0300741401c1c003890f01904070001c5440a8254468940792021640c2400306004c1880040e074440750344580260000c10200386004140b041080310f5120181c02134001000480104090a100744202c050200d40d528004002940045d80400150801e0b03403400c8212100295109103481804440d42c0240d41c51020401d035900002d1441c2c0e00312000b032681e0350301d030004900054082d400c11009994404240d07203483e4100321440000707420024050f81c940601c100c0300800d42480c0f00142210035000f64a1a4013541003540585951001c071801800d80b100401001136800c2c000d030041c00b04042c0f0141109400b9144c0345c10140f8204004e040c0408040300300302c1d8400252000540944110410b03103c0139200e541d00001039061040381813901d50103020002d10740ba4054403d83c8007a21501000429100b62a10041003040b500c082004c2d0300c4800c0061824504a1401000c28141c103079203501c11034100c81c1d04e0b000c0290 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 379753758 1250 379752508 379752533
    0x2060d180519020301060609080a060f0f0c030926070f030219060f0c0206060a0608150406151d1305060a0b0f0d06051e06070809060a0c060b041a0f040207 68
    0x10b4004030102d60114138003800703858010001031404040280c200340a1544440315140d0040502e551541c481460320b002d5044103004d1500b09000b0011101312400150103441d021304c085032441e5a650015080c0282d0b40380003900111072011550405505956080b4040c03030b03055094095210700d00011030b4441705011603042d102d105460214510880403000011340303400400200641d002001005141e0301c5e041c802c50115441494482c1994803800c0440c50002c103140c10355034000f41802008500460040e00803007105149d076071800d0340c1007980c429840f0301814260b2000e510860350400000e0203101504401c0d0409030003055411413035920110310300540e0261218401c0c00f0404119110141564401c8600402d015915011090313040d443c0e91524003640780c1c8052058001040c076005000303000095031180c44014000e5551600b01c114042c1c0208000d41c82240e400742801e50401003400d29004184480301400011210000900100421107085581503070300180c0c01e002080203d4603821840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 379755008 1250 379753758 379753783
    0x41709041a180408161b03030f080109020306180a140a06090c0504030803070807021009420b0301020d0f050411060a1407080c010e070e06040902060d1805 68
    0xd00d022040380148181c00d20b9400d920125001001c0c10000840c00403800c50750b08103c10400240340d89480e240441018039100c114408005000f4404400c0503045810f0740700c0e0112a03116420f0aa0380c8110082c02e910003226095001122404200300c90081050240d03000469800046250404484894010a400c540381e014003521078408200c210914450400140101e00e8107074a00303821901c503101503101c003400c88400c21904800086189100f07011000103104180010b014000b00e900300f02c44d8000c100c4118410560980c1956840240307003100084141c140d01c118407404026001001c0024030016040d070750155002c011381b0800444c40c0c810680c090303a240e180040e0b04d0915007044803084103201491805800c041080307400d456003020f14945100310191126548000624049e20580150303403900030785600b091440e120342c0308040341c28001d0314004008030030540d8031901000140d4070002ca0181d0400b208024404c003030030042c0c000c20040c410310b514000310b40440d965036514021401650 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 379756258 1250 379755008 379755041
    0x25030b0d2406080304210f05070b18010504080c120c1512130305030417040f060806121b210d02070e090a021c03091503020408010b0a0e04170904 64
    0x48100711410321495002d4008400258100750810032204581d104021105c11303021500c500c007004011685505007815580702c2d055408031507450a00c4200c40e0082d41011036600ca500141c03034130f1544500159812600443c00404081c41d10340c06105011096190034890750080000c00b00031500c60b0280340840c000c0721010700303907115070300c1c1039030400d049001e414040b2030344000c01c1d18008264040c1c15a42c020fa00711900444421420100700002e1050b40e1020200310901903001a9503074001d02014440d031400c0d6000040c0488402003103464525000341c510340310505140342074860901050301126801c0c0311030306800008424400f2441c3c0005d001080d40140e000f448240301000882d200145c21407410802030124001302e6001601e01a110a0690350f4450514401c0e024035114000302402401d0b0400d20480c00084418010065841405215100e40c00c0240c0c2d220141003202400c0200da01040388402141c45540e50150500c98214100c0762465061046165075642c610a240e51308201954 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 379757508 1250 379756258 379756313
    0x5330603070f030b030706080103120207030516030b07080610050c0f010e0102070203070e13080c03120a0501080c06070c14030a05070909020f09040f0b10080714040525030b0d 77
    0xb00506480d07090412500903006074134100300303064003c458107055070b52100c446001c00914000880c9030003446d62001d451840f401d1045403829034000403043c20340e80204203100c02540d4405050700d00c10402d440258110310f40007404400c0610440181080c905068144d4008694050078903007035504a20b40c41c0d40c1c503540061800c0440ca820403020008281041901c16146009211031a6034035940314090040d040010704012490300920403614502840300d1400503a041407442c240050030240201a854070030041d591b0503e140800584100d99070001054074810f081110300e6980605004126405104401c0d1050000e00c0601c8a8809000c00020001e622000f41c0100048001170a002c40e000310036113420700c008100744540303070201c0c03a42045500016840d01c08803070b40d00341d80700e90202000f4000c440010454500c2c08158840400040f103090006440d0300744810108151400c0315500c4410704006040024001e0300100107510009003c98071510641d1a0454500c001407143c20100b0580710 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 379758758 1250 379757508 379757537
    0xa080a05010614090c040e0403031404060b01120207050316020111150601080604020a0806040b0109050d05030304050d0930060507080405070e15010318170d0c02010533060307 77
    0x80f10074960744112200c100c3c0d130034003a442c885944501d001d8410f4a81c0c4a400281c2494040d0b00450000a48000200aa4034140c10074070f0003032803907d00480c0000c0100e4044410070170903000390b906e00340d0400e014511303008402c4c8420121030000b910803811710400c0c664114141c5801c3c401600c41c43d0040000040c04d1400d64001401c80c0c0e0000c148030302ca1441031064a020381d500503101903104105440c0080c05a0300340780140c600130000e603c51036010011144a404016001c80610300484c810400c5410150303411009803000719540c0101c110025565030b404440c1180080d42c242a8264501c01b0804000c080e02c0b007600740e410403550500840c2d074010601c01000002c2060307600900030102c000c0c03441c0c00d109034000c841c0d076102030181d8101605c800881c03803c2d45490790b0b504489039010950024503882c00c082c4001e107030007042d001c00c60340e0b14201c51814024018002c0d50310030040c260100180e00d00d204e91010070801454800100c41c0c681d100580703403540300d20004502a9003135860f00c1002060382c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 379760008 1250 379758758 379758779
    0x307080109060b0a1409010233100308030f0a0e030403030804140625120903030c180f0302090a2405030f070f142205010311040c08150a080a050106 65
    0x43d03210680c030001c204040300c1c3e02503000450040c41d5610320b0440303541d8150000100d203410b02c2260119a06948074008468480b010002c0711104d0000b681c15503201d580702c00c10100c0c041424407020740102070820005000c3c2c810741c080b940e40902031345000101100946a00c5240d90420340080700070600a4050000b80072840040798141c00546000305801d00c0c0c18020744220407084240740010400ba40341d0300c1007040c0680c1452107a8009180200f11840d06820b000300a0a000e00c0c2100115003094001004c02e00ba100c881416110890310b44440d4510f16421301195202c020651555560f44181440010784113512807900840c00301100030145090808060030000000c040d09000d5002010030821850109040811038281c00c81c2038003031130111700100d20840050840740c0c44840080d000400c155005500c801e050300d0050503012010b8540400303110031135480c0100400401c040302c000a40059803071241080296002c1c0905181c2e80c1c2e241002441e2220350501140c540c0d45610061010b820f54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 379761258 1250 379760008 379760021
    0xb04050a0b0f0a180f11030a21030b01021506090604021210031203020c0601030212071a04090c110322120b0402030d0206040201050403060911060324010e010e090406110307080109 79
    0x144103484c409140d0b507a0b4055482c000c3e0042541400704080480f9907401d010f080301c201d80101d034000409000c01d06050b0306034421802140842c1c500301d0040c1e89540b000070018000c1c0900c03518030070517841d0b240400c800e00348002c1810313130300c6602000b03403130a50702807042e84a0044c0b00d00381044a155083d468500071744105608403200705481407107071640190300016404d044a4054440c01c0300c0940f680d000d9824251a508020820501c9001200100c0030100c0184100c03030b807282041004030024141110551790030761144060350701c20b01c0740c0501015142c0c1c0903a8100e200b0400c580d512580d902c440c01700e00710402e00641d0030007a041e08000139800c040c070250303083c0162403006d8a000d1800e5800682070b400b5500014000e1a031b074000e40310400090018812040b14010001a16072400e003180b49820b0018000720050381c0d1541d240c44800d540580513580e4911016100c01d0704568000047c810b0300c3d50300400903105030b07498801250030480b15074025805001c06648208072036050484040230b5961 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 379762508 1250 379761258 379761281
    0x703020a0c06210b030a0204020c06010e06040c090504020d14150a080c010f0f031812020f01050105011d041e020403020307120302030306090a200a120603050a0b04050a0b0f0a 77
    0x100341d180108442000344000c400d803020000003000b500000c0840d00e0401b0a11000350007900c00500100c1140c0c00140f040c0c100d48c221404400195540c8050000707581500c11140d011844a40d0103016600d0a42c02401607100005000102011130070020a5126400e03182c1140d100d0030840312565604200b1040c001428101d801082c949038003500082040c20b2f804410b4080000312912142c280740310307803c2280c1d003e0340810b08591484035400c0c070600300411425458058031030284111211501070143c1d5048410507120050000f440c0780708061844020746045a02941d540030340f2941202c05044415400c07406000140c0321400d620501d45450303155008a5104071076841150700103a400001c403940002d042d9025602500c3da445030b840609031045030686040111106040851004c0d0041e100c052156561900a07011000d204400c496441c0800303000c640010080380049860110042d0b04075100f50211255060b031902c5103403401c1d0041e20401e04a681d480305101418265014a02400c078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 379763758 1250 379762508 379762517
    0x101e08060307050f0f0d080c0304060518030607020714061b0c010e06031603020d270b220f0507080f0307051501060806042007060501170a050a03180b0703020a0c06 72
    0x20b041c000212000317000f03051281700d400c00c24003110400049800361501014010201ea880d691107890180c02e6030043c4c1d03803440f280555100000170903d000241c3c180688800d8018000075428081e85503204141d030540b07160842d4041001d54981d29280400c10072041d06030700505951210117000608040700c0083c1544111070520901542458405541c0100400c6041c0140c2d00c1e0321001d9101c000d811304081f04035030792842103005103800b50700c1c03913440d400d00d4840e4102c9401c0d5510101c0e000382004051540320340c10415001c60200180d004c1460700352280c001ca040318001c82d5220a0f061812200d1100d54a95070004154082080400c100c1c11100321244407288000c1e6041650003444000014102841240c132802c2034440c00c1d0808007001040328140c003100e955000b850508001500081c07143c1e1014a14019070015000004103c01141650201c00740001c603200d602d003204d00c100d10f0003c1d5980b06440000000305a451a0020300b043c0c0e11980107001002c4c85800e00c0c010052055102100f0700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 379765008 1250 379763758 379763779
    0x15300601031b06050d020705011805010b0a080106260a02043e0d0c0309020402030a1d0a0b190e071203030b0f0a0911160c0f08120306101e0806030705 66
    0x3c41d000300c00d5410b00d070601400141c0720358807814140e0142038144040c0a0070a00a031803e410700c4019080300030300c402c082c0c1d00c01c0b180c0369803200c004d4205d4000d8410300710b18001344803c6c03411030000802007900c420b415104407100c0d000c15400207001c640032507451154144903214011808101c0c01c904610030034012418400780e02d9603002800040c401c1071510324071681d6403c0042030351402a488003d0880d0040c2045481e0700c2e141080390000c00f0b408008415803003040b00105003402002408142283c1e228000b0300058a032000540c01c0e108800407000312054031a00101070744401004030340c0c000c00361006203012011082c14040c0c1102c40b0810160b000f04c20300351441d10140c03a20102c150403150b1a0f180028140403100300d004160040501c090780c2084000000000c0c44641e02411090760300031002401c0d04ee6881502c950b0758112826440340280007440090f12528060954440010160800f54080f0902c100302c0e16141c07120909140c042040507003442200d050400c500f4014190a9171003c201c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 379766258 1250 379765008 379765019
    0x7080c0d140a1e02030d0f05060a29070c031a040c09090f170d0f060504060e010f03020d0609020d0510050610120507050f041403010b0915300601031b 66
    0x81e012400c40c0400d040d1001541100d40b04c0c400c0086400d10b00c490b41d8100895101000c444001e094184c41c480c2c480c0640741400702e0380c598142082c60640300700c220a078a036541c10083c03001c6160000310064039400c02010300000890045020301408401c184a18035a51078140703421500e406035a046146424604008000081d05800c0c0d2b1400c0c9a4001015201c1e45201005c0c00e030762440745180801013607050070040340070841301c3e80142c01501c0c01294180078982c1c441d11200c01c4c041c0c0c24031545001d640b104e5010005810140c50880003507004840101d00703070685401040b400550744e24212240ea000403555143c0c42074078410b441d0072180031105c0c9101c40305e60b400d005090380c407040c02490b2040d82e0b410203d0402e42c010300c12604081d40d0801900d07140c542c0d0f003002c424082010380d0241c0c040c0d420050810100c0c81c1c01e45000e0301c1420608441100141c00500344000c280b00502000d00d02d1141c4005001361815100c0503c4105004200400c4503604600d0804007031620388180050400c40007170305000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 379767508 1250 379766258 379766267
    0x30f120507080f0612010c0513060516030c0201090504020703050705011406010c0803061f080f060303070210050703030f1508010e060405210d1b030c09051005070807080c0d140a 78
    0x7000103103c07032611015298132000528a80e81000508259840c2071242d8a20340c1d000400303022002e1441200182c180d50b01d403400c0e6214403803c10a480c400b104e100b05800000d000b401da0900d047d0040c5406407415498030b02043c01c03030340001c1042e40410400b107074030401c0240c24095440380051046070b4925074181200040c10800c95100d0007420480e020000440e6a25121411650a603085280f0b081e100c1c52290003808a24080e22801030b00821400007130b2903801c0000844241660251000c081070b480300208881c1900320765012410141c4a541c1d0080d10380003400303004815606400321041da00d243c2240942154210610141d09130040703000c2001091001c140902140e02002c1c030100201945030b140281845191240d822481c41c0c43d250141240450341c031803c0005140d10100280c2e9940d1400781c0e2400402c0c45000d501155010003c9541c074414000f07032070950701c14000030382849440c0c0d03a40811600100d40706451a80305070001007c00e580025200ca8100c03040d80607602c6c01061500081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 379768758 1250 379767508 379767511
    0x1060312050c0c1e03070e040305070605150a2601050f0c161703010911090d14030c101b050f090121090f1b08060f040201031503030f12050708 63
    0x106018011520300290a003c0c40900c10010000788007402e002400082d2140000c2610881402445014008201078240d04402030080e81c0548885060000d0380c0d441718050f1a008040925844044640c00c000d5110150114003500702d0030101c01c14801600303086810480340e9009424035038100018816207a18842c02a41c11060740035041d0358604484da025404210800301c028130f0780d40d080040c8840b88110301c0195060b070703065180900050f40c0044040e1000c0c040d010300280e11180304001c410005944105d0f40350820070740000c1e6418411f08500f0700382041c684036007038000c0d90b484541101d10640051006502c8090038203207282000004511000031b1b0103040303005414001601c41e089914a074030b25541c41c4000d13041d28280302c00602c5141c00045102112402c94800170508248016106142c01d10015505078800425655580150200d0000400360059051503038459071444c001c0c800c2884900554040d4507a0008032407030700c80c020704000e003021152800d40d00d04420b018100d40e01001c900d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 379770008 1250 379768758 379768793
    0x40f023c1509061306090810060e150406080a03030e0c01081e0402010c0b04050a02090a05070e010c0c08070f150207031a04110406080d0305090609210706060e09010e010603 76
    0x6440d522220301086941c070907508940241188a20f000845c075a020f2000340030358148505a81e2081001d034048000d4505c2c902914103603018240008190483c03c10800244c198002c0012a4840d41c0d8018642003110310801600044d840b042038902911081100549000d800c0ca401c16161601e000d4011498020410070000c90003164045019688218079810784941c1056045420b41420316019950781c0348824101d005401100000f2080c2600d40319842c0320380120b4550641113503403c0011580c4400ba118121001400351101084480d0100101d030042c0502261a0740590f041c21000d00304445070203602402c56110f201e040c000504420400340d8805c486c5140d0512a449514110900501c90039401d07421034500b03100000d05d280000380b4107820840d581c4040040b512503981c81c903203a0400f100d085207550700c04c00310a580602c0240d103510580400e903280f141864401d030b58403030546141c0d40c88031301003004100902441800031310603942429070000003003140c1861941c0f545c42d0342c0c5011101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 379771258 1250 379770008 379770049
    0x15010509010b070302070b030a0605130903090b0c07031a010302090c0310090209040209150409060608040f020609060c0105040308060108010b0715150314030d0617030301090203040f023c 82
    0x1040500800201c1c6c0a00000180c5a44920345540c280c40101454424988203c9845001d48100c420b24840d110105415583d1410b180d070400d15078856a9014030b90101c2c00e03102c1c45d0000004a80103c8680301e01c00c4418a480d1200d51440c01040403801c40640240074101c400c01c00d002081e24281c08043c12100c1840e030250301d940c2003074000f800a008189960380c022007100d44407a10b21200c000280181c545d014801c10100c0d0701d4003000c0702c01315000c0301c0c020210103203900c108000d480c0007c0507003550400203103c1403402840b449580d080d02c40c20b039011408070b505102405015a0045c030418094124400340c00d04103421621342e0030202e04c00b14000d0461a5503006154005c403103c9240d01c02443d00480d02840030198002010380d81d034054803d034141c1500d099404514040595602d0b24100c10345402541140d003051040c100950001e00101d500500b000316200c01601c1d20000f60800b40740ca5210402c0c54009a10050601d0100034411a50101041e801da130140e039480d0300e06030020841690 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 379772508 1250 379771258 379771267
    0x3140105220b15060304050d030c090b1204050a020a241b0b06060d110904110c0703060c170f160927110f0a0e0105070206040e04060b2115010509010b 66
    0x5520260743e10501e040d0b00084000204001d021000543c5180c501c802c3c1d604001c510320200301250768078a18014400082c8040102d0080b00b1024060a80c109024000784c2e40e5603205540091070843c2c2c40d60141108507122210135104900d40203100c4444411414a640020300032840c1c40d960803441140140701c14112400706810342c448d0340c00e0358101e0082c104100103212100c8034600181e0002034800c1e03c030340c1c00d140c01300c1241c0d0000010f40d4410241c010041290b5402c41d6180f00161440c18021800c001710180f4503486811a82d2026014000b960b807039140e14240b0000c5010b00390059001c1c1005c0c8101c20200700600482d801c0080d0b101d5608070303400444912558802c074041d00c49040003401105010030760020102c0b07504010600c00c0f807076489054174014100010364960280041c003a520a405106c100032410350140f406921034450b14001030302c50300480001c0c104280480d10b4080b0b070554a48408840d01e020070804642c0758408500704c803598035250008210400501a8210204001c0b5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 379773758 1250 379772508 379772521
    0x90b0a0510090c030b0f0607050a0b0c130e01051e06091005310f14150d060602010f14091b010c12080708010605120103031b0c03140105220b 62
    0x80540060a164402403121103d1800001e01034800484458420704c208008594680380c54011031300030582c04006030810843c1625001c0070040001d1410300703048410003c40303800f80b004200300b0003d03101c804058141c0d94104801d01840040141c1d08414040d1a101101c0203941c80c1801e03144e545004171903060000d4100c04081310383d40148a6040e400c00e109a80c0040104c0d1220062268030201c100800300d45070784c91020f09a031230010301c200265180c00542030149420b1000c03081d4850202c80030020303c0d10380f60015800450304180d00102c010b07551010403600c401c519025a008040d0041d148040c9801c200e0038654a40d4503000d00700783c1804e034035050458541d02826043d8050342d000044000c0304001f01d100940203510444081c2c0006d0400000481c1c06401541600c80d084002d054901890f1308550302500e011b11070b170188000920609140703400003210328203140003541c400c07800342196032640c10712a801c8d0754001c3c10011020b10074041f41c00448102078038003464103400c0001640e0548842 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 379775008 1250 379773758 379773781
    0x912090a0506040b0705010506060a0804121103070605010603061205060f0402180a020d05070f020d080405010204081006090b0a0e07080a0209090103050102090a0801110a050d0209030f16050301090b0a05 89
    0x241d00150b000b100210700002c075214014040d00d541d0380a4002884903503104400c01c2640c0c41412100804141d100b004940424800765101c00f5a544900b085001051481d03d102e18640000c0c1046a1280d1200d0040c092964180202c000800c2550240c0c810514580e4500303803106030040403002d0b006401c0d0000303400e42d5110007285070081001200301c86141041180c1c240a507000010b02c44031242000d003c1028144940c079648054640c0b42d014045c0443d100740100d42b0b81311302800c02d4400750b400f8407012510100512000300f1118001d0000502980313000300c01e006881088000e035101e0030644904120200340740680f1036005017a440d03c40b20955890f49258000d020360042c0e2a085040b000020040180544c000e06a049080f5004203c082e9a415602e080e82c01781d00300c000790a03806204d02201c00740980d0141007561016071026040c1a0740d18042440d210a0240301f0059900203600c0b24002012292158007903c4240c00034000d007038241e04e401018003009040000171560300c2000600c81c082c04d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 379776258 1250 379775008 379775029
    0xf0c010902060403050d1b0206071e1e050f010e0303070c0f05060c07150b061e04080a1a0a060509012d0b210f0a0b15130608010509091209 61
    0x41c611520f0315103030304155513110410b90004000c141e004070210346280004e510341a415034000c14240c80c0028030359856502181070055403901031101600600000ca505202e4911302181301c40c0d4061351a21818030724541800020010a581d00d0042115103402020044075406200c0307043c10110b48075507241c05410601c807282c01400074003401d000e204800800c04014550703980541e189640c4408280001011200e0395040300d41d20172420000076100404804035482002188c84946081c031707981380180d13804c1280171f08041790014200da00c8240c00e4241420440e07040718008204020302414000440c243c03690600035140640200004827540310313203040c0c421a0a028400500f41410359401d903018894000d2407285514907520700c18a411400518507443c8070300700140042c034640c0c54901460005003032002480b80c1100e80401c1010144030001d000304000e250240b0700090152400c039004100c280c1c10b030816485903403950b00b8413101c1d10002a00d56401c2c210000d10581e5221030a0004003180c40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 379777508 1250 379776258 379776263
    0x110f040501111e07050a05010f090e0c070b0408030a181a100918120c230304030c060c0302060a0c05071b09060303050705010b1c0b09071710110306060f0c0109 70
    0x14040b00703d10f503c0004a0400e003121780035039011007280d840d200107503100c00201c80303481c0010350420400c01c0b20081c031111003500070706900d0120b4504005512250400303101142e0580c1ca04e8000418080910220b1203040d502c0d0404000c40000c1d00541e607a00114581c0420520001804890200e6400200b07084510000c0c0b40e01042046003000c41c000c40b005820300c00d81c1c140c4404c0a4140703060f1120780514008041168804c0f50a201c14504520340720443c40703694000d10a500c8203000c007100088840410502500407504c41c0c00401c4020300e0700900c1c1100080c28600b44c00d00b440740c0311801607040001c0e80c0181d584400404444144000d00541c032184960101030f4280c1446400014541c1001c01084607501410080c03040d849880c0c14481d424040b0001070303000100340c9004c0c00105a4078400540c11440401c10341da40765035504c861b1500150074100c014140d801001c2c0590641883e4820340c1040000d0080d140d00707502c1c0c4140060800d02841c1c0d1003440340c410001d65043e144000b94454000642d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 379778758 1250 379777508 379777543
    0x206030103201002060403090602010e071226071403040e01090506032a121b1e0d15050702010b06090d0c08030c0304030b0124030b0303070c03050d0201110f04050111 73
    0x3c07100341c0000d5444a00750350039004034681c000046105881030142c00000d0301580700400c0043d2515002607194018242d0682c3d0306c40046a4000d00008501c2d00448c0d030020780240142c441038103081ca44058000e219065015a10030001040034140a40d00e050459000c5c820000b01c0f940e54201107400c2180403206540058422031007400c241030721b00e420f20b8940000b5916100100d4220382d006544061000d0440740c10000c9200700113041c40e24503407030180703407281c545072a08009014000c5041b03a9108641103134041c8000207130290816503485601c2d8800780030303c001d10048034204040350040c411414160300032942101c0720014000000340c0f003802084043d085960318884003c1980d22504180421200140e0b200c00000c0c00440140c09600303041c0302a8642c8258944210301075000344035501c0c80382e40500081c003180000c40d0041001c0801140070310702414034036021400007403c46400d00040c2150042c103204c0c00076414109010b90f8291b070403e007005034001c03000c500020700d030044440d02c0c0751184 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 379780008 1250 379778758 379778779
    0x120905010608010e03031003021c050d020c01140a08190e0a110117100e04060b210106050307030f020402160b2d0408031b0f0a03060f05040603020603010320 69
    0x41540010300300c80000d0000c015040841181315103074441640c00d09905140c0c40300c240007524090780d1103044c94044c1c41c44199048400d595050030701c0c6040c0103050140e01310b901118041d503048409510160108800c962a048483c48003a14030b900182140f0304c518940d5803410049411540512440010001140c00d0b21526240c2072004401003e012400140d00031046401d6600724014075006a10500d030900d050360409040601100c40204155102c40d11001d4000007600d90303e10088201c03500035111004010140440b50944090740d01c4580280c2c042d00041010840ca4030000c0c201c554101c80169494011881d001224024400050000c108043c03c1c003200341c2c0d5080844c0400340607030604c204041d034082000f850240d400c80f0042c000d0101003000403901c1451000c102e0700700703024080c40b0b130904900809404c0c03503030172010003035010903991407003030250300b0480000c84010038049906204017402c540c0420114001840004e046203010301d203282c02c40070304000141c801c1e0300182561010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 379781258 1250 379780008 379780013
    0x209120a0204061e09020d0204150e01020f0f0c040e0a0614010e060604030f0822060c050c061603080c2205090601110c10020309030a0c0f150c0f031209 67
    0x11440d680340c080740709900d0300c00c0018140000c440c8010790f4001c1d00f1100110640381520140c043d511804441060550800c07000c80e072000010086200701d4041e40e02d00ca00b6201410000e4904003583e131809450b07500a64145c07a4034240003801c4c3d52007070019a400305440314040c088a1900c1c03460340000f8035107402e00058202540030460254100c484864020b2405c0c3c4455003444003030321460001400d110342c10603c1c180441c05060050660110f000f06c01041e44d400c0c0100e404050100c1e4106030006580c00d440902400010031130190b424a00b207d8003494001c6440f401141c9103000d840040034005c1c14000107040a46079000e0b20482c0c0e02c000d804070840d070444070b40d2900c01d103003501900f480b5006420209845511940c0c140081e540d59600500c001540d070300410004450303000010003144410000f00d103071503e0a02401806a2041c05050325007400e200381041512000d80125445c0300031010346d26521548030820b942030581261950704442c00c6030804561824101d42c10b1200703d8141040e8408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 379782508 1250 379781258 379781263
    0xc060c020a0b12190b030618030904090b0910060e062e020c09010b03071d030109050a1a010e0c04093602090105060414130e07080a2919020912 63
    0x10a15544c000c601190007202200802c07210104180d0b034042d40003500140307041031800024280c61441c2d40c00c0780d050a5450340064140d03200850119090020b203000d102c41d000c81044401a65000060b0612107682031000701c1c020700c1c3c402450103114511400a80c00d4002c4000c0000000c0c0c1c0e100b291070144000084006076803146689000d502419a55000040b130300006003ea0b40905555520194026142c00c26481b0341e0b5400c2058a9240d541c0c0c80f80c00d80003407030030040c00308a1849510401514942850400d2004005038048140d440e068003c000c00c0040010445061700d000c0140040c07096120042106541d418041840803802510010301080c8014007604030441c1c82110080d806a8840d030502043d40140c1c42440e40c0d0100d00d030200342162804c1d41c43c0f28001e40c075122001030b0b00c06004459900e0081c0d40d5000640c16008071080f401404044404404004484042c1c9581344010001c00300401600920610150f1480a90004187c5a94044507000800288951118600344445a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 379783758 1250 379782508 379782511
    0x7050301150e0d060b030f0124080606010512040309050d030302120705130902070f0f080a0906020102070305161406150901090902030d0c03050409060b03060906010305040c060c020a0b12 82
    0x11810350041c4021040c8a42d0764035010180150800081060325959400a009110405039150040c10162000102c0c00d2050703807500400000740030491460204003500780b10310758000e805e49030840b204001d0070f66004011600420650113003003a40740d81e0350030115180c0500c1c0d0040f0794130120700304400e0240358dc0754014080c442080c43c0f03039103c41c0d20340001c159102e100e520503110160350440d40c00c00c0120002e50141c90143e00524a00f201040e0580d1607640784a03c07241c04880929002c200c441005501c0300d42c1d00701030030517800210300e001000d031000780090140c62658038689100f29004001c200041c0d1a1b4400800b80f8001c8079210f08108900080080582070524010300c0318000002d0707460f02c0d90264009a80e00600035180d4003032101002c84400c454450290103001c8100000a2900c0e00b0b4894100106820b05020b40c4074140003040188a0201400f1079040508020030f03c408182101d041104072401414003100c05465480414106a0a40c0c404070f401c140105601070b032a610034000e40d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 379785008 1250 379783758 379783769
    0x100503070206060901080c0607030e0604090204060809030a0c0f050c030a0b16021606030e07080a0605060f0607020a06030b0312120906061002060c090a08060702012a08060d060b030607050301 84
    0x86109950b58070038481c0e80ca500344034421003a4007140d40740089003031820081540c0b50081c42c4c4155904bc414012404c2548194003620046034001010040f5030f520160340740e0080001c00c00b80d8a884517205008109000050001e402e2185107200d040811034100100d00c0c9030080030341510704c2110303581482aa501421100e061003200c0c5044050360302c034400301e0390060103400054040005420100c0403002014811990401413050720004101078004100542d000d030710440006c1031a240581c01c2c000200d001032349590084105014500059a90780f481350282c1d4198a0000f610940c01d100107803611009022040d80e07820300240390039441b140351924502c01c2c010801100d0240e1500300901206000380b0f0300300801a00304c5008505040d01002c002d0501110040801c91400e441d80b82c40b034109401614040301503995030072407481c0030080085032511103241005044401071068800781006000405481c0314140140e02070b010008140d0184e98141800ba04866061401d500054900c0e07100b8041c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 379786258 1250 379785008 379785013
    0x6091f1a1909112a010603050616090603091e081e040815060306010e06030a060f0f050108120d0902150a020a060e03090f0d0c08060a1e0e030a1d1005030702 69
    0x3c81081440e040e049910320078000002d00c180304442c0351445079080c124001400d582d5259140000403460800c0014002c00040d0340c40c0505032684440500540100c2c5d105d40141350500201c0c3c00030608240c00071041220715410764445050f03901e0451038501c0780414100051203101c420b5031034005000064410360790f00e90f0441e408500100d4034100d001c80c2c111600c0b0f40c1a80000010301c00d88103400d000d5500150081c044418a0005e9a1201d050740c0740846010802036580b941c030302c0d03421800c3c010140140a240082c0c945940c01000d540401c4c8a1400000c0059031501c0300c0c40d0031074640d25040c0c40b040d44102c5085840703244601c00217484200c441000c3e501141030031000000c0c0b1002108840344154003c0058816980d000140244003030120400e40380c00089960000c0c2055080c010b26104541ca4a00020b066802c04400d44503d1a0510280c510b80d103458424014104008221880121717a030500a0844803541c018000c1140c00702440c0350002c19080c13040400d150018080c40c0621056001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 379787508 1250 379786258 379786271
    0x11103010f0e09151902040b0a0e03061302012f011d060a0204080a12020c040501080c1203031014060f0c0109061107112101060b070506091f1a1909 65
    0x9803256218450042c0c4081c80c807821000c1585c99869211004080250f03070805410310b96a41ca00301030035045181e5400215040c0c803029070340b6150500925a0000012003c041e800c0c40b150002040040c828075845403042c038010b490401510113100350003644860000901091003101814510801d000140e034015104e040c0104050fa8001e0003179905a40c00c3c0c0000b00011440350b2110314042c200e01d002034080d406200040c10894685008040c0640040c6c0300400c010031104042c030400c080103078605529034005000303010102c50034030740c0d6100315010840380802242502d00010094800c1062404a80c40c00280b600d0703c10b503040d00181030080c0611070810008000303d02a901c0c80c811440010300030706071303c0308814891900b10042d0b4140e0342d820302100d031712140c032803801403c60707030b46401410324100041800400c00108210300c5500a0085024162001c3c0c5c240000c4d8100e040400342c2102141c461060760791454010304000c00701d14008003180048403480500d4620542d00d402044007040c1010b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 379788758 1250 379787508 379787521
    0x2118151506020a02090a11030f06091f03060b03160e011410050a031a0d050114130314071a161101021c18020909060906070309030c020909011103010f0e 67
    0x40c030840d05290041d2548040580c208000c00c0c5008080c0d071402551084444c800d2181d00001e5880350340c507082d0a0100e814610704200360800b0081400c01882042c0701d400b8000000008054120b903032203200400c82e103030000c0c0020300b0040146513800515141000000d011034102d4103590403500b62140602c2400e1204007444600300070b03400da0b000030030401c000c0c075184144241d000d540c0000714aa042031185c03a002001401c0103203030000658a60303440340e81c8800d81c402c3c42015181c0150001210000c4980700780c0e0050300000b0302c0080c084089602046000c01e00099100c0e1503e80d02d19600301414a2a0441e03039408401025059000010340800e021140c205051084840d5201c110036841d40f007000c804101c0c1c002c2c1003020180204c2000c54008070006884141c413081c0a10079000240c142c4d464030f00217007490000010a50010103007440141c1e80425001104450315130703019606005d06a85590400340585075212a059203000000b00010f0343c141211001400d03070321902e00301403079900d030003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 379790008 1250 379788758 379788791
    0x180c0501090e0c0307030915090b06120a03050714011803020c01081015020c0315010e2203050c19030f020f013e04060903061b211815 59
    0x42c040e40c901c140303010000c50107890366070014650103c40c500c0c1c049a11a100d81d140c03030300c11211458901405460f803551604018040c603110342d0000003036583d07201850584681550b00e0068950142c207015000a46030144004007040c0f01848680b200248026401d582551801000c4050194010701031008a049650720600c3d0440c000c03802e519400411500701105414071481d942d105d80254414107004050035207060200082d080414805483c00b5850a50400d0807100d0083c030000040742100d403080c600100c4144107412190301844d041d81c5441441a070340741392000e000700141500b40c84403041d10804d6401a5800411060b607400c1d0303198201c541ea6550b01fa03c2580c5007074184815404503114000d2840c400c0201e0701d28401c0b5500d00650051508880e8070350050300030100080e0144018010701c100d6000c0e4088100e80d280840b4401041c1400081100c0180c9a10a81400702c40190320741488480d002103402c18070320141da00d8601000e242551b410448503611001440c200398040798a581c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 379791258 1250 379790008 379790027
    0xf090605120d110a0f06020301050901081203220206070b01140a050d08130b03070509010906110312060a053705010210090825060b060f0913020d180c0501 68
    0x1140d00420359501c00d114151143c40d0781d002c080006100300400000800c03c40409054454007800b00141c1c1c0354141028810940d40c142c001d0040c030341c00b48076406c4d040c2c424101140d42c4480c51042001c181a07034001e50380d042645040c2e01a40c080c1002c5181000e01c1203410f01a07040754810040050400d4408080c0068000c2c0351080342d03072003100510168041a00040100320652421a00041e6140c5900e40e001c03040d0400d6441e500041e2010410703941a5030400c1c240005404282412114200001e0940d03541c3c0c400c131601b20413450091008901582c41d51000300000c2c0400034440f1200c16030214040710416654411000076030709140700d04407815210172565050341c0c03041e8050314404040e5890039001d001d81c002e0456203040100f1410422521051449840c80340441134041c0000c01800c1110980d04c0d00341501d0310401007000805c6c2d00d00000c004550394004141c0d0040640015010854000d0081086d4805030300d04003c09102c54003c402d2800c03135028410b818286240d0b03120001150890300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 379792508 1250 379791258 379791289
    0xe060f0c06090c30030702030604031706032e062d1d040206070317010b030a1a09070c03030603120306051302040b0a05090d170406030e0115050f06040b040f090605 72
    0x100307200b0000c0100b424080c4d54000c031442500300c901e000540e9003c21718003041201e0607000104000740070142d000780030140b660000800c070018809440703c521204005801c030003460b11240d10401002d50a40181d402200003047ca0220310422004504c0c4020b104140b02c0000ea106080030440c0400c0704d582c00661502803c0b038085803006c141c0d80315130902c509a84540d500350144107003405050180c4040080c0702d4042c06024a03450744034144403400000b85d803074540b003500f1003031000e145c2000726886000007160f00031480e25244070785c04014182503000740300e1904041d200300607a00c01008940e415030044400c4441c01c5d00c0a05480480c042038808a0195000300702100c0c02c00c200d5903112511890280c410042c0082012240312120380d41d1540020007104030200103200403504002c40d6405100c1c0034101c680c00720080c0540c203864080d200c58a405401550b1040300d109417045015118002500d0150a00180144ea910f454548600404042d4030400c1d848c507017024404210760a00007000350031580c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 379793758 1250 379792508 379792549
    0x100305011404270f0501092405040209040b190f021b0a030804031d03030c100501050307030b0f09120c030403060501062a03051611041103090d0e060f0c06090c 70
    0x903100f402c10462124242034030b010a42441a0740410021b00ca0401d565205802a00745410341044440f5501480481e00c84000e24000800c809603c4284151750300c1a80a078084900d44d60300b086880103590b00c84c2d4941120b900d003049a140c2080c0e01c1c2d009140340491201c401040341c0548047c41d549841e2040c00030000382c04a00400c00007401203041c010f00074128421700914401c1c0f0400b081c519088803680b000c60780d000c00341421a00340340d88074140c0500410f90140000a046450300700d842d21014144c1d9440704041400611041002d220400346c201104110a60b00c468002200d9075030341090109aa1280c41c0c0000028014080d0464031081300201000101c2d1a0706402c8410044014882c20ba0500908002e0aa045625841c0c034240e404e21070f0903d044550750910511085030f1140b00000f00000040081c00807a80000854545580145c41c1816114070414080b81540c0284500315400704000f01c2c4000c2c403024007080041c880d104c100200c031640c82c0168200200c9a00c100844c4c09001e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 379795008 1250 379793758 379793801
    0xf1a070f031808070317010915050f04020417031c05070f0f210207051608121303050a0b16020a122f03120912090405040f02100305011404 61
    0x1402900700414080d02d0001e080003121054962241c150300030401100060500d005001c5007543c03d51100d0301600403101d00304048071a26507a00000100307405111701c1500c0c04106001d89684680440300501042c01d864000003201e00c0d9a19035a400082407480700515000f80002c819810344034092040740782e603031344440d5001210403d989210509000201700a03092544420001101c1d9800d040316107207040040e6214030303605042d820003a00311134480310122001d9041000e01800110b000d40582409525503540e0600820140c4612480d0f20003401c0f40038401240050207114850a441200310311908002140d002008a03254000e003030b0300614030004480c4102c450740c4660708005170031220103e07002e11240e01501c201410300c0704002800b170503030000a0a14404541c12212600043c514005059241c5108100d01c140d014101580c0d000d07aa45d14005401d11000d00740e41d072205038001c1c1604a41314040200100904400d0140340c0072101c910007049901d0400d440740780c502500d15540070100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 379796258 1250 379795008 379795037
    0x5091f090e0a0506092d1f05030309090402060306030312010902031e130308070e040207050a030f080709090207020117040c050108010503071235030105030c060712080403110a0f1a07 80
    0x2c0701e01040002800f01b041e0b1180907042c80d50b103585d5070040d04078032503c1d01c00390701c2101680e103815000c3d0041402030300107119121041e119030b40c209030410b0b81150526100d030b0310348002c00d1a6014117030b810701c0500003c1e400080d0300134040d4009c50261844d40382625014014140950b00ca03e41510500e101129414000010a00c41c0a500d5001405803800c405030143c244001340698202c400300f92001e40081d00781c0750406401ca0414920840c0500700900f85142c0304602600b0100d291091030083c1c1c0e00000d241c41168401c0c0300e20748070601c1c130b490b640e121030510303003445100c2c0809402114007203a0300c0710003c45e103450000758007000c5614001c1980c0302c01950b650340c000b140b26050408002404044a41600140d450444400741c09a145100c1d071250700d40b41c200751918040d200d86a010718000c220000104001e000303000142000350030061140c2e100c41c68211180301c0405080301c03c1d070183c40c00120810003400e00340310310796020303107601e108034500c80d07045d964500e10a80d82030300401c0c00034612524 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 379797508 1250 379796258 379796281
    0x1121101030b191508060306010b0c01090b01030b041b05150c0a0b1f090603031e020c040204120303062126130905090a1205091f090e0a050609 63
    0x2002101890301040e161069404140c00c00111800d51a000c2088082030000c035074401c029407142c805614029202e401c111003c00d0b01c030341c018060303000034000000b42155080c509400c03580300194086910723585503030b40303007450124024240c03021140350301c400c1c0400030100001c0020505a80004229021804108061103000e81c40044900724034028000d80d8030225802c600c041784070300c8a02036084034403503882160200740e000355000b4205136803800c001400880d501052202086412038011810301020072030176071800e0314034040180c1c410300009000c11030208428105076010b20a44040c040d070354031001c0507220260b0846011031415005078905010410a5100b400722860154880000e550b84103007030440da07070104003601c00350248218200700d0b012080c070801342d01c0030321a005030080205a544500d400504840078400304a000319010315a590b41034803807259200700035443c004045c1550750240c481c020500c40c3c82c0c040f19440000550081050268920800d402040700004e5a1907822111 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 379798758 1250 379797508 379797533
    0x30e04020913050108010219031103062701080715020102041202060906160c031e02010807050a200105040611030c040e04080d0207060e0d0908060c0304051f0c0e0402030112 76
    0xa40c460306410b203280180282c0d1041c1030103400c010001694030200c4800001c1e184100c0540c5804040c80d20b004100202031400a83c0d030400c3d422201b2035000d80c880d540052a589115100c6445409200d00000d90180002000302c200c404d1718103503080490040700168202e015921841610141c40780e04100186805001420240e000030811410058164a03002682c01c1d0541d00b1110424066002d00c28810560044a85005070700d40141c87c2c640c8640c0003d158403030107800314052010214442d04e0460044540c0e4440d00d0007440304941a04070b001c009406000d042d00c0950344980741c90080100c005640301224480d03003080710083d01e0540307405250880402d004205480091040c0408580402580020aa40ca008034008104801207480300c0c0d0a14402c1d00d01c920070301250080401c2042c0000c1445984540f040b41099200d40d51800c01d5418545000c81c0542c0443c84507020740d0a09296a021019101159036501c20503072500080c0400c80c4070a00070848040c449003481d10000b042ea08021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 379800008 1250 379798758 379798777
    0x8060109090f0b10050f0f100c240f0501170a03081f12050c03031c09150c02030a09060c02090a0b0f030102042303060103030912030507080a080402030c030604030e0402 74
    0x80b44000107039107520604440a8600c0744c452641102c00700943c0c505202c4110200780121000d5035015440c1c000250182200c850050501020380f00380024030601035840c52070002049c8410140d8a80e00c40980000e2a648100c109540c0c6840008642000841001884200440300401c0040c0040d2410ba84c3e0190003040524828010007000074a2080303c18000300402d8020851a0303003d03098640542001c4a403050180030307038420b0050b14440c1e001000c0440034030301d18510001d00d0b0704480c1014482030044030800310210b810030011440c078940c0040285800b030400d9807240c5c103171a181d5200305c41c03060070300c031000c1c3d407000c00c0354085101d1642076400781c01103e00081c40d07040c4248110001c2400da0308a9881855200100740500110210b260219007001c90200e018202c00d606503038001d05a8509802000130303210401c00540e007054014000c4842c12504100c0c10354071010207520080202c04211000c82c064001c03c0000b02c5182000548240640d501d0344030a0465141c00052100941006800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 379801258 1250 379800008 379800023
    0x80108160605032802180102010902060f1e0f03090f06042112090b07030f050c1b1204081f0c1d0a0906180b060f03130f020306100806100806010909 65
    0x21070180e500d025041100070b1343c04e01c05a2600d00b54401801c1c800c54044055041d6410034147c200140d440e1400c079500031458485064031f442492170780c46000c0d81c01c45a03031a5004400a40780d103400030440091407086486100711686400d40010340d0b81c42d000282c50082120042c491415000507002d580c0006015091a01c00881d100010310002030321541310042c0c17400d18180003484415070745070142d0b60b940b2501540070701c4103007010707521607082d03109130010900d101d9210300c6aa8917840c401d11410915185129085480d651610306054880c031046448020001d2002c03095002b800881c0180400fa040540f0380030080034605800c26086c000480316183d03c03176160030000c40c031007480c0e100c0d0308050051003c0300308007445102e0912003102d0310015100d01c900030030300c00fc1c4808011a03013200c2d4080c09181c03e01e5038422003440d10900440560390029410700520040242e0081040c2d441c20441e8407100454560b900c4200103c00281114040c8807880e8020303000502c10380100da0441c1550600c600103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 379802508 1250 379801258 379801291
    0x12150402101e030e0d0f05041406130e1501030c08060d11180906090a20060d020301060507050c0108090a02060310150c060b010305060d020111100f0c08010816060503 73
    0x40541000d003074518101c0c0801c0d0f40c1c10244054131030410840305012401e00305a0000d401400001d00103024074464891018400c08140c105074895400382c40508420002020f406500daa1494501d44800c455203003c094000382541c050b58800d0191303014100705a16000903603202c1c2c600748180d00c8500c10080d121300400711131030606a00d43e02031806003c411051905450b080010401d0b046c01406840749038150300031104113010481c03074850340c1e001200104a01c26403090040210f229800341801c1181c2c914400310000441d0381d007110040c840144200280e07210400364030019900b100054460003c82e602c030034822001414082d0003590003000e4400d032a18003e0b6514807122140181c00c1c0210002221a41040c1c10040103004401e1082c9007401c0c144035515052002c282c1c040c0100c00c02a04200c108044007010000a1100c0c51260104200601020142d100481c01801c00c9200010004410b07800020b805100414a10412060560a10300181c80c0001c122034640018140d94100c116444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 379803758 1250 379802508 379802537
    0xf020d0519060b060712051b1b010e011403011205030f130e1815070c120503060a0803040f031103190b061e01080c1804050f04021215040210 62
    0x86108500c400740a216412041032510006482c0700700c88207800385a007030041c2d100003400e4516280c06000f0a1924948802c18900710713014154017a442d0480c01d010782e201c12051144410070000c0091000c0c0c803007240c194000001100d070341c2c46141481281e02d0062005101084200059050140c0a4011a403e0456031502c81c150b0782d120501181d6015076580b42000b0621081d2245a4044e601c45031210399440203042d10b41d01c6111181c410001c5100000000c1d43c1075000d84055032006420001325a40b001400c1400f801c158402d03a05a4420301400e6400076a4823400401c45094441410304135815a14503901e5909002040005d680d1502480500901071600c140c55400303101d0181403184001d01305030080c000240c4100070981d00c05031480c1041d003040c3e6000b012098105428281c40e503a074201902c84226280300c410b02603031340f081c140000d21403039240e44584d0300c0c041c50080f10307071082c082c0d0001d0109585200d0514040f04402601c00020058580704001100c480170900740144d1048821 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 379805008 1250 379803758 379803763
    0xc04020c160b1908070503040308070909020d0c0329100e0d0c031b033f11010e01050103030f03050a0603020909030a080f100317090a060203040914070c0f020d05 71
    0xa40040702c4000000c41e03a41c0340c0402049440e80b0240781400c01d4003960034143d0000b00340384401080035040c0820f80340401c00540c070407203035003004100240c400c40d00c42c402c1c034202e0705c041c1007c800e000c00044d003000c85502040c9506454504101c00ca41d046103540318008003400741410310f201c00700051042c840a101042c0c0c075030151004040748101402c03910f0500f546400103c14a1301a03401e0407aa038501400c2c400240b0107040700140c551004612813184109a80380400c501140c2d0415441c92040031010122581004649007508020300080c0481030301203904c41e08845d000d1101400189151190600c0c060180d1301c49078000e07621002c04107009459402143d01c560007640d489045a000098500c40d242d03006010030f030003102a2141c00010706080b0382c0c0da881d26015002c0500036002c00c5462085013000c00781201c2070900040c1c0b1100041c1d6071078074040d4407a0001c1c03080c070101c0760420083d402c07a0105030001d917104504544540c0710918091b164844a07a00f0348004030f8120740ba1310000400304008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 379806258 1250 379805008 379805053
    0xa0b0303040807061805090f25030b1302130e040c03020406030b0711010b01090501030e070f0b07120203130612020c070f1404061401260a061d0402030c04020c 70
    0x1140003d041c100e1400c10000c0a0745503c00c000c4001c120203000c203001035910f0b208401e13040701c1c51314140e103103e44442c901c2420a00e5050a203040c41c640782c02182c50840e425400000501008440598024088806841c26845222400b0516400614091104034500d02c1071035041030194900300040c644039404a81214240d40050310700444250401400c3c41d40103004070f602c0b005041c000e01c1110b8000b00040c1c011030701809001c0c10715403151505142800100642002171007407228001c0280da03100740c10841e50340551000d99007007504010150009000000b1a0005030514400010031440c05008403034290300504061811502000000c10781201000008080d0507200c501c0c518481c0b810174417916004104200a0086003004020040c20b4401d280480c0180401e00f015601a114101e5211000508160b9000c840203640203000e210980da038010001d8424a12101180e2204501603121204049030001d515505c5920503480d98103140d0041c20395014400200c0d01c80c09d2001c0d03854002481d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 379807508 1250 379806258 379806269
    0x6130e0f03030c030109060603021305360615180613180b0a090606080109020f0903060f10051804030c0303020c0d2d120b01091a0903010e030a0210050a0b030304 71
    0x3e02000601280210b485103400400c0c0a0400714902040d4200d411581c480c5c0c0e108a03445840c51a0304010a00c501290011081442c450440301d20200031744450110201558514000c1c90031402d0144035003e41c2d8111a42c0b41d00c0d40302039503d03041940042116030751250340071540d0303903a0356000010700040d20050b25040000840010680c0790a000074040001d0041d07100810990a14404000468115402134152000114050b90b560700004004074244a9a41441e0b098800c10040020900b114194213010300c0b111a650307005d03250b8920412440e100e10140c006c0030b02c040c61000ca40001d02815a0205039886400c000d401d0003088940b1a0800c10f16483d13080c08036118030b0301340c54113008441d1101c0c60040750200030340000c0303000c503402050034030503d011114481c0e0b60f080441c4036a001d00c104500410890000b074800c3c082800d1100311541005204a00030f40c201400b2101500001c4213039081007140b40c0c01000e24090a410102c0a442c01030082c4407038a80e40c2c4881c808584041c00108003412 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 379808758 1250 379807508 379807531
    0xc0304170a170f010605090d0c030c030309090f050106091502101802040f06080a080f04030503040906080c1f1206030f0308010305100c05070b040203010b090f15040506130e0f0303 79
    0x503501407421038850801084070f00640c88520040c1300361130300002900d9813050306403102c0325840c1c01d03840e01d04800d03405504058551401140c0020405610510701015198081c8051110100b00d07542003061315001c3c0036a40101e20055401e00c0120011010107045500e1441140c81e60124410060115407403c01d6500c80b0001c0350403a001503081c140a0150784032401d020030441d20b450a03903140d0315007000d184010642c180c0050300007103102d2041c05442c00b860300b1209499545035103101c20070007002c0501c10780f0510701880516030b00c036107491820380c0c041340c424040014071000341e00380888242c280e1151012003559100008008078080308884480740f40700e43c41f03038040d82d419400d00500c2c180301c1010103a0558100200c1030103076684103082e200c106a000d20412201d48540c80002d014000751803841d50001202c00401c0480a008842180074038a61003d0320b0002d44034100780400c1e41c104981c1c0319009a4449a000420120356020010020580098620220015410900351303841a540b0640d2031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 379810008 1250 379808758 379808777
    0xf0c0312050411040b060909010e07110d03051005040b0f01030f0f1e050609091903121a010e0301230c090d1202070b0c061b0f0a020307150b090c0304170a 68
    0x44c00c2c5031054140c00141150700c1ea00b40009a00015190b001c14080d800c901c47e00c100c003003844107014002c02c0c003a124016080e10b26616404a0003070003024101d903000c1007944000070008541c2028441c00240394030260604070018800b0740190045d00220f0560b41070f02d0781d103821124550304148501602031410383c1c40840f40000e034030014801d0300e00240005209020360400c0c00341c00d5000081c40900d40a02c3c810194014441c0d040c20f89102656a001c900240c3c14912a0080061403400e41d1030f10001c2600c9d9003400c0303810074060500700c03192100c5000c541c846c0140300411081022804660220381c102509141c00d1899000c101102a10f0404442481c001002981c4c900c0c0c0500c080c3c0302408240c091141803401091806680303c0b00900640d01075070602c50415040ca11170800c44203030080ca00200c0781d466915010081d620303400104151a004d07243d8040349241c0c0e00318011035805050080044401d03403601c07200f00026500140080700d10011074040a06803400c01ca01410703400d0b040d6110040340c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 379811258 1250 379810008 379810043
    0xd080a271502180f030c10031802100512090303070c060e0f12030901050105041103040f03030b030304080a03030e0c0114030c041d0702010c0c0203100c26010810020a0f0c03120504 79
    0x40504d450b84910a4208114940040c1c03101019101c1c5035241e0725000c102c814109044007100d048071940079411003050101e02680c0d40e0407800500714090700100c2c40c0065982c3c1d42c0c0103502c0380400e0741c107140011501d03910703100807607055002281c40200b40c5055032803280300071025520706050542d00301e01204002c802c00c16061800c0c0318203401400c0646040c040d4142d083c01d00c003682d2000900c0142505410100c0c1d200b454444e5000344c01d0700c0d0700a411a80d50343c5e120740199564004148003180000e0238035841100612020030040c50130791040c0c55051489448407440901a00000d080b441090814800011180505400702d0b282070b2070045205020308110100074203403145050a8824400c00c1d10341600140c4000400c1400301c00090740000c0d000401c0790048030010f1303190b4115040c8140d04640680230240c070b403009504844041044610880060b0034060580c050702c031060300072807140540307024034600a00022030b070300b1710038500f0200603030059406404a0f14181e40680d854034144801046 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 379812508 1250 379811258 379811269
    0x1030603170f1b1f0c02030d0218032e060803030a090510060906170a1703090c03030705010b01030606140f0310050607060504021018170f0307050d080a27150218 71
    0x31095041071040c4051703102900003950300e201c0d00720380340115680010840c81e8103294001504d8400e5009050750030f4101d91701c1444403902d20700c054691034a01911042d01d10942d5074890007044954042c003550440d030fa800310000081600b510183e0742c0b0300a00151004440d5103100c0c50028040368100040c2c06400c1c12202102c0782001060f203040ca0340180540d10114601f2507400d10084411100d0682d69614050381d1401c00003240340294052002040c28801c000c410740081a8502080e6001c01c0340a650308012a8a24642043d240b40e43e8010082c0c081d008000500039a441600218101c00456848020644561100b0320580716a9982c00902045140807030b0801c645a2551515108151248000411202e0036219030945034044c50020a910705082c00000e0f1002c00c4d25084e680c950320b41d820400d460b007070400c00040000c0c26080005050030010300c104110406100928140745640075030f80b205428415800381e0302d1078607a65402021000394001072624054808015802605210071301a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 379813758 1250 379812508 379812553
    0x1a030103030f0e13090203070f03110411030708070e0d08030702010207170a2a020d0b040c05010314040b0601020a051204060e041b0804150c170601030603170f1b 71
    0x1810401000c8604280b44d03903540d500d07100071480000000c0c0004a91001034900356190b4031400f24076054080020500c83c9082d6810039a19007502c080c400c210351416011050300c41111304402140058010a1402e842207210070034400f000b030300900b0103c050761100c42140d00300720b0310310005030340000390402009442e620303080d811a101d04003181018902c010180544560075029071500550003006803650514038215411a80c001d010011031403060304215415030005c0310180c03280020717000006250351082c031918140c0b0003901ca450307050351202da0b240c240700c0c9000ba01a40c1188900381070180440c03001d00246011604014405a61f64504071001d0070484a0203401781c800c51905e0650401c4c0a607102071003503080320602c2e00b110b460760b0302e203080c43c040003481c620740680c80d01e404250908203400c001d00c60000450900264810366500c0e0044059801b036000084c1441d2144801c9016440b2b020050002485000f0401c1c1c10a41c12060314890180448491501540060499000300700c8910314070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 379815008 1250 379813758 379813787
    0x7030e010905090a09050c090423060105092d0a0204080c030c0a0e070516060203040201030f0513030305060102011e0b0114040602120d06030510051012030c0602131a03010303 77
    0x80072040e207020300107600058000c1c408218180c07107051060401c00300340000080c01d41c0080011080741041e0030b0003140022400307a03c002c01805020b90500281001903203c1c100c0d44028040541f5960301c40c40d41d07402081c3c804058030220308060403000710b41c900002d134a00c1100f211000503142d034a004070940c905001e04603240d01940100c50411aa61902c001880962b50b200140c00b06036114504101e07681d00c00d803009404250110401201005000e400541c0034034009d036418045001c00c80252005c440e01601c2c007040303010300040c42c64001ba02a80081d540f000c0140000101c418440704c8014401d034040011101f1556160815902036810404110b0036003040c08840c3e0030b0504000e0080c0d907030110504103011182002c503404a40000c541c1103580a581d100003590078560940c02807a014002c2626110040448031b8000308510400b02c01071051030340c140c0d841914070202611154002d602c261981b82c41900e01001c0842d07050b403000ca02043c00244840b105540307600d9400c004005a8042010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 379816258 1250 379815008 379815017
    0x41118010311090d0b220b040b1e0c03010807050f010e1917010506040c030c0207170a021206060301050109020c0d120f0c0804060e03041a031801061502010e0703121103070209010b07030e01 83
    0x4803030100700c110347c00d030703a000703500203034138940c0c0c1c0c60f4203403c1d02070400b007034801c10901d01d500d5007000380480940010358125050745d002c84500356218001c1010f42c2e4500b60b2928005884a00411609e1524080741080a0740c0240100042500d4a0800d144c49441c00d155207526074484083c001282024414000002214501000a800c0c00d1900039200c1100384540032048034201c1021082c81c40510a442d22154014031104540909500440e01c070101280e02038429487c080002402000f14000c640d011101da0010380052140328000340d80403e01c80c0482c910340c0d69180d0166803e4801ca209542c03505000352640595846c0904d050000d5508540210145810501080010f001d00c051450281821440d049849666014065145000c0c210b074601c1d2a40c2086000201544182088804c100403a4003d01410b2461118259105d04c0b600c80141303510314459407000004c0c8a2003e10000c06824415240790008940000741d508800785c014490074540041d000e010150040c1690780181400c1c01c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 379817508 1250 379816258 379816321
    0x9010c050301030209150d0606091428061a0c06010b160209040609020306070306050307050405011a0901140a0302040612090506040b2a040302041118010311090d0b 72
    0x34581d0106100003801506404085401c506800c941071107540c0d800f038007106000155080a00c06090944070340300c002c43c540841116584107a100551160002c0c1c00307148000c01355042d40e039021810303030300039a01d02c160384110120b0f01002d01c20304500b040103814680c2c0c2d01d49070110101420b00b41c040e400b034091060208080303440810300681e40d080e00341d011541179050b43d0f10350809001803e02100025414018001000a216011760012060340d409400700c804454603007061004642082c002c5007040c400074008003001c088120300808401506141c03650010b040003407042c002d40c10007651040441e4002c14140000c80d40a160003000c5152104d0900410813244c40341601c502d070182020700000050b000044006050380d940c070110301a44400101030304c0300700d4000e83c0150002e0100f00d10450401c40f54400403000a03044e104003002030389080c103410b03040b13000540c000c24442c07100100c1c80005211202c0c859981c808070070100c50190707601051900c0c1c1808000c000c101c030349011441e010350005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 379818758 1250 379817508 379817531
    0x10303022b120b06030f040605010801090302100b01050c1c180b0304030e040e15040b090a2315091c0503010f0605030a0609020a1d04050105010c080d0e070801140901 73
    0x4820501c0c0050b4248603804151a0141e0310140c40c902501075086500001408858034216014512490042e5810001a43c851416a00703903020003c0c0030300141c0c008505005801400d902c03102c0049014180540b1b040c00f41e00c401c606011401031171043c2002990091403506400c034081001d09942ca219000b20b66080c940500142d00002d40050100445000c8550080d02c803039100304034209480044034602d40031000c817140b00910481d001c840e0034050201050703140c54002500c100c050b0f4041e1000c40c030074003410103040d040303100940440464442d400c168154291301c05030f010b009071000c0300580b40205190801c040c211650310862400c024003000100150043c050f1b100c030540b0705910b4a0f550302d0b00c0d21a10f8101070111900040790840c4000752150b065604008480030f2500c190351182070142d201800c01040310401d214550121f440c420009000405140082420981ca4000000c51010040e100c5140c004ca030781092240b40c0d544c0300340808540050091640c051410f0009000155469 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 379820008 1250 379818758 379818823
    0x5030618010e0613030e150d09020f0f06040e09010f050f010302030d18170f0304080309090a0c200a050d0806010306080304050d12090b030c0324011d0118080601030302 74
    0xa1382c0103000c0104540d031110142e9910320000481300311011601e40c13101c07265028a0002c0c107480500300e00c45c0000056000d01800c01903c40380140400800403414285041d00240721040f00400b10540ca5680d5150200305100c20301c0748034005c007880384005a0543c118030525103400100c40285041c0940188039540041100c0e4440d81510825500741c0314604d04188451300d0031008200c80412400049000b00d041100040603202c10501103408140c82c0c0c070750041500880e029500b000300000c545100200300712901140320500549110304513901c6d196541c403501d0500404188800c0098502d00510245680c14020400942f6241d00514038083c902000610b07010751460008101080301071442c0c0c41ea80c0518480d0f40142040e42c4610b90b41d00d040482c1c00c00a070700480b844848101580780745403a034035000c181c140c20b43c60181c4074203c1c03400c200c100891103a06907428a60400081d074407000c84842d01140c0d268001d10380d00e07000781415411407034040d00304125607032a0000c1e50f94025210810840302d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 379821258 1250 379820008 379820041
    0x6090c170f160c020604080c040605150a05070309150f0e040b010e091f060305160f02060402090612010903051216050f0f04170a02030d0906090b0c030405030618010e06 74
    0x1002800503030041089426030f0404190b0074040d6200034089000030702200d0105001003c003a04443c104030081c0c542c4104400d1251441e68180001002d011a0a00070b0003030000b440554002e043c1041a90350358219030107042c0c4005074100c006448075071900c020307541042050b1000981114188030304170010000900300b03420300f0500782c410096080455400140558103900301c020750011034440310703251100600030f07203400d9a54020280940c680d071441d89101c0e252009a540f440d42c050303d00c0d03490715020007000d040080c0c40c1c0c3d40d10120242d41071481c07040034032401141c01d1080d1905620750704542110078101d080104051129540400d560b4100c40d80001210726015100c1440d0380ca031026a00c2001003406990048035000101103181415407a00261700064240f0132011102c080c480003408880d200c1c10ba02c589000300314040800d0100c0300300440540041c40115040b24101070707441d8000b0f40350407016103080e40300010202326080c99407020301039903003803680400040c640c03418a5240d4626113100f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 379822508 1250 379821258 379821271
    0xa150f02211c0e0106080a051c080a0f1d0c010806030307031707020109051b1f08070c0314030a090b0703060b0909090c09311e03050d06090c170f 64
    0x70845002040516601070940a43c01c08003c10002d41c58030308481d0f8440c4217001c181d51030700c1060031004031009204440030142e499691261165100e200441d00508400d60320005104c1d1111021340d1003000da0340c10f010500c0246401007146490040c000740003510081c0c103040c0250802c2052402080d003010020340e6006007089086500e0742c030170348124014030f0001001895401000b0b044004c0f40d001e6080b05002c1201203c10960380c0501200e0b80130542d1200d00726102140c10500010300c4a0b0007240c2c034104040c001d050686101492138110035469008030784001c06295a8144002800660700c000b50344040903040030040c0c1030411003c2c00c07581c014180e04078491030314240004d041d203c0904c41961041c3c03000d066200d4038103102d505070f5400015140d03101049407980b03041984070710344425240704d8950071507002c01100034114240e41d1201c07078214058042c8141000090b4104040c3d02c2040c00800d143e0340700003908001d03000e00034a06903070382c62040442400e51090006a04031070180c142c0088 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 379823758 1250 379822508 379822537
    0x103020c06040f03090315020319020c06060603100f0e0106020c0105040e01031106160302011a1c08030403050c1609050109050705030a0b0f030d09260304140a150f0221 74
    0x3c5103280803149400e2980004021070343d081e488004800c80c0f50003640c00340108407130342d00b4203100000d4190200e0080080c0e20f08542c1c01031020407260f060010095811241c600b5400100303541354030400201c0e100ba0703402240850080401007082c264144142ca07d103050904e060b900e00b9240400b070b5a005541030002402000004110000359550f807800c8500d81c840c0703441d681c8018205400d01a00910f8580180048140c042513a04c0c81481c1990307810415074201250441d008000e502c60810310781000304210306200c020001c01e0715a020800c144d4200381e000b425440e6a0500b04185201559011f030302640785917003403609001d121500310040c0ca5000e060040e001501031144c0c0c0026080c980e2416034103401d4011003a140101d642c1c0701c5055400d64000074940c50380301d02100440e0b01d80400983c0034052075082400140318900c6603e44507040b0b00345c001c0c0f120030442e84072580d21980c00b0106244d840444d00162154030401c0c0c0500000b518425040213034051005040c036040c40e148107409a922406 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 379825008 1250 379823758 379823783
    0x30c0d02031f0909060501080c030307031d09160908011103040206070f022805030307050c10020c09070c0b0702070302100c020102030d06090203252c030109030f030b0103020c0604 79
    0x4411140040035003103110709140102e50b6540407440145025201600c4981c144070001c54a5040090f00714001c50740030b0001e6182c0780250b01d04507010245c000405818681d04401d1406a54070114001e006945480e0b0350f180d061880c00c805880d102e080d174044001c0d40d05100704040c48080000c2031704c0d8800c1d01518001d640c0c2c6d00500d0040d00f0508403000c001c0d8000440e46050b2038030380d4145000d011305940c5040710003503540c0310000c265903401035030320003019a4481c40301c03d0740c40d04240c03060101c080c0d6540100c59032030070000b000680c032400440c0c4c0d4200240c0209560000d00404889480c0c0020701c0c4e00141103a1810b603004a0706041c40344129000303010000d1032290459200700103c1e00480c01210003085000d03152000d580181d07005031500c9403015034411201c0080507641c0b1203513000a6103500d5094005444900e40040751fa22100c41c1d070140140600404ea40c0d45080c01840d40300c9100742c1e110400c0d007000500182c22100240c1c001c9040510501c511149054000f5545422641018013441c41c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 379826258 1250 379825008 379825021
    0x3050c06090310050903090a140604050f0a1208071a10090e0c060403050313050105180f180a06032307090b0d051204030606050117160219030806090c030c0d0203 71
    0x8010310b00310400b00540c135050400c21255804009840300c100100c800395600c50751000c4525a003007021120a5000c441080104602e190000080c02d580c03001805415503039564146501200015450070b40e141100081d420302005059444200040ac411000c408142000798240b090304c10303136008400c102541e0b048030104a510820803009081001485551f4842d16490010385036000b02c0c29204d80500001c0c40890710f076000f042a507507180d50302d030b524082d40030509040000c90440300b03000d581c21810450344d45810950300000d4900c10080c0c484c004c146c0a00d145480c00c4400da400043c880f0b64040f10281c40400080442d0482c200d8030380348004181120b0b184e002840c5c41b602008000c016126840c0804c081403d440042d10849000d48410402260b4940064030300803101140403002001c01030004107003042d000445460a080c0348121008dc0250f00301c141c0700000700050079004221014100802d03464596102940b20102902c8070b411400c0c0118400d040d80070713404840301c2c07407074010000952 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 379827508 1250 379826258 379826263
    0x1f0b0d0c05130329240105070c0306140601093218010906050402041511070306051e01080c03030426010603081810051c0204050918060a050103050c060903 68
    0x190240c00d1142d0b0058a50b8074a00000742e8142c011518442c0c9610001c940030f03048400c48100c1c13180c03000741300305201c00004600030120826030b00e0096046c01010b00004002c2400300e290b00c000381d44116400600741e00307600100c0c80802c8004100504001d4900300500c142c03450702144010030248142c1241a03603105004c2d0803420503c1d0101e00343c104154111010880068640c1c40d4103e039100d5504008468403201840141d00c242c0c065090020070500700410442d100e00030107a962800c01007a075655944903a01c4d00b080d0354054860403404081300e0514075400c5481c4252a00401c0c0d060b000300351000014002c01d46a02a5100300c0500d0f001201846118402800e0f00c016070310380c410020003031140c503480c0c41e4603144c100e0035506141052a0301d401145042162004094000756291541071202c9040103912a01195124107a40381d0280400074880d2180300d180d501400d2040c0c0e4103884250202e88262030b001c8010441180309041c440100081080801d00420048043d20307070607510303100f050101b40b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 379828758 1250 379827508 379827517
    0x20d1404080d110d0c02010506011205010b0301051e0901170f061927050714091b0f0c030d06060e2b0303180302070312052511181f0b0d0c05 62
    0x284c16500300350290080315410b51009216880c26280e40c1040d900551803102180c000340070b00e03c0148810001801030385001c1400b901c01403404681c40d0300340c1c01400041907841c0c3c02a4810381080d4490200d03e8010300040c41880303100d844001c0108060314100b06080f0070200050711109500b6601c004004890400c80814815105070414402c80c00003c1d1428560f035032014403456080621800c200010b070302c1c3c959403c1d0701455046419002c200031185084480b40d001b50507015183c0f004000d60104003c0c00c2c4003404141d483c1070030000d05146424409800c0300001c21455220b41c014001d9100e00c4450031180c007584140c001040607403020030f40307429401490700d8400e010b49042c085070102c08041e8000366030400c4d00d21650241e40c1c0d04034032a805a500e070085601d01d070f200060b040710100724001d2540c0d40d168420f01911841c01d014401c0b0300411102202140c0d2035100c110740d00d042103042030600c00b0105840500300284000589040f600a14a00440101c4d503495901c800d1210079107880b030b00548 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 379830008 1250 379828758 379828777
    0x1050409030302121e010617040b070216170c030a03021218090406020a0f080603031615060b030a05100e0402010c0606030c09090209100305060402100c0b0703020d1404080d11 77
    0x38520700b0040c1c0d1503041c5c541d059050034112412070b00081183c501c01c2088105550b000710f01c07850142c5856032034002220b402044c40c0300b14400c40000c0842240501c0078070b401480d0003000ca44a122100c1c0200d4244103600e105c09000c0d0b0301c01c00400780040c2e4002031a000d41402c0c00c1d404d036102c1032030025880000b00e44502c081c0e44210440203000c00c1c040c055009141c00b06840d01c4886070740b00044810384d100350382180c400ba0305400c144007421074604000c081c0c42000e44146030b00d1307c44c100850303940310482e41c40c2c1d0819089071001000300080701c82d1030711074242c001100c01c00000d4401e14000e0350011149000b04000d041110217543e52042000c1a0808400740d50701c07020903182c4a4607240342c1001480700703030002c1e031048001c0c1010440101184503504180ea0b000300281c1216070780e035003d001040c1c140391490010803007500b2020000c10141d503401030040841355000369940b81210802000c1e2542d1998010708070b0400ea080c000000c01c800304940c42d00121745800b103021140925094102d00980008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 379831258 1250 379830008 379830037
    0x20a1403090d08040815150607080c030f07030f1106070e0112090302060601021509060c090328210f0f09121112061501030f0603060e070e0a1401050409030302 70
    0x20400f000110b2003c2c000f40c64903082100d040804202d08210500400e0314501001d20500051100906100c0000c0038800d005100a910b8810305410389403440c2c5c00070400303003042203012540d0303001c140c2c0c054100705651115140ca040000f940d459090b480e48005401c0350180402c0302c050741c009034040d0400c0d0031f00000292003048107400780c3c200a51a0002215101d0041c09840d4500e41a00c840a40460180f91540002c003040d03541e80810840980c01032442a526101d03540c100e000442d03600c15460500c00029030552600c003500e10702600030300710252440352000707942011401465032000c0c1a24907222189811180c45c4850b46040d03d28001e50b420405010740340c1c5245c4402c1c0b105400807000c82c0c600a541c034414070b1003990222038a400c07060303601600c420700c0c149616500f503110742c0205680c604242d0300000c1541d0340f070b681c2c041203807441ea4502c01aa005244100510a60030300d101e0351040e680c0700240034a503c1c02e4040c0ca601c2005020b002d05c03c644d80c0c040e24080c94800d9040c0c0720300c4800c0501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 379832508 1250 379831258 379831279
    0xd0b030d11060615070605090c0d050d0201050f09031812030a02011409030a021f0b120d0e030303071b0512030c04150c0f03121121010f030201020a140309 68
    0x1030100c059499860030034441d00000c22070905101d900c55007a021a0b00b100c13805d00c01c0c6a40c0c3c403405454081c100c000b041c4564425444659501c43c3c80b030b801c3ca803061004042d402d00881010b400d6410050180c807280540f60208050301c4804400c41300d03003d642044820820820400050341024921204a118031012907400301e1281c055010300130103800d0202d41c200564485144641d01d10401c00004c0060f0044526a05900400c0381c0301e8000042c4010042952040c031800f151130090001d0f90100607600c281c03075024285030010211030407040309502443c51403401c03980180c115462062070019001050b244a0207108044c800540320f0315828100303a640341070808443c0d4031500700d400f61294408040840b40c1c2c02c42e0103100d040c000c090740301c2501c4c441d4aa254405981c00c1078060390101c032030303622034588500c0e0150080092801c501528126088402d1071081420180c80507000795200075200c14041c00542e800144e45e200803544048180b01b80f4042c41c00003401d601031080c00c5900094003c9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 379833758 1250 379832508 379832533
    0x60909060a090507170f0103170d0b100504051e090613090506040b0f01060203070c23030610141e040207080c01110720011d0103060e011d060102030f0306060d0b03 72
    0x50003c4104105c88034442810349a41c400700c02040c3c400e00c002484409500264100f14041c0009084000c00c1041d00180701000c15001c00c1cbd14100e503800420020f88005401c0c417840c64071610203a0010a05c3c901e540805000102250335400058600c0b40301d09075500149403505040d410801006074450f040c1d6103a42000d02e8002c480140c142d440100303406507540085201d901c0001500e24907904000c1007403040e0301d8100031450340b003d1601d6503d0801c507002c02c000b160751000c11034140a0f08954903420182403806071803100d511041002e182c892141c24100d103420f011480c90900035540101c80c0180d50b950782d46042484da21950520000550804000f1985007c1003000b610605001da4050010003040480b900742c003480d0050060b0204800c2d01c450070100704101c1d15080c0d42c4206060000e2000d0b00d500400782401426480705d180e5445a1461030b04200071468540e030040000c1c0021401c00d07a404181410354000105200e024040104020841754103640002d0700071403000c4e0a03110040d0226 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 379835008 1250 379833758 379833767
    0xd11040603141608130515100503010c050403080a09170a0501050a05091b060c070b040812070812041a0903091e01050d050a1506020a11090105060909060a090507 71
    0x40c822000440d1500b0b000d040c52440441c1080d00c50307485007091091200742c0710000c0c0d412003c050b0007502c00b803900d17082d0100060301c2004810030504580001e0f00c107500e00f09401400602c1143c00141c02a414003240c00400798002d000d40b03081d2540b140c0030030703190b1050440403100076210750b200c640c0780074039540503441c2001c0c0400e83c5481180101b00138401c50f5074451048042d20b000344e40c0000f66070b201c41c604440724513001d0509a91080000c011900c0c02000e0002c4519101142c2c214072048c5000180420040d1810801d10400740b0311000d405091800070348400c0c019000d000e0300180f0500c07107075001804001760f500c26101002404d0707015010078180400c031566a5041401d059008000040124880e00003000d000c08040b40e050351000d01d030020000342e1501800f00500802c0e41d150700d41d408140ca0000b40d08000000c4c10340d50380104451280c600305491641c2140c0d400d00c2c05030366488010320003904c6040c11584440002c0d61036403481e440c0e500204249102c690301c5101c03200d01c1d1400703118100c2d074030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 379836258 1250 379835008 379835017
    0xf120109050c1305130b03030c07061b2105070503070303092a050402090d120c020108010f1211280f0e0c2d041d07030c0c0b09030d11 59
    0x4034401c206a41c0c0d280b501440610559002060300300f800d4000700000d01c0c10340c102003081400e42001217540c3c004080420f18680040c00d0f0203015801900d814400c280d0b00803141c03418904d48000640410401c0c1c0c81d50b00e6441804070050103804007554000b9022809002103401065000f0100ca68400040c28028018481840110303842c21901d11803035900200003280d003031045540011001c2442c940b004001c025800080f1158000b801003c00001040041c0d909010008030340d11031186040c0107200040c503440058010802c504c0e116401031202c0c114516203240015030101e603105000e49918005001200c2003080103090309904002e41c94101d440c22408001c071600612140d80454a4103601050b80d001100d02401e00da9041c0003500c90000030001a10034550126101040e21b00c140503120065800740e040ba07400181e194040c40e0081701130040c419401142898100071048103824014034120003010090101d42c90034001c5100f0780c07001d204613a0000d41200003001100140303505009035400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 379837508 1250 379836258 379836269
    0x1020a0801080c030601050405180a0c03021009030b06010c0303092102010c09030f11040902060c06060102061501020c0d030302160c050f010212041e0302060307020f060106051c050c0f1201 83
    0x5030000180e40301e00001c42520103400180a852030360f00f840d05120040c80001c004c030b112082c034241d180b0f91164040c401281c103140a89055803055042d030050200a040840301d900c200030804c1e000b04081043d15481941000b000d01e0001c0c45203950342400c0b005040300c3d4001500c03440090b981408500c0381d005803c045480c241d002032025641c060000d441801d1540700141c610300042442400046402c24544203912004000068070307561900420980e4121402d028030035071201c018003034190b804010f490390001c03007445021b4a44040740b0000317440d8584c00d0140390144603604402c0302014020f4046c0c403406030701e00c400100340d00807504000304204038078030826000d1079140060700201c5d480423030001812450010702ca4503184c038040300412100041d040302840c42d0350030100400182e54800c006c41c001c6446a0061030182c204241c5207080120607807041d400c1c00002c004210325490f540c0b00d80c0010303070181c2c2c0e40018190707141d0b90007213501e0bc0788020240800d480003456550081035480071605890 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 379838758 1250 379837508 379837517
    0xe01020709063501020a05030103140c01120b0d12050403030909150302120703080d091506180b030a020a090903080c041a0319050406020901270302210f01020a 70
    0x580c0c03061184201c802c1c500820030f00c2e1040c0d414080203541550200440422407103030410710400401031881c00c90f081880c1e180c00041d4004010000d1005407a031211100310f0f8003002d000784454883c000b0300f078880418240e140b201d03224880300580e07a55400b110010b003038210b030900d050300c40051401095603020703001c12404110303010800701c1c80f94030900c1102030040c01070243c10141c2d820344c1c0030041040d9045c1040c1100b0312901a01000148a489c040d00c1d0369058078101252030301c41441c0c0009684980700010b010585030401c1008000b00c0f101c841580c446c81c610740050b03001d0300c07900401d080c00c001a4029401c10310000c4005a400c05943c000c00c801c5000c1e40c0c0c1c0c80e00544030244e91540b1031042e40700303c8034a036070400d900355100c1580500441c1c10100860000050001141404080d030f54103c8003611110783c0441d810402e940c111500e40844100303110007012030048081d0f45200e048803408060700501105c000440c0340c0c20030b41810700c0c11000070001c40d0b01c9070320911801404ad40c0031a05820015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 379840008 1250 379838758 379838773
    0x190e040606020d110a0b0411030703061b0e0111060106030218040516021e031c060918060f0908032202190501031109090403141c09050118051b011205070e0102 70
    0x86401050ba01c6126034801200c801c11f84507034840c04802030084407403560600075403074000009580b501c0749401486c82d044200000700c0b000780025012400550109050203182c44000100c060b000c1011410745185060040e1211110500d0884c1c03214060306c0c1da6007082c50b010070301500381c4022003580e508042c2a0708880d46840511650a4003c5075241c0b401100e50042c0941e1840e1001d42404082810719018001f85041c1d6951100c01580c40d0003040004400c94600340f40184420740c0291a01803020050500c0306c2d280603619058070b40301c020020310400210340660341c0030f90380e034491003441d040e00200600202d0015945025501456120722800700381780ca6002108142c4600954800b22001428005541e60700c1d02c1c142e0b01441500a80d10085408005125144000c0304880701c5070342184c1e4001554100604e009421200c00c13105401040d034900305407000040d0300091096842c02c8000d030401441027210300594241800c1124128664217100800c00180d51062074441c070341070240c0c00c84416 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 379841258 1250 379840008 379840037
    0x3130e0f011d011703070f080a0f080c1e04091d0c010e010f050702010c020a17071a04120303060f090b0f090405030409150e0406060623190e040606020d 67
    0x1d58006901103a80d10840b401003081038100728400071890500c2d01580e28043c103e90300d290101300140c07008c0b80c45102c0814902d203400e034891030140010a0030f04240c101820321800401d000d00034405404600d040000001410401c00400c0d2401011000c00074030540c1c0292501d0721201a141ca009541441070a003280840c0d1700c1041b51a02c40311041c3c6034030180c07042ca42c5045449601c0300c0803d81c144906400c0160040e202d001c00000100781c4c3c03007080400f542c120004642011036039030004071070b80c91101c2060400e080780c3d030403102120350380f03a8113022030380070f0b440e056010740400e600011000588207400114802280c00004c003483d4121148840541d0250030007d55180c1902c1c0500940c0c8144028040507200d40d0100001c1400743c01403407405507035180e4280f0805404c44003101c9071522490100505600100c00b11445502c01e240340503a1889642c10b01500e024079a80416081182020208a54007070041c081401c2e002a0041c019203880340c001035514840480180006540f90061545 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 379842508 1250 379841258 379841279
    0x1090606020f06060604050603040816060c02010f05061503180a080703030c050a0e130207150e0c1f0806040f0e1606110606060702192c040308071103130e0f01 70
    0x407840000344802c3c00c1501f000d051025541000b0320840307103174900300003040084402140300d0429612500d40450703032820340c0c0c030005d0944415804014640e0700304030902450b640c425184280d80810550000c0e201d56400c4417042800030141020012070080384070400500850800426080e80683c4050001000858088a45200740700b02d003000540640400303a0585000c600609110080d0345025060501c0782c0c4039045039540341c90b03182001a50701c02c4841036166090194000244045500d41144022400310400c40c102143c01c0c50104042840041d180d0356503580805a40544110104500d155040c100c99030707059030f95211051860f0302032001030014070070701c1c0101d41412800d02900b002d841d151300b44015070300320020403070303000301010310400d0340d04d9410500e00e00500510040700e2010482c202c104a0000c500f1005a807158254803c101c04280c01110b06a04031a082c54070810424405000c6801c41c02641504e0704505240c00002520201c0700c81110301410001240840c2039a0b103000c0b000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 379843758 1250 379842508 379842511
    0x621130b0103030e210d120f0213080c0105040602060f09070b0c1f05010b0720120303010f1d0609132f040b100507080d0603080705010e010b0121020c0601090606020f06 74
    0x14601c1e8084504c0903062407081f9441c08903d10a6038001c1018440052107100781d070400f003503281d0400d140c84000c21400b201041071390503184081c204540f5007420b00400035105d500041003014100025004105109400c002c1e40d0b0061101d603c24940358001d01031883d4641c400c1382035000c06008821003210601c0c0c140d1048504848409191905d081b04568640c0004140b500307000c4c800c03001c0c85030820341310344855080085c081e1140c8007869980d8141000104a100e03581c0101c6803010709008036034039641c014240c90380c0102003210790780340a83d01c1c00d00401e86401e50001c01040b24045102040b50305084c40130000c2c1030000040020030310005081400219160a0202075002c2d14044c42d084a8500a0f002002000c2c058103455290412600940007034445990040f00d51481c0041c0030f1041c80800c0c0304038134420602200a00400c40000002803421281d100c46030444d120722030a0b52060302242c2d0481d124002c20101b55110780d0f81d184048030080c442d0f8424013001d40107140e4409070502001c14000e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 379845008 1250 379843758 379843819
    0x109050307052202031305100b0612060d1b140924120304080a0c090504020310020c031b060708070206100b07020d02040509010510050621130b0103030e 67
    0xc0190703600d00010050400c036551401030103441c02812540c1038032010f000441c0b080e4100394800c1c07022049860903a00e490300102c40040c00c01c0c50400e2800039561000115441e80103011800503045d1141c100040f60400780f82d070018841c810b02c1224140d8900036000c0383c4121454000820020525a028001c2c2698200c4003a0030310f07144201807214a58940c0220b0035520000b07004000d42d00074080c0d81e80d1842c0e0080d00311040d540d01c152034210800141c10184006801c1340300c0d05110300d0a080d03020035618154031071145547c94006c6a94880d8030030030010b0341d210f840706014144014031000c0c40305032291000c1c0e0b030020014201e100003442c03031400081d159000d41e40b03040b440540c1c0c92410030034040540000354101c1e406003002c12514050b030744030300499000f00c0c0200000580d9040031101802845000d50105d40200024081a001c1b407071348030001340060070140607808413541d4210100c001d03207804510040013031010500100038541e2040019540c000140c07080343c4216001504651030109280c02e5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 379846258 1250 379845008 379845013
    0x5210111040e040b0702070806011d010909110d150f090203060708041e0c090509060f06011d090c09030f031c140103020d02040e030a12060b13050d05070806070503041101090503 78
    0x42800a034609004e194030030b40703d2040c1d0b410240c54000b1203041c0702081e0b00083c50310000000c0c0994141c4481101c50040c82c030f0101c01c0200840316681d04d0b2100c41400d80c154806c0141580c0d290a100707240601d040c035046119010001d0440b822441c1c0c00030040144240d0181c42064001007803217004040040c0a1034220b5000c015000b1590000071400440c0b1504139603088194100040c0701010340200f60040034442c0160115140100e40100b88000c0102000e0400c0b800c4c0301440072500001e1001c40c04c1c21020342d034180c45550b442100915511441000d590144110904000948030200160072010b28641810f000c01c120b0544010581d0003804058103442c2c10070780108018940302e43c1c0721a041c0d10180003c18420424000309085801c5980c01da00803424880c8521000320030342c4a00c2e4060041c25180034100b042020403d00003013150300403980146501d000100610404206020090190f0007c071010743c0b0709400700525075002aa070031a200b0184800d03008456005108c06e0301601c3d0702400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 379847508 1250 379846258 379846261
    0x3130b1e011217030c0301030201030c0804080f0a020109081902100209090a02030a0b03070906051215070516060203070207060809060708160e031b010809062a0405210111040e 77
    0x55000405240007044418007110b00103283c8014820002c1d5200b8007500090740c0e125032441c0005810365508100042c204900c0104210001d001c03241501c01e4000000440d41d11040480c030241d00605204501130003040000c00d201c080d41500c1e010090380118584e00ba18907414070340c2c440704281e0054405a075441601034001800e6283c25038081c55015144c0d50340400d0001d4024040703414100a03421213807440b0f484580a1041d0b04141c03000c848a040780c08010b003046246c0802d1ba00c61002c000d03111400b08540060340802200c41c64590502954205130115601e080001c2c0c040c0d82c3d40904d01c9448045203500c2c00081c801080840c1c281d102d80320700e0300c4403d03081c0d84800f100e036601c0ca40400c0034814000b192058000c50b440402480c1d003e220388813201c040030b600c0b51001418070310009104081343d0340f01301d040100e002c2c0f0442d40307034070310b24488140c5400e0490f010300c0f04480d600454100980001e003900700c440030905040300105009208000800c08804820b60004184c0709034003401a12031013a00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 379848758 1250 379847508 379847519
    0x120605040812040606081213360501081603020112050a020441010c1101050d1e27081c05190c0224180303130b1e01 51
    0x1000103502900c620507080c80c0108982414054140540d010f8036015503c140c2800200c20820000003990350f003441c0b081c04c0081000e0304803d04203007400341040c0e10040302e6a0040141c1201003404100460a000c511404440010320000349001d1180d02e0716481200142104924109414001e4a8040c0e43d12411405401114000703040081c011511450303080000290010685900003040341e2221603c0540985e80c88569890f25054000b07580c03004100451110356a80158000d0b0f078007a84440030b0640c10381034100503105801500005074066050620802c11200e4240e03580c4200d17002030784e0400002102181506041500144a1350b9440f0480441304c00314040318050540c19082d014800482041c01004200b81c5005481100302c0403402402075203c0b1400b801005000e0110b44028289203241050300301034002d8201b0043e140b80c60400124603c5024070642003a0707444014102c943d40d0402012070b0389002060300d0f003907074011501e50110348408429648020306611071080700d00181d0928 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 379850008 1250 379848758 379848761
    0x405060a0e0a090c0e04051f170a0503040909030206070201050702071e0b0403031701090903020d030914060103030810060203120402061b060c0301051201022a0a05030c10151206 78
    0x30303101d180c1e01c45105440012201600d016418600905540703185181041c84280310a03200c02078003140090010018190820785040c500c1d030f00312403100030002c510042001c499400c1400d04a00035206010010700482da000c03054200e80d8200740b00c0d0742110741569610302c04030700301c520a43e02035005800c10601001029000f20a04002740300700e101c0b490070740d07998481e07804041d841541f0031000305100c00c1143e18214900b295440c0141041c1c54282b000c60b115640080d00c81c501604200d0a050791003c090051208000361180304a102808440065849003006450160304075823541d4032007045200070484500c0441541d0f81075400013203a030500d4680382e003008042d070008949982d44154150824082c1482000502d016840d47e16509945e541464244004902c600c1c1151200c2d0380100402403c00c485aa540418222203810700e41d103a610b24007030300d41007200b0b259029180c1e00c40860a15600300c004584039102c0310311210100000d49001c1c8101d009540b00e0f2144181c1d954800e8141000f04606 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 379851258 1250 379850008 379850027
    0x90a0e06030f1005060a120302070e0a020d0c080603010b010e0307172509140105011209050f0f0309040b04050c1611100c1b26070b070f0b0c0405060a 66
    0x1826a40c1d41d29811100303500c0c10703000c0504083c45070f840e1014401581001d00c00301020b400b100d006010216110385000e03545001a10a0310110001c1c500002c181c401d05506841000c140a00305000d0001d5060005020032015511103129518100040e020740d800b032480302d02140300140140600c0d510342852110000e80a10003000c8134000c04c1b580002a1841c004280c82031810040c00c104141e080440c80c204880c022804015581c0e81e110062099a81020340b005102c01e103001e02044000c00e516256080140d4401143396030311510034071042454010002c0c0118100030fa130100b2104141da001c210540b001501d01044d076034410820b412269182e50307010f11956001d40c03821140d0000e4100424450048076031b40100041613001b8041c1080144020707c03040b4520340f81e503041c9050400341c8140c1009003441d04410421000c7c0134101da030000c20b001010007408034040d019180c204608100c2111645090100c51940c0020006091070100d0020713581070303c1c2d0251150741040351000d0191041c1070b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 379852508 1250 379851258 379851271
    0x160f05010b04020c070f050d110622091a040203070903021203040f030317071d2403070c020a0906061707020a050a151107020607030f0909061e0803090a0e 68
    0x101d80401c1401c54841d40001e22180301190300501d0041d15001149107640700917002640b148284a03107050102e48082c2c000f40010a0403101180d07110b6142440b810610300300c0740f00000710309040200003039078466584943c0800100c011201c6c0c0b8820200e0411040b880200c1c2d03100045540141d00b40050304240544204001301c0313404a914080e100c2003400305170707225584201d0010b819604c42503041d40c1d80501d4a07801480909214842c803040c032070100401a40c01403002e00501c00702d5031101c4140090f07940084448411a125952400d0000c0010440b4500141c164000d00c40c001000542a14502c10907040340c805955450300600110f03280240c000001d445030085100f55040000880d60070301c1049006441102411481e200404451040e00e0348242c0000a890041c4643c1d070160f01d9000440380c4040e494903040003030741020381054a074801c880e0002406140b42c404081043c218400380c2d040303038a41105005200b150348042c82c507580d209841c106070b0085000c07407007000a40c244986040d003000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 379853758 1250 379852508 379852511
    0x50403090b030a020405132c03070c0b0408070b04120605130209280905030403060914060705090414061c060b060a05030105090115140901030b060d020d0b06160f0501 73
    0x9079510341146058100b80c40c090480c0740e00040802c01c0d407800e0b100c580285500c5200510061003043d0240500c149071510040070b140c6440c0e00200009020310480b0122a80710004081c3c250f00c0d64101410f98005000c2c80c40c00b132007100408100c00082106941c115480c16034012103076540c070396803030b0054100075011124801d980490301c0f0059581400c00380c0305043c9503440c01c8003840201e41c0b0309260b517050100841039034500460100410008002c440989400c4400071501c031040780380100880c103101070101c0f40380c080c10090044042d8480014048800222810b10003582140000c0e10780c050b069568682c0f0490341344201d07510a800300d00790740c04035015640c0043c1102800780800c2c207039480742141f40c00041000006009500e864540c2c1c501505c0000711450100824203806494400030014401c20b020b40442c01b81c035281e1003500440380ba40406002c6645600d01e8030714000194010401c6c0c0c14055040900314480350400c90151000130080b5000450070342c56a4035400b041c2c0d20070709070980742035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 379855008 1250 379853758 379853777
    0x922050712080307120509032a06040b04030909060b0301031b0b030c04090608030f0313060b06191b260d090c0e01080c0a060e220c0906050405060706050403 69
    0x1400024040c05081c090320a082d52460100c5004000d05200c00d48030703803c5e502d0034043c09801800001680c62100030200c11711148003402d1030717540b81c400e00441c04022503c10350081100f04100c00320043d008500c2034445581c0b2503110502c03941a113a5034080e0b2105140d0500c010004181010880e001440c41183c15240031921502e00110660044a413901005400142049104d400d88500741c024000c240240d820000750f04100005848041c0003440707084061103282e07050003040c0d40000d05020004050550b074010a0500420f4403851818040110303103281c43e42c1c055103000c01882c103e400d900424041c010700401400681e004003109003d030000c0000d201c0494015428424a01001c0c01850200d451601e45114150f0300b44058100f866180c110030001072064498149a0381a61081e0805481c85002500818544e0500046030100c60122604908c502059640200c04040d0242d59001c503003a22090300f503400384104d1289a800c104104650004255150f0010760002c0c4070349000e0406 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 379856115 1107 379855008 379855019
    0xa0c05060c030f0a0f09080f0a02100909111801180302090411041b0e010c0b0109021e0a2a020303030a1d03040e0906010509220507 58
    0x28000101c0d07446000036050007920b407811400500a51142e44e0040c000f4403075080034500703c01195034280013042c1100f0214180c05c140c69801d00420240c03681d42d007440742807186200141c04111140b07e020841207540d029500d001d407642c110715622001d503641200c102d40c0c2d100c107003e414001030040d032540032080c102030345c000c6039011110420301340d507507040182482030b1030603016038020b161a482e4205009000080080c65041d60340e0311100681000c01522400d01b48c0401038060f1728a0001004403502c41d0300102040d48102c2054420110380380001d4405400c40d80003080400c18001d98850008002007001c0c0e160105480710303c2c00880907401090710780c03101804a40381d243d140c04400f82d00d022503000c200c0143c2040342c03c40ba6940d90f2070321032481501003501c4040c4140100000020355181180d15a4040c01c544c00c040803000b500700008240f501c1f0034803c00c480d14042c40b81d00156 = true := by decide +kernel

theorem cover : BRFrame.Cov 379676258 379856115 := by
  have h0 := BRFrame.cov_init 379676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 379676258 ≤ n) (h2 : n < 379856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
