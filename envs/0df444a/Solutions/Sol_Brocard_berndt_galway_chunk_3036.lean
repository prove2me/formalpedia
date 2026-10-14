-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3036
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:28:10.668041+00:00
-- url     : https://prove2.me/submissions/8f9e81b6-70ca-40aa-86ad-e09a45a2b505

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 545863309 ≤ n < 546043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 545864559 1250 545863309 545863321
    0x30f0203070e271015080c0a0b07260d06050103180c0e061210020a021603080f0702120609011a18010e061f050901030f0506030d0807030e1203 63
    0x4426907001c1d00441110100e103140400f03645281859440502d5032010f58203002280b40c51007881101040c01190030144540145c0c0d0741608081c0f0b00a22403030343d540c091203100803c18503003031143d1421103030304010a40c140045038483c40c28a0310b03406002040e100c0c00444604920011b00d01400c44450584da0004060749094005000d580c0104521384440000344030800c00281c647c99427405880400b0355242150352910081000038107100d0303100100340f048007003180d0018015001030035050003d13403e6035680d0554104109209a040c0001841b010090000083c0341000001510340d01c0d00080014840304410003140741041d00a5410300101e944460160122008640b890550305009594403002080c034072404211241060003950301daa4640400700d40030b42d07141e80001090651f241841b05040c560490058590f1f4005107401340030038101480b0401125582c0f04a42c0325180140c00f400f0408417580d8100c1da0050020483d2047c1503880003290070804007007000180c200141d801c110368a060030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 545865809 1250 545864559 545864563
    0xd0b041b05041103070c03140d15060206090a080304050304120f020109060206130b09030d1104060e1005040312031407050901110a111c1a010501120603080f160606030f0203 76
    0xc0d401c07190040c0d09054200200252000440e6800080762500301d14034202c6103811101000076800c40c47e040b260119810260b0309030741d84125942e003071604079280180c4d0744420907615158104c660103c15088108404041469600103641c86132003141039a107025241d08400c401c21406e82070541c0c038441e900f1440c0d811560010345540c0034081c940020866494480403004a1003010a00101081c41c02c4e00443c1c420f003401c000740d85043c0544102030140903012a01c0070645c2e0071500c2018001541c4220300701c0241000494006102003680d03505207064207603140c4d40d8036400101003c07402c042c3e507020030f981d41c000c1c0102072501520782c55407010750700c0c07164000040c500b13090446403a030309402c440329080019500041514610307000f0354080b030900140c4110340100d01c050080c05044080804160500100d010b2442c03410fa400903215041640c030340b0a400403c80b401d901006007003d500700001e810003a0f841c80900f4071034580421803416002c255503010300b6175110307500850307070150a020795900f10303c3d013 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 545867059 1250 545865809 545865863
    0x1009110c0f0109110f010903050102030a200405090c0f0702030d030b0a0f050a27140115020109051f0209030a060b0a0b1c0209121f0609021c0b0d0b04 66
    0x910000d11201030241c65140b24150000506071055200c0c5c1c5800441c0d034040c43e0744a00468000d00219100e14200034030b040074040300f4074800c82460003030b048081c500c1545010740d000d88602410400c1030390348a0b44990070030f42c401031082d144600d05009210041e581000072145828031070382d0208006840c4818009052815048940ba00c0f00381e89052095407201882e0004035815080d00b00c83c00020402e40249160090542c20341403402c01d800c560003030010b04600f074102c801503820080c03521000c50b0308030b08980e13540c040102070b9004081c401e80b81c43d886800345086000e9003503005207004900750000f483c0c012040303800c42d031207901c3d441c41c84a980f81085043c001000d280424071701d04110764403084010b11001c0260080300e54003096070300d031589812103420202c00c400c9003140ca000700145c0309000c0410600041c903000c0790402c01d010640d01c000e4000d54214001c1103a00001810024025030041c0c4a411070390f540203811075417070348081044480c100d4042d07402466030641480e6018192007201d0781c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 545868309 1250 545867059 545867083
    0x705041d28090b01080d051228060509071b030807020c120f0607020706090e040c180e0c030c0307030201080a09120908070501080103020901030305070f0b090f07050a05010c0b1009110c 81
    0x310202c1e1b842600a000c503000100c0780c4c1444091030780c2d4030300e800001c615800c07426002d0440c800b00e0194528003c1e801842540c10407507201d80903544101e41200d40c2c2d4920840746414058146078500000c3c0102c4c00960411a54019901c04015403004203202c1e05002c03400900c0b50380a101000c0c05200207002090304100c8510107085443e0400c00094170380d401610a80105090076800501800821803503070002d48461400c00fa4050325039910240507066902e0301613045c2c010303040301c2892854006640050010050003402845140d6001903d81e0180144403060150301c6123814400680e113070038081c0c040d880e141c8038000348a003001d0071140307482d40e0784d0001070500010a0040c40035980380c020181c116503062501c90b5603031400f4a0701882d580c0c01030070000c3c0000800e034144020201c0c0441c00381407031901103003110400b0b0740d40c004100d1540d02920805000c1031140d400000425035502043d0390003800001e044178403a66170038034002100c4042108550101001c42d500d08503d00c2446010b9a0f04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 545869559 1250 545868309 545868313
    0xa1707172805150a090501020f07230616020f030307030c0f020303070215130f030806041107020907050306060717040e0a1e020a020c0910030204050705041d28090b0108 74
    0x302041d5034080c0c3e00c08140c1c99412904910800080300344505070411104250b0040007591681c0104a81c86143d41004204668040d420751281030700792a010f04000009039200011300f11a118802d0102403d614102c904045018400c5541100d81c010001940203501607900003913184a016401080101c8082c0b80d802190010024402560360010b0488400000d2000b0361089444d03030040c0010b2284034050052000031078015003018107401a64261040105580c24016100d074030f28a030445116180000b5482010103012504140c4250051a03200001810081c944070103610b0f103c80700300c29a410804002c0d40054140641c1100c20f02050300301606900c14088010140075481c0407155106c50840102e9010401e2142d2504c00c100e48460101d02802e030041c103050104041034442654007081e800ba0741048081000c00c2e208000721003c8445070300c006e4140214000b828101345001030081c44290346004a085131140c032211003a409d00315801c800242d01e0700f00b403500d5856110168860591a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 545870809 1250 545869559 545869633
    0x108040c03030e131505151303080904060f030602090310020c0a15060f092306010909020d02090603010b072102100e010e1c0806030c0a170717 63
    0x2080040301030140ca40c141000d600082199020a03141e201c01c40e0714140c15400d04050508002440081e08107a407000d0710600d0010444200c81c1e4014410300c1030b00703000703e0a0140c040004c250300358050440503500a00110b0401d0f5128081a1784090a4006a801c10307030000d1840c0341850108401400c0008400b030035400c03c0200c019103a1110540c1c000a0000c030502c50362441c14802591000000e0100000d0b54040951070f00080f000501d2103904e0b01d000840b000c0d040800005080c1079142c49403005a5840892038104507400300a50030031801848080c0d004d10045143d031369804c0c09140030f4540d921450b40c9030020fa041011210001c24110f00705107108803003a07103c65501242103031884d044c07200c02048810a9101403801000c12180b10729a6004504610085014a110b403180c420120b030b41d00d20480c0c85410415803103d003030400e00342e4400c140c40e00c100051070a0710400e003a064003040c1559075007a900c041e4090045207060183d400c44e042985c00600696400805a8010881018200300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 545872059 1250 545870809 545870813
    0x108150f07080604090b13050c060315060703020a0c0e1f0e0c1c0e060106120204050907030905430302030c06031312020303070e0d11100e1c020a05010804 68
    0x2084800742068041011500002e9520784964000340407040e030000e408150ba180a040f0440b40302c0c00003200310b0f20350040030500c100c0741c90b101301543d000f8070042d080302d031050304c0c94410458198051541101175000f045e542001181c00700782014010943d0a070380348500e00d4030910100711060410b1908448282200e401d201c00c0c041c22100980c0418410b54640e65220300c1001174804540e10b0000407055800c017001407504100115000b41200c2c05501c500240d000c0009107030041e4003c0d401001e40115499002030709140c820341058480703d0148044da01ca400403583d014145041e2001008070441c4d0b01c0ca0141e804511006155070401540d10360f03200594150b030b000a8840b40c40031146031240c04040003040e041303100c40c1c02c001584c950101d8600c000c04990075000e91283c10881d200030108102d86001a60750800b0103090009039806050541518003003400c100081c00840460410001314400380c09654991021701d00381c1d12a481c161480c1140144104083c0194035000700741040844024000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 545873309 1250 545872059 545872081
    0xf0b0d0b0a0b01050f040f0306050601080906042907030606090801090c09090204111b0607110604030c0615060c02090105031207240906020306040b0312120603030f040e010815 77
    0x14110455070000328000d0102d5004965500401d000340071202c00020700050400d001e480176000316031060f84103102c1c44e540c00300151005902100d400c507841d00301000160008421780741d444908481c442254414072032070341c00e030b642c006400c07149400802c0d5a04020301070030382c000c1a154020f100d544c000f400700ac0c0c840c1d61303101c401c500c16216000340591180408401c542d6540c00400d644803010280d540caa6514140380340c4272005010144029024940110700424407404140c0748101c24000140f0541e100c030340d4100c480d01003c25003a901d15503074400c20b00c2e60842c10855040106001c0d904c07060b0310b007158010081080010b9000c50704c254400700340c4104000081050307511241d0800c8455040807a00d05444c40c20807062a41c054501e881c2403015010403210354080c50054500b0759042090b6084401810b5032100e0368030361803e040c001845080742c022800201290300400160640c0c0c1480884d580754202d030740083d00450b1182ca4080018011801e080156a00050144034418100d091400001d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 545874559 1250 545873309 545873311
    0x30916080f0606120d26072a080306010c060f050c041a04050a030201052d0d05090106060210150e040302030a0219020109060503130c0f05030f01050903090906030703080403060f0b0d0b 81
    0x4400e211b00d50050884030200f40b6401c40c0d814004e45208a282e160a40009241d03200d8000c6607450350140e6070900ea28400500b2503440040e600c45501752858a843c001554110342c1028202c41d40c07901d60169503da9a082d005450041070a10105519135003440380c0c45014684408200b1300003507003403000700102c1d5152140d14007169020300340700781d480040c00c3d2946140c0903404410300b40e42040c00148410344080c0c85c001c004d16541320104004640380c00c06c1860a072182d034466140140e020040c2142d1000d00d1740e000d0900303089111103460301c49076100c8240400e25005c0740d0036400341e000400d0003803c003a014403020450b090761145442c0941d0481d8000b0f0200d03103550041c1c1c401c0000201c0092074040030090480344294000c1940c4103a1070752060078606000050203428040e010340c4034a42e5a00b801402540e02400225014504040c8400144001c0b08001024aa8540b040c0007000020034010b070010000b55000306408204100171080b28016a05000040c4c0d0051b0f1b0012180c80c007041c405a421 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 545875809 1250 545874559 545874583
    0xc030c010c0206121003030f02062403240708010e13060213080f0c0102070b072d020d0b011e0303080f150612010906060e03060c030916080f060612 65
    0x1c110020650010032880d000321012103c00328104810300c1002c003183c409600c100d0b03202c2d80c1c5034a04400c4100301261030b841c0507614000d440b00030b41c04810340c8441a031180c5550120103421075960601c1035020301803281c0d460000c020700403030316414001d080f0750206165014120090101c08182080380d20440000100308018007020f50200e0100409401c101c10b0100401d419030442e085c42e100c86a01a45034800141028054843c0e11343c00610318001009999a00340c010035842d0200880c20750722642c0c5816000301c0c0e040c180c6555014001a60b41d00040e0301c1e8140106c410040c907606001c5030f030270070b9109a0044100f030f01c040e000400c00203a002070295400a21130321450916201d69014031400310782d003000240c3c40200070401881808094410718100d802e100b0b000c2c418a03995000030f072840c907103000056405401a03400512002c0001004540007030050084501400d1000340011660341c0e10340011a03030360004112444000c0007040103a8001c082103d114504c5c0c0c074203c07081d503510812140c4c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 545877059 1250 545875809 545875817
    0x602030a060f0b0d0c11030406180b0a21360b07020f010b120c0d0c092a02010c050a0e06070b0f06090a1505010e0d0c0321020c030c01 59
    0x140510340341c0e0800c0e002406a0300b2148400354036984003010b0354020200c9584001c0c03510282d410410b1061035200c0c105410130016525160901d0130848050b0f514001000c10400e10105c0000c500d01e00000500380715003150b44490fa0003140e20308468072203a150202c201c05905203051501800042c814081411301403010602d0b0304030300203071008040240d030000a02201026000c114501b50045101d00c0d030f894240307000b0040007083c0410041c01c540e8901c00d04603154001142e108450901c00034074075209005084076100a03030740c0c6510760b040d181c00000c040191050240c400c051100c4480f0400f0b20181c09000901c058041c82c10000c04a0084120000400000445148040d00e5000442d444203401506410642c5402d0713242d6a8a400103445040c09800204001542d00c01503100d141d80c6800c588448141b128604001125003150040025612a0f90040c41c0350000c1c404101140041d481140c4580c1840b018649410440c001c0c00d90020540d000b90340b00c81c3e03082d500030030803400111b02420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 545878309 1250 545877059 545877061
    0xc08010c12020318070905060a080610030206250606090b0609150307170a050f0702030a0f0e0406091409240415022703120f0307080901020d09080d0608070b07060203 73
    0x1401311010469a40b02400e40203004001c1094442c03030f04458400d540554603018250741e01c04134141c0d58038080342d0461603108030b004c003400149060401041d044540500b40718102203003500091400031100811160380d80d44440c00c002c140c11038080c941004004a40c030278282004c0c000411140c3c25001181c0c1042400000000c40e91405542040c1591455042900d45441c0191850004050558071240002d104d00000390840e4400411241500f5039940d44004880d40d070641500c0c469110f45272960b21a4403040f004c904100301c0c3c86608154586001e030111142440c86059090914a402c40e011040c08485680d032400d0119406c250000e900c224208608541030321000024001d00d014201000100d01c12081c0c0401401900c0c41443c0040781920301c00c000b042c0130383c0000d11615030021104007042c000181da05c2c2c020140fa40e80507079210300240c64060a900380c0c03021103a200308201d540304e03030104071122100c20500c20000035040020060405500f004130081035802007900c02856190000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 545879559 1250 545878309 545878321
    0x1020d081303200d0302070b060f1c0323120609100e06030c0414100510080708060f0301230604020f071b080a0305180306010f120204060e070c0c08010c120203 70
    0x4200e664100e00c00b1010760300240040c18004010b90f02512054846000c000040303901c91814004003c116070000741422f028203407841c00b6034807200c483e1009a041c0003030035160b040c01110785c0b200d242e00b0314140064260354000e03c0c60748401149001e4589070003501070304100494007181a206000741c0c3c0c10303401001235640c1d0700c00c0000e1800c2017010b90181c1107410111070005000854424a00035050155800042a00c4400740040000d45540840001c0c1205021414540c0946c403010f80140005d4405450300c000704000c6800d4030344514905800240b250406001846c124202c680c02680c100d9040d4601007403024180f29a024605000d40310b510040d0840e01640c034850b103000c0c010700170f01d070075110089501c0c140540180c0110b80266440c0c12002c01e03810103483e010071690305a841a1500b1148a4204007009000c07034118801282c006540f03140202e18552a105031600c00d800d9942d030220600e4044c030341010144503641c0046a242c0c14640e1100809800c0255180b00c039441c2e1034010386940e00c0c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 545880809 1250 545879559 545879597
    0x13210f1e1413080d1e050909042a050118081b0102160603360b070e091006020f030f121b07050a0b06180f04030302091e01020d081303 59
    0x2005000350b034811019800a5225004640c60696600a8589141888101c289100f14a4144090000080c0b003042030050700d01d03205280d9034010380607c085441612443c07500040d103091110740b01194034191130080115680c08012030965003585a80d01082e80e02e0044400c2c0d440d6040c003640851201448900c0d6216442040713610000507444811040c9a03580d030b40007500400c0d2072107981221600b00c0340010002e0603003c042c905405162140c518042406031240e0f05a17840c041c200108011450701c10714a165a00114a801000402c980d01c00417458a1400ba1400341c1c045441c1505400500c5111488600c1e00d00341d512800090034000016512000151440c000318140707036441030400311703c200c184140064102a001d201c0c1c40c0f0200140c407503900300540c1040400c238038001e605091000a40b540c030440075080d042403090034050705044112000400412210480700c1030b5003400300110f1440d6034100807090b000191428056001c0c02d01402e200b0010244280280501c0f03c6500070800c44c03804 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 545882059 1250 545880809 545880817
    0x90702010b21120313120903021003050910090602090306090a02061e09060703050324030a0f1b15020610050d0b130501020a020a021e0108060913210f1e14 68
    0xb80b2074950305d00c0c20070750340d00002600b51000d030340294000c40300e005079a000c1d00042c400e4903002880d0405868500000310080c00d8003c286200501640c034174442c0c485418040e0041c054450000980c441655038203261811000402030030056020705100809a160881107940c00100c42d202500290145c00b0150a40c0c07043c10501a002500090100c09250b0710001450152403400348114410180c5901c05611150b0000c909a041d04030110120009401507204a41d103031107501214400c0b40343d1035200803182e07005d5204c141e103000e0008004100d82d5040c40516804552940740706c0c969820711001c220741e2189100c00800000041c0085010030354101803010600307500c0002996100c0450500945810003000708900902c0d486451400304408512074a00002041e55052541c0d51040300300b044c8400090140080f0050282c81030300881c02a840946020001d186440001d207a400da0080014410410074401c02c07060810f9600c03484051100130310155a1841d0041407003035440766044440c46 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 545883309 1250 545882059 545882083
    0xc080a03061211030606030a03091401020a1502040e0a0207050a020409020613030c1e0e0a02030c0706090b06090c1e0d0f060e01080f0d0f2001051302090702010b21 72
    0x40720300308010009403140800440f4004e40540d03420b82c40390130626a80e494801c4009003c00d507550818400380003d0442c1d02c03082c1a051045914003180390300c030031107a0213019000311445500028284006000c00303040781c1c1c005000d00350071403500c9002d8542c03070b4981100443c024403840c0c0750f91100041d9a21003041d0307000314041e240d2192560b41d4071728140c0304014940c450b01414480c80303030481144001030401e0500310b600800b48903580d40d841206150080d40010146070f50400c0611001c0c000c11414864089001d100b403040c2c103128181402088a40c4000400900c01d4440070070455001150019100a204032402b5642e41c4402c00020b402018150311007501c15001c1c0780090008000307800407407945c101c1e807181c8142d907180d12004007415101e510700ea07030f8503000c0fa1078084145031152003101400c01c0201d00016084013105520407490945a007500c4030080c00d00c04660060640c41c1a450440e0001d0307150000b003007280d10a101150440400681c140d01c5900210030f1503050a10a1160b141e03504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 545884559 1250 545883309 545883329
    0x8151b0d0506010e03030a021507140301060203130b070f0303050709090e071403010c020a030c020406030b0a0509070509090717030d0e03030a06090612150e0d0306081c0c080a0306 79
    0x540c0c003615100810085800b02d0010360503007806620760401204640754040503501402e44c03145103804000b95000301a00caa0200f01d295190008040700300030146028112a50146585951034916041c40241030340103030f008540b00f04800c400092610298550b00765240c04c0100e4581c4d140c07401a126280b9a0744004c0c0f06a0a01d000216402000705101040c0c4140c00c6a00c04018044024103089032400990f07035025030b100d048203501190040003c0a001c41c40144003141064480d51790036214181500c1c501c400d15181c00c10300071440d106101c40c80150105550801440c900110095610b1029101d8048030000800400a40007800c6c021105004d00d19501880100707801c4007642da580d0300482c0c80400f883e00e000030100c2d02140b6070203a602143c40200d41a42001e5007a00d609046004441109900c50740c2d0300d401042c600010310001340c0c9840192000a211458400c010741040c0c180501001c4d0304924681368010310340c008080c44282c540040d04161079209411058000341081c0d01709403808 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 545885809 1250 545884559 545884567
    0x1309051f06020f1213050603130c09090308060111120f0717040509091f0b030f16090c090530030304061d03070209150102072d0e0108151b 61
    0x540000b0340c00c410703080c1c2908481d01c4d801445910402c0c0d0182028403c1415401c2900f0005880c00340051070700042c2d02584410003000b1643d580c0264100350b8003d2440c1600c6c0e8849406254020303802980c40282070800c14001c1d296441032a445018150f80d00c07088040118101015244032010390310703400e0b44911010110608096240d10329040792280520403034002000801c0440046014114106c0c103402c00e100442c0c0500741d64024190700e0390702a07050301c90200c1da00030010007000368035031103084155159071150404403070780c081c4e078034145404060180c03500d410001c0d03844603134021030380d900001c0c80b0501ea1070210352103203050300001c2c21042c051f10020003440180702007940308015900c800714840c0030f4070640c02c0c0400d84901030520f010f5030151501c00003450744d04d01c03260b40c0b008298052040d02c00c10341d1101c1c11610100c1103002682c8149881491515101c0f52101e4048080d0440d82e5410185625102e840c1d65a0400c08000c0c180c10b10300760700810a1802d20810909452850807506926 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 545887059 1250 545885809 545885819
    0xb28051b010e010b0111060a0c0c0203030307030e12270d0506010605030a060504060501050a031509020a08180a150915061206050c03010609050d0213180302010605061309051f 77
    0x40c201c0c038807440382d003540f030b0502c50b1403a03601076402c5a0191180070054035155031110220402088170a40c0c440038000382001c0000180d0b014001140f081072561030000f403944a909400c0d1501025150344400800d04025000b141c01c20320144110182150402e00c101c1121030006ca1100001c1900080451140000108000d504040554401c2c02c00c1c207420008280d0340c1e41008180c0e9460f2040c140418400c00c08000f05503c04d4200855290300d070a0200e0b03542e682d40b0f6000b0220307400341c5100310000d480708084c0a140e036401440034030350300500401080c2c4418541c03162607100801e003450b0200c00740e0b43e0200301c2c100450a40c03e108e402c60082003c000c6d880e80c8400c00030307000748030754012107501c1d241200084140c0e0608040d2816915070303a841d0710301d0a0070902404102c0c00403000c01daa00188440da40300d10440d42d070180c0699240340d144064404a510b1070302a003900d110b078001912400c41880300b5010302604c45001c0c0c003102e0510b44081203680710000e030b40d030340e81c0900030480318104002c21700030031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 545888309 1250 545887059 545887061
    0x4140f101e090f15110f0a0213050714162111070b0a030e030f0706020702100806010f050904090510020c0d09030c030605041a0f010306060b28051b01 66
    0x2480e00d22040c1109001007003004111082481805000141c000d501d60a0082078124071001840a50a003486070192030b065002074902000e204a0b0112503000d5100b02046060003072004580c02811078003400036041268000d001c1c880c8031140d6803000e10010034540d580b01c0140b905100869041585a8504c84098500081c0300701c10700340c4080860070482c840082004005070311022a52018039250030140011401c801416600454403c0c03072006010200b48104240006d10800d84146801a03848030f080c0306201d0100117151441342400000c40070000d503640c225003a0440000c41e40b800315510781010000500a1420038800b030304501c030f84820030081c015a64000c0c081781340d601044568120b504281140c0e080d038280030042410001e81020000030b145600000d821500c18a80c050319800301b40311b0301441380021a2150108440c4c84010400d101a5200302c00291103001c06051914150007403002000d9100559007407110690114561180d1042c0140c480c4034040d0310800d24511440e400b1701d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 545889559 1250 545888309 545888327
    0xf060a05040b0c0304141801030308100f12141203190f090b1f0810050c0c03030c0909130209060909071517060a12111302121e090304140f10 62
    0xc1c0146c803036144003500516000c8882407895407030110340d035110381c00c1d44d8040310038410142c42c2c100c0001d409c1c40c0120700000c0010020b40070300b8024040c0c113841e00481c00c0504184070031002e900c9180d08a16542681c80058004490740038410054404407100c080b00b01000410303007002e03001c0f60689041c451108000d81c0c42c0700d4030300840e590700700d50442c516201c0041c02c1d621082c4c071444810341c0c0043ca100e000440369407c1076178007010b031880882c140316403204400e0071a8000c4580c501c83c00f10010341d001191429013405500003000e500d4118501c43c1a6020542c5002d0241010384200381d03840001d205051300300107031805090a040d140e44c49415071500904400b0381d00f6032440c2a85030312400030b5000e0501d09401000c441c1403020076000c2003001d0703c0e40d40190142c02d00441d002078141303c203445c0036015030008140c49020111010514074000c880315442003d4031000130743c44a05801841900c002c000260f8040e10b070308030001c070441c490100000e555415402a0b8a401c01e40403415243d20540005100c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 545890809 1250 545889559 545889569
    0xc0403061a180907090b0d05071706010e010b0d020d0e160e0c0c06061e0d0804090c03151e0f080c01021b010f080403020a0b0a0b041a0f060a05040b0c0304 68
    0x811100c580c15181d245403903030840b901080c1d9407044600304005c0000341c1004090300f502802c02100d02040c4c0d01c5560030140a41c00195902081031039201c02c1c200100456401401c070508034422550600c2d680388071b14440e00340304420407500810300004100c0d803a80082203859110044500318281c4103805044202c1c00d21402400c04030f8a00060001c0e401001128804089800541b5807a524042009a40c0700d550f2041d025000c0712140c200c0341a00c8503072210f130000d07004010060b160b40c5000402020ba406041c00c2204041c10921800100c0c01105245016a8000d0405001400b2985140f41110b4505d0348800b80c00c003034982000459030004206010128000c1e42501d02000840705040000c0d004d8180140c00502d0500111800604c1034610940046c480c1c03040c2c0c0c160320641d4403a40c014410544080350619583d06083c030b00c4e480c00344640340c2caa01580c034000c00d1182c05440018030910758080900d0040f2000101290802c0c8075808407400340204817103460b2500e0547c04882d07901c0c1c005002d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 545892059 1250 545890809 545890819
    0x1e09060f050304020d030507050709061206061d060918060408071b0617040309050607050f0c1206040b0c0f0c0604030f050309102d14060402030108070e0c0403061a 72
    0x19109030903100350200c9101d1500503003c21041d0a0303a58048900d50300c0b00900341c2e02400b58500101d0741ca402130250000038120b0388204004003045040c12411201030354000300d480240f620f500600102032000d07407548600c040b5040169a514a41070302500381d002160000e480c001d035030403c010000403c01401b10310707002e08200120b920f04200e9402c081c80180c061100442c41d031074101c10008000405455005219143c207804480c2d84401051140e08006421903190b00813010380c2c44107290421801010480444a03200114581d5098035110300b000ba01c00342080f00e10306d00080d11512001c08842034242404141035840b110054607507104d080c1524110005640014081c440510407002c3e80d00440c0c07901c02401e9910001501e60300180a000608100c01c08462800b14410b103400d462205c1c0c10907001000f00754172000c40480034603010b00500d061303c07c902c18001400300b5540040d2000c10386810b03c0000203035845483c21030b80c03540a15030000f0101420000645503841111200482050050318 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 545893309 1250 545892059 545892077
    0x403030c141e25060c0f02010e04140a0509010c0e060c070e0403050c0c0301050c0d05090c060f0d0513050303180a0c150e04110f1312050303040203150105010c080a1e0906 75
    0x3440c0f0091601c98860080050096520070b00422511124a05485e105046c0703038007200d401030045000d0303c071800b824000ca01026420803645048034003800768040f1b11040200110284220054182002221302c00d006c0c0790702164580031000d0420001c0302a00c1e0502c0c01403594603041c500104298041c1074035203054001d0052840300742c181400f8560050f1208030559040c40c800e984a40010000140b01c40202c0c0300d2150b41d9900b50f22102c00a00f1601880080317299542083c811080540300c010f89406080c076442822400405e00101c01c4e01c0c1c204c01d082d62000c24541008442c0ba01c0d105503040041d01c0c0003155000003440c032119000c541402c130402e07202c02d081014034070200011600d00000c079401c080b104114420011103003400522019500c0d01502a074540c580440d078810390780d103000440f100d41c0004240000d6150030007001d6107608090f200d14000390f0410300001d103d00035200005040d030b403003c545e030341c4203601500004280024001c007014002202c480020000e1a0600c0748001182c1694 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 545894559 1250 545893309 545893363
    0xc092403020105090d03020c12070801140c0301031b08192013020903010207050f0705030c1f140c0105040f140a170c0102040e010603020405150403030c141e 69
    0x1088804981d016142c8a050085010500084140102d811002c6000d42e0200480e03540d11034501100b0125880c00604003642040c5ca0607003100c113034014000701c1a00e040200701303940c0c3d420404c17a4156075214407482c400441d00c0940207546000c2e9000100107000b1052006900d00301c00100c80b400e0760041c80048898048003810f0081d450013a00d5480d04155812250801100c9036001000e1034003000e00014900350407911100c1c10000c6840001000d074020540c200b10303d2408208006d0310700400c442c401410300991400c2a00001207102000901050210084856000d0000d40782440c9540000340b00724030382131901041c3d031040044104e5801d072010061180d0120b001400d001d02550000c07500c2d98003020300b085403400780c2290090310895034080101003401000105107a000f40b0305902c0c0586c82c0d90a10f003c01c817041d050b0307106400e00d12340188002c20200f640f0025241086401c5a2043c60180311450414104036001218120484a2011201c1c001c3c1c00041e111205450140341c00517900600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 545895809 1250 545894559 545894621
    0xd05011208030610091a040807090e0304030321020c15160e040506060d1d010e0c0609060304030e0a0b0a02010e070501081602030c01111b0c030304120804030c09 71
    0xc030141409600303100103100380c14044092880d0004500308020800d61b00d04240d40042c0c40c0300309031144080c001c181080440020080300d030250401081c07e0000c580e02884055503805103100190400c004034003000301d00c89045100c1460382c407511006640d900208107001d035540c0c0305e900740d01d10301800780e0000500440400062420221f59545c999900302201d10030071000d4a800740006901500030480384448500600c5080003003516080f48045040d001b040007821249041500080d51b0040d2011482c00d5850b4001c603084440f08a4001e40c03241c07103c1c1421140569241c000c10b40000d021440400c414415174060008218580e009006c9414900c01e2075440b200c5030710945001c120f003100860641d24003150300140100c51441142e080007109140c1c42d00b52403c2182d45c0c5400b10001603500c09a1a041c801702d1600a40c140043c20345060750000f00755a4490345c4a101c0a2441c4101c1020820070f4403402c0b900195040600403822607224410400205401e80411940810410085007082c00b8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 545897059 1250 545895809 545895839
    0x20906091506072102060702121204030305072105060a17030307110a330e0d050f0d050a0204050f191505071b03150e19020301090b010b0d0501 63
    0x4500000103540e060704041c080980c0103a00c003182e0f0385558000900c540200c542c40ca40c0e03502042d03030040c26070741061100642010300444140c0c0072000304004103100c0130443c11090b0b41103941440c0c0000d090780c880320120b40c203083c00e002d400c1000d460085a00c684103c0358010501440044506074407039540c40007401c13020707900d40302148401e410520002c1c81040c02003080007504c1381c83c40b05841c400c40c01551008062141070070040011030041c10f504141310801d2340300304601c4032201700c2000a00f9944034803580e102c4c420100701041240c00100300108061020985012136101c002c10720050038407a1450340650090b0040e680241d102c140203080d00e1400d0544900030303141d6851309919240c200700e0340c0c44510451400350800c2c81404c0010000051200c100081d04000c00510010702c5400c615256641207032826203046902d0500549520041001c01d202d094810700545030014013429102103800350403008009409114403c000040c2c1c2680c0c00000c154408100b1020852603072182c0c0e1100400b48 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 545898309 1250 545897059 545897071
    0x80102070213020a090b040f0305060a0903050702040504020f030307050c0f010e22090c060c03020d0f141e030907031401021e09030703150903090e090a0209041a01030f02090609 78
    0x1010803603550b1500c558001c11181c81d07945403000005403550b00088180d405940240d100c40900740040007803280a1150980000c0105424040307003480d51402000c034042d160b0042c0c46a5651701c0480c0441d543c54010004851001d01580e44640507401d28507111518610583e02451a50030072404541c400d250303070309070034a00070413240045200482c03000c01c02860300c503003500d0f09588114000224180c0c4880340020318041da100c501e180c2661900038141201d0400c040e0901010010500c00e8640145015070714061101c1965100c0c1d800e1280c0c0d0000510109824500310b80c004280011402c010070080140c90080ca000d01003441103004035800c03445804280b40700000b00da82500d000c00f4061000f40383d00c1038028100c6c0c1d240d9880742c0b940d40081c1444241a06082c2d80c8202510425070042e010303400030030346040e1803490740c50314805450b290318010308000d20031503106000a04000e8580101000f110760822150199078483c03502072589004d07400142d100d0441000021428a4080c003c644604 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 545899559 1250 545898309 545898319
    0x7050a0908241008011e1409030306040e0a080307090f15020c1e180a0b0d0b0604090f0f08090103060b1c15081209090f01030308150f0603090105010e010801020702 72
    0x140641e0300d95002c0c402c1c040c0c2104080c24200100003000f0500b400703240c0340d10428400312840030740400d02a20032202002010f99603043e4000030045c0200740401920381c003e1040d2004036500e00c0c000c119508180311594002c00302e50000c000e1040c0765a003d104c400c10b480421010410b696154038440c03100c0042d400440c401a40048680220f5007040e40405e42450810038980076510944400185102140010002c0883c40401080f04603038503070050303081d112400c0c1e8980040560039118007481623002082d00c3e00664a1303110071020044900e0a0288098110300e0700d42c24030740c003407400750070030ba02017188507002038103050020642201c801c0c00c42c0c3d0301c070081c046403121a01c80658054041d10806840f1945c48001070b40c00036a01009100242c140d5620148156503440c905080004500300501144090700b01c5000501c0040e812108258020800d5404442c01c00703091b030001032640350301d140303487d4000f800030043c444642c0381500402e059580c01036003404140e0b2035005640c201d001d600c0019500c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 545900809 1250 545899559 545899603
    0x2070b0c070603090201050415020f0613050a0807020105070b0109060801141312020f030d02191e08060d14010c0e0f01020705060d141608010501050f030a02090a030b07050a0908 78
    0x2c03500070b81c0804022031040c101181016502c200072140c0f40e84455515015820140524140e49001c0c80610f074000c001850142034900c5a440d07060795081d00702c07001018050001260720940e0f004009403009264032a030256565a102e65443e80900454400c100c00c560074000408000140848154030560842603241c80702d00b126110603c10801400310001940034032040e100003400c0034001801e05040c011030150340e8524090305134600c4c4900b03031381031804c0081001c4043c00b5902c004040c2819820240341ca01d44503155040003a42d0510441d45c02003004014500d003816041c0d040d040301307490281684171001e01c03001c5071060140c10001c19104a0050300604014809850100007174440100c0c44071001030300032105404266015400d5500600c42e00d46c0b542c10351440b40d4408009070241c04286030490030030700c2100448105000113440080e42540224100c00503486840300d800040d80c00c44840139041c20000006000350b03201c036003031100045098a0200e40c41200042c6031150500d009610003113 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 545902059 1250 545900809 545900819
    0x1050a02090f1e1c0311030c031905040503060112060f0504211b03112b05090f0406090e010609020306030303150d050303040b0708160909050903040e01031202070b0c07 74
    0x49048070040340c03010720145a0031050350340c40d82c03182c81e107910f1300150301c5020401e030324200030702007070311340d03101c04070241d0080201ea0b0700050080160342c0c0d01c00c202035200c916030890300015102402140c000c26050305c21000001064601c0852109403540039110812100c400c036408281551400c0f00c0250110340d60b06071300714070b1000d0300030030381042c3c4910724001c090144104444821808220025000503800300000322120105100f1848402c46c01c1070110010800603181c424441d00e4451840203104000c20444810b4807014250500c020000b44208400c0f601c520706c5100800c64084400020741c0b0f05000802d01900501c2182c2c000d1034001d00035811517a800d00310541c1140c035070746c2c07458100ca6072207911230000d401040079500980c401d042c828101d10b045407008242c050001d0449011b5102c00d416281c45940002c51082540d0f0188000309503551a051401c0c611701c0ac0364010a28920710a0000060200e40c1007400c500c3c6825070f090740ca18030365070301e54038003640280b981c00d04854000d8401040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 545903309 1250 545902059 545902069
    0x30c01050915040f06080906040f020607020619080a0c030917030a0b37030201320714070806061c060f021603020f031306050d0615020f01050a02090f 66
    0x800c080082180000521140b07001420b80c005078011104044901e0301400002d8100300c180383d05c034005200503c02c070300d0107031900e40c4400c007000000780c007900c80081d25109541341d180c1107a4900400300c0d800740b40000400c10040c0b044000700c0704504034520701038080300c41c0c1e4840d000e0712090713541040f4151461041002c42c2409170384041d080f46416940e510028904c0d4403004c0c0d02002c543e4407043c0c4541044c1041d45c901c586c0c00e000790344001181244090a20042c1e800242000c01402a40c0d40d50501c10500308540130f500c140d101602800200c04120481046401240303554981e4466040c0d45180b80c0c0c3e0040e0941d20703a010b8580c2d5500418040701c208400d000c1d1460103c0a600038000030401201401c100c81c100d900c89004035004040d1082420b05040d0104000740c854501d000c001c51420440d02a102c1041e4080d006850821800040ca26034100003900a40003815015262281e140c08424000e5528010f0802000240d403d000024408144600c00e80326551001b800d03111810254a003040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 545904559 1250 545903309 545903317
    0x108070509040b190b1c06120308060102010b221406030a1403070602040330050d0207030207031203050103050601170715020a0b0405010e25290c010219050702030c0105 74
    0x1600841411a10101c002013640544001c00304070441a81d20b03290a00c1880e105010301c1d065070710280c00d000b01001442e1030311a101e0b94290b010701d013060380f0761a2900100c0c050000007075215403118000c8090100c502001c040c180740b03416550b00030003142081080d240440c40013201d0351541a0001da8450307001c100c800403011403060070b02c81034034070b40780712543e800089820035001035038210f086180120320340480d950a540040005407401b0090040d1180060103882025007500b01f168001c0740400425000b000716501035135202144120751070f1107200c014020a024402951548514800080d02c400c101200d481213101480c0500340e000d050400b0340d00c0048420110504520540d055403002c13816003c5001d0040c0d110300004200340900c0d240c0a40f0b00700c591994500c250745110002000c0d001181c0040e4200d41c410103400d04400074041a40d05e40000c06071381c24160b5000040e18450b801011350040c28a0804054800d2501040500032a000e01070401d0003501984080032425a56000d032000d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 545905809 1250 545904559 545904581
    0x60e010c02150c1c050c130501051206010e0f0301090807020f0108070c170405090a0c030c0509130c2705010311030915090319120f0b1806030c0901060c02030c010807050904 76
    0x103010000d80300b13402004444046410f407001c07100105100d05203601c644844801080c003403070900e04005440c880801c5d5060043c003064103015202c0a520351980701c00f032041c1ba0380c06d0b00030000c0240c1d0205017010001030703005000892060b11250a100d00941c014032446020300c0e090342d65880500301643c1d40c1a61924451074004d10940c0503c00010305903034030340c02688514481c070404501600201c1c00036091300c04ca07203603510512101344102d03441d41c1c07552a0384070000e84020368003007802c1c40031034401e031544019440440400106180202080101003140d1400c0b50820799040080e120509210364403400b0682d2100320a41008180c0003144c1950030b0380715000711400007030b6498004110180c1c0c6a0f030401900301c0011480e01d1104000d00000e0744150035000c143e1700e03000c0c020044a48000740e40040c0c2c1150040310082d1160204070b040d00c0400c0312602c43e00d0040e002e1a00c3c0c0d6101c0002034000301c245c1200300e100344035210760301c0700301e5101d129131601441440c0c13070b0541040780d903000704809840000c03c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 545907059 1250 545905809 545905837
    0x70b070519050d02010606030204050d171608030103051b130902031501180b041b0f03200d0c030c1d150f0a08010b0403031b11040603060e010c02150c 66
    0x4041c5020061004201603503102d88014444040c546001074203440b0958002d006061050000300031903103507004610302e401d501c85181c2040c641003881d441e51901840c50f080c0c18182101c0d01020070000711a0046050324040c9085030002950b80c82c10071942a0080322254020720340c0c2d0800d800501698010300e0010384000d00351028120542c41884c1e440100360f10036518425800b01900d0300009030712404507883d40c01d407024042d042a20b0924210f03680080b1101c01041801c008082e0101c0c0b10354084000c1940c240020305811918005154513038200e03c1c201e6956525010595558a0080c801d02005900e0341c3c49512803044840300d41d080503020558160341154030025202140e222000083c03580909841d00e01d9141d58041d000141211016001500c1200d010401880401e40101c640d0700c0e00b101884101e460f8090600d0800340c0203d0402c6040d23000340c200790002c0100b05c010340045025032107000080141c1c03070901e003040ba50b42e00d85404480307558142e40007150070001050300810000c500810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 545908309 1250 545907059 545907073
    0x61407050a0303050a060501020105040c030b0912030415141b0a020c090c0309070f062f03070f060f1104050409170a090e0a1116140a030c060e01050108070b0705 71
    0x44450070301407014402c600180c0c0d11001c11400e0301a92061401a28080c402080546406e40c2c8814040e00c0c940009020025240700045007800204078040e0342031640104035403130781041d02d41404025552584080024200180d403580b40386401c4003240b151040c950409140410140e45060a83c41b01c0c2c03d80c02140581040c00c5007a4076020f9100b8000d4421040d62030b52880d00701e002c2800c2140b207801c95505c0b20038580d0200400341d840b58032000b12101079030040403c000e00e5134140740e26441215440c00310b030001060200c14080051404000c09008003000e002c2c0f0611005164125100d082030584480e00610082c80142001d034410441548141d4822400f000c04011400d082d070010b003d0741d8001060700005209030860309081c3c03604848941c10038008901051440c854900825002c0c03034150300d08541d280280440181c01005c070030704200c141c54200049040003411030400c100700361402c500349000448141014402e0604845501000d010500d041250304202540304240541d42440340312 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 545909559 1250 545908309 545908313
    0xd09080c0111030108070905090634050703020106060807050d36060b0105090d1b030b0c040905060a08060403140d0f050610170619090c0207080708060907061407 71
    0x100c0b4060014000110141d10703136150801c001d26001050b0819145181044113100008a0000e0401d400c44a100720a1041c02100c00919114080b190300041000565030011081d00e5040310090415900035402481041d484140644460809480c0c0200081080060101c3e0b103440b80d02055902c4044041c0f01c0300c1d42982c0312000f03d0300c50b0030721222441c4000c42000008014062141c100f03052420709006041044000015041c07a107003860280040a602001e0004108000801c0d0080c0d603022070380030401d007080108042aa00302e801628aa186444c2c0400c01c6441c00310443c100b125103880c001d100554403558120750362272195000c0082c4150600070500d0180e1a400380002c44509036000044501e003c0c0100f1840001e58904601808a60495524040c002003005a4000b8042d54138000f01d4442c401c0007101c40001d0307805040110329100705907071034139030200e0201d0450f59100203e0b1005612200050b8032580c0c10380d84000580c0c041c000c1049024007602100040c0000301015600304170041d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 545910809 1250 545909559 545909561
    0xd080a11090d12020d09050a140d1403040812070c030813090c080601090512100c181410090608130c051207060306140f0f0a080a21050f0d09080c01 65
    0x110201c90000c81080c0c0c150a1079810417072820140114904521841d2818000c1491366495001d00391100340e4412426500e503c50005900005a10803401d001070340c0c2203240107443c0c2d00a0b000e00075050140f0101c10a50506c000182c40c52650844000081c040c40c5a984524a900911000d6031042070201c001130458014811401180d40310344401d00c00d46040000180142c410f60400d80c030410b40705000384810000090b10340600b0070141c80014901d0f80c44401661141900300f50900e8035182c0d44400318002980705095945942e090328151651101414142d4203c0c44030300031100094141e41c001041524801403003104140103410050306549c540e004100e10481080d403841d0503030b210710420001d160f403500c07502d001444403040071200309424900140c20b811a88041510410307a1800d114099078802100718001c0c80c0746000c80d00808500cac0780400440c2c8441c40b040302c01030015000d403490f1b68003407400c5a02810340050301c9031811883c0c03003582c8014501103805944100040c401740044500c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 545912059 1250 545910809 545910829
    0x40507110d23030c0703031109060424020604020108150f0402031f060e0109061206051f021b01080c0a0c1e020f1c080304140304090b0f030d080a1109 66
    0x280c1d640726115218400642406030403206070b1000010010810011100c120000f03032264076906141c0440d407503d407003803c2c0c0440c1c000c2c40500ca612400014000620101808425808860070012844905610a416070f103a24048030f001c0d01007100c080000c1c00c000821030004c06203d40082c00c4500305480c500c041030483c0c00480f484055070107244601c4065200d401d4810005100b9841c2691800c60b0300310000741400304032310440c81071040d0b00310f1a0030030b803c6030b800070f20180c034004d00440440c89445450041100c03603d20030102500034064241c9004070503010f602c003d0901a101c02401780c848030208095a400500b100ac10080c503450402700045030010143c183e10010402d000c4501e00e02d00410031950b100e824194400c500a03510007440285100e02650082d80103c2c1703590f1250748608040066141c1042c44003180d000002e00400c101020350320800480d01c003910011021288401419030303e40d18100c00001140b0840001840c13010300c0d0700f081c031900d4400501c10342400c00e4074011420f6209 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 545913309 1250 545912059 545912083
    0xb040b030c13081207021f0909110f07080703120605100c030c050a033f020703120e060f01080a0201200a020910031a0f0105150702060307030e0c01020309030c04050711 74
    0x1000a00c0c41c0951400d1801fa445001402a842d40402c400d034002811030000c902c900c2406940303950b07151414100d14001d540d0760004c000d00e0710340e491020b490046801d03404051300b1000f00364803406500000e422481030030150b4402a11405812582002c00d681c00701880c0700840410241c141d500e8009202400351281c414420784444051800421500551040c41c1c040340f6055030700c1044d0300b00f01500840400003040a100c40050fa00c0091b42002c0302c241c0b0f96405c1e034080d0141003005002c1c05010000310340c2e100e044103c0d0048075590300c2d881d5003500c4444d07143c0e0103400101c0c0340310b0740c49040c0b04082c00c0c0e5501c1004c0000700ca10103a0240d000c10b9640c04103d0b58000c040312840d10820a2010003041c018040540c102c0118061074013103028990400e0600940740104204d420104154035428100c44e00150020007050712464000002400b90802c580030107030502511101036074a5000100391a581400180541900402c030b00900004040c000c20500802c0b001c902480810b40c424404041441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 545914559 1250 545913309 545913343
    0x2f03190f090507120803041407050904110102010c03020c15060f12061b090d03050a0c080d1b030b01090504091b06020609012306010f031103070e01090b040b030c1308 73
    0x1d81e6041c414204009688600ca2400e54500b450002994030012681e005611201e81c285203d10307000c00520b490f0468000303681028441c030501007800085080079043c0c080c2680203101d01420804110203030b00a43c0e41d102e0407071340126541c508246100340c80e0f50f03201c3c4010344091503100c0481c0008840060203010605950080c0080c0010607020400c0308a580819644545c0703018004004030349441c80c0c805010f0708108000c250014041d2160b0303c0224010b8010301100c0e02c0740c03480010040103114000380044195035000c1e401a00c02c0c040d000d0024690f40503154100d10a00c0c00042c4809004031a17422511580110380554050602003a5440602642c2d8010700342840c0c2007400c47e0869140d18a0a0f1140000300700740da484400400c1c4840d44400f080c640386005c82c43c218400c0d0003424602400200c4144040100441c684e8403201444461600b40d0768140e9050b40c40c0400d101510a078000c941d0214001c1001030b041000241c0182030100400440101d5555582d00345418600100d40360706c584 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 545915809 1250 545914559 545914571
    0xe0601022e11030c0901050a020f07090606020c030d1b030e030303070c15050906011503020c120903071a0405040915060f050f09090604110102011410092f03190f 71
    0x1601d81c0344104004400310251035441d500742910310380d5590140701d05103410060000b43c5d128400344240aa5074840817024101e032003480e160490f11015040c64001c4800611601d440682c0b240340015000e919100302d03031641007038500101c500c6458614480c00c2601880300180800d1070680b02000107607c0780025507582e5a040d9003e00d0035001508004411000d142d0600d010300c04207078804100720303044135074680c0451022007044a0a43c06400364004903403050013940546250301100c040244441d0307400301c0540c0c105035220416190140c21a13441032501080a120501c054107107a8020720501d400340ca0610071911030a45003c0941c5d0f4150050340740852161b00801c2913042c56031008560400481c2d1220302840c004411580d00c42008002500301804070000c0b80c0e1030b034001e42c046211003900e41c1d0076445501d4001a440001d008500c20070b8030142c03515480e62100c240c00400040e00b24191a204a03400144035150300941d080500401f00210040386242c024411f6441140e192011250000c114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 545917059 1250 545915809 545915893
    0x506030f060f0a050108030a0203030f070e0904030f0206090a1106070c0b0d0e0d08070509130b0d0308040c060c1a070e06071b050102061902160b090601090b0a030c0e060102 76
    0x80d10307810b031b2044a00740c0c02801900344031a00442541d503c000100c2d02c1000070f81d15003008544a18001d111282c0040d80c1c031080c40241640044503405c2c003500c40d0200c1e0a151543c40a550744c4100000003e01100c850820f103100c3c1e86001801001d585020709611042140c0310b200300c0d03031540d22141403244010f03074038502804070900c10700c881d0b803100240d420041820301e00710001070140d1040c3d45500344540e81c8071b4074403c0d0040113680311900c500c4000c0c0451040f8007842c900541504400d0b9002d44003e0160341001880d54442c0c1008a0040d901400e0b0550042c559100201d00000c0500f4220074003100a0184034542c85000241003c0f0780290101d000b008812082e02c3d417002034507045503045400c80c404100280c0000c0b40558850204040010303920900c00c0660214000c1d0041e005088100c0c40c41400f00e40e40b00014501c0c145e4950003002c000c201007900410207212a01c0c803004100800c0c251003000345241c10701d0200d60005d41801960040f070790038060041e554001c075110000e10890700000e124 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 545918309 1250 545917059 545917061
    0xa0b06030102130b0304150606050a030617030a141e030f070234030c0608040c061e052503021b0a1a1e0309010917031303030506030f060f0a 62
    0x600904190002c40ca031500c0c2d581d00001c460014041c4150007800000400c0030484105019480394207458070411485860f42c00007000e6502c000f40d6400006d080000c041002c2d044800102004a1180000d40c601041d45d1401d40d945990000c00f44030044092011940d001c103814603803070494401c030031030316a6450303c00d10030094004060441c03002c550060340784c4140d04031032200c0113541202424489080510050700704140c0f81303280d0801056503213903140004148d0380026419010360700c640d22500c101070301c039a4201c5580b40d00c1c4000903e03000444091800702d9020b04c00800702202041c00125100020b00001322070608040002c50041c1d0042c0f06501c0b50b1100c881c441142c0d01c208552400d0359929040740941080c0c03080c41141003c1c400046c03524190f22807854072a030150286800d02d40c40c0d00c0c213079119900a024040341511103541541300708020055281c102e80c8903581c6422420700310139031038808800912000385490b41502c03c449000c3c1403c5400c2003014070882951484148901d0082103103c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 545919559 1250 545918309 545918311
    0x603150a0e090a03110d0e120708010f02070c060c0c0504020d380a0503031207020102090a15021504020d0b04110d0f020f090426090a09050a2703230406020a0b 70
    0x2074200004046e0095031110303409403100e10455500900e4030304400ea0604102036a48240119071078041d0103401c00030160040c0140074001c0742c024503490b41e1a803003503580d5400400000c08840c0c00420900c846d18041e030160036080742c5954002080101c0484604111051140c025600810702280e2240c1714034241000540000c01c2e42c2415099103401c0110350703a8014900300b992140402da002800c5a40700754180c8107210002045c0d100090392310f10f03641c0880c0c0700480e60b071f1005002d0780c2c0f03100c00c1c60504003003090700465000d08003d010701c40948491012480140046034000300c419001c801c2580c0d803035000407005000c1c020208800741c0610403c10402c00003861240a0300342c5008020119014824850070380340744812001403000404801c00c401c5c441e202c5130a5101d9400c0d070340810041c400d58400c1c2e2141200c09800c01500c1a50395140e52513004440c915000d1303011840e084000240306c0c102e100890b4410128008802940c1c02020a66410a400c0a401684003500034014441c16050709 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 545920809 1250 545919559 545919587
    0x130b1804050a0b06090f041b090639020d120e0405060d030206040209070c08070f140c0a0512151501120b0f01080414070b031b090603150a0e090a03 65
    0x2004840c0030f48001c108180a0300309114800c1c3c6003040c5110300c50301e854102810b5502e010b40150181c001105000c0c0c103884245c0540000a411800381c0241d0200a88400c440c54080280c241700d44486550440000d18082c00202e0b0880301e21448480055090880c4268299454481104410043c003d000488200401840c0305480590411000c2078000c945940c01c66010b40e03000300c03d50b440c1d080550308803030f00201c0240040b070001b5034001801035941c9200c1d400c034441c1d800c003c181105c041c1d10b160b507482000781c1164400c040407000c20140c5480803800d5002c0800c601603a00700d690002c6005c040c88021a07403444010180c40fa819400d44c1c1c001c0c0c1d00031008185003c10421a4500c101041701881d0a5900506002c2c0340350100d018407400015540310140d400301183e042e143c517105800200e800a40f240514054070558a60302e0070690420381d22080300140100382550390b80300500d12000748003110103802c455504804a00c15044aa12603c241440ca004050640b65450000c10003c0103c9007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 545922059 1250 545920809 545920811
    0x601080106150e150702031f0b040f091101050c010e1213060c0c03080313050f0a1202070e0a0f1812020c0103020412020f120d0801030c0503060106090902130b1804050a 74
    0x1103c2c000d0b07960b0285008104501044180c64a2041c8042031500c0c820382020407a031040030200e50f0f0240400d421101c100c0744c094400b40007601d00d0f00301130026074180e070500504010101807015115480f46002e018004c1c8500c002203020040d103e46039082100500b181007034441e00081680807039482d004940d00400191411424400c1151181000d010135408014400c110000100349075800400c01085901d030000203840c00000980702e041d540b801600c604484d20b0b10b100f01602c2c0307001d00100d00041140c1102080c200030b503880512304170080c40c0e49640f4000169a607400600a40d05000c02440501e1081828808001b203411000e40340804070407400781090f00400081c40000034071105180c0895042d0344001c00030200070f000454400060300904614881e883c01c0044c0264081d9095040303901808d000318002e0b071076206250300c4840900509003c030b00201c0d010492074403a903004003400000340d02a141e9280d11000440b02d40c0d802003003421010000e08080ca08a468144031b4660001e0500354 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 545923309 1250 545922059 545922077
    0x50d08040e0f0106081501090e01060804050111031314010905030705150a06031104050613020d09060f0e0601061d0603010306050f1e0619050a030308010e07020f0a12030e060108010615 81
    0x4c00401c1560001c119080b8008105001d1805901450310040034104c484003100d181c0d0b0b101d180c000c0c000300c402ca030159003544c2080390ba03407061a40602200e00600650340c801c007408a4503150801004142030307645000759a40c081c1d14000c46d100740040d140841c41440509502c8a00c118041c80c03800d0080d04441009280c035001b00b00081f0500941d00000300c06541c041099540e4500041c0054000403004440e40d0000800410700f0340e0365131041828600c102010085015140940d50485042d4110440342c0c1e44400014029070b8000e6111003440c0349404890b01e4007920030700204645070020380c412541d240d103131028004408828810140d00003040703103030328010b9100d42c110455104000b82c49940541c540003078007907111a00d140d0401c081c01018010f080315030754900c1c0c002d0501a003485030040b041d524801141d00b0610100301114614481001007062640d0354940380c4015824050420605644445202c5400381c103201807402800090000502146001c2e01d5000c01c0042200140800c42140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 545924559 1250 545923309 545923319
    0x10030605060706050a02130b091801030803060d080d020a0306050a060c030c150e0a050d0e180402040f02090d050d1421040609020603090a03090509010803090f0109050d08040e0f01 79
    0x10b45052680101c400f05640d122162103400030f10608010f50001084400c0214101001d04001c5c0754051040d40c01320101d052860b00d1100500080c000103012903070400201c1c68501e040d040b8114240d00800040c4e10340b01569000310101d134003078140b0030003203600c40000b009145030980c1c0c0a401040c4605002d4007182487d507005000040080c4001c10010b41218202c1c0a04460713844000f20701d484d0011241911a40e09060343c0d00c2c0d88a001803400640c02998020040c1883d10708030301d0108240e14001065184c50b0700704005081080d210b2103215a081c01034901a5942d080000305030f0780604050700c40d00c440400c009102d1510b40002c3d078403d04d01003000310b0100e00c91422038000725842c042d400300c440d05d581c03800c040941000d41e00a940294040705010130b900c4041903a100d04e500c00d85802020300d030303110240204007009210750302c0d554205101001503824105000c0721f890105140001c900c94464001a09250643c1c406541084000c07034107122440c5400c442540040c0c0b0580320302c00b02c3d8500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 545925809 1250 545924559 545924569
    0xf0105070312050403020705210724050307020a0204230603031c0506060415051801021c0e0f0306010b04090b060306030717010204031a0a0f06030c06260f0610030605 73
    0x1000c11042c140390b07907100207000d0610920500018010041020a400d000c0500500000404110302946405181000941e840c40d50b42c441c28000340d00610020010f03000c2d0350507500c1d50402087c0b04c05501406800300010307a9288a038210454102c1900f098a82c2450480040e10030020712050003035104016005603048981a103905940840b4000b094a6440030041007041c0036540c00141e0801c00b100e10080301c0b80d0860b0141505416030b100e034481c0102c1843c01280e03030301040d040074800414082c0d02500741c20f10a00c11a900400c0142070340d01074448010100b0301d040c10036070003807001c61030214081c072020000e07005064000c0005c50700c95045003001000a80c03640510300c110307e1f208042030030b41158840f0a4066a0080d500884a50700f08088407103841c441100446503400a94505007030085056164840c540983e80c010808690007801c2c00d10950b035204900c50a80d03514141103210035540282078041601c9085003000d801940e041040c203000c20460410501000d05042c94018441e540721 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 545927059 1250 545925809 545925827
    0x1b0305101a070201050405122401060915050c1c020c040608030322060507020706080903071205180a03060204170f1c03140411030607020d090927110f01050703 70
    0x403a4031410742c0c0d4182840161810300c03031544002d0308125032400c0c10381c01200101340701c43c07062003000c0000b9081d9840e1022216060090055502081e4007a005001101a08222050308105410442d2400000b0025249030042900b02900c5c0820b5044d01ca6524a0b03041c0030b0502c0641050b2828840b550030000f00549901006240080c0c0100d008080c0c20095a02c80c5000c1820303070070510800c49400e2882c0025112203042c014000072920764008034925100000880741159040b09551900114600d021a007640c88590b00c0c60010f56404142d00e45e41c0ea804034107500541c4030b4400143e0ba6442d02543e44250241c4000080e03ca8112042506640c0070108284502c0140d07020f0a881c0e40c0d810910075001000e0700c0c5400b8180903078042c01c00c010840d4614080b11300950450031a12170f540e951781e0807680c1c0c118400c0c0c0540001c8250508000070f5200d60059540b0b00ca203142c5482d020301e14002602441070205409546403000c5288a118178101842c2c41c025001d000e2074124641b00460300c01501400c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 545928309 1250 545927059 545927099
    0x1020a091403150f01030c060e0325050a08150c040e1f090606080a140112030804170307020d0e03071d10090c02032101030201080c070c091b030510 65
    0x944880001c0d515076042c801001504050703140074070241494075030030060440c00d01007216400700382c15001c200b5900404044070303001002401041c0841006501c075116514180744000681480800465507540d526036100262103041d00030302c4100104540e02c80784150181034941000010007060103181c440440b81a4065241d1100c00340c1404002c1e038007900b0866a521461445103442000f250301644180243d02070407200c603040c042540d113080c000c64031100c00c2c41132601e0800c0024030100068040c031401ca03031081c0a90040d0407403c180c1c071035058407a48110b0306140160083c0142d2941c0c1034101903106e460000c01c2e001049002d04045003072600e1502188048200e5120b0800511606645043c00e000303007119032400e000c4000500350295994000c1c0340c40d10218945100503d02da030000e001e80b103040780c0d0160f580700c0054407440c01c40c041c80d0780301402c15520320010310004140d00d030380e60103803407114000039502c3e40907021035100040803500050710b50207039034081190030080d840303014101048141e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 545929559 1250 545928309 545928329
    0x9030816050f0a0909090c0302010f090510030906020c0f0a0b16080105040911041a1e0d02100c05250e0f010512210d0c0f0807120b1305041401020a09 66
    0x1008015130b00b0808642c0445401d50400208070200480d01c42c2003c1280e2003230f01c0382d00b4910192070301030301c408845001e4103030444010302450108522031303000f00841e00c1c01500c005141100070703002c49060404060320900360780d0104d0380c0b0504200c0b0885c22158400c145042820340c90031440c60040481e4010b201c0d0070b1180d41c4403907259041c0703c145d501801c11504000d004008149180146411402c1d42104036172040070210030718000e01d0180340022501c40001070680c0403580c010340c02c00001480118600d1308020f00d5118402c009941000300c0609080301003945504c4070a0440301a00c00b51761070300700b40400818201400702100d405082c80b4103403031085850610030b800310162103240c02c81c2c10900e038103414905081c62801e906040000c1030b00301c3c1000310500c505c0c0c00c90682652240c101001360400622003200062070789101d0000c0307290151a400001c6210591040003035100c0c040c90302000f003180c2c0e03600c0600007044283c841c1000821441c03402076040c120640005000e480d01c2e44600e080c1c507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 545930809 1250 545929559 545929567
    0x611300601081b031f050a050312030c160c0302040f0c02190303020c16150302030f01031719030b0102060f090c06031005090138040b0a2109030816050f 67
    0x441240c0c0da8103c010070040040030748a2030000800c404d550491550ba510300c81300f421000c0f40904001c8035240644601500a1506009030705990845d40d2004051002c10603081c00140c03540d0400385101120640245a180c640e24214010070048403c850b81e1000810700d013000c0a0500c07a0040382805c3c080507101d0003141c01f12000e0a0980103441403000c8500c590040d494207050b980b0401d100c4030250b5681c649410241071421205804a00c0141c0d40078040d00c0e40140104006003a00e080d04403c1c08081440a0030500c3c10b03190f00520f4403aa201b01c03004a03407a54996402035904220190340001d0505034440f080c203000b115580c40705075a82c0c9681c010900000020320807001c1031508001000054640d110a42c1e43c0c2c502d00071484c80e90768207910080891204250351083c0f0131031041c442c04524507690300d06880c00c0c1d00820160710540b950701c180700307201c103006141c00800070780910302000030000416002e20300c1c60000c0501d4402441c204031940c8401516031034507402002d03101101c1403c5841692 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 545932059 1250 545930809 545930821
    0xb03091005070c170f042603040b0703080603060408041703040806040b1009050705090f040f1e2f03091c0c060f02091e010c061130060108 61
    0x308100009148940c41c10002403203886940801c840900034000c1c080300b40101c802040001d1680b048644a0090b03441c10300c403c2c0480d00348039255a0344950301c809240815240c88002c5030554006600283c0f80901c045007a400740341d081845598005001c030054040340c0380c580c2e612004c5004500890000c1090183e004110003402c004580180c603207a0308a4201d854103160072442d81c40c0c119100d40b0920841100003840300761074090240512220340300d03079003000e0402c0140322141d071402104a6009854502004181d1858440c03110010034107140b594048c0040200c200a85030850143c032500185480c054103c000c07801820050b408010340c4165807600c1d40c0d0b00300d9140000d00c0b1001c01941d80b80044801d5650b030040458000d4901c40c40c02801405880130106049000b08418950407031840b011402d00380214440c881040a414140201c240b181303600c480c0d04852190510145403140001c0d450f030340c00303044140c4510091140002c1c01c2c1450840000548802001c0c000c0390502c0a6480840c070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 545933309 1250 545932059 545932063
    0xb040207080711011b030219020402070b1f12020307030803090c03030c03030a0b010e0f01110f10060e220b0907030609030e01030c1115130606030308040501240b0309 73
    0x9035a03006503000740c0740d5025040040015070184402408070f2086580e0b10012000b00752a0302c0d0054140d0080d1869501846040020240703000c01281d0065003045000c0016103d1164a802803a140c0859010503411344086902c25510740c000700d040c0104c0c04dd040005990010340705041d241d000d50407903103176161040801d2600344070380e1350554940070200d0b01da01490000805144598803245040c407078401c0310300c0190b45040c03403d10400c1c2c002ca0308100383c00d00c0703500481112114804c00001c540c14524401311041c140f010201c0700070200340e1102c50800c8540303284c1038000e801ca070303020607510390b51031140741510b4800d075000b080140036200c12000100c10603c2401541d0040d50002414008103517140303402018860303020040c90111307240584a280040c4540b56542410401d9002042c9241103007684550515000b0602d6181c18420807c0d00300041c0f05000300c40003584291034024481c01c10380b401a0940c1d540710302c2d0090a0289201409400045610380022169500c103500e6030b13038444190240c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 545934559 1250 545933309 545933317
    0x303030905100e03340b100f0509010909030e03060702030c0f06070c020d14010504230106141309020303161202030a0504092c03190804080a03050601050d0f150b0910030b0402 77
    0xd44544014103d00910800c1071b00da501c41d01200340480302030f03510740c490366602d20703818090f10f508003010400500c120705040e48814907003802400c5c80d000030303188040043e00c0c05000f2111a00180c0020075a15044c000801040100c001e40710050b000740c3c0380401e002802ea0140d524040c2c0f0640340d200c0b50500f80300d01d0110300501c1400100003440f075440c00d07007003088181c0399100000000054a0508108290044c4a020143c94801c02440d008224107801c000b00b00c40901e00c0b0040c00395940180d0301c01a68100010a43c00841e5440b020413001c09081002c0c05030000120002550010442c0078180c60b489801c41e0242c42d404400001c0405400146030a09049070f011990400c1210040381031a42c1f00102038894403a910340c20054010004008640c06141510010301c410412b00c40701c00d540d4000e1300056403004ac103140860901012f01415001c3d110385203492085140d0300e11a005009503241d9540c1c000c0d05958604616102c0070501054156021601c10820141c1d90107034261a80e6481d0116 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 545935809 1250 545934559 545934637
    0xb070503060613090c0f050319110d061e050a08300d06030b10030b040f03110d0507170307080a05090f010f050f10030b0115030f02040303030905100e03 67
    0x150551501ea080c004010039041205e840856403e104014940d03102d6000c480c45030440e80840c922912080e01c42002804101200c140404403e01101e07400c1d010740d21840e4003c101c00d0b060306024818604820294040c990002c5000300c21740b000030f210b028400106025014040c54081826401c401d41c0e91182560310507040020010028010921040640001d4180da000d000103003000d89030103000010320032103844001c0c40f03060742c1c0340014003240107001e0302d41c100350080c14408185080d81d00400c0c10b044002e150080465030100d0742c1818080242003120040e990611144d01d18106028007810101009101c40c0c0d54644400000b1880c4400b0b0205005034070411740203000303803006c0c01620006040300316400d01c0031403406400101e003805c0c94004182203981100f43c2c0d4049908141e28404501040c40c440018561200000103a45402e032008200a5010350b0380050410300310b2500c54144060b001c1d10a03411402c1a0048008030310200c1103801ea032981c0001c100c103680100032901482040c1f2701e40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 545937059 1250 545935809 545935837
    0x60412031205130606151b0501090206040323030f030c0c0109080d060608090714010f090b130e07020a03022a0a0806060a08030406090501051c0e07080d08040b0705030606 75
    0x5100c1031841e4254030038100d44c4510010301803152604c0c0c840c0801080ca04108000410034495502000302c58a4003d080b60701074070001c180b42040d5008511180d1141d403007210541442c0381120649100a4000d034130071402440503500d0204074222140710740c00050020840075500151300301c40c1c105e0075071140d0307080799000d8406602e0305194110400180214420f400c045140e040001d212081d01082d800c1c00d840e080c6c8020085605010011a8240c3d14002514280201801c1c040380504083d4094856404400d4210f11b2890030141302e54590540078000c1070a65001e014080000780e0003040062644404c0c40c3e6040010b9034940260040c0460691002d0304260503140100d1031800200e0814800c82c0199520b110480e60b03900e165503644203500c90500040c05042e000e0103c1c0d80f04000420b40c44610794480c02d031035013860036410115640750321204195400100b041000040c2030214203540316150401003e0391801d5210f0240f0550014030b0b000800c040040001c803560354039000d9600204403942 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 545938309 1250 545937059 545937061
    0x705130e0a08031503161518030807020109060e0a050603091e03090103060f030b0c0a0c0218152202070501020c030d05151e0d171602120c060412031205 67
    0x2c000c52158410303940c004203401c0a80690315581400940c01340c4000b20b0025401700301b46083d2100e20280c44003283c5400704007031020403000d0054005e4074140918016030005036521180c0c8009454038000780d100b0000d001040f190421f441c0e940044440c211035041d228241d9075610044542d080203c505049100c16480d40f55100030410004041e100c0c0707030001c0c2c908020240e11001030314400002844014444240d100010f4240c4010202818546d01079041c041a070048075030000d603582110268190b400480c407420403451900c06c00c041c1074044000c1d24405041c03c20803400030f444405100f003c80c112600040e48008218096044401b81524131341a2512a00c14656440103450180c40103081d400460700c0400d4540341800d04490340d01150703410404da4924001c2401003010000c441a202c60303500d00321890000380044020400c1c0f5848511041d2842150710412244280039070104140e948240760446075034032030710100c50a1311000c024030030158031549012109542880030510714070303081c04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 545939559 1250 545938309 545938313
    0x807090f0c0203030108060c07030c0f0501050a0b0619080c1b0609060105010546020c0a120507030b0a020d0207060501030b0a1506050a021e07080f010902030705130e0a 74
    0xd4024003800140d104140300c11000404200e0390780c00280221807041d044200850300c04c444680041250750300c40d082440c100380c071a86039011078034840082540c650351500200f0020b10b00900c503a41080701d04035105410808408181540d424080182200b44000c000101d0003260540d02540c3d60342c1002d9501d024011448280d941d103d801c04e80300e00031244110303070000c02c00d9030003041580c00114038010010703007500c90b0100c0c183c540745c140c510f41948030209465409030f206031012040422107841d00107101040e119000d10403104400d512201840b10081e1200001907030104820701126080322045509031190b5240e40003e01c034080000030303001c2c40041e0b090100701d0300d40c00c6a4100c030f0141c82200c030591b80c0c51540b4000d441c03607050345030b40003021903200f0f00290780104068100b489445c0f048601c0d064003034007544044402e4803010200b541c080407080100c42410042d001c45101c501002341701c041c0c215070201790b0310b5895000703d51040f00e6407030b07200c0c0c01c070861540440000c0e0f0b01401101c0b00c2903024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 545940809 1250 545939559 545939561
    0xb031209120703020d06020304060b040c020f0d0207050d060b01180f0f1707030206030721051506040803041a1908070815090402090402010201180c0603140c090d030207080709 77
    0x2400400e4025075621064811a220124002c000c0380d402400c01d030481205540c0b40c0d0f00a41c0300900885070140e039105c0c0d4840359183d61040000020880d0000e20204200402c41450f00400790303248801c42d440841e0600a54952000001c180b0760b126501080c140020b00041c1c40c1e100c00712400e40800c10800c0c8000840d851103084981c100c4036505240314210b902c5003504440c0505a0185101030ba000380020001801c00780015940300c0b01c01d240038521080c2d001c00c000143c10918505020700340d203420234070080d50742e19a400d0710728100c21500503207090300d05002d9940728001c81c8140e07011441c20380501400b50122100300c0f0180d4004100316031603c001c240000c0d0005405540d1749001400000000313840041c128035480c200b440041151540c0d40d0385508200088100a0040341155240c4800350003441c0c1d481c00380700c130045c81911200441401c1501c000c00700c6030311038410040c0701100303400c2c0304240810000715486420240c900c1c42d454440340c28248d1400a05600004040c85000b500040041301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 545942059 1250 545940809 545940817
    0x90c1a0301060f050304020f0d02130e0303090708030a09150e0d030f020714181806010608010e0a0204060804021c320604020108190906050f070f0f0806130b0312 71
    0x250ba1254018040300c19804c5429002c100c0d40203400c040400c403e00006d00d40700b071030104107500c0208a1581c002c2d08410300029551200300080c12603001005100030781c0d0702400f40b0345c09030610070011418001c81100c0140a81c0251142101d511840343d0914078142c0b05205146000758060101d204070801d603d402031010075440c4200d0011301541c0300109071468035543d0a98001002080111001c41820f464061a40042c1910740b201e49001c005100c0c808007400110300034178040e12103c1c01907251841583c5100b030001c003400d085134410442840101d1f00166441e4202d0340580b904126202c400c8240c1401c4040700c480a09100080ca4410002c0800e1072444083c43ca0084040d551012600414540c0c0d82030a82d0028040352010780026044201c0182c014080d5400800114648074161140422108180c80701012840000304111900d41c0081880b165204d0b10715060b03221340e442900c001d15403900684000d104481c140c40f141003845c481d800c00c09104400a003034640051242c0c0700014640c2c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 545943309 1250 545942059 545942069
    0x141e0a050408011a0604060e011101060b030618010305031905070c1401121a06031b040308250203060a0e031b0a0203060906070806130608031308010b0409030e04090c1a0301 76
    0x8200360600c00801c1600c0c902d14501c1c1c0c1c0150170300b403c00741440420354035292881d808904010400e000f02e00621000d00840c00103020f1442080d5990030108140400b01d0960002c803c18050400e00420002c1c070000101c59015a01c10032060110200d0b107022a194801c0c1c4202400741820303c40c0110344080844003000403c0e2090720390030081d1022503106000d880c485100b0074600c454512507001e45040402c020b40d400680101310200c0c80c002041c4084490304180c00c10f44201b400426240d0054045031403049445815001000b00001942d0002e85c1d2924018503100405490b03980741d050102c42041a100e55040c8d10030024a0345c912025855604d00d420300d01a0300c24401c2e007022070748001001c00c0c883c5c055507155a5802041c0d50b406c05021002c010380d8990548180c1d00c40d00041d0220052019101c007501b0180001d103100c0c5001103c60941301c851044502c154500200940000e030000039078000c2042c2650040350411450070581280000b42c2d002420088a120428400c1a0064000c0d41656 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 545944559 1250 545943309 545943311
    0x1205120a03381219050316210306030b13020402041701090b0a0209012319031a060f0a0309020a09110307090812070b0a0e011a01030b0f01141e0a05040801 68
    0x4100e0104010003900c00c2c0d840f80800303401c00d1400000307080d03d5458520000340a102281d141000609008107500001c80c010303150b042c00c82100394400b482c40b4065280341c0e04a881c0500141c0e066032510300b11410007801031a43c8004124074002151101d40582c0c00910042e0b0748040c0300030001d0b81d030f00e0280061050071a0000100380000780c10400c00e1094a00310081070359001200c600c21140401200e00c005003d4003019070500ca1000e0b8034842c0c007040001c00003240d8010030f4803040c0101e800003043c190540c1d0362040c601400b205007180b540d5020f6504003404c5113000b2030340083c140082410001290042e1402078200f104c540184c401b0000214026001543c030000081d5445e0001501ca814115450041000411494010071849420680c1095040c1e01c006000c03c1481c540608445540900304030952089072034020641c3c040c4550301480e0f0084d9100300301c0d0101e01000a100c1050b0b440110f441800110340032001c15241c070158100752510170a511b50750780301d12a01410ba9006841400071039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 545945809 1250 545944559 545944661
    0xc010e01022205180705030414101d0a030e100e0a06020303100807080304030602030c0c0f0f01060f14150f0f04140d12030225060609061205120a03 65
    0x2605000c04040c40038180808244803589170100100c1b040e52024105444031605c400a10300c0d181002d0111a1800660400000700d01c0c4207028070b200320413100c0210003e941c110903284000709802212050001c141101c0d54240d00007501d005841c1800d1707030404a900000080d50101c0d085400000550041042401130074a0580c0e480f1004c0e0b858001c0d00031291103400a000800c0003c034207802441d00092202d60240c280b83c124402c1c00e00e0448942c1412606c0c2e80000d009142910003849600c002d07200e150b2680c4d002d03506100f2000d05400714407000501542007100810040d040013010b8074444a001c2040640c2c55036070076042030194105020f03620b40c040d1010708207441d40c039145a0440b541135200200c0390003445658816402500100e0000c07460640000101c0c074200f0b0440780550010b8407590001600c6402d00b000401101c40c690881320345407030211050f2002c1200011a40e5003074503441c80040d560907034441d00728081c0c030b021074900e16820400700c8026804c00718580b480c3c440005500f220441 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 545947059 1250 545945809 545945819
    0x9060b0a020c0603060f04020703031d0a0201080c07020d0c06030b010e060408190c0906030303090b13020d0609050c041107060c031e050606070b09030301380c010e010222 75
    0x90300c40c4051190141e8030940c0788402d01e0a10901039903000c0e200525245059141901260580c0e1110b40b0440000343e03102d4100131100c80000d036840489030810010010b1117519030001c2d0040c030380600950340001000c40c0c11411507690000d0704200a41c402001c041e10b41e52200e0103006041820000e81c0812502d10242449040590540313041b2a200d074020440c0b0711007902024402c0d40810020f84480c03204600210385a40c49000740401140300340d400003542d2f1010f0908041c902005404000c0781d035001c40f58040035a9170100c2011040780c10020004040201d0b26000c0d190901010307629401c2401d051141c0000400800603003030681c09580144109106400300328215101a0104020a102d0760a0f5148846456000c0c43d404900a4400c07450300f940e9464040090004540b01071940d030001006010303042c2d01d007858801000004e218003800c0c610004e540c036034000840c180f40102000c04100f202900c8400d4001200100400000b10754070800c25049280d41c1401c002c0c020007c070008100022 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 545948309 1250 545947059 545947079
    0x2b0203040308010b0703020703050313032003031902030d0c081f1a0903010f090c15020606100f1806080a0b011409090403090306051e0609190506060d050f010906 71
    0x84290303419038490b102d0740c0c2000e165a00035080000143c0c2184104840400000e004000600c6958942d00c4a911007031b182d490200900507a02141c81a100b6003480d105c03e060700d000080d20304003c1401904001072049031812444c41c05005081d042450401549c0c0e47c0c0d00b03400c000e06901607140d01800ca90b80401024141003072402d18814040103107a04801e104c3c41100f040083c4c00c403a2401000820300c141920300b0078055505000d8282c800c1c50fa90141003102c2c241d544016000404d16002804181c9800000220b21100549072a001d1080c08079621840d10721940c503544661051b440325400381501c60303100511204040b92481c80e01d85c030f0854803008543c00380303419400607100b500f0001d00c2d0400507804c3c01100d02c8058411414010743c108080005980e900a092007400702400a581411403d959036a914074041c00d0741e03000d41a64000d0016a12003982c4c10542161045004526903e8450108940e8401c20105061091030b15051100a844040c1ca5a049641e030840900601c0c1e16844110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 545949559 1250 545948309 545948311
    0x10f0207031106070e010516060f06152a020d050a0516091526031c050c0405010509090c0405060a050301030203121236030703090e0610232b0203 64
    0x300805e03400043c201030340d84904018580307040b0800ea2141c845119968003420340b040d00400e1450341c2d46071803060004000c103590021f038000140c50040540120080c1180303604c06440606031080706800012015503e07004003100c226503002003141c96050507810913645510400010304e1856100c22400169000d1a0003a43c290140c040209408175240620070003040c4100140503500480044017040684410f01c003074115449602c0d812070000035818108002c80e01d0081500c0c0c40000144801d0025980c403006580d184074042c1d07001c0d100d54481c009124168012075010952020000480c0401c450340500030b54100d0380300740d086440e50340034000c41c4001c5014040d2150001780714000000c1c404064190710469200848819590000f01c124030000c0902400c680c55800340d000044113801c250744501010002c00040000c4e40035401d003100041c2d0790403c3d94400c03200700102c600f489030907001e58a0140f0403844d04024070560b512203203035403a89003280d6101080d4002d0450b0b00e0038140c29845008407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 545950809 1250 545949559 545949571
    0x9030703080d200406021b0a1508180303010e0c1809010b0403060f02041202060a18090c020f12090f0118080c01110d0e010804080706090b060f0303090f21010f0207031106 75
    0x3404030421210003020007024121100d65100230407050004012038518201e5030750414694a01c170641c944030349494041e4542507154200c5600c00c00042101d500700041c411303040345558480759a030303041d900320100e1800010740815a1180c2401d00000d000c41c60070000f002203a10802c0c0500070450603540140880c01648941002400c01142c0000140350000041c40100854140800c0f401200d168400d007220071074010340d10343c85d603888003119100c0e01009448540405140103114403500c0d010a03030158011340c2c003180c0c000e01c102c02d10917a143e801408505914541c2d681d101101c40d6480320340329a1900c042041c0d80c0441c044d04030804401c1000b01d485000400f15481d082d40e269061030046404050041042d540f418082c040c000000d000c070b000b00c5019500820344074200f420a8003c1203030b10344601440702d102c1d6002704044c0c90740da01c981c4ea803200a06011500c0007214000545240721001c1c00440c140340c1546040b4140301910507550150120601a56502e118818003440c529a01c40042e1030b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 545952059 1250 545950809 545950813
    0x105030c040b060d02071a150112020a020718060611150615072a0803040f030602130312030c0320160501020c0a050f0d030903120209030703080d20040602 68
    0x10140e818903411441000901a244074685042240d5150880e003222104452843c0700000d1900301007110000320b40c0000c0851030f2a1070306002d01002800ca2081e541268a0643c1c0214080c10210300031711444004211448116100c1c400300c12441d0300070101d03401210007045499481c00780e80600001c225000c1d44030760000c20021f86802e0b00300301e109031000030752005030300c0f0400c8034100188600c0086541c405100c1790f10340103c14645203500152040c2d400032061644180820040518a420b00704101c0350801001641c40c02017840b1101c0c00300c22904041d0100c01c1c0302c0c0328440f007a64160321404001940c0c0c0d404006c2d018114403010640c50f941c040d19021190144070401c80b0a044411503001c46110384001498100016169820310829070001d850642121205043c800700610040207400121721b000c100350a1a560094050a08a60101002d40d804200105a0b44040040030055600003614070f031901304820700c1402500c0032400c07034102060100d0f1840f032a8507945081e60250391036600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 545953309 1250 545952059 545952073
    0x70f0804080c01201908070f0c171c051b09060a020c13020406080c070203030304140f1002190908030d09030e040207050303090d0804031b030216080c030c0603010503 73
    0x25440030a80024007882c200e556950b200f4402c480c0180c1c00f1401c8002d0800500c2d0301c42081200e050303000344001d01c0d00002e202c0400100108a91300c0819048100c44a09180c3c41c1492241042c181c2180d00045190310100001511a004a9414041b120003c813a07070080c0050799421616044842c44812241c1c8210820b1001c41d0192804001030b00f00d1000074411a030600144400180c2c507040d400c0301410703400c1da00040500500f0f5200000039403000e12030b43b91900c1d004259012a079039120052005c1c05105601c49000d100100030311001100d650210f0443d8140110194400000c3d03014612410445061180d03240b25071380580801c03030880b52240701a40c205581e001c105009460780346000c03001c20080700178090b6280d80d1031010340f41071030040d0b00a503200c0c41d040f040c0524000030300c001c54041c004800c1c01c000010703910103011150100709807880350042c41c4504d0180c2c50016401c03402d011299803190f0114505400199071140d005c0114200c4144640520030311049200a02582d501600200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 545954559 1250 545953309 545953313
    0x80d0f031113060e01030b0307032a080114011d09150a0207020312030403080c07080301032003011d10020708161a0c0a030b0f0f01180504060e060306070f0804 70
    0x2074800e070719403080103003142e1402200360301042c032940c0282c0000020a05808003c60b40d0f5074580b00300003000708154020015035045440784030f489108402c00301000d12020320a140715000520041008006400080c400707103041040150550000b4043d40c0a14104206026200d44501011501801220002c1c01400180a40740c1c202004010856905240c00b0130017000161001c00be207240444090880949a0030140360080a20344040e02e5515001c1c400d1084202190701d00c4200c0741100d6010b500c0c0128507a0074404006c098005c2d96096a06520300303d50f2003134241c61440001e04000c040001c0d181d0f144280010f0004900078454068107907502809034041228007101002c0c4c0d001e008030b900342104a214900d07402819400c40e02441640e070085458502d003900b40c0580e0b501c1080032900f0143c0c2c9242c01002c90f0707a6200103625641001800b081501c030422044826402134a0080c005000d41915081d01844003c01900c2550092003036800199085210303900d500c022101c0395440807000d40707940d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 545955809 1250 545954559 545954561
    0x30b0f07020708070b04090c09060f05130e1317030702030403030c050c04051e01120305182b020f09040c121704180c030c0f03090501110a030e07080d0f03 68
    0xd20200a5116020b4040783c000400c000b4100100410201e881d544c5003000c0c080c8080e10300354078403942030103420300044c0301c62908500c40500b5228980b034800c0d120080060788125084050b4801900f091760a010301c41481c1c049503c012241e801805000040c111203101c00d203c0380b000b1a0140d0068000b800300307000107403203260004c07842c5018008943c41744000400007812035070180c2d0b040d040b04114100c041d248203031391780c0311500414840386410020082c0d40c8014000744641c002ca60542e5496030256041591003840c4042c0d10a00c8061041e0340303220b0010b02d0a41241000c2c0140d100d4104800c44814910380860303c684541c0d071202040621520302110184030807d00c0d07504503000ea0608242000c1c455039078010b00008e1551380c1003005a80a9016860300b20b50352071105070101401c000740c0303005058001c1102d9071080d07510310b0b000403451018100745004200e03500494220030030000e09a0002035240e0400941d04640106481810f640d5240c001e03606c100c002c1c030340004030700f080e680e1500583c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 545957059 1250 545955809 545955811
    0xc08220204140a0c1d060415180603020a090906120b070215090a0c051806060a0c06110d060b1305060901030603020409051e0d0903080918070e030d0801030b0f 70
    0x805080480c544500e480703803400210382160f203001c900303995200503d6000c0d4404c00d0441c0100100c80080800307241c40010541902c107178001e50014004011004a29911441e9840280110358001561707054441000401a500820100001500c04500461214032503c101c108079882c50111860030505592090340308840203001c00c0643c000c2100400d0201240c030b6040384501c05501c06850071030300603d8240603e211a400c0280100e55296141960308000c0013000e820540460f1703102c1e00e5100c0c0600c221074058000400902035410301c1c2c2803100030301e00c4030080c080c0c2000301d8009118060301c820703c0000c280698150014a6564180100b01500f080d50041800106c10300d00400c0701e035107a07004141512403041c0c4c11940d0b0340c0540b1510791011b0700c1d544110490b81d12500980f0419101500092150341140002381000768000b4054200e0754074460641603078005000c03152200c1c07034816030207080d08110382c105034000d0103540105400680700b1203149060300d50004244000742c0b52419488000c0700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 545958309 1250 545957059 545957063
    0x309060e030c100b01032403061109030c011409060409020c0d020a0213020a09120f02030606060924130b070303180c03080d0905121c05070207050904052b02010c0822 73
    0x1d651f0840050041130380c00328500c4411011021119985035250000c1111b02e01001a00031100601000b2001c1da400b05000d44400070034601241920515260b0b221a4811000c005510010008001646048940140a0250058060341c0c074400c1640b00a0b626101d404800070b44c412000c0030440d20130b25859018001400c064540760107041d032500f0554140c12440b803001d8500d031681c89201821880c0400c0b60960120742982c802e42495910004201f89a161a042540446684500308060040601510b61101c0e84031800c8407040d55641c1d01880c241c2c070268040d4006404c050070910b150a110301081d202c160701420504142d071039a01c481149410030f03140c090181e9180d0034140d002c60401c018403002660700440250380c500e00c01c10488584881c6c1c2c100103075811706110030003595a0f000f288020449005581c0040f1698891810501f0240605000d158104800c24030501e1510090817031020b18040307400801940c03060840c107940c2e158013245d43c1c1c2c1c40b000c03041cbd08091154100c0080c09004038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 545959559 1250 545958309 545958311
    0x306011e050a06030b130b0a060c03020123061003060b0d050901020c0f070603060801050c22031a0106030e01020909060f0103060e0c030a15230d0b070309060e030c100b0103 76
    0xd034a0303100140c0040c1203580301c000041d8031101040038900e4031078070600050b04541401c01c42007040101007030003060b161241d4001d200d99034208405060007908240588031148941c00400040d20804000d5a4002c2d1016401500300c0d04c1680d52240c000d114650130759051b141c84504149035112045c01038a8010084036483d502404100401c840800081c02000441d202400110b0b003010030090881c0d0b0107900c001e0150307042406110710303d48ca5404031624103c042000300d94412103441c1000329180c0941c0000e240310390542500000c20800d54406068a10b0b554040c000c0c42101c2200360300340d000303120005501401e54004101c07640303443c45400d5100381041c10b020075480d5130381d006480d4a040072a202c0035022400810032000c20041c0c42280d03e0b24018034a0b564a15041c03e400001c102c01c1e00289040c3c1145500d01c003074203039070380380d40261141c0c3d80071034000220f1a0804000300944601c6030704440240c02d0800c0b1031215000401035406425010008044100072015040d002d0200014030718145 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 545960809 1250 545959559 545959619
    0x14090405040f0f051b0301090f02061e0c0c0906040902220f020c071410050711040f02030118050a05070509090a0f2f0a1b0c2408060d02030601 63
    0x2a40c10543c0c01a4640101d019000c201103903c1d04460a44000c0400341c0b1a034944101240058404090701510300c3d01500e0103a21140521482801960282002e841d1040302140c000540400018494501d03131068980c00701c1c80c0c4950086c0015a001c21000030750100310070100c0d1a0140c41180300721480000d41e0f9001c034401c41c203041070000700e82c45250754042c1c035080210f05010a01c50800e1032402584260780c045055000c5a600030024000d6403001442c059086800406550341d5402000b0302060042d411940c07569200c04848405a03070146102c40c4d2400c001c0002c500d070202d88a42c520400c0152641c0b46421418010480c80180060008640e81d646001c400c1c0e403841030340314220703000703180780c00003401c8401e1412988403200420f100c40714940d00170003d41044a9000d00c900f0300b50807588400300c1c00f5100750700e8a264844900e0700300c80800040079541c0d18000c2403640100780c2d82101354031010041d40312441808140b100c07842001e501030b1f10940040000b46020030101c01300b80700074010719101d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 545962059 1250 545960809 545960813
    0x606070f12030b1503010b0f07050f19141203010504090203030408071512060605071103190b15030606030a0f051207051e010203101a09120a06060614090405040f 71
    0x1070066800300c40000a540c42042c098a0305044000e20300750340030039032850f04544c13608030b08410364410404031600c0090b011030f5031000c001042003055140c1c20200b0035074212188200c203200d60405440029205e400300b0180080550f1b0340032400030011b141c03002c1041d240d030b82000107010152110b580b0490b00340c4400c100000d00343e501170000c0005044d0248007004000c03039545d001414074118050008000380f0700a0100b040300d8000d421511031950010200241e4400100003074103280215909810441070300c5a0001003000400c6a64419844058060f0184243c54107155880301e084603000d4140d80008520804150b4405101000511072000c460460b160601501d40360303045483c044a807984a000030b01c1814011038041c200503100c800c001c40c00e614003c0c0f05141c01410034481c0100f50340e0310322403214144007483c08480a404014060b9548158405851a40c50f040408191581d51612802040703240c0303e26400d90006620211840c2010300343e1003004014480036100319800009a0503001c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 545963309 1250 545962059 545962073
    0x308070c06050c030621071503060b1305040606021203310809030d0822080d06180501080a0b010911042606010f0510030b03191202010c030506090606070f 68
    0x4400d00c403c0c6a015200c1c203124040c413446010b134003460380740a242002c1c291000840001c1000403074040074603074010700002c40c0c81600100310075001144800d200017030032000c4c0da5041e440e00c0b041301d001b691308120441d0344850407a1126807241c4510300222007040491201c80f65080030100c0140407145001c1c284030788413007101d412011141d04841070540443c00c0c1820b8070b014480914068000c1c14905041d103400107001c00043d0410719903182c1b400c03c0d007092800b4041c0c100156003900c190442d08004103a1031303030900507110000410030618141404000f040807030020900c14500b56000c07640707110b96428001c100d03016102030010b000c0c9030101444001544181405007a0040c480c00303d840c0181006010024207240050700042c0f250744c000841000a502e07002001c8014800600d0000780d100c1410b000a030411401402a407225030822a0740000d1011540709010107031520f8000704140103565000303800752a070450344254042440e200050b182d007098030007080c0152058109190305040390762600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 545964559 1250 545963309 545963311
    0x91e060a02101401030b0604023901050c0a090b21040303020702040e070302010e0f190305150f04030e010f26011d0c160f0c060302030a11090d0308070c0605 69
    0x440142d020302100001003940d40302c0c608000350440002025981107803100310045c00045e00060140f0750000c0e1134040807404200e40112413515074943c420380840a0055403841c90003500b004c2c0365501c0c25002c6038628072890215220f40d0a50786401d4101403030100d201e240b40d000080e021300e0500b61500a41d8502c40c1d020036192283c0e00ca03460060b25201217005100403100c01c04000c40d59580711440038000350781c1101101030f030007404950240e003806a10021030480b061104201c0551061003001208000011030301600c031001c45041c1c0d8081d607640c40c24403840c051060310f000c0c0c0480c41041180105500c50361030304001082505042e0303d0314041d16441d010381c0e072103069030f603001c4110000140f149003102c200c0120045040144056035080c0003c40b500c01d4880c109035203100e00c514201c14000c000940500c58641508200050002d60b510780014021f548200c1c1c400501354601030440701c030040840180c0d90f9424024054440803d40d030758095842d420041d0117003081c052101584000200303a4040c107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 545965809 1250 545964559 545964577
    0xf02030d0e0303181605040e010603151a01090e04030507080405060c0c12010207110402030a0b031002090312070f0b1803070c09050c043002100309021203040b091e06 73
    0x42d5900d02c1c00b4a09892103001c440300c461401c0e0004480c5100722800b050503c1c055072000c5070000740260603001804c1c01001954402410038104180c00c00c94040c0c5540000805001007002ca0341c842103820045400582c9070084440d000300e62404100442d02c40c2001d408824458507d8a01c2c003500d420006460f5005825444096801044610342904004080e5140345586130002d5040c400f140e41d4485058585026581c00755a0120000e000042c441c0c2060f1941840581910419050f0700325100103540b02c5843c10b4001e10030711320110703c0748000f0400c47c1c0c00c85800c00c803c840192060303500c1d180e45d100003802e4440e82c600f51080303078551740340103000825140e03102d000407021207454101d85100703a800043c59003084110a100802c5203440c1d001da00000e1a0805821a035000201058000400d1a0441c040e4010103680700183ca440c1c0c02d81d100103c05030089a4845003101e9a800e05680da1017a03000b901c61001e41408045035030b0034000d051382c07500d01500c1ca004103c4000ca002140d8141c0200c181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 545967059 1250 545965809 545965813
    0x4150b040f0527010605061803070308041d061c0206180913110a031a0714040b07061404081b0709090b01290f0d1401180c0c02030c010f02030d0e 64
    0x9901c403e034014001c0c40202c2c07040d00c0207008045c5403e00180300d6002d0074482c03039049003820071301446a9a051140d1005198441c0205850300c0d200c1502c220309028100320719500045200115200b440d00315000600700f4121f40c900701d4802003d900b4003a05802240039aa8891030040f00c203078182c0c2d1801e20303c41c4030f6143c07002c01001d1a9414205010540b60b00000b583c01070074030100900102d15203000d044400c5030080b14114840d201c402d4201c85e86c402c0f0008001280e0404903010914200c0c8800038100d25015810602804075081240e00001d00c0a441c000c00e07100042041c045090601c04446084040d407505559225a8410b001c0040d248403003011074451032190018040f24002e2246c2e00041a0466050207030f0819502c0d8082a0f44500b414540d0a020041060300300020b01c1e030041c00240c01c6d440404281543e640850101c0044000001c41d000790400c13001c0d4220340d00c0b8078000c089840d0014003c000c580c50280056680d044400744000071170000700942c060f0b20204c2c0c010203424810040c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 545968309 1250 545967059 545967091
    0x21612290f15090c0714160609030b07082509170105011a03070504061409040207030f1407052121042f0906011b05060109050a020304150b040f05 64
    0x482500c109501c2c2c010910400307541d400e00001101150070b0315000781d0300241100e003500720504e4007464541309088003030b244417002a010801a5000f0702d02c0e03040300d118040c5100942c5a034075080c1e903c0e40f401c07100800c1e003030300d6100300005011048d400d000140721581040038200340c50303c2c02c5418030821041008000d03912070004100c840c08100194216804c030100d41404c60900d000c000b44248220700c0381c00100840090b0001800000300d044804001000b0401c65484005240182c603070f4840500c00d01c00b05030807490f4000403c009000302c43c1d4456120001d480d250224803030810500081e0140a0081c04050241c0b6801041c50b8a04607030401c41d003c1c88000a03d42031601c090484d00d490760881030800c1d4554a0035249540a410080d01d80b0200c4001034165260780040328091007000410701c00103a440c048005205000c21894141c42c82d10b0b4080c8807551b600302e444820f0303100c107540080c45211a004201d81002040d44003000440c0d00800101e0042c40c41c40c250b8059a10640d4101c4614081e01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 545969559 1250 545968309 545968321
    0x402191107060507030807030f0605100201240807030602180909072408070c050c090a15080a0b010312030605061b0606040912050901030204080102030702010507021612290f 76
    0x280c10700800003460482d00d0b04600d60ba0080c612400a464401819120f90040e104c000d89500020003a04024007804001c84146c00004e0180c8459030f881c0907424585450b4440e15840000130300251a06000103007002c42c51aa9108001e501c00c42424221080c08848088030b40c0c0c40a0015001c4c01808004000c43e03403c1604400d480c49840010000103ca0124000105a00704000640c04400d41c10001c07403406850400c203080503421101c450344442c0a0040080542142e41f221440c246414030140f00ca40c1c49021a6030340d00c60b00b01003d4244c409000c010400101c0c500701d4500200001e280200d4015580c5003c5650b60f0010b02d103002e5a600f81c11001054954100074035940018111000c5c07191601e25140c60604800300c0540780104070340002c03d59603a90080c1c04880c0103240000c0210f50700e140c0a500207008100a4031840014001c60000c1980c2e54500c1e400708041e19510231401600e802595a503c0f00709925003c0c480b004140000c06d0a0404a21280c1c20310610341c0c10304820b01d51401c0c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 545970809 1250 545969559 545969563
    0xb041a03070e060a09020904181b0e010308041509080f102702040c1814030f03030c0a0309030c0506041a0901060b070803041b14010306151d04021911 66
    0x50b030050801e8540030701c104900342d500c141304407086800246006941d041d00c44007181c080d002034001d5841e5200c0c0d1083c900200918540f041c00310b95480070030031a2007500e038010030341560360a1002515401c1d05200c240b18046256503005041c1110307080001510f0340da608000e040505207858000260404c0b505054a03400e58040d80d25800c5021032801684120b81d507140e03244610111000e0301071030381da81c2a080c80da4003e1203030300401c80c604565010344e00d58515484410a1810105a004e805045c0320308406800c00401c2d0b0f401408240c1c0710604100c07100400b10b004004544081d8100b159007045540400c03400e000c6180140d016260070308103000c005080500242c1c02a092001c2c80e0f240040801c01e8412403801c2c0e4140075808080d0350f6a94680307003481c1040c280398032008031780c9800d0600002070504030000c02d036817500c40a0301c083c4642580c6c3c0c02d4011700103d10000a1010685088580041d00d010300006404544020001400d00020300001e0740301110030b0311324070049560300e80c0d003212580302 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 545972059 1250 545970809 545970823
    0xb0c06070e1f03290f030102090901330302120105010912020f060403060501260d0c030c0224040602070b0a0203040501140d020a1709210d0b041a03 65
    0x100e003080006060900085804051151410440749904000d403000e001e110b50407110206504002c1150a46603511004c154802001200c034450520742c003c4100038141030080c0c81800d00002e1140314642e1030102d10f0005805005044064680c001d85540c0100c5884c4490541200480da4010703101c80902c682120f03a41410382180f41440707402c1d8820801d03110020004c15410758107452282e02000700c940030038400d0040d504000e26450604002142820b4101d285030010b900290121041100740103400d629003038101038100008152420440210b4040c0710b101141500c003900100d06088000013007195183d15110403198007100090420419604200325000380a216500c00c0c60400c400305e000e580c80c841c070301c039150500907a58031381003000900500f905c0142c00e204d4002c0d9900d1244101c000c1241049410681120301d0680c082003070800d000400c80c3d0a0344000c00c402050415406c003842458010342514403002d51103103e07440980c0c0300c900030360404001c0c00d4070850304107120608140c10062 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 545973309 1250 545972059 545972071
    0x150903120a0806030a05030a1b02120a031b0b060f060c0609011b02030309030d090305040317040302040501080609060106050310170d030c110303221b0305101109060c07050a0b0c06 79
    0x1105d0001440410004821240360582d030341410102c01c2d010140000c1c003003040303413400307540590303103c00d5080340a201051300900d00d4400e07642d01c00300b003583e4026444514800c1c01c0244c0048904000a842030411507001c07401e0001c014111410220102205403134400c4c00c0b204015165150340340103010350303d180c4641d11420287c0c0023840c11490140d144a0f0749001c0c5600303100000c0c1d120030034642418011000c4030051500000c5490520340d1a043c12000d590291004901891400e0000141680b010841500031a02000134050691801c201180c19130009800da880100b8500c6000401085c1d01025910b0502001c002c1d1245150304500a403c8507022008441408a070425400c0c2c204408801c0300d07070001031819a03a0114801010302011034200715002440800f031044140d2110b003001e040401203038031031002c807260081442c2c4e446041c0c4000403c1310700aa5800d1007440b4030b500e001c4025184a0052800b100c00240d80d1b4000215458503540c011403001d5400190381c41002d0f03060044030b334009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 545974559 1250 545973309 545973313
    0x16080d1a010e0616030e03060109050907050a0e132a0512010b01140a200115140307030f02060c06040f050d031a0d0c081c09050307050906150903120a080603 69
    0x756001021829512036204c01010b40150444402e040500a02c988500c40300c01a0403918290f031201c00f0000240700c144c80014113031066500c006818945100c0100c150786201011010517101c04001d00392080400340200c2d456005902090b0302e942c01c3d019980d9403048060714010750503240070207010320b40c48105859906a41003032154200ca90700701451a120b2000307001c2c020750f200340c00001100c45502d0300408403c252080c14901034503003015000050301081c10600c0e41c440540e2100351b01046030030342918a400d03402c50107003040072658060070b4010140c0040c280703500c0c01c28100e06150a2500803078003240c86401d0720195205100b81004034410f89005400c1c10080b4041c1000071901c1c20b00718080c2c2c42e1044014884540400c00400728000040c40e04500b1149481411a5580c4180104070340081c00904d24420018940ca8002042022a40d0103001144c10b80c07511000c0c40b1300306080040b40d40d040c110410254000e524100148089040b21000040d2105032140d00184032010141020380b10f5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 545975809 1250 545974559 545974577
    0x6080606040f0b03040311011b021501080709090204020d09030f140a05040306020309100e1f02040b092e08060411071722080607020601170d0516080d1a01 68
    0x41c03900b01ca00c8090b9403c2c40010b0b5140c0e80c40740340071160355200d042c00742d00395420109080b031443c01c05c503070500310402035400f84d175012064a20f8004140b042485070700b02644c44a1020406500c00d58030103245140040c2000d443e190b5214100020f0710300000040740082d01015125000c4c81e07100350b0382c1e6004940910850301c0d11703500c00002030040c007a601010304420707400408101c0c0524100190718046200305003e000314814000e9254407121a010750710540c0b1200407116001099038401c4805507800e00c50814280300039101408601a00b400c08160450861b9034010b041401100e030340181c010040c0d444086902c0c0c0042171000342d41240362403005041d001e22030f40000405201c0d803000307034411301c81c0182e171a00011003070120140c410071032001c0000d04091001c1003400000c501c241c0700303104640889210f80d0341d83c01041c68880d80080854400d410121000414a104800038a46201e03289491180e00f00310792120044c0307a111a001441031907031500b0400400032414501c01e1a00c60900b000303428 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 545977059 1250 545975809 545975819
    0x31606081f0335070209190509060411030f071206110d0207061103041509240b09070c08030a1e0c1101060503011517030c060906011a090d0305031b0a090608060604 72
    0x1d940244c0c4002403040f0003181c00102c0d1a11011500e03006980b481105012508004a0b1984c480d00d040c0c5040d5092200b1281c80e2069040000301d20340b03580e0804006100c840e00e8601078800300825543d04540700ca8485038540140c11000c40a024148482d80700140c2d40c03070f001c0ca090001c4a1a030b002484591806204200114111008070b090b03c0c2109180030030b240a051030108080013448a1160000009038160308203901039071701070405100250760720012521760000996021081d980010201202040001ea40804a801c9202d00008100203580341980c280e25003401d50300d42c00c101c14001800150780c012010f409018000041c003058008000b26000520b448076181102d0064100c0180440c5d25192440f904104440c1451120815030fa0141010440641c80e550702713102b8091118103242403605c00768001c400315914200d0084c8009241e0b4a1507606550310307000107202490302d5000c0e00e00084000c0d42c0343d0041107802002e90303488030304905080c000b0b0480c1c1c80180800303025081c240020b0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 545978309 1250 545977059 545977163
    0x17070605091b04061401050d14010902041404090210050d020409090807021e091810050c09030f010c0e091e0c0c01060e010518100f0e0103030e031606081f03 69
    0x901d14081ca441d23a03641d054240000050310a0705808042c05030700900018640340e40d81c1c0038000760f41c0e0340079907440d590710018200400c4d01d0710910040d500c284401148007285009174014440c030b110070080503050559594044c411a6103848040e80c0ca9107000134031800b1443c0081e031021083e000003690b90f900640c0c20000c40d0700b464004201d1103904244541d090704458081100b080a203e03452401e000c03515044c40c0486880e00700030003080c0030748107848040e03940100c10300580804280d07070b94400707440c03a030128100545400040d00540d0078211078041d415582084107411442480d440c1b02255480d140c48420b182190740a6220752101c4034294014015a9034102d00c17a421191624044049901c40030910010407019501004200c0f011f400001990009a409941224047c2e1141202e601c000018151501d40841483d00d44c4500340340c050014602035a00d640d0400800455100546113910202d10503900b580c00945460f0502d44000914001681030391402022a4039007015820800305010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 545979559 1250 545978309 545978339
    0xa1208071d010302040f09020d0c0203030108150615070b0403080709030c1502011d07080c06030408031306020c0f1509190b0705070204091a0a020c030717070605091b0406 75
    0x1240c07003440c094640a680c46034041e940604000c0c800c40c070f031155581c91940025402000540f400300e080602070104a400802564100c0301502d005d040c04052900c0c0780b4141c082e00401207581f201003070004c800810001030181a54910076148044242420f08024120070001080300f01003007800b9130107000007050300b0f0100007190400d0424906150502000780d01401d00c0c40c00381880059002c02d10039070315800080035812a115a419915010446c800748402d9120490f4007500494040020407411001c102d003020015000d18401410128001480360a00b081c00d40350501582c03040403030481440820024075001281c1da401030241c6c1705001050000d2000d4a4006440241c000300021805402035007143c481c0b59008104000d00041c0713180c150321031202d034420003030400211400250b1001e003500c02c0315403a0b9803200081d402d04400d5500d0581c0900c40d40c0590034450b50034449040091128052140107102440280c481951080c1e0318040e0420340080d000c0c8228100070741013010381d4000c2a04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 545980809 1250 545979559 545979587
    0x10e04033f05150d05010e0d0c0c06020c100c0303090501021309060503010b0916020a080301060306090f27030c1a01080d02061302040e03090307290405030706051b0706020a120807 79
    0x4413404980504120b4018006101ca480d0240586032100c1002944502e00c06443c0e44540c403c0300d461394407040101c4e81c5e1040f20380d40e03980006000700700d10345c1c3c1406180d107850714074031031f00d00400e041e60182d40c0d8600f660000d00007070401084000e000c0c80030001c1c0d4021a800b401c3c065000300701c00010100002c1d003440c0082d2002020a0f02d102c00302500610034004918803d801000607039072560741c0c41000b0010326003441507010706803030b00c0b1600d8102451409034219241c100c1c04400c4911f0800b03000e02c1c810144003081181800000d18440000400703c80e0f0303000410425058000a940c98401c446081104039420902190030910422414204d00005d074810640c0547d00081c078485120392880c917501c07030800d00c154988134403500000c1009251050301d4000c86031074080080d04280860407940d40c000c0c1c6c01888c0c0e064002e5281403000e01d12a20140c030150140e10302252400b1510350100341020450740012006130030a407980c60501c0b840204a100300d241c13a1070410664541580001c1039181b44102e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 545982059 1250 545980809 545980819
    0xe0604020d03030506130204030f03120c0804030f02010f05040c0f15080a09020a0909151b120c020115060201050f1b090f031f2003010b03010e04033f0515 68
    0x450000d45821004031080d03c8505001c550b91030f1242031000c04800780410407070015828000803880722940703002c0d04444803a290ec1d1184d030341d100c0b50703800c2c2c4820b88103a04000443d075903654030100c002010700406d4050f40c001c090020099080a034840c0b1110340c1c0350401c0c400f4031080b83da5125500c0e03002d900345912910000b0001001d101a10014240307030184c0c0d101504060a128003401401000b2018642101c1540000c0054540c41c3c1844421042200405008908085501008500300c0d4100170004031480c400060048101c0040301001e00541d0031400c0181e55400411142034070302d00d01250428010380320212082c041403501c1c41d8511074100c440e0b0207080c070404000c21a031400c0010385540300c00701248500074600c06030307640700400c88a48940690760350001c02800c00c038103403c105c82c162420360b0b20080c03542c1c1c01c02c0b08030160800050411420800c5242c01c005031000006140303061070345c00e14121054282c0a00c20342001c0c00d00c00c031408100c00d1804051004103000464005660001620 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 545983309 1250 545982059 545982061
    0x307034e020c1b010333050103050603190204110a08041b120f0510021b060f04030804121101110301051e0907210204060e010809010501080d111f060602010e0604020d030305 76
    0x40103c005d809001006c40c040340c1c0b2008441d40755564032102040103159243e010300090b40d81d2004409613031081c2c40154058001c0200001d0b0705481c1590900c5c0b044c00940007040484a101030b40000f6484031440748002042a0301380b000304019400c41980c0c80020f042d01251090408000352059079454030010072803605011040d08011003480000d1503040102c80031512003030710003461914012180c00c001c245000e00800602480e450466441c022500355440301c00c0e50740d4596400b203060650b8507001d0305200c0c84018414500030300340151a100c0f168202040c0e181c0d49444280f15038682071850a052410082c00f00b50002d440314100d40354001c0c40d030302d02203141d41c81d4024449003030b0725030300049030b502800010041480c03034000042d141014001c0e65001c21681d502014a801c8034001c1c09040c5154200070044c05e0303a82c4c03150740040711080c01102134540034600d2000040c0c400300d84c05500641207855010070001260281305550811152402a140c1440c1c41d500240034010080c00003014140d441c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 545984559 1250 545983309 545983363
    0x901051e04050c0d0e0a110402030903040b0a020705040b0d03021b0406120b100e090307021e1f140a050d0e070315090c0b04080307034e020c 62
    0x80d1010408503005403080099041ca000000050b80c02098040c940604007000b00c2a07100001a000041d02c2e002500c0d0410200301c541000060762024003240c180348418000800d09500310300c007c11a9056540003070040c14608000c2c00305a8042d489054440e40711202004042a00442c0b1516030034002c9200100104c22080014001c1103550022160304220010750410891108440d5002d0b03410400d50885203036480d540300d403a0001c211000d01c480e8005001040c0181013103480c00084802c00035800b045800c20f940818612001c440d0410b0300049a0316070101810703007107a01c3d020a0040d09800b689804050341014249205d200301c0000010380d503081c181c2504900380b11400c00303980d00640c2c0b02c0381d884030029220081c1c031188600f80e5003a045000000f0785442d0404c05c8030708031004480654202102c5803025030b0203028200703040c40c50100d03150035002d01115420149843d00c20045590a0b00f003154811019000d8581c40da03501c2c100c1c81000307400c86007170000841c0112038618400540f0380c0c038018 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 545985809 1250 545984559 545984599
    0x30f0204090c0f0335040b030a0b120120190809070b04080601060f0306060909150305030a020f0c0d02030717010f0f021b060403090612090206030f040b15090105 71
    0x59120b03c490005142010040000c846500d1003102210030b0800c942030307032a00360b40303452048010034800140070800c81007115601c2c100c040c6901a041600011791030481c103020030015203140a0528080e5925207400c007a040404241840040001d500c0c542042c806000552201c0c1410303005c4014810504005461007208024240c00303080c52200c403c2c2c0301d640c2c44950f0380e1746040a000b010081000d0603c0c07181d01030310070b20905040320085e98401c0081890002c0a400500344000c40450701c45482c0703c04804242c08100a164111203035004041103507605801c00d0800312110034480c4217030700c2a04605e025a40005440e025550003820040601c0700114506006000e03400e0708081250408200c111004c98540c00b41c1040c811010b07240000394402c0207002e0302c0710f0741200c0040124500c24400d00c425072140002e00070401e03111000042c04415a0001855074000f22281c03030114601e402040204610364651a0f0000d04060202c8014001702000a0200d101409914068000c61076082800400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 545987059 1250 545985809 545985833
    0x170307170405090702060618071b051606110d05090d0b01030308070809030a020706031109030109060b0a0b030709090c1e0f02120f07060209010302070c0b0c060709030f020409 77
    0x8000c0c900000340c0d6144600000316041441250701c64008400010262800803807580d10412006102d501c10103001c0c02c00c901400d40140510040141009a90040480740b43c890700c92a40660b0042c01c0c89186003c01008440080c1c0240d01088103c004a61129a002452144500c000d00b4080c0d202c5145001044ac06140d0107400341c04003130315000010506410a00c00c500a400c240e80d4040c142c0c2d60504207a0342d038410000e101005a20a10b41040748034400d60103d400508005880b51814100c080080d007901e004034402d4500716500d2000c502646864600d403c010080b240c521410340c40c1c0958050a4030b0110302c42c0c90746460704e45e05000001c42c82400918100040240601250600d141e001010314800343d00038005403080b41d03c02c10307810800c81d060704d02506401c0010b1b481c200980d510400030f50041244641403507020300c40b031000030306201e4020707000e85510314070700b40c60b155a102980d141c05009007a20040c014032150510214802d400c00142c001e4040d076000c20042510300d040c15049c0b038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 545988309 1250 545987059 545987063
    0x3090907210b010801050105070803160905040e0f07090b01270b040e06030c01050c0d1103041a180d02010801210510090c14030613051002030403170708040b01170307 73
    0x54808141d0311100940d001e9141c00c1c41c207a80c1c00b1003903070b02c4100649641c4141000907040c802d0031300014066010a00c442c10155002d464200c1080350303148046002d0f00d1313002544908540003424002d0015000f044810000c0c910713100d0a100b070010003070000c0c1401035123040703001265220000c0c640350705003808220304c000c1c050442100e94072603417181388840410f01540c1d100d2007401040354000301588600d0039208030304d07905400303012502103074141600c0140b0f0300c0c44d06c82d146007c1030000113000b906509a001c0380b440404041c070b07a0340c8034585402c0101e000010099215410f12410704c07001d40d0740490002c0c1520707215420b000c00c0c003c0a0f140e5405001c5d803018011710910070184012040622070b0440b0f02c1c002c0c07003881302002454644000050175a419440583c2607802030740040d1011a1520702d01100c14080c100307441038010403803410010799000320ba0a40118003c810040b00007403465907100d9100c1818504050281015070351311030101e83c18812084012106c0f02804032101c418011919000d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 545989559 1250 545988309 545988347
    0x7050114280c110108010e130318060806010f0f090b0c01090209010902180307030503072a06020a151407032003100f0506070f12031b2a02010203090907 67
    0x545072041c0203012048041c0c04603071060392825100007039409008224181c601c0506400c205603140900c103011040c4010341030b400c000f020380b0358100d0842040ca213030b80070b400e069407890f00603d0550009410b101d10b00301540c0400003425401c4050030f070f100c9050425943c0000d00c25541c0c1108907030050141803d094040d520404003000054050082d0780240001032a580c00048448654020140c480c911071102030a560020046403002070a0f10704480c90705516a00c8110800c00c0032600d8087c62230042c0c10540269100000a00c00d1102c8104013400340c1c01e041174144280b102143c2e40c100b05030300180072042031644910340c11140302c094002c030b2402040500c03d465260301e45039a0031001c200942c0301707090b060440e0600104290030700b481121702203034100d0b04810360007034299100c141d12070b1940310700020544d48844a403180480541c211907011015501e1321455030040842c085440d01c00c4039018181c08d0400e04c0400143d0300801034035a0710700c2c211a04c240560f1084001e48074500341c0e0740c10340002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 545990809 1250 545989559 545989627
    0x1912050f0c0d080a0e070510050c0709090b06090105030d0806011110050402180603060705070501020409050a0b0109140d0b04110603011d130b0f06040e060a020a030e07050114 77
    0x10600d48200190703943c148103440b98440801154003160303110f002d60704a038000b40290305004400103d0003205203000c034074152185100c2810405550041c40041c0d8407440083c051241407003040380c2105003115462510b51410000031361312480b0000c040c0602c50800005819607003c0da000181c41c00305001074440b80d40b20f000d100c0004000c101c070220310035210a594003c0f01c0510444107032040002500922464688000a9885170094201200c0039074003044040b6503007446020f1140034980c000d10100d940240d0030000744c2402800d40180c8407604034803d080900780c1d03a0010880d1166000143d0110903262030500380089c5054801d45134002d0400400040c2000410204003005030314090301c0e103480e4540000041140b900303020302034000c103046004180540c010280031608010001c0c00000ca9201500b14181415001c64045404c0c42d404070340713000d035150540100004408044050030b03515062000291821000003548415450082800e010007060162082c1c0741c2c0403001500c01340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 545992059 1250 545990809 545990827
    0xf0405120301170613080a200102070303090b0610120b04023106111e210d0b03070e0c0c120c03040603061e050f0303130f03050d021912050f 62
    0x540c051100c80384443c0c3c80f6080c001643c00c0740034034000300050f034010541441c0010b03d02e001c17144070150303403001400e0300ca40000b9014207000910040c11414400d46010035101700b281050b803603020740285083c2c0101c2102d500c11840307030b500510124405405290010700d8024510105009000e000c0d401c1d400881c1c0020304440035940d0f407404080b0000c070385000a100b5902e50b041103503080090440062164001d41409208001c3c01c000715a10301880c004480c02c0c00350124589515206201d040c019544002030785070404400390049118001d002c1d0000c0a24618206082c9401d9800600804e80c940f00800c452540100038082c0c0b200081490240585510642d801c0d03548980c054030440340443d14014000500343d08450725034105014025203500741c1c901c2c0ca0b051000c0c25a82d0020643c0c10b0004004407111558130894210240038200d03181070006085143c030b00d2420031811040019503110943c449403c0700801825800c0c5940203174000c8100640311810307912401906003a1856520208071501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 545993309 1250 545992059 545992079
    0x12070f05120a0b030f0a0b06090a020c010218030d0302040608061c050a11010f09060c150b06040b0405090901151505040306050a0b030d0f270f030308040c09140f0405120301 76
    0x80040c0044050303403d24085c0b03d8825035030b803c0d40c510041c00d00d03400c00300040172071a0045076242d04c0544e80701d001d4501000318070f105089134840102e0b920380074109000c3c90a41d01f0100800c80c0317182880d0a0861810382080000381c200e540042c68588155071805601d085113120020020030700f68008104c03000f59a0501d4440e01480c56050200d001034000000109994482c21100003100c1c4152100c842c0c10780349494108002017143d0111228585540d039540a0383c542c0300051000345440419152030750306000c20040c600401802040c0d540e07040c00340900d46110042140400c5070b414020740c03d4188840c1c3d0301540c15016650000c1c0400d407401d02005442c042541141c2d0100030300714252000740000000580c1e1383e92006040000080b07050404080d900609540103042c8070200400106441d84c4030819030b540c070b01d030b90800c40004052009000410040030300c7d6002600d01d151042c02130b40003c01c11402d08003401014203001c91744010100d018005c0a1020042444405540729665078468140d20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 545994559 1250 545993309 545993321
    0x60c011503060b150307030902030705030f0307050708070b3406020408010516080c07020103091202010e06240d240c11010b0604050d020604080d02011b0512070f05120a 74
    0x2d41e80a003080b00020346032a20014004010095000c02421629800303000c40061610640c05c90705403190030000b24160b6800c101d00703070501882ca002940c0d03420741403034102d041480550180c04141e0261605202d0071041e4005e6402c1c03480e100d9030f40c8842000c441c10b00c001840108144054491056080a0a0020765001401a039610000038003107619000d65411801001e020b00600040446021500070a028001803100310b00515021031884040c1d01e660740e01c801443e4115002d030703544442e100d54460041c0300c8294450303085617000c40205060b9a451030440500707043c161013110007209642c10004001e8040401032035203240c0e01100c40031060414010300e182004c7c400401c10284144841ca10140902c0d022000007600b03080c200b52a00d018407100207a003402c101d902240034000401ca03000108400d403400c1c05685e00100788a500101c40b04219409064a5410860100300c1e0008100450b11459045511403500041070403031894129440c1c06141e4030003500c0000442401f20303450541d0056 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 545995809 1250 545994559 545994563
    0x308030108010b1c0b180c0909010f061a07020108100b16020301060803040b0f0703030905060403180506030421090f0b070209070516060507031d150106020303010602071202060c011503 81
    0xd2002c480f03291419400300d030136450003400d000c02d030340001c2c40c0c80e10602c00d40c0e5403080741e40301115011100f0000040c0c00361807c03614003d00341e660300d03040b554040a502903000140203181c100c00d00c01220381c5410340ca9214400b4084d0501240601190b148d5400542c58401080c00720581d580300c0c2d0000402004000c00c1002c241c1c80ba60030071a01107500c2c00d000c000c4408031000b40e150f8614024030360038908465040498260141940c0300724000c003213801800068442e620130355170200e5014500f11210094812a0040350256900b40f04000020b15580014640511344170b180e20496204250f00701d0325150541c000e80d02ca1350f103c900c00190018004041c00721180700b1100054141c2e107581d03040303903d409110114030316044803e103030b040800e44542c055500107009240200303940d020308a01d4110f40480c491105000d40c00f801c4101240309112174610b0140c0403a1000d035256500d0920000d40d100310742d0040c2c0940c9512000024115a215801c9442111000000380510303500500d051402840a01c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 545997059 1250 545995809 545995819
    0x5010b070b071805010c0602210406050f040f020108091e010f0e01021602060309150118050a090b1503100c020705031002040f140402120a0506030d020a021f02070308030108010b 78
    0x20400d1a401022200f105040303000e0042d4800d850207004640104080009582460b402c00180018a540c042d102030b00b6544d070042c511081c1414901342c0110b43e8010f05108500700c0c10f40501c400a00540400c220701070b024038120246450328810a814812000c84101e541e52000590b00c0000c0d506400016000788800f43c10007040c1ca01a0800b400d03881441000700d100d00f0034115010051902d20007840c1c000b00564100c071400d0441400e01d0004c01400c4c0c111851343d2000307511450a42c03405010b45a80040354040c1440912069903ca4001060107400059640b274005031858036030710100030103000c03540040d50a001139101004061b40703445090081a0082c090503d10964046060085804076100700e1044002c0c0c42c80c280c2c949074085a0040c19903400360b02008101000d10050605500034802c3c031400140e9802c061040600d060558801c4c982035402c1802c051015aa038120081003d00c503075034107512401c2c0048030407818a0210307000141804404070000c07445041c158071458501a050b50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 545998309 1250 545997059 545997061
    0xc030c0c07090c110606090402010f0915120b010203070309051e0402120103030801061106010308090609190501030627020c0a02100c0b010506072001050d0212041e03022e05010b070b 80
    0xc130301c3d03c0d11000c5a07203d402020150206006500c42d1548001d0003100e460f21030585511168030280116140059400280c0907404a0341941c807288120300d4545030900080d403401c4403d590182c078125544c45020300c101e44080044030680d10311320f8900f0b9404001401150b456014400d0100d10100030f000540c0058403c4c1c00105030385020b40c01d030441e6240c1400061103503030f2850361505180d60001d16410b410450a0201c5003407626241040c40703840407459034000619061800040441e0103d0b03011441140350300705080300c02d0051003004210449030b80c2c00940d4a03100b83e10b2031841c01800490003500700c00303d9962440141c1d070000021080da8820b10007001d550b41d035241044151300513801c000d05240c000b40d02c5044500000c000e80d49041c101810150f08210328101400f003281c010400c260b0145000e0b000300070400c041c060000a0711008610090000d10040e10002d60710500d40e060f0406010100700d0784561180c0508040e100004580018001c9685030440c848890700200c07400c440e6580480 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 545999559 1250 545998309 545998337
    0x12030f3506010e030a0f030c0206040e1501080c0708070524071716110a050607050901110a080403120c300201060311011b0812180106030b0c030c0c07090c 68
    0x1804040003c0180200901d09070b5031140881c000c41072100b1020700040086030720058a50901900040404a190303c01074075102102400e2043c4a00395281002035007410050b10b90310a10940f10640e0b08896030035100c030400d182280c03501c0480d8404030605844170320345488005a8124041c480d0016a441e070a892001443d108003115003651003001150180031107002e4240b00304800480d003425282107070340e4400380740c40300c6007805819a40700c40055000929918503582107200714401e091000018050040d80d43c03144500740c011400010801291030030003468140c8120350b00c0320416003001c45082c8080c0b409040b00f004074040002e4841041c402483c4904060040c8500c0c0101c1e074100000007641e444103001120409105207400a190081c54002c0c030125031003401400c0d44c65090440d400c05410301b9038140040140d40a440c0c01c1c1d0ba07041100620005186103000740e0840b5180c541d803030312501c610040d0061806001781c0340110303104141002543d100180c10595030f480072501c80c12280a000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 546000809 1250 545999559 545999567
    0xc0301020d0c090b03040312050408091009090c1112090d060c0323190506060f07051b03031e0310050d050606090a110f0906071407090f0612030f350601 67
    0xc442c0540440d0084441d402d4000c0c007a040143c0c02b40c49110400d1034102000000796207505400c80c0300b8005540260140302c03100840c4140096400c45050443d803c07203513080102d503160680c14401d00c8102020030b0300c51043e00c401008508003580f00c0000e210311203400f50010000d001c081030340065000343c80681d881d92003100c04c0b11409400e101d02440c0e07203940010040000341401070b06594200c5c204020104003c54108090a1101c0c0b0440c003410f81908042c00340502280498495032090f08100142c14100404110908104940c0c22449843c0d590709031010000e8142c6074442d07900403444440e103000700100030561350700c2500c0c2161350361156160001d0810480e4801c4460800c040c4040050440b0442041d028011403400202003620303103111544c031100c1f4406410421003240c2c2c0002000d02609106024500f19140d00c0f580030004189080496010440489805018000e820300310724000380c840d1240701144100c0008180005035041c1e00b801c050b143d00a0700e0700e600010080406c0c035540c41 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 546002059 1250 546000809 546000811
    0xa050d1d060901080c041a030402091b0a0c080906030c0a111612020d0212030705060609060d1b080102190207140102061906030f030c060b0409051e0c0301020d0c090b03 74
    0x81d11050500700410015075140c480036003042c0b11040b05200001c0c40f0f0b0b0000d502105800c013584041a280d003001e20500c8030b05003014043e88004c106400c18414081100380940f140380045180c840c0440c42682801c100a03c01c4100c0180c10030780c00010424100e60400080c541e1164550750f071301104010781070309601e40c06100d0b01c642800855100c100030074080e1400410410b07000070006040c107030030399000401d0406500b40e811800d40000c1006000c0c0003040c0105a4015410b803125052803a05000040e503000a1880080442041d00d141c41d5400410103170100c0600041c5008554400e400580d030050304402c0300c1100014072400314086843c8915207428038103d14181c00070071058888440c010f6201d0452444c111110340c2ea214000003103042c0b00c102d181483c3c00b90300c070307070040544504014069444604025000764103103401180090700000e900b00041d08448004002000c003a1021424446200c01c030039499800841e200c0e00310034459000c4150511182c44a8100d256204d5a403485800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 546003309 1250 546002059 546002117
    0x303020c01112509180b071d060703050c0105071d010c150c020a1a010e010b0307020a0308180a080a114918091406040e0106080a050d 59
    0x415006040b440d5950003103d2070101d00c3d0724407000591181a80307000c03590251458101c0d5050528200b00380080d031b1503110f81200c03076423401085c01192441c5100d40c221700490180c0c051a0700041400600d4800c10644035250500402804281040d0400804100352006a46586403da9400820660041010105095005c030000190090143c2244014614941071400354050f0b0b010394170010f10002180100c01490081c1e0b078456504105880340f000c44146c2044548c1c88003041800320a540010300100c15035410320b45051035564418030411010448100c0c5441031040f03407060f108001803113000c0c10104441d0f41d91800c1c04004003c1c6940c0c0c0d10300c00302c80380c0c3d00d400c06001c0c81041c00301502d00c40c0c011a40d000a0440030b080151100303224040030a0000000500003004801003100c401b40c20340000e20f00040140801900740c00c080b07012080107059288600e0740d840c1c00c0c1d43d0300c002c00c1d04154028954030041d07170790305001030070802e0b180c1c5440301c0c200700040ca0086845112115070184610030034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 546004559 1250 546003309 546003313
    0x120c0a03060c020a0819020d210c05090a03030c05010c0207033906020c030f1209041a031504150615110c1009080f06011d04060f050703060303020c0111 67
    0x1520316141c400041140980c410210300800da1040701188145004040307110000720f4820f884241e03e50700905240402052108000c568500c103850501c9002010000110030400011041c545490950303607403250451141c1c20030854403001003030540000440000c2e50044009110131807415400f20f84528281c00000c0c00c2146032a40d921800000d815045886c50110210300035042116402c81c2c070320045075101c0001a071150b111030a10f82003d010000b107100d50311008001d003e80440d450092401510f403014041c030f80c1d5088a40150540c000401c1d65110301500395280701140e1f1020741120281100c0980e040a0030351001c91000c0c66500c2944110b503148100e1000303114440104039080c098812085803648070309100c16556984a043c40c42105230a40c882d001680c1c90000c2081c20300300300001745092504480b00404c01420529001182d007001400da00031550364030310300180280201002500300514003410840015019805401942e010390201c0303210051420045070828462007400c0026 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 546005809 1250 546004559 546004579
    0x906060902091012090204020316320a020102070b010308091503040b0103020d08091816030204210804080303040312112107110307050304031208010807060507032606120c 75
    0x2445103034103103004a6130000100e040103160b0000750991300142c40c81c51115840c9041094010740080c045111a01000d80e404c101c4e226440e1403002103010300c64100415040003d184a42038800e604035000c8950080c0b04151950b100c2c00e1590150308150080385c00703070403910b003c0e26105040c4415203100d143c0c44031000a1680c2036070700f0320660000303040c3d048482d40380600401c491a5906085d1070301350007185240c41424a040d542c8080c9540650074003c0905104200030b000d01d950001e8100d05804243c0c40c0900d05618910305002c051246030701c02c640600010083c031041581c014004881001501c00500c118001c1c440142d14500c1450700f03200e003e0650000c600c01894007090695032100369410400c1e410540c14420500b5a880120f0844664000113000d000b001101100e202181d0342e83c2c0340042c0c0f01d60600c200582d444030140102800d00c070002c6400d00c201446804500440c000c0082604038422140b600307417944c0e40c0290790340c034450000d850040311424070019140c40142801000310042c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 546007059 1250 546005809 546005839
    0x7090e0f0f03030603060615031f0b28030e070311120d09052b020d0503090d06090c0e06031005041e05030c06090d1b02120d0f021209060426010f090606090209 70
    0x4820030f164ad05c04204550800000c140b045e050280040031020400201c2d1248400c415940074403801d0800320900d407802300d80d240c2d000e00000340b00003600d500c0424820800408000102d41c2801361149101600c100c0c0411507074070303038440100c00072103206442600308840c010300e840c2d15078501201c4160b0343c160442140301c0545428101429164003035002da07031801d0300d450081130782142c50384c005540b040d03110080c030307000c000c01c2c0c801800c01019441c241121b90308007007001903180e00b201640e9400342a141c1c070124040c40101c054045410f00082c405054050952510070740726000340102c1c0318240a14030002c1d0440401040340d6200038210369410340d0749520424898048040240c043e44c00c8090b000202c21084010000040440c08917112807000310a04800240f50102204020510f0740052040b9549030700da10050303400341e0300d0482c1039100d034051702122803400d03042051000c1d807a90b00300200d009540280f036000c006060300400f028007001e81c84418103010b0b840303200c5660350442603042232084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 546008309 1250 546007059 546007081
    0x60b030f04061508010605011b0f0803040309091a030610150f021203040f120c030807030e0f12030702070e060a030219120602040906061107090e0f0f0303060306061503 74
    0x1e44588a00c0e0009407480f16104118074201c056008040f59030340d241d009021541e080701d40755842006100e49241c2c5007071030383e55406804450500003411800044081000c26028440242c0500364140b010880b04a00d024405000d14031000058000c0c021880452079a99004d02d0300c9040e1509086074840c01001500c08550f0240b225003503a0442c0a10103d040881030020021800340340100e8002e50100d03240d0801c4d41c0c00c5440c00582c9001d1040c10b15940340007039003000d07482d0b0b0b006555040004009119403881030a280e1285120011406503908005109140d100610701030141507003102e2900d07440740343e0b0210700300c2e060b41d4141e4401c010f03010410052406195903280c0c0130011060a6000740e8601c22000103811490040b0340f540d40124050002d001c0510405000b40164034003a417544401c900c03400d84495490080041c43c9407a00314440c50400104030940c0200100e004039103440d20f03c20701150f140c0c0c006803112440303405080e0108800d440c0c00c148040d41251000400e80c40c50f120021010f03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 546009559 1250 546008309 546008311
    0x601030e0c01020c150c0f010c0e06130504021c14040c0f0e040624030503090103050606040302060306120c030f06040b07020c181302060a0c0203070504051315020705191401060b030f 80
    0x40c4556031708000c0c0190b80c05090285015848041c0300114882c10700d0384c1c0c041e01d60501c1d500854000c010501ca0002c0601183c0b45d001d04540e810f0700c00580d90545000e841c012030685501c0005198203100d20340c0980e802d404090380c0300e240104d054080c044d4944100100580c000d22400800b08140f1022070302044d000d5102d8902200d60502c0074400849501c01505540074591007600d9580000c00c1205c882d50f00342c050982d20040440e20103103000c0c1958005482400050f0040e4041c444100c052003200e6020802400c0d4085e0060440b024107504e50041c1d43d542a085070b0869031070100d280400ca107503000203070780c40c3c5010009009401c821502440c2400e00a0000d0400d0583c6032401c151030096202e0034010b00981c0002d60b43c940d1101502d0043c9490094140d100c98007035450b0508120400703400d401000c8502d0361184c40d00c4100f880501e46030020303000c0c1180103089802580304001c121400f1813182e0884620445084d83c501d074144100350700320b5002d880f0300784040b402000000c0600d030342c000c011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 546010809 1250 546009559 546009589
    0x105040c0c0602031302031509060a0b011b06060b03180f0705090f09071e06110604030e010e031e071503050c1213120e0111070b07111c08030601030e0c01020c 70
    0x30001517001034002910740054030146030003520401050116540043c4041c1c3e5026074408010700074200c1c0032000808868000022030050007100441c141003280030740001e00101640c00203262642002e0043e00d86500d0b0b4100100d400348a200c6403c84800310105049040715002031081446640d40c040c0503d224100826002c51405034800201e0079156490b1390b004078070404100307010706504084014003808c4035071049030040d40c4910704002c000f1350f10121030304542d80c007031a00c1c00d500019003000c41d1a000d8000070941c07560303007082144d01c401ca20008650084480041c405c0f400c83d11180004d50844174161900310080b6800c100ea07404600d14048055000001800000700c1c1d064640c865103205402c8a8009002508054115281c0c1d0b0740201c14200010220700940005407401000300d00c00d1051841c0107080e50b40d5042c04c6221a90340c90b00f0102c0d161090661002154064a4028555801125214041791900e240140841d10000c0c40228031641a001084201501d00c02c00c607107000c1d0039140f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 546012059 1250 546010809 546010831
    0x90603030705060405030d0f200a17041505070f0c0219030b101703040803040314010209030703050a2319020f101106011a120910060e07080105040c0c060203 69
    0xc00003502040f04078826800f41000e9a281c1ea826501030080d2241c0c00c4180f0421401c0c81c84001d041d03106150a41c9075800d0100c02e4690750100206c0c29900c001a640d036000e511018002000b0902c006002e44518200802c107040101d544c0303100c0180c40d18820913404c81e00085403403c4035001400c040c6210009680c000c05058000f558940e903450307a403c001c0300c00002c040c0c40040c04000c007440c01c0440e0481a00c81c0400703035080509040900340e40e03006070f200c00303489101c210a0900760150300b90304548034000c000e016900141d8890628554540c280141100c068440d001404501600e0b40300d00d82d1440b0003d0701904441c8040140d08a92540513402680c1c0548807200c1c800381039980034841624280c2c19110054807000745040c203410140141d110035580d4666998001010700444101c40f2032251540031403c0c0c03070721059101440c00d0350180810020b54500301c00816540c0103105800d2241d03420340c4c1c50340c1c00342e80c8030018001035410402c809404105000d41d800e000031180e4010f10317400004800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 546013309 1250 546012059 546012067
    0xc020d14090d0c03060b030606030102030c09041a0627060f0d0905120301080a060621290c04090c090305101e050109051f0302030d0e0619090801060f030b0609060303 73
    0x1034546948a03da07104440071035a64480e0f0300141018082180d0000e0110021800e514200c0d4603203401c0e1013207c40e014829540c0c0c0c280d10b07000600d050039440210001411981d01c0f50b085507988a482c0c221540c081000b0a861902c1035064601a41100d68140ac03031801942017a600c5402c1d2405841070f51070071581c0f4054840c01207480a2139074065802054200000d210b01c071268142401205c10903009122101c40c544038801c1e02410740c40d0309446180e44a113188042210b50140c0111060710203404070300d00921041800000010100a071041d9100354400300000200038500b40c3c1c2d038040c03911004085400c44400d24900b030f1a150f102c405002000c0030303241441400e0340b00c2c600c100ca000340c002014007682c440911040316200d5031402e542140c4008070205030360030354000a59449202a410080119600c600c0c591078071a2800e030341c0c1e464552041c1030f415041c0071101502402c00350240140d00d43ca81280060344c8640d609240d01148d40022040400d42c84070f2041c032803240790082c805e98161200f00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 546014559 1250 546013309 546013313
    0x130803090a140d12020c1005041406211905040317060907080106050d020d0213030605070507050309060901270315230408070816061b0f0e0103060f080f010c020d14090d 74
    0x50003a9840704041c1e46050b86d81e80ac00c42d2000c1c298451a10460245c00c06000029050441980101e020703501da0010682a80d031310824204da008282012050040c240020721080540008070b0480c100d141c011010584d540d50418041e1804d002c885a00c0001d24400040200d140181e0040c030310100042405880c091180b54070704c050b41d0025801d01500440214108103210b160b01c60181c20619900d4024501a81d98403055543d0050103000340c41540c002920035096809540b903031902d100c0d20502c00c4480c005a032254504e0441522040d1f40030710408000071800d64040c45001c0a4007181d61040e0300080d018a140300f0301e03200c001d03c1280c0043c0d04000c5440800d426038003130522441c01c050104969100c0d45080000c2d034034110505060074007a1400f00c4800c60b005102c15440d840c0b03c0c903103007110a400000403409070550ba0b0051038201441e49010507154004114050b082c0c5003e402840f0b0720411800032681c0b1401b00c03d0364000521940040104a981a40104059440140040c4002c4825 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 546015809 1250 546014559 546014569
    0x2040b04060b0c150604020403150b0102150a02070303050903090a030f0203030708031008010b03010c0801030f17031005010219020f0d0623090d0801050102070b0c0102130803090a140d12020c 84
    0x2491007985940800401c01d0b401d02880344c201e9200e14203807000c0d0b04251855803140c80341419690039585854480b112600147d00c2001020340d80382983c10103440710304041c0c84610007540180c1041d0002410000029803041001089540c5030034060030040985207544c681c15071100c0c075420100e034940010059400481c0c3d01c0000386005100c1c1b0308050f100d6031b00d04003015007185c200303200c414026410a4100401c043d0401c1728241125040300e560500780059180106550440c9034010305200000320901a10244122030301040d0b0b5002e8003119044512050804d00a08807503c000b940558080ca083c001428042c00c00e4070000d1041501240c0b912800808400010244607100d03c0491100704001100404008200899201e414030342500d50500c80001c2d2120030900075411001c00006840c100c00c1e800350f0441d0218041c0c292010a0692030340f00700d5803a68400c0161038821000b140d40803a940c040d50000d481c10380d0f4000d20708114140a0b0382c0b822801c640f00d100c2d260550007240c036280f140361a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 546017059 1250 546015809 546015817
    0x2702060408011b1107030b010303081305010c030c0e0109030503030c0714073507050907051e0a17150904030318050c0108090d080105060702370b07030c02040b04060b 73
    0x100e01c42d900c1c1c3c000e0800d02c0041c0320b00000141c641031680621801c2010030b4a035001203041d00c0c0c16142024503580e6515040981d250260002421986010501c1c800c0a0307241d44400d5010369147c2e0350380040c02034400112a05461404040c001c0e80003000440ca010b038168008041c0940705402480c0c0030f0081c0000281040441d0380300c40c001c880005a0b0301054841c20004600004101c07004208020b600424076580310068051a4015400940801da44e01d025005550481d40206501020080c140075030340d9094000f014060f02103101c0c0300710701d8a89120341040e24420159040e0b00054240c1c170710100604180050000e80a01d9518500a100ca03030034034a803855424050002420759000c010b000502c055401844080c407900407041c403c014582c0074802d05c0c1119011281c1d1030302c80d80c55000203400c40385521004c10b00101244102861640d844c0750960204102c551144410790707499150030684d00c20604004c0001d4040803003440140b4080d4441101400003500008505031114070342c046582c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 546018309 1250 546017059 546017081
    0xc14070804050a0b07150c050408010207060605040c14030a050601090f090912080601020a030e060d02040e01060e010c02060a11070e150a0504180807030e03060721270206040801 78
    0x703018809810103d000e41d00801403205441e103403059031340b03031040710200c28003c0e00b0310a6201e400f518400341c8240180c5000e009504021950b555280c81c01800030829441154040d9042122a032200c5010f4400c440094160021040c0f075969988850002020001c1241d81406646480441c03c9070004007400c01a00c1c0a04001468004506040c40419581c841c00410040e40104000181c3da02045c039007170305985070414ad00d203802050700140302c038003818060b10480c0d0300c081400a034000c000000c2c1812a21540c648458588640d001111005171420000e90030420400000f103049101d150210000760150058524003a15050310488401c41601c3c84894003c58841120052810441100007000102c41c100420030320507060b1603c0001130341340582144404200401414002c05400680c1d4400a060711003504c0c01440250440c0740015644601c03c414545a00c0100c040c0e2007601000300d1034101b15150501d841500816000e8050b00c2240c00540500ac001403540c0240100e030381540c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 546019559 1250 546018309 546018323
    0x51b0d08010924060e0607050313050a091118040b1005091503011d0402060c06090703060e061506180a030b0105040b0d120e0103111902060c0a120c1407 67
    0x1514110801095598140f90b46003115203110440c0040d1102c107165030216582410628044d41808000900c5801840c0c8041d16500001a0075425000030001c081e003a190304448240c00141c403513885034211110b02c0580700d0481c000f005281400320184c504407a5081d002400440c08640c0340010a001240e42b00700c60020400128070155140341101e442c54241c0c000341c0c00c26085600d0000d101090b00c1c40b0090007a1441080e2004c10150f40f03510080700c0c68114194225455800d0898079903603075030685d12040d03802e01e14224070511966004a002405496554402c944003074030b400400c070095000f00200714044801070101d03003064989000c29030040d40100e130040850b615120502003940d9645062610a00c070710580040080d074102900040d08002e89460700940d0340200c0181d0043c00c4080c0c00106c0e4a2011480383c02d071001c1140000305103d11982500c0711500c58200621650113410582c20109583c0204086501101d62101d1600380881c41c0c024080e00d4170300b8414030280d005141c1a1001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 546020809 1250 546019559 546019561
    0x1507080609180109050114150f1e090c03011802030108060f0702100c0c0203150106080c030a060e090606101404230d05071a0f09040b030c221a0a06051b0d08 69
    0x3840c1410345158811a0003100d81c1c02c1c1040140001ca40c0003941500c01d124103080c518001c0701142b408080924048007401e41103003801c00700e5038010150402d1090040554100c0b0300c5a241400600030349040701e425400900e1207448012500c0306003600181031000b14441e203100326540095600503c071150503a6240d0084118103801410305040f015070b000011041294010850686c3c0140000e0307200e8046a407151326915003c150303c01070010b03903100250350040345013440261900816194000c000c2220b0390340b0403062850f001d0700d40c41c240f02035503a0002010b1208219841d18180000c002400d249015695411100300042011803009020b550b1035100c50030500c80e50703407810003d1a911604020503420285d80050b02e40040c03052240003800307103480300310081c0551410082c0c0c0c0e0303c03400010141ca501081646000a590004040ca010401c1c20140300403039500e81059040c1d0010006441e0400e41810910161803030ba104c007024180003108800d004400d40401d02500c100c007400c0d69109445 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 546022059 1250 546020809 546020831
    0xb09010906051203070b071b080d050f0a05061c05010902030a05030304032d0c0302030d050106081605120f13080304050a15181401180f0515070806091801090501 71
    0xd00c00030080f11400350b03070040245e41c0c0440e01e8404140d03488031b402e140085030030b04c2e01c1c680c0c01c0b403a00c40c094000304442c00c04209001c00708440d802c000e218800c008d00c5001e0390740c2c034208100d05070781c03003903070215000b43c3c03440c1c0503600307107403810340d034800b440e0300174000426541819404a440c117234030818140c45a0304084140002c05520183c6034851080550228402d43c8004a40914128030100390405006e840c1c85024105402841990351500b1f5800e4100619a503460700a08000070032651054500303400080c0c00c0d081801441655449510000c1803001c1c0d40d2040121000c162004e0302082e090418071051100107582c10f03004520139031084015044042075458500c0d0388185082038480310074140304903441580c2402d4081240280c110313210112038281922050b00414440c0756940c0381d07525400491081c401d8a88139150150301c514201d0351641108054030400c444d0642ba0000043c008401103000d41c5081c1c44102c0d0440311000c000140152044802804c45000510454903a5120540012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 546023309 1250 546022059 546022069
    0x280e04060c05040e15010908030a080103050d170a1805061302210a0f0813081e2e0204050d030e01030b0f030d08090a0614090705190303120b0901090605 67
    0x1c81c0c0400b410594201420301850707140303054006001c0090000300d540c200704144e100d49280c000902d03001c030941ea40c4ea0011480180b14003000d01041d10b00703125a40220b03c00c0391107408051804090010031030590385034516451302070084c5003035090100714508001c0000c5602840014040c1c0e0041c038010716404014414403424848071107444201072007800d5130200300d1602052045025910044501042c54a0f2070316040b5800340c00c00c0600b41d601c41d240b0200d103810000644651307548841c0140f02c1902d0101107019500c00c001c29550090001c0e841c5c6182410141e000d41c49a6800300040250425448a011800c01c411380300064000410b4000a40c02c10358240c81102e44c03410099030103040b0030072081f000c0307550340100010020412071404006000c607441030100c8004564041410702990446450210350000f00792000070740c44c015100700203000c1c9000d0301c40a9200036034900450f40c213071039502c0948854000300a048800c41e121314240100d0760b5050001400391603900300008600b418801800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 546024559 1250 546023309 546023321
    0x302010507080106362c0603060621010905120c0147452a0c0624030a2a03150e010e0c120a0503040b0d0b010f0e280e0406 54
    0x98080d800580500180f915407859034007200c042c6804490384000120010740c0100b40a60001d811401a02c41b0015811542c40007410040f950400a000c0400f455110201903482c91100b1a1100c00c0d092007074112070064816a10038859150040018080c04408103916800282c071086416000b40c48642181440d00040d5204f000e00e842605414460a01200c51420000d000e805000e4000c0310880030080c0901001d00310303050551925611142d0628407150340300030035501080d44103800b240c3c06180000349403c2c80311800c0300030000d01000f10380c1e444244100c0c5c2c100c0f41c424110070340000d00c040c000c0f000358200f46c0294850356460a400c858140c3c4101191000c02038944582d041210320780b030706000004d004099240481d0b01c0700030400140191450b00440300c0004006000208001a0f60702081c4090588200e10b11001d03c0107541b084c004454411890710b101001c0713100b140340380b010350801180c85603200040100081d6450b15810700c80410400769840507020014043c1044100300207401a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 546025809 1250 546024559 546024571
    0xc0609090614010e0f0f0409081207020a0b070807030b030f28081209010b100503010501080105060a051b0c0330030606070b090a0b040302010507080106362c 69
    0x22818104842d000908400d80031800e0303442000014601c00c1d1550b54808500604e0a00420030001410f241c60300d0f805503002561503640c480202c00019007041d00200708001c01c25406000c4030850394491105490f00d11010380888100755840100200a407010040580d500301071400901d21560094018411280001e94601041c40800802c10008281000b90761103c003a1024108855455112003801050310701015a440b5640f4400c00c241d8980003401107041c1c078000c9c4c8e05c11300c180ea200d00508c82d00340304840d14500000e40c01c00c0b11007490041540d04244032500320081e19960142c29001038604641e4180f02c5050844224607100c1b084204d1582105103683d00c850142580303403450000c0d1207409446409000190140001100d50000b0303c8a117507480e600845602d2141042d04000340288030031615400810351240020403a2401021041c0280c440c94000c158201102c2c4054401001c54004900f4580550200030034500c0215264584130485c924505003940348054030880080300190039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 546027059 1250 546025809 546025829
    0x70809010614130b2715090c0d0b030a140706031503050a2402030c0301080c0427020111030c010b010909020f0a030c05160b0a0e0c1e0a030c06090906 66
    0x4540e664840002c0c40d5821900c01400180e9040e844000c113050f0100038458016035042016017000c0802041c81c401c0c014408030310982d46a005900500c044541d040d03640a1792031109215001c5640c100790070032510581e0150941d044211960380e00c1e04c0c00800c407612100796400c0b5880a010b9070303078980308002c10854085001500c20b031440e110262644494140039110100b0701e00c1460070141407480b000408104404115900e28080301a520300740c04c203014094960040500540d19450280621070340702c0f01300d0906111003007038031000d40c0944020380f50817810b01a0313444550b1040301d000c3c005003400080c04800428809aa1030006014411030b8000c030a0141c0705001d00125005200299450010542000100320014400a44042c025902d1100f000c1140700d0001d01041540d2218501a094482c0c0c1800590b18130300c2c8880c2c58002280c2c0094211003006c040f41907110b00315600701c2c0701c000302030003030505940c80b525031f90400009034001101003442100100000032641c82080e00030054210 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 546028309 1250 546027059 546027089
    0x306010f170a022b151220041107050303010e060a080d03020d0209030307141e030906090d02130504050607050301060e040f0b061303151b030c030906050708090106 72
    0x50454484540903140480c010342c042114440c0b00c00a6400300800d96440c01c100c141d0f00b0100220001038061012801504c08201c4000210b08880c041e05c0d801d1b641c2d100e49071400d0b20303540c2d14100103a40780b200364055000742c4656110082c450040c00038540d050042c009541c3da0345c18004100d5103005c020b02003038024540800708019030700b00400e00360301140041ca409030f610840c4010f050064066260700030742c503000000313201c420800c12410f03070100c5200550560364904141284d480c088441902030b944142c000b00720307454151402100402c8841c0c030040240700645001d40100d01600040d04c840c106440d916001d010500c80100203c60b0b00a90301e18010307103190704220004003404040b21005000341e0303c0789456103903e251504503140d1008081d050588030720400200d080040b103a8031003694034042001d144880d0607041d0090083c5d42c1801c0c01100080340b841d000850040c00b5405d400e604060380d980801c000030f0618003906000b00040e586510540c10302d01ca440f800c680142d8410000044181 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 546029559 1250 546028309 546028337
    0x5011a0303030703050a060f15020c0604050a03060207051501030f03110a031205090f010203190b1c1203020d110d0b0108010f0b0a170106031b030218040207051c03020306010f 77
    0x4101d0741d008460340740c0800c50746c80d80629070016220640094180f01720401000c1040501d1084100c0036001503803c8524803480c038020b00801d1311581c040c035500903100031418400314500b0740003041202c0c400d604455003a5046081e05194806c00c0e003040321058650065001419401822918081c50380c1014140d00005694007512180c550140e002c845611000001c107032000510000d051a030002d0700075035682c40e101100e04c012495503001101101d1820710341d00303424200034006005c94010700080a1b12200140c803102c101c006101c0b207080405408101c00b0310682c22030700030504010092100240c5415168035484199001484058100400c1c1d80c0100082008450324a0072a1410807940d5134a002c941021180601501c04d440215007096000150f410750540c4401e504044206074420740c0708202000f10140d11400e00d2240c03985038503050041052400e07074010018144a44201d03011102c04d89003803202c090760a03c6007c0401d80c08420001d036960803c0300900f00c442c0d980340446155000c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 546030809 1250 546029559 546029563
    0x301050108060409140a080a020712020d03110307080d020307080a090209221a010311060703020601150e0d0b0f010b0705030711040216320607121e05010305011a03 72
    0x1e01d001e12464139025150f00780700c05120850800070381303c01641c0ca20841da080100032a403080b40d64100511130702500041c1068810400a812a8024005140680c00752411140d5240c0102d18507010302042001c000000c0300c1c2402410001d140341001758992507d8a4040c001140040a0400c170074104241840140d4400002647c0321038132000f2105400380031100e219060180c030500404038061950340d060800704d4401c071141201d00c0f5001c013841180c1d400040c03114a001e01c200040150341b01d070300140985003503a03c02c0f040c0099180b42401400345a00002031900b88440e10030b4034502ca07100c05102c0503046030701c46070340582149400c4a240480c0c9070741e119a248110381c00903080a00078501c81002d592960101e0b0001c800c2c200701c501460300641000f10a40304c00103840d890340c400100d100d840700000b13004004041d480c18000b6203d00d507a01101035070b0703940030100c110200c10f5481c610000309026200c800040205c41010004040d0b0552400c2802c40300b14800c503800b801c0482880314031a60340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 546032059 1250 546030809 546030811
    0x90d02010c08090c01180b1323100807020a0602180f0102120a03111308030d0c080103030e090a151418010e070c05100504140d14160c080a030c14030301050108 70
    0x203190001c008003000c00320b0001b0340d103590403c0541038000a01500d04411103030666054036030340004102145107074406d500c6900b295036401500b1144c4d002101082500406c070995100042c0d0040c0d81d07a8001a9461100300d9010584420b5409602071849170f00741490320550081c10000e00050035103484149030706226005940160302016250840c012040071640c080c1c8202c5d280480584841030740b500d090b15105c2d0002e51070011410714101c003110115109030a200c1c100c1e90183c1f03071211b80748290b6041c8882804020004404144c0b60010082c0321481a40d40c10000c00407440d01011000b42081007000c0110f074510340800701845080180204044044030b9901710625051610340080107141c030905105840441c00407035480e040c01c00c01400b040003000f0701030500450030740d4515680003109032a400060399901c0c208950a019882c0d449070301c1c68145c1d50060040b483c030b181569403941e91a103401411402100000c0f0400006010010038003040c42c5560310140c065400c660600000807c141c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 546033309 1250 546032059 546032083
    0x10b0a03021e070b28272108060a06110f1e0c04110d051902030109020702040e0f0a021002190507030c0b120402060714030d050603100c080a0b18090d02010c0809 71
    0x11780e40e503694806c1e811800c80504000660300c0700c1040d01000d820410700c000036a1142d09410b10080e100551402d103d80c03200c9204a600800328106507050040845e11240710224402e028418881d414500724070800484481040640c006c213000b04a414200d800c03d410511150b000e58101200707603070050220010340f440c500403803074000f41d60f40c2d50a0000003480f1009030400c0c0c505200200115150201e50014486903009480600001605000a556980c0320442840ca6604801104001498480c3c41c2011107103941c412245031046408a01c840845c000340201c41076482100100108448050418014082400301600f072103034404030504021030080c0300a21402001038180308001040d07040d000708500300e00459071500191098034006020559010340300744140d5243c0071882d079a41c0205030180c1d80f10350740d4138415169104d0038005411001c1c0304030b41c04620b1030762403540c0048841000c2c2c401c0140c04000c0104c01c885039806401c41716060342103401c00c01c0d004200109482c0000341c2d0039450f4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 546034559 1250 546033309 546033311
    0x50105162c01090e0106050301051011030d0c090f06050301140301140705070219090504023307020a09110318010504020109030f051e0106030204060518010b0a03021e070b28 76
    0x30302003004a4043d00a50441c3d9030300d0020400109090764840e0181d41a240c095452241c0081c82c0c000c10ba03100e0600b40e4280346250300c10841a801900140c101590350310075802e01c000c100c2d4807140341c0080520342d5000301000400100042012061000d8001c1800005070020840c60324002c0d14100b40201c0202100240007001406078119258455070b40d560318480c00c0c821409070b0302e9500303a20151000395000e034400e500010b03100c0310070324a01000c0300035000c01c4002006a5111400c803584030340c21100d0709036071000d044080050341002034041d80c1c80e980843c0541561f24034010321104500c440c0b616080015030314210412005036040189182501d8100303c44a0203496146801d518220505d85000e0000000102c05d14002d00150009810fa900c01c48043c08980e4942c81031013420941d1200100c40401560010405041c080d0010302004a081c60003610b4480b41051404e11442c56580c0c5040429000030408240220b807183c85412491103a440c0c3c1d80b54152288140c1c55080c00d41d2140212 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 546035809 1250 546034559 546034637
    0x9090516240c020a03030c02030606150d111e070b090a02030307061806110c0f1507050715050f0a320720060106090e0907120201030603060905010516 66
    0x10501a1a072500110f500420003030383c0c26141e19004000b0542540d04a002c0d22a4001146151a02c00c2c07006002000109045092440d1903c00c1c1e0003070300503290004058901080344e08000743c5e112030084450409000d140340c1c0d5020510f04070840c00402003450045030020b48540c401640c0110072160810740154001c204040c1140b0195085101007a0050110b032420a80848120b142c03009409040d807040184c900c6005511030042d261620209040d04400c5408005a0824040ca0160810b40d00406640504681124102c0e0445074140d4516000b2a401005c10410010300d0061501840390810507000108052506480540342011408660421540000d240c0761051050100710103140a01c003040c4031390384c01c840d5201c480030f003c2c540000d405440081462401003032a24081c0783d2500003401d8103403030003401c00b4894035100c000301c0c101900d510002000c10128002c007015280144000a0f403401c00c0181080c1d030004071400340007031240002d03403243c9240c2c411500d03085642d00d04100c1c80711 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 546037059 1250 546035809 546035879
    0x30111041a360306090f06060103021227150402040b040c0c2a0315060f030f060905010b090a0b1f0e04050c07080c07080f150412021609090516 63
    0x514218010841c0c152044c1003c001c00298005450392240c401841a20500c1c0c0755000110241c0c410440d078942021948408a003849001401e001c04086e00904429070b0240320303030410360500d6010205810704440722420720085d854240300c0c401854800311020000082c0e00500500824443d98000e840e610500700880791001c240115450014510750807920001e49a25041c0450000e01e1810b660441c6454400308032074180c3c4e81c0100c25a5040854486103503165658440a01111001141d043d52030b11003004003911440310440c0500c44850003c03400c0c03428401484460124000c08441c4455481110b440c25900a070004810b01810740c2d003c5a26500c600e918601c61003100002803c0010004901600340d81c0450501d013a5070464080c0c0b81c900030642032596070780000c1142e1640d020244d2000c100080c5402c0703003109401c416401a224000d8900001c28000c2d007083d4010420140c440d0781c07200400c0700620034400310309615458031654038200244207402003c01c50841070702d41d210401072a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 546038309 1250 546037059 546037147
    0x290a020c031207060513050606060a0302090418062d1a0a06050909070903020907120b0a0e100f08100b0303131203030506010c0b0403030b010509030111041a 69
    0x4a10030041d003101c9410200c4410b40c6016445031005840107868030001c20380c1d54159102040c4a40c0d0030000908154440104110040d8010448031081c55802c2118000c1074a41e80600340018010340905020b40c51103080050940310883c880e503e000400008112009507213501c4d010b034100a075000054001c2001a019942d5080c40d50342c0383c0c1c8842d2040b000103016a0000003440038282c142d414600c20740340d0040075501300c0b415000084d4420b10500005184503c0384109001d4154000c1c408110b040c444000700c0c0403104103810041d00072240300700f08190340302c8044a844c010108041c03c0791010386810748540d1508182c3c0d650b040b1443d210210004656010029111000d42c40c811010303030156a82c0d41154403032850102200402e040000144056028045844245810200031840c0340d4403540c045000b014880c0030181072040c14000218242c409125258016019900d81503076541095801100700c4011405410043c40030400900001c440e00c1352810540d903601600c00c031009040e01415 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 546039559 1250 546038309 546038323
    0x309030c010e100b0a0803090103021809070309260d021305060d0c030612150c0201112113200105092d190311040905032101290a02 58
    0x11690b00b81400d40c03005050101c0d06002d031001c101c104120086086042c000343c58518072804d0095041808980c1495005c4c0e002400b0110440840980300409040002c0440c0c0040d50001d001a5a4000c4281003103c0ca4000082c2070038100d9461201131910350031074680384030318508500459004940541c10842c6000204c010b03001c000e040603122000207411000828085002d480000d042120004840c1d00a030328403d41da98115400c0c0d5820084040070102501d00b6000d0442103650340d031361891410001c64040c3c4600304803031004500040b81c3c9032482d40300c8c000150541d0203094101003210002113040d14140d48202c0c00101084054880d500141c0c6c25002d280e4550740c0245603906401445203070003140242500c5456101044600c4100034042c00c1c4100718440c3d500a0400d40b01400841c840c16041480c4000c0240041004031580da102411074000c0268000712012210300c8a41c176281389044c80d40980304806501d1a03651081c031400180c00700050185009107400110b80c0c200c3c910a101c03031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 546040809 1250 546039559 546039577
    0x304090b1f0807080c19030c140d150503070b1c06030206040f03120309030f05180402070c03020108011e12050c040501030506060a06180b090d24050f1b030903 70
    0xc800010220501030402d00c01202e503140001c0b64070300001e61034664241910400e805203420044035905001d015001050790076000000e0240550346988444007180080950004031400480c001d030380b0f500b11500c0c0c40b401d908400c0c0300781c00010090003d0905031003509d4043d403c4204641c120544181110001d00301c940000e900040005008964203414040302030481c0c0c880c0900704400144600110125000c82d0802000a140302d50b600541e1881000506054082100f40c02c00050000002078101c2e80301c41411034003001d44a0b020019985c100050a006040d956000c4400054500058a00341240e008588440340440400707002d003c03017040000d00058019000300a2941c41e030501544c0c0b0a01290018446c200300c05000c10342c581310b20800340504111140c501c080c1d9083c04150307001034000c080c2d40c039040000f40d048000402e46d051241450003071441c190791702c010314008070902501c1c801003003120f540301907409100c0892080503040f2503040c0581c4c1078649940307501c11001e085100b00c0501c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 546042059 1250 546040809 546040849
    0x30c070812150901080f1c0905040203190c051c110906072a0303053106050c010b0913030804020102030d150513060305031605010f020a0f1106090304090b 68
    0xc000d1402c00300d005403406588110752040d1281e0740c5403140e50f565862445101c806e50081e8410036000003911141c0c8010381c0c0030342421011507843d0808a8102c1c0c0044815864800b042c0180540701495071040070b00c00c0c1200e04e00b503447d069029018110b4500703003c41030050b040e5194a09009460440c2c00e4072480880140f82907501c2440782040d04075029058408800031291a40c080c0200039404802c2c02102d92680341c09080089040b030a10414400c6a02403448814440e841d695640104448002418654551a8a070302203040704500312082c141501d800b8022410602500c00020700d10210303950b42c5131070700907150360b1303140700403800c60081011002c0c002d410310301d0115009815095080c240e803016102524003445a048800940d03072217201c042e106d50810000c2c2c50140300381400005109001d000042113004280042c0c130200d034000101c0c0c2000502024100c0c4840c0d0b449246903405410f43c500030540f03030a1003c042e581f00d00c6180b140c08100355a0364040040b940f646900040f0408103a41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 546043165 1106 546042059 546042061
    0x5160804090f0f021608071e03020f060c16020d0f0c080703021e1804050c1f0216030b1504110a0c021c050a0308060112150911030606030c070812 64
    0x7c03003a00c2c080703100100c1710300c01003140c00c418186601c29401007090a641500749030818001a0401c96907500400c1010420b4154104440100303404031002c510780b102500d04034030400d62194000b0414940c1c2c03400000c190b80085040d004490003640c08d44d03405409804003104070142d080001d50f005600d41c4124031840503e16200e548984500110780c50b641e070321000201800300c4110840c190240c00490310030380503410303c1060940d40e130324142c0418441c2155200c81242100a082c08001164114400c00c0c55841d5082071805007408040165100500440141040e9241000341e016045005490306810700c1222803400898005d4054016003e8a9074200d0f030054010385810b04010401001e905075880d148140d0861040b80a00ca1507036614104513031056030381884080b030105c141401048001e488040480e5840241007440c01c3e55440945429500380c06031001400003805080 = true := by decide +kernel

theorem cover : BRFrame.Cov 545863309 546043165 := by
  have h0 := BRFrame.cov_init 545863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 545863309 ≤ n) (h2 : n < 546043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
