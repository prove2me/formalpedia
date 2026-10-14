-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2169
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:51:38.016532+00:00
-- url     : https://prove2.me/submissions/46cd856f-38a5-4c54-8ec4-cff2c90904b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 389928057 ≤ n < 390107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 389928682 625 389928057 389928059
    0x3020a080607030e010902010c081605161a0c07051c02030111220509061315 35
    0xc200998803020811540651601030641c1c519130540080044090a80000b881e69044100c0601038520000303032001454028441240d0b0709800030140c81175035030105003821030070301e091040b41009000351049400b9480040100c070f4040300d20400401c0014078041c24004070740c40c070000c808900580d901c1c0303510160714207000b41d5080040e52151581c0e5440e03800662a01503400c0d660440c3c100c8640c80003441184c4030030b54015080442110840860800400180080c0c102415103046000010f14 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 389929307 625 389928682 389928689
    0x120207051008060a061407060b042003100b030606030a2004030b040308011a0913020403020a 42
    0x2d001d241003581e51074012558104003140c00340c06240744841c500f15400d025842c0019a8179800010311004007442d0340140c9071048001688c640fa5107035808020450038650b6681000d50500540781f00961018036040341c10f00400c0039036640c00c1c0590368041d00340c5001185044413900805111001034407125402500441c0100511002c56903031481030b446500c8900d41641c84840c00070308458609044000040c04000000242c1051400d5003403494a450015003007030b469a0000340d010324240c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 389929932 625 389929307 389929339
    0x3110d05010c1e080708010501120204051c0b07080c0a08071b030905130b060712020705 40
    0x3a040c601c00f41c0795030f9586919944203030220410400100748181c00c1c0d400420036045440074a4446500e00040000000a00c125401340b039002c44907031607002d4900e40b041e400303082c418040d40ca80d50069964080503501c468045030302c140701b220100811100580141a41a080903440c501105010804101c03110006080101580803030130b4a54100018901411a03840e000034100707050142e4018a408510301d40203d22005140c0046405042c24240c0300300044001054004c0280780706a1600c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 389930557 625 389929932 389929937
    0x80322060903020f012a02070512030a02060c0403020109030b06062b0b0406080703110d05010c 43
    0x8801c05010703100742c2c281c80c164202038500b0341c241c4400080d071801d00300c200c130740440e24083c403031710341d0103804c0707198015a82c84503900e20008205d4001805010495000011050070171541400010fa0180c0350003884e0b41880d04640000344450000e000c024615141407010900540d00d034400d40d000c0482c940395944141c440d03d0190a02c4c003505900600181782030a0308800c10f807409001f0002500c1548004081c81491a1140c4c224030300e107200e8560700001e0080882c00421000c2c09049a5051580c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 389931182 625 389930557 389930561
    0x151c0f091103070b04050102030906180a030309031e020d1e02060a030c1d06040308032206 41
    0x1ca04805514060001c000202a003502035450580703007000107920390146e0030040f0322441d004a030b00030f59144044072254115000800c1c003c2011785030f1401a040b018507010680d40041c045184040c2c00c58103079508203640341c00400c8131101600c981c1e070b185000c504150f14446071282550f440c2c40140c441c0006040980354030784005c13039451503043c4020410360124003000c08202c0300e031480500e80d856410846c4c0550342c000032415506c0d6120b45c181201003080000410010718076500c81020700204ea = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 389931807 625 389931182 389931203
    0xa02070e0604020f0313142e0c0815040618050114151c0f09 28
    0x120644001151140004001d89000d1090b55810a10740d42c0701c0b803950340c8015030344d0300d002c1c40c0100807541c4090a000c0d000910b20100280070440c40c1002400858449030141c000c80c1c138081800ca0f480c080d050051000350742d070303021100940001c8040b00b00c00d1003401e201e00042c0078110f150001d031194002003200031240030094002c24120340b03000d801c3d00808460b00090140e40d08403d440300f890107200704071550102e40318000b40c801d005280d400009400c0c4080c003000090b200300c6402030306c001400703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 389932432 625 389931807 389931809
    0x210106241b060e030f04140a05012d020f0f06070314250509060a0207 32
    0x451440c0c0c0308240c0c608004000c01e100103807081c1d0754492081c900154120100103448500c09840c02d103103200f000c0c01c22880440c00300d0000340b0240e0340f140901050106036480200c03550381d20300650720007011264104031039540d90f551100c0300403a04114a00191031f1300c11100d5610380f00900c01d00300600c070240d81505404c0030381000101c6826014408000040c2090411340d45001c00c1c2498420400e43e000074a0309880002a104052041c410f6032968040181607958402c3c500601960b560f45da = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 389933057 625 389932432 389932469
    0x1502180109090c0e01080411030a060c0f0e0901260105070305250e210106 34
    0x1d803903450405403035140c4401250040c0c52034030040303034100d001510503602a140407648640301e4601a0a55040c541c080384c20480303080070807074120341c40e1340c1501415500302064540d403c400303241c100703480c3c08034a0004080703090611a00c40c11b0300d03880c1030140c0740050319910701031614112002880a801c140308024010101204d994a01c000381c8484d21044ca0084554504200526034505640749008000c200c9000460300c1c03035140c903407803403941e081c0f00e210280039030303001800d66a20b100c0341e4600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 389933682 625 389933057 389933059
    0x513060509011517060d080f120907080705041e020c07030506012c04150218 35
    0xc03103580d01400b200c4060090700f030b256800091695448400781d000051401c0045000d0fa2140301046500541c0507034081d032200d0311980f481c003940d00400a00341c2400a604e011801100c00401c3c1001a04c613154060085641402c060002400603420004841d10910b881041500c0e1244043c2c46112216805084160b00e10b0400900d40b902c185c004400c9802c4c0030a80b03141a10207480c3c0550b1100d00408226181e41c0d66040a0528400074510b01100798000200c5901804caa40e003d031701e1200c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 389934307 625 389933682 389933689
    0x3040c060905090103030503010902090a0305010e0d0e03011806022a0706020d0906020a0609080405130605 48
    0x30840c1c01141d20b091074040380d0304030703641910341c1c60940c2d0030b11111230003a41200312480e4004076004800400311300c090040401005846029091003644640f0080500b0071410505003e68140b60001d1003030751a061481d134803260481d00041c1c07aa9000308480c9501c400c541603a80405000b124203565107440490984211111902201e015800c1307a0f9080c0c0d178a072805e20401700560040310b99000800c107242c010240361407081100d186040e403207000003041e14071519480c140b855541d06080c001030a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 389934932 625 389934307 389934317
    0xf0607020708210d0c0e0904060c18081e19080d1112040b07031103040c06 34
    0x4034115181c1c101011000b91580d055820415180191010480800d02e22105002610351b000303111407441c1c00050880400060081d04d400c144204409503844c91000222522081c41a4800e8025440075030055444a40301e60b001444850303008149034251403240d0184000c240020106141c119072000e0302094045040600744281460140301280c03140c500200d594400250f400001e1000701000041800b040c40a0b00c240d01238440a0150502c60b56070b41030608055003a9035840c403d220010f5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 389935557 625 389934932 389934943
    0xa32010e10020f070501020f041409040b0403080604060b0f0703171005270106030e0616021e0f0607020708 48
    0x2c07902c400c112f144a030540300540004200400705002c60703c519005684400c010300301091007591034608040c2035001329083c42d0441c0d00480d14008040d40220585a0188825030100e01800c180200c0304000109100b50342c4110130140c2d0701c0020990210501c0382445004540009540e034481d0040c000c0e159410100c40c4501900f000030b010a04842e221a5686070954024007284084400461040d101a03041225502c21a08090b12400307082080320706c9041ea59014011003031a080502d450300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 389936182 625 389935557 389935589
    0x30a1b1212030f0207031b151811040b011b050a32010e10020f070501020f04 35
    0x1000d1000952800c401da0706d014101c0403900c0324a2840c034248858600a000481d480150846c2610609000a1000d8941c031101c8942c05081640e046113041ca0300c01261419106841e1840010785034031645605a10304002400c442160554042c0a00b404050000300600542210301c02c80d00702001c4075a4040c13000620001040c1c080110507032402c000220303842000a107500460740400000740e5290701c484119100d03400b91a000524540c00801c4c0035500745c4900003d4800d40f202900d280002e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 389936807 625 389936182 389936201
    0x110f13091e06051806060c01020c070308090108090706050a0e0a0506070303140a0b030a1b121203 44
    0x70070001340314803c3c0400a40440b51940700c600c10005103500154902140d99001e0011b0384460344180180300c0114400e0486035a150f0000c40003403c4100e0080000c100d640103060200041c82d0030000301d542100051400d44841d0900100152908515410054004a02003114400c05805034800c400060b030354031071110141e079025007107019503002032009a0150000e00b01c5d40000b40592103811001c443d0000308100e460b03100d81920f40b0340b000e40342064940d100180e004001045d014411121340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 389937432 625 389936807 389936809
    0x310804031e050114060a0b2a010b090a0207020a03080a2c0112110f13091e0605 36
    0x360b1346101340240c41e611040d40c001503030329205040b070391010040015900a03540c40036095100740c906490408401065200101c000c0e015070b1070041c00ea4449150702c04921504030700035400b030210042440400c0b036100141c420070140b81400104000080100d01c008511300b003690f15030b03082c1d5100c0c95010b5644103595610025171180284024194110b030180c890154442001a415010400c1542c10300303012002c0004000c2c001d01002007071103241e00c144462124010044040741130038400182 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 389938057 625 389937432 389937461
    0x50a171e090c011d01020709090204020702040219030605040504120c050f0d050909310804031e0501 45
    0x1300300b0056031240940d2014404000103c2560007001445000070300c018141000313500860180e03071001c0c4d2448a20303400d404416007040d805214000c041c03c4151002c101500c0c2580e2040c2401145087c0c0368107000d4140714281c1003250420050702e0300089002658150394142c000907146d038004643c0e0302e200700c48520000e4200301c804c8c4e0b000c075210a51190440300031800c08268030700e101a1410103845c1c50703a0030480130011440f81599091816451203030100300081c03605040342116052101c1508 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 389938682 625 389938057 389938097
    0xb0102030a08040f0201090b04060315240804030e100c020f01050a171e090c01 36
    0x60000500025148070710050000c1c0440700c01e65520300c1107a107d0801030b405031142030a11904c458031003d00500401c143c400c0800c0020a4510203e00d0f409484805127408080384140c1c48036600394442240c410101500880c00e11042c03041100203903455046103544a0201c0d07071841c1d111001c0d401003214020ba4100b50a043c4401003040c0d90415500241e0052690f0b01c42c00c3c943c4440e212040c0502c8440c2951300c804e00c0081c003002c240400c0002c0882c03400f03d112802d0360307148020001000c0d0084 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 389939307 625 389938682 389938687
    0x308031e0c0301050d0c080d05190206063a050601140108040510051012050a060b010203 40
    0x8645003a40d1441d10b5a030910003004100e52a44030144d44035114040b0105400f0010810345000c0119901c4071625440f0041d25038000740482c500030000c5400250030300c0712545807551140d04100900b01e46075040140702c1c0203030399040d02900c5914004c41c0d140c403019040c09400719801c2e06a03429001c4400b05440fa043c0155410141a1002419a400600350000c212560307808246c005440c51501070051380e07107480b01360007419000c60541e4203410210f42d8104001c0940f08041441d0f00c01c1c00510b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 389939932 625 389939307 389939311
    0x1020a030b0405150d170426011512150509030702120708060c0705160308031e 36
    0x2541c40014000b00071310242c4208a50b1146800c02090000c00003c008000b2100050080350b03055a00180703031007024902e4041072900d042e0a00b142c0c26141c0b01102194208c06006003080444000c01c3d03400c078900c0c0210040541c40c44014100019500e003110035040270b9000250b1001141000c9050800c07891000004d0003000d800e01448070303218640a0300e100400c12001c26010140002489020820703000c16000300e114999900c5c0c00480d0341c0080f15400800060441060803039482d59400038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 389940557 625 389939932 389939941
    0x801030804030b040c09020d0e0709060b04091505211b0d11031204060201020a030b0405 40
    0x880d0060501c000c00020700301040d02c0b5070151213a50204041965014610b007641c03c4204c40a01150311201020030b198010410030000b05000103051180034601403e040881c45103014010145446042402d144286241e02d03000500001d0101c011108008800b000750110341109070649004115201040c504515100750005400402c47d022020090352000c0b000007144140c0d40d0540103800044c0d0022076408040c100400b001d8002581d2140011401401c545400400d244220318000600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 389941182 625 389940557 389940563
    0x709060509011703040b0f0909040b18031303023a02031e0628090809090601080103 38
    0x2501c0b4001d521541c45d1b00000440c1780d50006203520199180050094a481028a89414480810082600c5002c07004403119605a901031001c4216100314614110395107000c3c5c550313400e00c000d9150f280c410782080020010980751411081d10079041d1487c4d90240301401c0000ca00416090024240d514102003080702d0003003007500d0001c1880c1d40e01007074030400201c0501840c21400210710385d4030000503a081c94021110100008039000c7c248480080c0d906010703d50b581001501d04030028000030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 389941807 625 389941182 389941229
    0x161103150402030c04091a04030807030c020601030f060b1915030e060403080403031a03070906050901 46
    0x713220040d06051000520590605413550704e8017a2845040c0c142468401e40603038085d5444620034a048c01000d0141c07110ba5155108641c1324800410100c1c004480000880d07620040c0421a0301c2e080d4002031801c812081210303544000300b50005034561042c00c100e00300345c07016101441104001c0c11a580c580d10111030213004180c5090004000034401e510410682d002620304000c003025034800b081c40c0c40401c0d0029004980d443e1000e03c40b5143c0000d0070342c01015100541142c41c003501994 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 389942432 625 389941807 389941813
    0xf14031005010804020a0915030c090b0303041a190908011a0a09020a0516110315040203 40
    0x381110740078201540103480b54000b142482105400032085c1a0800c00d00d10f111a40c450791301c1d0122400340c20100c030059150003514041e03490410382c1131340c15441840f092110060503030171102c41c5004c03031100d03d1400c8410840740b00b11031001d00d0454085079840e0403c02c101142802448804400a0742000380e030b20004c2e0010704044450b00400000300d03808140d200c140d0740a042100d2585030784404031003030980c50b03103401d45150700c1000049020340035400c2c036010718880b007820290050345d0003005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 389943057 625 389942432 389942461
    0x3060f01030f060f1d0a11060712050d1d030a0f1b0f0f050d0f1403 31
    0x3540031914070b4110312401400108005002010103a4000c02c3c03a0f40305d8080c207100d4214503007031307020b0001e4440c5412078010100e0f00d991074010300c0d50310001c15480384010f003400d0000100d03a40301c610040c0e90064083d0000d181e00300c200081d41c803e20940760303404802e501020501d144000100306102c5e00203c1d440c94550350500c1042c1e00191a51101102d2402003100c081042c41a1100001c3d400c1c844500842d0a42e180c4030f4035600c6404000e010180d01c3e07028040d00b03d005204101440c07600305038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 389943682 625 389943057 389943083
    0x1c0b120109020901171515030f0703050c0f06090402120403020106050a0b040b0309030f0f070203060f0103 48
    0x8407013004640c00d0314124404004e2010344601d810a462003034041c1400f0614401f01310344000180e00c42c3c8242d001c00403840d00d020580c00d044a4100f4054000b041900003440075034000406150ba0101003040100f4141d6102c0c030103407000c2c801488264009182c039240207821074a1f26040f092041041034004c001500034441100c0c140d400600032251240c50384841245107014405e080540301c0c070003107101c4500c00d1020002e00030040c021400c842242c0c0702e40d00f40b0548400280005040184401c1c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 389944307 625 389943682 389943689
    0xc0f0906050a181205030c100c0203030105010e1206010b0904060902130e0c1c0b120109020901 43
    0xc1102c01c15614841c0703c0415070007100000b10002c5003030780f1010007440b5201840d107840f10305100030308040d51644140c07005d60800703400d002d003d40e000c41141d0650b0b409003403050400ca040c50108412001074182980329100380720010440c0c0074200042c0c00e0b0703120200c805100751501c801d030020603401103080007a070240c0044824058401c121054680c8030000380350040c107020002d08100a0303001d5900161006039690740070544107062000384402c40300d9046009204201c05c590200b4200e000510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 389944932 625 389944307 389944327
    0x50c0301050607030e06040306111e18040914010507030b030c090f040b040f0b0103060c0f090605 44
    0x41003405d1a4201001c20b8050086500203020549030901031549521000000e00300c01c48159004010380104080d4400c41d030041005442031810512a0682c83d03050940c8019180c6005440c41d244030b030006146039003503d200303d0b804030000762101103143d9141020003102503420001c4860310b202c0e02d049111810540c0000300041c0c25a00e0341008103043c881d4007525a00314a410405081c00c66849003000000380204448650002761110100f0341054810f60908013582c14966509240040100f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 389945557 625 389944932 389944937
    0x5071401081b09030a0c0503061003081c0f06030506061807080f06040b0909010f050c030105060703 45
    0x81e0400c502c51105041c00e181c000c0c04000241403000302e050440d20400209014451424104180c9a00c81000380a60300c1842c00c545a28002d4090f1000000f5a04035501c41500c4001080e00010071200e43d000702485110384911f801d03900da5000b1100e0500903038000c03248403000c0541310704250290142c3d448020194451002014010100070100c513041a02d0700500450394980083c042c1c0b04198280000070008201c00c00d0708241c03075001e4031a0044800c03c1c03006000700e6885200300d81205a260 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 389946182 625 389945557 389945581
    0x2070b070b1f15020d0806010e09010519050409050106080d1b120302091801030507140108 41
    0x50350003541250b805410018141c0900c200024418160010303541d1807a1440000101e02d00c0e0300050000d6100348044040030f440a85070b18456468441031004050810412404101301c040011605440394490004494091800801c216180104d0541040a814150010085003880130000b04060100440150754841c01d05041100005030450080c0201d9002c6544601c0b0100c00140c6290200f1b12241a6801041a01e15541d561201410200c049601717107804210b840e000566250442 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 389946807 625 389946182 389946211
    0x10f0923120304080d05070908030a03090f05032a030c1209030109060e070602070b070b 40
    0x600ea00031644500080e40c4040c00315040510f01c01d81c8202281a541c283c030505080c10b40d50064845000d004800c04103000c80000803040c1d482e02c4242e0f180000d0340301520305241001321000d0b00080c01900000130400207509051650303000c14036000309407000303405c07911a89554a2142066442268011b80308000703408000600130300403038200030000318020076039840314401c465a2100b0240c559100700400c002d0b05406020707960041c400702181340c2c14049075031903d903902d4130010900c045028a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 389947432 625 389946807 389946863
    0xa0c1704151b030e01050a050126010605100203030a050606091f2f010f09 34
    0x1003085409000c41c05016580b09444810500100c0e40541001c40202c040800a108995034400c00744211802445081e82071003e11000742d002c40981c8410321103405081c8008159903407a0808601c6403280c0004150060740000308218040c0c0080c411590070103001c03140350b460045000000f410085000c2140151007003007074500e9413090700885610020408082d05958126945401c0840c0c02002d10250562035003003650412010b40984905480340c0e902224031040c46156070080201c0c5040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 389948057 625 389947432 389947463
    0x503160309080d050a060614040b041a040807060509010909050408090d0204020c0f060a0c1704 43
    0x20312140e41400180f016050584000312506020243e40b82c10401a10380e000c0440348100d0b90204400d85404d080c44820f0919102c3c500602120b0944a20040000b144441c00c030703001400c4203402d80343c940392985002480ca07031050301a1800941440400700c0e02601c90310603e40901d9100e02600c0c03808030000300780140c403104000160303840760f400d01400303100583c00d004441c084d00e40310001d0600d61800300c90140460341101090010011001148810920002180354000d50002e1914a00c07188 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 389948682 625 389948057 389948063
    0x9050702010e010e010b0a0801060b030a0917160c0e0f011a0d0612030f0503160309 38
    0x1d50040568030b1814000b44542d06006030598000c00f81d10072800d003d180c0d11200401c0910050040000321008641d28500c0e50795240b0030310000303201162040b01c14107076850150307140c10982005000f5186c07a17107503207800d0036420345040c0c1d10380082540110164a95501004444081c40130a02e04441048010250003c0f0300d00200c1c0705442001503045405103403079000f00f2213560541c01411030138403e854216134201450f4064a25010841d05078a51101c07410611700751520030b801c01401284 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 389949307 625 389948682 389948687
    0x60f0b03071805060a170901020306181b04060e0414040804120206120412020714030601090507 43
    0x7802c0d002c9810340328040280854407803030b1100c40c60b5840080d2254078a003001098000130380d2051052207410354030b8440e61074458010114802d00380d100e02e012125440804401d00034800800200025040d42140d4010f80c151400c540800080542220b60031203140c081300d00070f02810b07082000307000d00e5030046003404d100f50000e451b00f4140038110709000c041c0c080a613025940004032801000710180d04000c810003074424000705105001245010990342c00707041c0a80000340d9101d80000e02c1a52 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 389949932 625 389949307 389949347
    0x1406061803011b021b01210b010302090d08030402151903050910060f0603060f0b0307 39
    0x52101843d24041100510f002400e1303000c200c401180700304019480d07400f0400d0004581d44840b0244960303001040c00c110b42e8880d0072640c41409041410b040250400210f02c0c005959010455000c1c0c80301040001000304528000d103035041d85402a4480030705029160110755060340b40c0b440b05000317141d5200c01181c0c0c0e555041040905080c10b4943c2400941e40b1170040180c0710803d0305c6103c010030b08020000c102c1c02c001e2002d90050712140c070051400c6940b881412510395900130201c1d00d40e09 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 389950557 625 389949932 389949941
    0x9060f0c070609080912070b0a050304030c0209041a0c0a02100f090c030b0109140606180301 42
    0x703565640703206840020300140c404c2c101c0400c1d5140c89282c0301c1a40180c980c0300c0401041410324040c1350350b0366802121b0844060110110002c0c043c1401801c0880e10280c2c01400f84402e4a06441d281c42d48201e0b422201103410040f10000701d1442c0c0040403108040041c3c0c000b411000c0d144001c000191015841e0011500d48825120780003416505584014611501e182086581850750040484d0184c0684004c1000c81d0300a0041d2070302c804003282e60300314441070320000000d4600d01082c00340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 389951182 625 389950557 389950567
    0x911040603110d0212030307020f16080a03030c033e030c03060d050f01020c1c050309060f0c 42
    0x44185c0036a9900c1c20491800380d034175100d0602d921701d41e00940b03112040c120f42030f00241d821580c82002034803400c02166003c4005004c0d42c11280149540c80780c10b801c1a000089088a82c1c41030f07a02207440c800f80501c100166401401c90385890700da41042000300000385a0f003529082a4107481c004000302c12032614a04000024081004661021400c429154000078003001c81080c1c0751064020010748087c119030520040342c4010090744500c002c03422064403156419800890303424003074100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 389951807 625 389951182 389951209
    0xe04150506130e0108030d0e070302060a0e0a15050d0e01140c0d0f0f0911040603110d02 40
    0xc5072800203c0e0007001c02101440d100d040d80c2d0800400d40d9180b48000149402100092005949960603509800d040b880d08807500c03d048004900d40508039040311032941c408141704109154080000d1043c001c0741c40042c029044209007860a0742d41074480081003252407030010380e4410940b00984440b800c400b20104100b145158400215001910b42002080d00c6801007014040401a600c6101c03001ba11b040102c0703451511607c49407240006218403c80441040a043d5643c84001c646503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 389952432 625 389951807 389951819
    0x120323040b0c0102032706040f0503191106010f0f03060f0b18070e0415050613 36
    0x64100191030b50b882001980214840d01e042c070031400800d8044603000840e82128031102c500f0740d00a5001c1404161102140040c02d0720413021a40707050a00300072603000540b0140c3c1840400c0450109000310017040c0451800b400083c10a04205031070505c91081d507200d6840090040765030f940f0b0b000c2001e442904104840c11010703110b0701401403407803901ca0000300101d80c514001004180101c6c00c0307203418003d692001080e040c6010109080104200342c62b800072480d0b151441c4805400111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 389953057 625 389952432 389952449
    0xf0207050606010c1a04051c050306010903080c01091a060312070503090f0a0815040303050112032304 46
    0x1703d40152030903076040d40220217800c4000702c0070402c109414028109181035190180000b0540d20441c040144551000309a460100809400003c0f4450b405811040b024021180341071030404103c1d200c3d0f10034440d503a10700303851001c58412554410342003005946084592011302c8a00489000703d0764202030200d00000c0c11100a201482e021048036030011813074103050500609444d0180c0091100d4501c50b04407100085d0414403c082000c504c0c3d2030b05040d9500ca000c0750b490b5005a500c275415 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 389953682 625 389953057 389953103
    0x60f010f0f020703020a0b030402010e4c020d170108060a0c030f09080307030f0207050606010c 43
    0x469128080c40090313800880303042f40010142002c000c6141442d044100c1d845809018a510500c00780e0241442c1080906401c182c90050440c1c04030003200c2c0190342c0da12050a42c01801d600c259080005044000a190300301e040d80380d00d00104420100080c40552042c0c02200c006541440000104d0291034900340600025041010017800d000143e0700941c00b40103c1c0c2c03420003251158030800d006034025624007a0690f002070b0001042540181c000004a40c8503005a882d100303501d91107690 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 389954307 625 389953682 389953699
    0x3041e030b0403030c0305010e06011b06060801021c0e0105060109090207051015050306060f010f0f02070302 49
    0x114500ca59000b1a0300c100085d00501500d1040e0000c100b80e02c41f2004100b1242d0307200326500a40103d900318841840c1240c10010000c0c01e603038000c14000d50000412249450031b2180e8003844414580040281142031442c180c201c86050740c15a00252000d00f04003e1248587c0140c00304d40d004206513540d0040350076003c4112040c800c000d100001401a0030030541c5418040c03190300070b6059403203040c01440c240c0020070340c80540041c6020b00000c041981e510b00c1c0700b005508065035010304002c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 389954932 625 389954307 389954311
    0x7030f0f09080d0e030606040c08011404022101031a04050a02010e060c01022d09010203041e030b 44
    0x401d60b00308400140c070312002c5e01203d00700d81c1c4a00c2084180c4520711110b40110f80d203040140311401004004440b5203001401c09031524141da8044170101040111900c1d000191200600802140e042003a565030303d10f020592440c1080d8030b580c0e48815500d50024103000180408221540355034081e1b8091500f49402152107000f1000311043c100000e075500c11000305444c440100b0540003501781c0f44921810790055040c2410599000441c041c0380d0344e5054050400180000069100c5031418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 389955557 625 389954932 389954953
    0x4020f121b18040512070c030b040c03141c23120603010c020307030f0f0908 35
    0x141e070340c484122040150030034200305a0108882c05607452a440c06880e401c2c0c0e0b507104400c1c0110020f03000540d0900744541080d100d03001d19444121130400e03040c1802c0c025410340c000e01040d80ca03810400c0180304003810014222141c501000c901450390000c1c5a81501c900c01c542c1e140d81c4030100c1c4061460410384000005010345014070440744080d003005400d050031604652081b80c15940200b0151000c290800744803102c00890b4030b0090082071009030112141c2c0716560010010784241034000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 389956182 625 389955557 389955583
    0xa050d0b19050316060221090306010902040603050f01050102060c07030c020306070905120c0904020f12 47
    0x441401c03079016040c082d10034503d04d0744040240f0055081120916409840348940c8050608045852070300f14030300c500c0d0300344488500c0e40e4080c00342500030310400000684c1c4c0c034a410009000d4500041558040d495a0001040f2603600032a4442d40300c6505240f1b540d031071070146800e0701c80d010a40c0000e90107104000c208518507030080c54620585400f150740c0444072a0012046648245d8442183e401000c500c001c0340042c108030000c8a4003800040a004e1240041c502c001c1c0790103800034000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 389956807 625 389956182 389956219
    0xa020909011d011e2003070e04050406020d1103060618040204030519110409080a050d0b 40
    0x3607074410410032603a10f0600e000f00c4040082c10040001c0d1210304540900c03070301740b403041261a40c4e900d03854000d81e40f104045418a8005081c0000c02c0305100299000d80040b050000b400e00000c0c081080900a034030040381d03070640c401340c24003119400c01004400a01c4902e005040103142c00c3c1c50b522004e1030f02102228428000d071a810140080040301e031110a14a0006d0703400b4001682940e49070401c0380134814005040203404241c01108a150303802c85214200050440f008804035004c80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 389957432 625 389956807 389956811
    0x103090210050a0c050a05070303020f030a1d0103270201091d01030206090406050306131509050a020909011d01 50
    0x107508881c043e2f07003101d0300c40c0c0714210a0350301da00c601e50169001c10310900c4c4611351008607500308124030105040000703030070b420344008002c40d80905641e512682030105a0004540e040203001001e00103c040030303850b51024020040000806001c043c0c42513101060003042c1d99580c4c0c01c00d0000c5c003405402da5002c4d0800d448209404000158110340307d80400002c0030300c0c1c401e180324110407a03802c02c0040480f216a6000c1c0203001802030b00d458415500c038982c1104003000600c40c0700d0301004034000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 389958057 625 389957432 389957443
    0x303090803250503010b0f250503090411070f02040902060d15140103090210050a0c050a05 41
    0x26500c0710a00c0b6942090503611030628034159031601c031000130240140105401da958000030020a14503040c80c0c00c003007044803c140d101c0300000c41d05003503613250085c41806005501e0300d15003442010000d4290f41c10168819415140014980c0c03e00003e400440d0080760062810f1000c24082c1c0218056112529804080500c403035140900040e030504c041c206243c1494a082512805600d44050001c0d8440f0070741001680c40c402034000f1103200b110054003074640c0c0150403030740c402c00102044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 389958682 625 389958057 389958091
    0x90d0318022d150406260702030703020f0f06070f0903050d1205070306030312090303090803 42
    0x1030381d4071944030070140d80320308011402020b030030a0b0b0002545001c1c10410151b4254150304207400f403200e03402c07658000c1049410040d5001c2c1c20150003d41e16100e00e40f4000b854038010000501c115000211489490080040d0640d0000190300b440805445242c404840882c4a5030016005100324009030180c180c01c00d03000c1d00300c10a041c109200682e158141982540d080f440b00400240d03008203d241d002032035030302450f00d6503c2860003141c030a00640700d9200c107420039a5817551145614403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 389959307 625 389958682 389958739
    0x408070201090515030412050d02040801050603010f23191404150203090d031802 37
    0x10302c0308880d50041c1e0721910028040780005003004003529800f90388012181d0003142154002e441e03500034200016141707400058003203900300701904a036010ba0000d500900c03198800300f40c01e2080d80d01c1003194240202403160042d607450382c01d4205e81d41008200a02c001d902d20441101000e1b1060040c405800e142000103010404c0032030000c04a03540035a5004500314204200c10f1071f22410040c02e60002c00d502c2c2d011a00740c09809c03000041e522540208880c25035503206601c0c906680c030306403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 389959932 625 389959307 389959309
    0x30a050607030b10031506050d0b090c0306090603071a1810030e0106081b0609061204080702 42
    0x140700011003003010f030503070440c0c4510340d40d081b80c100000410411144124001c20750950034040c0482d803280c0340c001040074282d003540c80c1c19400d9000300c10030240341405140e295203c0742c11001000658940944441483c20306221036451041c00a02034000040c03145507000a290b0250025030300918503078008008002d50b0201d240e881d4200b150000d81740c0c8001401d220040700c40804a0001a070060800c21543c1c012180187c210030700344921050351480c0a03001e80300381d00516040c0c0c0e4a038450300c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 389960557 625 389959932 389959939
    0xb030403110c0906100203190216060905091b0702030a060f0b010203160b06030a050607030b 42
    0x440507006410400081600180070030125032440c10142080340036105d8140c803030307082d180240b09480d980c01d02c01502c168540d1350744100958840c4074a089414811402c4000b2510070b205665000c00c0c0c48003c0c04240960300e5000b010030403030b807000601480c81403050080a0041c2d80a0140100c1c007401420041140d004000121040b15800c1124505560081040400440304444032004183e00100046441d40c0c2d4080802d0401c0c0b49220010864022602005810364065100f000109020f0703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 389961182 625 389960557 389960567
    0x908031308090d230606030d1b06111b031204060b0a030b13030801140616030504030c0b030403 43
    0x6139015694000604103010f100b0041c0175041c0580305030303400c940301c04160510300070074030708407040b240424078620544000b040e0300c102c25583c0b803003440c550180c0070441040008150340204600f0302d01403814089540c00c19880b10001c60841c14030400581041d00c550000b4101690380f0080c08100d40701c018180341c40e2403107515044016030b070b100c4010707121840c0040b1440d04401c040000618403800e492060444510078102141007907180e0300c0d001c4146205811080b00040d0000070301013407607000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 389961807 625 389961182 389961233
    0x9060912030601120e010b0a05120a1115040303090806130515100f0803120a0908031308090d 42
    0xa001503020302b80072040503004003c0065070502c002e8004414041032241c3c240890b2000d00014814980340320001400810164005000d800311046030007668010b4580141351140b880640d04080c00651081c101c030007100b00d0400c8003581100300c0e0580340001e80c1d51080511148a8154071600c1c1c0c0b5000455a02c0802c21a02e0003598401d40140e000c0294209c0c82d039941c00d59000140101e0303003180f0500141802c200c0c10030110f480c000002003000303908040c14a401c4e00c0c940b80b04640b100208840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 389962432 625 389961807 389961809
    0x90f09070f030c03051005010c1e0606060801050f0109150504032909060912030601120e010b0a 43
    0x40c01135003298002c1d5040e83d40000303400c5040c0145e500603c0c0d0800054414440c2041d40f000152041c240c000e101401115526154a020400c440e1710220040c0900021524130400b0703940d0000182090700140b152020045402c5450072205000780c2c01e8030002c1da00100c0788186141500074552040084210300e403540c071002c1c070100e51600e00001d4141e10524440e03004000144006400e02100d80008140504200d0942c601008040c014017074020200c00c84000800d81031615010480780d407000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 389963057 625 389962432 389962451
    0x90801050105030a0c0303140f13061d0a060f05130605040815070f05090f09070f03 38
    0x10f5004041c903010a6452070340c4506288000b0f0708004240315a40710250302d041c2150720f041d6485003180c1e1101d00628490074005000d204400105e10b00c0c1d038030041c84450300c031f0703110101510040607000503a19080c0165224000d0816003800c2140401c028041e41008540450150940384d40301038480e404c0920706442c0030f02d0b9030b80c0c02d1400c0084008100a59901c446a1404d088151034034070384072100c417000f2401c440848144690701880c80820045020f5000b00d4036101c0340c20b180e84c1070120000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 389963682 625 389963057 389963059
    0x8060703021c05060f0a0905070206090c03152a07030e0d0c061809050106090801050105 40
    0x28401d03205142840e0351011400700b81c04020001030b140141020768041c4002d103460b49a9500c10100c0d50040010320f00110322032900075030103814400000c105c2a556005201c01800c43e03500070a01052140c0c0c0f050116090f80c42d144854501400000300f6184c02c551010b40100100c80ea00002d00089442540d070940001c5120302030000c8082d400c1001800940000c03028018540201807042c1c008001300d43c54281696244551805e0703603003c0e8040c0020404100040c040f1007020301869000d040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 389964307 625 389963682 389963687
    0xf0f070317040e0a09020d0203190b0a11120c1b07090c0509060a0f0e0307030c080607 39
    0x82488140f0005088042c115001480140c0020710080140b004c1100c8503040326020354180110100c0e0800410344400075400f035840b90303c10302c0a56039160390500489a13019540707103c0200c1481502070351242d5040c80c980100c000200d541c03e0820300c800d1250581c01540300c1030800d401542c4108801f0b11140030340209900c0d01c0c102075050000c86400700d000703801150303850402c0220380d801c296000b5021f01c04140146002030103075004140c0324140b441100380a0303c500c2c1007034850f40c0005881c0c0c1d031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 389964932 625 389964307 389964353
    0x209190e0f0f1902061e09031f0e0a0209070513090e030d230c03090f0f0703 35
    0x8a0080207411a00c14040c80c4a40d5540301540c2010040740b14001345825072140c0041d047c62014080310508189c20030f1b10900c8842c55101c2c00190300c4a00c0c00038840d01419400065048400600d9001044000600e44050b00c2205c2446d074001c00380130200303000b90441074445c180c403a0041003070b1503041890600f0490504d40c034107110940c4400d1240c82c3d001caa86505094050079400241640620310444483d0543c6034010440c0707903040e11301030001d08145030551815103800c5481c100600c2d5050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 389965557 625 389964932 389964973
    0xf030112120903030807230a0302071703060603280c0e04180209190e0f0f 34
    0x101d15203005d0002000109004100010031040901c0c00400d07600c80c812030460796000544403001504043e000b94009601520303610395400ba60301000000030201d034450040034290a0a588030400841b4501c41551461038110403038601c0030b44110035500c2130a1445c40c0d0750b51507180c045c9034841030004560407205040c041241c01146000941c07110030f40e4680044050b0302070991102e81320048030082c404070002c94414040c00303109140300b050004080c8580380b5a441600e0521508680d400401e1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 389966182 625 389965557 389965559
    0x50703060b070201030902010207170703060e0105040506240a030302010203070906050a0c020105030a020f0301121209 53
    0x1030215441c941001800c0d0011001448192400c0f41503118040001c200740b14040300c004255941c02004000b080e056142800688486690110990381442c042c0800601c02041702588405580c40300c200c0031500d2030240c05041500000d203600404a04d2001c024998103400a610130407168a8031041c0070798500e000c460070f1041f04a60300c00200200605001988650011500600110009800c000d5041121440356000f03901c00c2d001610440d03030300e008010069400e00d00102307850500304d00349 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 389966807 625 389966182 389966189
    0x11040b0c0f01180b150f0609121203090f0303070c080a1e2012162604060305070306 38
    0x18541c0c00302c180c11400212400c079191288c0400241c101454916408000e008080c209001c20b06103902840c015040b4000740d031240c4602c10f800d540d0301d0100310348840024801072101c50118a440300100740c94031091810348110300f12100005400c80c10003c00b6000141100b01c4544046047d81044d4401040b0101030800d96101c43d0f900350b0280580c2d20420318080c841000c031410440000743e0a02c1500030102c060325141c403030800214964000e440f400c00406c0c02e203000100054403030b118080aa = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 389967432 625 389966807 389966809
    0x50d1514010302030d142b02040603090b0a020408030f07020d050d0305060a0911040b0c0f01180b15 45
    0x40401f080221000b002c101100440314032030040002e85c681d58000444140e81282c0c0106000a940b040ca903402d01c0120740c0b44c650800610f400440ca01800c041000b40c580c81810340c82008544006070715411034545464601c19560050142c0354020644a0010080d04007038501e036100e035442400c0861821850302c0354191b40c05c500038805113042e103000e03a107481941214203440c00c58050342452180040c020b002d03030310202d010080c004403100841c0c41c0003d800c0c5270140199410108800a071001c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 389968057 625 389967432 389967467
    0x608010513030305130f0b0703060f0605070f03170117070b0403020604050d1514010302030d 42
    0x40c110040003803d05031240c0c00220210031501000c140d290700864503815030001801e00c0f40c84000140e41c1c2d007001030b003450002304a28003c101d002c82140e4960351418a899480e488030464140c4441084041080003c1106000703410907001c0d6010b800f203000c2101000b94a036040a1500342c9551110408010601c420800750707507604103440450300241d487d80040300c1d00b45400494940030054640f055031030b050201c0466540c5080580c140c07031083e8101c030b80400161405079441a080840c6804 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 389968682 625 389968057 389968081
    0x405010c081b041509080d030b031c08040b060f060a03061406030714031003080c1006080105 42
    0x1400d2070300700700d4560a01e010b039090090003c505c40200d01c034501403010a1410315161404140c40e45910705042c80c0144a003c02400c0c0c0038038400100f261a80440c2c62034109402624149080d111300c400100e01c008031480c500d512040006413020f82d1601900187c01b20f0300b003404050160349558090082c1ca100807281140000c1c143c20b0900c144824084c007030740c0c100b04001c00c2484e1060700e9a5560015510000728101158480d030450342006c0901e01171900640103140013440941000c1e240f001c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 389969307 625 389968682 389968687
    0x90203190c1e1a0f0412110f01081b090406050303040b0309070e22080d02030405010c081b 41
    0x20000503e03107a07552400191500414443c0398800b09003d072007108540d00707000501c2c0f55442c000200306c8000c507400340d54400442e20200f09540040c9010700610300c5610030009040100090840648003240507a0760300006411500180c0c00500c030000000f0404c03a424101380002009852000258510342c28070b024001d4804e04400000702210304600c008000303202159050761a400000c0c007082d0743d2840c0c02e02e0300e14040e081d50712150020640050110718030203401d900703a03900344400304945030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 389969932 625 389969307 389969339
    0x10020403020603190f060603050f1609090c020a02041109011407050709090203190c1e 39
    0x12203a000f0300203031005000822001a8060211144a051302c6e40e560001001a8071001171094248101d044980c0000548100c400b2000f25070340c4c0034200703805611036081420354800100e00182c0c002e2001004e410390007001000b82c0007a4645448031030700000329003400074080202c1c0c1c441072148c3c84200e81d0503a030410000c0c11650712f400c1a4001802e616541203806024805001008060101450294521500b850803019080443e0b4107031030b42140384901c848180b034040812000b40c000c013443c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 389970557 625 389969932 389969941
    0x2119051c0c0503070b0a02040b1605010c09050f04091106070503031b04051e030f0714010210020403020603 48
    0x4400281751011401c07001d4990151000b90055044243c0d80700715800407a5540b84200404840e6542840d9070401b00328003640c44403084410250014070340002c00c0d4104002081c055404170303024210310020220700c0e140c80c4080d21a19226100941d035070b00b08442d00044504100180c00909030301044140038a44980400c442c4100503100903094511010703000900740f5019032543d006038442e84100041410100d540303110107207001e030265141d4030b0404d00f1160130713441107000c0690050300800104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 389971182 625 389970557 389970563
    0x609030f17040302030f0f4e0c0a03030b0f2119051c0c050307 29
    0x111414554180588101d108200010040e2020b1007224000e0807008040c108240c8202c0186060215050303200d4000007802d4107070055921655941080c41d1225644a201264458504038907100484540005200049012409820700141c0b484a0030301c03950f41800710084040a008100403500405a401054040c00d401500d1900203224440d03440700088800d1046000380348000c1d40610709003903810340c100b01444544030810220352549500285001c58501225483d600c5d104c0c050030b4001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 389971807 625 389971182 389971193
    0x506030c040906140c040609050f0f0f180901020306040c08072c0918070609030f 37
    0x49100025820010020300303103800e1644181c50b8034402c104c11701e0603281c014003c0d50519103408408546540601650803054004c1d01d4206d403003110340c10401d207824840c090b604100140700c1c0801c8c00c91ba03507000140e5403042e281400d1682d000b006201d8240303002c1c00340b05094840f030720780a01e091403d800c00424038901c80c4000c0c81d80d00305501d00386151100000c2900500040540031807600d040042e00418140b8201c000c4030102c2c040c201010859511a0660000300c2e9007210b40501d42188a8944 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 389972432 625 389971807 389971811
    0x90c01032009010e04061d0903070c050d06060503121b12091003150303210506030c04 39
    0x8107102c50b41458104139408030200040c0485603d40c0041a0703040300e5464103440c2003452030402d0340201d008001103092035455034417450341c51218040c407030083d40f403080040100400c90700180301a140040680300c848200e0f02c1d40030501d0700300c1085051807000a01140160220102e11070449403801180d803441d0010000a1210300b1261010301020181d031050940c400380c21071502080030b90700c070760307034400c4014014211200c014085502024400d0714100500031030303075000160203030304200541e00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 389973057 625 389972432 389972437
    0x60b01031103060f06041e080f03070c090507091a0703020d1809050903130e090c010320 40
    0x13402041d15603e05803405000b00f0140d800440030305040701c1c0a2034580d40319041c564411300b81e0104aa840100a49490591240f00e80f01c1c00ca082c41e45e494040d200040c444810420038050001c1c05c1220a4000212069550a101ea4600450030300900300000352102d2000d001059003508210500d05c204202119407044001034a43ca0306a4541e003148102c440724903090100030302c08182090b200b012a0301600c81c500854141e00c4c0000d00540954051101c44500110000000107518002100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 389973682 625 389973057 389973079
    0x13020f091902030a05040303060b1c050c0d090b040b0a06030b061504120f060b0103110306 41
    0x200d00303544064000e805980e40d03490004521641c94070001040d40d040c1847c02034161500b079082981021014009441c0c100e840f0041e00780c0c00d0010030310225031a25901c25808580c07041e040c03020403944c102900042801894604d56008601c610f0f005a080e64a01d083c0104440c0c0c0390000404400c10280403410900c0d00000700d458001c900c84a642c900f03a61440c91000c03214040c001112169020b02c1c058040c0000d510803080c0040c000e082c28040c0060740342d13003e409488002c2407035102e88075603a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 389974307 625 389973682 389973691
    0x1d03060106020712030912141e030406030c0c0605160e010507051209060409061d13020f09 41
    0x1180c80711441c1c7d002642c000040c540b400d003040341000141d01c0f522241e00885001a81034070000c115140b881c4104001c2c2c1d0820082032007803a120390402c03404421030382007c0d02c1514165441e40f0446204a5480c0556414415161a02c580c45010319510000928009050211942310540c03a004400c129980e55180022a405292a1002920300404480070108039041d039503006a10064080804c5001c0f40c1c011000084a5812005a42d03183c81e8002d00507201300365000061085401c1c001d030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 389974932 625 389974307 389974313
    0x2120607020a083702060f070c141c090305070803090d0206180901061d03060106020712 40
    0x100c07038002d8000131040303103041207100616041c80c0c1203088098051040342c0d000f0741100491100751812410280650b108940c000700702400b403003074200124205218034107004c0030846030040058525480100050010700081d0707002d0103a58030001d1410030001c11111807040241c0055140340b016003c105894001c0d00c2c0354202840c5800010030540d03110034105019000b1921490b0304201d09020b241d0003040c43d00703c0d01b4080d610402c014020150002031490441d0301c00d000300c240403103081c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 389975557 625 389974932 389974957
    0x90308040e100f06020c0a0f031a07030b1002161505120705070204051302120607020a08 40
    0x11a00d0000d01c1007030b0342c07001001d4075641c4c000d4881440e604c0702401007079040f00000d5a00e21442c5001e040300e40181d03068881605a00100342c03d0100980a0741c00c1549904100e6603e9550640c2d01180e4000d5400500307840c5403960200401d1a103513407004500c5011400c642910a4102d0200c0303100c040003900c104060b03900d0383d00a5505001d94840650424904820052603640c1a20030184942c005c4a41029843d80c641d103d0b035a48100302c540900503046004128000303404000541004130740315 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 389976182 625 389975557 389975581
    0x115050306120106180c0f020601170f03030c04090e03030114061b030a02060604060501090308040e 45
    0xb00094502c0000b4041e400041010000c001c520440100001c411680b4411815040001003010201019030008040d41034a0b0030940d2100b203a044000701a207020449401d14840d40800310070011030441200140c4205e42006409201e0f01d40340d0904e8a40300d100034080c98000c003400d80820189400c001d00505569540b800050243e81c00b003001f81440d54000c2181080160b100f80108075243c1414003400c0b005090078213140c4d604a0450796035400030700681c003500c982030440c0c4c80010ba1940d124 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 389976807 625 389976182 389976199
    0x91509030706110301140a0b0d021c05090a0212070f030b0604140a061502060115050306 40
    0xe4007400035480e040f007040d01c3c50140f40c02103049170b0318101c224128000e00801c02810400520031000070b80000c0044414004594010306224a0301a845072172200710410710380700382c440c01c03a080003050300010000c1c1c085140250440107000c400e030b402080755500701040401c00010901002d02040ca031030001500c10355480e017280e440c0c404d044141d900340c2e0500c1e0000102408147c019025003000d50b80e400314144d80700149190498507084889141c1c40b00b020f0003038403203a201604664221111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 389977432 625 389976807 389976817
    0xb0303040320040908030a0e0303070e0618060304030206070e1e010309030c02061c1409150903 43
    0xb200042c00f610400307101510903000001c140030b0243c0340340c80380c04160031441e0051421807800800c0602410404000d9a014140000c2c0407104510310720406120721400600301034403810507050007555081d04036015800300303032628440c181a10304a144001604840720b019801c954801004402402d541c180840a0101100207640180d903650081c05454890000c040480030b0340c3c0241d00c0c02c0d00d6041c0c0d042c030307000c802d0344051003d4880007162525014070200d041c44907540382c0c0e2200314510301c40c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 389978057 625 389977432 389977493
    0xe06010c0816030903020a050102150c0c07030503040e0a0b0609180a23010503100b03030403 42
    0x80c0c524840401024680a844d090061005078840d400007600001e66500108048400202d4500c40a1b10740d034544008407031540041005072054411003c010000903020002440500400100c0602900d00000f003001543c00006449000e06400e11401c03800e078850b008d0703415014400300440c05090f52040d668600401074102d4040a0130404c02c529892141071065003810781d0020b500b40d51114091941d03030015100090340341d0360103500400c000c201082039060f94150720415192a111205c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 389978682 625 389978057 389978077
    0x71b0213140103120314010f090c1202030f150906030a06050709030f0606050301150e06010c08 43
    0x11400082d0081d03010300304610f00c11141400007821a80e80610340c003126a807404c014003800916040c1c64003a14078641d000103001c048544180c40c0388003450314440c1c03400c1c00002000740310040040018020b520860401c0700b40b504110400084510071940b0395010343c0910351040100b074a036003203160040c8890914813207507a203e40b0741c000746a4204c441a2080342e12544104028142403007442456404610165407003410074142041d07040d80a031099042029401c05401403043e000c3c01c603042424 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 389979307 625 389978682 389978711
    0xe0f070e1512062e09080304060917070503070501050c0c03010603030f0206071b0213 39
    0x3110500c015085800050151108080b200c800316a5481013032112007440c0c12141081a050581072003c00e6920003916140e502c614500034444035594520f144c5107821640002012820f50346052180c040381c105c0e107120f6030311142c0060480c5890301c00402e071a104940103190401400041d5449010300400001c101141e0103002001400ea41e030900505410844910b040140926004034040c40d00c99980001386150014020a0606055081202d14000007003810310080d2960003840314441d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 389979932 625 389979307 389979319
    0x604110a180504060302010c140c0a09090b0f0c09040905030f030903120109060e0f070e 40
    0x422010003001c0361a528903480310424520003400282001c41d800e000b20f90940e07000070002114180d00410707000c00c0307020204500905201444540314041c00014100d03640354000350281949190607a00b020084000c12010480207103814883c01c002840780380341441d46010b02005106d81e06055680d40428480c83c11500c0015005500800c00c40c2c0007181c4400398880840c0500034107070311001040d8a0a0000c001c01c0d0a410600340d80b1000e0f250240c140340d95101010340300c0c0d030750301424140e01c03030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 389980557 625 389979932 389979937
    0x80c1912200a0e06040e0f10260d1107030609050304030b070306290a0305060411 37
    0x4080900307009a44003a540c03800107082c0401c49002801c200f41a80c09841405001c400d1136500e08168400040e80149166034045002d400000c0d0281685000340c117480560010502020340104003d00e0b050440c0c5c0600104180c10700107071031548000c201c50058a51000c00401c1c03642c19403d255286014541000c1d026a4509007485030081e0551700c920204c0c2c2e20001d07220121a00d844896003070b0700100c2d484115901c820000c5034003da04c2640102d80c441c40007400050281882522041d654 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 389981182 625 389980557 389980601
    0x51012020f04050907050705070b0a11120c011a0901031e05060115080c1912 35
    0x11490031403242c603a42000e040265049005140b14100b1000344031050100360001001d508450324020100c1c1c0c0d40b4649a400c403505445d5030f4501307403240302d0300d40c1c44d65031801c26000414030806034200801018140c01218000d500401040c80e0b070044610f00180b007c500350030465084500c00f894a2030030300500d50b88060034420241c0c05078a4441004242ca6032490304904d9103139001d08800145072604024003668203644c0341c41c1046004014039000c402510f03968980c04541042d01c1d03010588400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 389981807 625 389981182 389981197
    0x501020c0d021b0f06030a0603200906091006051b0624090403050405101202 35
    0x64002881d460318405075400c40e4a555070001a4042061180e101c650300605500d60380b0026080c90300003141c121301c0d16400007030340942d640c07a4110389040b190340d100d03034004000388400150300c0c0c000185034110000b1103d001c02d5041082d41c02c0c1000300140f241c070040c081c0100c0c45012410f0401d800d1600024041e00703030b0314249024507203008200f000364101091140000700c0808181004d5001520882e41134941c24686030501041007595003440007040104501d0b14064034185006001401d2913 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 389982432 625 389981807 389981827
    0x909040506060f01050a1b140a0c290d090602130602100c08070e09090307050102 37
    0x103802003414030030b042c1010119160980400e0070a9072601324a05401080d0070f01107010890291025034103c000c014506036000f01807004003088405100a0741410801012244180d41e00c92200000c01d0205040401c0c100c005030042c16141818000152070300800b92084c1c0200720b452650030400c0c0d8002821040080025051550007040508415440d040807107004c0390700340040c41401802c0281e0345501440242840c5010749a281c650340725441180e196002e46407004020394004030b070a00c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 389983057 625 389982432 389982443
    0x2010e0111070308281d0d0206040e151210090c08030304030216060c020109090c0302090904 42
    0x4d0f600060f0043c64690071442e51950f0381c20304c14039024003000190380307030040101c010f4503a8a80e5810b043d60154010490000d040050b40c6400041c00182111024500d1601d40490f480f0040303410030003840d0003031076052624800c0010200e075900c5008040107000a407129141014035071804070340c0010b0030034070002007070200b030540001b120b0400e4854003040e000c480e88c075100121444044648001e0120b400681c0c1840401416006010403500f540703801401e00440c0000a6400802940c06840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 389983682 625 389983057 389983073
    0xb0a05033102040518030d021e0d05061f0e2704030206060a0f0e0402010e01110703 38
    0x2003100d140704210a031400074045d14003900040c004071101840110455125000da030301c00581e82d8010030450350f03202500a0348a1403441c408036008400c41c400c1d800680c402c9204440c603007581c8066040390390b034141d2102c0b0307258002030400603106201d080165014002d43c00d000040c2203801f00c00303d08140c80d41c900300c40480060700200d007400402d081c000c1c07118002d02076810055003c241441e080960325840100064100200c00440d220564090f1550100240b65003003940d607250307168184214 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 389984307 625 389983682 389983771
    0x1030f0323040902070506091b04050901020c032817040f11091611070b0a0503 36
    0x61760044099a00d591200700390301c0d44e240210482d4450701c40c01c41003180014605a131190760f000d81e000d0f0000d454800501200d90075a440040c1090242c100892680310021f003040e01004103070014140051008034030356031115600c400a100911504a054410b41040b1221240c0380010101030003404d09801c003d074085d51000e0321078410f00001100d1429611400034005550780486a803000700500d07100328001d08403003030b500051100e00c2040c105010303000321510300103010345034002904c103508 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 389984932 625 389984307 389984317
    0x1b05030d0c02070801090809060307030603080f07210f201e120301030f0323040902 38
    0x1415030b0144480341c018440e01008000150907503c0c0c0f24800d01c07940074214841c000000000b0380076030003a80640c002d9500408080d0f15070301465082c0d0b0700d42c0d12298059a4400d5440c0c00c010400c1c0b0701b64040141d640c90fa40e600704c05d51825060517954074004080c004010800ca18600b0301146c0c08200110f003041c0d0958241c440000f000180d00d04180800c2900c514140c0100b00510224003450b01d040404dc3c1d01d440d0803070100059100c104811122142041c0c440b1000180c00240e005203034020704 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 389985557 625 389984932 389984951
    0xf05070e09010c030207120c0309031e17070c05040b0310020c100501050117071b05030d 40
    0x25041d402d1150303440680c4d201e0310031030b0b003810f600c055120383e6200074440850301c01a5860b002c50910041000c04408545030010011003640564240f0f50b4262940c9000b01c0014206085c200c4815030034060f041c001404410b80300181c460039100004c410910030006480c058600b0300e4214190310004a10180010104080508051200017800350340d81c0c2d00011130300411018411141d59508001113001c0310311961003e141420000300416441003507407191411580a000c20310929542c030b81400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 389986182 625 389985557 389985571
    0x506270424050112020307020601060f020102070503120a0e0c1c0f021503011d0906040602070f05070e 46
    0x40c0030310110b03284c840d0014410310420540540004030781e81901c0045c18500308070030030150100d01a10031038000034034600000c5585c801c00064000e40500604034801e0901c4003d00084a407035984003080d0105a1100c0765942400c840018086008003050140541d00008145500405c02c50080344a80e48260b813000401003140031409100d8080d51104000710720020f01381990340c240ea554014201510307041c0d0004400d82044503419030040f8103603000013504c3c1401d1b55202c03540302120041b076000b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 389986807 625 389986182 389986187
    0x103050709180605040c09050d080f04030611030f0c041a03190606081005062704240501 40
    0xb00406e00c104081e50480c07002e1103500d500c2500c0400500003d004000a407084060f40d01c0c40d80d081035126510301040e101c90b070b242103000c1e01740402089403d8105034111070f040041c106a10b443d05042078103022a1000d01e00415241c94400004134020394441d0a1480c010700f05100104565901c40740700a094030000d40d44030700300401741240030075a4507041d011501d036903008403c0340c07000c03012800c1e0b040610110b81040350340c820b0f41e44003203086011600350440410a020200e070080d03182400c001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 389987432 625 389986807 389986811
    0x130c0f030b07110c130212070906020c04060614090d0b04060902030c011d010305070918060504 43
    0x75034886040c0c504404410500d000305583c80d0381d0401c0640c815080c040b04c241885200750b060b00c3c4440e001c0c0c8142100382c01e2401c0d01070000c50303143c05060010300079100101e0031400c06010b854101da48035586c1c211039200c26407060409810500754158054a81c8070040003203401442e01901072400340e48001041c1c0d41a104040c40c044101d01c009060000c0300454030300c3c1c808110015400d031402820040f4217561428003c0b504250150009071402520420701104003140e64400b5003503c41c01c1d141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 389988057 625 389987432 389987453
    0xa03020c0706110a020d150e010b130b06070b0907032405010b190503130c0f03 36
    0x10a038540030b483c5080d20412030b00000c01c0300c0c0070b0f50b40130800b42030500c01091b45c88280804054100465a000318022030b001e0704000724400008105200306190101c2003820824604100303007009540d89002c8501180e0442c11440c0c940d103407481301c00c3c200362a17507000625040e0041a4140c002c510303c1450750044600043c1000103a90b40d0031410504d00c6146c418800e40c001801208408501810103540c03c0004180f0038855801d04d65500300d0219065084048038100f05202041001914010b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 389988682 625 389988057 389988059
    0x708030a030516081504060e091501090506060403080703021002070b091c02030a110708030a03020c07 46
    0x2e450586900d850340d0080d000615190081503180302d810170b0002080120740580fa099222582042d0b8403400c111400c0008110075810214450450394140da032601d080050b00c10071740d2800d5222400300030400003d86180004c001846c42401a540001d11071084403040760004901a6601d08280f030401800e0001840210340d00000c64410035160340e40000001d40c0c901035a00888248140c0ca00d404441c20000c10407640141419822642d46d0b200c1c030540203029400c0001e00980621480300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 389989307 625 389988682 389988691
    0xc07030308060d0203061f0b040603020c120c0601061209060507080f011a0901030213080708030a0305 46
    0x41c00601c2050f8200650158040c00204410003118004000e990041620002490707440b5400d01906030b2290340010300090300030511105140041c0a58164490001402807826020080c40ca0700c0d044140b11354403c0c0001034000c1803000d0303051303081076054bd0b074404d0041096103060340000d0054403080c0c5240515810b100c00121b00007401944d51000e0f144502c01e064101502c0380c00450117503201d81c10382c0110001010700003590300340400504000d40000f030041c5488071500da4004085500092 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 389989932 625 389989307 389989309
    0x60e040b0409031d06040b0c0d0e09150d06142a0a120209150c0703030806 34
    0x201041940d041e43c9008207803512011580c4a80c00050350152065501c2d4002d4502514043c540a40e4407031100c10050307907600740302143e07001003021900d0558191030604100c0c6d200c0c0b0010008200002800d00c20003c405240c01011a5400d6070780000201c404030b01c40660744034440c188905040b03484506204141141d0b0099000c01007181040090591603000b102c2d103080b00d94040d80941c59104540010b01c0d4081d1003420b0002146000c0b5884e4440071001403150201c0313000c0c1e195603041d074075484 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 389990557 625 389989932 389989939
    0x220608070e03030d180c0b3004082104030509100c05120c1501060e040b 33
    0x1d06540050001001507090400151801c030061a910000c020b140c2c041340c200c140003441d1181d800c8014100400c055440300c00848240c160307501443c0c807880612001c1158030132043c10004085070000d401c21036181c0c80c1c2040b4801c034600011900803c44d14154542e04000415034400d00400124406176440d0316002a100300c203031040d02d10480028a076420191100c101d0748484405080e035002813204540c24141c1a41804943c840c00b0f80091f000181d285440010a080a00030710b2010181034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 389991182 625 389990557 389990567
    0x110607090b1804090b04150903050928060c0516050d080a02010222060807 34
    0x1888042500088120200c40c01c0c1e1a815444469241d01c001c01c4004031102c85401c141401001e10401000c400c2075840396220b0010002c4074001c10014008507240000300802090702000261001d10780b20b000303042d000c540215251804030081401c524a540c0300d900c00c1d8080f8010441e0380c0c0c00c00009010303221001040c0002124080e1800c030020f100529003202c0030380304000c00603030040018801c0d01150a8088185405c174000c00e0641c42442c0c4844691080d40005004078000c10300342440341c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 389991807 625 389991182 389991193
    0x7120906030b0d06020a021501030501091703150904060f110d050108120d0f09060c080711 41
    0x300220b6808044a02060f001c5680c80d00100700c0070030304c0c0c4150303034240a80c81a00c20b461b003820307001640c15070356a40800b010462241c1c1c0110303100041c001081e0845c40c0c0f00c688480e0710600b89080e5805011003801140c00c000030ba81060341511900e0174140f10002100340003401e540c0161a841031914189400090051404224207900701c0324046103919014024200c400a450302e41c450042066440c10744ea8003140f00e41c45140003161031903440d00a1410500c134001c00c202000030200600c0e8005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 389992432 625 389991807 389991821
    0x3191415040f0201050a02030d2c0d08010b0f04260f03120721020712090603 35
    0x15610002c0c00c0900850003030600030f002c107407240362910030021b0352009203c900c820000c1109a150341012400780c40d40c0d440f141d41001000c11880640804d080481c0d0b01030f0f80364560f403642000c00028494115081c0b066084009000c009940300c80070011048051258408244250b90300300b400d070400070300349010100e50380200302254602d40c204000d198440501d14014000f000300d0401010f000700c5d100402c82d8000c1c00403418205001c2c07401040a4240a55150158002c0e84c0c0da406405842c44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 389993057 625 389992432 389992441
    0x9140d021605040c08040237052d0f010309060204090e0f03090604090b03191415 37
    0x170f03641c900303030360391158280925191140002d4805042d181d524842000c61200d201d012089131480c01103100b8649414000c4404801c41c441c141c40c81004855021903183c03048070f4090304400c456044000003282d00580007021400d001030000c034000070300801c2041650704040a001d00f44400c0320715000c80810810f4690041e03140d904e902c07103000c0108021441c601e4000303031010300000381a034550390310582800b510004008012a203c41100d04110880103003441414035250b00411801201d252 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 389993682 625 389993057 389993081
    0xf030a08100806240d0b04230d0203070620160c08120d09140d02160504 33
    0x46202d4a80a500c5070f204c1c01400d01000390110344880301c80003004244240090038441000783c3c1a000034200545080700604244034074414942d1141d01e000f01a0246e0410028400407500d2508000e45e243c600100c2e00d03410b10742c8050741d00d00c5507000d2150400740100140c138030420001c698504030001c0030520001c0c4032a008494944005120b86501440103554a480a40403c540204a0200407820109903403002c012200041d4891402c0300345108901501c1c01e02080c1c51406108010b02140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 389994307 625 389993682 389993701
    0xd0209090a030f260613020d0b210a080708211b0a020a02040c020f030a08100806 37
    0x118135107510030b80d520000c403242c11840041840f0b092140c120640c004036000580d120b00060346500b0105d92038102406030300880d411895031200c0001222019644d18018060010001c050015540c0c042c41181e1050f51003410304110b54440e200281210590055001ea4141000240707002c2c0f2400c0d640080d00481da103c43c000d03009000e12208540820008045080f00c4c4415801445124001024148010000c005417034940c0c2503142032030200d1040c004070903008209142d204906114080c0c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 389994932 625 389994307 389994347
    0x31002040b09130906090506060411070b010e070c050712112d0d0209090a030f 36
    0x144070005400f4040f201c1c0c02020100782600b00101d0b1a8020b03030200722141441c00c101c0c0d1107442c1102d04031301a5007030070a0039120404180407110550382103c0c0c1907407207900f090400700403179402034442c004102440c64800c0200c1e07000d2005038001d18411101c0706403102c1500d440b24036280d031b0b10340c910320589004154200c0070342c0f41c2c860f1004d2100e420b041e4001c00c0503d400060760203280254040d4010410004011b82a039001400c0c00101d0f010391140d00c0c9141c0c0818007110121001c20750343e04820 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 389995557 625 389994932 389994937
    0xf0c0209042913110d03020a08070c0f0e0f06330f0706020405031002040b 34
    0x2102d40b035594100c000401c100300d00c9652001e080e0031486500318854041c40440904103800c02107800c01021543c0b807419014400c4180c2d080b200e000c039070700141152500d500030780866514241171421014200041e40040c4105100c0742c800103103015804840c9100c0d00c200800c04900f9501e03502003000c0c81c50b05005208001c25500a4003103802c000d19104c10002d80305031340451a181d009201140c164101300003caaa01c1c2d0005404e0085060a200c1c0b1100c2c000700c5842941414104030b203840070f60 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 389996182 625 389995557 389995561
    0x13031d030a0b0912070f0b0603030903030d0504030c0210030212150a062a050d0f0c0209 40
    0x150881440c0d240b94850307103425441c2508a0059180d6280045144010041400c00e04101e0502840501c0c0294580008241e124403d06007510b60540c82040303410003100d83d941041d680f043c0a0306040c075103031220341c0115494001510b00000003da00040280c080710604010a0b003110452441c41a04814800401d00000490150000303003d00b4a90100e100b0494009a4070040051070b03030052207280e47e10f0019500e4045482d0a400310307294110481c8414401d0040b0300920b50018400d0b0f1080e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 389996807 625 389996182 389996203
    0xc20030909010e070c0f080405101d0411070f060b04380406080613031d03 34
    0xd4040180160099814900220907615507140d0032000c0c0b08440099507d400c00040c100300a01d0a41c0c0002c2e031413041801d20b41140102c1c1c2649000c02c03202d000078280181e41300e40b480c5000118010866400507405031503820a11070720304102c00241314800d001c0740540d01c2c3c1500d6500c2d040e0000c000d041c01807400004138002054035495a90f422061aa20541094460501041c0c0180038040c0a00c0351204210304030600d00c20b41801003805035031201007852028002c0c0c1c2c0e480d00c1e0b1404104030604 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 389997432 625 389996807 389996819
    0x809061302060a030b06040312080f0109020c0a20210c030a0c09051305010c2003090901 40
    0x40c0c6034022200705d581d43c0800c4800459200030881e4007e40500c0c0c000d0300f605401c8840e40c00001d208070000545044a00841c0d800c603158202070a094202c0d075982e9010b2003140c240000031a140400a40c980c0d40341c0c00c201e24240845c1c5240015174000726030840d803804a46500c070074080d420540044000845001018064030140200462196200b814240700c401003d50080c0c01d40d820072214124564000f07101080c40142100001210031011a00980d2031090003c060340001d130740304c010040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 389998057 625 389997432 389997437
    0x607020d18050f031e06040b010f0302062b06060e01090f29070f030809061302060a 38
    0x40b03481082000d40500420701759000a100035007068200c0c4070703184090403461802c1c0c42c200700501030507000000180c2e0490414030251b110344041d100c8003804070000304181030802d0320520b809100311140c1c08460381030920104001d0b6000d41d0b04500c1450a88500200c913450300040301e201c400034007a81c0003d17608148405035407004111440d41e0400d9107001d09180129584980780d00d00c0d501401600400c07980d2042c0716072500100040c42e4030a4500c10040e1403900e055000a03c40e100d00300c0c0340f504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 389998682 625 389998057 389998069
    0x910030623160e0d08030f1e0402040b0103060b0f04080f0d020601120201120e0607020d1805 42
    0x50104825641c149403400c00b00e0388a804c624050082240b004e010758010065012100115500d400764600031102402040c80c2e010803440002c1c0062074950003032042c0240600d0007140b007540d600302c5070803260800101b44c4202d0101040070311070140204454540420244000d10203001e032600040e468541c1802840202254020801c00307690040080c1d50144031904010032100c12503240706600c0c1d07141a00d912005001c1c16030109243c6205000025120704155407440d9454901020098 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 389999307 625 389998682 389998711
    0xe0705150a18030f020907022406030f0703060e0c010804030909020f090910030623 38
    0x9a0a0b401c24000512001480301c01c0450b0756002100c691501d0300c2d4510961420118031540308a4610042000500480c250419040c900b1050382241d54804081030403503a0500c8800521400c0008983c011b0b5560b04001002d0030410104685600400d12700c2d1085500c2800400c0c481d541545802d03080c107240a0007840250711003141d240303001740c040c0320b02c40b035564540319003500030403001407040141c1c0c1c11410b14000300c40c2c0301c0c1101a40aa550015403015800c0c1c42da81590203480201041e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 389999932 625 389999307 389999317
    0x415050607120c0206030109050f1003050304211a0f090712080d0b10020c040e070515 39
    0x100580540300140c5040d40050100c6d03200e680d1480710901600003100e0001c0e08103244000f25540003d1103200c08240c9500c280030b14103060408060340c05900b00301114481c2000c103001e0304404265080c2082c000001305d141d582d03425140100341d110b41a04050001c29560380185800c00c04641081d1801c1211540080310542c0c0714002d507410b1002d840c044860a501c050303a05030814505800141d1200402c00c05c5d0750078081c0d140c1e110f200700c0d10340302644582d580000040002d100b07180c2000000308 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 390000557 625 389999932 389999963
    0xf2702180a0f0614010f020309130509071706011a04180b03010e010e010b0415050607 39
    0x100503901d8058607800d8030b80740e02400d401402000150b499200300c020000d042a85003d0344101154001d00c461025a9240010038800b03420460000481c0e44a54400a05220541d000050300c8844c0291103120000d0000320541281e840001460072800c02c0070a0400e07034031039481103113030000b1030140b032404000302c0e58401d81030980d0090000868601d0b41400034250340038902c5242071a552189004224201805010b561a1444490b80c9940781418006101c5024940016000950311b2a080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 390001182 625 390000557 390000571
    0x4050312011e15170907152316051002040812071a0907090f270218 31
    0x26001c0c0c4c0c0061040c2e91501d01441009030f18400020700c0e4048802e901e040c1401c40404046c16180070f0b0300b41d26416241328504100307210111144008004041d0080d41400c0d142440d500e03001e013496510403c644003960006000c000801040151410b0048608111403509040d65a8400340183d908040303018a00d50000090500d0800d00c03103034000b4040c10340c0070b00101103104c030148010300000d00501a040400d5500d00d0401d00f5010a0651b5140d0151041804104455000d000c000c2c0c010321003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 390001807 625 390001182 390001187
    0x31b0720120703050106090b03061303030203090312010b030601030b0607230a060504050312011e15 45
    0xe06400300024410301e080341030380c0f003501e1a940d00c4d078043c0945081030007585108101500149181d05040301e9030603880010b07203405800c01d540071021500003842407085410005450706075001d156182d03480c40000e40c0c410b0f150309000ca4034080e40c41d5150304189094520300c3d6080740850303034010b8040200310f6070300c14842c10203d40c80c080e2000c450000360551150500480c015001107807104d100c40741c0c00700404010b803c801100c1c15034103080000e03d41c001801000307131544000c8402d042c2080075000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 390002432 625 390001807 390001819
    0xc0807150509040e120313030914030c132003011d070e010507020406030512031b0720 39
    0x408402e40f0308036980d1340c1c07810388003032801f4001880e82240041c0c2d207003800103690104c05144410118004000d08181c0080108000d50000904502c5204555a003601101d0b03c2036000100c10001403800038035240d40c98040302010010b400103001d500504924200001c15500103441074603480c0900389503448190038000f060081006d0780000b800741c1b00d07000d940c2000781907803000366118003042082d81580603908040b4450314050a000145a40d103240d0300d05848450409600d10f03074803406014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 390003057 625 390002432 390002443
    0x4061e0908090d0213020a0c050c090108120a05300c19050306030c0603040c0807150509040e 42
    0x1803041795182e0320082401c0c0602d81e035041c03c400b01a03d02641001c100220b001c4c801d04600005014100340400d50812a212608030a60380e401d140c9002e8441c3e0003014484248001c0b030380c29044000091120000c1504410010a519070b9900360b1144094002d00e642c00b0081c0d81051070500100b4000e80c021508844020100e074100d8000000040d91a801140e048440c0c0031000740800c5050f10800012001e130020001c00c01080440040c018040e00550080c28461600c0b403c0491801c48180003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 390003682 625 390003057 390003079
    0x50c01110f031602042003070c061b03140108010b09130c0e04061e0908090d02 36
    0x2444054000003c081c1031440c10b4440602545000f26410040e4030b100c0a408114242d03a101514030804090002604041c01802c500d001c5c50b00468004c6500594031105104030300d1110404000f080e0f50f40720310030a00050752841405000600000c020340000c0744001000d24100521865210080c46401d908000c40d0407410b10060130382d100101c880f0f003007d01e001030203007001a40d589031840c1b0340d00ba80c0c903214606000c1c400c0e0294010885924041d44032051049110070340e1002d0386c22000c1400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 390004307 625 390003682 390003703
    0x1404170d09081b0d0206092e06091b021b2403010e040605070507050c0111 34
    0x5206a6940083c0c954182d4072605040b10120100500c40e40304010340350300282c441441c102803156210340c001040c42041255412150b480c88103d2000c5014001041e0810030201752281a0b0200901c2001c02109200c050301c0952201907200241315a9050300c2000040546102c0100748a000d2049a03e19001202400d2403003801c4000c41e805140207000250403042142010706068048401c00b0b00381e0010000100041c1e804510001402c2d48c0d449405e02c3c0200003404404245e9040c81030620 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 390004932 625 390004307 390004313
    0xc090302060f0d05070504060206090c0105270a1d0105040c05030c0a0c02221404170d09 40
    0xf041c041c1d40b511200c090f0090300b161003490054042e0703200140b51000089220040c1000585829003042c0c440702d1400306001e00e2401c541d10754501048403120faa960100e0100080c0311250305451406024201040c110031306030302880c0a103040c0b001c044045500102a40d511451416803541c07681c1e2100000c070756207124004065000038420303016903070303040e001502c840b10b00c0e207154824810303124440ca41101c845402c80f800f0700284c403082c9001204080b10307001080910017000020411840c1c0d51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 390005557 625 390004932 390004957
    0x509031608090a180b040b091e2809021305010e070c0206040f0608190c090302060f 38
    0x8a41c502c01c4c01c541d00c001500002142040220380341c24105c2c40c051000d080800c0109807960580988030062944c0b402c80743d5440f5148110398504041c00c5816141154400201020042d00019901d910842c0c40c80c03030b49100020b10004550003480349040c603450314004a0140c60051001c1e4070314600280006281589810540601e54415880200000c12020400210f000c1030600c03103407051600da070700b0710140c40308450007814008203000191141c080002c20b40e240d407070003604a966100010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 390006182 625 390005557 390005579
    0x140f0c0306130c05030403080f0415020a090f1203021203040309030209040212150108010509031608090a 47
    0x2202d026000e03131120156220300e2103a1190300f1076071505201c084035010205d500911041d40f81c4040800c040f80750300a08540542c80c1843d02c6119103540300844011300940008215a0811040b0410b240d81046100131400a49050a1031740c207040d14002d0000695000c003170300a40c18000420115122807648420350803074902603810b640c2004c041440e82400c28170a4112942c2480c1c0801c902507008011140704078540c072500070840841d6900c03e05e954014515480e404041414002010601c007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 390006807 625 390006182 390006191
    0x90801090c050f0f1e041503060603030206161d12070e0a140f0c030613 33
    0x2034440400445082100d850003d2103102800b03415240392000300000c40c081002d007120b85440040103860000100103a4031150301817030129600d8002c0c09002039403070920030000d001a020941c018054040091345e92014403e04114201480e6940c0c2a45903800301910144008408203552265030008019000c0300c0400010000e01411071001c0110700f004060700c0101c2d41c0a0000068000d0084100212444184002c56102c8402c0c280306503640c2e15240002d4030390514042503604580b80c13 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 390007432 625 390006807 390006821
    0x6030e0309060406110709060503030702040f090f08070618030f0507060627050603010b100f090801 45
    0x81000905a4084174254140d0303120b40000801e400596014100581304003400840c1040d406400700000b80030b5000078000c2d11039542d01000b0100b282001d00380946801160043d030b0760350141c0703400002c440c0d10b90b0950200d6000d8400900c00031b540f04d450300c800b00090349015a2200b92a0400c00010b200903402166410200b100c250325100a40c096030b00c410716042e2007000f07299211000c0c0b5090f50040d281c8550b0002550300f6000d101402026000d142100500e04106507a4036098994210780072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 390008057 625 390007432 390007439
    0x61d0105070f020d05010b2403180a140d090e01121709030d020a121806030e03090604 39
    0x50f10007c01c045d0811800e1150011511000054554200078903904c0c0c46009012650040410415111000007000c0301c5072030701e00d101c14010403030f03a008130307038295058404a2500000c12142e0795101129650b501d1602c400082801280d9089072003100d00c0001804070415092225142c0410909200950b40060b04120904101c0805038100c295103108000401c0b41000b00200e503818140303070005400c00c0c02244460306000312000e2560390700c071411003007508000356042d480e40100110750b170b1750700d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 390008682 625 390008057 390008063
    0x406030507080705030109021f021c18050d0b0708280213061d0105070f020d 35
    0x280500c11602c480b01500c07080c6032100c0600d406c0e41c0d8006070194104400c960035144142041001025601d001d10660310f80000c241c15040c141d040540c103000000354001203254000e502c00c2445802400226040d00300c0c00790560b1000d984000c010011000e000c80c00c030001c3c84c0c0250800550005407010304503082070b0f40044090740d0082d041203840d15031711150798901140d001d0044418043c00b03804130410355102500341e801100d0580c025081103a80c1020071704104012b03107500c0c0d01c00d1150343c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 390009307 625 390008682 390008693
    0xf070c0b0a0606140310170f01020a0e031509030a032409021b070b04060302030a0b040603 41
    0xc2d48030500c00c05030081113400340b0b0082c803c0c4044c610703d8000c007601c0d4a01c0c400c0c01031300c120070b00342604400c91003020480e40d401000020000c654800402c0c001a10031601c06420754080e00a00e0113100307050280503131030b1f40300e00c503000301462030008551000c13402170162140803130a003a4400c016458201003240b070350f030142200200050b80e459140706807260420300764030380030015400380c0c00c00e00070710b01040b094600b00c3d8110304000d6129220005500040c0805440d141d40292400c08000240701 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 390009932 625 390009307 390009311
    0x91c1b060909061e0b030c13090b03010b011b030c051207080a180e0f070c0b0a 36
    0x3014402c0e030080d80d190010118850001004120400f0301801080070150b0810840401d81d90000d00f0a55981000700194070100c103100b5961001860842e0b0000f55203413014040c03600359030064000d941001001c2a6008400002c403001100700c54162800c1c102090081c03520900d44110b407903800c1103a880205225040102c000b00130301e141116955214455100610340750300c141d460f8082d0010b014840780008810051030303038a039a80900c1c0c0745002640b0380aa601c8580c4205000c0d01e411001503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 390010557 625 390009932 390009947
    0x7050402090a0924080a030e090a1d0a0c060e03031803120d02070c05010302091c1b06 39
    0x800484d06010f5200a42c001c0001e64201740c1c503000000350850182c1200071400c0c1c80303450702981c888461500a14400c24504c40c0807a6200d04d00c05000b13800314500503030903c2185400d00e21a1110f900325100c00c0030500d501e0b050750040001c8290003111441541051500508460300004c2d008140c0c0b240f500f24000c030310324144d00802c5142c2009840460030016040c28a811410001c0040000300c4c88820300000c0940c1d1b410015000043c000350000200b0b981d4440b8195494460356110014001e5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 390011182 625 390010557 390010601
    0x33007061a0a1e0b0a031508030d06050a0513020313060f140903070507050402090a09 39
    0x1d04039158038803555951010a0840040101503650580b807143c100a0441400700400310a2041d1074000780240070108402031422113900310004981c80450030902002e110b129000c00b42400305c440001070b52600b40060350020107810403a10880d004000314488150131092072011903480401480780030f0742115204000e00c030003120014181d0b15440401c09210700070086900c1e03190040080d02c0f0060806080c000070b54806031100d6040b114080c00001c4540f600d00c6044d50074154072a42c0c0703d80c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 390011807 625 390011182 390011231
    0x807050f100c0c0b0103060f06050915011115010303201b03010b03300706 34
    0x344862150602c601d01d24100860307a03880c10303503540b6520741c41404000c2500e81e8842c0c00504000f015800070303000d0f0401419045840c1048c00d0300c0c52440b0403580005000903610443c00c0d00c6003401040862130361000b0b291089a5900b182d40541703220150a0080302c6a00b401600c82c10a02410841c10b0200040c0c80450440100190185403c4d140c0c0c4e02c060501070350240d81d01170440d2102c1e01480c41582c80360800034021804003001c0c281544038500000c0c080505000b4960002c2c0e10442680125 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 390012432 625 390011807 390011833
    0x90c0509120f06070509060d11090d03080105090a06060c260304050f15061c0807050f 39
    0x9010360f0000070340ba00c1c011010f680049a0180c01c9070b0400305c0600fa00001000d05040845c0014024891080503030340f00704014900c2403180e074a0074541d5140005120240002405c0c440d9054203045051040030707400784d2061000754000802c200c000d40707440405840d82e06402048420f00000104100c14807a00094140b03c020210b400c813681c28103078080c1d03285214401d942007948440c2e189241140b03032140c02c4100d190705004038800ba2502031140e0300c00f8031307211400040410039082a8010141d0f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 390013057 625 390012432 390012463
    0x1218030f05031003030f05070203030318060915060405130503120115110304090c050912 40
    0x11035150080105101c4108140000c0329445011a01103d51502e800c80c20800c038618115828003d0400c000c0d058480801800548000050190941c1c0d6400044a505a440c100e80c10b40c0e82c10840c2c01c00400d50f000c040480e1560a2503040710303a00160005031411801c14a0340c2c1d00e40740d94804007441d14000c8806005110406a4108104000809240c44e503003003032244100755100c1c801d521440d09056a1209180c44a601610079a4080800100230b03446020320201d074161506c0303080a55466 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 390013682 625 390013057 390013067
    0x4060e03060718090c1103030f0414011104090c0203070c180605030106031e0201121803 40
    0x15035035040b022601d00e40c01c94088400801e0000040244e94101e40000c003150a83e400d0100140031242c01032440c60b081200c01040c005408401e00041c4012003051056180f0b9260090005a00400344400d407485684207a015465035a155403280038400d01c2600c880c607034005400c10481303a440c0080031031003042101400031140391000010303c40c82c05200344421247d001d10148103450314502d507403007401e0401005038184003619000074941d8071584110407d001d841c51090081c0c00d06e41c200142 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 390014307 625 390013682 390013693
    0x415090f052406010f1211030c040806070c080702040c0c08030c21012d0b04060e03 38
    0x1c41d01e4480d055607901e0030f01c280040c0242c3c00c04120305080000d81440c03d4680105908a0010030050300c400c0c0e690703814000c070481800d42c014041c2c09940c3c8101400700300301500c20400b0394012034200540c0c0d418401203508003c043c100c2c0094000411142c11100c80205010340025402108519034540c1d0300c3c0c9100210020380728020f280000c45148200041062a0b86452810300e06500d400003401d8181310410024814202c070f401c80000c0c0f40010602051154010f9034400b9500e0088003210b0303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 390014932 625 390014307 390014353
    0x10e040920030106050d0b1005130c1209050c120319020a17030402090415090f05 37
    0x1590805114034001c940d801070901886c403e9540350812a0798001c1c000b00c0400e9413000d008038143c0c80303074080c1c21068a240c20000411a100a100810144c0c20b0b0b0404c4030103500704115400403c0c4000349015102000710f45480916594108441c5588125001262010819501459547d03008682030a085000e04601d0101a1342c00c1030800303843c0300031900254807004401c08240401c2045862000344c0c251b20000280758142510b4011b00c0e50f00c8104100e505510401c03045100001c41d40d6544 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 390015557 625 390014932 390014993
    0x504080c040b09070c0309030c0905010f12030c0803100e0a1b02060c0414010e0409 38
    0x300036480c004288107a40c070f804000a90041c66420440c0704c8649500e41110186003d9202628605500341c011440c42e60340c1e00414100d903024a03141c28401e0700c441944221080c1c101c0020700ac03a036001c3d0f061000a401002559025a0f24494240d1903507441c44810052401190090013030350b9140700c090700c129808408449142d243e8401000300c0d252643c8514000d20580c041c5034440c40382c00e959102140e1040c2c010300541e00e409030050001c41c002e440c103001850660320350140c48146d0502c64a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 390016182 625 390015557 390015559
    0x32e141201050108030f0c1501030807021305060108060d0602070c1203081b030a0c020313060504080c 46
    0x74240c850a104103800780d8420001308030040d00c2c100150180913403510544902c48c1e06100200110702003030300242c1c0d11203c00110b110031864000b5000c003c118201c40c051100d8580540080d147c004010302550003010300c080c1c03a10030484030368103d4445980c070141d100d03e626207401c09015a140c8004046000c601020040ba14101450301c0380307070803c01400d80304da10b5980d90002038000360556214100c20342c8820f10411085460030000c3c44003800c803942d40c154856180160280c50b00010103502 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 390016807 625 390016182 390016219
    0x60c091208190306050109140a05130c031b02120d02210403030b0a0b032e14 35
    0xc040d09220009001541fa480b0b011000e42100d1260b440350351700c0b80384000040c45c00030540c0c5018090480c0ca403019107071404000b004240360010301c02045450000b152640d0300b00d0340c007802c074840c5610358900442d0003031a0320b52483c1d9070a008401c1d07680b610455024005655184d2001c40740391529004003034884c540750482c003411455601700480d070900c100390703904000040f503100d2541100301041c0d11b0413142d0030314002c40804d03035440008135408848600daa01100075941d01d0780c01c0280c0c1045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 390017432 625 390016807 390016811
    0x919060e0315010303050a0908010f090215040605030112020f10080601090510020a060c0912081903 45
    0x2d642000102c050100740303918581d4141d07000d80c88000c900060120351400024014003c0c8155164400d0348100851499940e2040041c1c60b5401e0020420041042c0000c2c001c80d82d021043e64190b031254409041d881c0700600005480000720103120340d110351100300d06c0340c2166000502d203000720000c0c0c03145c03c00300b5214070800c59100c018542e03e50050707200d018680c01280682c2c2103082d5208041c1020440d407919034010074222000e03d001940c01140018410903a00029005100d14078154501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 390018057 625 390017432 390017443
    0x110c0604121e0c080d050411130e060a150906060801240e010f050919060e03 35
    0x308440c540040114503600c0b181d402c20b4605100141410201d80c49032032007100509151400300810001c40c4210315130234140542c1d9010000d9051810a011500100c00c250348562108001842462158200c41585604140c150708403542d55110b5400f51062a008131002c15030386070041c1b00340d01c840404c1d142c56007460241514a804001c1b03001d44001140340b081410000f8441102c14100d020b03204403101d00c600079040000d04007030815420b0004105000c1d9400050014100c0c02051800086 = true := by decide +kernel

theorem S144 : BRFrame.sub P3 P4 TB 1680 MM 255 390018682 625 390018057 390018077
    0x30f15090114040f03030605040e030c06010e0108070b300a0c090b09010f0201110c060412 41
    0x15a000c0015240014009841111060011440382c1000a00c1ca510323940480d04403239820b0943e40c0ca591001070500d120100c00c0010034018000c2948400096040c1100c4a84441d114402c407a880b55000c91401d03c1c019100d6560f0103d513080120004181319600c140305540031055450712060791900c40b90211562240740001c06885c68140707040e141001328001101d4200460030b0702e03000c5568400c540c07441d4000d8407009101c160224030003400746046c282030032510503060345034103c240051142c03 = true := by decide +kernel

theorem S145 : BRFrame.sub P3 P4 TB 1680 MM 255 390019307 625 390018682 390018701
    0x60f09030206031b210f2d040f060515030c01180605030903040302030f150901 36
    0x103082d408003401c030a000d2140074044d40c40c200722680c100d82c4610045d101103841c20418141c0f82a0b41c0e01c0c101d405c2030651842401080306400220b00e011940150710090088070a002581030401040082050300c2000201e030080e00400d040b8070905004201c24502c1441c25440350301818600b4005407225810084da4600c660035410b20700810714140d034458500a903407615445801440d5010329040a50b06000d2208040c08024000803200320391084107a00d010241c0d00c0f045064202d4590b0748 = true := by decide +kernel

theorem S146 : BRFrame.sub P3 P4 TB 1680 MM 255 390019932 625 390019307 390019309
    0x22020f25030f0e0d06060b07020406050d03140708090916120b0a030b0604020403120801060f090302 45
    0x162090040520309080e0360620029800f5540000c0f003070896400030f40c20f0f0154500030030181c4006500c0707082c50310400083e1203154004074000d880c08031044d40840d03840094001003e00080c0a1030f83d0700610f007003e240c14466944101d4106190340709015500303034000c080c3d000e1488103555100c0360121107d008000c1e83e440b10001c590110001e441440800c811035541500808028401440e2503540e0b03490b50100e1a104442c9000f0540c0b140c01040b0a580011088050b03047c20701c0c1c9000e0b503500f50f134 = true := by decide +kernel

theorem S147 : BRFrame.sub P3 P4 TB 1680 MM 255 390020557 625 390019932 390019937
    0xf1d07020a03091a0705010c0503060a090b0f01080426031503190222020f2503 36
    0x9810025a42c00784104020b40041580e2085217025000c00104154280920546106c4e030200107144540002c907000c81240380d6400490003229032407054560800e1038600e81140c1540261800d9030030a124101a2280d00f0142d208807075981e1404162010400e0000207020054000910415904000710b01070401e06c0500c0106d000707c000d2005000b40107517010b900700141d0414103039017000c7c401c8090391305664642e5030003000c8a4031350003108218100342013040c03450081445d42000300c40d407a9054 = true := by decide +kernel

theorem S148 : BRFrame.sub P3 P4 TB 1680 MM 255 390021182 625 390020557 390020567
    0x7081201080f1c020705120f01050415050f0c0a050d0914010c0915050a180f1d07020a03 40
    0x7a01b40660f290041c3e070040500649002c40341c038144250303229800d6410584080c0d800c143c590500c6040c1a010b4041e00340d0041c5007003d028010700305450000c0c43e0344a43c406500800038049100303001e0030101d401c1f81c02060342200a803505256200300d00c600070b100c000c1d01600411842c0c2c0700007455a104075050020011291501801c041522105840d00000605000400350341d40c100420080c2d5060455405008840c07403010350b008000f00d880a201501800c40b1056600a00c4030100082e442 = true := by decide +kernel

theorem S149 : BRFrame.sub P3 P4 TB 1680 MM 255 390021807 625 390021182 390021193
    0xf0a0216140906090a180b0106080a020c0c010c020f030109060b0405090c130207081201080f1c02 44
    0x8103810b04c100c050320081802d8005a0b44401710098004004040280759420110130700784080c0700b29030020b519200090300d0f900c128800c1d103540d00c50200280005140400045031481c2e1841020383c0e004010080c1c0030800d9030244118490359114920125030302039600d040004603070008102c40740a810441c0501695a85c0000b0010170070310707c00c001601c03241c4508104080d4014841d52410301512280042248140040c03002601401401120100d0300c03501420282110a1040c41e80540e026 = true := by decide +kernel

theorem S150 : BRFrame.sub P3 P4 TB 1680 MM 255 390022432 625 390021807 390021811
    0x50a0e04081c020a050418141602010e03070b0f010b03040b1b0f0a02161409 35
    0xd881d49812640103584030241400265450074001d05288002d00e40d00040765030b4162a82e04008403440302480e44429120090700700120b21a00300345005200da001046814200c40e144000d110036809441c00c0400c0055a001c003060071400d0000300c000c51403003014070a101c10800c1e038032401030221600098401408000100000400000707591014904010003110714a0800b00c0d603503940d0040783d00c5110154016000100c0751020000521511006001d4a6515900700c047c5100451044800 = true := by decide +kernel

theorem S151 : BRFrame.sub P3 P4 TB 1680 MM 255 390023057 625 390022432 390022441
    0x108011e020c0304032607060b0f010f090510050c1902031905030403020103050402030a0606030b0a06050a0e 49
    0x111141070882c8000590142c0c04115103074541a0700e0b40300087c00828403007150004ca500c2c1d101141c8501028103800b006441c56049403030400003181c0aa9010081460314070307140400310201e41010303440c011490300c04e1400d00300c048030b007941c1418058814409508041121f040301d10130640f0209604401d54075621b40e00d0240340b000a04140c0c80fa40000c0864801b803040b00c00c620782c002000d00446880b858030011001085800a18003450890f0000c4c051801507440380c101c2d4491520b2861640f00d = true := by decide +kernel

theorem S152 : BRFrame.sub P3 P4 TB 1680 MM 255 390023682 625 390023057 390023063
    0x40b010605040e0c07050a0c0b0705010e03030615030a0603020a0e19231e0108011e020c030403 43
    0x4d035001842d40b00c3c099030840d1424881c986404401c4000c59002c0c04200200082d41c4040240a024541c408042a0059800c514055000c5901c1e000b56940d10b280c28a00000061402c09081d44041e000c2e6802038030720382c1d41d241c4400803080c032940181d5080d000000002c2c5c160b00507204034003400c1155030070205520302c2c03006103038a0790103520f0703010308541c400304c9011590380e01541e44c008081d4005c15a82740041000d401620b2441c40080c80c1c50300d000b5100c1d004010000038000d00000310340459038 = true := by decide +kernel

theorem S153 : BRFrame.sub P3 P4 TB 1680 MM 255 390024307 625 390023682 390023701
    0x70e0f04230108031309020a0903050609070302011b03090b09041401170706211e06090203040b010605040e 48
    0xb001401200f018089e000303080c0250744c04803e0f10f405107018044251107031000c1c8010382c0800d81080c810608409503080c1022800e0381525919092810414240b407070760000303004150019500c07910052100c5402c90018000c181407800c8600c05441c01c3e000c142042c50550100040c0070b100b40076030511000c00101d481d056558100700265400e101c0304d280200300c017150030502d546441c00c080402e0480780354004520542c010710421740180da07114021030381442980304100840505001040e0f1041 = true := by decide +kernel

theorem S154 : BRFrame.sub P3 P4 TB 1680 MM 255 390024932 625 390024307 390024311
    0x14010c021005120916140618030304080a0506040309050f09070e0f04230108031309 38
    0x40341c550310107000c0c040c80000c0c011a19880503501c51058200074140e1140818180014518507400000030015104c0c0d000e50755840c0e10b0221001222059541c00c0b00401c1000040d25521540d049110203020b05c0030f2440030000005642400745109480700c101e9140c80d80d05120542d90410b080c00c0c2c1c8846e6400104140c40e004064401c41c2c42e0700582040340c0703401d549004c2020b030741c89500045110b403142d2891900120502e034038540034000070005140303020040c199242014469018119003d5 = true := by decide +kernel

theorem S155 : BRFrame.sub P3 P4 TB 1680 MM 255 390025557 625 390024932 390024949
    0x6030c03081c0c031d0706020d20030f0702040f0501032105042c0114010c02 35
    0x602d2459000d02c406645220207455481c0883c1010b030740354168401c02c52540c8440240441004288141c0c1e0786000f107108040059002514410032284910001e021102c08160200c0150791b10034071076070440c1c112044154400b2400310320f420a5103407902071440809079003401041030b54116110890030320820f604042c80603014800d10520325200b0821600104480c044609180c0340442c070640030044000504090030028000125004402203110140c0103c16140c41c040c0141d20350901801e070 = true := by decide +kernel

theorem S156 : BRFrame.sub P3 P4 TB 1680 MM 255 390026182 625 390025557 390025567
    0x3091214090d030e06121e130b06030312040803060907091d180319110106030c0308 38
    0x60081c54413404500b14140801c40c00e9010013040748458400c00c0400110041c0340d884000e52125050405145050138500c2c048900c0300001e004020111101c0043e04c9618100240c03080c00740b411080c2905401c1034105107559a00c2030f05d0b2140180300c120700040006000d11129800c0b192000c0c00c0c040004c1c03000794103844581c00640041903510301c8020816005200b04003900406005070b40c030880b601035440c0c01900b00c0300e5986880450381d0401e4030420104840300e07200c00450350000700c410b40d51 = true := by decide +kernel

theorem S157 : BRFrame.sub P3 P4 TB 1680 MM 255 390026807 625 390026182 390026209
    0xa030933020f0c060411100203030108030a0c02040204090203040f0c0807030809040f0e0a030309121409 47
    0x28070b00b402510021030025080b80c46a140a1502074007041510312400d016040f004a9841228004810769040c1c440c80801107003402c070400d00480b105080b041c416a0056401c04c0086a80290380c0015032241d0300944100020a40740e00d489001c000d5560300c00d031602d80008101f4800500e482b400c0304d102c9a000c8a0204040c00060300150041c099003914542602c1030304508020550190861100d03280100f4420b1940141e00c003040e50310558070040c80302240d10401c505c1c40e540ca0250f1242442 = true := by decide +kernel

theorem S158 : BRFrame.sub P3 P4 TB 1680 MM 255 390027432 625 390026807 390026827
    0x108061e04061d011e0e16031409070503121306140f0a03093302 30
    0x16164080001c041c154030100c1900300e1a12000c089070f640c1492910348800c40003050046428800900030441020608921604185c045900300040f07241d07858150003422580b1880e12044103540c00b001502c2c0e41c045036940c00e035242141a81c07140d01e6809416a19401164407081c900c90300048108091409080c87d40c2c0241040c0d070f1a9420285401807400182d0030210107a00802c4e1134226203800c0040c0079072100c0c0c244034812900003211500d00b40010000720904640040c40390b0000d101850 = true := by decide +kernel

theorem S159 : BRFrame.sub P3 P4 TB 1680 MM 255 390028057 625 390027432 390027439
    0x5060405010509060f1b0f0c010512040501110a0e09130803180a0b0406020304060b0108061e 42
    0x603000380008005001c4000c54510554000c486c0e104030a0a825800d544c1002c1d06a2002a200c14540c0c03e41804600200300c00d1068031984045258401e011b4000020445040c1d60b0b08071050380484280000a803901c0d51118076480c141c180c02d074200500c1e5801807035241c15661400b0f104c0c08002c002001119107a0a00d0340350301c1c804c1c00f01140079984041ca5000381d1404bc98050020741080d40c0035640213103040355511031940940906402200e00528025042d4001c0642c01856035881500540 = true := by decide +kernel

theorem S160 : BRFrame.sub P3 P4 TB 1680 MM 255 390028682 625 390028057 390028069
    0x2010c080f0709050909101b1b0c051201090b060306131203110a02030a020706080105060405010509 45
    0x40c0c2d644d20045500180b00b61429109a0030245501c580a01980a100d031401c104a101800b00258454014034041c09044220852a0099900300c28040300004404c0a41001410074444a07aa00c1d00700b802450911411901c910044001a03d540f9020a08034440c0da54030221442c45082550b07618842111920401c09040e0788000c02005101c1000c0030301034440041e002141c0c1d0b80d00c0140040c0c54004254408020410402c0060103561561802d46040b100300f801e00c43d840700125400951 = true := by decide +kernel

theorem S161 : BRFrame.sub P3 P4 TB 1680 MM 255 390029307 625 390028682 390028697
    0x60d0f021206070c11030604171812100c0206150402030c251202010c080f07 35
    0x404800c4100319800c509007100000c00d020314420741a240c01e440c60450041d240b401044840c008da820560341d41040032440496035050707001002e444103070001b00003241c03001d80f1554246c01007030140d41c001e400c04000d0400814160341c8001d0750b043c00c54000c1810415220300c00e54480000d0310065800503180e66600380d1401251180302a103190720041d194130481540f958040c161503040c813440010840c4985103100340d007615189890400407901c41000a4000800d0341c2d24140c1c40801460040c1 = true := by decide +kernel

theorem S162 : BRFrame.sub P3 P4 TB 1680 MM 255 390029932 625 390029307 390029329
    0x30b0f07050f18030f07060509120c131e0501030209151201060e09010f05060d0f02 38
    0x2603040081003d0b240185250b080307416800700f41420145095140c401c80c86043d005088100003a50b080303400c07200c4c0c4074000e0310801c100048500c49141000384400c01d141c0c001c0c03000710010000310055844040a5100d48a51441c03003c0d03c915020201e9209003c002e4004040f0030100d9411340c88851303407058072031004041c2481500000c030700c1825506940d1100c6172481d49003091010300030082c011008840b003a410b0400c054605040001c41400e03482c0000f0b054004200c41a000b507440b040381040b = true := by decide +kernel

theorem S163 : BRFrame.sub P3 P4 TB 1680 MM 255 390030557 625 390029932 390029947
    0x30504050a090905010b010203030c071407030209040f030f0f080a0f1b020109020a050406030b0f0705 46
    0x41d1010840d000820715405503845001c4940c4507034020420440b2200c0161384900040f2181400d0a905220500100e416020000012031208040e103403403948950000307000c0c09095406603074419a211607a0105500440004410442c80c10718800f02510720300000d03e849001820616810344449042c010701c0200d42003075a18032011401e01e1030b18140108001c0c020302264000383c1c8212188100001e4500b8244101001e4035004034810040d5519949480d05546028081008001003042080b = true := by decide +kernel

theorem S164 : BRFrame.sub P3 P4 TB 1680 MM 255 390031182 625 390030557 390030559
    0xc0204020f120f0c0a0e21122701020a0b06030316050f01050603060105090703050403050405 42
    0x203035903a000d601e0681900b0a400100314112100300e001e0395011002c000403502c1c05400c260010010071009001d00e216461032044090419441c00e1880300c408050350403580c1611014074401380980044d60030302c14000c1c41010030000c1c00d041c84120010440181c00800800000b581d13401c01340c1c64010543c40d05848144043c2d4910100c54050b10051030186010700300da003064000c13190030b40360010314042c002e03449440100a42c1e200c20002c01c5c0d00410510780000c4680701d0f850112082e12a545c411 = true := by decide +kernel

theorem S165 : BRFrame.sub P3 P4 TB 1680 MM 255 390031807 625 390031182 390031207
    0x20d030219060516030905071e170304050a050103182604080106150c0b070c020402 38
    0x1a003040c00a04100c03020300001c8901540c0003c46131801035926020b0702c0740b03410700d81d04040180302150810b02920201e18030410f0f405107200c620600004c6600d006000c0c50000060300020b10f440714600000d100d55a4202c0d000b9905040c00d0648130380c10744002e02442b462054102c80e01140304403610640c003481c0250031410031908000003030b000c00ca20805411000c00c56001ca061158440f840d850b003110002101200100104041c1003c0340043d449080047d181500044c0b006150100074100c0c03 = true := by decide +kernel

theorem S166 : BRFrame.sub P3 P4 TB 1680 MM 255 390032432 625 390031807 390031843
    0x1050a0e0603090c100e0108010b4e1e0f1306090219150c0b04020d0302 33
    0x3025a00d036161a003002d000d06d00800180415030580190500c50000c00c8280111034583c400d0455080204034002d650f00c500301c00381911041d800700c081007940e02c0e11043c1e00c1009030788110184625100c41c16032900940213a0004501841500c44a1420702100f01040081c4648020420003034081c101c082000c4005a01180c281654858480c86034a0f0301c42003801a1036180c20b4070b058a040f0703840c0003021200703507890b0580c0040010f071000340304004040000e0200360080c8007042141d1b4940c510 = true := by decide +kernel

theorem S167 : BRFrame.sub P3 P4 TB 1680 MM 255 390033057 625 390032432 390032449
    0x130f0602090301020c1c0810060e0a18050a050c0313080313020604030b04050c01050a0e0603090c 44
    0x5469174002175020030400c40701c91410394024600d00e0480d12840f0865000d1042034141000300a020702418030100c4100c401800d003050b1a40307840b1071710051404d00d80c207210340c42c2d1143c0c10b1045c590450300c10030b50403440d2555464507601e0004070303410409007d144001c0403804008005081104030054020101c1c0d80206075999031a0781e8201901060030599058480d070164294010540d070140044a1200741079859000101450300c2c01c02c1100e0700000c121001e1800381001c1d000d01035031074820 = true := by decide +kernel

theorem S168 : BRFrame.sub P3 P4 TB 1680 MM 255 390033682 625 390033057 390033067
    0xe0907081b22050102010612030801050402090a0305011b0f021501120c0e100504050c03130f060209030102 48
    0x64148801c1225003c2c00103590a015040080650341181c40324541c5c01c0c3d5014114902c1406558050355010809442a68038a05242c00070360b0090002c001d000c100c04d02c0107401a44161310440852030b10740d03101c1221417000070304250128011190210760b908208501c2d00e4501d0440058070752201e503040c081078080c03c40303414a000f601c41d070914148032881c00d414032095401c003e00d0324941d05000c2c010052001000050301c0070150340583c400003a0016450114006d01404080035015880454 = true := by decide +kernel

theorem S169 : BRFrame.sub P3 P4 TB 1680 MM 255 390034307 625 390033682 390033727
    0x3022101020f0301032301050f01122301020a020c19050904210f0e0907081b 35
    0x4162132800e40005d059141d80c10a6903c1b8401ea014466640719010411104000e64a03040030809140e8000300c00f81d42d17000019030012014107445c8080c1c596100008001130307403015a0200281030281c005030145c803401c0c205101d0321203c250240d031503099076801c8034140640c3d119481c20203003000801446010201c89440d081e882c0d15009803a00c41c02400310348603945401040c0d0200310990308120f80d0840416078120100e142240581003800144810710803030f40c94a081246001003180300000c = true := by decide +kernel

theorem S170 : BRFrame.sub P3 P4 TB 1680 MM 255 390034932 625 390034307 390034313
    0x1b053f01030c06020c060702010e1504062609190501140a06090506010903022101020f030103 42
    0x61100035031460529910042d040c0e03211034259080490605525100c4000300e400054080c20000c010b540f100700801c03582d820300c082d0301c9981c0d540405c0c045000c82d80516030080c00031030041850302c50308002c5000c40328408290b501c521194440011840c00d207282c81d02400c41240920000505d150146884080c0e00310107c54041c585ca13941c0320b080c0092002c902c03031507800c400d003840e00e452000d0841d40803c00802c0f50000703d00030121603401600014400350110340e01c2d940d007075640586950303480c5 = true := by decide +kernel

theorem S171 : BRFrame.sub P3 P4 TB 1680 MM 255 390035557 625 390034932 390035047
    0xf021032070c0b04210206120c0f1b072405030402030307061a041b05 32
    0x1005000f030340c51300c980c8650b6441d40354240c03058a105d4402c1c025003080b01044805a504c4442d0103482d08200750f4043c0f9894034000304a4045540c0081350980105800c0740c4240d04141010468030006080c0c241000c5030120440201e2001d14201c0a412000d00000100103411560140115400700782e006c44100704d41c0c103500c480c182e2040c1c1c55480042c003e901c0e204010070f0071310b080a442184421541d88032441e2140008120f100c4a849400311070b20019200c0c020142d05007075045030000f100c1441d = true := by decide +kernel

theorem S172 : BRFrame.sub P3 P4 TB 1680 MM 255 390036182 625 390035557 390035579
    0x10c081e04241b0c0c0e0a02090a0807080d1403150d060203040f021032070c 35
    0x8075140040f1020b600d41102c20050f0340742c001c2069420f03a4400c00446528030408011302c5a00d0003081c10010707281c1c101c45a19000515052142b6680c120050b1208550f00c601c90b564060180000e42c140c0c021040c40240d214200510b500e56500c42205d2100da050f110803464220a00146990000d015440118010780c01003020031110303d000d104020300c0c0603541140204024480c030044621100144c100d5032407118402c0d00b10148001f02c15680250300038581c015000908500b40051000310700 = true := by decide +kernel

theorem S173 : BRFrame.sub P3 P4 TB 1680 MM 255 390036807 625 390036182 390036191
    0x30b0c0f120603011503020310020a090305070e0f10080d0e030a0c0e0702010c081e0424 40
    0x10321800d10039405c0c079038042d0313694002e0741d0b824040c0d1b43c004014103210b50000c00700704000e40c015074481050264140300000811000d0250030000c00b00c0c0c008000051414a1203001074260060202d05d0107280d2800c00d01503140001411004c0040c00e00304000440c072a0000249000c0700104020000c66000c1e03004140151607a9540b030007401c81b6002404071082414043d1900c2d0800c840140103549100741a003d00707107210300328a41040c0684c40e10303e617100c07400031450060110f000303070044060b486 = true := by decide +kernel

theorem S174 : BRFrame.sub P3 P4 TB 1680 MM 255 390037432 625 390036807 390036811
    0xa0203010e0a2d0f0b1f030b030c06030705031005040207020105090111070b0c0102041815030b0c0f12 46
    0x4040a8044400c17805c0c1461041c04c2c1c6100d0300c2c2000c0e40c0c2c500c96000540581c00c0c0090390300c080101003070810308601d444c0c035400f000000c200004550040046c50144206000110f103203910b50b020311040344a440c070003a003c0762041c89400300640c0f013034242251901c00f002c107440341c02c2c0c0e640c07003140101d800c04000e110a507500450140070b00011814a1146440b4100301445450390602d0358241e030100c81c1c007015001d0503201002603260801d00c000c41c1ca04c94084a80e0680d10b140a20540443c0784003 = true := by decide +kernel

theorem S175 : BRFrame.sub P3 P4 TB 1680 MM 255 390038057 625 390037432 390037451
    0x6040e0102130614041409041403040f060915080f060a170606090a0203010e0a2d 37
    0x203481da001e88003000c01d0f501c01a4040d41c42002400d0115200418847c6005942e0990051042203c1501c0100d4070740d05500d940c010327800c0003241c8022170109000198000c6080030041c11071281c1d8001a6010750700c0205070b060003400000389000800040780681e0b41d880003120103001c61030210008080c00a1500b903980340c00b501c0d0b450103640f0b0781c8049110000c4500031a810388601d115000c030309440f9482d1140040200c410080309042014894168240b00d0601a140051201c400420307620003 = true := by decide +kernel

theorem S176 : BRFrame.sub P3 P4 TB 1680 MM 255 390038682 625 390038057 390038069
    0x2040203090c032d01062103090e040b0a05010501110d030b0d02030a060b032506030506040e010213 45
    0x84001580454082c070001c00c101802e0a9000340419221800c1031003840a0241f40070406000e0300600c006042c0f0340d100c1e10002e03e4940b500c400c41810480d81020144e0404000007803550194031038840c01503102018141d80d082c103100440c001e1002550707044d40b105041e00b4403400340e28144a07400c076243c040e0b60f011440c1c82c8820103251400000c607100c0c912103009501000791043c8101100c0094a1403031401003542d0302c1e0900047e02078400d0119500700f551001401c480340b03591100c00d00f000c88a07 = true := by decide +kernel

theorem S177 : BRFrame.sub P3 P4 TB 1680 MM 255 390039307 625 390038682 390038743
    0x10209011b0f0821100305010c092702160f0b1008030702040203090c03 33
    0x70340308003100080710003490400566226000d040c20041d03644612103a600161156082c000780352018800f2207640c0880640601c11820042000f1415440d0060135503d082c3c60001c20409211010080a0354420b03260ba521040c3c00d41e41801008811660400780c442e196009070040c09540108081018501c4d00c40a5903008054885040d25445c014980001a51040c0d1380f41d40c0c000d10600e0054a42640155044130310b520880382c2d80114200864100700344503500b560420310030080203035110b9 = true := by decide +kernel

theorem S178 : BRFrame.sub P3 P4 TB 1680 MM 255 390039932 625 390039307 390039317
    0x100e28140c0d150e0c0a0306050c130b091503070e09100308030705040602100209060702040f0b1201020901 48
    0x2684c280100703e980c81341c0d070702c803149554001005003901d40c44580401c2548034840e450040303002c0c01040f559202c03140b00c400710399141c2c3d4101401c1c060004444000c0c4104001d00035035002d101c00e44003136001030080c1d0300b0400e0302e0030f20480280c1c201d040c00d03450308411540c9403a686c082c0d4006540803c0029030009040020030ba04000100308100250411440d1950400c0002c07014800e040e4000c0c02541c4030300d041501100f0f540d0012030a1100600b101700c440300305a07985c900039800301c2407150206e0 = true := by decide +kernel

theorem S179 : BRFrame.sub P3 P4 TB 1680 MM 255 390040557 625 390039932 390039941
    0x16120308060d051507091d04060507090e010b09030c03100e28140c0d15 33
    0x2a481d02441415111944010f01a602ca100600900c0002da0071490f401038041ca406168250f0710042081c00300070302d464400c0d2030101c450510040c4412030194950200e060304100e03114030f14000102500340381c1407190710b4652001003400c1c611690f0500002c4c0c50488c0081c210391195501c000e04000410402c400044984030b40c201e04540b020b41e850060800031103110140d451112103880700c2821441e00080d207040350203500300c0d845040c0d55100650f0003e90044940d110000031204501e4207d5 = true := by decide +kernel

theorem S180 : BRFrame.sub P3 P4 TB 1680 MM 255 390041182 625 390040557 390040561
    0xa022506050105090c0a2c100203030105010201140c16021507051f0e0c0f0316120308 39
    0x1c0b20305e101c581000200200208150000c0304443d03160071349000740280c003545200d001c900d0707020060000c200d03d112900010f940ea034001e1050784d00661800744428410b48182c550540544003034a4840c3c07800386a03204040172215040300070b90b888040914400700c040c00500050140d90701c00c0d40603021511003101046a0300300311461050700c0070b00b08060075092500c04200000c0a07441202e0400100140101091401031200012014840b400e40c002c00e4250380808401c004030b110380c1d01d4845035 = true := by decide +kernel

theorem S181 : BRFrame.sub P3 P4 TB 1680 MM 255 390041807 625 390041182 390041191
    0x106050103060f05040b03010b1005250b01050d1b0b07030206100e0a02250605010509 39
    0xd84039000b280225060703e10303810700d86410700003800f010b412a0115103070151b4803034103084a1500d601042c501a441155541902c03956103011072880556800703514a003160920041c200412650b202e07140c110792040301d5071068009a45406020f4404060a00e414812103840c0010f01c4036a14000b4510a0310070307401d40310070356180c1c100401c02c207416014000303d1200440000c0c86e089d600e9401000b0801e60340f45c44140e100314100c0c0e1620034920285085504c0303134a440040002d401c0404846822 = true := by decide +kernel

theorem S182 : BRFrame.sub P3 P4 TB 1680 MM 255 390042432 625 390041807 390041809
    0x92106060e0609041b08010608070906050a0810020a0e101e030203060d020d151d010605 40
    0x540c07000c200709582c1c64000750346410039406050f0f2001c0d5030001d502000000d0a90700100c40365424000f00040c1040001072140c26946100010855603903a5001c20510724428800d92610340c10146403555840c1050f4040c3c0708119250409200b41301d031145c0094804880344c1e9240d4040b40f0303803039460540c82c4117903000b4003000c1c0014281186582003000c0004c0ca8400002c000a2041114030452810450f0120b240d0b20a14411201400300640503500d4407100103a0625045556181010000303503 = true := by decide +kernel

theorem S183 : BRFrame.sub P3 P4 TB 1680 MM 255 390043057 625 390042432 390042449
    0x3050c120402011805030105010b09180c2703030c01050f060307180b0109210606 37
    0x38866844902003290004011070019071040c8840c1d0041d0000742404019030b500c800010b1308590b002ea00070500700313200181a180b14241814845072034182481e502d1443d24107082d07005000d20507021510424103401030041c110080964841c0b000c0b42d00601201e03260402424814020b140540b05150f80c09100e40014005150003d000030075256120314107641504219a50000340c0381e117001031418086900c074080f40300406e10518503c50f40091500c0320f25503840d07040840c216005034104020 = true := by decide +kernel

theorem S184 : BRFrame.sub P3 P4 TB 1680 MM 255 390043682 625 390043057 390043081
    0x1020d08071b03170a06030512071103150f070305011410170a050105180402060306010f09030f11010305 47
    0x8241f960f151036541d04003010382285800000a003560411144d1402005e520704044c0c00c0d2081407000c0b92900c1d40510341110b941858090301760004a200b841f1340b00d00d13070584504551420b0000c3d030f688140300543c000c90f0b807103074240600036072042c99000c2f54640051140000d941d000c1170940c103202c14072085d44030300361024a03140c0b40d900038003006940310070640b54001c00a2900e0040c1d4122a001200c0c40d01c8e25900c05007407030391409200014040020f01c00c1e40303064001e0300c007480300d0344510544400d = true := by decide +kernel

theorem S185 : BRFrame.sub P3 P4 TB 1680 MM 255 390044307 625 390043682 390043691
    0x140c030622031101020c03160b010e070c02190506030c04140d0201020d08071b03170a 39
    0x114400c1c101d4400310740229036020703a10082c03260002101558280040b006a007414030090510310300041908800010901c0d150300c070365006801c401038845481742005441900300d5143c0c0341c401e030103c3c2c01000303e407480040e520070300300281c008940100b800303c2030062459a1a018105440341c3e0403600e9140c0c1005824480c46034404038021340103a200d80300c0144080d02a40d03145030404114608035550120444d804207007010204030481c00220205002000c5001a862044d04411100c60521 = true := by decide +kernel

theorem S186 : BRFrame.sub P3 P4 TB 1680 MM 255 390044932 625 390044307 390044341
    0x130b160e060706151505040b0315130501061b1a060102031b0c0f0d05031c09140c0306 39
    0x40c6146c0000c260b60443d90040d50031540c07659002c14020380600d0180c9690380c000485030341c2040e079001175886141a140b26843c1c001c0f04510700d843c83c462078904840002c045040d2007440d24643c401d85485d0b990000c0040c01140d0414502c0b00300a101d0b00d9000c00610201e41c04131441c06078610b04010302030030303030355040d1520340c0002416140d01d40c40e40701c0c0c401c107005410001c12000982c104a9804140c3c45031700110941d84c130b2014183c0341501c511013103176a9403091046c01d01081c200341540407901 = true := by decide +kernel

theorem S187 : BRFrame.sub P3 P4 TB 1680 MM 255 390045557 625 390044932 390044969
    0x11406031905100806010f031a040f081309090b01030b130b160e06070615 34
    0x7180380401c02481c0300c544501d5118940200f20000c00c0000103850703401c068035010080c2c00281c10409603110810411a520810502c1c0c00b28040306100305051569031000f007180f07000001024070138085596002110030f04800c50041188400a00c00010b040c10441094802030206441c40303e5020002007485c201540c489000355440040c102569445d922654601c0d601c0c018807000b042a4040c2090b001d03503901001d401030034050100020326190900700c018174400700703500c8860380300071610010 = true := by decide +kernel

theorem S188 : BRFrame.sub P3 P4 TB 1680 MM 255 390046182 625 390045557 390045571
    0xc0f060203030723130501030b0f24070f08041a0408030d18150501140603 34
    0x1e56a00000b0400e0041c400c5261014503081540a940d00c01c840c48007060f180d45e052414074803071005400d84103441c0880e0402c02185041d29000320410301049010701b190000c98081c003205d5100044068003c280000100f00340804680c0090364811100e015519290380c40b071400c1c0800b5400c82000c1560349180b002400f003880710100210840b0182c1c0440304c1c0105000f070304810059600450643d00502c000c0016000100e001e00b190441070488002210070841402d0b00002e1120501c02100c4134 = true := by decide +kernel

theorem S189 : BRFrame.sub P3 P4 TB 1680 MM 255 390046807 625 390046182 390046187
    0xa03140c04060521010605060c0c09091914030409140106080f04020a06030e010e030406020a0c0f06 45
    0x1411004c1458100d07050120400404005540300e40d4001865181d0b00040c11920301c00c0c0011308046082c8806202e880040240038000b81e0340102081c60602038003103428400140c12501249240204190440c03075841240c5c000f6498902d05211892482a44621281aa0071031303078810001c1d407140c0c20700400e01103064034080d40c019002e040401c4018000d50050045103580720000c80c4400081c0c0a560454200f9031012001d40c00000082c420080075486800280110006a0305001e0412200 = true := by decide +kernel

theorem S190 : BRFrame.sub P3 P4 TB 1680 MM 255 390047432 625 390046807 390046819
    0x20c06042a2103030f020a03050a0e0a1e0c0510020115050409030c0f060b0a03140c040605 41
    0x80b00041d100c2a0101c000d00c035860181c2c0913092468904540c00d20100700d090b1800c0c0c0c1600158010a82e49100f00101d81c3d88200d41c503241c500100c00070b00f8510b01c4004810144108141c40300c04140900c00d103060300d035200c100150f06012200c0c540c0380180c1d140c50641c441c20074041844801800c0c00c540400000c8074656019010084440c40540b2008130703480c100051010507000f60140c0e110003058410159141d02d031107103012a01342d074140020321a182d031400d09401c00744502015103e0003080 = true := by decide +kernel

theorem S191 : BRFrame.sub P3 P4 TB 1680 MM 255 390048057 625 390047432 390047459
    0x15051b16180c05160204200a020705030102120402040b012304060809010c081603020c06042a 42
    0xb4440c2c804d140c3c81c07401100c0f0700040000c110307180082c8600000000d210080700c0e040c7c8000521500f21901041103000405094008501e4420301303c007050680c200c007500007441903884107444041c0c0e80c8941000f100c14002c41c0c0702150849280ca40c0c2c050036610502c640004140800b0000700100e01c10701c150044401503442d072100e6951000300001002c02c445031210b003419401d008400904008008480c4281c0c4280020305101c0c854070240c42c0004200414010b40c008c04510900689814064 = true := by decide +kernel

theorem S192 : BRFrame.sub P3 P4 TB 1680 MM 255 390048682 625 390048057 390048067
    0xf08060f010306050613062607051c0302010f06090203090c040615051b16180c05 37
    0x508100d40c2c0340003091546e207401b12407a0b01560b08090510901e40ea9960032031014400041c0c5044140880007040310b1000e02240900484100500b00d0038021a540e0014000d16084e10080b403e42d9640c0b181034035590514040c0c0001400101001038681c540074182c50700701000d005130702d481107180c440709200e034510500e00c1d4024800d0b0b2b0b14206845a0000b10a030f00c188500181d0f40c095072047c0121800003080c410100c005407050340034080c6002000710107040a40b10440c0070400030031000d00c0 = true := by decide +kernel

theorem S193 : BRFrame.sub P3 P4 TB 1680 MM 255 390049307 625 390048682 390048689
    0x70218010605120916090501090515060403030e1804030c21090608061306030506010f08060f01 43
    0x58000001c60103404d00019200703504401c0c8030101c40074a00009000000c80c0400d0651500c500300c8160b03071000c0e005040003004610bd10503296500300c100c07002c4070360600f0417021541240000410580320030f0500e10b0108036400812007003551207024240010b2183d0041081d03038100600c1c0304100c00c1a4070b030810200f02060b500303024880c091031219a00c160018120351100e4860198002540d0702a401240c01e03500402c0148400c41e120b860417805821164020400703890140303a4403241c61418030 = true := by decide +kernel

theorem S194 : BRFrame.sub P3 P4 TB 1680 MM 255 390049932 625 390049307 390049327
    0xf1006060c051e101b26160329011b110d050a080a0302070218010605 32
    0x301a03580814580807403e2113400c6550b4072080381044088441a0300300501901482e12544402028400000c100a450b002d0349005040704640c15001560b060003e110000e0a0a02413030300044100d00041d80a1500d06480d542503510001c1d20707011401560415020700d5a01326800981130940c40654419130f8050074102d041d13018140f805003c3c4100b00040010008042d0300417030303446d00c548270120000d000390403e05090788940c108176071010464600d40c4030070b410703203200796141e81c54a072500d4 = true := by decide +kernel

theorem S195 : BRFrame.sub P3 P4 TB 1680 MM 255 390050557 625 390049932 390049963
    0x40c08150d0f080406020d1b030915050909010f06020d08091513050f1006060c05 37
    0x1110700c140340100c0d03103074601424aa0710002c040c0d0050340003a015801040a00780c0103a0828940c02d500102a03c00040c07840b281d6800811030009400f8005884042100100080d4824004c1c1c80503024080c01c0d9600e1540c40c0c1180600103101481400700520800104070046031061550900a43c0120014581c07840d8107043e2087c0780c4402050a40d040300014507200110303004001d100120300710075000e400d104100c4000c0e174094034910303040b40c820302908100c40000160000380d850490100d11 = true := by decide +kernel

theorem S196 : BRFrame.sub P3 P4 TB 1680 MM 255 390051182 625 390050557 390050569
    0x3050c0a0c02040b0612150402030f060d050708160f0801021810022a040c0815 36
    0x907a03403811500e031074010900c1c80c04004c0c401a2500390800d54a41020412144000e0380304031040a48898a81442a20b0003151025142c5c066a9240030602248210340081a511441094030019804004101041d1208200c2c07403003000851a0100c0d195440c019500494a02c0c0d0061200d110b445201742c0510b00210011580300e00002c5d04100141c1c01d0580820748803030100b400000346a4140002c1004c890078940c25502041005031011040390020300c243e41a2070303600b10840300c00c00307989405 = true := by decide +kernel

theorem S197 : BRFrame.sub P3 P4 TB 1680 MM 255 390051807 625 390051182 390051197
    0xd05071a09030c070e07080612060615040b0a0e090603011e02030c04090606020a021003050c0a 43
    0x80007081c0a000800c0402032115081c0303c80e901038034035040c6104d07807030410420090400fa40101401d00803070264250700300c01d040004405034484011204c4943c01c2141d2081007140d8002c1d5031140351f07800800318681840641000e14104486829a4607082a40c1d41c10308040c01e940600c0c550420300201c2c444415071602c0d41e034000390350060101000d146460b9581d0030440c225811940b00c04016084006218118039000706000380c00d0000345418043c1d4204080e80c210b0b50f11580512000f4007101 = true := by decide +kernel

theorem S198 : BRFrame.sub P3 P4 TB 1680 MM 255 390052432 625 390051807 390051811
    0x5011e0f230901080106021908030601030b041805060903030103171308010903110d05071a 41
    0xc0c0d4050720101c203204a2054600480d01c201c076403020124000708a03041003620740054503a0fa0320000c036a500e4804900041c42d5005d445002c0021f0003100185420100505000c50006541342c04502280c010519210540111018240030300c80c09201058002140001039869903045071207a407080136480c90950720741354001800c811442c00d6456080051b003400402444001d0003400e004002c1106000114618041c109144140600540c01c5413a00303540141c1040c14580b14000c090312510b00 = true := by decide +kernel

theorem S199 : BRFrame.sub P3 P4 TB 1680 MM 255 390053057 625 390052432 390052457
    0x5070303180309080d0e01090b0a0c0b010f03021c0506010302220504110a05011e 37
    0x190400142198252070250300d05029100300300c00103002030b403080c0a07070403092042a6154110742130050045201000182182c54107018401c00d5182c0032500b017117020710521500c40280c3d000719010b1f00d256110071585941801d1400b0983c0603552008540180e9000ca10381c6515054201d0090600c903401c3d54200200c90601c050002d5041004201c0b0342d88000382423090f91300407449040d5581800310302109001200000740e200505000300c0500b14140841e9001000d01003011510b03102c0581c655 = true := by decide +kernel

theorem S200 : BRFrame.sub P3 P4 TB 1680 MM 255 390053682 625 390053057 390053063
    0xa15051606060b1c0f050105100e1311180303120103120908030c0c0102010e03190507 39
    0xa0b900070101400c0b95110160b16181810010314010302c20404841c4854100b1007401c401044a2252604a400c01442d16000b0460403606a440740c400c0d590b4140c00060072401209800f0071801840318058050b0121941c5080e884044503031402010052031281d002004080814140811110305481d00700008030704101440209681c050721789d9109030034901000c1000c2c0e02c0104041181081e060084c0c0081c0b081006500c0d1068a9124516a145500c0c0c0b4030521620024480c01c050455284 = true := by decide +kernel

theorem S201 : BRFrame.sub P3 P4 TB 1680 MM 255 390054307 625 390053682 390053693
    0x807030608010e0a0212030406020304050402091c0507050a170c2b080304020a150516 39
    0x120600440c5070542802026055100400108038115142c01081042c1002240300c0c0380a400070001404104d6001c002c450a0b0362060302e015954000c0348020420403114030511242240100d40c81d507080040100310207049400c102d5941980649801d401c0700440060070002c1680c2d405020001200d0a04044d214900f03180c054480b0300d413043c40303240c411119182040480301d011000040108500e002e01c400c40181082403000c030fa00c0041c41d140035040f84035110042d0315103010b94251004004 = true := by decide +kernel

theorem S202 : BRFrame.sub P3 P4 TB 1680 MM 255 390054932 625 390054307 390054311
    0x5071716030201240503030409022505070914060904020906060904090b011a0304050706080703 43
    0x500032401082244400c1814203141d0103600c01141540e0030f1020098112010344039080628480c8501a0183e004200401107890384c1ea01a101c91400c03a5000900001000382c840c00c041d10161041c0e91640186404005a213554801c448085c20b845004200b64945803000421948008002074003500f035100008190f0ba503400d003181d041c500001c0c000c010320040d41c1400140480700f4000d403400d01c3c11840603d07038400e04603810b0360301c181c0d4084002c1a00b40d04107d41204c20720b00c00303030421040c15 = true := by decide +kernel

theorem S203 : BRFrame.sub P3 P4 TB 1680 MM 255 390055557 625 390054932 390054937
    0x6030c0a0303301d0a08160510140901050a0902010203031315060305032206050717 38
    0xc15183c0316005000741c2804141d0058445200342c00c80f160b190b035440e807030124400c0503110032038203135440c1a180d03c02c0d888001a01c01e0b82c0401c1d0000c0c00300501c218034034101d05070313000c1108034805000035102c0c1004581e40c0406505e07220000e0b1680c0042c0c041c942e1039030f5050303020758550f5940d5907414100006440d4151070306580c1a101942490091003680080c6000300d00640c4c0b11581e1b00000c8808c0a40f81070140504110200c0410900c2d400000341c442e07407940200e400741a003884100c400143d0 = true := by decide +kernel

theorem S204 : BRFrame.sub P3 P4 TB 1680 MM 255 390056182 625 390055557 390055607
    0xc0a0f121b2006160f05100b2103041502010b01030b0a061209150c080a0506030c0a0303 40
    0x21841d02618030304655400c1051445c1c80d00c0074116103c0c05200c1d0800b25001c2c082c01800d4502c1002400c1c00c80709030007071100d405114126005221180000d020016480144d0000344000180980010840c0c10111000400726402c0502161103002c0c170090034400940c1c03152850400e20111000011401550b0801c2448559440c0f0501c034007600340110491441d034410141c3e0701410043d84140025103036070041540307441c4840354083e0001c410300000c06c0401c1c42912001842e41c240e81905040c0 = true := by decide +kernel

theorem S205 : BRFrame.sub P3 P4 TB 1680 MM 255 390056807 625 390056182 390056197
    0x314060f0a091a120c030d170118020909480c0a0f121b2006 28
    0x6139441c075009a522607a076009107840c0b0b030050101030500444c0c01059080c460040100c402c0a95820221411200600b00003042c5203002d40c4041c1c064412181030652101903d0b04026a54003c0c016030940865001c400c40e07140001613484a203d4030045070b440d8403c8480d00d140749020012000105030081980003034841891007640c41c4400b440140d4030071110304000c8000c01d211687c0c003503003855111050005000005c0550f0711003041407040100101c620300c030045240036850319203008803080c5 = true := by decide +kernel

theorem S206 : BRFrame.sub P3 P4 TB 1680 MM 255 390057432 625 390056807 390056809
    0x21023705010207080703090905010e07080c07020d06060513020309061b040e070314060f0a091a 43
    0x9510010f41d000820001c000203005e0f0600c2a124510250358030340010003250024031a90f99140c01d1600041c82851145400b185d01610603e002802c145060b000b145585004100450b2007641d9080240704901c0c00300301042c50000f84010551851404403000c584900c0c000d01500380036001c0307031040e00c0b54030b5503002600d0140c102179051007100e1070000380042c090b161062040e0400051070000c40c090341800400b100c3d51241c081c02000d0030b0391412408400074a003200104103d00a403180c440c040d = true := by decide +kernel

theorem S207 : BRFrame.sub P3 P4 TB 1680 MM 255 390058057 625 390057432 390057443
    0xc05030319020105070305040201050715113022060605030a210237 31
    0x5410a20711100c98510038164010141c1d028003072590300552600d0f08200c14a850740c0041d2980c014104050400c01180b030102540c00b2099000c50030318003040720569201c2c1c00c044c5d403152200341c003104204240c40a0041ca51030764a00d09541c580030300003449581d000b0700043d61000c0f000c2400ca841c2503509681380c550010b040e46040c08207503021030041142d4203840703501d81050301614001e5503440e000c66102c80314150345154850103011103a80d1070707581086903090094140e0002040120f01512 = true := by decide +kernel

theorem S208 : BRFrame.sub P3 P4 TB 1680 MM 255 390058682 625 390058057 390058063
    0x100911041107140c130b010206042d08190f08010b1c050c1e0301140d0c0503 35
    0x2501840d01d0f0458951480054181c41a40d0362020a0300030b01c8144902503401d01c0c10380040a05072100d403210201800790349024080e0042c102c10b1181c107004960103d84040d44034034a45500c130050303081e0b00f100103603201000d40c041105444a08135100e0b8407048887c11075003000005541d40310a03e2035551115407100404900354200707418420200c28410003000c445405101c032447c500c006c0802c1800c6880300388110650106059002d2000746080b0100100d07007072007a125100b403a5a80d81c00f00741 = true := by decide +kernel

theorem S209 : BRFrame.sub P3 P4 TB 1680 MM 255 390059307 625 390058682 390058703
    0x60c0512070923100f0e06041701050105030307050d08060607061d100911041107 37
    0x141c08a60341d94076101e0a0200107100c92100b650703000c4481405240300c0c0d10742d90302c250308520704c820b4926141d200c40c2120401903882909800c0c00d03940c021004680442c3c094414007041c1076400112000307026507680d40301813503100c0c45400d03006070080e04412034000b6604e001e0451160060000780003940b9041503030b1a5202110842d00102a68207140300c1e080d80b0500003048420799a043c8400100001c401d01e950784816182d81e1145035001300c2c1c650902c91445102c00c07044e1144548c2290b20f085 = true := by decide +kernel

theorem S210 : BRFrame.sub P3 P4 TB 1680 MM 255 390059932 625 390059307 390059311
    0x40506060f030a0921080a1514120a0309031502030405030a08040305090a0803090103150e0103060c0512 47
    0xa9a21005c5030b84420f40d80e1400107541e9075002040a440305407a5206003c60072200c1030040043c240050124014050000ba11282600e0042841c0843da144141c01040e5400018001d008604260b4900381c540b080c0f05600d1420281e581c10f50341e00c5807512600401c5281008501054814822940c11100040c002003003035445215080d1640c2c441070000d4046454141c500220354401c4a101c400c550075020b4100741607185480701e0001d03081100590042240402486c815641882c41185c = true := by decide +kernel

theorem S211 : BRFrame.sub P3 P4 TB 1680 MM 255 390060557 625 390059932 390059963
    0x60218060c01020c010e070b040e090f06090d08010b07080403060e0a06060f0302030606040506060f030a09 48
    0x76240e5000304140c1000802406614030000402014091440c1000c43c0b1811500030b52090140842001d0003140301540d05124080411005005540440c81c1113003005d9036a2f203c0210210001c4c030002c4c00000d248030000d007503c0301e041c0e015441920b450301d55203c0b80041c120102951189015014205001456611134400100f502e480c45c210708919600415080900003002503000b542072604002869980ea01190740000c00f4030905500d03504c4041010f002130211010003000b0040025900 = true := by decide +kernel

theorem S212 : BRFrame.sub P3 P4 TB 1680 MM 255 390061182 625 390060557 390060577
    0x603040b01050f030c010813050102040f0e1021030e0406051c0b160c06021806 36
    0xc4000100740a0a07000303c0401000c1a140c1c6000906a03000200603101c4540310b4440c0c82045083c11b0140c2070a451640d0204400100d0b4000d0800650062160601c0781368281450317800c4040049a41d4000081d80341c02c07420071206c407803882006054060307050400403d606055004503000d0a030543c48103a110500707107140301541a41e042ca1000c12803154580d081d1654806002c807a4000c0c000c22124006504840303101c0005409074020507202002c0307040030140403191000100241d211013404 = true := by decide +kernel

theorem S213 : BRFrame.sub P3 P4 TB 1680 MM 255 390061807 625 390061182 390061193
    0xf0e0607180e1b032e180e150702120c070f060c0b150310020711010809030a021911060304 41
    0x8a10a80f600300140e0340311400780d049080315810703c254a013102c0b60000318002d040c80d1031103030340249580d81807082f4100340850340c103295000710008000b040b903000003c079101510302008668029503500c06050b92040c4000c07000070701c2c0c8440c80b000601144201a40c080030802c003c2c0a40c1c00141c61000f8607000ca910446040b2400c0d100c001182820303503804007a25501840900084d0700d840400100650782d6003400301140881e0810201000c10407039528060074007000301820548e16801c007031428 = true := by decide +kernel

theorem S214 : BRFrame.sub P3 P4 TB 1680 MM 255 390062432 625 390061807 390061891
    0x9030b0c0d14070c02091005100f02240a0f0e0607180e1b03 28
    0x140362000d40e0a10038444501c4142103410b010354102e98800004040d03202c941c0c018075040040c20b8201150245007000c0a0722032001800c200c03074071603404011980150320034211980622030403051901504002002849122200c60312640c01010b0301e260990f17980008103101c4a640c08251141e00520841d8040d20b0703e050302402180c0c10070400c0300080b42c0ca00001400c4211100c8042c414000100400301c07415040d079004e0019000070380307517100e0b01006410540186031404203040205d0a50b40c55 = true := by decide +kernel

theorem S215 : BRFrame.sub P3 P4 TB 1680 MM 255 390063057 625 390062432 390062437
    0x32705010618050a050903041d09120a030b0301050615180f0d030906080a090b0105040207020109030b0c 47
    0x141440d510f01c103003600802034602840c130709403608180009e80d45400180ca056020300384041400140c042240411240b000340f1007a07261a500074000d402002c02c070015034003039420200041c41d84d2408079005c20545020b00f090905001070301c800c2081d42c0418400711034012444070b0741c50b4440d6980410380d6040c00d229540740c002c1e107820700d00c00400c200400340003071000508141591000559064503a4150342c02503d0060b100c13459400100c0f92108070707a102401d01d14484040c0801600706000 = true := by decide +kernel

theorem S216 : BRFrame.sub P3 P4 TB 1680 MM 255 390063682 625 390063057 390063061
    0xc0f0103021b010b150406170a06030b04050a06050601020a0b041415130209010603270501061805 44
    0x403170310600c4901658030110b15520100e8089840c283c503489520041c040c006864684020b004880842d640c80300040030861b05840e0504c1240700384045c02c0603010f5841d007101140d00260402c1c0c115401881c1c108005544003410310742103500481202541514402c51a01d03200c0d41400c250201c0303586a05103d000d50b407003561260707114801c455055041e03803a110b044044038021006a044030034020501c6a040f00745c00d0207807050324094800403410320f4440c402c0108201810740c080840640d6441 = true := by decide +kernel

theorem S217 : BRFrame.sub P3 P4 TB 1680 MM 255 390064307 625 390063682 390063701
    0xa03050a0312090c060e010215100614040f1a040b0f0a080a0e0c0f0103021b01 36
    0x405030400018645182c07210781000c8005000c50094144001122920b0a00c140703a0984c0c000100e003000f40b0410f04c0011520301d401405031032882d91b04418251100e179102d2448030400300035020b00c24043d0b13100d000440e8003900c00c03c0c0091109184107460804000105508040d20b441d080c911a401024945200381c1c008142002d4207075003d00040d82042e4888020440180400621611283c42c00001030007260110307aa4203450340b296049614041e40c250302d000302840d03050071684c00707003c1503070 = true := by decide +kernel

theorem S218 : BRFrame.sub P3 P4 TB 1680 MM 255 390064932 625 390064307 390064313
    0x2030304030807050f04030f0c080d0e1305040b0705030907052205070c050d1209020a03050a 42
    0xc2d8244640e4820030143d550344a80302c04024400350810050000640d1080a010114018407800d210700c1c0e1540c03415407508130580303c7d038400300c4d00c20405040d542c41d00001d10200300c40703038020500540c1095a161521020080d1007102402001f0002580c880700402042000307100062484646000da91040503a4030058950100000c1c10003000030f20a500070070300b01d401039600900070a54130f0150002121070440c005c0340e094481e83c0714841180907a80b505a80d001650107607002d020b00c1030703142ca = true := by decide +kernel

theorem S219 : BRFrame.sub P3 P4 TB 1680 MM 255 390065557 625 390064932 390064937
    0x606150409200f180a05100c08090414010f0905010b0409050601020c0901062006010b0417100c0203030403 48
    0x2510750044c0111041c1d0035460600d00480c03008020000710b9020f00c030b04c9a509030240710316001920000500200113000b580c54441e034206200074284280108003010f00c4002c96603801c07501a0f581a01d02c0160513508040c40c1c5071550014044c080c28141c154000e08226090a07106e030500140640b0080d00c5d0075040c0c0854121400015140800101107a04130100611100180c00c0c2203400700d802d40040d21000c207041412890620264a00d980c003007520b802051482282c0200c0554070890194 = true := by decide +kernel

theorem S220 : BRFrame.sub P3 P4 TB 1680 MM 255 390066182 625 390065557 390065587
    0x40909081c023c0a11060a020d0b090c090409061415030606150409200f 33
    0x100d40512a080c40c1c0301c0d180c0c80b034460042c040240118071840a0035a00c0003030304108000d90100205c240c80300030131542e8012054904050303106e030454110001201e81602d100380c8601c0080e004d020031001c0d2a001c6507260202924007050040c07180c10000c0103800880c645050102802d4100b0200e14902c42c4907040e00441201518001e03104c0d1000c000d02235202c0325a904005d00c0402c01000811420340c003210952142c1201d402441040d071f4044071b605e03004080009180400010f103041a03080c40c2c = true := by decide +kernel

theorem S221 : BRFrame.sub P3 P4 TB 1680 MM 255 390066807 625 390066182 390066217
    0x506090708310b151207061d040c020a0b07050309070303080c070606060201150b040506040909081c02 46
    0x64482c1e80318400c0b4100c1c605454102041c007504407015400c08d105441c1d100c100350304c2c0c0303080c030742c600c040d0828606003170f0a440a900144000c0c54074002c1c00c05d070807542c0790032008480c02e00c411102d92450b80c1c40700b802000000d10800f1000d600c11480c2d07a189007001256598407040d980c1c0e0340c0c829130050f9190300620b07498141249504009005002150b46082d103807a001c00c20900640c4110704415544000c14410320050750101c41e00b07140303031044010045115046160080d00710b43c000319884140d8 = true := by decide +kernel

theorem S222 : BRFrame.sub P3 P4 TB 1680 MM 255 390067432 625 390066807 390066841
    0x60b160203060a06081504020f120a05070503070605181516060506090708310b 36
    0x50020649101d8040c0f5071403a0001049000e82c295034448265019000074001542ca010038404100302801d540c0d62b188440c2c10003446034081c007804000d00780050000780c00404c901840d180f401000d9003e602802c2c0c0800c02070303005c400e002d952030703003814003206c0030560031307640d99880000d001d04e01510600411604a0700b45400980e5a250044020f03104103002e440382e500c0355450080e5441800f448a49040000d40324820341c00c14900280c108203511072141c0030f4641ea5080114105010b1044 = true := by decide +kernel

theorem S223 : BRFrame.sub P3 P4 TB 1680 MM 255 390068057 625 390067432 390067441
    0xf0b09070b0418020d0e072706050105090d0809030106290405010504090f060b16020306 40
    0x4400541428909003e202e101e080802501c642c0650005400e440745005402103128460410100c0b0405590f41c82162035540305880251001d8840f00e106084280b05070060300b040341d2059550609144a04040281800c0c0d0340c402115100c404101c42455610b003805860001c2528004c0080800c03458000d68141c01d01900d00a00008800c00c000c0c410f41e03801100303032401e8904103171000030840902c001c2c04c002021541c0000101d1000401c030280340d0f0f00c016008410301c6100f681960f60540302d = true := by decide +kernel

theorem S224 : BRFrame.sub P3 P4 TB 1680 MM 255 390068682 625 390068057 390068069
    0x8030301030b1303090e0f0601091202013e01151211090c070f0b0907 32
    0x10044038181d07a00b20340e1900603a501c5001e034100c51078a0403c120100000310704001041c800101416025801090403c64982890400148030700f40384d8004010303e0344e0322000140141c4e0840910800d100e060110300003181c078080c0b07101d00044903280d00706c210f440681001101d41201035201001000c40c2542c00c2e07140070b8039464941450002ca400040881c030401714051210702e85448410b80c01102d404505140800c603580f00355000700d1050084a010318200103110218009101450282032 = true := by decide +kernel

theorem S225 : BRFrame.sub P3 P4 TB 1680 MM 255 390069307 625 390068682 390068699
    0xa120605090d0c0314040806012c0603060612011103041b1202090c0a05090306010816 39
    0xb1101465410740c030030480104903825240041e0100145105400303a880755074001d08845c42440000306016107013608007a000451800c41948801c500807400e020390314100c0b21964182c20030700005555060017000b043c0d030041c0e044000202d5901c1c1c5d01750b04800d41c2041d00c0540d101d048013550749441600111504001d2300c02c1161905116000f44d0000b4804a002090901c2542d000308800ca00c0b1409001900d400d18001400d8075840d41c1c5401102d6500c0c1044520181ca940c0c10301000903c1c0d48 = true := by decide +kernel

theorem S226 : BRFrame.sub P3 P4 TB 1680 MM 255 390069932 625 390069307 390069313
    0x30703050c1b0d0609050106030c0305030901030507030c021e0a02120706020f0120090409020a12060509 47
    0x10040c0c0010360065100250201148058000c00c3d9594080c0e400021510341e00cae50f814001e038025500490b465000843e0141d078561f0180704099020000342018007070403800010007522004070541d080b0100790b01984039800c40790b013001002000d0358080d203c1485801c56002580d52454544039400041c4206480141800c0d010b016104001c3c0c85000c0300b601410450f81c500100f50001e900e0380d07400a40d243d0640300503950f01c0d45d0160003011134103480d581058580c01d140041d1100140b90a02580c = true := by decide +kernel

theorem S227 : BRFrame.sub P3 P4 TB 1680 MM 255 390070557 625 390069932 390069973
    0x70501051b0c030702010507060e012a090602031608041a0c0c060306030a060b0111030703050c 43
    0x20310b80151a124071940d58001c1c180000054807008110094210301c400403003503002002030040000d4100305451000c3c101c2144400c94039040c42c0700701d0068405409481080c0c0c021810b104403602e42c2d4001c0c1c0203020040d6012034040c000040c010785510700d0320a00d4000001456207449120791010328045c01c044400e40b00d80c0007401003080c2a180050b0340c544c0107401110101d400e0702c0c40350050314280c1d030a5040e8490303400001108018142c01030020540540110b04842c1410a031144699501 = true := by decide +kernel

theorem S228 : BRFrame.sub P3 P4 TB 1680 MM 255 390071182 625 390070557 390070567
    0x9071701060e010c030f05070f1103070e090604020d1401150e160f08070212070501051b 40
    0x2d41a1100f020b103840e40d4a0070345079a07003412003a10600000f0020710000420b005200e80000b442009a000074031500003e1500d440440d42050106000310b00c140038074240d0014203143d00c650304a4003405140074525044040341b44060b4403055940c24880c40d170001060440d48001030f1801003440200542c2c814002e03841296802c50000c1c007040b28066030900144c4207489180e803000081c0119485590f4001d01c1030301d2a8821842500c6595490702400101c1d500024652022146014154180 = true := by decide +kernel

theorem S229 : BRFrame.sub P3 P4 TB 1680 MM 255 390071807 625 390071182 390071207
    0x150303030b0409240e0d18090b06090114040e1017070e01050409050c0907170106 37
    0x4155600894003446200070b2044c21038000d8031104003d00a51800103504c0c440c2ca0810902250405507988085461041840b81d95036034046e4102500c0c100c0003060341110090000c8452035000d885164001c008105d405401d191b25801c0d68011a0000c5401101d40001078070b0800100c0e400c948024440440a000f4100f1f040c14407500001010040c4030f81170180f603981c40c80805210041c13004462880c00149540103600b410400100702140da8000c2000084205e000022024000c1d011807025 = true := by decide +kernel

theorem S230 : BRFrame.sub P3 P4 TB 1680 MM 255 390072432 625 390071807 390071813
    0xa09020315010302180d051e010b19150c020a030b0c0306101b0209100306150303030b0409 41
    0x101c5d4192070201c00b03003071850710410003610071310031610503040f02e01c160110740008005807a0700d41e4550840d402e02d410070081c0c0302094400d0f405810240c0c0c0c280580c580c0d801c540c1c2c1c1e80800c00c010b40c01450000f551303940c0101c5001150030181c50303a1745050003401d02d18140c0c01200c2d8140038840d075800c21003034584916443d40b0f01d00d50303005d180d054840d8554200140d50b400034011002c1000101c1d0080003144c403078428180c00c0514034840055036490351074090181d50702c0308102ca200340c0c41c0c80c03c01404 = true := by decide +kernel

theorem S231 : BRFrame.sub P3 P4 TB 1680 MM 255 390073057 625 390072432 390072457
    0x1b14060a050c0c07030201110123010807050d0b0a020a14070615061103040b0306040603020a09020315010302 49
    0x60b100d20b0202030f041c40840c2c46141c08c808401d4020007180a034071031075030750911410041c400c08000c080c000c486160140020101703440c24840700031007000c2c2e0014865a150303181d080d1f014000394891642c10f002c22000c905118100e8034a0700c0140700c00c0c4c1c0305d10000604007041000c0c19500d08002d42141040003e803042902da80300000051341c080d500d010440c165640c0390000020001c0007035a0000b5046880c10300006510700e2954051441109150203450031500218011400c1f8420100c00d03444 = true := by decide +kernel

theorem S232 : BRFrame.sub P3 P4 TB 1680 MM 255 390073682 625 390073057 390073063
    0x140609060d022d19061106040c050f0103020c011e0f0203010305030a1b14060a050c0c 39
    0x9110075154003d01808004400303074584044507903d48103a0b2411000040b1420b882c44051420340f400c90f00800d002000b400824079500580c0900c0041028068908283c0c1c009603012900b1b00d5007880102c0080c40b07041030742107095103480c20500f100a20340c92620804c02002d1000e010300740300d02501c1c40881c40b081c80010425842003008108003400380c0c45401e800d00c680c5070340921103402c6858200c2440c4090f118045550080310401040280c207100e8140c010136021074807030620460401e0550303 = true := by decide +kernel

theorem S233 : BRFrame.sub P3 P4 TB 1680 MM 255 390074307 625 390073682 390073699
    0x20f1c05120a1b1d0f06070f0c031b1e03030203070b0702010f140609060d02 35
    0x3000120140070740c1d10782c0d4440d800c000070b240100f00749441c03081240d0a41c661070b070081c1c44401101800306403092654140c409200c2000c83c10f41e00a6040202040640e0100b4103401060010070300c80c3c0e01c80802c040d5240c03505032426540c0b0082800300003000c40204400c054080750140c1080b00300c41ca8411040c84d41d24041d4590165100c09821060200005090396100f90f000e89101018101c081100c1100100700b4210f0401c01c4031140e0040d42c5d41000304070680341caa01401c050319402480d411 = true := by decide +kernel

theorem S234 : BRFrame.sub P3 P4 TB 1680 MM 255 390074932 625 390074307 390074317
    0x130f0f0c050304021903021011061602210d0e0f10020f030406050a09060507020f1c05 39
    0x94a000024021410550200f605c440c689940200d03801c402c0e4110000d02046000c60040c0200341c040180550007521442c2017806403074100002502c031035003d642003a515100c052102110000402110004036620504100c0501401c00d0503031504950182e1811501403451034007410f5449008480600d040f0751401803a59a80c0d6603014014000502000100c43e51000c0210000714980709040c0602141d0f0014928000441c002600e000280480707505001d0040b4400550b4036046401c0d10 = true := by decide +kernel

theorem S235 : BRFrame.sub P3 P4 TB 1680 MM 255 390075557 625 390074932 390074941
    0x9041d0319140304030309171306050c071a0d0b0108071211040302130f0f0c0503 37
    0x4581c1000320100711100e8003405103050285141c511650b41e80c64541401001000307028003c0300c1078440042980b9400d5098403c0c1c0d100030700200b40f626649807510030151401e9004e040c450303540380030340b200006a414100d82c01542450b038000341141d42d00c0700d8129a04c103d42404021a050003510000e02200ca079122600c40120301092400003000c00502d9080090ba010780d034070003540619021905141a14a40c028580c1e01c1d00b1140107200f07801401c0340300700540e1004125100094000d10015 = true := by decide +kernel

theorem S236 : BRFrame.sub P3 P4 TB 1680 MM 255 390076182 625 390075557 390075577
    0x6030b090610051b070305010908040323060109230103210203030c040302010e010318030509041d03 45
    0x20032071100d501341c0503008442020001400138043c003220607009480544d200c3d8111709124030480071240e400310607030480100d9550031181c0030401c1d5045a035040c0d00011003070030580c0c2d805444c1c0004501c50140e410f641e000481004021a115198411401c50361149086a84016641c0c0d100c144c821606800e400d2004100543c0304601c0c81c86003c8041c90701040c1d030014010107040148195600310f0101d100883c041100781800e00c6084490981c0880042e08440966a010b460348541c1e1210 = true := by decide +kernel

theorem S237 : BRFrame.sub P3 P4 TB 1680 MM 255 390076807 625 390076182 390076207
    0xc090a0908070f0305190c0210050a140904020d060807210b0c03060112050106030b09061005 42
    0x9400000c190504850300d0080b2a406c03210024049101000f098004c041070810900c01d9a4070710303904503099019070f440c1c0038100c100b0000c21714000c5402c00100e500301c0200b15220380180014203102c00000004100c0705160001d4555500c821001e0007101308003841088520398551241c2c0101c0895994415803060103001d00c6c04200010022031900ea00822606014440300c2a00300115a501d1100a000e800511101340c06140840081001400c0401100311650140c1d2034007880c0c4400321098 = true := by decide +kernel

theorem S238 : BRFrame.sub P3 P4 TB 1680 MM 255 390077432 625 390076807 390076823
    0x213090e071a0d0204080d03060515090114030916030803060a0914190f0e0c090a090807 40
    0xb40706143d180d00d401440c2598500107581043c1c80c8002543c0401c0d07943c403042043c1e003404c0003045100e01903108804d1900c908a40060b00c541c810950100200c0004000250994001c220000e140080d01e1f2810202035907a280200702540200c2e1018000d20000130002012034441c090445140c1c0c0d4803603026941d65540d40e0b0031042540c01c48039400742d02d0f02c0f681d01d005c281215100c5c40f61109039110207002c1034200702c4107000700800050203034031116280c0b4407440b0101c0c0c615019100301d19404908 = true := by decide +kernel

theorem S239 : BRFrame.sub P3 P4 TB 1680 MM 255 390078057 625 390077432 390077437
    0x1203060604061d0933032d0f060a0b030c0a140a08010213090e071a 31
    0x16904860701d0307408519000c06403a82500703140510790170348296000484000c1034110650070881ca0403c0b00b20402001e43d000d40100507012050a8815400c0101c50590911140600c01d440c00c103201404103010700d01c4100014800d03800c0031624581901da501d107040e4001e43c00007101030710b684d8818210300201d6036000c107813140d400b08000c003048480b0703000c4c0c10000e1190700006028010247c886111002c0b2410b2040c01c0100070034a142164076a11130b41320708111240b1030301030000c030354403e01d00 = true := by decide +kernel

theorem S240 : BRFrame.sub P3 P4 TB 1680 MM 255 390078682 625 390078057 390078077
    0x60303171509011511060105010504180b090a1d0d020c010c031707050a02120306060406 40
    0x502a907892652501c125540d5000207406041e41c418503d0f10100101d0f0007600845141101600030741c4410010070807aa400b5003101c0607240484000503403c0d40203980440034110408641d80d2001c211002c108580302654071a00c18801704031800f00700803005400032078464054502400050300107612440082d4012841103038140d21901d04100201c009201503600f4490541c0c006000400000d41e07203003c5541045007a1a040320031158514500340700d00001c001c0e1056210b00020300c5150300c6 = true := by decide +kernel

theorem S241 : BRFrame.sub P3 P4 TB 1680 MM 255 390079307 625 390078682 390078691
    0x40504060b030423011b020c030709050903070602030a1d0d020c01050a020d0c0501021201030507090e0106030317 51
    0x9603401000e11b05400d8651207590f8465802031034000a1100400c9000c408688002d0b1b140ca100c14240e03041640c000c0c03407a900074084040010156006075900c5a0b042100082c0c14021002d0880061404c419060f040d402c078074440205154148440c082000c000e0078802d03e0645d03001d500030341c1d070042c402400040015020f02d000401c2020b4040300c40200c8210406003555840b0b0030907030703140c1302c581c0309240b07442c1c0c9819500d40340d250040c01100212071309501da4101030042e41a211206003401071 = true := by decide +kernel

theorem S242 : BRFrame.sub P3 P4 TB 1680 MM 255 390079932 625 390079307 390079373
    0xb04030e06040f030602193011181509010c080d0216030302040504060b0304 35
    0x18490425580f600c03850442003040d042218004e402140381c0d00242c920710003200b0380045074109002e2004030f002c800310030324804203401c88094400100c1609400c88a501c07103503000b80c5401190b5036400e1041040d02c01d01c401c1540d0319002e144c81e446062032062442043d607070200b00507901c05024003d00c0d01d410b031403600300011040e400340d400c1220300d250480074562501d03d50320070f440c00740c0c135149071408010890b400e5521110010380f00b0810031001400030840200b409036000184461000341032 = true := by decide +kernel

theorem S243 : BRFrame.sub P3 P4 TB 1680 MM 255 390080557 625 390079932 390079939
    0xf01150e06070606170d09062006010311010e0f0d080c070b0a030b0109050d0b04030e 39
    0x810200124040c04241e2107850310300e00f140c042c02c0d0701e000c1e1403001c003030049003031003810400155071031040059192542400c0c2001ca04480b200e070840340310b6a00c14003c40c80b801c006d0500300804c50095000e40c0c0e00f945038421000004101601c0b4424041c0b0450505141c0c07400ba42d078621100302040e601408280da42e00710100c8083c146902940400b8090202090b10303204290541c000b0300b81c0510990303582d0f518980311001c00c415114110000740c00346c250f4030005400a4005c01c8141e61442004 = true := by decide +kernel

theorem S244 : BRFrame.sub P3 P4 TB 1680 MM 255 390081182 625 390080557 390080567
    0x1150b07080d0501170f0a02280b0d0f0b100212071a010b03040b0f0f0115 34
    0x1440c0080c420070f02ca80ea008000d10a03480d045040306a0101e420540502d12010319900011400d80240c0c9491039505821504849215440729400200b840c00c1900d503080380404550004003032800c4003032604030904401014000b00300f020241020401454564a8080c0260300103400810784500c0681c042c02c0994024030f9910300e00301004a0700b41214009801822040501006002c2800b4244000650114280d0501e20a034208400c80c0c05041905108504c1c800320666110314810f4455 = true := by decide +kernel

theorem S245 : BRFrame.sub P3 P4 TB 1680 MM 255 390081807 625 390081182 390081187
    0x80d1e1d0d03171e0109050103051507210f0b0f010c1e0b04030c02011101150b0708 38
    0x1010300f4607000340b0340c0e080c03003010b110410f00c8110300660400a07140c0da176651303200b07039044079000d10000c0c0051304941100f45484116003a0039030411214506501d100c040d0891000500e50200410005203585150040004e060350148046200f001c44c0c00c0020300c0a4a80080e0154502ca200140030022400d031155254a410354111000341d04034140c80110318040c5000b0f0b11284012406a000c18841e5014410202050280c04080343e045440c0807040c51404500c0c151581040c041101c07140801e = true := by decide +kernel

theorem S246 : BRFrame.sub P3 P4 TB 1680 MM 255 390082432 625 390081807 390081827
    0xa02070c080102030103031205070c0b0a0209030a050109050a1205040605070615080d1e1d0d03 43
    0x241201c5099901c01e9008a000a04031070608407040003506c940c9801084134034016241030f00a4480081029010744445002c542c0013419a609507010000500305035440402032000c5402030134071948644150f401a64001906051201d050f44584c0803607095a4251311583d04002054a5002c010035002c1d03c0e1050300c013201d440119010104002000f03100360182e45641c0c008040112081c010407040034290140700c440ca0440c01100420080309600800aa41c0c1810300c4919043c219414510 = true := by decide +kernel

theorem S247 : BRFrame.sub P3 P4 TB 1680 MM 255 390083057 625 390082432 390082439
    0x3040f060203100501030e0d020c100c050312041403090303092205010303020f150603060a02070c 44
    0x1000442d16030405000307a00352100d00d48140d500090406001901c19880480c101c90010380540040c4203000d0080284030911f0498400c540605c1307941d402c1031012490900091205550144001d80745180034500200c0f9505030400910300c0780d20501800d440381c1c40c000700700c8280312800c82e08030b40702c0e01c014110a000180541d9100c5049801c1200000400d500024100252402c4038180c52000803044ea00c01c01e080e0741125143e506a0002c0302140d01c840460f402003001c0d40c080c1c10120083d03901e = true := by decide +kernel

theorem S248 : BRFrame.sub P3 P4 TB 1680 MM 255 390083682 625 390083057 390083063
    0x5040203120705010c03060f0f0501050d1503141908070228140307120b0c03040f 37
    0x801e0050440703640518000a07050132010009421103009900c0f204854040300000c002401d60440b0210071101c007070070f02540e1860b00d044518000c0c0f000304071a0b5840c03984420080103100d0381c0d0035202201c000b046c04440a24140c421101c0507003041042c000c1401038100064401406c1c1005050001c40c01c000181b141c807050a0645480d681d0180c00802e07032240320541600d4149000c00950004040d0062040c9041507503071109032446d54014400c120403a000000b00b07080000d0420604030542d0 = true := by decide +kernel

theorem S249 : BRFrame.sub P3 P4 TB 1680 MM 255 390084307 625 390083682 390083713
    0x307151b0f02121f0b0108162d180b0307110c030109140d0804120305040203 35
    0xa500c883d030b418810080340428000d02401c0380d407624003482c0f810510680d81c0026040b800a2424000544610042c48050200a8540c0b60002001211188407103103080303814012031a2101490b080c0303103a26405007448500d00179038042d04200d607250022080f11804007400c0c0c0d134140141808690300c280002c020f20008020010000e01000304181055040c64001c40f904130044c0c060030708920f0466001b0318105000e40d60103100c82103450140b0381c046004003000f07442280c0c907001e2417070308200011 = true := by decide +kernel

theorem S250 : BRFrame.sub P3 P4 TB 1680 MM 255 390084932 625 390084307 390084319
    0x130f021c0509010b0603100303081317090108220204050703020f0301140307151b0f02 39
    0xc550340424164640c0c080008080d002e01c600c4515840484000e07042d4100880c03528160162400002e0500c408007000ca50401c00a2490f210801d900c2000f0742d25820100800b0500c0341c00c001440c501240003c004030700d668030b94014021708410450b840b01a0451b05400304805080080c140c5000d0550804c00c03408200003140055002e4100102448840c4d03035a0380074075241c0305e03507603001d0441442150709003014035034050714801c139180070003400519684050800720424645004d00960005c = true := by decide +kernel

theorem S251 : BRFrame.sub P3 P4 TB 1680 MM 255 390085557 625 390084932 390084967
    0x91509011e05040603140103111c0f0308150301090210031a0a03030903020102060114130f02 42
    0x907031034000742c45a08280140c400107840c0c558010100c81800c411281a00d4000c048405030004000400040303000540c10100400660a0050005180e11440c00c03501c038807a884050703441c6440e05410314400c040e01400c030f00c20b82c1811007000140c0c50390209502da0045601c0d001c00d81c0c2d04a49040c0b00d40407002e1b24800d800c01a40c50300001410351040010050303d100341d0079504544da8a55086891002e2a400554050710048011600a4a030703801690b00b025040c50150905242c0f0b01800c8844 = true := by decide +kernel

theorem S252 : BRFrame.sub P3 P4 TB 1680 MM 255 390086182 625 390085557 390085607
    0xe010801080a2a0e0105030c010806010519090b0a11070603020405060d150e10090507020309150901 45
    0x1565041e413640a50400c0c007010b182501e07104e003041c100501c032010400c4030390f8840709940b901d021840d22540803030011f110a90361644150840f40e000113008c200c0d800d80c42d0340104c003220420156019152682d07101e06080f4268480e5003d0f254024104100e440f01040b0940d100c10010700f1003004407011261071707011076000d541c030070f98400000001d14103043c03103194810311615411800e680015417801c809240031500100c00200f0508a40c075010074030301e40a0740200c01045203202980c001031050 = true := by decide +kernel

theorem S253 : BRFrame.sub P3 P4 TB 1680 MM 255 390086807 625 390086182 390086189
    0x30213091b090c140f09040b03010504060e060a4107030c0e010801080a2a 34
    0x9501121141c0a40e00c90381020f00c44640704010545110b03080500044070100244614100c4034440d0b000b500f54840000d00c0421107540f030002080c2151025107041d0740740d41d12444202c845600801911350491a01e1004200c14095850324181b08000155000c10729051301c4008003850080c600340f4500c103d400c01303a899250800c444040c0081c07001c2100000803440d4020812625030040b1005030407940d007080a810b1482c000d5868900c1441c075400184181000e004890102c04054850b40740030b03 = true := by decide +kernel

theorem S254 : BRFrame.sub P3 P4 TB 1680 MM 255 390087432 625 390086807 390086843
    0x3030d2703142224090509010501030209040f050f22050c060a17010e19051003021309 39
    0x5490185844402c4001011911350719009441c0c080010351a00b0005024041c2c10300c0703031030f040c16030005000c5050f859903003004854948040e4184202e0030040b012880802c41118111703001100c46041e1116508403000b081681c0d034002000b0f01c0e114103041c04120b02c6a00030310010050140301c0d4503105000c01d0b072003030881c003c4c1440c46140d4081c2c42c0404003c078000e1a24100340b44054588010070032a100075442030801c0d2601a542050440c103011041801041c45000c0a030030113055010701c00710 = true := by decide +kernel

theorem S255 : BRFrame.sub P3 P4 TB 1680 MM 255 390088057 625 390087432 390087449
    0x3040e070f08071205360115051c0f0203030d27031422 26
    0x1010465480000991009240030300e54040c0540c0d500580950792040c502c0c44001c103001c030240c4006446c61942d00160601d4909800e0003440d10180b819502d400a03c0d258401a0b416081d00c54008403100703001c56a03007040106507290104824034004407204c0f030b40318208904200d05454080d02e0040d40601000501c00700c8941d03180d10810381403841204d861202c6941403c5098042c036080002004250302d610301e0808950302c6000781c000780913841c61070010482c0d031000580c02ca009640c0051403 = true := by decide +kernel

theorem S256 : BRFrame.sub P3 P4 TB 1680 MM 255 390088682 625 390088057 390088079
    0xf2505090103082802030703140412230c03061302040f110d0e0601050a12060e0304 38
    0x20b5643c210108520307601319015881d42c40360812060814554000f00b11107405800d4a0600c5041044450f10013461050b507200c0820551014007000600c042c40b01c04d00c01c6503600d050420100c071100741c42e01e51030307016198103140c1c5a0449400110404d02d15002c40d090944001e0000580c28098268402100c107038080d110049000410b030340c0171030304032032103459210700c0203100405040d0714081c0058040c005500030304401e07075145c02c07201c0200079564000e011041404030540e6181d0b03842d01e40002c2 = true := by decide +kernel

theorem S257 : BRFrame.sub P3 P4 TB 1680 MM 255 390089307 625 390088682 390088687
    0x90504060f140910020c07051306030606050d050c010c020a05041a120f250509010308 39
    0x2003034880c0304006582d41214032101440003990320308040e422501c0c800f41c081100380c0180044840e464151000d00341d60300e0016942410b40800c4c2c1e40050f8680d0380c10800d028540c45480c00601d001c1e10100108111551f5260f02c03a1029900c10b410300102c002180199200c12140c0e0000d0030001e0000c01078001800c3c9042340c500d0403080e40754441d20750701d010500704a901091500154610100138100740348080101500c0326071040403183e20341c888880000c7c003680d0350117142d4001c500405140781d = true := by decide +kernel

theorem S258 : BRFrame.sub P3 P4 TB 1680 MM 255 390089932 625 390089307 390089321
    0x10f1d030f1b011d1009110d0206070503030f07120e120f0c010c0818012c0709050406 39
    0x2801e000500006030b4030000e1780014080d440c05a00c810608188010fa4a0300c174469190780d0b4800c6480c0c1300d06582d5241c0d0084152a1a031909420218814004550440c0000d60314080689001024801c110010050f9002002c01c07018500f060200da0340009500410050240f142c588c4d041d50074021201c0740d05150f9101100d5041040d407100700885031040c614004d0341800158540b6400003180b1908090818042c1000f40048030381a070304180103900501c0d485810704080005200c0160880d00c = true := by decide +kernel

theorem S259 : BRFrame.sub P3 P4 TB 1680 MM 255 390090557 625 390089932 390089981
    0xc0d0e16090b0a1a25110109060c060b0301180b09060f010612020a0917010f1d030f1b01 40
    0x35120007084405c2500d1f40c00307040d4210444016444410545040da01c542004009034003551303405d5500c8030321000c141c4005408440c80ca034806c2100c0a154140955000d2628500034401ea0140300c0c1e07080140a4242c1241252401c9600d090001d0fa0750b880c4100102d411085c60380c405c056058840406090390310b419000308100c10251901084540003d01c0312402ca42031540c1c1d48e050a42080203081d0120060400422061052482c0c15108006007004c6500b10360305584c4a20890131074541d142d = true := by decide +kernel

theorem S260 : BRFrame.sub P3 P4 TB 1680 MM 255 390091182 625 390090557 390090563
    0xe030102270a06022107140303010510050a0c0b0c0d0e16090b0a1a25 32
    0x51200c0030007000306204a8150004000d16038001c83c90f2100011004140001440141840e11590151040103010341800c0099030a90f18000001507041c0d802c01c8404442c07581a50408954178400d911891000440c0c04000e8030000d0122505a40c10003030500050341440100d41100048880000c40c1e585103920035003c2240000c007003118040584441201440003c541001190045110b8030030f40032204003255501c1605440300003505d40c000501140414007590710881640d804241c07140079 = true := by decide +kernel

theorem S261 : BRFrame.sub P3 P4 TB 1680 MM 255 390091807 625 390091182 390091237
    0x306120628050c070201030c05160c03060c050309060105120f0703050f0c0a0f05010507030e030102 45
    0x1481104a1844840842c0c204980c2605585000d00c062005035110b40d01c481c0d868412810312038508080c40c140d1030031300304441c0300c115401c442c450014000c0085900502260f501030741031030b6003941001140161070b900140521402403486900302d03106070700304004200c0040705000540300900c0d1617007060b9841d07001240700c20031a442481d020007141d0400c2d08125003160103a0582011441c00c000046032203502200d421703020843c0035008403049690a100030b00b14103031946101300b2403c241103c1d1 = true := by decide +kernel

theorem S262 : BRFrame.sub P3 P4 TB 1680 MM 255 390092432 625 390091807 390091861
    0x21060d060e011a04020711060c01021303030e0111010519090302030c030403061d0a080f03061206 44
    0x45030f01407800d50302181001e086640d4460b0760044010b0807445a0004140000c3c8036009404440c1c4800c60b0341c1942c2d40240da03a2401811114454180d1404102c80d2038030700800410521426101c0c5100741054048092030300f0b6400000c080c52103080c2e00314042000f11aa00e1442000100300851040741c0000720040d45902a070710200e00760307083d401d86070002208080450b00380d0050301d0300100000980365680d1107000c00142460301e00042420540121f008019003140b29651201c40010101e10b4 = true := by decide +kernel

theorem S263 : BRFrame.sub P3 P4 TB 1680 MM 255 390093057 625 390092432 390092471
    0xd080702090105090403080406021305040e0606010801091808160501150602070b21060d060e01 43
    0x45114034012404e0741c42103034107a5604416582d20369a203400782d013003080da0391034450055501050a0f0b49074020143e132804050700070201d51502000040501c079040e4850045036142214032a039a00340ca110650032190454170351680d80c00810807101e00340d0b50020000d080d0754031389006464401c40c00c44d110b00848480ba03089450301912900415554421030030300784590380c91000e00c070030000081011907030b200900601c2c92980c11002c0d11448159101c01c000312002c1d075507800000010a012894 = true := by decide +kernel

theorem S264 : BRFrame.sub P3 P4 TB 1680 MM 255 390093682 625 390093057 390093059
    0xd09080703050a02061303020d030215060a06080c1b070f0f0b0a081609050d0807020901 40
    0x42449800c040010000201d00058050226a0449001d6200c8107030803a0f00c244502e46034000fa610407440d100480c00d042e00401e450102c1108400701002507941d88090012811007442400700285c0284002403840c0c2c803610142203940104c001400c0480320041e20a441c02d62203400035001c03400380000030440b0800f5840300c000100546102e03141080c003428400741c0b22442c020841444110140306035480380d48100b02a40152100030b06215407203c66041800c140c1d00090f40490003000a200 = true := by decide +kernel

theorem S265 : BRFrame.sub P3 P4 TB 1680 MM 255 390094307 625 390093682 390093689
    0x8070b0109020c06010602241e07020715091202190909150f1b05030603010207050303090d09 42
    0x4243d8452a4021495041c0084540080701400701448c01a40003004d0300301d0701e5a40703e0784100c0c10182c0d480c211060310240e8404502040301c0c0340c461a00954401036807608114a6080c000c18110614440001900c41d036405070f42d44443c103840e00c0010000b00351016003005400613920340040c401294a51148546141031012040c0d4030590054428036401c0c104101e4199200d0ba4081d07405800103000c440d0599424040c4c0b2000070300c10001507000d04000c83c0104030b10418039000900d06103880c2c0 = true := by decide +kernel

theorem S266 : BRFrame.sub P3 P4 TB 1680 MM 255 390094932 625 390094307 390094319
    0xa0303020d0908070b070f0c05061606050108010509120a09030b07030507080703111608070b0109020c0601 48
    0x101013451400300c0d912094401d8a1014141180c180524010320681c00035078001000060015542c070381a4042c1d5028200700000700b11040390033300b000043d00540500505018070840d0015240d0482d880140c20041c0d801741882a090019a050000204000705815881000b86485c00b1034640fa00010050002c0d00040580090625042441c0c0ca030810040942d059143d9100400c0310b0030b040b5040c26050740c000c2d0040282001840d03000401ca400d10303500584484040300d800c54400d0790301c0b10 = true := by decide +kernel

theorem S267 : BRFrame.sub P3 P4 TB 1680 MM 255 390095557 625 390094932 390094949
    0x10b0a090f06121e05011e050103020a0807030c09090812070e0f0909120d02090a0303020d09 42
    0x10042500c64000f10104420403800d0a000244d04a45070261065541c41184c0407020140060842a0100f6107101260950541c010071068800c594810200d0740e0103c00200005400e081c500021186940000140401d1368207011030b00d44504220400340c4c0c4200010800243e800246c1d95500358010b5940d106642818010300c0703540c0e40c080d02c0a6641c0d6003c03d8000302482c074524010054110744500150421200c0000309182035595003084016030001d1809004280c0d00440e520000e08410 = true := by decide +kernel

theorem S268 : BRFrame.sub P3 P4 TB 1680 MM 255 390096182 625 390095557 390095579
    0x3405030f0604140106030e030409050a060510140306151207020705030714061b010b0a090f06 42
    0x1034800050740f007440c5083c1c192541458045185143e680b401480d6004030342105c0540e518050503c94107176190ba00c85022600c06486400e6030740d036060400c2d24801900411303034078900c50800024080345008500d86180495202c1106c0c1800c071040230b400400c1100321041c00140e4050175080c401440c041040d44020315840410100358000500410031381c0c01144628002c0043d01d03001c3d4540614290444200d004020300858034180d030714907002c006404401003200d2420329104011440703003480 = true := by decide +kernel

theorem S269 : BRFrame.sub P3 P4 TB 1680 MM 255 390096807 625 390096182 390096191
    0xe01030e0319111204210f030807030e0609030a0f05070503033405030f0604 35
    0x10300c0d40140d2081c8150baa002c036080341000b025403200d08020a10341c0c40030b00c0c03103401c0c11611211000f242070041002c00410035910107441d291100d80c07040d401d01c0d110607035070710303500388015480a02044016400141c2d4540203a1203405070f40c100340c003214010700c4d140048680c1d80c0d1007100041c0004840c20340d0529014042c5090b41c80b401d5000020f5030441e5510179031125a03541c81c00115140d4810038011071031010352141214090102030b9142c0381d0764603001e4000c44209101404050007603207031 = true := by decide +kernel

theorem S270 : BRFrame.sub P3 P4 TB 1680 MM 255 390097432 625 390096807 390096821
    0xb090301111602120a1b0603060e1012020a0509090a140607081b0c0d050a0e0103 37
    0xc540e00400710a242c040240115409075070100000810f020721000650401008a9102504055402c50681d02d018640209140103000704070400041101481601d98841d440555410704000d0541e80d00d05141c00c1303a2010800d0703404505a1a0380e50054041c520403c0102403e10042ca00701101d4044d10b60040f5a607440300782001209944084015080b04802c00c035254141d004d100d1210032803150000504091080d0b034000e000640e4070134000d102a12065481d20855800714004501303403000 = true := by decide +kernel

theorem S271 : BRFrame.sub P3 P4 TB 1680 MM 255 390098057 625 390097432 390097447
    0x1404030e0105250221010c1b05031804020c0d020309030706170a0f020d060b09030111 39
    0x104040d50481d00e4011551100c0e141d0300040342c4c860403d2100b80082c4c00c00000198090304c5d8a400010502c5100c00f0107003500e0000344118641c00d0a91001c4e800280b40001254400007502400b034141c40b000c2c0000c500a401100251f603014000d0802c2c2c40c1582d40e0010141800c540d045040701c84031643c0740030a039990155071601c0748080c2d10013800580458002e030042070710505080310051a008011003114129003071604940c24141000130b10080a25007402135054101c086102c080c60106c0c03 = true := by decide +kernel

theorem S272 : BRFrame.sub P3 P4 TB 1680 MM 255 390098682 625 390098057 390098077
    0x61609030b0a021605340b0901050f03040506010e06030c103002030405070e040507030b0414011404030e0105 49
    0xc01120030140d4001c1c00c0450303100d03100000103c2e2b0a0107440710201003081c0010603c400d0040020380e05040300d4804845154176a1448149500d4919010401c5e822003088040800010b004502041086400311f180b0020f01e6101e040342054080e03900060f40306240d00205220600c0014082e85010f01000360a0080302e0525990312941d81c2101c0c03002030505510203011404202e207045000c460f81e5000c0000b84103d45545113805004e0b9001c0d1021000703d801101260980c3d400354003542d151001d = true := by decide +kernel

theorem S273 : BRFrame.sub P3 P4 TB 1680 MM 255 390099307 625 390098682 390098773
    0x918140a180f171306020d030b1e030c0418020102061609030b0a021605 33
    0x140c0c0764403000614000e044001c29025000c8805101001e074032031241c99020020740301d00840d5518040181316010081c44c04080114103043c046801180b01042c0e4590301c60580480300c141502d10101c19840c184034030010300c00d02610511442400140f2031001c111403400c01c030b0044c840c40d00011040014220201d0300b9441540e44c00020500d503849003180204054003030042d02c0d074200604401806103403043d5001a1150001d089683d05015140510340d002500c00c0d400450031992007001900c = true := by decide +kernel

theorem S274 : BRFrame.sub P3 P4 TB 1680 MM 255 390099932 625 390099307 390099341
    0x2030411030708100f061815060228020609030111030a0506031b01050a0918140a 37
    0x104d580148a1894544041c20048503054011030000c2008240983c101700c102484070014200c000006444000503040000b4075501c0044c00c82c40f00120702c00c101100c2450b8803404d0178400032000c0c040c1e0308240d0030131440c210740d1424800e240b036034910a00390a45034100f1540c00c50542d08091308841c843d5000300b2111007080c100000201071020300342005642c40b880c1c0346040e1078409807030303003c03e443d5044581545400507941c0c01001e1400b00341004001d099440700816822200368507003412402c0 = true := by decide +kernel

theorem S275 : BRFrame.sub P3 P4 TB 1680 MM 255 390100557 625 390099932 390099943
    0x90803030c030406271b0603060b0913090c12110607030c0609051f02030411030708 38
    0x40c0c40d0383d1000607240305c0407030288400c643d0f00300b12245000c4030b100c102510300882c0303a403031344480141401c015480d854100c001054240002444101071000481d10350034025103000c2c1224854a113294020014a0750040c4a0303843d41c8000241140d5078010501d00300d016051440000c20002c04005842c0300700c100060104a40b0b0044201284180e03210aa080f400b0701c00355542c0d64001d850141300e2500c03003500652241c2c0e0200510040c2b0000f08009098079800b80c00400c240c42c2458100c070358a0 = true := by decide +kernel

theorem S276 : BRFrame.sub P3 P4 TB 1680 MM 255 390101182 625 390100557 390100561
    0x109090209030c0406080c130603110103020702030f0106060e010f08090d080709030b0f040201090803030c03 49
    0x20a10400141c4407940c600000740f405070003803a0720350824640b8001245801c808540340440042c01d55440f0321840004400c3c0040300c00070300c00a03000a03a2451500785035842030700104541800207048404902036207418030b0858000d548250040b8040701c500142658010f5901084036156007041d030300a1400c0c0b540c140d110712014611070200103101000850042c00b036000078002e141c10128520451409240d0140d00b010b040e80d0070380c003240940e44009846600001100e101d0103529215a00395 = true := by decide +kernel

theorem S277 : BRFrame.sub P3 P4 TB 1680 MM 255 390101807 625 390101182 390101189
    0xf3306080105040213090c110c120c090411040924090c05060c01111b0610050109 37
    0xc1416030040c002c000c60b0800b10055107485001b4082543c4480400e4000550303c1038003001c05441c14820104101c504440c081c0c2d000e0120500a5615111031941c2031040b003112000c034007002610b0802e88415403001e0402c0c0f11042c07840c18524088041c150310300d01d0040c3c4814000440c000d09200306c8501c3d0b83c3c41180e100d4120f00f00028404241c001c0d0102180c2c1390740c0d80255444415040002d1300000ea41048280400c445031001c003410107602a15065058058690903c420703038200344c818050f0b = true := by decide +kernel

theorem S278 : BRFrame.sub P3 P4 TB 1680 MM 255 390102432 625 390101807 390101809
    0x21e031b0102030909180a1505103002040e0102220521010f3306080105 33
    0x10107814011950800c109401c5405121346d081c2910001801d500d4007041d00d10401744c04481a07803d01d8007060003203401600000441c1c000105440c80800c02c1e04c180c045c0f0041041142181e00400c14006000d0785550241000200d00200010390343c555464100c10260142c80800310100d86401e03080c04a901c450b040d0903803445c040d1038281285034101074460b000d4401c5034001c01446040170b00710710126021900f040402988a101110b8103c1d400e214482c01c090288580c0002840080041080b = true := by decide +kernel

theorem S279 : BRFrame.sub P3 P4 TB 1680 MM 255 390103057 625 390102432 390102439
    0x60f01091b0f090b043302061311060c0f0c100c060209010903021e031b01020309 37
    0x98034000c00c82c1010054241c03030000300b1384031140141010b07000b8288001540320840c80c6c1020310440041c13018000c040740029540c030494000c20007581c091180c00c00700080c9510792801407000c1041c800780c03a501210205085410580002e60740d81210919021920310300c040c40e0400c80e0b0301c1441031000c0c1c00074000120130b03800981d940d00648241541030611401c071a40700e5000800880d84804840c01800c4150009041450f0030082000070032901c000070b100c94400440001e44030b10800410500 = true := by decide +kernel

theorem S280 : BRFrame.sub P3 P4 TB 1680 MM 255 390103682 625 390103057 390103067
    0x8071403150301020d09050c01091205031b0a1703011e0803030103030e0a03060509060f01091b 43
    0x1640007440c0000c0c0280300d46541217007043d151000e1401081030126008c21004000d0301c0301ca480903951003c0040000420400a210360800c00500900c41fa0f17074a03415891400300c1089600c1c9822681e909034645040e03005200324628003100410804804940c0c402d030105002d803034029243d1030491501e6503800180001428080c140d1f00804403500c2d1083c20400664000074188000d0404c1c0301d00ca81c80300c4080e02c0030391045840d82c001207801d071000c2c051802c03110304106003079a5940c01c0d40c204540c = true := by decide +kernel

theorem S281 : BRFrame.sub P3 P4 TB 1680 MM 255 390104307 625 390103682 390103711
    0xa030c02070b16050c0405070f020c0402030403120c0c170a26180106050303070c030308071403 43
    0x9041d00c110f017500e0f40303442c040340000d049460880380c04002c03c8130900011107a680c140403480414404980c118250304203074030001d241141c00d01801c031b0955aa0b8003403401e000c3c02045110380047e84500003c62040400c802e1046d1500603c2592003c200000000c2c01e21680f1207013051013041d1100c8a03500f507a656540c541c0302401c031401c0c00880179587d038140800d05450500042122900400c588180e1500d1850020540301000788070f00100000e01f480d00c4107030034842d8201d0390010724400c0c900c807 = true := by decide +kernel

theorem S282 : BRFrame.sub P3 P4 TB 1680 MM 255 390104932 625 390104307 390104347
    0x81603020906040209041401090501031e020f10110d050301090c0c051f06030b040501020a030c02070b 46
    0x80e03036101c54101d0401c00c80b004007c290a5a160060f0b5001000203000580301c00030710340d00400d0700d40d01d6103a04c00ca001e60000d1450400703000c0541080f42d0003400a4040040001c540f80500ea0203000b08885955054561240c90310780d0706220300c42044486005c00101009010703090200030403004140aa080c44c5100c0c5d202498065805e420009040c46a00003400010440100b01c1448030660151495203c40d90701071180c1c900d49002240e9444407030060340c8400004101104664840090b024 = true := by decide +kernel

theorem S283 : BRFrame.sub P3 P4 TB 1680 MM 255 390105557 625 390104932 390104947
    0x306022821020f0f031f1e05030f070302060a05131202041803020a06051905040308010816030209060402 47
    0x144100e80110b207240d8203000c1074100030385804507c107281a109889045419105640503034440d9121140c034000e8804081500d6049a1703050f82e006454038861441a241070207948042002c8003c000e4002480648022208921034000d840c00c104142030410080d0841e542c1e0701c406170159201e00c003c54000b8030142d0240341d2290300c2210300780001c11102241e90503034505032016000504028010300005105000c032910108041914006440c910fa022461502c23005120034810b950208009 = true := by decide +kernel

theorem S284 : BRFrame.sub P3 P4 TB 1680 MM 255 390106182 625 390105557 390105571
    0xd0501060b0f0901030f05010513020702040b03061006180602070306022821020f0f03 39
    0xa00400650304108402400802c09603803440c2540c004000c00c0000303030703418009203900d03e4903801501d02c01e00038039501500200d1586140e0b0842d5014100180c0020720206003912050b010900341442603402d45222070050320203011540c1c00c202c0d106d060340d030843d088212032850400001d440c2e80890000521003070b00000d10112000e00d9124030340000c001101c4540c0008107008c03028008210404003c180c0c3c00c1c0c180e44181d0040402d1003650343c0c60150a090a25146000b0500030303c40d84020452 = true := by decide +kernel

theorem S285 : BRFrame.sub P3 P4 TB 1680 MM 255 390106807 625 390106182 390106193
    0x161202120714030d020f030402090f0910180c060f0807080f0f040f0b07030c020c19050d 40
    0x1134645008503401c1026030b045203442200000d004028002180b41018840b80c0c820100c03482031035203161503111389546050242c1440141513a801100300071744018981400401e420147c0c441c0d516686080c020f0082c0401e6800030001990a030109810504c01c28032035000d59030b0030006401580361214000140722001d841120340c54804d2100e0800114805089407003611182c40010f6407100000001c1c3c1410342e411003507840340000c500b42080c061600500c1e0030640303406481c810307548800751402c1d = true := by decide +kernel

theorem S286 : BRFrame.sub P3 P4 TB 1680 MM 255 390107432 625 390106807 390106813
    0x6100b0a0504080312010609050301090b0415020f0f03041b0308091e06161202120714 39
    0x8a01421110341501d4031786030b50507101c1000000c01d10030070700054003000c000504c6003010b11078007882c15003129043e0065a100d840b0305201d182c2407401440450703401c2119448903040c40c0301601000c84c003c145540e6a00307260402c00c17100c003038045000300d440400850820003d1400000c8070240c3c03505aa019503160000100050300c40c01401d142c581100c00010f0713483c00710500390301401d40ca52042e90003241180c40c0ea4000c0303a032900f41404000e400c0d101005402d0205450074030020b152402c003422 = true := by decide +kernel

theorem S287 : BRFrame.sub P3 P4 TB 1680 MM 255 390107913 481 390107432 390107437
    0xf0203070807110d05010e1c0c0c1505160f02100206100b0a05 29
    0x100c0c042c0d030b002202000c603c000100050342c2c0403510b51300540309608024201c5000303440415040c1c03101003003112140c41040b107803030240c070380031051040038200b80f2282d1805c010041e0f401a10f00c0060902d0b01e00941380840d107601540e800941140d06807903139202900745100718101490704070b00044c1d00740010002841c10b080f08600b0400203000d641140c403008100185200d02030b07002e = true := by decide +kernel

theorem cover : BRFrame.Cov 389928057 390107913 := by
  have h0 := BRFrame.cov_init 389928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  have h145 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S144 h144
  have h146 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S145 h145
  have h147 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S146 h146
  have h148 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S147 h147
  have h149 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S148 h148
  have h150 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S149 h149
  have h151 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S150 h150
  have h152 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S151 h151
  have h153 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S152 h152
  have h154 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S153 h153
  have h155 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S154 h154
  have h156 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S155 h155
  have h157 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S156 h156
  have h158 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S157 h157
  have h159 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S158 h158
  have h160 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S159 h159
  have h161 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S160 h160
  have h162 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S161 h161
  have h163 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S162 h162
  have h164 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S163 h163
  have h165 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S164 h164
  have h166 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S165 h165
  have h167 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S166 h166
  have h168 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S167 h167
  have h169 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S168 h168
  have h170 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S169 h169
  have h171 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S170 h170
  have h172 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S171 h171
  have h173 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S172 h172
  have h174 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S173 h173
  have h175 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S174 h174
  have h176 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S175 h175
  have h177 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S176 h176
  have h178 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S177 h177
  have h179 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S178 h178
  have h180 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S179 h179
  have h181 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S180 h180
  have h182 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S181 h181
  have h183 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S182 h182
  have h184 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S183 h183
  have h185 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S184 h184
  have h186 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S185 h185
  have h187 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S186 h186
  have h188 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S187 h187
  have h189 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S188 h188
  have h190 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S189 h189
  have h191 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S190 h190
  have h192 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S191 h191
  have h193 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S192 h192
  have h194 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S193 h193
  have h195 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S194 h194
  have h196 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S195 h195
  have h197 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S196 h196
  have h198 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S197 h197
  have h199 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S198 h198
  have h200 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S199 h199
  have h201 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S200 h200
  have h202 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S201 h201
  have h203 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S202 h202
  have h204 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S203 h203
  have h205 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S204 h204
  have h206 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S205 h205
  have h207 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S206 h206
  have h208 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S207 h207
  have h209 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S208 h208
  have h210 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S209 h209
  have h211 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S210 h210
  have h212 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S211 h211
  have h213 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S212 h212
  have h214 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S213 h213
  have h215 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S214 h214
  have h216 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S215 h215
  have h217 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S216 h216
  have h218 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S217 h217
  have h219 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S218 h218
  have h220 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S219 h219
  have h221 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S220 h220
  have h222 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S221 h221
  have h223 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S222 h222
  have h224 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S223 h223
  have h225 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S224 h224
  have h226 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S225 h225
  have h227 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S226 h226
  have h228 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S227 h227
  have h229 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S228 h228
  have h230 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S229 h229
  have h231 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S230 h230
  have h232 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S231 h231
  have h233 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S232 h232
  have h234 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S233 h233
  have h235 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S234 h234
  have h236 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S235 h235
  have h237 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S236 h236
  have h238 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S237 h237
  have h239 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S238 h238
  have h240 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S239 h239
  have h241 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S240 h240
  have h242 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S241 h241
  have h243 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S242 h242
  have h244 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S243 h243
  have h245 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S244 h244
  have h246 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S245 h245
  have h247 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S246 h246
  have h248 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S247 h247
  have h249 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S248 h248
  have h250 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S249 h249
  have h251 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S250 h250
  have h252 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S251 h251
  have h253 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S252 h252
  have h254 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S253 h253
  have h255 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S254 h254
  have h256 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S255 h255
  have h257 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S256 h256
  have h258 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S257 h257
  have h259 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S258 h258
  have h260 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S259 h259
  have h261 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S260 h260
  have h262 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S261 h261
  have h263 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S262 h262
  have h264 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S263 h263
  have h265 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S264 h264
  have h266 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S265 h265
  have h267 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S266 h266
  have h268 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S267 h267
  have h269 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S268 h268
  have h270 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S269 h269
  have h271 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S270 h270
  have h272 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S271 h271
  have h273 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S272 h272
  have h274 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S273 h273
  have h275 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S274 h274
  have h276 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S275 h275
  have h277 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S276 h276
  have h278 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S277 h277
  have h279 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S278 h278
  have h280 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S279 h279
  have h281 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S280 h280
  have h282 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S281 h281
  have h283 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S282 h282
  have h284 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S283 h283
  have h285 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S284 h284
  have h286 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S285 h285
  have h287 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S286 h286
  have h288 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389928057 _ _ _ _ _ _ P3OK P4OK TAB S287 h287
  exact h288

end BRData

theorem solution (n m : ℕ) (h1 : 389928057 ≤ n) (h2 : n < 390107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
