-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0951
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:27:33.730368+00:00
-- url     : https://prove2.me/submissions/06cbc072-95c6-40aa-b7a8-880263645caa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 170863309 ≤ n < 171043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 170864559 1250 170863309 170863321
    0x30b2205010806072312010e071103030709140a03080a030e07080304062a050102030a050f090d0819060b03101d010f030f050f010c0e101b03110f06040302010c09050108 74
    0x142a40d058403004804002117080884158040303881030b248511164480300001040c4944a2504180600420f80760740141c111400043c645034001140c0c4407011809a020404c000c106d264210300000100030800310081380c4950b581140b035008107a2400000c0d603a4078440060030b00411012025000442c01142464601740d0010241e0010318610402108460824440307a0301c903503a4410303005d038080025900e80c6071040e01c400080008a8101c0c0e103010f05e2a000c01e00c030000c0491014205151070743c48504641c2ea0744d807480d40c81d600c8ad259007031603190b54240025580d0203100c0507602400301d01c00348002040c9030115440003042007007a0000c084049200410282c107c240c1c8840480c1da1000e0000008000c80c10f205003040501409400b8550a04800340b000c60352001030650051012907104c01901c1410720b0407114445c4800d400030458440e407220102013802a012205450000811240c900b1800e100e0181442070985d41140980c0d10307444031030740040d0007103083c1e00548028a0003076120300d014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 170865809 1250 170864559 170864567
    0x20a030c17010b0c03071e0c0608060a090b0d02030304030f0506013f020301020307120f0b0d060504020301020c0a0309050a30051207080301080c061e030601030b220501080607 77
    0x10f200f0300b1400c210000b03554400032028002d903111580c003d0400071080c02c1200f5084030305c0510345d1003107540030040740021170400e002780d60b15809003c01800c2c0003e42400d024518008000c02c420b42039004043c400414016074042004202542c40380400b07007200b10103032802c20324128040e00000600c06000039102181c2c0324a13400110040003803c0c01442c001024014000c0c00201150043c0d01035000008001001e50004003586d80324007000401c0043e01040c48040c0d040b12205590709600c403c441071007501260540d00819080381c0001c00062a281c0742e2000d2a18143d5141812000b00e544c41204003e145807203401c10703008140d07085041d40d440d00d00590000c5005080300c244d50340c0308044900c9400b03200003045100e4003100002d440707580d40d442c0360915a00300d0700244108822031280180d8001182071400507900507a00c8600c84e40c000310005122921241c1006003902e04150f178a013118196a50b031014856901828180c0c2014240c010000540907104142c00482c0c840c3d20200074880540c0d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 170867059 1250 170865809 170865811
    0x3230102160b04020d0f1a0a02041206110408010504030804030f0302250f1e021207060206131103060a1a010309080d0c09080106060f020607092702070203060a020a030c17 75
    0x3000b401c1c200241c3c1c40384000b07102e40004600103455140b28421140400c100c201081c1091000b03040364101a40c1e465401c0c20a03485240210342480303460300540c0d0001101d9030044100c000e684265141410345800c0d07860b003143c104850560009408009000c103068010036540e1100420786425891300c41c04060380070903d030901602d14004071040c00040180554031011070a81d070b51181d01c0d034041100105240c0a900440c4006922890641c210280076220000d1050100d80154002d40655580c040d82d5048001d0030b2142658601c2c600d081301210350f54103020184c804e1380d00350703000200580080c5030240c1102d00d91591505042c5800d0160001c18254000d9540460001c1000304031248073307000171556036403981c0c0254000d40c2480301c08100b441e0800c03014182c1412075421030740c20b07694511003181c03024118890b00c0e401100f12200f001c40203048426003c00306110f21005898491958003013460084229807400d401d65000c40c1c1150566818000c42d411441e25241840e410210b040112403007040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 170868309 1250 170867059 170867063
    0xa0819090812040213060e100608010305100213080f21030601020a020909030403061404030f021b13020f070b040c050a0e06060307170f0a0c05040b0901030b0102160323010216 77
    0x842c50000f0f0115551004500703540340403440c003405031541d9025140e40d038101c1030f2562001c0c05d40142002c51110b01c1a10218103c3e5000b4000b410030599074211800207500c04d0714030a00042281401007100c0b0001c0050414503103000c1c00a120588180214a6004244c03001004c41c0f0308041041c020030fa81e0005030b9019064040707541e4103260b11501007280c07640c440e691000300755a0900c107a0440d10301407030304000c2c030450198a9501d130121329844101e803201913190440100010101c0c0307041007410a5000c109400403500c000501d040546240c000c40398203c4281114401200d0b4104410442400046c40044c24151015002c217802c103813041ca02d0220080c0791038010741010000549903481a0031003203090411300c3e002d010a061450903001c07425000c5490100130344c1005c040e024941d100b40704880031541e1002089003080170384801103025142a80055045210300382d4095101c00d24041a5001984560014144c40e6140020040c5520315070040d540c0d02d034818000c103a500d000c0014120346c465 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 170869559 1250 170868309 170868337
    0x50a0b120601091e03051b0d0b040203030403060501080102190203030106171e01080604060c14190201110f070606080610170f0d0f02010b030601060f03110706020a08190908 76
    0x541c940300121a200c1d241e40c400c000c04e03040f40c020003460549946404007a2801a0151a8039185a00081d1102800c1001940d0400300918085001c01c12220b0000e411520040503a880c0c00d503607445040c10b81e0420b8100c0303030181c1d500080c01d003510710000314011020f030400e002a506541c035007030020300070b0560340b81256610602070b0300044000030740500402503c46412185c0340103503100c0c54401d80d40c500c1184c2c12100c19240c444503084650055000030003403210400001d01c2c00c00c1a2824a688000c01040c0f5400d564907802010012100d50300541074a0030700c9403515031181034504155054925a600690383c3c0e40001c020301c44262203981807041071b10f035603100c041000044c800c201440c0035083c0b602d6402500440c41c1e034494031680725203a0a943d0015600900980c00c141c020191078400a108807804103c01105035602c69000c0e400040c00445280b8006050209a4840c001660300c1250610300080400b000c001030100f6030740100e8003440c004d007420800b607052a514441c0510441039005d40c42 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 170870809 1250 170869559 170869561
    0x801212a090f0209130204030f030e01021c02030a02070b090d0f0201050c07060306031103030a0e010315050d05060a060602120a1218050d030b01020a021e010e10080709050a0b12 78
    0x10068a0341060003004212010031650341d5541181000390071080404e44a019150950034100d0980d00a54003501e8006003201852122603805549081c0000030450560040326500111090f12401030594550a500615561418004024104201a0044040318100313120005582c2c0f200c0104a0403a60301403255151542c0700e00040ea59030060200c807218520444c030000c12002d0b0302d0f400200860380f146940380000980c03601010344a001e18414400040d1009040306002e600c0f130740040c03800854030f804c00d080c41600d50011480e0851000016101d95021100340240c154082c85200001c0600b44040c04003010301440f84000d40c8039080300b079401c0103e84200500901516030060f13680f080307889005074080b2014075280c2d8803110341d103440c0c0011901d001e0820b00c4550010a240400780c0c0c0c0145203030300c008004000b8941050144240754100103820720350301404c0e290b903d03400007214100d4035104400e02c2d01010003030002d07815030400c900824400e90104880040c15044d10107040f05e608028030f05d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 170872059 1250 170870809 170870873
    0x70e0604020f0a0306060e0a030f0b040c080f0307050706090807060f17042609060f070c030206070b010905280203131205130509010e040f03110a03080121 68
    0x20303002d6204104075910700000d11980440e015401501201c00c25104c107996840504100604450980700281c00741503035011200000703200701c40c000d501901c070300721401101d52500c642078940340720f01508840b554000201c00d001c2c46820001c80008007058030704070744010b04010300c080c0c40c0e00c1c80344541800d1040c1d88049401c1c940c003440c02c001d098000702d01c000041e45014240701ea03410111004c075007550a0740309500c5100307a419104407071054402525080c03a083d0001c0c0c400d18150b10000050f90482c0c6098004001039480d1002400e40d2030040408120550410103091300700c800181c01100d0044410111801e450700a28104190358401900162207940b0850b0006188c154103100400d12100e4034142100f194218015202c40e210011001030307156110010311100e40028042d18000c03484690005001030088080d50305200c3c840d25281e4510382c04501900d10380040d101c42240031a440c2801403004001850380101303034031a20001448021219240c2e804641c4454441000406085030300e040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 170873309 1250 170872059 170872061
    0x102040302041b0f030c081504020c030a05070b0c0c0a02010c050a0506011e080c0d0803040203070f1508160c020f030a020a14010f0c030e130b0402072a0602070e0604 73
    0x40155005403082c0207a0002c910102c01c0f800b0f40f10b04040114403801010103c180c031034429840c1c0041c95499540ca0354840000039480990984c402541c4181c0801c0090741c00c860601c064000c80c0070300c0e20355079181c4100e450601c00140c801014100151030a20592070034070000100d9200d81038080c00c1c144905441070400d903080010f2641301070018810785000240708854050412031740d10f10442c1c241c8100303468a0080e500c4040c0c1c03e22459009100b21080c40c00f041c0200000c5412030310040840f000f480c1e42d42100d0400e03200395405a918040c201d241646416003000780964001407074860b22003540d11045015000125100e006070007481401c1e05154151000c000019031350350024088140607a442c2c40007501c841c00040b046000a41c1342500e01c2140e80110801c82c121640364440403078104503007040c4030400032180561580b01c1d032981d0031007240352520f10003492054080c250303454604550039180c00030500d2220f0102c20501c400c50b03003004519800f0a0360f0050b9060001a00480c2c5c94041c00a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 170874559 1250 170873309 170873317
    0xc0403030518120a020a090b0603190e0709060503060106260a2304060606020607080a0c2c040c0518120a060606180504110a030f1d0106051201060b04170102 69
    0x10f4211a003514068103c1000107404040588202c034485800c6880c3d0164005445e16458043e8109100b84007017132140a861074000c403100034209001449501034140285005100e074891045617540b0380d014042400c0500c9103034058903c0742040302c0002c1000d03003032014020700c80007901641c40040c07000c510480c006401c01b52840c007001000841d2080500f07051542241c05549c200c44052400500103091800031a4562240c075480e00c03a00071981d40c0183c48006807980112000c00c00070041a03c0e0840c031304100780280c14a04d0b07001c0000c9080c0fa0f5000b1701c03003211040c005034003e100c824080313119240031b8105401d020140613130b52104c9c080032024080b8503104598000802c09400d202c03020600076480410030350350083c40c980780b80415030349005210803180c5482848201640800c01d00c4180b500940040c68504050540001c090381030755180030142007000d0418000d65100c1204200c60b1410f014800ca1407040a4001c000c4145482c035615220b03c01e501c2189443c542c102e00401d5001000c1d4151 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 170875809 1250 170874559 170874607
    0x6030c0201110406091403060f160c0506161d0f060c211c0516030c050d060b0c0c031203060f06070f260c06060f030102040315060303090e0c04030305 66
    0x3c2d11151103980c0038020710404e0044050152440206412034600000daa0340a2007030203045a110791540c8070100040d0301b500c84020240320240c01124000350040100f5442a401080700e03501c07840d0840c100400014241041007200d404d5180840030035900e03d8509414910201c0d02242c2e6040e02401d8a418441e0f04c043d0f00f8012002c0440a403042c22000c4014850307000c00c4490340b55110807a1109030100d0308161041c1e0f20181c6c507100409403040c041c2d031201c0030380005800e005080c50451200f0505a69142e0010304840c1c401051482e40d46800b00030b2109503103c110086d084110a040c0e6100040c0070061a551040c4a9410265440d486442c111080c81c0d0300500d00c03842e80156810108039543d07070700c4c032480da558a46149800c01c80070700105640d440742103000074120b10313141c032810095400c0e40c12800b503a055600300070010010707060090509480015010204d44030386542000b400c010b40c150301c400961406401004511b072800411030702925490704200303480e041840789010300d410140da80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 170877059 1250 170875809 170875841
    0x130f031d0d031e142a030703140d02040503030c1605011419090302150406020601050904080306040504030516030309050c030d0516050307020901090506130b1509040212010e0a0e011506030c0201 85
    0x141c41101410f9140c10300d402070040b02e171408a0f103c44166140da900c240300001d000904503d9410000f41c1c1130000400c621005140007508054882c80080e040d540010750100703c950004502c2c28201d010b090112004013800d080181c41c01d4024440d14407503114504400c80f6100014880440d064003605082001e9078000d40303500da0880959900f01003a40c0103010701c0d0098429640005020f103001d05c0300900c515441004281140c8902d01400301804002d0070803001e0100c1030001910000c0c8031b006030b05901d40030795000301b40018503045c407d041c81c3e03858072081c0c001e4200703864142c40c1541040071610307030342104244050141c0040c00e03c1c3d821401400700c0258001c0303100b000010050100d40220340505021034441005e01c3ea09003403403040395110786a49800c034040c0c2031300740809150100a4602c8080141015260205452a90803156030036006051800200014000818500d00c1b0b42c0400c43d84030802000300031000068030150401ea8481c440c1051380b1010350cc2295440be40040c0b00384502c2482c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 170878309 1250 170877059 170877067
    0x311010e1204080c03160302100324230108060118030203100f1a031c0309050703080a0206090303060f061605060c040510080f0a05130f031d0d031e14 66
    0x854503141d440740c45001d105100307040c0119100c0c40c002c148942046c51608202d09000c3c40e40d800e0100b003442241d403800a060b1760391400c0a01c511441c034481008440940e0315040349040c100310310840003503411013404d44100d00c042d0740c410381d030060b440f160040707401d00300105610b006410756448101c940d040250140208805042c04c100c440c3c01010703000844580500041070b85a00e240c101d01c800d030a5085d0b060740009103c0d2a280c036141c1800c7c20b03420052a0105540d03019403072b11494500e055108031078007c1e00090400c03560740d06208a54005126001a5103103003490000624901d0a84012503c0380e0400030b07104000c40100c0a080e4003130781c4e0040948a45280410307e480d0240c10901c24940104002d56440305031501c40c0032260312814280034049040c0c0c40c0d000b003003801854004d00035091b620080044901051211002140d00e51080c1d540890011807007100f2070401c0041c40c01d140c02507a038802c07440c0000e034005002d0b005450400202003035031141c489084034800740b012144400b8441c001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 170879559 1250 170878309 170878333
    0xb1b01020a03091205030601090303030b0111010e06070e0105071502030c071a04110307030c1530150311040507180b03040b0906010e040807020a03021c0203010506040b030a0311010e 80
    0x382054540501a948560394151003144c140c2d514441181c0c1c1900084500c5400e000281c003d5014280480c4185071802c0c8401e10a003000e403c550000030110f034954064806c100300d440c2e0140d40303205418002e103803660a1070141c1da107021a0280c030176640143d150300440040ea1940e00d04080e906015005260451410724458482e016040107940c1652035100003d03c0794030300e040c000303406002c44e580a1b2170440002e103000709695002040002d001308200c0c01c46400540c062412044110050340701c540400b5403904044040200d038020b00107841e04448660080011030480c035407400040c001a10003113030b243c2e22428200c4549010781c8001011000c03081002c2403005000d0082c2d44154031801d1022420340390b0140855480d8000d1190300e1589611800141c0000d500d2009080317600d10140100b1209901c0798000382010584201420300c1a445108480c2940b03000d014103600706209407010044031200c030f80425100c803c80c1c000070313061200c040a00076034000f0943c081e4140070401c41c181c5100314504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 170880809 1250 170879559 170879561
    0x9021c0501050a05090c01030504021201050108061503011806090c0e0907060e09010f15050705010c080a0c030501230303090604033f0807021e160617010b1b01020a03 73
    0x2501914190318180c00126040e450340f091364045e011640040072007450b043c0044014040040c01241c004100c2903900700c40302c00034040c80380a0820030010740b066240c80c5129030312421030184182d110360f0400c58003903800c0322416145400103810100200b888941414081c928844071303400000d040034220104001c40c0ca000c10881c054030229581c60000c60101e01c1040342e074a4080c020b40da0814210b00c000c100a10104209100700c40550404a04100d82d40d1038090840721480442c1300410b09a00c00c10582901e20700c030b414500d1025041c03c004650429060364441c0700041c151a4400140c40b2000c0c003e69010000d40e200d071a0010b10003583d581d102c0c038007004a09064880800b605a040008240c031a5420340c40c41850045d0b100008201c08041b18111802200075250307206502505100f1501410781c0c03041e0b4500c03c001c02000307100c80c03603d0002c003248000f22a8400070400610141c01c82c8441c1918500340c2c111000c1c42c1019445400b060400c2030b0440c84075546502039880054004882501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 170882059 1250 170880809 170880859
    0x1509050601090f03020a21051603020109061806050c01060e090a02040b09040803060402030c07050f1f020a02120c010b030601180f02030424110a030615051306120902 73
    0x2030303031400000c41d900d02040783c19042a020007940a170404006001703195040d0700c0035440a644a1800c200c0341503684070a82405d183c03004903080300c03505100c1402596001400300c00104554076181d94858141481000c40d0319003405450100640000c08810020007504100040c00740341c07804691038107089801543c0c0b245101d0040b40110b0030007074030f00c0d044e00d004550b45100d0ba810902c0707030b480c0d5038809080200039880241050f10101c01481084040f07101080080c3d07102c131180000341800030b0007440760301c0d00d00e0100c603100100a004210101060b640802c40140e03041040d0780307698607007070250423040c098165600e17103a4040c0300c1c14000046c076800c0d540722138801c1c0c0038440c400c00c1200200900e82090348001c0300d0142c42c42864800003030000c039035002c101c0580141481c00040b2001c4840150190758400030f03001c1c001075140d400c00d20412188034049001c0312483c0c01c2541c5080b2009400c0c25240c1050b2045605003d030003100101203c406421030a81c2e02c0e0b000b0840307040c03407103130358003503580c4042d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 170883309 1250 170882059 170882071
    0x1090503160e0a020901140a050f0a050703030e0f070e10091415091b070f02031e0c0a15180b07030302041706070801050d1a0c040806090a0206041404150905 69
    0x4001c40210f26030001134821981301580603582d10801500d4540f00803465813041d403400c01002800c004074040000d0540c041e042d00000ca581c0c003036139801c46040080648091211400054002d540f40c0c4401c1500000c00a04442240800b0724440d039503480c800f0101c2e07c00d030b03000d0f60780b25080140501040400014982c0b05800104c02d1840e0b04625006111151004960405100b480c03405480005030300b0344050074000748a0010340386440d4103a400700b0f040034800e110703800d06104004c80d2800b010380300b40840c826402056415401042c07500603404541420b00d180c03a018002e012000d0207141c4618800c40300908880803c49a0703860007498001d000754024808c02441c00c0b10300c2c3d4140d01100001c100d142c001d944603035540e42c0603400c1c0320800c641544118811282c3e14200c0701d4040c41100032049840c41070b03040034801c646640c076003000c90f82040c0008201040c3c82c0c00080d001d2006944540c00d4509440c03d80740e80c0000c07008088045001002c21400510311101e001c9000280d2050982000307104072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 170884559 1250 170883309 170883329
    0x23360c01020f0703120503151002070620120a0908120405090f070e120a05060a09051908180a0e040b090705060702030712020409020901080703060b010e010c0609020109050316 77
    0xc001840400d403110f0107404024180400b00c6a0143d1403841030001c0e50704803400d00d200d10a40141e80001500402e1540c8285004da00460301c10403c490b00503a01c640c815140741c48a150003014040100d40700c01c0910500b0350303c694040755808845200d03654020103081f001c0c4c120350320000f03211103282c225000391081910403400000003503120030f40790356410300031381a0343c0b503558405070310500304005141c1c8486064440c2c49020900808207900700a900e0117840503890002c0c1c9a031071402d185083c448020030541034040c50074400301c00039070083e0486210180207a400034148007440002144032106e54482c0550100d000c00340700034055281c0000e07002c0c00302c8008484003647c0d10428000c19009485d0040c1d89904414400c00410300020940035200e0320081c4005030180c4031350f00003a141642038221800c580d003e0442803003001707001e100b4003035078500900341616000b9550000030300c55030f00c09000500154036a0002d10031640190340340b130f018003001015125010150300084034281014480c4181003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 170885809 1250 170884559 170884573
    0x5010905060109030209131506060305160201020f0a030506030106090c030509060601030c050706020d0e0111071b1809030e060a03021e030928080a0503070323360c0102 74
    0x90740c020f24000d000c895000d810240d02d030365402c00188101050318420f5072150704000300e80c40c4030005449864050521038400181500740550481c002c01c107c00303000c1781568410000402c106004800b502c16003604ea04e0f012440ea42e41e00041390251100e6448280324509141d0340400d03094040e0040e0b880340c1e03d030341d04540e413660b2044011003d54880d15140c1c0301003074042054101244d101d400030060110007000105146900322003290854000a1100c0c4101101080003020444102a0703440c241d000803880082c018284070f404030204e20549001c6580541d60703200c002c201401190300c4528424000d2a250b251000d602014020f54414240050101041c00d4075980041411080c0c84c00744040707d000b0884900920584607503070221554000e450002e41040d0000078002e44d000704030a00c52907441d00e4413420804c4000c0c0607201d010740d50f1202625800c0242d90343c10a6803440960107644002501401c0c0c00403041c0c0701007441001014480c6040c00e01080030130085c000741200c800c80080c1c0c2210700d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 170887059 1250 170885809 170885821
    0xb10090f0c05040b0a050903071d010608060a05130f0f02031008010509030a030509150a150b0c0c0f15030907051212031f090903200d08010509040f020d0605010905 72
    0x441d6055080a07000c00c2c020b100601c8070b89041000b0381300210325401c02070f180c8100180081c1c075048040c4d1208000d002c40d240c03a0740c00505d030261035900411070b90614071120b05010b40000c0c0940c6450041c14024451044441410542a001099040704000082102d03403030308000d0401940c0102d84080382ea0b001d0100004402005105d00e902c42e07038a000180d801c00071210400c0b005480003405ca00e9840c4540e1804030100d10004440d28000e905100000a0040c25401ca0805100e0180d21060380203209114495001c0004116a414903c04071000450540c26400189001c05400e0000001043c0070007000001d2000044450036104222181020440300c401c45650710507507a098028890420b001245999440200018150400031a8111080d0326064100200e929620040c3c1c00030b2401e14440501c1c0d1030710248c1d0103003080d0300009403556030b403003204c0034007002c4061242d24050103901c2c00041c10700103403800c16900e01c3ea0003009d201c00804030b400e0082c043d043c2800b0300e0060f14a02408601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 170888309 1250 170887059 170887061
    0xe0a050111070b06090604060503100203160c03050a1404120f0611041a030a0b0d060c090608010f06050d020403080f07060f180201030b01030e060702010c0e24070602070b10090f 78
    0x792196102c3c0c0111040d941d03e00901400e41c03006030075035030069218140810701d41e4040c00800c10345108540c0058503417600c104558141e801c645407480070b104c1c80c0f42c040d60110b070703110341154540c400700e00702258030404110140080c0d00c00da522600d0904618101d15080013039040d04410507600424090040b8020a550001544507901c0707940484c1c004410400c540917082000340d80d021034482c00001e8104000400f281402c800c20104440740c1b980c440c0000c0313030729401c110b00d2400340c0543d14240c5034540c1402e00e151001c801d2401480305005021071003407410085901180c002d95841141c00c1d44a01c6081c4618846401840c400c84210f81060004140e038440e510482c8440d41e81c4031004070169240c0c1e001580105003600c240741c105a120300350100c04441c200542c500a01c200d600000780005031120080ca940106400799208181d86c181c1101c00d078603080000c0c2c4a9034840e50410b60754140b1072608400a109104000300521403079404c00a0b030710005000382080340d03541070041c811100780c10700e260 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 170889559 1250 170888309 170888317
    0x30a06110703120c0f0c03180b091806031e1e01020a0909111b0307170a0e0d0b0a23010303170604090c2c0c0c0d0f0f0c02130e0a050111 60
    0x4800076180c4403400c5481752050301a4a9454000d00b081c4c04900c007000001c181003031982d08000840c8a00045e04401800c001840e032142422821040710700d400e01c103001903110b5608455062005400d41e0f040d150005041c00714602c800702001044c01c01c0044111303814040e420840c1c02001240e002800010400031501407040500d41c00c000b01341c6030020040915908a080740455200c9200038040500002c80000210043c0c003030000760140c460694000040c440c030200002c00e402610f0a691130400070751425049500001e11030b9004c1448400000e422440031609034844000c007042d50000414103400c44140a000f01e020548088035648181c103003c19580c140c44000c100c940310b81d008000002220140d0700903244e0b5044030240b810703c00344000f0f10700e074010358182c0800180000c440c41000420010704a0324217080c1490102c07021603c0c40540000142c0364400148108009010115a0740244100c041c1030040000c2004500100c07046641e0040613008446075860038032554208500c402c281c1d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 170890809 1250 170889559 170889581
    0x729120a0605120c01030507030608030a0c0b06060f0d0b010507120905040617060a0b040e030d0f140c070b06061306020a02030f06010810020f161b050f010504060c02030a0611070312 80
    0x20131415548800460003020000c021504142d030b502e001044240303085c0700900c1049425580d20000c040307a403c01c502e4413900605401d220384c0e820401c12045a0348a002e0b940078001301c0c0303400510030700d0f03d8005a4451103141d4000700254802180403480725007120180c0140ca000f5102041800d4894001400d07a04c0800703001c2d180790340900c0024429034003a4000080c3c150000e0004a11409403032005072545c2c2026029440282d01c0d04400402ca0385280b054040e00e00c80c40c4181107141c200118041e400340f113a0100603141182041c000341d840c0d1552011200e01052107180c03160160742d07561009480d2240c05904a01c640144e4101e042061000035010303043c0c0d2607100181100403c1d60100c07c000358010820080902d50510558241c4000d807202800755a024154034030780c8041101c54000c07541000d030081881804038010007001039078410141d0301906c1960600d114030200e03034000245000484900100142c0c00c1110b440450b0f20804047e000180c800c1d00c03090554682842e81034140c650300112 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 170892059 1250 170890809 170890813
    0xb01081507051b0738130308181507030f110705010f110607080610090602060a020a0e031c030b120c010e01050f03010e04030e060c0729120a060512 65
    0x10300b0548181c408243c01024204504840015a940000c00c03600499000b5a90b866800c00c004a403603001da120440d8410785040300c0840c541004c8911194806280c0c3c080940080390106111a03a035001220940409200420400300442e110443e18610b0380b10354400c9002548014000e000c65020340002103100780440050aa000d0602d401120003003600c21000d000c00c000c021a074007844030f080c480c0358002d840d5a5200c8a0900e4951f013400583c14080d1418030400c19041c804200300ca50101c1d40b0352b003140c080301d00560340d2a4080300880d0540321804910380e15015030040b1582c000500c5510003030420554406000c5040b03a142009100e4080310700d049280e40056554218962103035030940b102210506109060101c181d80e82e000c550800d800808601c2458001e000c249604200741c21816141111b0072860b000049610070f07181c1c04144122042840b0750403a40100d4001211001c5203526840900781d2114451950708120800c00d555040c0e5851405c400030a880c2810000c00000042da000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 170893309 1250 170892059 170892067
    0x30807140c0c010e060a17090c1e0a0503070b071101120e010c03180206090411070804090e330601030618050609330103020409050906061305280204120b0108150705 72
    0x8071f001104000c02d03001040c010103485624591760140c004070022008117000c2040d0003070360240521840e4a4008920039070001d10100041c0e82074608642000740c0c07102e8448810f000d04801640d03881c2c000e01850740d620381007501080c0d084a0540c405920343c1e00660301400b11000303041892090000101c0041d4010404001001d9181403d4106d03c01c4c0604402c245407500b90152524042c0d40c11540000c2400ca4075030150416141041000720302c4d0030310942103a01842211109a500c01034040b154041c49250140021402e80c080e5224800401d10242c1f146414008802c40600422044841d40d200d80c1e11240400c0040060341d05041c07003400510030303402c110b9104044400c00c800b0445090303410103400308408150740205007e4640034032480d00081449003803a00400048030070f80f80260048034902403c003c5c2c2c295440a40070b01980351106100240d004040105000e44929040769815480c9058920200128801d085048440c1c6500741c0e58101d0060420307210460069030480f00182d401e00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 170894559 1250 170893309 170893337
    0x9020c0601061b0b060f210106140901030f11030609070501081501080106050d02070f03090e090f1c0c1a3304110d06030302010b0307120b0103030807140c0c010e060a 73
    0x5044d9504848000d140342c08807690710001440d041d41401714030013240c4402c20400c014410034003845000d080340c000c3c0b4104a084490205d0303000f03981440003400203c0041200c03010700441c05041e40e540760000d02615254502031662a580d541c2c54425a80001c803144009038110030050002c44000b50160f40390011079203407103000c076255000004031a0749154200b1112000a01400d21035101a1003038982d41c011070301d08040d5442409004207801c010b50031001d150808800d011801c200c030100007a944118514030240d00b00e984046448005001661007003440e5401c502e9011041d1043e090b500c0c034444200039803d100c910b01020800303100c8450a0401c0c10001030702d002c0e04071585115052040c00d040070541e40405058904560003900540d640304203102c0e031810288a91400303042c0142c21202000c3c290341e10004071040500c00034041000117030200301520710039043c01d134000d80c1c812100b9403200031722a0101e456400280469020405000340b00c44d071401c100050340c002e4140c607207424032171034002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 170895809 1250 170894559 170894573
    0x121d013b10150803070c0609060e3003270a210f0218041106040b042c180607140702040905030d02070b0a0605010206090a030f030b0a09020c0601061b 66
    0x740a00d2000c0640020080f8420a08201418201c4d006030703025520b440c54503001a0075108250461000c00241000001030350301c17000303000080d2101000421403003803030720701d00800303641c4070340040c80c05c203020001d40d5000c03240440280710f04000891072121034201e183d40c1040801800d40c4500d54000614244074100880104142000d0702e01601200c40710313241544c0000c02c2e0b2200c440c442e1100469010030300062040c8031002e040b94010954441d4a8241080000c0081d40030307070300c601c0e01348a00c41c0480c44012031155404000c11268415080312a00b07000480d2030a80340e20700c1d246000c901c105e00000744d5403407040300b91100b21080da200c81e51034040b1507001c0c08054140f51100f0780d007504c410490222410300d00d2004200c0c141c0620201601420100c03002d0042e5001399005604640c001418407922843c04550001da00b9414200840d2102d84554190042e01074001216804040c0c4180010001b001c4e400400c900c18609041d181c50b44e88401007a10008047d0001000e0820103900c414001061 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 170897059 1250 170895809 170895821
    0x60d0f0b0108091c3b03010c0909020f0903070b030405060601031505060c0f0609010b0102100b03030a050c070e0c0306010e04110406230406210903121d013b10 70
    0x81c602d00110050518031000144190064180c0d4400464908070102401d00312510a0440740c114020300010307400d2311005262030003c4c002c2c030b10000d60019084243c000c100040790203401000d0107540410341d80b5440900310780c00840e020340da140601800a1042e6109104a802440310342007124211070528040c0718454201c04030b110900d1286c0c60410750b0260381005200d12035400310b0004035500d24090300090500c40c01850800caa6070403c40d20722115030700031050b100c004989140c19503c80c01d00d0f2030740070b140c030b249588118103225014052040e800c040400640c8140400c0c0c03100702460391803800344002c4072981602c48103281d200780010302001c0c1c45804854501c142800101d1400c00c045400c044290b40680e0100300414908003207580c8440500c20030a40c0210312410802000354540c40281070355034003a50191146036900403040c009203100d4072059514081c1c034004c114041c5030100040c1c2e02c0c1c0c4100170440803101140d6030040420f0703000b00200003009201002c0c01c11096002c005002802c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 170898309 1250 170897059 170897113
    0x120b090403050a0e030708061914150109120c090e0312070f020307020405010b070b010f0806010b07060608060406090c0b0f1b0705090a020301030b060909031e09060d0f0b010809 78
    0x1070344c002c9030b8181da810002807001d001d44c940a003c4c00d0400e400380441c1d1542c0d42451070441414029003e8042e00c003205620381c492600080a011002e0000040b503070000d8640080c805c0102041412003803145e0184820103482000383e04012144200741059540e0017902c0040c180945540001400c040c411800408699140d0040ba41040d125900003003c0d030b4000d03003195a1040c000300d2120140329080c0081030050101c8507444400760300b004002e1b51200c2050090004038400052200e00700036140d44214010140300c000e40341c00381007a1510038007514030440c041c1d07042d42c0300144c0490b110b22450b048580140d0000c960524281d450119003541d800b140e0b081001c0303030041c1e48c0c00080e80c3c1c68940180e4868510000c0040c0daa605501e440c0c4038412018103460300841004040201c003000010407110350032a550b281000c08442d80b1008c0b80180320302003002d508030700c0103d07a06800e030190313421400b01400500402c0c449521210700445054000b29180819580401050345241c40a1a15980048 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 170899559 1250 170898309 170898317
    0xf14130b030106060e03010c030506010f05031902030702010c03150501200a06060b030403030c03090f0209040c05060a0e01091401080c0a0c050d050306010f090810020f041a0307120b090403050a 85
    0x29950100003800c4440399070100307000c0b41d080d034443e415606d800e00c184400449507050411460a280000a0100640a550000740700d80007001c00c6403100c401104074445090250f0940d564075102400034041d0055180300c8001c02e06004501590803001e80d00035054a2040e900e1204107160030800d03082050f05451505058068001070030080381c0280212006003c1e101401c60703a80c10540790090803254501a4281010f103040070443c0015144216880031740e8048800b00e0851700c550400c0c8204459aa00165200f0800155aa04150071408134580401d00340c82e09a0825501c14001300d40a940e00402c1c0c0c001002d01d400600480030803070281022001910389078050001320341d6414585003d602265012803c040200b003650769106211b0803002c0064034200c90100e18000406541d240342c002000c000a80210744001c3c1120303c0400d4500900b40c01c40c404500540206500c01598425207032800040c402000c04440f42c0c00ca03010300c0b0305001d001b03444200b00d80d0b2561011511908100c104000308 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 170900809 1250 170899559 170899571
    0x16060e1605090c03060d020103020708090405010807090f05251b06020706051602150711070308071209030c03020108131a0105030c01020a0f020918030d020309070f1413 74
    0x11404005018400e9500000108014100010040c000300010440364a501e0100100106512081c14901c550395082c20b000d40c4802c0149401410780c013441c1032445d0890301d80300000601000003e1850f080790b900351400c019075002c03061450140d5038105c8070142c0c441c090907022034282940301c240c80c81e41209860a100964401c00407203090203007400e001e80700c0c19001b250410502985c1d1041c0346e00450300d0010103240c981e80c80c0010352501000c0c8100c074000315140300040e820358003500265005c6003c10003941c946949a00c0c100815030821328050707556825030707091541e510b8000d00307050017680d403c042c119090340d146900444040c03000800b1505554180c9110b180000e505500a0a20002904506030300358105003e00d407a0600028045045621182c1480e02040c5a41c1c051010941c044d540300942d940c50304901c54100c02c855403005c0c0540b000140001001c106640958043e03104002a01c0e207580d546c5038170405841d12030007035154420204000c1d5002d40307820b071000305001400040100304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 170902059 1250 170900809 170900831
    0xd020619020c061b0708040b030615030402030a060f0f02160506060102012a0219050a150209061b0c150a110c0a0915080f0c090c161e0204020d06050f090103081606 72
    0x1501f00307510002c40004080144101c0e403401c05494800101010011420b51400d600020399503201100081c00b400d5aa00f4040c22001c419000f5280500d84038009656608505404d11012150004262044d0080802140d01c940c410b00610508900b00403000d54003641c500c07072480f1f0405480b0020720661080d02203c010701610b00281d10b10f554000c40c003500d1031685508003150f03c000d40c008010010391041002528030354810068640d00c2841c5280841494422b00410740351068001c48507511a000542c24002c0103016401012007122555481c641d0480380220a03a0f180341000ba0075901800d176050a0055080316440a03012281e80300c40210916907501a603030a1441d001c0641c519608005001c14440c100358040c1504501001c22062400d603040302005006c6c9001c5000070300001201c28150126000040c1081d40c6680060086503100031100d031140051840740309040c0240c1d043c012100080c5003846100d0b040303940090200e482d1550b403410661b80c51448040896406c3d50b20040941 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 170903309 1250 170902059 170902073
    0x21e210705030f0a05010608010b0c120f0403052e0902030120041707140607050a060f14070201091a13050307200a0305101d0d020619020c061b07 64
    0x2014858944980b03603207003407003984201d00c00402001d203003290341004010007280b40d0182c111411511107240b0a5120b5042d034502a00b08140c84803504194140801c00c519540c212074002c0040364414011109100e2003002d012005101c072100c03c1c140804007580d81c90100b2150b030031501c1460301c0100001443e1100d044084035104240100b4642e1000102e070a10040c0120300e4003020392458072000300403203403070f00c2d602d0305914840101c454000e420218240007004401c11442500c9907001c01c041c410094050000c10043c101c41000f601c1480c0e0050204900038010300c1103142c103d4020851070b0b001c405445e54807460300340181c400c01518a103883c140c80420018005054114814031803881210407500101e0494401c10001b01e20443d8909802c04c0081c80024140b030034500b140a000c07070f18500170200c005601029042d10005030103100003010040f6400b180280c424048030342c81750440c2c04008404403c038001e851115203258018004980440400d0000c0c02d10b41c1290a24289003410507a1940 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 170904559 1250 170903309 170903311
    0x302100305100909020f040c091203020a0606050109060c0b0601140d0509011109060d110403060c030915060b040509150315041106070b060103050a06090513031101021e21 75
    0x41d5942040c0910b80310b48100c031600074034840c2c4082c0010036940c0c002900c2e44484000152085648540d0100c040e0f00841c401c0d0000c007807081603200c04030418100a5160703448101d00700d80c0d152800740081a10741c096000034050b940395035902c0640700c0d500c2d920940c00b01c1001e42910305000110301408203036041c500c02000050032848011540c2d0038030b00000c038252110318542e1a000310b401d01c00384480d51518825242d03d14660040800c50b41406203004026124640014007030906100c07100d141c1c0f5406400600409104901c04d5101c8180b5440003005c696181c000d507032040100708410800d501e00340d0250368004501240300c1c0a03d04a020000e460018801e250790421115202084240711404410059031282980ca0514241c040d60310f104646400801c070074145a5194003003819401103610030400f5208040040045080420b18411a03140200e0114000750500c0024586c464060017900c000c086031030004000034000b035524205c1500a0b02005141503610b01c0300c10f407140c0403c8245 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 170905809 1250 170904559 170904589
    0x702062a0a12092310020a0503062728090c1401021005090a1703040b01050103110d1d01110c0706030c170403051e12040b09010905070f08010b090405070603050a060302 74
    0x2011360100000c141014001039030a60480d1051140100480d000720843c0d60061044802c45407001200080306d20420396001001d28149c403a000300305d00d01040680c8600001100c5070344c040f5070009503001c0c10640742817080c002c140d86072120b010004d07211031200d80110150705005680b02914101c03405000c85904803a19a070700d80c02101042c080c85010001c821b80070f40c5000d591455890903884103222050188580d50405958400b4580d2400d00300040d01e42500d041c4009100300700d5450a020103001c0000c0e1004030303552070560034052041e403c0003261786a004410107410050702d000401c0d0000c24912040c1800e0144803a511b040d0040c00042440c40756108c0e45405072506c1d26040380340040040c540801c10102e00070420203c035501d04180c01c940c0651b01c11100342455488040d12405031200c1e0000410510034680007103401042c00d20440f060301c1c2d015000300400c104000c20407101703490585000c0c6c007030b810480c801d115061194100940c0900300c42000306040e960f071b6010400c21540c455507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 170907059 1250 170905809 170905853
    0xf04090e0304030b01320a0b0d050105030f0c010c0b070504030503040b0705010c0302040806040f0213060e0609090a03360303030510091a040203060d06050702062a0a1209 75
    0x2402080a20800d660151030007484806c44416200400c07150f803010203c000d00035400c00b905056603961034600c032001a00e14044201c0c0c80d004c01990b040040e1100303003e0103202e03000c1c45000303071244880000d95209440050303655140908c601d448055031000064100300800c40c003000007102246080000300000c00d03403018100da403051740d420030307508558024840c1000c1500400040203460300001d00b41c2e17041904a203243c420507009100103400c0442103804903101d1030030301000168408110710603500c0f07144207641600080e83c444144030740b035082d015002030100d00311145051206034043c4035403021034002e108070710a0810382c50000041100c694402c50019032240c007080286180030139500c00801c01d6110501150b20399000c01d21103914003021380c50180e540880003807650303a10f0981140703495800c200300f00325134201450004d484000480e01ca54050791850b5001d4625038a00712450700600326545814100700c10040d046900321701000642c4c5a0b16220040d450101d9640480001c01e0440610 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 170908309 1250 170907059 170907067
    0x6020a03020c15040506030a091b05090c030405071e052d0f0306060f040b06070b040b1003030c08090d1203020406030f021201030305032502061e06010c0204020f04090e03 75
    0x240c000d2911210080081c010300c01c00d03001c4103640d000c52050f00d0a9941c1120196220354480c0030600050101240c0500f030f0181581e100201000303041e285405071034007034070079180d10b56a4240f40308680c80709a400600d940c1c0410801c010851849415500c0c90b031f140f441c43d41c101a540c02c0007900401c101284002c0a00107a2141105200c2c0c43c440c0001858094481c080010782e0304001a4032504020b209500812020580c03008a17555540400d104800c004c00440d01c0e00024144200d01580845040354004140004540c06c44103c0c00090300301e0f9403603541c141c0b00f80402e80c0e900890307802000b4440d030004500d103141ea00064000000105038105d81c0e0380162501c5c54aa0014103880c4800c4100c6e000d24170400203c5940d20311004d0241c1540c0c2c160504641e41d80300c0d00310494081c010b11100f914502260140c00c0d0000d0b174081059401902e051910340403030414005003181111098038881d01280800c5459001801e15401600e4050800310001d0300703146e5107240741c205460601d0400050381d00006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 170909559 1250 170908309 170908313
    0xe010f1407080c0a0c0c030f0302071a0706091a04050d0e040c080a0b210a1a0618090304081f0c020606090406020d0908041d010503010e0a1b03020a06020a 68
    0x4420050303030100140103040c250400120140c00c480000e010704402c0300b000240c004105000340d0410300c01d1580800b5201500b5503030b0810540603807030018114014002c4400000356540c00200d00e20500540300072481c5030005940c7c1c0d807001042138980c101c0380c40c410100c19020058007a2155441207000c3e00160200241c08000200f001c5660526103100305e29000100c1500da0f44210001d500c00095030001030395102a00c00201030300c4001c8540d159050144240c40044100441c2008555224203003010089401c102c0d1003200010888520b6002200c55010681051355a44402d40015410055926150716090b60300e060800d101e03640c82c02c0c2c0c0300c0300b4160f410110350751041c1000416144007401e031900f03200b4001107000601900182c403464000c2100d14920180e944003056981c0d10031401035440e5660340c4d0442c5030944c00b260f038990128001000041e5400c3c1800340303520700c004c00005805100c03d503680d5030200721407000008045034074400c40480180c5030098400050034840d00103000040e024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 170910809 1250 170909559 170909561
    0x61403040507121202010f150603090c03081306020c010c0305030a0b0111190b0604060e0403051e04090b040b0f090118060302040608160f030c050108151e01020c010201090b0c0f0d0e010f 82
    0x20404d450780d0518081a108000040035081d00c01d5402915001c00c3c1e10030076060031070f41c00a06403c00780683b2000180d905000c00180c071080c0480d4207540035500b2410110005440c1c002c0d05000c0a808140c1c01c20001d2030401e181d601100c045081414054a10f04a401a46181508a001e0081e115031210705001c2809002c0c5075040d80000d04403420322200e0304041c21001e015801600041c2404070100e8840003282c1402113048440d5490303061a074840350365968503c0580410340d1040d0150345001042c1d02103080ca0b21581d00441d038041c05040c00d503481c09055007a0f21813504240702c01280d54a50110040e40c41c5d000f9600101041002007420030170700c03918500d43e6036440d44034203010301c10000c0810000d810f00500004036942401c14180d207130340344103054401e40440d09001e44e1021801891442c01c0b043c1d070903064041c40081e800c9407106120000103900720b0b51001c40142c9034001d50310000d00200340040c01012003200900c00241000300360840082078404112240d03903180d44810700d1328501d40c45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 170912059 1250 170910809 170910821
    0x1b02010f140c0f160506040c050907050307080606030a09170409051006090302060306060c1c020d020712060c030b1c111c020d03140406020a0b0603030406140304050712120201 77
    0x14510354100e03506268408440e1449100f03040003c3c0d80c1d01050030650b41c1440491144015088026100d02d4940307840c10236089203460003510f20901c0c2100208042c00c0c4500240ca10540c2c8607102c0c4082600c2e0302c0200001600010b2000c0000d0361150344c401b00045040b1802c2000e02d80c0503281c551035509003039092003920f10060070808003d031b607024104051913100250000f1643c0542e80d00c0c0ea43c3d100d03c004581d581c841d20051b00150320034080f0340240d0303500c3da2a4014102c10f130303a400d0b2100c04122280491320f8519620a91032411840da5094010440c5a440041c00300c3c4181000543c0d4008200422100491424001490150000341800348104101c810405880884445101d8040d0440f48071001401d6840030703029001441120041500131001c10348002c41c03010903d5150f80e07440038020342c0ca000341c11003106c0004601e000300700729040020964056903d19100c203104800c410b8009400b540000300141e44901c0fa2a02c00900c1d58141500400094059075111140205500000c0d0a40303903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 170913309 1250 170912059 170912081
    0x12011d0a0f0605060d06020703020307060c080709180207120f0e0103050c03070c0512032d10060507060f050a020403110a05010806040b041d03030403020609150c0307031b02010f 78
    0x201594410008150786030001c4225400305000a940d110360010400303180400000610780b0744005090010b254001010303101d03040c0b00e564103000b51203021004a90850042e1140c0012440c89041809180c85e45070f144900c0003070b1100300506110081c5c40351000580200306007008108054441e02c02940d210384140500003013070805016a080080c0720880d10b208c01051007007041107030290041004406d1000f0141002024481038490410200310a11601c00d494000341000640c8034045000805601c03040c40b49019900b0b0610303540c41c00b0004e45003940290300445030142d54402181d00d40e02039105450003402c5840e0b00603121815490541001c84d14881c00358030030f82114008211980c1c0c00042117a00a805880c08501c0c000b808001c01c000d0400803030035010165400422401400d00000994412802075003218100e84a0340d81d0551a03103145080c55114071044070001e83c51460400c000c41e04042030b4600091500640f02002c007400282e51a1200140d44031035134444680300c2400f458181301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 170914559 1250 170913309 170913313
    0x3041d07020d0206070309050a02040c08060f090610030207021906081602010e0c15120a24081b0a031a041704230103090b01090c030c1d09060f12011d 66
    0x3070b1070440280d5a160000d0809041644409240301040000d10030b00010320b6011708240220f0030720312005088281c00300d40040c0030300400c02c0c0d0000300d4984881c03003a0289134040c110900d00f000d2504218065403007030106a801020324150482e03203526200bc1d500040c405592500d00508091103070100e141410841d090843e03050001011003400003240d8401c05d800c044a0a035036810709410151841d0066480c0d96090700b107040100b2122694980140e02200c52015450b04107112129030011800040e00500c01c46510907204005001d8002100c180041002842c05014980c1d80d038822030081054100700c00107901040600007004010b0300c10185200440030a80e041a040c41c1801c00c41d020031003c1303404480901200c40117aa4003e41c80050000e4002001490940e19102d5501c05071000702040e00010346001116800d4a21540305e10504040411079104002c240d141000070250010f4207803580488040e4490300300341d40340e8480c54289840355002052284e19025045502c861500900c040e03a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 170915809 1250 170914559 170914573
    0x304140d05041d060a0b0c03070c0e0c0403060b061303060b04140705070b1801020307050703080105040b060d020309101506140406170702030d0204060e0310090c0603020901020a020303041d0702 85
    0x2469800003203480c43c038202c1e0300f41915a84400000304e4104880d070251029110014500f000810084000c15600d80940604d007161507594044440c60320b400ca51140319081c0030f0006000140c8039030840761800f0030040c4124200350000c19010748003684c6a1045880c1551008100701c9400e15009248444003a4030100c8814a41480081c10070b2190038030092400000100184d44502c6506039161000780710b0000b15128a08010054a2030f888110150b01003459007000240600c0e1602a81c0380000300503140750f04102e400124000650005000e0742c40500482d10091544006403007840c85048000d014808944c2c0b42681c003800c180480f540724000800108424820f141d08540b43c08580c12225410342d6080e40c681000303d04501400150018050000800054883d400500078800e580201c0585613034442c00c2a01101b01c5820000086c480d9025106c10070029000e0380c003501e550801801a100c00c0c0400354002401d60b03016400540300450300340450080d8000c810601c60780640d0900041900f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 170917059 1250 170915809 170915819
    0x1602061305090a36060e210f0904090321050610020622290106120b010e010f03020702060408030706060501020a11150c030a2106030c090513080304140d0504 69
    0x1501424011131903401a0b40b0301d08000c005039809100c1c0b141350484010080c0325001714074187c030703078040f0300250f143c0462a052980c4c00f0040b05089480190161082d240b600c4821070500010740740100c000da0a00c0030800301c20442c0140254404414480318900285924040003049008030145034014115403024041140e026010100b6040086081e5518285181d0901d007103c041c40200340700034040d40f020800e0700b881151085c10701e8140c5250f13440d000c81e00e00701d00d246c040844120300c00c0e050025910314140d8007a5402503040310381d035620034580945440015008a030183e441940100a140e0000a5000a01001d0b100c1d03903000e46003d02c064407001d0002c1c0c441c00d40c400d11901c0d86901c0340c03008041d191050b80100007103138000505001905e46800000300041c00d0320015560b654000c42e9800c1d0941e2094680780f044a095035404040520074070309003c440001807030010a030340915649104844049443c00b001f840c07240384910784001c822003071201c115050225841c400f0b011b1002c10701c010300c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 170918309 1250 170917059 170917091
    0xc020106030201020f16180e0304080303090607080403170c09032b02010c0c1e1505090c010e0307141c1b0609030b04030c02180109140c041401051602061305090a 71
    0x2003201c294500700c110701407c8020380001451190500c00c010311000600048224010000e54840d2005106a442c16500d804083d40c2d125021a801000541e401250080142441241d0398100c002c0c000c616051210f604003181c600070295440030258016040c00510340d08964600041440b943c0c4020b2054050985016122520500b402000e0701030007000c04200c103581d007100b00030762074012065800e40540040039000600c001e4501030401d00a003003d0420650194098000024000c1e00030310751781d41350000200b43d042c0f1240c46140d0020380440c0c1035002003160403c0b004e0f8280a0502c150303030856181c0000c07105140681c8031005020000314104045074071401c03507e07403140d054204110148803d20000301c528840c03070400c0098541900001c00d0540c00b41e80001c680090403425091a500e400812030703942d010360b100310314a0104c041c0c0005899446000a40704200e041c0b0b0760382e0300340c04035540080e00c240c11418050090088529040129181406c0c446401040f8414100110784000e00380c90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 170919559 1250 170918309 170918353
    0x1701170601051012090f061a03100b0307030f03091508010b12040602070f0516122a090204090203071d010c06150b030114040b01091d0c0c010c020106030201020f 71
    0x58800c8140a40c120403080c0100004c0c0300442e003c181c10002c00f1310600c3e02140480000c082034884614181c0e00f4541400f241c41424010f29000f001810980c8803001541d02410021002581501a003034001002440403500c001800388661280b101c924142115821801e45c02c00340305d4200f212402c010405100c01c401100c584609102c034514155403581000702c068071401700c0090940080140702070600ca03011807030380100c03000540d20b103444903651240340d07062021b040c1028100103451003041c480080401c01518840704c4100b0303c080907660782e020314812a005544442003864000042102d800e9012011704102c01d03009204060110072200000d0600111203001030900e9a5049001e030a0100d00d41c0d600c008000d19540541c0d65038460b25040d200018a11000e4040c0d414010164155801403003c1e009945000c40c542500c0546280c00019208003c0d022811500381000f03108624042030107011981862500040380003403540c400285000200a003d4485401180408000c000c0e100800c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 170920809 1250 170919559 170919569
    0x8010e0f0406020f030a0c111204050f0307030b0703020a020106050909062a040f080c061921020a020f0c0102010e1b030c030313030b0f01050d080c0106080106061701170601 76
    0x8200a0781d4602e0680024440c5120b030424452000c01017082034000741c0c000c000044a1a076400301c0f8905444c4171107076a030703000c200d1010f00003206100034032403030502600820600e1070003002c503a06c95503a921040350b090b07401c0d81c01d071001135000982001095024085c000003010241c84d1140289400c030b5006441385070281070071035400d4280700c0503507204005c84800b64560040301c850700c0da5281c0e80c5080398403042c66881100d2950054614541c61450300009603a8480b01a00303104083c0f4801038011a0014095081c200c0000e40c0111800c000085520140410000903002440441c0d03080101c0c6180840381400281103a04040741640100c1c8046420024244001d02d1200b00b0410701000074101401c02d8403181d05031102003210000d8128480070710302203034000e4a4035545501c0b1500b000369425000d01031607410a0b800e03107110000031340490007024031403840400010200d8540d00100d080d1615a88030000064110000464491103090810300401185d4a42c5c040b112030520780d1a01c426052082c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 170922059 1250 170920809 170920831
    0x50c010e150402010f170c0c210909070302040306020403060902010e04110412020a090f0b24040b0702130504140f010209031209031c020109330f0b0621060108010e 72
    0x20310300b440340c0550b000700344900035040001d1281c80c07e02c20500654000b52051443c2d841400c40132030180c0b002900002e00b100b071400e801403a1108100030700056103c0a025101055400c21000012a0f000e1001c1d0020b58403515001c100c0d00718074000140900c41a0903010310451030802c04d1601c69010a003103030120303121001c1c440c80410b00c0340002140b0a01d5640700004942c02c201807000980d40d5a4032044100358221001050034000c0c50000c0502c10700c0e54082910705100b000140462800c0c0b00c05810101d20003000c1540c0909200e082c80142c41c804d07542226034800309003c0408080f000d00c8010285151000218106003100e0700083d5600700310410b200183c4000070711901c1a4505004000324103650b110740d0400d0001420000340245010f4034142d0310019411802d04c0500340007071080e05803000b6030101000d242e002e80380400081230a604114402e1b680c42403000d0150719039101402208520510201454900700303207d43c4902c00080841d4108072420006100021a040b04107030007081e542c80c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 170923309 1250 170922059 170922077
    0x606030b091522050a0c03051305150c070501230a02090603010509060411071209050103050106121a130605040e060403052b050c070507090b060a0309051606050c010e15040201 77
    0x19261024107500302d4804a43d0781090308002107001150054101e18036130ba42c1c1001107980d10415245095540d00c4000e15a4200881401e0094040301c030042e00201400103582c41d240301e55852380c1c21034407508400c005905401821100030750010a08d0756125460541c01d41c40e0031880d0001038802d00c01401003d101c1c2d01c3c0800483c0c0140ca07164044030301c100c110039110341d070740600b414407150000214010500241c5003100200d06540300b8081c2c9812030b051034661082e2564211542d0000c0e210320b010990441041c006000f049542c1c8001840d0f0b929500714002a64500301014007058031700340703991500a076000005000000b54000704076200b490784508403a45014002d0b0b1485507040102380c40300b8002c4d040c44140018050b0340e400030000c891043d011034000b156103074003820644840700c074116132004007807002c040e40320f01070342004403841d2140050710000040c0c0500c118000070aa00b0040001e1000b00741c82c041050f00740f0444002c01100c1d8001c01000c505800e0701140410000d02c02410080b10034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 170924559 1250 170923309 170923339
    0x901050d060302180a0501060e060702010c051609020406090b070308070c170a0e0f0102012901030e07080604170c03030604020c03130308190c05030d09050313090606030b0915 77
    0x7502003070165078014012000f80d1000c0e4501d24400c2e40507149245100d140a0002400324001c4100c0c0100b01c5000d0002420003606400540d1010f01c505400d46060003000002c85050a80d03d00c42000f8000c140c000503290ba04046004042001a4002d1010b4100c1005481c022035080081ca540c855104c0c5481d4240404c1881e10b60680c030b851180c51580c80402090751000141c02c84148051000b003581e00d040c0034603818004900340c0e00c0307580c0e01d14249400c0560001142c84880b4000340e0001e010b0601084148900000c0f81c0380011307a0b48410003580205080c402089070f040034035142e40c09a120713182c0c204036400d41c000d07880e03110190455100760f034005115000d00302d01703105030380480015144000342242ea03030400000c40c0e4031044110701c03100650488048224012280140c855400c40004e50401441d01065802040803000079592440180034881124540240005c0034085000303011a00c0703460310b200030b82a29401541140300341020310400581141b1a500443c200c4012078041a0740d400423 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 170925809 1250 170924559 170924561
    0x303070605070221030121110103240305010e0f2a04090503071211011e150f03050a0b0705030105060306012114101203020307030503250c1101140901050d 68
    0x2d080820768040403001600441460101546c1251000842c80610b018884002e001403000444010103115051042031250b511a600080107004850140c801111240612070b100c004164001c8a1320383d1962840c9503090030601c1000e46112541d00100710f042c0070072504600000300302c00700144800d4055030380c0d003560340d5580000c0384090700302d016255594024141000e2070b0481284410100b813a800515008840520482072004038400c0c171050743c450b04955180c064540f4100f604000d0300c1001c00802c1400403030030700d100250300c0360b4010f00160016180c41d04114000900f60350a01100703000400480d02c0301030460380d0184091a003032900616a2146c00c90440403030344112000c038a001030103c500034007454401e028540c0345002c0c444070740d174800503045800c4640c0c50040050300140845c0002030700400c091904070a01c400d50300803000322135020922a0202ca00c07801c2c000f4010b40c500c0710900100003001074249400786024004020369046060f0144680c403282030421400252081d100f001d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 170927059 1250 170925809 170925823
    0xf060504050709051608010501090605041406040b121501020303010509011e0b0f07020103060504091205070c12060207030e1008010b0c070b070f02030601080109020d15020d050f0901060b0903030706050702 90
    0xf640200b02905003010f111034502c2c000701181d408109607400208a541c0681d0b13440303045030300c240e580e42e107010b0a24100c3c0d04208100c0990a07008601840f000c290516080040c1050306c0c0d601000003c03d1030030070401445005060001810b540042006200c10340710074407058156442907903d1140d141c2c039401c0500303d000c1039500c45002c0f90b2000c80c1d22106003490500500d42c25000b40d80920141e0b0715001084212004407500908003201410441c06950003800a0011140070301c01e480525580c40d0351141961000c135900f12401d640c00190101055000350f0501041001990302240381240d19170040c00c0b401c03060103030420369000031424403d03240040040e14083c1014446007511446130740742070400300d108000b040b03101e409510b0022403041014400c5108464009011043c20041c640316440f60301000c11038041065020060005480514061700c0d025007110fa240b814180748c041340703181c00c4a940b074100c400c500c1d10400a00711140d40000a03906420307041540080e230380d01c0c0c40302d06920f0004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 170928309 1250 170927059 170927069
    0xb0601050a170a0606020c0916080711030a050d0501090902010903110a24110610050f0109080604032c0f0609040e0d020105090705040203091e010f090507051005070f0605040507 78
    0x10301034100000592650481300c03c44079140c08a6590701865010003551490403035082d8180a007006c1421041441904803980200250038070302845088851200d0842d808580703490045800002d00d4255101c203031050360b0040542000410029007071364002400c44035144005841c03221080b50480483d41e48101c240018101c43c0e04505d41056100c1034440c2081c030340c4114902003031031070f2200103110401140307051050140d501050280c1d828a801c00840d04d1622a020b81000603040380824034900400485000703d02a4440c0340001c1d1300b8850150120059078521101da000d0300e03030000c2140d1607050030600208806c0360415100e2000704041001401c1c00074042d071240c403410388084115501940300c18020341000d0140e810f090784a05c1400300340d200582d016101f591000c445191032174030340d00150481d10642000801d0220241d43c451081c1c0308208429200b6401c4800204494980368115520305402800c000c0c0c140082611040c5590a182d80e0103080f107034a40380020100b11081c030003100541 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 170929559 1250 170928309 170928347
    0x51504060608060907090303090b07080f040b0306030c060a12020d0e01050117070e010605070f050f010c05040915030b060904030509031506190f1403030403060204120213090b0601050a 81
    0x10396503841c010003540b401d0740c1d03880c000c25400003c100d86610540b400800d4a0f0542c0b00c0101c1a80760142c0c2100a40c884081600c000c0410701451740e0024140004000030110b08849603200d00384141054200398241c070985102d007000700312084000e41c00248032800200034507001626070680524040162200070301c030180c207502c0c0400124003c180422551359036000d0008460509403220752a0b0b54240c402e00610b004240240007010014501940b01c403807880c0b0400c180c0b01c003803142045550a4666000b4050046800410240060003c51003020040d81501104060f0a03207103440303017191701c0e501404050007561003000190070f160040d0308031003401c0006002c8801c8240952102000340c0c20581d4541d1084142c13020202500500000c9003065075019810415190314103c422001d000304141c4a5415000c240800070206d03a592015000401003500300f841001d200b4810040c400d00d000610200d00313460000c0c5000030485205010f075001e030b400e080042d43c50141d1038081d2050003000507140c0d440307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 170930809 1250 170929559 170929571
    0x301020708031803030f06060a030e0a0c05010f0201020405100f09081518030a121a060309070f0519060309020f1f0914130b01050f13051e090a051504 66
    0x1c405000107601c01d4440f46600b0300403140074002c4036120b120a5a0843d0640e00708408250135250120080080241c0d44c100000c0c0300c9041071400741402481c08051382c4a02d9003510411555070442200b0440b0186403008519003814400040c02502c1c0302d243e00c0080100315001c071021395001e0404034000c0c00340d6000302d4081e801c80386a11100b2240440d0312100f45581c1d900e03000d015141c00400c3e00d1000d88d090b12006403060b200c1001c4002480005010840b00365151000042a1600801036002c0c1d0909805454200d05008100720f071400194042c3e03010b822440c02d0000c00c05101c0c10200196041780c41c000c203020403d4000680e505460360846035101c075040c0103071616402c18040c184991102500c1c2e106c2c02550f6103000009000c5545c42081d081940102c0742000d20505a0188810700d805052103800d0072040300c52810380e6007201c05656008240c00e40144080d1030a1103c00394852181c040000a04401c2008550001c0d00a000c94004644800206421443d40718a81c04001c0015204002c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 170932059 1250 170930809 170930813
    0x406140c0702190305150603030d0204030f0b10240905090109021908060d0609020a09091b08030301050a06110a1e020108130b01150302070602030f07200601051e03010207 75
    0x14503400390600300e125154800100321a0f4080701c0003001100e800c80d0162094520740096685141d40c000e180d40e5040c0001c021a0a182c0443c1c03000c0c201071801603001100690b09460720121000001c0d04a2810403c0d01d902042001e05108503101d0b41c4981d41008801e00c01030210955680c070a581203c0e074044071120000c030300481030394041e1640030110390aa80320007034015019510114153740481d08003207000910f2000c03410507040844541c0c4040d00d424030340b03651000c1e08000c03101070300c0045440c450720f00c1185807100458144030001d070252501444c0f07154509400190382800e648500814411504015064000240100840e580e00719a0903c4d01000b00d001c5070703030002a02a02280401c2244000c50130350444880152070386944070048480c16404c000d04c50710000c03420041c00040540800c150130020709940003550280c807000000d41c900781020b40010707041460303945111103168103036141807070101030001d516030440e0001c4ea003070303102c01c024060380c00329420503c102181c040d80000f0b07040b02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 170933309 1250 170932059 170932081
    0x50a061b0507170d031a04020c0c0603070c0b01090b01021b1c03030507270303080c130b040302040e0102030f150a0302120d030c0f230415030b01180f030b040614 71
    0x4088038802525000818928290700700c6006d4070968605650801074520541056801004201032050403140e5880300c040008425030300441c0d0410008454103054401c01c8502080c45015001c1c4090602003a07113a140000e5642c0c1e50f0a480d820f80b0720188102e0744864450081440b03103442d44070056100c0c01518200940500b1042d43c01d00c00103541404003104a01c00c0214103200b0308d40750080044034900d0b50b00c088a80b41c0d8050040d0500042c200074040400280c5c00316000203080d00340b8215115440e5004000c11100e54501154259004108210303140d00c03400001540b04241d500c1140703500d2100408181ea140301c0d0703000207402c071043c030300110205100001c0141a09140c0e6800703100000100350200c5d0160000c825102c0890b031925440219694035802c103048058007194030504066803002c0c400e50701e11034650040c2c0420781d14032000c0e42d81d50f80b24045080c202a256000d04045140001940506c10307584009004104c0d0a8003150801107150022405080c80c2d0030f944610b800c01c1c050200c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 170934559 1250 170933309 170933339
    0xd0f050703051005030c0a090203041b060e15040311100905130906050603030a08010b16081606050f090c0f1302190807090e0a0510180902010e060301050a061b0507 72
    0x400303c0740c0900005002d03d0000390f0704580000103402c440400745400b450b00d0280d00058400c844000c0891485035000c072418080a0040c8003d80d102140d904d0b4000038444540c1141070a0006500f041100340f022581e542807560b4029400c1c2c8208a10301d20401003150120f000d508130360b0380612800031036000044a07070089282c26010360300c208050303150902015a0791149290400104030307580010000112980040c142124000c0580d11140440355524082603100d0042440c0c282072104141c0280841c40c402c15a0104200704810b170142820040c080e95800c1501a65100340c407002c4040752039460b411203c2500c400c401c0c005540391006100c01b1600c00d9041c006200018040200041009124007901e0341228040c600303031421030300c4800c4400003400f401003038a040308961800009807034101100c018807407545d28200190889182c40010314104809942134401c203070500062055958140701c001c120b9846040200404840004170f0032032544410700a08a4010581c0001d03030003148007665 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 170935809 1250 170934559 170934571
    0x911091c151406030609060606180910150e131503170403020123250b0c03060301060f05060f0304030c050a0b06040c0309030c1b0f090c0e0a06020c060d0f05070305 72
    0x2c01c19038907103013490baa03490200c1c0c24030601c0e88900080380382420100020b0691510454001030241c0e29040458140042030359102c1ca00d2042110807c045a0b006c4842d88224000e8500a0301708900c1c0030003c1c40b039190600c984842c09580341c048400c04000c12400d40011584039100d212402d030b810031700c005250801e100680c040343c00b139100310b03400302c0f03181240c00c909222043d1818101201245c40a00403074801a524400c500c2a282040119159424442c40303401e507401da0b80e95a00d0000141401d541c031650021941003401d181c24801541c0340c00c10b170341c8a2504440b07c181c6a581d942012030391041c2e40306002d0b116014604c04082404110010a071040c1010f5800380640240c04400310226207402502400041042d8a81400940791040003000c02002500c107490068845540c201c11002e2a0310910f00c03a50385034849407102c0e800102c0c075580907400301d0704800014606140a92940345d0b40c1003180c030a000c00039401c403403094035510075200746007403110800440c94a8003000d001840e0544d10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 170937059 1250 170935809 170935841
    0x3051008240903040e0a050403140c0606010e01020d120203100302150301060305010b0408150702011d061006092402030706020313110306070c02090402030708010c02160911091c15 79
    0x2e0401c2c20000480d0708680c05582400240c0d91030000f240001c000c060401c90400c00c503042940b078040400d00140c400c0002c40000740c402820942c001400c9034522907502410b54200c1d00324008c605402c40340010700e2941024000d40e8959606402014104154000a52203a070f404d038041550300144000d0b5042e01c1103501c0c1089141d0300d4118002860141b84900d0703409a1100c1c4040201100c0404400e81010103400040780805013010105141c0400348010001035205a00700401d0b1144d2800e060020b14103810700001c4241040e50403540c01c1c001d103500c4041408404903903115540300300220340c3e03140d4008004548034100a0b120344280c2030340d44010b1303400c600e0383c9a0364802840c0106241d402040c05403076040c07500086509105880340d0041c41642d140c000c0040004500c44203014400105072160f01800c03010302513415480c1c54010b0360b00411440762034040720b94242c60313001d41190001c0d042224014888181392064031003080503044011b1284084481400d2090300ca50031586c40c0150b1810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 170938309 1250 170937059 170937061
    0x501090501030f06020901090b16030314060612130506040b01170c030c01030c030e120301050111010603020102060c0904090507060206090d0206060f04051305061608060301090b06010305100824 85
    0x645101519030a0001820015a0001c18400110741c2c1e402803100035810b04090081e0355841000b07800580200807064040142d4600800415500d803150b520040081c80300403040b82400d002054190060580d0700043c03003140c401081840440322110703103941d40d0000484001c1d2500c0d1500c403d11700001e01c12486840790303c03001200354981c085000b03800140c000c2c00500702d030700e6142c004501500c1000c1d06142410b41c1d4a888407000d1105105094051011101d5943d4a500d840001400b090f00000428680d0f49084c40c06d00c0181e030301045160f04000f6400c0c2c4962030364010030014000345000c2c0030042840c030602400103501074010031104e01c01c24803082a918021803680040c0c2c1c80306400c481480e4080b101a09800391803a00e07501094001a003c02c0314034842c061640c0d524a481016900c0403540491400400b01e01c0340c3c031443d40c43d80828160003d2286000b10364407449240b001902c041e042c035031a200002c0450855400c030000074007042007296103100c0d050f0a040c003205d201c2201c0c034412000c0703e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 170939559 1250 170938309 170938319
    0x40603110c0a080f04030501060b07050d05040f030809130504050a0209011706010b0a0903050f0304050901120b0f0603012d0501330203070803180f12180d08030106050703030501 78
    0x94252584801c100c80503228207030032076540c085160b20403500362486600500c80840480c000344102e001400c480126a0b90b20801e5040c075610303000c00c80a902080100801040c0b0104591020b9001104d52050301c1079110000030b0002a620030b42d1440320b0000038a003c08100600a0001e0030750040d034001d0b40c0800d1940d0300c40802052003081441c0d0441180d00c081d004000c0765904200400e01c218540c1781c01d5107030903126a00d590400154003009403039a8000300e014012441c02c1c2c446180103000d003440f40c03000111180d503802107a0000802c00c4405002c0c1c0c000143c0f141d00c00390440c82600c4c10045c00d004c0040c108220700a500c010f074801030020700b0f1400001042803221817074058000c01644c8024601200001241a070242525881c0c2c4210f0000303001d803000141110020703501403442521611254030301c80d81d69a2030002e1a45110390305601422984105041c03800886241e105a0341044004000010100b4500e04500400800075100003000080c0c40364000003601030141300ba40c05120590340d903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 170940809 1250 170939559 170939591
    0x602031905073e03071707030b0702150a0b0a0b0a090302030f1f051e090709020a0c020310151205120301080123090c0105181306090f020301030c0308070305160305040603 75
    0xd903c2d58142d0302203242170140a2101e40401c02d82201c0b4011142e01a880e540c8a2100e1103081c4da1820240e0700212807d4400d150410f030300c1e07521401003c0308020b83d44020002400d0b610291003040c102020024070a03002c0c0b440b07141560055500a000c441810100307404603650740326035610840c89502c02d4801e51042044c1030044038001e00d580c94070541075941142c0100407141d00981031940078840ea401c002880c90160001d4240c03551a9140e000701c42500b070042c1070604031615070075031010f460290120a401a003241c01030994200c100c040402c2000c2d441c186150005070b00303840c80e0303182c404000010201d10540211044c0c0c0751031201c40603041e400b04041000c4680c2981c8074411504180541d80303440d40f08001421104490250305500161a4804141c140c020000400c5140303031142401d2205102d02e01070b04034070314060b00b011403071036156484004801415000003016150005010410302d0b106905990000e501c00c5603120340e0303121914004d49254058814000882d080600400138601c4c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 170942059 1250 170940809 170940923
    0x60507020603150d0b011d070c15020f07020d083006041802180402040e0c0105070f060e101a0f010503040f060608030a090f0b04060203190507 63
    0x800352049046884020101c000503000c19012134011445681500103c0d4020610900a162645100c04511041603c1200b83c1c04010905018070041c0c90b80350f00050401c10103582c1a41ca00c2c040142c480000304c0c0c03440380078071032904060f42c03000d82d9880000521440070002c002c84400030070700c02035000340c0110b24070072020400c861002c400c003c800040c1c07240c2400e400c01b2004104009000754030b000e2030360020f101c0c1d8181e90703401404421801c040204504182c400c2510411611005011071f5141c100003c04034425400010800e91a5207007800030040b5a41200406042901c10386081090103000440145400c02c08643c3c4614801040780c118203003695440c00080d810b0703403201d24656031307510307146c0c088038204104664550b5150070021301d801c3e09201800c60325680766502c01006240c00a40e000b01040791b0050310814600300002c10034030fa000400c031890101000320300034042c2c2c0e40110540d011f00490030090304488481001110740c9000006900300c84941d80700d180c164003c0c403489034cc00000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 170943309 1250 170942059 170942063
    0xf0f07050907080a060b0f0309010c2a020a0f170d0302040308162f010305010510020a02091801050103060b030d0c030504170f030f0c070e040c090c030b03150a06060507 74
    0x41c0007011844480c810594140c0c001e01d20000450b1a03075403000408100c3c1c0c0040807040c00c0c101c010040c04003801d03080c05408088411850005040482c000e40950101c01000300204403480029510741151501500c0c400207100e8940c035182d195503242c000b010340f41d010113086c0300540680c4081c00c0c6d21600900c2070b542500d810072102414440040b14010703094040700c01c1510031004001716100e0001c260701075902d0054626034150801d401100024059a0b810780200703203d03010501008054503400904400b226404941e21075107a01c0e00094484058450400d01080c7d500b450000f200340150390b007000c040b01d9400d1b003c484260301c260004540f400d4003543d008000031810401000400c00700d20340138404014030002d0710500c0c40198542c81c6140d10070b44c4150710a010100303103d8880d08050005200170301c6207200f03042c81c0385420b0740c0d505030169070b50048001040d84c4004100c540e0b0300c654043c24000f003002c1c00300c0313400c56043ca050819415080300c2854025003010000f1990b5441003041d00c1c1d8683d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 170944559 1250 170943309 170943319
    0x31401020c0303070c020d020301050907050a05040506030606040902061905070b0c030708010b0c0111030a1a060c0a06020a090519080f0703020d08090301020909010b030406050c03090c10021606020f0f0705 90
    0x5200c1c0c0e401107820017815502070781e0012890b07184501680d0284651801508c8c0d9000500315903140a0a0000d10b45495100a220b540350108000302c03518040f1305294800f104480c0020700160783c2c80000c684e40140060480c4515055580c0d184098004008058050140340c92000030398071005048641d1008558101c0007848200040020180c82405030080700e4007100041004040c0494000e0544c100312030303030104a03031140c1902122102003000b9102504c803c0e544607143c1985c2c1d5100940e01d0001040041483ea4001042140b00380304003214030150030300905103000c0745681800c2c0e440041d15400303010064001c085514400c1030380051b02c401240d9001d406c0d40e1910603540c07107032011034010307a0100d80c155408008940e0640e4510b50039a01818100e280241c8078101030409000302c0b440103100d01c0007070304204103024441e4030001e8155805801103400218501c00082c04a08000e106907089081020904002c10b106401140f4194a01080c0d01207420783e0b0190780c52a555417401c3d2213074036009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 170945809 1250 170944559 170944561
    0x304051002070f0b0c1c0209100203040e150a09060803070302061501090306110c010204030f03090f031e0f08030c0d0b034c0b100305010b0d020a0215010f031401020c0303 75
    0x140864204541c4524a81c170824102541c402207030100401603690b00005650000c2e50240038030b000c620003549078485100640c141400d143c03280d01921000340c04038084204603599103402d550b030402d04202420382c802c0c0c14002d442da50b00e56180e40c0e4201c41412005405090b00003001c0b8191a6040304040310140d695401040c0f031510740c000100362099429100c1d10b0100601048180c090001b0001940305d165622a07000c1c090030001c000c640c1507000481c1543c03100718200017080744481080d81e900c284045440704220140f8106000f1403101c90700801e05400403040140e0401300501a180c0d001e40c0c0842440301c418403104141d112131461b82d4403d00d074001440f0b2074034444d60800c1810802c29103c0c1c03800e014682c86503184541c0d54810aa090b080b0350311400803500c0d07420100020030201c8141d050a22480d410008401500e008851081c62a15800b09064100314070800400c07900f88943c194220440d610354502610141c0701d030205943c0d9540150a019107944d0500c00c42c1c0100042002441c19 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 170947059 1250 170945809 170945813
    0xe090411040905030c01050f011a0412080c0102160606150804230a0c0f06030b091314031606050405070b07030503010302042a031a031204030206030606040f0603020304051002070f 79
    0x1c1401d600d080e200f600c0f05001c5500002000d110b018000d43c107440d8000c000350700d800c2d555441e01070840c80d002c0f1249800d100030800d401c42e0ba14040707207090f40110182c3d00d0300c2d00c80c0310306402030003103400908031003024080c408140505540058155400d80003003092501091005440c030719810795004242403a524042c400c0180802181c80048101c541a121036540544842084200c282c2001c0018101030b0001c00c125070f014860a01c04000950b02805d0307618100b05410310300c1c00f01680141110000300d0042c0f441080c140304560800c03e00310352060f18540b482c10312030014501207c1c211070510402c01c000c2010055081901d00150f40b50740c8443c0b07141c0c2542e003031101401882410f624814aa03010070401d01040102c0488030550710740e80043c695560294100e866420142154001d4106030582100ca41140b0100c5080e2601900e100340d0382d4523400e000c41d5207031240b684018401340003c3e02c00301e00c259041e00118080d5010340c0071124024180f882e180201e10601900400c03480c0e0901c0e00b000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 170948309 1250 170947059 170947061
    0x20d050315190603051909050a03080403030b03010e0307061404020d080c0304090f090501050708130602280807080606092b02310c051b0705100f0e09041104 69
    0xc11a020b4559940302c0841c100381d040c00011500a100481c1c0c80d0010007002c5c10598583d2182001411421301481c0c440d911916110021024040d0801c0800320004040c10700a800144100742c0141c0200040801081c0c4a80c503900502001c030ba100d420454212100d00c07a1410751402150024003968000340305544010980e4404002d0090500090000090340302d018480d251b45060148000702d04402e09140c900c0c01c684004121206102c0d0300002d0201c6582c11040b0307050700c2e40c1c0c440001a51000e41c143d0085c151031a110101075001c0d01e00f84450000e0391710240c0103002d0512a101c288031901c44400300011401b5822a0766002411018444585000d4580c00708000710a0315801c0c80c0e006051300070035024081e00101c034000744405005403a01c450701840b84501c0081d004d0080000c0801400300614600c144900000c210b403c00c0f480f04150348080c00b1080080038000c1c100d8544142c501406000c0341e55400c0c0c56804034140078200b03100340c14190130451081c0c1c4e00601d51144564807404001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 170949559 1250 170948309 170948341
    0x110f16080c010e0d1e030507050d080103080d090606050303030a02040e090d020d0503041506031209080303040503030f0601120f0c0306051e011d0303030f041e0b1b120f0a0b01020d0503 81
    0x20721645002d459000551102c204056101740c081c2c1e41d082d9440c0240e0600c42c0c600414410381a04211034a0010404078a8400030340700342500c82c6001042c0b5074074034140840076012030f40002d0380c940000401d01c4503509041d0700900850717182401080003543d80e0403141c1d8031542a10803a40240e0001e01c0350f220b6080c82000150361082c450042c94141c00e4080c207007803007101c2c855002252800d803480803c0c50000d030401c40f010001c0941d08003e40c40c40c58259906034403030001400c0780c03080d2652031000c11040d80c064000d81d4880c00450b4010030603442c900541c40301624541800741c3c00b0074644000400c06080041c501c020300d203441d1580c030712407204803401190380d0003404c00c00030320210050700d0142040d60103100450103001d10a00182050415081030300880944080c6007460318460414180081d03c0c002c00280e000e0315400a0b20041003511004400780d1240c1401c04001301941c104000001c48008415400b47c80b04c14420441c401e5200016640c40390313a0500b481c045141400080c02500d4411005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 170950809 1250 170949559 170949563
    0xd02070506031008010e07050411090109050402072609040515180907080a050a0203070b03040b0109020918040308070f0216050f0604050607050303010303110106060e010f110f16080c010e0d 83
    0x2102d0f51591981900c1c02c503014481510040e070440841009941303040c3c050148400b0540c80c0c0c0768500844000040c0003540f541c07291a0040303801180c114180015100c640740060500c1242079025000c03401ca407842680030055452040345032001090602c030641084c55182c01d005048066451700c0f00b00b400044103001000020b4910490f5404550903009000782c0141e14414401000c03114098410503051420702e410885001c83c0c1071007004007103281d9000140c115400c3d070200590350030030700001c588600041030010781c60421358024041090b0780680c0d00c900c40c03031071031350381d0041e4644182c4102e0b1203d41c041038400152415403014445032418840441c0300410040c946403400d6556800b04031282c108400644850300040010400e040d049154084980010b2008020103803d254001e00358007155031103203041210603d2000300080c020005c1c3e040e6106020200c44007100850640b99650300c400c0d82c0d40f40c01680e0040c0002d0340d0346001840507805001612518030880955040c807251841c00641 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 170952059 1250 170950809 170950831
    0x80111030c090913020312180603060303041802121303030b030609071a0d15080607021917160c0611010501210512030a0603030f18090b0427030905030d0207050603 72
    0x15040040e1b50400403040008000e05595803103402210040c0345400041901078020300d020410010303942e90101c12101a0b03025010407081c1c00c0c541705400c1c0024014040504040300f160024820a000400da1180301a44a907405010220403202410707100c031415607013100c5076408108144a01403503d815038892900510205007410780b40b0800d00d0070b0b9500c18041142901c9549020f20948100307105403035001002d0300040c8000c600700180c002030900d090300c019004078841c80c038500b22401045c04076200452044038403210701c0c2c880d0402d81e441450502c60b80c80840c0403004d041c0102031040c0a032038107c4020300d07200c080c1569055082c4603d600814001c03200b42c0a104a000c1c4611010700165010361007207400000c6050442c94060904580950000b0502c0700038025001e000d0010b00c00e000c15944c1000c0045810103014011030017802e01d6404c0003884600c2d18154141c81b02c22071500002060195031000003031a551014035859507083e450b590b0068100c080180a1820040011500005a000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 170953309 1250 170952059 170952091
    0x90a020d0f0905070501080702070608060d080705150601030e06040f030e0a081606080903031f0b070f11041509090309150806030d210e0a0c060801080111030c0909 72
    0x110003100c48411441007015500c060704401d1040401c07801000e0002800c00008a06000101950b80c0050f48203480400400900090240d1203284c000c07002c15a010300641d8580f5828035105880c1d444900c20307031000d2044000021041d40c400c0c00740c07482155070b0001909190b00c45031110011200c003c0c0c1c054040c03019030945104103459010400c00100207549c06442005015901c0c801d169400b030f804070003004142c105100d100038012044a800140d201c000301d80807503201280400f04010b40d032000b4007100c008506c600074801a140e811010742d104410340408400348000b04402c880054a5080210f1060201484204020350010520305c1c0030b4105480e05c1ea603140b64003588948054a2a00014100f9040c48840d0900704481f400185150400f031203c800c0154030f42c184861440a014541600c0d142000344006003840b42046143d08600008041c1c0e44484010344088000c0c07040c80c485619080c1c10b03422203264442920700428010080518000c115010441c1076040980b00e02a00d001c00a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 170954559 1250 170953309 170953327
    0x1b020609040b2107061e030b13060602010b040501080304080a02100e0d111c0b0601050d0f14010501021204030309062f010f0b03010603231504051006060e010905090a02 74
    0x1000f42034001043d000303046010120900340a007445225840300003400f210b0a52103e01254120351015040280c5ca40007840d0500c41000403c89402c01207400708640c46d0860100b01da0760f040d003002c40400c0c02035500b0320250740d0f24036050381d40744604d104140c0250401440e1500602d07141107600d100e07061920f0710104951a042c0012010a82f00700b00b116500c0b40d1801c40c1e00241010141600f144038120b43e0108580d0303558464407aa00801007a4504010000480d021240c5451340514002500da440070096083c0000d54030841090171701580b030161241410b15100c20b01d0703500480341aa681070361030135282d030314003101501c06800381c1405804503007409900b10b070180300120030811540703803a20001c910b80d01c01742000012201c000d9451030003641008410310105910424410311828801911904501e0001d2014102014541c0c0310364680303c0981404184000041c0b480842038181c1c804010f00756a8038401d5580100c3c1c2c0d07074050301040e440c8104110503c1d100c1c1100f64403003041e180152421341c1c00303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 170955809 1250 170954559 170954569
    0xd0515100f0e0615031905070215040b01030c0b180f040209060c0a0c09020a0503180f0607021606092105010e120d0f02031e0402010e0d12030c1b020609040b 69
    0x364204861900740d4104005041c9030043c0d08000341c1302089251455402d103a21b42c0c15510150010007822580c0761800b0071030140c401c03c107184028580e400030200c24109131401480468080c40301340c03481140d010004c9041c0305054202c815051042c00510921001e10081c0308410344900019a40310f0741c00e0114000c00d031510402800800e00d290003030401101030741392000c90144203421118141c0c4c0705000b225291900071046a403c4400110507000d0b040d1b650b25464941034442000c031007507000361020b10560540006020280b0310050000d10402600c03040101e40d0f5414030720681e0107040543c0840d8907c9440b4401c40c91240d1300902c004502e500b520920b1034030f040201241c9644d1990001444c2420b01c40e80e218030368105a8003601035145041080c0f2802c950458140740204441d4044085021a03010360701c00d4032029030160240c03500780c01c24104220358103500803410000c2400c0c61800341d48903115000030074045080c105021087c1d003c036024807140307801540283e0340103562201454040d684d070b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 170957059 1250 170955809 170955839
    0x602040306020c0d030b03280503190f030b0a0611070807060210140108150a0204050a14211207061503120f020105010f0e070c1703010807050d051510 66
    0x1519016a84a001c3c0b43c6030f51400d0003550051080518203500403050384d80c0450910944140003008215900b50700304405000e0591402c001d01501c0001050402030030b074143c4601c0c0c50440703a2200010b4401451054080c0c4d01442c05896108111003810300c030302c9000710300e5140020311810444048603100c0e41c52503d04101c0780c0040001d603003c84e0703c0300300840c003500400c011220200c200040652401550990320030040409040014103800056410a071a5050718001e0000820004511782c1e9030344e124070040252400709000301401c840019948480c001070b000107040312002010082e516003807080040d0410003045418644030304140300c40b1601070000e14007031400366064403d1302c5090000034001d401030046280943e41000010844088000c40010407108410340c240b40c0b56403100c108a41f40c00d05500001c0041009040c009010403405000d0341c141d65840301210f0007581c4070000c00904508a50000381680c3c000e0104a1194207654019070b0801070441140024070340390360303084940300d030b03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 170958309 1250 170957059 170957063
    0x25032003060a06080705060f0d020c030f03040c03150203040f080a0513080303010603061e1a0c102004140d0201020f0a051612030f0e06090d050303040209090d0c030311040306020403 80
    0x1844a0f01803101c0c040501021008010444882d490500c0380100404580205400510820303804150000e6040c8103008035080301500e245c24a603a880c19181250b203012482c0803c0c1e0342c040315030142e1a1001d00c1c0f80301301c0c1d02079038020345000c5030201a596007020300e03445036503144204403082c06185a0250242103d00c0582034460141d0344079810700900a0440d1016440111a105c0c1c104401c030303403040c00f000c074407003a182843e511b507c00c00d01102e02c0d20207a210f07a0100d40840d100b82c0e0503805800e030b100d902c10b551200c640444101c042d0800421080103000d01c0c06990f08600181d5856411450a402c0513010288180156260200d28040a60420f00d00200607100e075008184401a15029440480090300e01c4c0c243c031003080381868500402c0924400d03280006d00551098000303080e6100ca055480250009000e01e0421280c2e00d0032503107136001a0340889c021146d07c1c02040e0a56008580c1000741310741551141c40d029015242140500081c40e401c848040b408c000c0440403440c2c80c001000914 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 170959559 1250 170958309 170958311
    0x406080108010b1017040303022502010e0a05030c0103020c0a02060c0a0b070f20070b03070f0206100302060909071b0b010816030b070e0a091a0325032003060a 70
    0xd8544a1114296800c54a04a2046150b56010840b130354100103031a80e6002881d9030000d00da078451406500030b2042e8840310390410700c0c2e00318454264100b00c2c00d01c18054400e03030395001e03208900780502c17100342198020240c1c950045807070484194400d501800004000b001181c047e4107507500410910350050f600d420058005510174004d201c1504e5030290012140d02e0801c418000750708005085d03116a0001059a403103202103a510740408200c4040900707101c03900150380e03090641020341004540300c0c568002d4002d480004242a418019510440750003801c01c500d8039860100b00f000d8801e00800c40028000000107818940c1d242403400040d0622805040d0302650400c00c04500c2c00245030820302854840340401d100040350b011304581c01c8102c604100c0385601d00301c00007416490f190b42210080f545800201008400b0701c0f0640d60089400350b00303607201104541500840790015074900d9038190036504003000069030340c540680d16162180101d2001e40c007030f080040e00b0440151141034901e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 170960809 1250 170959559 170959561
    0xf030c0201140909010506180a080c04110f2203061401170604050d0f020a082205060406050f0a050409230a091a150a0305461403040608 60
    0x15600440b44001d0750b0b411010460412000c0000101400700501500340559804600709401a9000b20080301c0322000800d040e1100d0b455485403940ca121080c1640d10490400b4000d17408900041c040722816a1016500e070301d805100e0b82c01140d41c05050b030907044803440580f000004512503101c4d524000015145c0002c1c80d514040300140c140803d445c0610480d0054400d1000007080040c450700b80e81940d00300220440007513802603041503000000035000000002e400700c0d040ca402d41c5d18201901c0790082c90501e4648817014800349000300c0c002d00b0b000ca5001c01550070803031456005840c04030b1440c5861884d203500d07005484150ba400408403098520f00b02c4880507200401305000e644000c0c8540b0030844c3c03881c580c50b188940103520301c081108600346004140e0f403e00400103000d0043c1e01a00000c1c2441d030300d05d81240c0d038521039000904072140080c160951844846082500ca5203540f005040c5c0740038000016002c6240260201d802d40900c48211402c035500b80050001130040c1d464071003103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 170962059 1250 170960809 170960813
    0x20c010e0105030603060708060a080f0a021018090905010209060f0c07050411220e040f031d1008070210060815010e01290d06090e0c04060b0d0902010c0f030c 70
    0x301121401209060080c24410040180c40008043c0d52000840ca03003070140f5251a030204218035950740241c6000c1c01181d0054051480000300741e003c10340301b5241c1d550300100c03080e0104c90400ba4062035000103210034000b000400e00c01d0b080402040e000d00b00044c0740c100c117080000c90300d0788869152000d51601103048041054213010002c02814151010701c1711540081804019108039003048811070403154081411252040c500e80240c101041c81030030034202070401d500501d031414412400914256805030550444041c00d50b824500600728070740a01c0050419542040001d00000451141e80145100c001c0b490081c2d40080c9003180c05000072404600d102d00134000140c000503604c400c40e09c0104440c014013291002d00800d0051842402201040080e0440c80780c8407414540c04c1c01d0501c00300d04840300347e01401001c800c060499030b070800400300384410b540e16072190480814080c8024145403807240c1002d07104900c149046203100d00159240f8034040c442d030f502540007074819041c00007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 170963309 1250 170962059 170962067
    0x1c02011706010207180912080105030d0915110f070f090f020702060708070302160803041401020a020109091a030303010b031609031e080405180f130506060f120d020c01 74
    0x202400400034014510700d8500c0020307603a2035440c0304d0501c4030034100c0d0075a0124079907688502c90f00c0e50f008031004404204420010110344080c054642709000700b9000710b0b08180102060402c032a821010705010403420141518174501300840c96181d4054500c1c51401e046d024485100542410803949a072a400e105a09007220000c160031448144100158009a5210819220056440710950f030741c41c9542c0c03408030b00742912400780c80080c4032000404901480e000c0082e0054401e460b0003c07a80209103070049035590303002c01c400780c0441c200c01d80a10440040c2e8001821024a0744d841003c4001100d0210f891580264450310704a8004030600182e111005141401e644442c90228a59801d41d1980c00d810344949804410944105181400700b201c600107030340081c08000c040103003100d9202407505107100c04503918030a040c00c4900050b1400b4900302c034100304581060050010303075103190034802540c03804110191300451541c50f2040f0300303c040298036030304e40c070315405405003104e0400090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 170964559 1250 170963309 170963327
    0xb09010506011805120c03070602070602061506070f110d03030506120a03090b0d0f06140f041506050f0705030403050a110603040305090d02010309080d06060801080c0307231c0201 79
    0x6040000030002140d0010b859000e28094890803542e4110300074003280c2170b61900300703480c6441c0c0d05402141c00c00502c498021440104403003054003551259917401140b9001e1840e140e661a60144050000d02e010075901c680000006200d41151030300d1744800c800049006500b0241200020b0f258400c1040a00302000341c0c40c4120220001802010b44030754003d0980d070303564000c0043c9050f01086000d503d0085030005d05d044184510100001c0352694802007085103007902241c0503008000301141c0504142c070588043c15050341200c03c116040140c2214150300004180c610400c0502c08400456030602c010030086104200401c000b40d482c0c505880c80c499400395181c030903001401084042030704141210620384c400c4070007021180591005900510000f04044c03d007900116400034609a540c3c048410384e80941c51b60b2200761380e00e010541e03132003235010f008a405802840081064014075050681d19000161a0f0b04040c00800080f0311019000121842030181141180040d544c1100d410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 170965809 1250 170964559 170964571
    0xa020d0e060f0f150a170f0f1905150916080c0f010311070b0709080c04150522020a090317120720251e090504060e0a0b090105 56
    0xc0c080c1c0e0710741444100307900c1d80000d20b040a4140318000050010110a00d01044c50200401451a040d190040d0040d504003e49903d913507803003900622a69000001400303140008040010250f030046110032400340600050211110f218208282012030b500340000d901c03903c66240102811007013221602040519a40300e04481d4005a41c103640b00e440c1d44203441c0107140203080c080b807a0302d403500403000c00748100040680716602324000d104840d90b2241c03840b0304491030201192008043c1504210841c1c210001800043d0004181002142484480c5160326a42804c1c008522100c1c05c0e19171050f0b9000d2445500002c1c0014002c0c010406a4845480540503c8080a040c00700d41030064400800107050130081c0100c02509032211944070012120403a404410790b0307184070302c10f00441842a2000601c2400c00540400400c0180c3c0c6001d181d01070400714407600d040d451425505038024103025109581182e20307031919004101c02041150190b0344500d140026520f40508071500b10b03140500b103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 170967059 1250 170965809 170965813
    0xa050c0301050c070803040b1e04120e06040f03150b0303120604140f061e03031308060901050c1602130203040510110c030a03020d0e12030106021c32030a020d0e 71
    0x4103d001c501d0f0b17481a03941c0726034025900c60b4952903040d120202034503420010074181c4078460400c005c00c070760142000c0c0d03d050300e40c40e091010610901000001e0140b40101940d00d8082032082010038135182c0d0428090035608000110b230340340b0700042400c5034030180703401d030265640c00e0030b218140c00c00d0f100b0311070b030068240c681f1704150510400c200c0340d031f01c80034180c40c6c0b09a0400441c0f02c403491140e01da41c501e8400080860f65225120a0280c4558070207115401041c0281000a0000e060601402b4802c590890910345000803c08441603454840325050340c0007081c0e1032080518406901c0107500981c05030000b07003200210501c05a0035116416840014442d0510800c1c03c9540001305948625031141000740e03c419800c0c8039180200134480410030584500c40c10301c000030b40d1600046060b2840d075400e41d00d05034242a10921020083d038145400203000301805142d21040041000501481c03506006107505084070040e4603402c107840d5081c0065001655007207101d0503110f0301d42d5800030880 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 170968309 1250 170967059 170967067
    0x50306070c030503090c040e010906051326070c060503010806060d02240706090605010612140f060103020c060f1008070302030309010804080c010218040c0305060a060f020c030a050c0301050c 84
    0x8002021520618070050a10a01001051464109011311341d03108201500420000c2d81c11909030f8080c001d4080b003a6070640c5448040f5480c112042c656850594004070380740c008003d000c40741ea90860900310158950001406a48009841c4001b008020051640c5503a01c07035040c0941c140c00c00c18058211882124801c10240040e00c0303400040c0e50f18076902504890917962001103da013889800700040040745400e030b0203000c100055019a050b41c4640e5500c020307400107078900b90f003110320224040500402010008800500c4805080c0e4014010300d0b01500307100d00303d01a149030030801e80b801941d401030360042140c04030a4a0303075030000300b010398010680d0a2031070f00807039140d1080700c03240c604100f034180000d814401c2c500d045a10300481580215910141c4075589180d030411b10704820311a505115494100134424064a40900745c000d02000e80300d40b0300042982e0241c0500d8082095000e902c03c400c803166402d0154000c2180a0809021450300c0e500802d401c59400070700076007038064140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 170969559 1250 170968309 170968321
    0x609061209010f05150117181f050c041d060d0203010507030603020306070201060608010e0a0608030301080106030b0c03040803130204230f070203191115040f0203120301150302181206070801050306 87
    0x10729248a1100e00087c0443c8a0701d5484841c00a508060f042141c41c0c810726100000340d442003a120503000b100c07041c1c1008030340c5580320092060703c03680c415105c840765a2030025500c05514142c49800c01c100a01142e00c203107056000c030b402d4a10890303500340400d6481c00c0400035400c041c03040c0f5078002e1030f07807000304108c0d0b051a0000c0d20500c0180141801d5402400000e00c05c043c5541c000c1d005403004808890f125a520410b8901a2a0a0204507a114146000700d46244810815280101d62000c4940c0c156134130310311030081c8a8500441a0303801900c40e807941c03080e5611804030707926407211802c003400c042c40c0410b8050419040900b10701300719482007101c260715155074215000100303c54a82a0080020702086915041c4000030300700c014200b8106000422418000da20702c1140b00780e00740c3d0401d00210f16844c0281c0004d10170a10007007004002c0c003444078070030350041552880ca2503003a41307448c66840100e003503840075904a44082c0e014401b03002030285c00503440740c01000304600500c0305142c19 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 170970809 1250 170969559 170969567
    0x10050c07030605090708030c10060902041a090f040204151407020a0b031018020714011104050d08130e0906090606010c0602030a0b03120a1803080403020609061209010f051501 77
    0x148800b0303012540d10800700c0c0b0001010710940300209100c104036605c4640380140076440c0c120071050b206840d45840d80010390105540290740440e07104441c1c05800d4030841000070050341c8190001c99110f152101c0071010382d41c5500c0504040c02081c5595140e4613070800c006040f00f0301d00001c2c01000241401031000580c0d50003c40820764000b010301c1500c1b0f8035526481004d0041d5a001a04182d510a8142c400c60f2400c0d4080c0c0142401100030307000000443c0f0003d422108401945100a070040100303103c1e60400024010220b81f0510020307141c141030000f91040c8000713030f401c003201a440060620400c0181000500e411074049030141805e0704014001901481e10790380001e00140d000b100040105100b41c0c04480d0280d0013a080d00c00c0c40241491815256100c00c842201241c030200da07080c441c40c00924442c081d640d01c4005185454116000c00c00640c00c10101c50358000000c101c4c81d0902c442d15031010703002e09902c1c000441d8405850200d2026508010a5041a4035031110759441c941e0f40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 170972059 1250 170970809 170970823
    0x815130f080c010608061b0a090608060112020d1418060105040902010504120f051b0904020f03120d0605151602360f01090e070b250b040210050c 64
    0x211044121018034149818041e9004041508440c1c1d480d209000070554000f10f8818410070450320000314003406d00c10304130000c0c000c128240e80020381c140341c20300000f4050a041c0d50400014140711418003209070950060380c0c000203190f1303075560306c2e590000c0c41c0000c03444009400c0906915114401c054a00303c05599040500c15184a01c0d16108500c096900910448020300003110369031210910724106120707103001c03d4400300c0b410f01c52000c003450a000201e2010582c4080240020342d0354403581c0070000c80b401c1030341c07495074140a250300c0e070090300744000010303c00700003000702c08143c181c0341400300002c510021401c00c141c1401003050500401310315070004080340c0d044800c0b507030b01590030343d41f0448000700040040e41015042d1008501c1000285400d110320303120b0103110542e13030300d0302c034501c4c02d850401e10010800e5202c0a8240019208103002e40103801d000d00b08060030b102c1c010029117001c04120000d868034a1210300380710560410080c0141c54005e02c0c00c04901c0c20681000c0784c1d5851032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 170973309 1250 170972059 170972063
    0x905090403050d061a0c0f0c0109062f1606020703020a260f01021308011404150e061003030f0e0f150c101410050d0b090c04090309081513 61
    0x1000190315118070304284c3c0420082c10200f02000702e040340b10882d1403042c0d400f0700c01162183c4103204081c92031040c00202104942d8040e036458100c5498100140c4814600d11707000c0d003008070100c5003031004c0182c040758190360f4041400205000030b1181d465000c14095600700f0400c44d045200180050f86a0010440464580710200d01c0c160800708a042e03100e14500c04192014080e010250444003c1500940141e07000e4034415601140e88030300141c203d81000300503884451384200042d010841c070050b20201c40d41d0100c400f0540340c0d400c510140c1800c000311903102007681c0101c3c042c402e0581c00310504ea503005040c1403105001c0c00e100c0015605400d18008144210311501c0c6000030580800182c610741c42c1d00c0c400b01d40c4a0307200c1d6240d14010f41010314074500216060000109510451141c0404981019110815045180d00d50f0301c180c420040148405e8415418001c805407510b1240340c3c443c0303004e0ba8036011010b0500722560700300208070340c1404440c800d02e428031001d019a4903854403255 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 170974559 1250 170973309 170973317
    0x10020a08071b120503090f010c030f0f0203040b01210b011517060f24030109020315011403240907091a04061407050a0b010810110a120b0109051e100905090403 70
    0x1540e046e88007450680914484482c550070042a8002c454040c0c000412501096006000c000e071b01c1d9440104031700044601034803500030600100710003801d03c0c1280c503440f10b6600c2c1a909a014030344605030030344002e9100503116104200320360319056100b540080c0c9000e140003424102e003402c100040c9490b03112021944200d182d4105213100104a8088860204412404a03101e6a55841d110001e402c00c98840103000b0315400c04925070741c450f0303150000002c2c1e44d0b00c07602c2c1076071036240c002c00600901100f40c17180c0202540c0c0400056a804101d640318030a60340d42c40c2001410580103903000d400340766030503548040904c030501c0071a4101c50400a5a001d00100c1e40d10b46030385017042481c00d01c0c3c4800107000100c5100011031409004101611505103d1001b070106845c0346d81992154846e000e500380004031401c43c41c1c001d0f0300e101d400c060030300407051614000c9103845100261801c0031440c1c07190000c0d01c01c805140c445003403040c045042d0000d14100105010b14120101d0441c80c0000d20041c200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 170975809 1250 170974559 170974561
    0x70f030e0111010e0604060b0d020108130206120405010507090515041205030d0213031b0b090d020f1005040303020c060c0607140409060605071104060320010210020a08071b120503 79
    0x103074400c41e05100c154090200a00131000c61070010341e1110700070764064a10343c1c18102218402d08017407002019032035041e0b45000d516a5411400c805a207101c0c0c2c0d003281e10032420031501044c40c06a5400324029402440000b88a04040c20081c0c0b808400d0b60156006614403881e400a402402c426241192070300030030350b074100245142c41d50a5101d07c2c042100c0da0391010450885040f841c1040b142900c0c802c800f0710b441c03030340315120050180710140f00b01d61919034104203e1060b0b00b031001c09440c14500c003505603840700405c0d07000120113408420440c400260f0108041003410760401140381071400075203080b4500a100d030660b9480c0c000003011041030200110402c0c60000900c42103400400071400100911901d401006003280e104c00e0054441d90850802d40751f051526115940803a83c0c0550702c01402560641180c49d001c076510f51407410740c000c02c50719148104403030000300000740055551040030314101401901c01c0440100c1c040d0381952140c0f10500040811b002070070754900c282030140e16 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 170977059 1250 170975809 170975837
    0x21020f130e0a0b1005130302120703030f022d0109060609020d0c09050f0108040c0b0c150619060809030717090102060106080702150c3a0216110406030b01180c05070f03 74
    0x1241b07a1960000390058120314019a610b0408900d60040d40c0c401d80d541d1b140c12244c1031007280d0380c1102d840613075204589100c90712078004e05009022034001904001240102e03040d16040119107165001020407038001074501e0040c2c1c814800d0480c2142a400c0c03100740c41d4100004074502c0b007405550756060101c840c0120303050001c5100c3d80c00c001e280b005021b691f1884422001516403411461645c0d0001a030004507005150103036032441c4010b0420203450606140c0030307003111400000351818020740010400340c401300303801c001e5850328250032070345940e80ea4446800092502005034001c40030001c002090240341640481c1403441c10440000700380107900c640800000502c159401c60021440700c40300115a0075140c1405440c08100c003560b80312403410b4038100780c180e1040c500585803410010240500060300c841902803171003c040d10010717000742c4a59414000c1307030080c0c002540d07001c3c03801182d0001c45010f008540180c102841c10604200311031f41c03540408402c81b90300400b0f100d900800908 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 170978309 1250 170977059 170977087
    0x13031101060b30010303030b030712021c110406030c08120a0504030b060120150106080c0430080c010b010e0f040b2e0207080102070321020f130e0a0b1005 68
    0x60482480c960010f25503075038a40500103000203413010780240a482d400240500c0c0c03001c9032440729034019220003c00c83c1c0f0b8034500d43c50107054017070854081101da881d841e040d40325803242c90055441500c1d0383c2202030401c40030f10710300000310b42c0e0300070000d00030404103103400c2e40b21095070101d990002d02500ca80c0c40320001a12102c3e81030710700c0301040410b030150880c001d0340003458225040403550074170800e0762900030485a0750030807100038440000800081081c3c141c01d2080c162545030074000d881080e040b5074908040c1500102c1d05955072480420740f2403a41200380b18121190000b400c00017004c00002c00425844115400c49521541d921182ca4140b5190300c8000000ca0314420101070001c500603220480001810000d10018810158081072202051089030b4481d07815458105081080c56251094101004a40c4050303903001d0040341a142da6078005072580c1c820440ea0221210704001880c491100c00a144e00c1c01c09081000c200714130b07180c16840361500500c519045580c1e180e02d1090385 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 170979559 1250 170978309 170978377
    0xf010203071413050418060b0a0506090607060b060403030305010303091e05040b040f0e010f060b09090112020303070503041d06010203130902030705090310020a0206070215070806040f0513031101060b 88
    0x390f00103052103181c1100e05000800c0c4043c451061f441003209000a50034050740d03c600e8018150008010041d9501c1d40c642a03001d4882d5612074900410a001900007041580c0c00a0380100c01207a210001803040540101c0382c1030141c2400030008900069075283c002038040c2e41c1c40754074002c035681c215410540c0c0b5070750801140314801501c141b10b4580d5120b0382034000c0c18914510084545400000b0a58002c0c01041b00c0b00300c40300402002c0c0703513400c02d0240238948600e41c800300d905100c100f2843c40000c00c1480a8801000101c0b140b050304003c2c40d01041d54100020002411500200314040011000340009801d072124444010703181c0d41d035454281ea4521031040e1083d858490b128020004110640082c01011441d40c245c07549a160000282c1e9100c0003d40d104d80041305050000301010f101e8655958091001040810303244070501000d000c0f10001c3d82c5060b0500341c84189903050540140e15410141a5003008000b41450704a040b610750040003081510042c10300300041603004207040034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 170980809 1250 170979559 170979569
    0xf0801090507110604030c0c14130e010212090703110d02030a060e03040504023c030a050406090f03020c030c060301140d050111040f1a0306060417011d0f0f010203071413 75
    0x2552903085c9403c0c0600052110082190040015240411519007c641e280389a4001a20350079841c032040c1c5940014148811040d00c007598244030510501c82c00012050080c100780e00600012415030400c0500d00e011251014003c8049000903001a01c002401450854001900180c800c1004186070b00314816544403d5003d4000716034410000b100ca03041007a40000d00c0400420110443c0c8400f40300d1401964480d82460103000080c0101400e801956200748a908002900e8240781c0c0c80c040401881c6c2416401a8061100031005003410000013821140440305241198034060551070001c0d03ca60602d03000300440c0f144401001403d402c000403204c07098401584032911401a107080c18417910454003070003202104c12500b54024000c9a000d00c4000d0f0040d8541428910880c10340900d4004a17542503580e0454410122000c1d04903c424080240107404d90042c954507103403518010b11010706080c7d1042080c00600c9800c490b82088a08001c4d08070364440d40d80f00c6601150710702c503500c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 170982059 1250 170980809 170980813
    0x6090705090301110a0f031a0a030206160813050907080c19020a02090103050c150903030405010c08070b0106050c01231303090b04141302030403080406020904060b07061a010f080109050711 83
    0x6a0240d60400446c401290155400700200700d00703004188031703103d0010340d490b4201d80034000c140007600b00b68000300881e04040481c905c65060341d5444042c02e6001c080c00c12035421280308280641e2910038421508400186494201c1d81440c160390034081c8a29905500000b40d111004010700d4000e00070342a5403600208840300343d6a40e03050541d01c0c3e1142010340d0303100d982c0c1c51030704582c0900d105d010344003100c102078000c5003031038101001903c185d00b03001070945211005120f0400001c0302103001a000e00501c0d50f40c903803588042450700d400d51703000785d070441e800110500d030702c0c0d0000070070304030182c2d10280b840025100700c0001e0a05945401650f00841d10b2034900240100d04001481c514000010050300d0b240510003088062008a00080d60f00400203000880031902282094003d0180000c00400000e115950351200c2c81040d031104c00110349141d1188020b40e10320500f0420945011801c2c2088c0c0008680c4900081954005004100895584101140041d88a6441c0b08588174040c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 170983309 1250 170982059 170982067
    0x6030b01060e1f2a0303140c03070305071b110102070b1c271a060d150c1e0314010e061005070305070c0303050d050c0406091205210c0606090609070509030111 70
    0x586407003084400b8056000c68280040c0070301f0039070101e10300c921690700001d003a81161100c007812805000094081c86c200000c80b00790f885480c0395064500400c0344200040c50100e040b51002905140c01644042c084040500000315003c0e2001c080c1c1014a6005000060098148690505034985c80491404555440700004100890724024000e80103142d08401229610001081040d14804d98000e0040b04034400d00707007088035035400001c5002c1c40e605040c00701c40700e00400504a80861424400000d41782c1020000080d240c000321b601406002c0c441e54040d1501e8000700d80c0d01d40740c283c04042040000100d40b014035110b4801d4441c0541d00c1410504541e0b540d0400074542d8014044195503030b03250801003101005107008540480b105510707543c414901d4088040d503829030040d4140c1740f500449051101d0b004800f20a81031540d9801e5403240c03075060f680b80491074024010099070150f845841170121559030701031465840714552600780c0d654019840424050411700750000e03400301c4041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 170984559 1250 170983309 170983367
    0x91e05030c010b0609060a03050730050907120b070509190311040501061e05130e100807050d02092203030b100305010308040b0f0c1006030b01060e1f 66
    0x30004101a06003080248030506a038410040c4d18480c00302000d0b80700008100d480c036018001e0f040194803942c1d50030001b5000e80d03490b1940c0350184e2002801a03403100003504504c0c10524605c161500303c01201d00602c0394509011101824401c0c88101400c6005000001007085108100b21020480090501c1003409015841c41c96800243e000c01c4070070540711250184182464400c542c100c0e1602e41c2c800c00514030300c0003e48070745900311040b6800c0140070403660310844060010000100309240c0c44c40600c0c60000d001100e03100c950b400840903500245001c06c02952208c0c1031500440d011258610b4640302d420621124126014003c68010f600e040311005054050344001b62052090f50701c031a01a0020740d046007207070401d000c002c0072070006000c144440b034010005000000c3c01020311601e811100d107881032500721a512050034050b2952014820007420a072001c0c014000c0d0704050080b24132800000d4002c2d4040d09606900320340ca00041b8942c58807d45406030710a520b94001080c2204074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 170985809 1250 170984559 170984563
    0xb10090912080705070b01090515090108060402100f05030105220f05040c0801090201090e040c030f0503300612010b100302090405010f0305030a080604110307181512091e05 76
    0x90624075022070a40000544080e001d14112541d095001c260b100140e800c1c02001c80003070001920000001c2c8c80c1d842d4405503902d0700d0b01d0250180200740d005010b103181c0f0344100200d08a00c220b0b20410016840c640540c400e8100080e80d05441045410488005101000c0c030320441804180c46045400d00c5410200551150700103801103008000e10401c0f41d4682c850b681c00c2e01c0c3c007103c00a00040d141340b01089159085103400750028462403c0e800c0e015542d4890f996107221142d0151800c0c0c0000031046482c002402101200703800c40d961161403280407482a2410b00c000410309809000350380041c82c0001402c0d13201c1140000c0080000c82101c0c80000000c000707411454185000b18501b00002c0b905001c032401c40c10803254441c00440c0f1340041c80408a078101c0000e009c40d030300152100314041c2d001040c88040c61007070b080d640c2da07032104001032041d00c0410800c5910000318204545499450705910000700310300260704220115103007810f85040c2d00b000c41c0c0100c1c1d001c513959441c2c80041c00c100300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 170987059 1250 170985809 170985833
    0x50c04110901030f0c120906020417060123010806100c060c11010b0603161404090f0b090709030215180303070602090108011401050d110d110306010f02030f070b100909 74
    0xc02c0e0f03410820032004c8070707401048585000307001c00070401041940305284000d0700a5900f01d4070800015041513070300c041840313089401e4a000001c98011400501400c0d0403000c1c07110009100c5105c1042004110001a0000c0380140006000f22000c50281ca061800f800644100341c1d802a4101314034151010002c3c8072400480786542c041d42088030250036898540300f0b40340100440301c4c81d001c80d9508800291007142541200c1000050f050000042d44003140c450380388040c82c281d201107420303000c0b00d081080321a0001c0624003030040c07a0000340050f07142d000303054110520741c01c81c147c2d840480581d25009090035504c05589072200041d04e90400441c1d03005000342102c2a21014039990300c442c3c06900104a0010140c00101309010741380c03400209400c80c20708540034102ea10b00e4200c80d1121102a2031000c0c8a0310710048001051112035648140c0c0e0030190501c0344061401d00392880d462b819680709000c0090410701c09400428502c1034121038641c000c0415541c01c0103080078505d0904c42d1140c2c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 170988309 1250 170987059 170987077
    0x60307021f0b0a0501092102010c060e060402011b03090e090a0c03110307060819020a2c1c03050318070b0d0c020606151b030d020c060103050c011404030609050c0411 73
    0xb58a40c1e001415501030741c1b000040c0d40c0440d01c1c07542c820703002d400b10245000602000380d040022005d91200450014411083e10152050140185182500026040d21850908045045000c40f0b459010a500c41030140c15940034111803e40c585586e2400d614250b50340c0e802501c3d0040385230000041101c113000c0c10602c1441139056075100f5545a10583c0c4400c0704036045022001801c5050b1203c1c0c2c15a8010100e0000c0d50900c5030214462451401c030301506400c50001c0a00101e2603140c0c00d1401d940c1c0640403000308d84000401c00b6203a68014018000034114000711402d03001604481e20f81032241c90040d10640301d02540b01c80b07001075044042d005180110026020302404a8044c1c208008900310140030130f00214030300381d51500351002010001c104151580001e0240c3c01c20700c0b40c940000c110205108000f0440755045080c840c1c18407c40301045030504c11042c0580c3c0300e8640b28815a0308a032340014000503140310508050303043c0a030892000c1d034818606020214400f0071400500b0000d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 170989559 1250 170988309 170988319
    0xc03080a1112090c0604030314030c0409051602010e03041406070602071e12021908031f06170901060303080f0c0d140109050f011a0f090604030b010602190c0302060307021f0b 77
    0x242d403500031700407648503070b000240000d49805005400000184000d540083c0c40c110750307524095803a00c2c4401210341c1035491a8000404503015204560309000307010400e18200003840c0b80900d0101e10728200d4000d9012540240c8004c11007d00703100680c1d06460070300c0d4000c03a4070184440c0f140420020450340c240e08031240100c0c500c01082d031610000324011610303000c080102d0380700300a4135aa5144c0d00028000c10800c20074411601e0030542c00b40c0120020b0000f0780317a6160b01e0020849800345088000d2400c280740c4c0c03514a00700003007039000341156000b4180070050301c03070790711030000f01180c41c0714560304c03442064200100d0b103c940710b5440c2024101c40b502d5904000c5526136201d102d04491080c81082e02c0d2040442c4a0b0710341ea0a0300d0002c2c0001003400c054280340100941c0880d0064001d6401078442d90118001000065010701c9060301080000d034414a01040030382c0c0d082c1c40b60040f808040c2c003a407404000540d20500070401070500c504004074032030f5045030308030a02c0c0160000c410814061 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 170990809 1250 170989559 170989573
    0x1021c090f0803090d0b04050a02030714100509030d050906070b04150e0a02090a05150a0f0f0b1617040b070605090712031b111002010b0415060c03080a111209 70
    0x10b4800030041e00c1100c90024400f0f01c000701580c0340e00b40007401c00751041c0e9842c0100c48040005075020400034004004810b9200010150030082002c00d0700d800c44410b040c082d04001720f286c0c680d000300d00841040f5070344c1072503910b40e11800d000c20f0007070059003801440340b42128180014000c01100a049c1c0c0340c10f010301840031580041d8619121004008000d41010565003c03914040b9543c02c8075034031010401480840c08a4800013035094069076020314111011076606000040c0e82ca03c2a6001d04440842c0d58501030100041848011400401401d144c110700c1400c40e04443c01000c4800404a608415803525070b9030920754020700003a40c8030006441a100005190640c00d40484003580d0141c941c0072816a59a00c0292408a99482201c2c0044801c0780e1200c1c2d41c0d07840612903410310040d03000084024103041408100c981040000c0b1028840c903004011180d03024441c2a88541c1c189071902003916852203443c0649403540303454400c110085540140329400a40380d07440303007058600322100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 170992059 1250 170990809 170990819
    0xb0a0302040816030b0601230f0304061410181407030c020d0e0a05040f020702031e0c06030f07052b0b0a050a0503060103030c030e030d111501061d01021c090f 70
    0x10f491028400280707140b45040c00980b0303e41c000c4035942d0403016001500c0710400484640760303c00c0d512800d41c12100c20404014441808024807805400c40703518a001c00d40c508100308942d0300c03205544103001c10304da603082001030350744031036000185080070421a00c041c81c20421030160140012000010052040300181d040c1148100300f0500720400141ca00310b03269003001c003840050140e1052101e07005408104c0800162000c018861250008802c0780c107445550303255041c180f20044100b280715160500a10103240d1001406680104050034a9a03581c504200501e0040105a4100041044510040640200540002040c1d98084811203420f98651042240840250040c1a09580b200006000080c00b0304038201e40300780030f4103000d0303402c00c03040c0d0002e4900803a40226000146c0050703a81c400045082000c2c0c414464100b543e110301d1b42c1010401000400d009004540e14200061208001e90003442088421010441540c4015100c410054001070062040441800a45000143d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 170993309 1250 170992059 170992093
    0xb0904150f05250306080a030306030209090304030b06090618040302071503090809040e100509010603140f2805030c03030114030f060a0203070e090a05010504051323070b0a03020408 80
    0x310881e403581030207410201e00e214101ca205100f034100b900345075450001284942017000410701481c0300781c0d0301150250940c410f001c1ca1810182c0007032b0259106020500c0080e4000b4411035001d85c0903651030380180d6602d0002100b050469140221820554045c07000749a0b01052507030a03104582e81d08030543e0000c0008070101c5c1e60005010300151005c0c04184124906608000c0800d4080d104542084100b0704590084580c01c0d00c00c840070360740d075650800c1003003030f1240540c1ca40e001c500007400c0820144080d40e900c2c2e0b0105c01c030300010744968a002d1220801030a120148440e00b000803642c03120f203004080c1e652a0b00a0140340b988040d54801e2806600e00050b543c400110714030090009610340fa41030b44041c0d040a40500c081c0300445507101c00c1350b00c0380b0500030b01c1240002e501154a51500080c44221a000b03440e41c05003441c1d0702c915401041c01c0004203114118541c812500560319a01480c0c05c0030020740140002c0500000c0c3c7d1050310368140c0282040ea001c01040c0c4801b191a401c0c044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 170994559 1250 170993309 170993311
    0x1c1113241d010306110415110705040203130b04050f12040e0f0c040308180d060f050a050c1608130e04140604150f0605040509070f0b040311130b0904150f05 69
    0x103040c0760030401400002c0e01030f004032401e030702c07084a5a0b0400d038441701c02c02440701d851500100050701c0e183c403c091021080140000400082e02d086245081c0400c015921414403000a4003415120b030103d0204842004641e600d1110041a91803041c208a01c00d01135070700c5449103201080c1110003154400441d25415406401c4040310b03185014955a500d61075600700105001001884c5812015103071074607020034030128071405001641442781b000c0c038801c883d00504034041d014900350420514410000480f11201e07600d030101d00721007060785400f03241072003010300c01e813003054030b54000060085603041424003a40c8510912081c111a01e94555917407141224060004011045007280540e80d55103d903016812400c00031940c01d86a4010805441c1c00b80c42280c420360201f030741001100f100880100103441c10040b00361801d0b1039901c54042c081030f140d480c5482020303030000030f200400055008801e015409020050580303002e0601020170160101500061030070042d400c0340380c0509200381 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 170995809 1250 170994559 170994599
    0xf0f01050714070305030415020d08040314090f12010510120206030604051905010605090a0906181e05040302030a03050a0209150c012003040309051c111324 69
    0x282800410b450b200c07001408a4141034180c0039551010001c20300600003000940f60210f03510b80900142c8400070301c1c11107041281401c0040300e605000000c0c1e48510f00144001d07007003184c1c90302c0c2c0b0000380c009003c00014801682e40005000109110b80e401074102c40d05c10003010291040303450361061022030600c80200020340c0810204001035042c900f5604c0f0300d820200c40041c50500c040000e004500300c800a80090002c1000401c10a071949403e10130013020b007480c0d40f0b05100b114035191074074131040900034410f11703080c0e103400a10340c14070541c203890744480100700810700441c1000e04019450381d000028080000741020001540d88906000322401c0c14005001580c40104000307690040b40c0000317041d00d4003952103500130107034074a03482072a1000300650083c039652405d15207000b908a1189510150041011a516801d0f240d058070340c59260581084c4042c2c890b0307000d00002511050402c81d0040d0f800d142010441500c3c0c14541e580c0da808220310041310240d61101214100148010f540d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 170997059 1250 170995809 170995817
    0x20c0f010920031f020f07020301020c0c1f12180f0c030201080105120604020405150d0303060806090f030406050d110406033614031b03130603050c09060705150c07020f0f01 76
    0x101c00130380c03070071503009040b03004000c1082801e1102d640c0c002801da0340801202146d5600840c1a0802854168641c1110799a880300c00c120764584484090030f40d14800070601c140d945e83d124070032003081600606580143e80080b81d0440c6208514048040034900d000c00c1e0b00140d00b410000c0f8031418404004100110a01e005041560329030742048082c0034000d151105200042c00c2e0201551245040b00080502c25200465110f0a00b624907280240080c1403d15a0b070003131105403220385000c0100c4c0d083d100c0c10700d05940d54a0481c04c5442c003a00c5603204010b610f0600003800950341e40d05501003800500d030100000b40000c4840c01c14490406090010f000c00400741a00d440041c15800f1510a03500c01c240690f81000031140c1100e21102c02001d01070015003001400c03811801c1c103002d03103401a084034141040075080c02554007409000352900380c0c0c014030001982d00c09022081091005004449021301031510f401c101c840c0e102c3d00400300481c040c080442000d603c070702d0400e014040911060751 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 170998309 1250 170997059 170997103
    0x30f04060b011803110a03080c0f191218050904080a1b020a0501030915020310080607020d0801120827040b030a05030306210d050304020f090402010e0103020c0f01092003 75
    0x40301c078143c03028170b40b17034940c06140442d000000030b0780c0b0005010b0409400c40a002004424026a810408030f24920742507c920401698001214808500c45404440c80c104170403040c4812410100002c1d078020704d034031800c44001c0008010b40310000705203140c0340d41d88294020018144500107201c030303400000e41c80f070340850040c400f80d4407940c003100b10540070b007128840b94400d0301c407040d00707e030301c1581c501307004610302c00303050084200800c59185c100e01c80e8401000310824030100105552818000c00007035107101a25030007805452015100d00300c54030030f0b01000781001e0502c5401d200110b02d1a40c0d004da42403a0308040b0714900414000d8541c3d03040b10143d4510b599220400041d030540528103403440c048600c0501885030b08016a00a1000390b8035000d590741003900401c1038209004400c10b21842d040070400006036400154007608103000c0c200585c840c084040c06900304040041100460340ca8117007140c00f0b00460401c070b07000300c800218130311081c1c4104006040d02c1c1d40d5540280d01c0c0c03035002c0007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 170999559 1250 170998309 170998313
    0x31b0201021b0f040e010e0705010503160c0609060c0818210924070b01050405090a02040903030f1e0c1121040504020f0309070f080a110a0803030f04060b011803 71
    0x2d203620600c02000b0066080303104010002004c940c013419000400743c0d5183c940704c0030b400e401c04c4500b01500f801d003041d41c03c5151044401c6541c0f0342c0b07410060f082160781034500c0b00308907282d007101c0381d00c40c0d20079420b001481d030001e4001d052a00c101c0300c3d45120071101403100c3c0707003a13808140c1c10303424000c03520640d42e0340008981300000b80e4840141d298104000024045042071070007501c0009000b0a130300140d0301c5401d82840c500360303001030b0001e034460761030300f020b01010101c0080d6200090b9410355021030442200d00702900105207982c1d041c031806041c00042554192107000045000c400740c04100300300780220000f255140c102004181c060341c40780520b0080e02c8880281c0443c55080c1900c0b0a1406e91a100400c0a0360083c24058460b5038021061060044003404010003a1504001a0707000d03e02e003021542d43d554040741c010741203407040c1613035124035118501c0c0400540214401c490f600d081420301c07e00f044004990540b1600d242080800482d80324004050b0060216001546040e00b55 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 171000809 1250 170999559 170999593
    0x5120402060c01060e0a0b01020c0d0609030c0b0a0902090a060518100b040b0a020c0103270804050406060c120201050f191401081b04020906040e060a03050118031b020102 75
    0x25109036030041d424400c90700511404d008074809801d20390051695414252181d00540f42101640750646d042980444843e80350b5203500c000b1645c004c5030200301082030b410243c0e074403031100b2400340c400d607190820421000c28581084001034402c0c5c0f0402a907940358031443d011101c0500450303512801c41590003041190051b406d40c1c00c03403e2424521103080da50072010110b40d000e6400340d43c0d180300c0400e44100203a0180941140c4590030300781406070302c0000d410b0614482000c410640b41d10021901c0c1030034090364034140d40103030101500800585841d2140a0140141d012302103c9000e078002d45040c003503106005590003821800c00700350698441c9d030002041c071071a03014801c42c0c540c2c3e20050702c0f80b8070110b034800c1c40c000c005100150a500c01a5100c0150301d031150221140030b24010001c803001615044211004c45986a4031a1040e8449000040b61380701e0f641e1000d0320540c2400c00310b10036284030800c4005903c3c8280c44e09422541c0030188400d102d14000b10103405604414401804c2d036001d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 171002059 1250 171000809 171000811
    0x1202190309080f0304050105070f17071b02060d06090608070e15010c0218010602010c0201140112030306031709031501050907080703060513050405060601030902030703061503060501170607030506010512 89
    0x41003920505040c0c80360f07400c04050300200c4058945030344950922080c0764211040800d280401d20f010907000680d04c9104451a13005408042088030440c0700e401d820b40e80e0800540302e280d0040c0740c56074542584e0504005403106014000c1903610f0014002801813001802c0707004c0f030b070005404000f0360707a84050024001040400c07049c10b2028808200005942c1c0c8443c01403000f020000042981d41004c4000b821a07009450840c296851315802c005020304c000c40050468504281114407417070549011000340175903500090102d582c10700d42000c2c0c0c26015004e0544050b080d41100d250091f1a03555104495081c40340d150032500000200305000d1241460a038032008508010801d603503030390089094025002001c0408641e25414402003200510090307402140910341880004401c2d000030f91118110300c8000e204695480c611440e54003804e50520003550064010001503039924004d00c0c0301c1c0c0c40004108440d01641c0c00141d541c900034442d29000301d106940c0c0908050241c20050390100d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 171003309 1250 171002059 171002063
    0xa1814010206041e0b010806160207060e1306090c0c1a1005040f150611011a06041e0807030305090f09071b0618060605150301030206031b0702031605011202190309 72
    0x21045003c1301103500401183d000f000d504c0000d2585181941e009000e90081c0c407806e00440d006007108201c02540700035003500c104001c85d0159012071700844803a0061525034404039055043c20004820a508102400301c01805241c600200e042d203951003448480048a110441c0000c00006000c1c0782800da001040e180c0410b0000207105201c24102a0800c00302e5111800007440c80418440e404400e02a001d05003515500c50b10390804040c0c0051514010b9014035103104102d0b128003120800e640d5480340040140720280c80031241c680c280244591320041c1554001c03e00380d40c0840035400d02032216881110160f880b69250050040d030400078060365802514020b46070000040344038030002d903c5203400d00c40d903000104186000f0501521180046565001c01014401000561181d40803203034000e42c0e1651403107030b203800c458006403580584000039405100e1030b1110300c101031300001420b0545800340c071002b00074100222480147c5c03080c0e1040750a0300c0c0e280303503c460410740660040d001c4d140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 171004559 1250 171003309 171003353
    0x403020102120115110106030c060305070207090e06060a0e070c03030f20030103020306010e15090703180b0f0105030706090311010e120106090f0b03030702091b0a181401020604 78
    0x200c10590360046001003a00807a0003902504d038094621a0404030720114501c0000c028041c03540f0f0740d1507403208260940326010074551944001000d8a1082c4958005011030960421010038926a000c1e9148070441e40c450040c10007d60100f0b03004940740705584180020b0380d07411000c0b0942d40d821405003910008410b01c0c2c6031036500d00f20a020482500b003920360f900e040030301d4580d0b1540c0101448c003030781a400024912100b07000d0140c50095074000c001c10b80419650502d581d161890f041700140040c00003540840b60ba0816442007140703007007c0500441030140c03e501942d8a0f03104240d2241c015114042c04100d00441c204009444d05986d01d041c032105042110009400704042010341f0120480001d8a96550205005d520344c0c0d40704003c05c820281c00300308850a203000100c1e540b0703c81c03ea03003e4481c40e2940002040152649401c1c282e10a50b60603098544103041d401401503510041c80d1a9480403078080802d000540d81212140144164001c124036200c0703440d0b07e0055001101103040e01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 171005809 1250 171004559 171004567
    0x12030207122708030c0d05090616050709020c031c0e03041a0405040c120608070e01031103101d070518040803180102040308310933060807020102120a050403020102 72
    0x1e110089580d0040100c034000c0e51350f801c9800801820441e00c454240b003802424442c8d00b2194a07048283c4004407a4540282d030302d504241001d91801441390301ca640c00900014010490110100241040d510315507110342400320b8408031642514003400440c240780e4400c0c442040751019601d804034442c41010a114503281d102c0380894246d501640000b40403e4a601402100b040540300d044d000782142d40142020030306000b0f0740c02c0d1454042c4005003240320101800b85081c0d07030034440072200103441e4108109000001002e1188203003140060fa03030500030b0701d2000401c1c2c01c20350450449210702c1110740901d9a180e179945a60ba80010300001000d030510005286810070906c0280301071400f0f8910280c0b038103150b4060260402c00c040e8000078600c81c010300c82109070400c01040060f078481180c041104040844c0c00710342c2d022a0710f03420305c07048011003107842c0c141d401040710307410790b0201c5d40c0f0301e034041c3d880d000d043c5c0c04d0f8070600c844840c510601100007184000207621407030700184030740300142c070b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 171007059 1250 171005809 171005867
    0xa05160b071e0306060504030201050a0512040b060f010201061a070c030f032309030c0411120a0c02060702030f07030c1106030a0b010806030c01050301030228060302071203020712 79
    0x84603004840000200c2e6404004250041c048502064103203140e02d824401d490902000030a14000c9200007414000e011071280246400342060740c60318840754036070412a15140c1005403146c0c0042c0e40c1680101c3c1c800401200c00d51040c050300d4242c1382ea0301c2c0c0d03444d080d11003c15244040e9101103401d4071000e1848401000040306451060000d50199070354140d1010a401501c02c034203100078580e02c51000070081d10446481c0800d0702c59418008640c00100d075140c825030030791a0b20444c0070000c50042200104101810654070845001c01541d0840d070701c40d0b03034003441a40d49108a80766008128028040d820009100b003846040c482d10840701c09400030030200100314550801d40d00710700b050b902d51061603280d50340480d0382903111000710001c1c0f01c205024030000e41a44410301020780030791848501d03d000c0030039141301800c1355a1003203a00c00c442039946400900075006554100c2c0e03690b00c0301c010400014403a0080d969459001215010034000800040e1400d8525290202d0741c410315014900b5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 171008309 1250 171007059 171007073
    0x4110d02030706080a0b0d03020d080a0f110418060308041203020c0607060f0b0102030310060806060714070602010b040501050609040e010f02041502120309030a0c1a070c0204200a0516 81
    0x525184c0c840d00f045040440d441015200d10351030b044c0c000c400b10460b00000c0b0741d0004000140c0f03440c90410001a890f44007050024020b200203114681741002801c0c580c820300800140300300d80d1806940c00d4002c0100103480300340c071118400a0b010071402c1c0014052030b1a4100680c0d099482801143e4001028102041e035079013001100b034414564034056450820018096041c10b07807001d1029625504e885000d4011443d403c1c05050f080156410019542d9240c2204596002e074100c07801c214a003106101c0c8554a11150003880b00650071700d60104403904003801020b058070f4009040341e040080e2036060000a080000f03482c040c5649804922510061740e100800240440003080e942c0c00031081c5029241042d03801c030000240700300300b080182c25007012040d00c180340010303d040b6004041c103080c601c40320000003d000304006407810600014980050703c81c1d120318400d460a12403a000021450118401381070035840b0744104100f419000e5207e000180718010703440e10406c9580400380c071112 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 171009559 1250 171008309 171008323
    0x141003150f03060b01020718021602033003010b07060507020109170a140702060304020409080d020c0d090501020c010801140105070b090304050906030a050c10110303070c020a05041404110d0203 85
    0x1480c0c4101c0c188240207001c002e000b0000745100a00060150300d01e010580075902618511524519601107107602400303001100444101d9001822100181f000503082c1d0b0028481c280540b105c1c1c0c44858040740c0080306103041d06d040710000d016044c1840c00325220304000d0326000340080d0455684181100009079644010900d40c0c0b1880d000b507464150316080a002d10600322550500e0070010b000d54001030746d4000c120f030381c002c0d410351b00400ca08a0342d2504240703901030120407840381800031a10074429400090421180360641d41c40d00d4201d542c4a00590320380001441c07503030014000d8401488030343c1800b1106000450181741240c6001203a403505d804900b81901c4429090300005401c100614015070b00700c0c0c000d03000700c0142c04210b8641c1da5042c1d540079813803c002d010f03811841c135129880c0e000e82c289500400802c02078aa0301e141103240104006820780003244181030300c15001c00c8600b02071040150003190308251112585680d2908408005202c04e200d0b840724501540500686040c0110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 171010809 1250 171009559 171009569
    0x21b0105040c05030d030b0915061e0c0105070f080a0b1318050c15071101020c0405040f051006080304090e01021315030509010c0507080a030617030a0306080714100315 74
    0x3081e2900c0c1003804250802070300c01844010035081120300303d208e0b40d40000d1203802400005181e1541010341000c203074603002d450200281d01c07540455215207014030f43c000f06a0924000020080c0303a540c01810340710b010030340402000040e031000000b42e002d20b00d5030241c290301100034090348035501003012007010303929202e004403000c0f0208850401040400c0105010182c000c9a00320325062440d007030340703405000f4504064034104010742c800d20143d009024000b01d410000c1c1c018012486c150a00303402104042804480500c1400c0030801c082c4c0a5100300416504450f02440c6040c1ca040c7c001e00c0a0722100780318040c40c1d50f081008002c0900d061504c03200804072100c600790460001c020160480d00c0c01804041c1ca81d041400100d00d059000b0102e50045607c2204652110100745048004050540080c030000c6c8440074031002c22000040078100f9101582d030184410358075180b003107403038a94a1050484583c0091441143d40ca080c0e01c03541041242450005510b90814454203800d400c0c070b0348a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 171012059 1250 171010809 171010823
    0x12050901021f0c0905030316080315090f01030506130302100e07080d080609070f05160813170c120c09040f05030a0504090b040516030b0f0d05010f050106080f0604021b010504 77
    0x319000f1683c01c40c2601d0001c1c40110051401d06003056003035245810721000003050070340c001000034001e24091044c46e04049002d000313110246050a5040d11100c1c003070005031070602c600000a4500340c002400c50184c1d0f5419070141489107403403494440601010004c026890190a1021682c54001c0180202c40081075035880142d05045d014040c0c0c91002512102c100018105000b03103868101c1d0880f8210080511404031050080c188643c0e0b80c081c042448201c07001070b6000090680d8a86200d05e641901c040c1039840003c801c004000785510280c1002844d5040030703184141c6450091103030355002c3c0c0074449584403000035a54245c10740d4000c1c7c9c0b810f80803071310110741404909020721403440c0e402c02c192010405410840e14402460342c0f0150101d003010340354110411962240208203100b4800074007444528070b01032904a000c0c1051107860751b909468640000745d160700c6081c100380509440c0030100c010b070f01d4000511020f503201103000071010011403100c0030804801d2041511490007820 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 171013309 1250 171012059 171012071
    0x21e0102120106260604060305010905010c0905040209210a020a0f060207090e03090405040201031509050a050a0204060c08070c0e070804030f020616030b1206130506060102010912050901021f 84
    0x151000e40c032801a0440743c200050148901304050740d80f401030011100c4040d6103401d40c0d41e060002005010281c20040c03065080c640c52404102e01500503001c1c141a680b5082c2a140c0c445040c0003c074040d8584003a4889101c1d01d0045101541c0f8007081e07102002002922041780582c5c0209000916991200a0205410200700001503050040102030000840c091150110b5000829903900800c400071340f0907035540b004201160700a41c8952a030700c1c100b9540020f4a56107020a80060104603950f2450a080100203028a6914800c98064490944800082903603580301c0d0b0002e508196804c4031002000000400c1070704820000510174900c56485004c103241c1490000c06841c0c9030071080003558032050034424080b072507403108818030320a4074000131148001000120580c4103812409524005d030810301140707107007811000410b14051800c031205502e640340120300f200c1701c01034041e086103000300159010300c0c8600010301210300140b040312250601c04d4024615603000311507040740141d40398 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 171014559 1250 171013309 171013327
    0xd0c170304090501080102030f010608070c02100924050a050708040e0c03060f0a051e130515030f0604030504030201050711090702010b0316030803040303020309030c030d0617031e0901021e0102 85
    0x10103411301402e4140001c0d800d50420352440d05020406002c0c0b0300078409680c0c0050480c5108110011450b0b400518000100b032005101814404040c02050f00c00c40c40b415208284820002d058000480680c0e00c082c6800d01444040b41c0300e80213400100d4601004002c005000800c3c6017445000d0030300702d40300503034070704228040090202d20301078114040d40d1801c00400187c0d460388940807420201d802440b010104410004204030200542840c54a140805000900c3c05e10400b07400035640039821a106441c94260300d9039518807c07940280081e100700014001540f2507009042d8143c89050500f0500d6800b9000503568481240c3c0000142e40d103811b0346241d86410000c40080942e40c11482d1000e90850312803103058030006001805050b000404183e0500080088410402190061340e8403810ba03803050a01400c1c862107041c220030040304480440c0d01c0084104c0c0c004422000c0004418440034520a095030441d03018641940100903544041d6140f05203d079080c8841c2c00001030b503c072015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 171015809 1250 171014559 171014561
    0x301090506091003030f02120c0706020c031606030f11030a0f061d0a020309151003050706030225020f03030d0219050901021f1d031e090604050d0c17030409 69
    0x1d100e070303106050741030501400501150141d003e89800d81380078000c0120030310041c0d103040110712882040c9100020301203030022001c00ca10094035415801d0b11658603403241095514050206204c3c1c070f41c54000d4041002e103000342e11118a030280c140c80420136110007402070b0080d8000300d0b0b0031990140c0326041c400d5140d07443d10500015011044888ac0340250070b44003c801c0f100014810550f00e0b90000214488100c20000c101c500408502008928607128658a80b03d503868401150584185940401c03450f0180c0280c4007410140a00c200002c1c84039154014200780801040e070b00070300d1046c000d42064505200419680701240c07400341c0c0d1000d142c1c41064010175190013440421030144020b000681c0c0c003250201510454541030501d600c243d8a03a14020424042c10f02607a960480103480050170110143c04081c40200c0124426050300484901c10304c192007907241d206008000500040c9060040c0a140c07500401c11a001c0320b44034204070b003036105c0d044c2c0e100c0030550001c41d041200b82d0007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 171017059 1250 171015809 171015811
    0xc031b0f080304051905060703020a050d08070e101e0c020109050904021008090102090913030f020604170703020309040e1501060c030806310606090605040803070b06030f0d0503010905 81
    0x2450404100e18003141c80742c8a0203207015282c4502a1140d5080700b489030844000040d0500621103603a81d02140350280d40d401002c04216507500400f4051481d1a006d40c8900f0711841d10b50725004071002c40041081180400d02a0f0003050204d42c200001c001016912403038035000c200d884444230b140c0395000261040a90358080f600c141c3d012810040180ca40d1490f00921340014101150541c840743c03000340c0a80913040c005504003030001f04015550b2a1141100c4019000c0c4e1100c400c0c0240302a001c82e1541d40440300944184c0741d00f21141014106000100407150103441500c3c14070325004000360940300490610000d90740400300e0304124804c0c1402207801000e05050070481c3c200a0303900034010041c0201400d228080d036a0356903054040940313000a1090f84400d440c240264200f51140043c480c0d800b80000140c910f00f030104d00c0300c0c001e008907425601000001d5082c1166a0b590201b2094020485a018000c0d000e040809140030820556001d00170340390140c6a42c1491640400c481c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 171018309 1250 171017059 171017069
    0x5030f01060308120612100b0414130318080613030807020609120906040b030a0905100b030604122d021b1003050403051b03120604020702060a0e0109030c031b 70
    0x101d01041000028081421600c880d1100c1a483e00c3c150307610350024108951a08018015000702252800303d00070542c403403680070104541c1081006042c0c464019041011507410030f01c02201c0245401203030165201600c1c05c02001000da113103580742c910b03c0b42044410b4480780c98100700959000d0802d504207500a078000c0d5607200030111840c01010150340c0e41c5591a00c045a66800202c1c0e40998651508480180600c5c00d01250b80741030028145004100c11041540c040c0a200d19100343c01c0c0150080d09103c640c010000c10281c0c49036140c4c40748041003849802c041c4400c1d813500303525850029001104211220f1401000c06d03005102c00380c03c00402ea9140e1100c44201c4a60b420f503582c4552881103000180d140001e820f6a0b01e18081e646072050700c0703200004101079400c10100310800001400d039a04074114425064440400f40f000740d014048000394881418001100600c0c480d01000424001c149050001160b990300d410165451030382003524100a59003d00001d644034900ac100100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 171019559 1250 171018309 171018311
    0xb06030609070c060204090c0c120e0d03110a0b042405010f090504110910030507090b0a030206031e0c031503060108071a0c0d0e1005090a030303051f0f05030f01 71
    0x1240c6800003a4403020020030441c24000c400c0062000e02100c0e40c152405040310160400c60100300201c0a8480140340d04121078040308048110441407050480c0c200b0b201d00a00003050605e01c41c0d40580d2010303d032031074500c4140b094514140c042820603a840340140e0107009508c40e1a10b100d04044900301440080c0c581c4107043c000100400d407451400c00301105c0d0044800101601e551414080040401180c10351000c603020a0001da102e41c1c41c20002140e106004640c0413030350f03505458058038001c0842e04c1e070000c0480410005810010011a448181900c051514108043c0c5030095810143c1e05025440408410800c074a00f0f9600400d1555808900a10721989072a54155468411380540d100700c04034242da8400c90031060040d950a041090182c0380340581c2c804008113001d100c0407840d4031504000c5c1c1c0050342c01b40030b0002c0b601e00d5103014140c00d2086d411a00c0a502400c0c01909442854005a42904101c5070a004440141440e030091049407460300041605d0038503501a08000ca03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 171020809 1250 171019559 171019561
    0x601030c051e1014130303410c12030f0f0901022b060503190c1a0a0804030909050f1008150609060114041e09110a0311040f0603050103060b0603 64
    0x3954400c40c81000c07110700d62401c1507482c0000d0107403c40364001c0c9210054176505d80c0b07001000b010b80009184c103a403c6500d40b01162007650b2049484016403154060041e19a405d088915003000f42c001450a803188000b101c4c00d80d0194004500240e200b2030303030071603280a5081800b290750460741d8041d070080f40002c020b40c10110f4903803018000c840316a651012892214000e200b441c90190001c200800004082d240d480b10a42c005500802c0884030032102c130304103c0c902080f103500c07281d034003040340b00081e51843c108643c012083e0f6850034094401e40520600b480d0001c1d5006103402694070809171aa41c1146a08280425021400c3c140e080102281c0111155605206405000681c081c2d0202c4002806403110700060340c12004540d000e1100c06000100410425600706a101107070b0030600291780d00c281d541c450b0600b100e4a0740d03000b01c52020100080d284c0948280c0103080d2004400b079185103441d40d21204418040099030110300800d44070401081488010f11030312180c280c040d030b071091039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 171022059 1250 171020809 171020869
    0xa0f0b0a050f0111010f06142704060504030905100507120f0c0803041109130506070c0804090f0f0606020109060510030206030f090a0f030314060103060308030a0f0b030601030c05 79
    0x4403400c00700c105810000d11403150003982101b50000c0700028810101009290b03242d0090b03003106035109802a001e040305030109403c0c0a4101500081c1d030080241400e1039032078a6036604068030026009404014034128042b5403030307846076101844001c8940300c6645d00c02251408400d2103180742c0442c014400903401544906070010540501994414036244d0380313654601e011484074880c81c044a41101240c000c00650b401300c548000b0200b4041c00c01c550a6945081b03084605606880c401402840c0a01c000c101c1c1d40304a0308170024224079002c0100f0450700305640001161419840040141c0d141c0140c41d050120901c255030300031501507100d10a0174215000b0031568400904540b84514894002590f00c3c10180201c1c500e4552001c0c168000ca8400d090040c0503240029000c6060081840821095030080c4a040f048179030007400b8070b04654804105038020b05000e00c0400c0e40c580c540700360810558081c031050740658800e18220b5841c034148420b200b42d08409105c448902c11148a010700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 171023309 1250 171022059 171022069
    0x11221050a0c0201020111040f031a090a03030c030b150a03060e01050f15040b18010e030f0a060e030412470714070b04030f02070524120a0f0b0a05 65
    0x14070044141420081035070303a880100e004110514500c603510340042404241d40d083d00b40c104003143d01030110800b0b07110103c4a0710b45a0001640c41000361391181200c81c2c0028041e070006090180c9130308000070f0611000317020418032004030f015425040d00000d00036501641512030b05018040d400e207619401e40c18680811402c0303400e0b5040c14403456210401c00b4107030083c1c07021207000d0800b01130400e171500c0c012445412050000740e807007404940d0b0504a10320070b040000e003aa03088203183c0020000010261518030040010603d00d4010380800c00020502440c40500c141950323104411604200500000d0340070780104041158805010980400640d9502000e5110940c01e8111600b8040e480d00f40040c2c800c0240c41c4450f00e00003001050b000d040c411402d00c950322a600a0f2510541d001c0184000c0ba25003469000f1264403814a13824112900d80440301e44000101c40209070380380c101c107049a82c516100c00c403101e01150303032a254052540d45482c055404d100005490702d11500342003000150b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 171024559 1250 171023309 171023317
    0x309011e09111302091201020403060b090c180102011d030910021207140703120323011a090402070b011e0510210b09010609090e06012105010209040501122105 70
    0x161051034404150210320309207604650100e18001c0011503143c1b490029503010390081d10007035030454a8000b40030124104644000d00c18001c01e0101468030322003400025029612800f05411990f0340d80c040307003050341d1044402d54510090402140c07a107605ca0200b11004848071503010031500041443d0220040030b03c1940c0103241d2150014018000c01040c1c64600142c0e5440940304a503842e440c406241d0b01913000c0f242c2146920300315010062010020390b9080c0b403e00c80c8114489420840480003484e600282191000080c4058688035403a155a10100c5003030b00042401300e00385600c1901c080604100c0c42c010102503441c64510481c0d400003170322081c80211000752174040403c080b1031280343c035404481c0300500106603079001d50f19501c00900d60f196602a048045203482c4169030300ca43c000444a04036043c2d84a05590700c5450b210b01d58502c0380d10181103c00d0340d024090040c2c59925402124060704483c000380d0506000e5003404540c0c08100f65400f0102d26040d40c2d10741c4090343c420115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 171025809 1250 171024559 171024593
    0xf060306090b060c0a0201050d20070614010f0b070203010b060301030b0601080a0b010e01110a050a0605060127050d0c03050a030305070f0806031506030718020c070512030304020f060c030309011e09 87
    0x551100702c1c49c0e0301140074003103002110151507403400080b80e4044014018010960103000c0800036a01d000d031200c1c402c06028000e16030002d43c540c80410280c60184003c0030640c0c40640003140350315414010030541d070401e0300102e07400b800078401c10a031540c0c041007040c1d1103400300d5024441a0700d4100043c1501c0d0038018045d04210f20000086c06070710042020682051f030120482d0403a6026042200041c04145d1b812800540d11200d800c032600180b0f0310000344a15980c40c00c28101e403a1208005a0341c400301030407154100160800404941d00740401c00340c0c54041d84002c10903140000e030081101c80582c908005100401040c0081510700044032405010780320058401515110700183c94050554010f652a10010380e03007068100554029284200200088400050300d550401c4020917407444c44c451664001d00000d00580b0b0900c0040c2c00d52600907240910308100c0d50480c604603801252500116912031030b5240f450140060540da91000e0140c00b003001d58800c5c0e0318000b001c11141c00d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 171027059 1250 171025809 171025817
    0x1203090f0117040809040605030a050606090709030308010b0a03110418050a050f0a0b1302130f080a0b07030b010504030609110f0906031b06040f0303120e0d0c1401060f060306090b060c0a0201 84
    0x10b07004c6d1500c0e4822006004001c00702c4910541c1407400a9544100316807090040b02c21101060b03026019002201c1901e0b07050b141c0b01100d07800c00b0786207102500406610420152a1041103654451580050016003104003035003101800402107401a01c50240c203a415040c504020002c0b00c3c618806100c1c1c0002c4045004503603401910006001106c1c46000c141000f80f0001c1d4991040a0302040201210f011480c40c5e20340c03581e5100403030b8aa4542880c09001c4078540b20000315814440c1e400011507100506115007003035200d0f1201c0c1d080f0307850300340203c074214040301b25240149490b60758030200a00803a002e610b40d29100c000b0070b850b003001c3d0303120304100d109000e60008140d80d01002c2e2409031421803600c0e4116643d84c10010041c3d404100e41581c13107880c08409541d121008102181006926204c84020601c01d5441041006164400c14215541d0303000c042150303464030342c2110062a02c0c0d0f4000c01c800c1d05007109001110207510810740b064404001380f44000e200860f031851030300d0f02420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 171028309 1250 171027059 171027067
    0x2060709050a0501081f170f0a2303130e25020d0c020103060302060a02010621020f01050a211d060f0604240923060a050907030b1203090f01170408 65
    0x1040c00302d00380306e0001d14816803004a40401c8800c42e0101038103011702c1e100d04584001543c42540754607500300800142160503060003201c54410030262020615079107600300ea1401001c0040741100000540106219002c46401d20141420303c54001415900800c2406104030305c2c80300295840008150340c20601c52014581000e6a00a6101d400196009028582c0e80d08090303000a0080c510b80c028280003020a503405000100003110040c00b8a501911082007880000010f460580200d0007283c10082d5081c0c0e5581201c032071074004288104180000b01d803e045011010498418860610401d0fa0000040140b8008540c003071581004090358005a101c580c030750718030300203691400c0d092480d000e0314000185003051548003034103003081e001008050008600c2d500031109415602a40e01600c2c5030024841d034500782802d035030031101c14103001a41440300070100d00f040211840405c0e0a41020454a1140c00c140140520361482480c00c102410364002036600100e10140c800b40014202003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 171029559 1250 171028309 171028321
    0x90d06050901180c03052104180f09030f0e011d060c03090907020a0b0a060e0601030b1c05030409050915011203051224100f0810030c0308040602060709050a050108 72
    0x7510566040084a584101040880c103002d002c113045484200c1c0c0f58415284541d0103001903441c0403654040c45c00c0f03058501803415400d01e41803d0400a2610341c03581d50070f1070442d8000e0709e201c0c1c881414442d4451802d45103920030068000602c511002c1c2c1031014040304d2149072052281100d4850200f00d54141d19004c1c52492685580500191141c105030340c0c0007809101c5400080a4090324420103895200355240c07620306080d80c0f240d205242e0405040400314440d58003035000780150640140c00e070b290802d0746a4424403211240601900c25800006091003051064069590320000700b0008000c000c1712440400001300b0144154210800111000c50406204008807a1000e03c0307079141500038103044485440f8008001c080f5030603084100414225410441c0c04008068080c1d254070101d946420420b07148420010640900c9030704950000c80042d82d125078690185002d40c0c000741d101c03824001e02910300304014041c0000c0c0050380e001080280e50340707085401501c0c400e01c4c10744501e032104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 171030809 1250 171029559 171029561
    0x90103151a0c010c020a0809060304141b0108130b07110f060703050114010206040b011e030b07050a1205090327040c180b0906070f02011110050f010605090d06050901 73
    0x20350030007000e009001611481682060002e09003004100000304280803002c541603a9941030701c600100003070b105001180807032500b500a03541c4140109509000403910304070b194100070035603407030501c0b080d5402044421540e0000c1c00c0e90b40072014004501210289441c0d42e045500000e06c88000c2226a03000024182028829840c0c01c41d001c00c2100e07040e00301200040d010740024003460072907c000051a0309150720014882d405980c2007000501140d00740080101445240d03005111000c0f00301000000254503039072140d104000c0c07940c40b5500c821480c03c0c000c00900d100490042690f00302001d10015100100c2240c44070702519042c02c6041c20000100e480c217041c0044110303482031130210100c1400b80c106841000556802c5002c04030242c03220b0740d490107800358002070380e001402440007500103034014420001d84d9005051030202203a100c4102c070320300312303017202c1c410000d58542007440044140c4500580c05030019017402400c1512420208200000d4030101515140c0c80d04046010942d003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 171032059 1250 171030809 171030851
    0x1e11090f150c0c01260f070c05030304050304170616030b010c02030105041104110a1b050708030409020408060f01060203070330050405070611151009020c0a17030606090103 76
    0x2454001c42e07110300301e03010820f40760b1031072a10700f40c0803078400a82d00000003490202c81c01c0f090f61041c8401240d0b165a0b00b60a403144009180400b4890b0f83e40b000e202088081000d54440c6100b08000e556070f6050a203019103e0b1351140c107075000e903480368040c042c08640010740607070300300c1c01807a002800ea02c84000403030750114544e0f0041d401d9441c100900082c4202d940e90300303140540c1a0340c03d101c61116590130103814486c610660000500c41a4081018250103c0401200f401141103480c40c2d500e890345182160700c680d00c82c1c6820365001600304a2034506115007540a01c00203c0741030a580741c07180181d107e10440e1402820041880703491568107002d1040c0c403040c0b1a40c441184554800c2a2085c4000c000984003501d8501c50f002c400102c0510507154101c00340c0c09500500556080c0c8143c45264490103001e018407121a5080800d00020f0351000d0030ba09803a00c0d000382049001e07401c0c0510f140700344115070748000c01d0400421920f601c6180c00c0380c4840000f0300e80060032510fa131401ca04c002e50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 171033309 1250 171032059 171032089
    0x3110f03040f1202150708070f080402030a051504051002090a060e0a08010609020d14010305150a1b050a0e0a0303050f0a03020405030d0c0201020706090f0e060f030708011e11090f 79
    0x7083e04216404982e00080b090000507008820101036294514181c901001c11205440040e10302c0040701031051280310b10300c1e0800c1c0b01804880040409669450a01d8004000321030440220400c100c20b0000800100014014521045291414140c0882c3c02e000e141d018680c180000000c2170001622070900050007409184020410f150311080da05d40a540854503000c24076040c0041c4400110060006904995014004200b000a505002450000c0c01421194029516126141220380d00100c0c00d84a1313501d076070303100d5a82440200117080043c1170511203003d03440481c070500000303401404443d4801d0304002403d03128120300c0411406403045420a039014010410301d4145e207500000c2110b00305200340c00f0745481a403222402c403032a00d114071590b070001103151001c002c00d0000b08261a009038000e005c0207005035041e40482c1c81c0080ea54411605607540d013994100400030410101e02409030581e00384005103923145401c5d01401003d28140c2b06d41d2000018105d5642ca103221b8068181c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 171034559 1250 171033309 171033323
    0xc0b030414070b09120c030613031209080a080702150703150503030706091103060c09100e06030f0711030a022a0d0c0302150f07030e0102100e0f01060603110f03040f 73
    0x103600c0b1801070a0f980c200841c85805480c5c0400f00e06001100418242c1710ba01028005100315074814000b801c07400c1000109506110400c0051454406507000380700c511409103680c4d507942e444040d0000e146001c010402801c6401c003a4607003011010b10300c512030700821980f074042a1f408400d108424a10002e6005a40c1840001000c04c10440781d6040350720190701400c190002c6504c4c0c0014540c5032a81100e58101c421010441450203281641c0c80c20000800791030300c1444a00c01d040401c501da40156510007880d2299400c101480d07a1101a502c0324503000300c061420a1400da074042d65404c50b104c28000d41000314041b65540e0189948820302d0940d0050032143e0f1a0f80030f00708810100e150f408141e0041c108849d101400400780d5044030950000c81e88207620b00081500c04541c8500407141060443c0981401c0d4502c1d00554014240c02c460501c0280c12681c001003a82030850302d060f4400743c2858100150b03101381c12150000c1d6400a104801521354903680c40c60301d10003034140c12030010260 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 171035809 1250 171034559 171034573
    0x230106080705040f05011503050901090804030f0b070906121119050406020609120702060c120f130e0108030304030f0909110a02010f05090705010c02030a051c090905040c0b030414 79
    0x25400181c454101c0b14291810402201030014500554a09004c1c000058658110340c0314014440d600003644004120b0000078040190f83d542d540e0781e1701c0769000345c442070241107802d014424080c007810381001150a20600352490011f01610091004000900c82540d87d455540c4600041007107844101880144600000b40038a0180040d007150040d040107114860000314140c1d000100000c8007600d11000600b040000e608000c16a03009007840b8006d07004108c03a510642103803d0240070600101c1e028580c40e50403945c041500800298428034880340d41400400690340007000300c3c0c4c0c002d070305450903280c802042202542d110407103030303c4540c04901e85035600b205080e07894040c011544d40d0780c0c002d201c140c402064901c1901c400741c9100f490f5030800786080040d0f41c0580900000240b02030b0503211128515180c107030034403c5201c1c85031242150740802014141c0d000c03401310007a206103481049141015100c414400c5814040c04443c000c00002240038085c060140b014180030a40c120f80e03007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 171037059 1250 171035809 171035819
    0x40b18070906090801050603060c09041e06090c030504320610060813050c04150e0103050709270b13020415050109090b010e060a0c080d06062a230106 66
    0x2020305140310b1100082c40c00f0f80d010a0000041c05600c2c09107070f0040050425454030002106142d011a1845901950b218009550702c5041c000c0b07042d580c51800000214103181982c0700f000e541e2003800030390400d80f40c0020000012070300d011280d51a4404410700c607240340200100c01044880c60101c0804d0301c00c0308108000c00303450f0000b01054844c10b84d82c8990b030b03403500c0500307202d02c031038500d0001d1494201402801c460f060a0380400b031510710988141001980c3c0303940c039003005082a08181d980f038102010604c4400602d0140c08050028a50000e0711030b0300c40d0040d400c0c840c062a00040880a42c0e05c085070030944170728a4000d00307540007401000005000c080d41d8000100c14481d0b540031403055100003646640901c503503245401c042e1a02c0d540c100903502003180c1903000924081c1032280540e1410081084070001d04100e00192000140c1c081c10044050215640055070007010310708800744490700300440b43c1402426502c0b5408410981d0348078101c09100c2e814482d07104a40d1318100d00041c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 171038309 1250 171037059 171037067
    0x18030b1504060f031202010606080921040504020a030603020f0321070510020307020307020a05030f030f030a20130b0f160f08031609050307030507050d050a02042313020906040b1807 80
    0x42c0c045d42640081180325507405080d51101c2044907444d031a03420654140c42c1080020002c0111000900e20f141e141c20b440d2000142241c0000c0c0c1c900340025901e8009000314200103907220f001c003c00301c0003481c0c20031180c134240d05c88040711000200c2c0603201090302420000100465080610708107403d5440e4a0440e0f402903a076004a0800e80c41280050400a00c604000c035005000403000c0002e5441c02040c809201e601d0f5102400301340c50551340e0401080c0f01c0800c0403600701c1c40e01c0344021242e40e40200200c400300340c2c0700715041150305441c00c0101e48042c002c00002c68481c40002c1085102004c41070911402c5010410005010f10000001b00b10350192502007022000300f0341c0d140c0100d13481d11501416600c01e0a400014020343c82354200b84180e160200c1d5080c10309102da82101d80114180c0e0218041d110001505024180c0041240b5420a114046503602c100008034805600403903030009205148060403550040b0303075501440c41c4607201c410f00c107040404090840c0d00c4d182400d0170010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 171039559 1250 171038309 171038333
    0x307060e0906041a04020a02190302010207120f0203122805070210110a180902070303060e06040b010207090b010302040f141c0506060f060714070618030b1504060f03 73
    0xd01c104103030000966585880d119081d80b10a903015840e50601449007070100940c4601ea00b0310951069440c14402100c0c4c03080075203030003442039001580b0f4140f94a030125240c11907901090902408801052596500000f5100c803c8000d05140c1c00320f031102403001e207a0007442081402ea20501d284818043c45280d08203e00800080d0300700d4003030118002c040c1c4111034000e604c905100c0c004012116215100e0384031201b8140e503000e512007850399201440340c100d0b442598114007007a158281000038881c2ca1900543c00107095505005800b44080000d48030007450142e204140c0d40e07035000d21000e911981c140c0e0050641000d08503511038440c200001ca0b8441442054880c0d140c11105000c64001d0b800c4500781c1c0c2d98003c000748101c0c1c1790712040014078032000701c0031a0008130602510b400f0800486508240100310000f50a0040c00c004005145240c0414a4034145a40c1ca20400c001409030420700d03401100140320a000d400d6101c00600030340b1443d80a526181c1d076a16022003403040406203c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 171040809 1250 171039559 171039587
    0xc01020f0c09010909050c060d0903031a090f0c0f120402100507080301031203270218010815040611070b0a0e150c090d0212030915040f0b0a0c02030706 67
    0x1140c0000c901940d0036940c501c0600540d80000707580004111000454025200c2c0d070f4030607025a4201c1d141c03030f40420b9079034120940c035200e0b00752036030520000e140e05480355004184200100921100b02c10000c81c80c143c50103440200d03060043c400040d6002d07000c10584099201400c4c0c102d90b40d0915141c2108041d805403400d903c80e900c2d080078610a6409070702101c24840e8440c035410b007980e195849080d444224412201c2c14141c51300f1031003c07240c00209405d007481c0c4018110660200300350052201c1400b07200361504c40011400018024100e00017030300d50142d03005c0040007815684a14185000d84100c1c1e2140700804d002081001c104680721860f5441062005020484070400100c1d942d624508014441034024081c004591081150002000ca620b405070269921030110b5002c0340501003140c2d0181c02d43d802c086089156454000000644158800a038500b03040c207240100b04680114480e100343c0780c50008180c81b07600d014070366a04103d82c009040c0c40c1e4141c2c0d038545c06003c04081e0100703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 171042059 1250 171040809 171040813
    0x402031c030e102a0201060515030f15031009080403060603080a231204030c020a030c08100b1f090305190201030e060420040906020d0c020705120303060904080f0307020c0102 77
    0x1001c29281014819203440300d140c031a04500d0700d0b0710307513040722068104409500c0840d501e0315404903131601d0728a0381c074104a150b105001d541c6d02d0000c81080c40c02e140501041c8040d230b5400c501e00040c0d600090110034503401c03008005040c08192811818a1281768401000281820400014410b403040985020700d140d0b05c50040081841c0c0c600c0000711241e4840c020702001c18041c0144011203442490741c032920a0404500d400c00d241c001941124065008803890b460301e003820f101c446014003413a0b88050941d8000d00c91407000800003070a411010001a2001c01d2100b0091611441031007008000c54000098a401901c028000c002004900307000768042401d15904000104002460754840c0703070050455400c0190108404c1043c0d40d841001d0341d8059251805080850b00d50320081014508400e0001026081c0ba07174040e0500d4a01d512071889950000305550a0400210071a58801c00803148881d01c0e66403890220100e000303506140c800302102000300301e1016000075100106031401d0302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 171043165 1106 171042059 171042073
    0x10e010e07120e0a1101030e0a020d1a0906011526040206210a0e07081b010318050d1205070e040207080d0c090f090504020105120402031c030e 63
    0x8107050076000b0781c8144e0108010003031030b902c0c1c0a9003801c0900031a40743c20030040c0c4541450320f019002d0500c26005000300a1005600075032403540d40d0380c9403138600704686440c0d51410700340240d000c0740f9400c1c10500d060328041d0003070b10000300c444024602c400003090a2040440c20182040740c2024080c8030400300c40d09480824801c4070180d403010701746850549402c00548820240500e110f070001b21050029503004580000c0c22607113103a5040e00c03a802007004800078019425480240c41000c6070050070880c0124420200d0300c61a03035601080903a50401d00102d40d410384885011a0890b02d00c084181001d0b006000750380e014540d814100590300554405030f504c44000780000410603c0c0c203002c2040305050b200007502c641103080240703140c80d5001034141d00c1006c441035a00c4080b04002021944d0400640701100652850000c46102583c00074001e0210180302c5403050290340 = true := by decide +kernel

theorem cover : BRFrame.Cov 170863309 171043165 := by
  have h0 := BRFrame.cov_init 170863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 170863309 ≤ n) (h2 : n < 171043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
