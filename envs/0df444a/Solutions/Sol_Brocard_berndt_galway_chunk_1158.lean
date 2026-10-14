-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1158
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:30:49.695618+00:00
-- url     : https://prove2.me/submissions/dbc91c18-662f-4773-9c2f-463f94004202

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 208093525 ≤ n < 208273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 208094775 1250 208093525 208093537
    0x60908120325020d0e010302090a06080403030e0102040602070e0f16110708010906020703110d020d0c061d030a1206080a020f1f08010504110f0d0902032b0809010507090b 75
    0x160315602c0d2004581222a0101c00d40384520026030080203800034050740043c00c01d5602c1d803080c2400c0d0303c0c01c0280c10019044c08005d000e000c06200740e00c404902410b100c0ea0240e8113004c6a08021562151655006551030440748208811034402c0800142030002d02d072900c074020400c46845490318103030403109880760801d4440381051880380c00c00004901009002d43d03d000f42c058840141d55940744d080c02009a003900d00183e202d644104115080264005152441d000092501e19030740252880c000018220210109a1510b24a03100380020b02012004058014054940303500c2c0304007100c0e000081e213403107222701c28883e0000140c04000d401c1c844489042d112004041005061207809005411000702c5807003800600e5880060001d42480c0c401e00c0c40441c00300e010941801d05010fa82c0000c1d01c2004005403856840fa101d00086441c1080654085010620281440071450702c0f01c603c240000c59940300050900302c04110f01e5901071040380d0284070742c0d55850320700a003881c121a507103034401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 208096025 1250 208094775 208094791
    0x3030c070608192d0b090f060d02120d0e030703050607140708030a0e190804030f0203070302031b03011a030d0327080d0c090e0f090c040906050901060609081203 71
    0x4014003c02d1059144501000c4d400c11031458021901c041d01e0b02e00002010350600d68456143c00100e010315600c04518581c0070301c152046113159034a00010812003403060200a40044455402c0152000c002c1141c0c260140303a41d031581c082c003190744101a540c00d914800030f0f0241c0c22034000f050030070780700708406000c000a0308000c134038100c0740b5079800c01d65902c11160b50020941c1e4400d882c10a0a00b80040d5401031001c0b4518541fa518640b2101b4941c82148070042008140c0307600d410841d102400a00700564008058a002c0207840c11210022212841207a109502e0101380c8030141008462103012200050020011400414420340c0245440004c00c8546e20305a83c0081600180e90031441442c0c2c455540580c4600001d04550180c5442c800b101c070074172809440500c04440214a1943c0c000341e0980d600410b500c3d0007024a0904110314211500070b0300b882d200350140801900514040c0c40e02030008c0010f141e0310030044828001900502c2c6542d0010500a40d2886c828006142c0203541 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 208097275 1250 208096025 208096051
    0xe0a06180905120301140f04050702071403190c030c050301020304150504110a0b0915090f0d030302040b0f090f030c150c010e060f0f1302060703140715060f0503030c070608 76
    0x10201d0020542e41091b40040c41e1141c2c1c0810056560910b0403881081200a072424025414640006501c07000903020f10300c4881031140b0240c40a9038100141da580d0402d001c0310744100c202e1401c2c4100541118041030f40c00ca090400006010704051003200e00c5503401440c2128010048a0120090310300940191a006001640c4240307a954503040000200940e1141c10399459001d400c0c4007140d1902500b10704486400c0c060070042d6118400c0c2000f640c2001c4802c4a0f45045501d0283c000f40030756040100c00480116418a481c0344800003407041c25404c843c00c0c01025000300c00c065480d0114401d4641000c000840310300c0011244003d0301900d072000d0300200c1d00100603c0d02601e030810407100c40101a44c01000d11881c90184c07140c054210b0020003100c1c0c0b24a070341d50003240e994030801f5001405c10109030f141c2d8103048000030542d02042e40c80030805040c260484090340140c90140116141510101000100d03840e0000445014000c1640036002c0f00d0302d440b0f029620000002c0244505e41c031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 208098525 1250 208097275 208097293
    0x2010815031e0f0613020d02060c010e0c1206100501180806091005130b04020d031101020c0a0b0601020718090203010914030a0e0628090b070803010e0a06180905 71
    0x601404400507090b810b145444809050b814994640000304122641640000c1d00303008112643d03661070107550b0380585003c080c065181c40860600c0c4109c0703d0f984099441c0410002500402142d40000c2c098100d48a000c00d0802c200003e80350841950300e084c90224403203040249500407010402490708590110b11500c2e40d8055150030b01d0782c2100d09003925000300054820002c80b40c4660b580001c4003121184214201395542d0144680c0540040d220301030040794401003501c0f4290b064940c0079040e0082d9110041c242c1c1003036403041600000c94804940c8070009003a5480002d80b401200e8004910051440400140c140281a030150030b903099500d80c6040d10214414242c030b074142020030401942d440700d80300c400034242a8181c0d001d600c2000101b1010000700c082d40285840e840c0c0c00e01018403400d1800b0408c2d00e80250381c0c0d201e040d4015010803040240301d0110055412601140840900c65642a440f001203460354055144141301f09082e00107250070a900c0111164465012070358440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 208099775 1250 208098525 208098529
    0xf1209011503030c060617190f020d050606040f0510050111070902040608091c0c1401090b100305060a06030c0605030a02070209010902030105100c1214040e09010615050c06010302010815 82
    0x21070303500107030f0200d03924622103010448030384580303801040c0d113110301800000c5500c03c2d5034442444d100728500c20042e040c889030a002c0d4841181402950042a0b80b88501c11031a00948a4034200c5955100e246003e400c07002d81e100b98007036a0300c103e8202110600300c0b424000107490340a80c0150a030202d21030600046003641d400d1008101510494441111628103190750502e001c0c86500111504844494032580e03140d045a450124145d00c031241e1149010041d61240c010001c1d1903001d08403414403401d000c4d00c2c9260242d028140d82c02802a20f62541d1420602000d8400c00d00c401440400300c071508200341403040b030148d0b4001010410240c5000669000509903110a070012051564004010010788c6000c4407a00702e40d000313a0030139841c45d031280e45403540aa1361030101031040c01440f40d001d020b660100c5044034003408003802c5107510390030302c020414000c044501803400310149050005001c14003480c10380300040a03400042407281c0c01c5a0044035148806002e0300c8e01d0040b051102001c0f9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 208101025 1250 208099775 208099811
    0x9160609150908010c0305061c08030103080f16080d0606030b031002070c0807180b040b011d0604080604120e03060115030b041e1a0607050c06090d0804060201090302060a020f120901 80
    0x4101640c0d004105820300c0001c11481d1203e0704482c1c1c271101415280c0c4000944182c0c00e0300d0460740c1103c2d41503111814a0f40d030305010f1184035954580c8612100d01e2404000f49200504a511110301c0d041000a86800b002e504880c60405c01590560180d0200720000e1501d80041038039900c28200c5400241c4d0380c1c07190625041540c0c000c100c9800c0110032680c45e03c1514071502c40a5401250203001d14005540080c1a42080b6000d501c80b217401c5028144036910f81404170340081c4214400c8074150f14003070510303961002002d011000001c15090321940300703140000b000e5060719003000c005900422402c800390018100402403d400c25110003d94500d62040007080da541d000400380414242545a4500301229504690398420201070084801003400000e08c0c1c08424010381e00a035581e5203d90010f035000c21118801000c055000030702260960341034000520f030501c00d4084450300e4485c20700303580581c0515500e080f0054010300c0000441c0398117400864111504100005841d0710400b001d104c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 208102275 1250 208101025 208101041
    0x6120809040b0f090405060106120b01050a0e030f150901050f060303031501090b030103030f030608070f380a020c03010209010c110d020405150108010b07050304030f0305040503070e0916060915090801 88
    0xe11f81218004002c00d0b0740020800900c0c510180b402c00c40f11183d00700280550103114051020041c1003680d03640c89440c100701d2442c0d550310240c00c85d800c034000c5000c081c240003000c44900c0695402d14022601e241d04181174540901e00040c00382d0704542d204110384080c58801d0f441281000104c078400035034000150000d41c06540240d4a0003410883c0c07000240a84059034055039659021000410100b602803844000761071400410f00f80700a520509217203040c003050191440c03d1002d0410b16a008596001090524070359000c0d00c414a4510701003500702d000d21100706000c00c040083c4400040c40881e889101444d008200c424125000c2c1c011804491040b202c1d8035110216414842056811400c070703a005090031901d1901d041851754446443c1d004520000b0701000d484d00d5038034100b41c02802a1742c0030705005011140001e6803541c6218820105a0391599980603040001061200e81c0360329200741c0c1d1103178031100801d5141c40c000032110002c0032001c0d0100300d400200440c2c843d80070300800306 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 208103525 1250 208102275 208102283
    0x30b180109080406121811010c14010e07080d14070b0402010c06050901020a02160b040618030f060b0a05010c1124070b040b100e0703020304030905060309060a06120809040b0f0904 79
    0x400c034017090140c44110b44201c102495180080c03c500c40029070801a107414581007842c2c001c20200351443d06907070044400010424950801a222074004c2c800518801203031000760442c3c03000450b6010584019400c000c0714007180104111010104200035441a0050310600d40800c45c2115500c13100111070041e03076101000d1350000340503040580d041001e0100740c250380741e0f08480240307030202c80c0e42c00b480350748150801e104980160045a06032050b0030070084d90020340468800166142200041400401c141c1c4540f810800200d000e5200d02101d03540030f6413140707052140c0f8103844200540c01c0700030400300c0494840f40740040c03003960700500074100329442080c846040341400e10749100036610041192140b019600020454246c41d01c20003030b0440258100141c0d40d80341c604041b1103003040b940100340c001c08000305218280000142461040340b803c4c1040201544401903c28003503000140908170800620101c11300d86803540c0615030580c402003400c104c1c90030ba50082030091030b040350306036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 208104775 1250 208103525 208103537
    0x160903080a0c0b07090602030910090b0309061603091a0907050406140306010b090d060b011701031b090209060d02030a02071209231f020f0106080a11060301030b180109080406 77
    0x5020043c00340038040e0800310074100012500e0600038002d50300c1c041c074510076100302c40e0310781c440c40120301910f10100544a03240c0300c03030b5491506c514050303070b02d42e002d490170301c400424ac4c8078406015200b0702c90f5a29070381e030122145019504221480c006030101400310003440c000c484002a0317654130f0b4400c000061540c808840c601200007802c041c240340f0140d002001000f01000078800300c0d42c03a041661002544000d000558604080040f1141355070025040c9001501d54000310a00c82507444901c4c0001101194002c007544070541c07403090307009075030005030440c00600c02034a42054540156903c070503141801030030310b1000e403902d440d03040000301120003048080038180200482602c0c102000300410421480821540c80450208018100c42d082e00c884010b05440c402803007801244007400008009002d1140c81d1059961039440c40d01080321060340c0c3c04e4080d0305a0070302e04107881c101c903017003c05900c040c0e03101e074812901142d04c1d215608095507a816000d001400310340160001d0100c1d80c1d101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 208106025 1250 208104775 208104797
    0x31509020d0905150103020603010b0a03060b0a112104211a0f07030b030727050f0106020c01080f1803040e1003061802030a061e060308030f1608160903080a 69
    0x3d2400c115450300406508a042030040c40903880328802c49045802d84400a69a035050300d404400404540d08032000f5039030f0019034416800d07800380b800b400c80c4120303c098502205640e444020100044110200c842c0400c1c0400c100090303c2d8020b500600d04401c0000c8120f1f016541c1c0d40c80100317011980000003044890030300c9100c1c01e03000c100a40c8485107080801c440707100480001e580300014450342c196400e000060550ba10307840440c8850000c0320f8a028000d9040000107110301c1d41c02406180010311640020004542c03007801820b008403003801c00c4443c90349071813104000611050b1008440c510003003100043c044419a00988111540440a468030b4150b160074000c3c4d460b8555503485242c24400180050780d004100c0500b45540290000303006022111345400484800a0b00a1880d00e042000018010a01e009601c2000035240981d00c81e521124804460404805054002840c020000b0b201c4c0d84019140104902241012401582d581d6036500865000015030400030f0521200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 208107275 1250 208106025 208106033
    0x30702010509070303121a09040b010303020c03011a0d0305070503040b0903060105122505040e01050126070e1015110d0f0212030604061229010e0106031509020d09 72
    0x5141d801070b00d40030142c02d0103031942c0c0300242952406c202e490201e50f566143c01096941d881000070410401420040c82da16003410005e8904809120540160048040300300f014501031103901040c008200c590303810116000141f1408040c2014204c0078131100b000340c0400b15404001500080541840240e03450a815041c1818540180d200d41c0c0a103922039407001c81e030740006c40e00c0349820000030702c8070514a200d10000004c00c1000c4e40001e4009180900340e02e55442d041d08854160b424030121070010846c0514038510403c500c01240505400c481428030403d201d2f03c070300c40e81046a0881400100340c07a1000c21882d1042c600d41c407030100702d048844500556007480210301d081c615062610765485901c0d0060745400c1c03141950442e100740000003c2e0b441e9202d902a1014010b00804200c7c800300c07514102120482008001600310447c1c10300c60128406c0c1300c0362034103896060a900809919040c010342c05092500003041c02c621001d10042030f00d504506c0505031b020f0480350041340400003410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 208108525 1250 208107275 208107281
    0x5010e031312020619030603060f0c0e0604050607030c141c020c0904110112060b04030602210613050405032712010b0603042d03170624090102160b03070201 69
    0x1c4000009681002d448026903200016541c40c20030880503816028101c13507080307000301130310f4000600213490100101080129607021581446440c4c0b61003209d01c8080c070070040329001d14850640e0003013040041000091181c0ea81d12103851184001419040c00e0034109424400d400d05c14401a064000d44e09420700c1d41000180c0600e04103807016203841c141520b4081d60030011881d2035040c0b180400107081c01c007403603501117001001c2458900f912280c50340341c003c0c061b41c041c02e0703000701c040303801c3c1c0c2140005521104090f01812008007181041d1000d40303180740151500400c15540da0009120242034400014405420071682c3c1e810820076000c10ba040040d0701038080540703442680742480558513616610b0840344c201d900f10845403241452300e02d10404804040e0348070500c1107103d01e026404c160704070b003050b0a0203042090300c00301640e0710b005002e05204104108800040080c0030503c00120900041000843c1817045d00e4030100c0d000f009075051800340d40803071139042c40041004012a8288 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 208109775 1250 208108525 208108529
    0x29060a18080a03201e100204030804050306070f0c02010f030906050f09010c020a03080f04050a0503040b07020102011d06040609020f180405010c020c150a030b100c0605090102030601140706020705010e0313 90
    0x3250050381c001c1c11079041580d8480f1070f140c411580807505c9103001c01c014108505851034071010810740d5510b4072403400d00070640140c402c450180c0726a1000c034450502688280e60807650f10380d140094040f07150011214260161042c0e0249661916010040b42d6540500d51080c01e8105401c0c08504004c480c40e0300b1500c007602124110340010380d845000a501c10206504500c5c84003440d02240c40340c0c1881400d041114500406a10000400180921048000d800035074001d0b002001000095018400729505d4030000e448190040340c00100001c1850303108808003400a000b2444012820f8041240514602000903065107802c00708000c0207024042e0b440c0300e09461001c2c0210103481e1012a0442003042441109a031010920f60300c080e2203070b07000001c0400c0041075900722059203000039002c80885daa0a8500d01d04000c0081e607491814000c59010702c1041c0d4404024070081000000340350050700040310f176079070208031450102d031090249881a00f60140a503aa5221541c1181c110110603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 208111025 1250 208109775 208109807
    0x60f020706110c1e0604031b27050912030702072108030f0703090f08030108010509070807140f0301050103080912060c070b040f0f0606080129060a18080a03 69
    0x24103100c10882c100480c402401c16000d450100701c0c04a06000c280800b00011941e0b904104007080000c14031414a0890960252000c2c44490054907800900f80401c948001d00c00c032601800112182d640b81d41d03120950251401003590000d20b500440010181d00507100b1a005900007142031040a1800000e8a01440e8140d40342c1c1d1552041d41d03075083d59002c0180305e01c00c80c070300b030038009447d141c02500a0018954000d500590080c503e20f4812142c1c0c100b030082a110358038100002d88121340001d90001501c01500003003421501c1d1010f002c40c070b0024082d00715004400411200d1281d1000d0181c0d43c061440307440e445485000c01d1003070109190480e1030324011907024005115042a4ac4400c450046030004081e6a8660b550304242e2801e2260b1100141018110b040c2070341803155590140055840c650001d100036102101959032040c1c81d401d50906d031580d01d00780b0020310b10b4280c00800c424200c9061950002c84d03564039a040c1803c1c0c59100761000d0704005000800c059202c61000040480 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 208112275 1250 208111025 208111037
    0x601121a0f0a0b0d0f031404080a050102041802070209060f12010e0319081005040f0b1e0a171504170c0a020103150b070f0501110c010603142e15060f020706 69
    0x900d0720f44580302005c82801400b440400d2245400c401410b20450300589920411111205c90360315001c0d0003544103202c2d25a215900ca0b40083c441c0382c3c5402100c811a400601079002d90315139030200038241c44035840c02075000c9052580c00300324002c280115400c48065201440d1a4100c2804202c25031554141c80c10800003e001080005407403c104442a51001e44000981c00c0035004240014034502c494251f2080c2d8110f940c0c07040c1c01ea506283c121003d01a20f0040280e507031011040d15107141c500c8544034a07008403035021451007008500c154451300500050b161056000100f07170317540c0c0c403d824000454010120300025943c05014000c031160400504810780b91810b9039100380b902900c90014261021400d03043c0500500750030040030b10071030000741682d13103010f03030200e0380201614071003100c0340c0380340d807559021051012031056500151881030f00e1020441400d0003600c110843c48498100f60344444030041a0703070301c06490028080fa0385a240001500303c0d8081e141c81d00c164002c00410007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 208113525 1250 208112275 208112299
    0x27020403050d03020a020a060f02070c050406060c0f02060d050c0403061109010c08070302100c0905120d020c13090b0a020a0809010501030804140d06021303230601121a0f0a0b 77
    0x81c0091140c440c180140390050b26620105412410f15a2030000a4882810f281c803040c420351059005000c900d109240603d00180d90304240010346000e486003401107400800c104010032801e40c03030000c46038030042a151601a580c1c0d59a0112001592090301c3d40a011905100f0005a4803171401c809021480141c14581e02d00c6c0000c040d2840b008004024170301c007003094030800d802080711038520068030200340440c040e6080010198001486110300c11301100c3c0300c0030b030041400305a41c0c07980701032507014083d000941000e00640400d41032241c00c041743d40d0188000801c040403503640c06035982d44809641c0d41042c94000340120300c045c085442c564541801040001c0f4100103c0d41212214041c91103580003650018020380c018000150401e400001c40c001d06240c0304400c54240c0c0d100d003515054084180e41c1495211091000701c0d02c1c2980031000500c11609982014444144906507103032000d0140c05d525091505e098a4500990b0480300034042c0c030308118003c60340481ca041d180300320014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 208114775 1250 208113525 208113533
    0xa05061503090d0f02100f0f0c0e0307050105030c04090203070f030c0e090601031109120d111501030f0c0504020705010b030d1701030602032a07020108070c02090f150a27020403 78
    0xd4811490f1400b403089074604208514003c0c000681c1d900d000d60010441c0c03034000c0061001504507400304188040c605891144007900030009001c454a000e0010300c00d039420800151520b51024001e100c1004061100042e90703076443c001103104079882d580d000c8204e00701900150640c0d04114142c018019049240599030700c4070104242e00100920b000b06642401c4e80e00c1d0a12403240101241d00044400d80c10a40d0700e1001640d02d2007408680d941c151001410144c0c0394481a03018aa68a001104030041000c104010114003400340100c01c001c12041c5d0324070004089038083c04048460b0b944405032041503280174047e184421809007030030501c0891070000324200000c14003004240300e40c040040b0b22480e0380038904034040300303801072a008030b4450300000f280075800c0782c60700b01d000030406000103510030f2041100f040086c0d80500459007645030341c114000b01c200d00500295854240c0103230300c5103075a00c03011414003e2840c528222221003003840c01000c0301030b10381d42c0300c0960350042000b00006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 208116025 1250 208114775 208114783
    0x623040803070c1b1d0108030a0507060b2b0c05063402030d0504080601060507150509010b060f0a03050109090b061507020406031a060307150509060702090a0506150309 74
    0xc2032161400700c0c3c80075001d01c0c081c61600e0741a0000586002c034030344049000c1500017404180018100c00011140c5e076200c00d2a0b64910a07034820b40c0000e40c00784080400902e03550018101411700528407a50854504400c01701d0700c1c14401140491800c9040d1401484811400c103000391030140c0749189498038880c00725420030a500074040d9030340c002100e1b01d140d008141c50000b4281e039004040d0b42c07510010307040041194100b40107000d40d50140c88000644540100101c1381c2c0198040c06018105100d221000b0060034018500d030803a540781c1c001c0900c3c50795800002c05040481e6403400762910750311702d001002c0300c6058000c46003203841c000010012801507011107500c44c601700d0390315241c581011140155401400002074110b420402c1c04006c010000117005458200c5950142c10782d503698040541c1e42c0c0720b92042014942c07008403040d04151041e0011700d55000702030142480e00c1d0181d03000c04c101c10411039010204941d1402440314504e0807801c501d8480d40d0400c402c0b41542004c0300100d4031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 208117275 1250 208116025 208116031
    0x403120c061506020d1b08030106080405070909020f060f0c070305160801150905060109090c02010b1e0d030e030a0203250b0f04060804061d0d110312010513060f030623040803 77
    0x2880785544440c6c010754501200c0400207a03000814076282d50b55004094200c810685003220b55010348200070441c05107901c00c408400303030001c00c0d03410710845840a03c04107134000c60601c0709210041080561040c4108139601c01107105030001c0c180d20701101a02005071040781c104100e039034141410780501c1310000b0806400e68444220005031a01c038100182c0d0101c18035401005c41030300300305001d10080c2c0c040d0b03c1b4003a2080305440030301c0c2d908040e040d5498104200945030740d121031000019801310b441804202100040601202c2d002001500001e28200741c80c4111119041b074541e00c00c014030340a01c0e4020092801890243c180000340c0706044044c06103010303980030401100005014411390350454500310840c14200c0c0e001d00d184004154071680e240d00700501141c6420034400210784004201c59401c0480c0288010503400d0800300300a1180004514000507115240400d0251040f1501001144660800900640301d44800240308d54a807a00d0300703428204008000c04102c87c003040b01d40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 208118525 1250 208117275 208117277
    0x5090403020a05010507032a02031201090f060509060907030e0106121b050906030319120504050a021e011218050f061b1804090311070b04180207050a03080c0403120c061506020d 78
    0x1018850b004038612f010318030602424480742000041c284600303512400030300c54031320301c10f10609803500140310070703118252074860300507400c2400500100d210354040081c0c1d27014580045141e95070f500c03211012814889003903803601407025034060b2030320a58900348010801a035075a006c0d851b11000181d120701540c42100c0501c004c4d8903641c0c0e416403050000d9034203843c240d14200140d0429051032503490990703000407801150034400741c40c080000e8022902c00e0441c140c2d900d0000d100380903002c00c041c214100e0b456481d0f00e40c03116080c0000308180600c07441422014024421450329070540300c003900307200c2c4400b802d031001041821004102568000701190741500c0114000c81249800c0341c80c030590900d0942140600d800125001c807100307000340100d03407502c20701400c808207490200040b4410b0003401042940140306080003e0701403058558000d030140d991909103607898031060140455220b01e54000341104d10103004000c42481441081581842030320600c0e07080c034201030355038100031796250 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 208119775 1250 208118525 208118591
    0xf0901050907051e0703120603081b0c0607050607080f01050907080916150f0305010b09042a0305040b091507110309030102070b0103060e0615040f0605090403020a0501050703 77
    0x4007460b00400031200e5900e0861500240c804c0d41000134601a0820101180041d40c503640301c02c40382c082401784e00c05880d0801409803606010720900413410721140f4402d0050b001c3d0502c00c600e66500d01c0050180d1600580242c040c1e807a003054000c10400004046007580035031080140030540f101d50400f94032840c0c5007409101903c60b14005881c11003480740e00e690802450300e01003006103030440c0c64003420700c064a828000040b8244140c1c20388500740240343c94500144002e139400d03d49078000c00d01c0c03000e600010a00d68110404811044104242071b003001c070780c0340c0082c08100480043c90b06d030b01081e01c6d00601005201c00313200f40d140e004090501010020310410424400c0024400c0b68403114004000b15500c0f03c00c2c2c40c011000c01000d01c0285c030707514901001074204141c08103d062042141040701111030b000c0e1070403c4001c2c03603c500400c242c2903880b00042000c1d00c50005181c02140a0380085c64889200c1c90002e0035182c1c000d03c00e4080509000c00794007140785080b5010512404030042e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 208121025 1250 208119775 208119781
    0xc05030303070f0c1a19050606160f0602070c09050603060106030e03070605100810050108100b0907030c090e0702010506031b0109210c06050406110c15031305010606030c09050f09010509 82
    0x70300110703009202800c0d20840080c2030003d06c4800103056030b840751000f01c05200681d103080c01c000302409203c00f061079a03007240c4551000a040503c60083d1a0700c0b5410040c100211074448444150268024103280c070b40e030714140901d5140c1000402d0042110340380c1802120b030040c80182e1070740690003008000075195804100c0c203200e140d8005014080380001c50300920314040ba04e5001e05001c0c0702e01a40e0340203108100310385060600500c1000100941900704540703e41004174000c00340c00359076608114002501183c10720055190500804042c2e0010a0b513042040400d030921390140c200030411240c600305081c06981015240d81140d00c0404000300a0801140c020b1041c40d40040090980d80e901c078000c504140c010b00036005039200f6507201103840c0182c2c410a80e41d03480d15002a80e00c0b0301c0c03c0214921410700200207551003000c0c07110300510b44070a030b5241402e4401c99000700300420f4950181c14107559000e10f8010082030101e81c10b9001d41502c0010811007841070103018000c814507000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 208122275 1250 208121025 208121033
    0xd0203070302030d02070302120d200a020d03080f070c120c0303140f01081204030302100b0301020c011b11161412070f0509090d0f050903070504090804030c05030303070f0c 76
    0x6003000a50300039096410600c0c904070025102c1803130380000c0344a1290010340310300604000441410001c42511401c2c0707002079009511174100c0c0c00b000c000c0c2d500c0c419084404010b032a048002c2c03903450b110740c840d0001d070b0a007140c0051003180300512510402903840c0d408004902c1d4004c02c0071002140c4d0030b0055402700b441c01e04030058040c1c4d455043c0c10301c1c07055091100c00640c405480c2d0403030f0710600c1560a40446140c00001d5849035104c042c0c0142c2c80841c0c140c1c0c813408030b9030010b001e0030801800145040c0443c01143d00755080c5800c0c8070100074550050501880d08019040d9100d06440040c000c688100c01401c040b868160141c09070399444010700d60399a40f80d240032840c24403d20b6084400443d500c80e40030b2140e45450269034000c05086002c038662000c0050303400b40b940000e13269004a04199001100c5035004010f101d40d15203e00200040c00351100c0c0f241454070707406031607010307602c0c0e0644c00c4c0f483c0c800340a80e01c118020341c800c000f04803615600480f00419242180303010407041d981410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 208123525 1250 208122275 208122283
    0x218090c15070b1b1909050306090106170a02062205120703031e0206060f01090b04080c120a1515090509011b0807020d0804080c0a08070303060506090a050d0203 71
    0x1000e01d4200c00950154811801c00c00c0180c6120762042498048a51340c642041d003811001c012407441c2c40c003041c07100b298204000030307603030310064000e203408a44284d950000074030f8144141c07494a42d6940d1400d082c0141180010b9005138118142c0081041d019203902080c0b86110700c94040d400c0c40740c021050940ca500c502140802464001c04054a08241d900d01c107856080d03038403084003c141c1c004030640f001c1118820740c03404801c594000d0040d0742c0c2c6550611098008030f144850411000c2440898a171080c00090005045036000901d42e9407070740e00900c81c0c02c10071054540e100d1341c0405400000502d418458100304a956031022030b4450780b07804541c1034150903400200c3d1513802e0031b00b001071707a01055205071507504100e014002c0e07d5405403400d5600c44800e031001c1005803c00a8843e404a000b192202c1e0002d01c1029880d20f07010b007030740000303041c0650000121054440011151705050b818006d1034003820b022510705140c2222a4001345010041348151805030200003017240641d5030500c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 208124775 1250 208123525 208123543
    0xc061608031902040f090f05040803040308040f0506012d14060f0d1107020415060f140d060803032508040f02220f18050c010305060d12021513021809 66
    0x20b0b2080d52501c0e00d032500009004010f0155291191500009075120b01d100d001da41d0189400503155450358546840c21218a88010300c01d4030310984034650000002d100304030a5000340074151254580280e40e044045c141020000e60451541054070280a5001685003940d00c1d82021108980c1e100e1002004038014002c182400c0070451424140c64000341050004101091003140c00f045000c10b00c00c003055446640c1d0082d0340001e0103140b4818003480c0505609403004020f2400a42840b4030840e160b8165140b6410128503a000032040c0104004000400050300c12010031100c62900d04140c01809910700900203002c1032140aa00000d40d141c294195414802c0d03402142801c10640b942a40076194091490543c546444e16502128400c3d601c000511a4000058030401c0c0d6450011805010064412030707002e8038001c981d1000600c940720040d0314000315005041c1d110030101d0200915600200b00303c200d205804100c03401607071040782c0d0703024081110204458a031142605a8a020041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 208126025 1250 208124775 208124821
    0x6030121080a0810061b0b270f011b0804080706112701020c0a050904080c030a0e040b01090303051204140f0106080606060405011e020c1e030c06160803 67
    0x14507142c826840a02036200d400d0301c3c980c83c90380e241c1c0c0340d00c1114030481541114000c3c840e0580c0c0840000d0841da070030f079048071002180003141418803030030107900f481041c540300150b88046150314244a0a0052005031810640c01c8400c0f4500c41c0c60140c03244030700a1005007807010014681081010301e501000301d0110015030f9580300c2030000c008072481c3d442d80700312144007a80420706021540c4001442100340602501030902585008140191601c014000320703204042401809170b28030040014101d161071030380d01c2c0718005699406100854696082c01410401c7c01001440440e8000085400340286006003142c81d59442c1048000c4080d400c400c4081d900074582d144030349403015004181a1844101503c8040d103c0004000180c4110711449001c100303410a0041b140c10728202c1c0e034507401703600c0c010b440d821340d000360028844500402810705034040076060151181010011402d03801c9040d2a0f01c4c0c608880030f03000f0860601d02c408001d20044002000503d00300c040142e001404a0b0b07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 208127275 1250 208126025 208126027
    0x702041409010506090907230a0506030c03040303050c0406050708030601180f09140105030c011206031208041a0f061c020d05070321090501050a030b090f090c0f0603012108 76
    0x148010790281c8820f80d04140714450500102c1ca88480105000049071401041610b551081d00200192120b5125009a200d01c01c0c00e80000e0703a40310880154415800741410599074901442c01408544000d03095100180040c031050000c1c5801404507035090350000c141a8403946e901e001200c0d80c409150825046980d02c2c2070000d03144028101c60025a80c2144003880300050100450300c44030400d02c2101e0345036208290284041d400740043d4941a0344c40200070441503103d4640a582002ca0380e00b110005040c4402c1205214451101620554005020807114141642200219000548401d2041342010407079401000e008018609066014210030310b64591810036988032442d610043c1c512100c0214080182403107940800d0188034140c440001c400d0900c0c004540c1e580010748440c4c1850707030b00c1054415503a0340f00b10241c420134141085d82e090703280c041c1065081003001101c41c5d00503190079040c9429580e41c50700340c03810345802240022881040509000c60a0101c01c0068003840c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 208128525 1250 208127275 208127281
    0x2100818070306050603120702090106050325020616050310050603090a0b0c18010801030b01030807060f09150b060720010c120203070c05120a060f0b03032706030105030703060207020414 82
    0x115403c5544144001c03002e071f4885503984510325030070b132103120702c020745c842c11510040c020719002d00080c51b0040340550821900ca001032418035904050f90300c42c1409030b48900c04100c2c00708080207010800ba41c0902c0c2c483d0079030500001da41c0c0c0b444114000c0030f2145401000051018030200851000c433a0403840910302030410201e14846907000c0b6841d55220208a9560200d9502484125048940c8141000003da185445591b9170360410003088981701d031170341064060703801240201c10542d80604e0051019480ca1a0010100c07100c10003154041c20b0140114404100368256080711a202840080f24100602c0012110300b8030b8054001c08800c040c2020b80c00d450360010142280a10502903030020a07101c0301084002d185200030340d1080c1d48807a09100008500781c02038401996109404240740381a1000241140c000c036140c180c51080c464810380c803480c204840c1d402042c0080e10f03a50310f59414180400d440c0c00032400302600c0d0540004040c070071521198844400080100c11068281c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 208129775 1250 208128525 208128533
    0x14040917040b0d05010f0305060a0c030b12060f09010524030c0406062003040b07060b010c230606120a0f0c09091118060109091104050604150f020a021008180703 71
    0x50008003ca00d4014a07103000420b07101d500000f400300b60703500301c8028611655400c0600c0054040c008000302050b03180c4540448a449841410b80303a00994070181541e481d05603104014280d00605100311a0f0405003800b40391100880c000e0b016030100c510704083d40030610003182c90100c540b40500d400c2813400e800094480c0d441780f10586640c41d04c0d00e00c64540710319094910b581e4001e900402c1d02030f2030704004280009240b50320a500703002060502c525048510380312030701646101c203291080c002e82045c0034185c0e901d05020655001108441103014000c05030295035451440d402c00914070040d0341041301c04d0020f41d00e001c200074401008144540c1116240c4402d001e8902104140140c5a1000707601041c5c40103a00144903101c10394811121515098111025140549502000700c10801c0b0101d6192501c0c40200003801c886a003401e0320380b5002c5d0000381040c903140030a00840d00711a03051030060351414070306050b03d882481c011595441c0d0a02c100440f48030120018114441d0b404008104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 208131025 1250 208129775 208129777
    0x6030b01080309100504150809150108030309070909082a030a020a11010201021809060607050105040b090c011e12020c1c02100b060921030d0b0a09020414040917040b 73
    0xa03407416210031301c0100f03054500b40c40c6030042e030090700b03a14031000034800c210506c1008020742c0460300c04111200c5d03000395100c1280b040e900f0307080904507800000410032056030811462000708114801004608001e8a80620078081c02c807524101c005080f0000c100b0500360041003c0c44000790059a6940a4182010707540325240c41c821181601c90b0785601c2c41942c010700c00c1e103001522981400162034118010002c5c0010000e101c0c82d13003d142400200e01141c002d00c1298400d070f200398100401410036104480c40d1250200c0742c6410004607100412110320040d43d07001c05d101c2c0300c0c01c11000000d00800390102901031000c40040794880e10166800004202d40c180700070301d4854099641551246075076906850078680c4280e0421010040344401e400c011030f40c0b40300040180460010b084544907024255849501c82c0314031a51900324480c02c52030f0100481005190b013041c00c40c500780c90482c0d40b4085204100029115079511480b104c141b0144504440152001400c1c40d03a4558031040e1110309 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 208132275 1250 208131025 208131037
    0x131505030f0106050412030c05030c0d051206030606130e190f0b060102070803072904050303010e0604020a0c0219030213060e0c07080702060319060b090f0f010e100306030b010803 79
    0x18541c045400001c1480c080c03030894054426000e071201c20040641c5094800b0300a002c422113035444200280714a40009101101c0c12520303c0d5580d540d520101c1600400e240005007000d41329070042418084695603114581c00b2000c5010030101d8100c14641c402414000c00030342d292040b04144803120304004102113444441e40c420504c201254071f846004aa03126101d015501300341c1c0c41042154041105407903030248068483c014040c0410050102450f01d28068408035840d5001200500c0f4040c60130055980c4480d09580860502c0c4003518003d06400600d80040d004051910589042200070800b0102940c1c002d080c9005030100e40e20004000e143c2c034891540782c6542c80021890504242084a0310300b504032014500740309580d003c010060f40080c14001c0d000c11a01605444034005009250043c401d0f00b00e01c5032580e054600f8040d42007204240144110f64508510b00e03140e800c410007400c50982529616000076075500d00358000e001503040a050022000000030700600004003d1403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 208133525 1250 208132275 208132291
    0x10501230f0d0c08100303080621070609030b01150516080d090c05010207050604030203120f0c1209100513030308060f061204030215070813062301050f060c0c0613150503 75
    0x44c25a40c0e41c0b0354000b5a070010301000300080d1550780440c50924110011034840505a0205480000c500b00c01510702043d41c3d100c100400e580c040208284140d44d500540140324810388980341284030709008100707200300120794442c902140c8525051103030711301c2510300440c4622030030081a0030605040e0000e00b0b00d031240900500c140c240114450400d03606540480340e015005000c8400d0a50030701c003046d00300300b20003400c591046c01080f51072070080001350001f0019040e01030ba00d0150b03000784250021941c45807402d2003000c0000041c05030b80f01600404890b050b2034040b809072101d900007112011075035030301540440007213408403a016000c0e110a004078400d8080b20341c082c0004007440441c40c1c0407100000410b00c4040052056040801c00d02c08180c841c1c4000a0200044059112407422000c045000781c0d07008801481316040043d50b41c1010001111b1050411402092241d5920310813203406021f280040345004060b4001080c090180c45150010740c100c0c900e51030000e00d01d80045031241 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 208134775 1250 208133525 208133537
    0x105101209111003230711190b070801030203030a0f050405041401090c020d021b0a090606020303070f020705060d020d061208190305070e121c0504090e0303010501230f0d0c 76
    0x2020f882c000d03c194510003100501d071004e44100340000070f2640390001c00072024030424130b2017540e07004024003204050010804041000a080342020051134400900719410321003040c00600160390b0010545980700c20038642018400303c084411601070103141e00c02504a81021441609054503505090503294152410805201401c0b412a500c501c07212400c070158021581d00c14401c039209008681c241405000010310a556881e00310032118243d02090051b0404070034000e85541c0100c00000c4202c044c401480100e0805000030b8161140b00259200c13654000f804e8202e10340c20b0b81181d4007c1100c1c90340c0c03132840c003424100003c1c154007004401d030350030702d10300009030b50507000b0320a490140a0554924598615660610100b1010300000010758881c8411480322043c440e418684200315541c1d03029112071400e40c1d000182c4014540800346500709000600072030f64414180f0203000c60f048000000e030403222206541c0c62096000c08201c2400005c1c2d01d45000c2c0d11900715200c0c1c3d03841a5100c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 208136025 1250 208134775 208134799
    0x210020414012a0b0907050d290105090106110a0c033f0f210b0102070b03010305030d02161203050613050601022a04061217040608010510120911 64
    0x4190202c601040f0304030020703030404500d004560300802d100d600c00055011640c4003511030000542900b2448000c43e82a160550b0b00c0e000703441d402010b0341460302403c0c00140780c0d5042c08001000000140100e10801c440d440c0c600803501c01c02c00035102e0350b5030417910103900076803a802c1c1901c4c40d110143ca48111000d6800ca95410200005c441d42410000503400380051396040c0422242e009040400104000c400c0e94a8094484410020490801e8840000410030010342c000b82c10400035511444080740240010000b01e0804400c40703038640c00441006a0300c420354400d25440c84100c0701d014104040c1c0890581405416a02460085c0b00031500c42d0f055100100441c030980d9821141140180c200328094001d15a2002c8c0ca050210320391080301d1b440306004c102090444c1c3c015440a0701d550345030031050050210002c054909031115940a604d01800c10001414000741071007154007454165010109061003011101203110100005020551507810420301c070701400d1003220300c101001100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 208137275 1250 208136025 208136057
    0x4050606030d0c0602090a051801050f0f01020703060c02030f191b11010804020609030a21020c100509180a0f0c020d091e0f030f060b030607050712021002041401 71
    0x14a551a40b0036640b0103905480540c2e030302c0003a40041c06403d07000280c0319004a03050b0f071400500f81040103001d0511000e5071400c401c111400182040e490300032040b0420700b0101d40da01040300c90580303070050404580018402c0c4103c0c69803261100040400202242070307800031548440903407280f001961101c1301c14492200100243c00b2000c0024142100c0c030760000c0c225401440100d40c800e000a140303900300f41d02440802c1c10403e0403842101d011980c1d08034200d0070005c0d85035090108110b44001d0502d503c000c1c000c1000c052130118400c0c248580030a1084c280d5468a4800d800d20b0000102c20706c40b803d160050310080c200a070010303182c003820483c0903159540b0010704d0406048175656143c00c80ba240481100c00c1c1051001e8035400c0f1180c2100120700d402080b101c502c000d41c8580b5042d41c0070812400d141c0c00704c4230796a0075a84640c01a1003400f5286074070100340c3c0c50040e0844048036540e400380405a24000c0e241c4d21561445001040028214010201d60961640281c80d014500400074203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 208138525 1250 208137275 208137283
    0x501050c040617090106090c030204030506010e0108031b030d29010f02030a050c0106080a05030319150e060102010e070305030a0210150915030f08030a060501020318091317030405060603 82
    0x2034100002c0d82e650614150f501075601e4107400c00c03950000011119101e0200b4001c1c0e0701a00360f540c02003030300010104100001005410700600318002000d10650410101c1a01e030b00c1140c52070402142d0308044e220604005100310399150030469003c002d100141402038500d010f00d0036406011902601900c2c6565004603000f404030022039018500e49102c401040d1455000410100041d6680340310100703101804014a00c4840c0c010001181c80307151a02c41c0c035000b0300382c00158001181c1403200b061009281020404195400349001b08210740e43d0307800403401810312500081151192070000420b100e40400240340c2c500710b650036180c201242c0c0c69200e040d203010250520744c1c11141e03482003110f40c14079444102d4115040d5080d41200d41c0d41c1c1c480300400454294150341142e0700105100752117120b1701c24200200f900f80041c0d414070b0548104803500001e0400328034000e030b0103800001c04201112141c0fa500304d0b07000340700d0000e4a41c084100309142d002203404a41c1d52203050042812880d00103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 208139775 1250 208138525 208138529
    0x2040608010b030c04050903120c0d1b0f0302030406022101030b0c0c070b070303110406021014010302010c030c0c0f03031707110d0c1e05010209040b04051504020c120c0a0501050c04 80
    0x50020826a2162130034000241001050207055000c2070010b5461130741c07424061401480d45150913034948844099030001ca4aa00c00b424255404640d07890740140d801003000802c1e01030a0070016160b603600d0404101910038410032070103800300250809400c2102034040c5051340c4c0a40990802581c0d00c0c40c1ca030a013885500c8151203144c0c408041001f149101f000100541c0d032092501050b81e0000c00046041a002a080400541c00c540d2407004580000e10a002e000281e0a14403809545160006030032941c0d285000303010080d03c4801c00041c884d080203034000420340c102c3c0c81c1c0c8160769039040041c0910307078503203144c034881c840800801c0e2101d1084c840e04480555220150402100300e2405a4a1302290b200c1110040500c0040d212050841e03004601282d01078000980d80300700403020030089404900b0142c0c8150710b41030a101d02c0c0c00005468020001d010340780185e0703d5010034500b80c03404001d607007810349940002030310000c4054045003595400c0d10078402406a42c49040380c2c2500ca00482c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 208141025 1250 208139775 208139779
    0x30203070e0a2117070f1e080313030908070801021b03040f06120e011b08070207080304090c020a0204230108030306090c0307030e060403020f07050603010b0d051b030a060302040608010b 82
    0x7085035000f00071000200d001c0d841c07145404002803400d20f22040c015400c100c0303084d5040c401da0070100d8288440480d001c1d11242500f03022265100a580e43c0e501e60f40405017206462600c5040c0c2d52040502417651200540f0150741254621665550054040d60182c00c13140070780b07818042ca40111a40004c1a00e0941c3c04540c1003185645c2407a1080300c0058444d4481d607079054861070350442100081c40f83c0981c00b426600d03d034a54210307003040500360349000b5001d402150722a500c108062080070041da003d46917990b04c0407440055103101240b1300b00a100340650700528129a1005051200b0300205150000b4406e00066a0380c1e502e00548902040714402d40002c000b00006619209540c001d5501c91101c1c100010f030702003216042442c2181c1150102c004d6403280002c2c440c4060100407000c0105401c58400c0d1466043c20440d900901407012581c142ca80c4540c040741480d21403084118005106900e116200e02d0700e01040e9020f050580700907801a8a0014081059213060060140c14800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 208142275 1250 208141025 208141049
    0x1110d0e0c1509061201080714060903070312020a0b1008070e011a13120b09010f0b010905040c020c0316090c26090c040911030105010e0106080f190606030203070e0a 73
    0x140412880a520002140fa40904200000d031700300d410040d060f5020b800c080c401840103d060420508084c50b2044c0041e00c035002c01e010040c00b5950002d0030394140c9900c0031401d000c4480c440710980c070f45040400000c04840d03803a402c00161440c2c45a44a04448100c4111000b86135078507a003100c1407a00307000f20300c43c01d0a16500280c1811080c0000d18005102d000007124042c1d45481600803500c1c8500e04648444980081c407040301c1090040303107031110f5032031000c1101840d010006031405180d40310f214001d54580984c0c001481c002d11400ca02d81c00301900b030701d40590090400c1501d40145000b0710803d903203441071071002d592141d4034a000400400c000074a94020f0032220140d164001402c40c143d510071110780d00d03441c0c2ca42c1c4c041c21008500c10040c01051038103071030416080d41c00c140c008000c22104c480c0101b1841d83d0101c0b1188c0c001264421850032920f48540320b1950709131400030120014242100040c0c00d59050380254459400d9a64606c0307502e8040b010020040038910a041c43c90744 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 208143525 1250 208142275 208142299
    0x110a0b0a0917031201063f09140d0824060702120705060f0702040e0a110904050c060703170604061412010204050d0b0906070f200a0501110d0e0c 64
    0x101541c6222442c64124040f01d00340305520a43c55040c2d00260050000a8450700000c526140d18001c440f4032a0406c1545002074100a458900c01c2403c0c0020b041c9481d44400c103203800d00003000f44603800148840c007900c20441515001406a00003500d60b110241c0022024031030303400300d0740000865a140100018501030040c0c08210b01e00307441c0c1c100c1c0c4100380100c3d800003e15580f45801412040c95103140c40b919207007103004000032501e802d1440c86107500840300300c800107458400030007a80070741260407087c140c03614181a490407070105103454001000142032014103811020504a10f50310001c68036040c0d803074400b400141d6a080c0300b000040c0d000390300c2401e03081c80d10610f8812410b0980d0001401d05076100001040c4481140f800c0c1d0710080300e40706010324101c0a020301e1b60f1118450074041000b550b6840010088013102a11280304004100004500c100070b0111480c19034000c002480422180e00340e19000b584519003003000d2074a49080c00c0d00406012030541c1c07040e2001042e070b0112403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 208144775 1250 208143525 208143539
    0x21501030b06060c0f010c0909090203070e1e04050604060606020f2a04290102060403050910030207020907081006110304090e0708030f1201140319031b110a0b0a09 72
    0x40c090315883e4403002c2806410010941004107400e0004081c00105103020140c0010b0112001500b080e80f0f12424802e015000da01d00095080450301c1401000a071170341c030101e00c1c0310500d208c6001e1486400080d4184407d000b00090b042e80902c0c0592000c0181310b03960001030f41c1d225a00010b0040a0700444a44101c100c0440142c54021507072851025000042c040081c08841240b20000480300c1d1681803e0300554403c039240000c0d90013800207000d00d08007074038050034174001e010480340b0401081c095192003502c60740503503844070340c05085800141030140c0c01400f040812500641e440c001d1101c0080c1d8075110702004082580a070016600d0142851000b03000780c03d409181d114244035182d0300280082e410030040500d0b41540b07100a403140180741400036226010f9104440000c540301c3c000f04999008a0403080e9155250700890050b0500c1c80c003a52000c406060400642840750289000d011761150460707112102212a054102d445820701c07183c6001e01c2042400207071000c2c50902c480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 208146025 1250 208144775 208144793
    0xc03100f0806153f010c020a060c0e061e0d060b090420091306030c0308130f03021507021315030218040807030f02030d020f0c100603030807121107060c020d02150103 73
    0x3064000d80c4d403012480b000000f425039200810b6480140e0001c1044420310850341710b551602d4410389450b000800500d40001e1541c000e05a5910003610841d940c0792010300101c01b03d4280302c0c1004414865140c1d582e650701c500343c00564250b8002d9013000c1c4c80300090090a00d54008261034858100d0502e5029000e00c01c0f0000300d6052084810380c0ca034001b00200c0e48403a40840214400d0700c12569401522000085102c000e81c010176050703103008002c0c401a515040c0420040c548201d80da9100c5d40d403400014400440403611180351391512003400103803510740b010f08007940e0080c1c0d405018003840d5024562000c20454020300401824012140020310855038001d0b1004c0a20480c2c4c104a002d541300c0c01240d000803d001181c05000803900300102c1d05007d204a089150340b07041005519580f4085d00140008041c0000c020079034800f0303628064660300440102c030724041c00c0d6807242c09603d07000004140305000c1e1000b62080c0700e40c00d5810f510001340702800f4169031940d40d4107039103995200400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 208147275 1250 208146025 208146109
    0xd080f07110a140a03020d08010506031305011d0c0a1d010302060901170c0d0b01020a0f030806041e060e24010309020d08210603150c03100f080615 65
    0x1260141900d510041040030f924061030103030700000342c912034920b031401902e0010b4050311b0901b804003040040002f0740ea80000d0307a500202d0024026030840180c80c01070300504100c004000b0842e403100644041c0100043c58245401003034507529040c42e02c80813418050203220203c4442d02090308014030040c20a0000381c9940304041c14030410a010040c0590310658088902c4102c4400104000f24a015030340241c420b044400e0005e0283c210590700e588550481d03529014041c0520f00d800704183c2d0701c03035510100000c00506550345146419841c550013811041c0304042418404101003003900007151840425850302111590460500c40c3c010360180604000680e4050400d9659901040d0f094001300303541c8501c501880e00c000085050b024034100301400c20342c081e0344003281104000b14a0400b041e0800d40d0311606640b0f0360340781203050060032480e0700400060f00000100203152500040d03550b0141882c4500400c10101c0002403251050308a02c0010721100741106a9207a0142d007900d982d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 208148525 1250 208147275 208147307
    0xb0301170f03180a060309150903091809060605030c01090e070203040902190206070e01020318060702060c031c0207030906030c03090501020307020a0b06030604050d080a09050607080103050d080f07 87
    0x100c0002048469815a048800c003a48100324801841403c0c1c90591007140107045c4504081200701002d0b110303105040102c201888400c0e680700ca0402c2813500511100c1c3c01815205070307413114900007100d0788000d81101613040300c095040c4507000c81c55250205555600c070806942d00c1400701e2401032980d015900c09000602076000801022a10b00b885000400d4003550441c8000044070603010000e1170400700600349000c0120204a1925580c0d000c4201c0f04854414004410066001c2e00001c0340d0b0320503400001e6200000140c624000040400580040341c80e0740180f0342040814045a01030340301d10b002c0100082c4100400f440804c0c0a94000c103050089454005462100369480900320303071040e04e40402503030011800108001004030384c5075010000b030740034060b00e00300740d80c4103541c49000246990a00c0003e4002401c012055440007501c3c503041000c480040c00c1082015280f81001e010030340e00f40c000c0302090800c0c1801a40101d0103840141c4c001040d82e076801e90112074000e04201c10300703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 208149775 1250 208148525 208148533
    0xc120612020d03180605040602060a0c0806150c33010e0123041505040b010507080d0507120204060806010908150129040305012703090e06040b0306040b07090f0b030117 74
    0x101131240300503400340c0908555122560340700d06001c806482c09600501c0d002d20b01e400c1450545d455a4480d2140da00b01005a4076141e60b0300c100034103400140182980d0203800e100300860b401800700b80320308028400565421000c64101c0002e03211201131800d000f803c040c0c8034544010407400d81d0b501e0500c60000d01c40180e1a0444044c0d0340018259910480c00b01049051b1401c1849949458418502d80000908000b441d00303400c0d569440050003454071440c681130380d0b10001940301d40500f15050103081000011945d0f1340c2c075000003610740d502c01d407040d03800242402e2011a0441c1c00213a001c5844d518841a254542e1901c1d0410640000c2e030f070a03070340106240c0411301800c1581100540003a52103980081030750b040120104285603da49200d80c510104554007001194208107054280c901c03806ea50b03582d0f40d81c2c10300840d018103000d54409405d44110010001402a0581182d01501050307a40c004441c1e51200c2911081e005401048085c250030030040020314034642d600703c0c5c2c1640940540e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 208151025 1250 208149775 208149797
    0xf020616030b130c02010b060c190309030803040609050105010905072c0d03030b090702121c090807031d12250803190906050a080f0a1b030c120612020d03 68
    0x1c96080e07070720a05840005031311403045107026602809500302d0307248150b5030b40303052607000d404047d55003207400082a1000d0480c030700c0710305251040e80d0f800d0145800c00700c4c03e80c2d2400c05180603c020b012444041e99039519050021a1090303072030040c81c1c0100155690740b01c5c00c4e940035950104042980290004458400c03d500c41d4540324181c0c0e13503240502a442c000381c1a000300d020b1001c6d030b80004203507034110740001c1080500d800e00303101502c02c16203003240250301785001003c0b043c0c002d000d0f050f005480300300082080010180c0c40404003482c1b0807400c4e07940c07011115010501000040f04502c901d0607421040c03d40c2c01b4840c070200007102c064031f24040720641c1641c9130045c40c116880f034007181810400c1c1907240034035075070003d17440001001c443c80d11038030b080c0003004000c1070110f01405d070501d40303800240898090310594002d00c03451095000081090500f000015005213500290980440c010218a040484c4607115490844240405000c0800019804c101002d002440c00310140003880b010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 208152275 1250 208151025 208151029
    0x1204171c0e13140a020903060c0a050a180b18011808100216020a060306030c0f08060601120905010515040b030102040e07030c18030c050108010806090703080c03070b0a050a0b010f020616030b 84
    0x102600444c0002001a6510b038000b0a041c00c14000410000c0c60b0502080b00d00f0f0031950020864519000f249841d418103481088004e1510019610140b8211004140c0300101100086450103003102601e90300c3c45e0780ba11148081d502251803203958040d0300101d400c4441122541c0051442c01aa040c104d41d112925a0000d4001032a41d0480380c0000c0e5900d00600400c60118031410140030840c512041e045d140182c00399480c0d0000f04032604016065003000305502c0e441c1c00202e10650300c00c000f400a45803510100301c6400030031903650b01c564100110380d95281810710849007034035035404141c0031f00c6e650302038240e000d0200640d0503410400300329440b00000764001c20820266104042a080040c6001d00044c00010182c1001c0c403e0742000301880620100041c0c10012a40e02c01c82441c1c482050b103902c241103026825000c2d211240c100f0412040c074a165014903c90458a2400c110072071002c1c0044030544c004012002c00350740200b001c1006100da440141c1140005c40c0740c003107901415840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 208153525 1250 208152275 208152311
    0x9071206080606042a0c020f04230115080a050c07050f01020705060a02042306040b04060504030c0602010b010c0b060616060920010c020603091204171c0e13 69
    0x20000d091500000b051014501d880d01450005116001c0780d0760403450305009800184885e2000d08040c003451a980000310748400450074071060300240108581c401195000c000c900c01803005495491300c000001c5059038441d202e40c603225683d942c400d0501e903182d4210070020a0b020709424290502848000d002420030000e42d4444c80c0c810f000940c49070070f00e1421616020001d80410704403401032109020302000540001840b180c00da11030403d0035028804203080e031007943c0094510210029000c00c17040e40080092044921402a001d9001d40c0c81400300d08803980251401d00050b25440c01d44003007284440410b800c400024440b51501c02206050300d0b0700354801004507a50743c4c03140b0000c0144142c0d032400780951000c01800d44000d205501c0000c201e24580744000384582c07004400b050031001c0404c000c40c030600c54500002c3d583c5440f521604451060008100903d11850030704451101d80c0001541a40484d620743c2441c10131309000704004090950314804029540f1020f041000c00304203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 208154775 1250 208153525 208153529
    0x6130618030c17010c09140913120e210d050d0b03010203010f171516050c1501152c0301090203010f240b0901030b01021c09090c020c01020c09071206 66
    0x7000320b643c019100c5803041d007941d000c500154280076020f902000302c511814400d0044400894004c0b015540d010140c05c4003018140d00500122206d0440580702508403102c0702c002d16044507000000440c0404c0c0d10311640110858075021740003e00c11400f444c0c01503001d4141c22400400100e6840d8408021900b26042684041a01603070321404001100c0c1035081014428480006480c011007004880000c13401c014220191091b100ca0540741c60601c03603400d5a400c80d4040060310303507007440002c00001250007070065001c0c0c0942c009110701001e004407551001c0001d201e03680c28403450030304624a158031201c10b8640d055500e5600081c0185d40a00c42c0c0500e82e21002c500040c0b041c54071504000c8046a004131024007000751100344003211000003504e04406017460042003070040c400c0100c1c1040d07808140520710400300844152503035040040300096a0002c40100070b00298030b031080340c3c3c03110030400c101d0150f00010310340700d07050400c1440103612070b5280c1441809030201c3c2c407259084649035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 208156025 1250 208154775 208154789
    0x408010e03031b0a0212030c070203030f09120a0309050f0409051516030209030c131b0203030405150411010309030207081204050f030c090a0e0703020d0b07080606130618030c 77
    0x1040001d107184007403008010f42035080365007030a4645802940e01e10441c00003a014250110004449809150071500d8640d4090181c940b20001c0c0114465039404c0446840d11038940e0111600240d4400141d031034032150075555005116103040203000403603107001d07021900300380c9480031030020890400079a480070b2034603503e886e070900d0102600020b00034000c9149040500412101e1519034000a000e0035250041f10071804400c2100714003001049030340c0360710404141c00320001c140c2c81c2d00400514401c13802001170395211802640107520400d005c4400425522200c0d0741c2c00e0301544a030f03004c040710b0381c400e004503440703e85c540082901d00550019041c4842000250900c414204002e590310b07142c0c4250028104c4054840002c1d052480c02007900708c201d030361800705840c600001c000506c01160003508a682080080c2441003040c44d007160602c0102e40c605000c1546403c003442202c407000b103151440a105420810304803010803020394046803841c1c2050300070000c0b40580d043c00008240c9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 208157275 1250 208156025 208156027
    0x408090a1401171006030e0312040f0c0b0906030112020307080106120c0b03070503010308070f020405070c0506090601050325050a08060405100c090e0c0d05090102090a091b0809030408010e03 84
    0x30300c41c0010b00354862441c495000c61090070501c4034003a814007441c0c05482c0c0c3c80c100070030b603006c0d0301c14890300e10b005080807100d1101d42d1794103201c14015400b4036515075074020580101100d85840e1040001c2c0f2800840d1500024108010025a460382020000e80c80c40103040c5c0300000c0e961110306085d1101da800c40504900500600300400c00b50102020092040c80301d51400d5150030a40039100340014840900284d0000403060200400312000c030100c25801041084641046000284000d441c28030854162140201080c2441400902c2d035040711001401041108001d540301036880b0403c40044078010400c80011030195204c5585c0c1300a800c2c020018000383c9400e041a514000c0940d9210410600d81414000c4569010300c05200380c4030110000201c1d6102e0054040062042c0440082d03030724a445c0a00c010468190020b2080704000c864040f00301c0c2d21010b00000300c0e40e131007070100d400c94035496034192558002c020450740018080c098a041c1a40c5903905801d44241803240340403600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 208158525 1250 208157275 208157309
    0x203060f0a260c10050c07030b0108010f06081506040e0307060e0c0a0e0f0106050319020703171b072306091c05070812060a0b070b0a050127050408090a 67
    0x5585080b10080303101660082641c0944540443c0303003041030b44072103410050300169001140800300190b070000c641c08201c0b010746696070007086000740101c441200580303040c00000240794400040c40303403e02c8800002140340e9110035040100030302540300000c401e40414004003011a040c1d01c01c140310110b826024001140c210340c1004240407641c0c0254000081c0348041c0000062807100883c19595207040c007581c2d903142c0c08403a2811941c0d0f200425202400042c1070420164068903400000c0203e01000b110760302d1360100e40c80b00d040701b20050824440240305440129a0992401101c03003d001030540c41c4205000b005401c03d801240c286800382c1c03003c0040c50360740d28584110304e000c084510f0204d0500382c0554825066200f150f58004040c0500404a441a82c4605010740140392140d620b82e030301d05052500c1d9800182c00c88040c0a100c0c030300f1000061284042c034800701001c0107a03d16009034040140820000c00780034006a803620310602015040d501c48800780400750020110b402500b003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 208159775 1250 208158525 208158569
    0x6120f0f0109020f0909330705091302040b0a03150e010314210a0804030201060506040936080d02040b0f03090c150306010c1401020a0503060310090203100203060f0a 73
    0x410b01501080c010815101007203200359010910803078109000c0b80b45400c0640501e000e1102d0b0042d9040e101c1f071260402e090010f03050b0014018205c010064036005000e00411001c503041f809580300c1c10f4900141040403402580c800e031f0009001d40c41f441c020001031511040444503c0009030400c4a00a0380c0e610b210314001d41c100400c000040c41040b150a0100c0c0780b0702250028020b4004003020300034013401040405000790482005008050043e0b03444540d600d00c828081c0806010260710401c483d54000491100d407020404e02c40310414540c440d003005680c41f01e2990b07000b00000582242d0a1001041c4d8404041c010084400701003445034907401c1454150b400c20403074481c0c8034032075270031191503489585594060301c0e84480e003400c0040c4010760314242081c2100030107104030001d510000c0d07092030040d0000051030190205504841c620555244208200c545920700a94184e200f400720342200d031035540040d50b00a1000c0c0100740100c0c0c0000118149030025044109c941c0b038240b266000349 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 208161025 1250 208159775 208159789
    0x6010b0913020403030f052508031518060d03050c01050406021b0114041209091e060501020a1a060a170604021302041809060209091608010504090b06120f0f010902 72
    0xc21010300843c0f5061455401806c40748540c4001c10a010001c100049010102c0a00d401c0743d19003001800222840751504a200d42e06c1103460043d0348100c031802c0c26450030b00c05200790044c03031100101c2c001a1603050405c8035640a100f0100c04002040010300203221007801854004c520440016803074040121400c030020a01811009150b0314085510009802c801c0d016908581c20010584440b0075180b801c8825030f615811108641d804c11400c01c010484103986c2c03550031514480c04201c01501d5100480c4c8684030310304040c00c40010f0f41c101210845112482c1d64015034002c14a4a00780d586591490102c07801c019003400a820500c104004d5003812a840c548096903007000314580360410301881002010105d40e1550990b07510400c60420000380e040351703c0c0610081c036800043c9040b0354249185030070740c0e04250000341c0707404c000070320740c00d00d0300500000c0c80d40b20310302c3c01c1e4503507500c422300c059002502000f0b1114410040c6500803028140035002e5001409400490b020f4400d005000711 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 208162275 1250 208161025 208161049
    0x12030f03111204060f0609061e060806060307030b010e1804050d03050705120c04030b090f010c020606090f09070302060f040905061906051b030d050618040209180f06010b09 76
    0x1d00e050800c0800b406840800306550701541c0104005800001c0c1c00b0300c04001c0c010754000304000c07403030014003040c02100c3d08034000002c205880b2034014141c4506085030b05480a0303603290b030000014004215050f020380c010b1045500180b51110442280b1000a01c2141628907141c44900c22034050100b480390600942401041ca400e00307002c1420521002012840344029101c7e0f44d074842c10103c2c080340440000c48000395001030b42d11684bc1094901c044e20740c40d8200701c1e82ca80d9880e1601b080400350010501c0c5210b05001003130804140d440c46540041c0300303801880b4000314090050003200590740e07480608400c5041ea003015032110305101c00c1c00200c5001070150b6228489180300802e4800c002c100c5002a5900e520703100e0344403510303543c10503001d440e0172080c164240000b08010780303205640d90204e80720305c20490300f40c1008004565890020030050b640690001444800114104108140a4031209142d011148190031040e83c460400400381c01444201400152100881c50401ca488013 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 208163525 1250 208162275 208162301
    0xb0612120a2307061b0305040218070e040c0207140108010503060a0e03040b0703020606011b1a06011704060912020f1f0b0409050c0114040302011205040c12030f03 72
    0x103180058140a01501440348088200409144044282a0040c1d001c004064481c140141c0301c140e1403503d24003401007a03091744001c6182c843c00360452031107801218008c64020f04000c05000d041c4004000c00d820051850040c01407030404000d02c1c2d1918801e41d507040c038682d03002e02501818450180c0d03070100c152044d00d04200102c001840903550101d0901d8004900000000d45072080890b10780c01d6005580c010100101c01003401e009042c1c01246640c440c0d54240d88400c02444190350080c0d8904034060098120b5005910200d001c603400150240c0103c0141031006800c7c40003500f1543c1e6500c06c840854404d034846050100700554581d80e2020b41c10706002514140e481c2c200b50550300d01a048500200e84004000000c00740d07980d501180c103d83c00a481401079440b582010340d030302d6459100b12400941c00c510b01c3c0e4000000300003034500b41ea034141d4428aa1681d160001005014041d0040c2c90355004e00100043c8145c2d00c0300c810440d1031198803480009505a40050100c61304c0003c0d00c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 208164775 1250 208163525 208163533
    0xb090d030902130b120a0c030303140112060c02010b130207060e0307052107120203030708010b0915091306030302070e0618070c05160801020403020f1017220b0612 72
    0x700041c2d86503040e80e03060300d21540300042c1540080340040c0c05c909071840d02d40c2150050002d00c10510958401e03500550f802030b28203008050704061241e00d05002407041821071082c0402041c0003c13225040b041012a003440040f8004014500042c80d10007000c640da4801540000c0309004c00a035030207126411101d00c0082e506040042d215a915805503010804c0c144807104d204584512100d0f064451a540268800a242030114006596540142c0340c09000c20301c52000000e9481c2c030702041340c0c8142c0000c0c280c51802c60003840c441075282c01c0341d900240d01009820501002c030703120b032042100a40c0030794018804545032200c0c8250000307014003d94003c40720000007210108205080a07040010b910300081c6842c02d07424194100302c120190b02601081d10355000444507815006030040e24000caa41c1e404240d02503007000a0f40150303040d0180880d120505450080101c0048246e2007100c1c840c0348040685904151622a130401404451411120090182c0380c1000c0e6107000301542400010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 208166025 1250 208164775 208164791
    0xc12050c0301050919090b0108060612030a1101060911130b030103050616020c120601060212040f14060f0d050103030809010b090109021305120307050f07060503070e040e03070b090d03 81
    0x44900c038401401068001d00b000c40103c1c101400d04545148458602d40080080800c0d5241c1503810550a218a911070710412020030f80a103842c4031040a440e060f07c00451a2982d00081a00c10340e10349003844000e07540e0b03854001030310801800350500e01201c61000a5481406e0102c12420031421b070803100faa11018801400003e000181c81d03600b1859107030300701c1c0d41c4c400c00340030407440c150b8074222309030b003000c50559101c0c51901c0006600d03041c2c2b00c1030380a03141710940e10055802e1b1401b0301d120f03440c1c00c50700c0030a0030010002550b00d64161100080e083d1854403069519068a951080c1c440c0701a60b5a20300040040c190310070307103107030f00800010024001211600c00240e03c10f541800703580912076000030500300d11011009400010034016062600e51415260555180d8020f0001070b604c2e406000d04841c000a8041404c0041d1581c0345c83d10b42c195123a1503c00c4401800310401c09130044c1e52041e8000a80f403041001e4030415200c1c9900030b000d13103024001c1e1400c2c0b034160410b2005143c10000d00b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 208167275 1250 208166025 208166041
    0x90c090305070902090411130e0106110c04050c0f031509010518061315120b0c070302250f091d0c030a030c050703020a060f02010501151704031709010c1205 69
    0x2002c011503411400c00f5890b019a00c0018004110089100700041e00c00500103d516203080702d61411036400e000ca1810a03a030365003040d9002c9441c0c0d0100138281c0c0140074024510b01e41740d448550410f8103c0c01641c20640c41d148420300c01c1c0c0c0b06031072000f480d140b0743c2c4560361145001a181c902420058803148803045d800c0003d040c41c44006884244140600d81708418105802e0b40034032016100907035141600b40c2d8450742840003140c00172040c0c1da6075584200041c030075515030080303500d0700d5410b81c000e0000c464a01c00c111b14440909209140e1915030030030004609a000c0d030020301070018607000290402a02d421880b45952001c003958080d000507180e40810780c0c0110b10544043c0d0542072000603c612880c040742441d00940000798843c1d0725aa0200b101507101002240d1a402a00204003903601d840001d400c964203100c030398001406a4820b001e15840d16a8001e8005100b42060104002111080a0740d55412a180d0700169501c0d845c0341c100e030381e112032241c04c0072003417180800407401c07c816 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 208168525 1250 208167275 208167283
    0x6161403040f0b03090109080d140a2a0509030604061b1e0c1b0902031e1009090609050a0503220f0515130902030a05090f0a020405090703020901030804090c090305 72
    0x103c0c3d8010b50300c012001070030300c0030290486200503138041a03c5648a444c0000c100082031980c40c80c3c514a00c0700000908818828840c1d02ea2124824201046c0795604162004581d1000c13100314040203000c0c040c0700401c0c1c030200145170281d84203d0010520a09d6650585140d010a00f07240b000c0201d80b0f07480301000007120a40900e84180b0349444000000ca60401c0c1c0321011504554180c80c6280600000b41f511841d40518042c84000e41c00601d1902c5990311a48104429100e02003c98003210702084030300b01359441404160301c5000045100303284da441e030030304008000c00151443e40001601030300000d0400c80d95000c25404000c140c041ba41440070700094540c860280d140211155140d001208003100251200c800c0905002805035844200c0c102c080d4005a40c003901c29130410b804544038020101d0b8020b0744500d048002d005104d49a0204005080c000d802000b09014111002c00580c54907084503010310f0080440355031303c5283c4100401211600d001940130080c0ba90418400102c01003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 208169775 1250 208168525 208168529
    0x5060f0a03060c0c08040806090f07081504030e1008010501020f012009063709050d110a2c010e040b011203021e0a030f0e060403060504060b06161403040f 68
    0x5000101480c040f503094800040c8450054041d16003c100054103520014a09210380420b1081d60348261415418507034500f22406504c4054206840030345c2c65009804049034414001e20b0407800c50810703d404038040c0d0030300c82d030078000040d40b02c001441a035030104500552240e140008001c1040410492622108140ba400c1882c2c000001d00e400e180c1d581d00169042481400600c0c1c030030b003a020161002c40342010068050041078156a061094081c55130301c0c00b11032002e03000c10b0418040da034441c02009400f10105521200440f00402caa04080071007191240c120f50b485c0088000c00c244140d00818140c1c007144c40c40c00c9039020130000440c40250301e8111501d07010a044220341c1440d0aa0601400303020203404202c005828400484d00001c4000b01c083c043d0326040c032041c002c0403040381da084c03040d00701c00e41020007000208005030f203540c00359a0050048000003415011880020526400303000401b0000070071060000a1141800b030315020090f4490085103003524015031502200424 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 208171025 1250 208169775 208169783
    0x8011208090310060f08060901020711190b0301060914060c0c0909010e010c080f100e01051201060b0a05040f120b07051605300309070e040f0609110405060f0a03 71
    0x10034442982c0e01d08001c1d10b038000d200c002c2e05002c225142c10178144500020302c201042c91080300e0105030403038018402c807210b01c0d400102c0d480369000500706002e01112800c000d0354402140e1080024848020000386003c0d103c80c0c1d407680085880c0408800030b080c9401079891180000b00f0001c0c13640100010302d11064401942c07480381540d1801d072034078010f1440c00c003642110350916002c0640c6981c000300c1c451246280c160706482c651106420245842c456000383d031070022103107005011901e07012080142c19981100086403041c0c41d03c0c10001190840c000041c0450310208092052411002c1090090043e0010303207001d605054480100e82c1c50301070802c0e0140318001802c20b003414140c02d601618503800004503002911109032509905003280b00d140e003081940380362620f080c80440c0c100c03802103030008000c021309130600b41c04205071240034004a94403802003e400000032003030b01410080c00c0c022803084074000c98113014401a120028580c03845250f09242040c0756a48441c2444280c07a00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 208172275 1250 208171025 208171027
    0x50406140d08071203020d0f020a0f0e03070305030c1e060705030c031305011e0e010c022a10020d0f0c020d0f030219080904110415140d0c020307020901050108011208 73
    0x4904001c010b91003808006081498815007910409400d07030000e0108040d9598108155683c4000d400203d01940011800244a4890b0812940d02c01c0e299120380300740c02000c0d110000d81d0b80c1e07590b07895540040084002d54000860021007600d81c1c141407040e090150010740200d1408013802000340c80003c01c429800314010000c00d400c41e600600c000030650740b103802040703150745800900a0300d81d84d1106042c000380c102111030141d000180034012022380c0c280c00626080d180c0328091407040c20090701300d1505001d200b540c1190755842c101c0a600400c4640c02402c0102c583c03813401427200c3c4201038600b00b80600c2d54030b214010727120141e2030b048840c0c20118600fa002c0381c904d822418106400c210010101c01d02d0b20071030510015500400184004503410401c0c01c0946d4024000e50182e0720070318041404d82401040c11600543d001d080e0640c82e1403c0f90b1402d03511620003011500030513801320050380003180440450805000c0240074100c2420103000b1507140020f0305600447c10800140a440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 208173525 1250 208172275 208172299
    0x8040b0a090f0306020909160c1502090312041a090114180402040b13090903050306010c05010e1009060b0102010e0d1d06030c0309060a0c080a0b01050702041103010f05040614 77
    0x201c00c49070403026041200e000034015690f4140302c0f01a40040d0b25191050741000e001c00e041082c1288681644101911003050510441d15862450f80500d01c080440039000c110304500d40d0741c207001c0f04500c0700d018100a600c45042111661030128218107080108070100280019071303805c0444ca040260344207803c01e698110502300500030980c180c002940080c00030a02045e0b50300c10707a010301001c02c1c4880354246060b039101c1d0140240e401c0b414010b0301003482000070403140c1d40b00303031009031a00340120004030381c05101902c0700c1d1a21034000841419247d4407100c0d4030800480b400341450b502d4003480280700d440140c0e103105440c3d80341c0440c4003040c07142403030300d4507440100c030100400341c501d0040c2240c0c1c5924000213030903116070048403415001d0190744001a442d24240c440c1c2070b0211240d0380d40c00119a0b410442000401c81d1040582c10310006210320300040e555402901141c071140c1c48840e80b254940f80001c1104030151700600c0c411801c000c010710281341c02c841c402454042c2107410044400d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 208174775 1250 208173525 208173527
    0x301030f02060c0a1505220f1e0b0f070e040e060c1305150403030306210204020a170a060501090512060a05070309050a03091d0118050a0e030a020717030708040b0a 72
    0x4080b103801000d19560000a4540c80420781c0040d07c01d01d40c0d0592100e40700c0702c61104950a250405c00107140b0b0f07066015080201d606200b0000040060042240c003401803034032410060b0381c1c100c2d0b52200382c03031100e01049410340e440802d40c014020191004d0200d0350b1484400c03600d80500034421070840001213903801c0c260545040300c4006113000f0301000c0b1400381490244185500502040d404281402d000003174225480389000010f2001001c402c01c060000da08100183d44410311910811205800b0301610050100e08036004d1f12150720300040181c5800c002400348047e40c0d10086c420b50703c0e02d040980805020400d01c1c2d00c613412280010f0a6a40c0d60000c1e0003e008441020380fa81c1300b032038003540402d60403080704c10076505041074020707100c0c0543c0c0310102245024020306450f02d88100c10203001281c0e541140d5000f04190170701203152000444014a0360b0004000707000168131031401000001c000d220a2141403901c00007071460002c20303454081081c40f50307104c0e603041130000149102d801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 208176025 1250 208174775 208174783
    0x1080405030d1103060306070908070303142505011515110f0d081015091503060b130302040b09040f02010c03020705060307030501050f010c020f061e0408010618020301030f02060c 79
    0x30302c405800c12243e4404195035185030011540c69000f4414000800d42c0b19005401400456401c0d20003402c071103045a40440302d100c40c15405440482c0301340314940c20500e410300d0300010340741c028005124020081c03e0940c2916241851001c2d1401092418480c1310201c07a00c0c041e500e80756007802d40c1903075107201a0524040c68099024a03074042c07042d03c418500e0b400001a401031084200721b020082d01c0715000e140d4603040347c1a1074041560480d0802c52400808502902d520302d5003070006840c0c1d03442d01d003081d190b0300c1101c01d800140c14050043c4110301d0030707114115400f00296260304145ca02a035905000d200246400790500c1400f8804a007054405c00c0410702500d400b503e0035840b81003414010b009404d0038040d10b0300c50000711400700042d51082c006d03080341c2a0020614101040c11409112070b6901c07210006001c000701c40b20300110540b0100047c0018460b12000140b4246841500355910344027404400d0203134010401040451003098181200c04d80444813180c1c0da0485100c0c840c50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 208177275 1250 208176025 208176037
    0x1120203030f0f0306100305060307060f111b041a060702061b03070c140d0302070603020f0405030312010504150b0319020705010e0604110402070309090c17130314180108040503 78
    0x28042c00010080ea0028285020350700030344050b140a124650100750560540d03004503021501a40580c100f0044240310b0281030707004e00c0082c1402c08182c400c0300b980b5130030825a80c0300640508507012800b11241418460010f40900e00303646280301521200015a05100d5800b01908c125004109840127100c001e91203c070003034105080741e946440314541440b00050701c0c418000c10491045810159007040e06040c904103605a000d840d11a040c920281d00170341000340c00f420300c0d8005102c040fa858800300300410194001c0b212031591589441708020030f07102041000200804940c0040203d64504d1090342c2c0c00c0340c05010443c1200e4401048407000740900c7e000035240b982804041803000002080c400d004074024400144000b031220700340026031088400c010001440c510080148280302d60108041401c01d28050310705044408080d03880c010140c900e0044004110b103204105500182501d2180c50300d003034400d0401c0711020b07038451204142c250445c18040800d00080801c8070134030844071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 208178525 1250 208177275 208177297
    0xf0d14271e010e06240a051309030219060203090601050307060207090513060f02030601021b1309110603160801050d0b01030318030818120105010f170f07090f230112020303 76
    0x1d0a85000501c98680d10000c10408170002035800e1903611034103210191500351007000d81204114021480d49000400d1020f509504500a00a00303c208540709510400c055001c1c0c400507840e03007000c0c204681400c0b01a0b100b54840e9004850802271f103a000706410003140c050100024066560b45c40d003030700c08920014001c201928040e84140c2c601c10f29405503000f2842a8220303030145005004a076281c000c01c1c902d032030303021015450711203444038107401800000d80300d0340e10704401e580c904004c500b05030001d03604080001180c000303178030156a20461140c01482c080b50380d1800802e46440e144011003042c007020301040500821002107420f091300c12402180e20440c1b1642d01d45100c60318880700781d43c541000d4864040700c426692020814007402c0d050b940c0c007000c4c17440d4940c54008040356600b04c180c000f01003400307241c240d101074250a024101c01849050030205a101c2c0b003402c0707031044500400400b00c5039002507001c40d100c0c015181c002030548a55860108104685000207499070244102042d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 208179775 1250 208178525 208178533
    0xc0102090301050c040611010908041406070206030f040209100e01030303050a150602010209040c0801050303030703020c0f03033103120506060906040b0901030506030604080703050f0d14271e010e 86
    0x1000955203c4000d00440e1b40c0d41d540c003141c1c0000f245001e420f95180361000381001a06000600c510304240c0c0308625400401403500b450003000354003040e415002201d035808200c6c0a80104802c1d420505642e030703446880d0b92141441c0078140b0043c45000d1006000c01f504050303544000480460070b40c0e000481c281070140c6006551a5590703c0207020398480d4114500a5040c2451a04211f0107012814181e840c0107000d5811039a50500c00c90003500554170348100c52040d48004007001c001440154002c03013525683c40721361541d01140300c1030040e40301c910508245140300c044000c2584540701c8607840e0a4404040340e60380301e000020745039025044401da4051b6001138000350454544009081e070711002c1c0c174240510743d01c84003015121541101c01a0040c01c0800200002910901c01000d40c075120f41061414580307101c04013030450308015551802d844a0109101e80c01402c40454140c51071000741c4003040d00410110b940d12070601460380c3c91140e1a4148600c071440080d040301030b00843c2c00c8216 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 208181025 1250 208179775 208179781
    0xf0e1501020d0c20091003151a0d06020f07060209030111270a0807080f010507030b03030d02030606070807060203070e1905011808010c08180307020d0809041e090c0806060f060c010209030105 84
    0xd40200007521003150102004c0407501607610103402744810a0001026054200389400c0a100c5010400718081b40c1c813540c2003100a0440c1d58200143c8410782c0918401611550980c0038542140c00340851101c4540c41440720703e0380c20540030841152040c41082e86454400703003c01041d01c1c848030342c003c00800d001c1e549000c101c80c030001503401800d03120b89000b8000c681302c0603401d4085442000225806802c100000c8042400c40d800860f04000050201803604000391143c503031941000c40200c844540000501144560040504c514442d048400801d0740f001e064020b610080c040c4038440c1400110082e1252964004c4900c00081c0600030090190181504000b81000000c49411103140c00a0101c1c61881c00001b0542c2c00b180e9018100d81c00740955a01d4105051300006191580582c171580023070440c0e5190515098091074140300441c250149280c050494032103a0001c5005074002c00130050030380d4800701c01541070300099074031f20790f03404100458501a00c03a6408107600342d800c040c14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 208182275 1250 208181025 208181041
    0x121e0c050c09010609030b0705070614041a010b032202030f011e06030308010e09030705010c0e010e09090709021323041a0108010302120102040f0e1501020d0c2009 72
    0x14680040e10400c151040c9982401c1003001e51502030050000061071002d040c400243c000d440c481d00100c05081690400790f60390f8805054a001ca01401084807440081c00204071ba9558040442014085815115030600401c001140001000c01460200c070501401c1c100d403001a030030f14a250090141e541305a000b10a0901a180b101181800041e44410041100309036224400540e645030f51801c80d1646400310340c03030275240c0140c04141c60780010846040090824401d0401400081e2180c1000d1010040058044078504c0c0000d4002c1c10440100a095a80400e80703c00b900c40b5000010303200c01d001d11840a9240b56600b20103400d40714078030000c4140303400f015140d9400b40212801e105001d9440d80c00208e00c2119041c04d80858940b000610040c54450b1a09010280c0f030303000181041c0e07072165600ba4070445980070f045070050f8182401142c0d4000c402c4001c00800a000074400340b02d2000340100400010b02c0082c047c03125181443c2c3c8118030340040c800c04004001c0802015040c0404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 208183525 1250 208182275 208182287
    0x20127080102030f0702060906070311040b0a020d020c03031201031211101b03090203060609040615170f1203070c230c240d050903040e070c0b06040504020a03121e 72
    0x12048130f00c1d510000081c54651000900030f1240030f0002c041c6c00581ca5508064010348442002011804000d000202d18150344001604140f11139a0041c81001301880c00030303050923a10740c00395000c2d800801c0403108085040b552319045940c08680343c60802c505420898000035200342035146801403135001044c0305200d4011031203245514448121801102c8015000c0750110301009401da04500700103800ea10304580b225900c40e01030200402c0410010780c20710448019030b080107680e42c01d00344044400d44420400841e8550b110001400541020408040c81e400001c103075008100c00f2055440400140d400108018415001091041600602d14a440d07400c1d8102c507500460b00141d0610030805e548202d17141e5007900d020312520300000440742c0405080003c102101c584400c100c0004c2c1510030114180c4181400e544202080c0841c0c980791144842c05040300c1c0c4510300f000c044c040540d0b9120903500460380d020800c07642c003106030041541c80651030000c201038021226103900c03000b41c01c90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 208184775 1250 208183525 208183531
    0x60e0415030821040b04390e160203040b1b100c0305130c05010e030f0d02060702060705040b0f1c0906020415030504051510150504030c2102012708010203 68
    0x103102616100f401d80c030031000500003240d0280180f0031010100307002c00c00c200408009421b50400034580ea41e119440480c00503c130b081450808140c14104101034080c002065070410b03940180034500c00b034040c40084d41d0740580e0141e040b840d840062200396810303651060f5114000c0f500151500035003c3c0340040010040e180300040400e0414001640710701c51181c000c91401d51100d2540f03021402d0200444000c90310801c0c40303415219804002940c05010000c000707035034003594018001c0d071a014030000c2c00c0103009860718080c000b040c0414009900f15006a80c0c40315030f5042220346404000c54002e0300510780d103181c07551031031502c403402007884003540060080c2e0b140010790012460081100300e040320401c4a0203401c42d00f202030000301e410415003144c0d400140780340703020040c523448021002007c038070072112501044000a00f00300308440007103824014031100c54114940081505150b5010320380711802410001801ca074002c82081c205854410300320005c840031403a5442d2801103000394070907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 208186025 1250 208184775 208184797
    0x1e0709030c091e0e0a080307030f02030a0501061404060c170d0c0c052103010302090903130b0a090504061202040504150606090305010b0a03230a1a0f0105030c0604060e04150308 78
    0x440300d03c050710180900c0912002d948000c06107070716030f0f07101e901139600050020340c101503c03100700ca0032000484c00554010074140c0e50000740c0303514005001d4816500e845030046562001c0c0320400100340c204d000341c0b20503500f14080740e10364082092485114802d200c5441115071501d0a0189030340c0e401255032000b14030a004550000b110380c00e4290024904542c403c4408608100610050500307494135a0008215803c07242044040c10000c1e10300840e0381c1082404010110b080011542e010000d10010700080d20200f140d10300b030030741c04422541e012501038003698945011404000c600665420201c030003560030030603c1d4481c0c00080500a881c40261762941c01d149001d6414074002d202c02003107035805000004a44289040407100f030440781203191032801080f843da404a640030780296001301c5900b80b40d50861510b901005900441a0407150081e8800540d038403807030322600211025100e6504040004141890010b00602103550078045641143c1e00000100505440500f0b800128 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 208187275 1250 208186025 208186061
    0xb070806010203190c0f06060e04030905040902100c030e310e07050d150f0207060c0905030c040b03070503030d06031202030306030a080a26010812031e0709030c09 72
    0x10301401207a49000d4890111240010303111300203002402142e00000341c502c644000401980540c6411044426503400018420300368010801010b5100d0625000307000121400c211416080e00401c8514036000c01440a000e1303a040c00038180350143c0441c40b07100c2e0000b007916644a48030b0005045407100c0304411624a050a40040343c80d01c56400744e100300096031001000d00b00e02c1e0400300700070128401c2c005e454460440320003070f001d19150f0003a6501d55003108000b50303462900f4135050049031512410708040150f680000d010310354000c00c003400070940417a80400c41c5640c14000a013481c41c80c0d80959858030000480400004158210b02d0489005e01c0746801c038030030750001c141e0300c0744021a151541500200540c1c80011801030180c8003985071494503651800d110940c00400181403004a2003c0b1a840010805100101b00c000c60704034241c05000d0450400f4070709035410640c01d07038824003a0340003100000d207254400d540303040042d5040002e01841550b2201c00d440101202160b809500c03007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 208188525 1250 208187275 208187281
    0xa14040c0c050a02091b04150906171b0c0a05060402040c090b0a0804080d150e100e01031509020603040303020c160506120a0209180105270f150d0b0708 67
    0x200a4682107521070b00100500200d000540c01c100d22000e00609880c001d141c0f14604084410481d0060300260880d89038141a655456401800c0705c40c06520000c204010300301318403170304240c0c030b9851a04502c00c0c1081d10341d5950550310301c400e0b9020745404081644101e60071801032200005a00c5d00450003a6005c0201040d40f84044941e03400c10300130500004420000b10f4041c034810400b0035840742c003904950341007481803080c0c0f0041e690516442620401041d409200702c0425203407640d0402c290b98100304156180c54850a00003005200103003020b045114130824039182c80e00003080003913008100c9581c07803038241f50142c025040a01c1001d110b1140006c081e031504803040459095420003001141008203080300403000d103000604898410342c003840945115107030040488440b040135182814198100b900780481c0c000c20031803c0740c2c01800000641e200006023002c1c00c0d0800c5101c1242d011550780c03074a981c2c003440302ca042031320341202030f1840d1141803040d0445094041d6125607280f4482e61 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 208189775 1250 208188525 208188527
    0xa0b0a090b0103080918041118070e04020906040f0f2c0c0304210c05010509160e1b0706020d0e0a030f032309030c10020a0203180607020a14040c 64
    0x188502400038140384a007401800803408800241202c4240100880c2c810040d080042d030000d9020f490895150381d5100e800a0517140c580788406210092804c04201ea14000e40000c1482d4640c5800742c2c042c44d07001858015507140c040444001c0c01c120f60062092503610110104040c046d0f101c0e150f0400c0300c0284031a21081f491076595018945078481d003610fa00c1f10322280c0c4075940b001d8001c58100704000300014803100942503040e40c1c4100d544400c0c0c06c450b000d04240b400e4501c000d10400300b036006001e04200da41342d00581c0c6015180f00460001e40c5640320508400f03240340c0e951200c543e4a0340465000100600381c1c004040f03a012a0307406000a59803640241c2e036a6407a00b5008004c240c0e40c02084c100144030346e22441c0740011865030107050a00c101804141070105540c021201c0c1c00018100b00092001c03c490004200340200c11468014440c100a403a07008800c1900d07401aa034045030340a0341e540710141c46026400424401710316903910142d00720b5140f41c25090b03000c1c1b400e00c3c02c0c041c01c407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 208191025 1250 208189775 208189781
    0x30b01080c0c1e03090118030b0c07080c01090f060605010503060f06181801081c090603110f0a03060311010e0609060a03090b10050102152412030c0a0b0a 68
    0x40603100d11a0544076a880e07416950030006400c400c0d0700c102c1c541d9150f0303d8580007240c05010000409035a07148a04000142101d081d00400380c54143c0722601040014540c3e0415980032110482c41a180e80c013518041c0e0f0b0a101c6e42c822031083c1c5d030130007808005010800341c00002081c0b19000030400b00391743e840151460301040728280d40c0202404032101c03440c2041c1d0000c10206e0f4101b0045100c88803020005a20752100030302c03502103a905280103204c00b06080000c1041003040e0b0440c0d006119138034900415401541c0560003c041d2034020400c4c00c07a0501081c0c0d0243c89070310002e50b071610701c8103000034004d0001d407005480c0010500d0101400303502601c00f603c1d4962002d40102e190a28140038801542e120001d0001010344c0d0b0415240415004013402740100003d41e00c507145c1910386030009141c000f04542d07492400345040c050010340b004200803e4884403105c0001c403180c0030f4143c0090410070304000051300b54000043d510030610300214a000c280d5100f001540c550342c403800501c0c011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 208192275 1250 208191025 208191041
    0x9030507200a0e0601231b011b030902030c04023c04030807030f21110d020c100c0806100804050f0607030213140102060c13050307030b180a0209130204020d0507020307050d03 77
    0x860001040850306400c0b01182d02e031f46907072825002007050281c6000b0241c0b0540d030f201d078440010f9038980211342145814440e2030940349040740d056050011070b08003182d040082410400d841c00601e84071041c2d107414002c9101c03001f17455803025070326503541c1c0c2440c0381c103540110030440000704c03014000c0070a02e0084081c0301082002e01190120007190b0b5901000a0640e0b1843d049049014011860001c1e07090004141001562020300320040c41d800c4c201c0107444000048400303202030601006050b4566074440b25007a601031500102580740d43c20b00340e00740211502c13148010f009030720812000c0b5070181c00a00c030502c84d00c441003030096540ca07550800d14400312a0140140c1204002c00c11000c4c2d50405006181c03c50400384c0743e4555600c00181c6040081e6104880740c4080004005080c080d889144c8066140c58010b0070500031940d0028048081c010100f083c620703264003d480135902d89505503595032031280ca04020318208100081e50f65002088102c407184204210016410711070301074a59 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 208193525 1250 208192275 208192337
    0xa0e0910180224030a0906020c0304091e2007030c0204110c07050f030307240c0909110c0c010f0201020c011a03060c131203030f090f0209010909030507200a0e0601 72
    0x400c689030300741e20102034500340905640c0315409101103a2404003d2006000070080041c000937803807000100e403418001810341251500c0e2038401401c00300e902c0005440200d80700d440a030f503030307a192a01d0b06803034100303d01e00003941040c44c014842d82c128081c0c0d0010f001000141d01200d040c1a60b8030200118001e901a200760560001d111344070000d8000f9039900080300300d81554845001504d850314040b901e01001800c000f54421200b002a040c0901c44c4d056000454901e162a000325454856915040b091000341005000340c06a0382e030b68800c0d41907883d48000c4600a00220031041500350414030740c904018461301425002c01d40c40c071020421243c070301c018059400c20040c070744034214501d40c00d13171a815418107407030300420441400b5610501001074800e00d42c454849125005014620b0300513000f60303940310718002900000c0398000040d0342c0e4440c0c0c4881c94001070031180407810b9030000c5c00078486420000c903100105142e80c911060740c0c42031200307076142d400d404040764000b41c4408010208007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 208194775 1250 208193525 208193527
    0x6030305070803060a0519090605060415080c093a030c0b070203070218180c010903020d0813170c09060d0f0201030e1b0f040603020a0e0910180224 65
    0x700003607805006035501030001410b605081c1e640b00040f448850301240405a56034040d003040c0000400d5204940c041d000540318a81401c3c2001c6501c2c0c0e030280183e5150f03040c48100030015401440603030032501c0000d00074125849102e1250000c42d440d0045210070105000843c15a10f5031814091080300300513095514100303090402d450b81d0b40848005030001e003c41c0010000c40c00561107410320480d0106464a6103040c624114030070380911105100d4003c001c0d08942c2c1d0308584c6aa0000c20030302a203070101c4024601c0030b074a180020003031085801c41480c0e810900c1001402c0c40c40c10141c070100c07404110548810180c960100403400c2c2007214010b074822010700551020500c41522408140c1c418100041c65034019403603a40707000c40307414404090b1030342581e1459aa081c4bc5010081403003082c0d130188400c0e41507a000440301081801042103040e24100054030611040204021000581001304030500180010324012500c006040e4000c0002e0451201c1d038005014801d14007041138a195 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 208196025 1250 208194775 208194787
    0xf0105100512030408010914060708070f270f03120302121611010e0d110a050706050a1806020c150702130b0301140c0a03060e0c0313150507030b040b030106030305 72
    0x48080e41c04030040741407503c014000420303180024805c2c041c51500500b00c20032000c0808a400b440c0042c001d01380380401400400348080340342c21401c0129280c02504040c81c2d5004442c8180c884a285601c0c2c0c2c004400003184005a5a90181205010341e405840d400c00b8129505209406030300c42d50304091001d10803100003452a0b00c05813001c20041e1050314002c0301c002c40c020300d11800e45524081141070341d0000403500240030b40003034003900c8a00d01440078003100b243d80c2e1a00b940f2024544a00010711000140d24095030b03110340e500c08100340c00886440c450a4031004002d5664120300c840b03502840c8020245082c80c010701c4250b5a150754000d00958800143c0d10041000d880100003040e0150f40783c115191242211229140c4614a4040200c1c0c640349911740060070744d000ea070301403905128240284000700a03020b045951182c1449101c00c02845030386030100c03060900180130350b0300d1880d140a0010300707a07040c1c105440060044405110502030441010300304c1b1054840107001c81d408100d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 208197275 1250 208196025 208196029
    0x2060603030c0c060d060b0712020607110304090b0a0506030906010608130b0411040b060406080604050c0307270b03010e0907060207050a090b12012309150a0509010b040c02010903020f01051005 85
    0x70000b100c90804042001d47c1d880c143c202d801e070810641200d10000400504481c25070401130f01d548180035290002c20400208659034030327442035020715004141c4848003204503886441011008200260009a82e4505000e400f51181400e0141d20002400c5001044404503601c0b00c5550054000c000048a501c4a66420b480d070030004449036002511205410300030340c3d500001d00014000341d102c1034280d01c3e250040208030b61006120303072034483c0144144030320258082c0c40c1c00e25200085c00c00c5601080d0303065903140c20b1030f030720362002c0c0707501d5000000070500c103041d1a03602d801069018119030059840f40000d0740c480c1e8070750042d10b801c102e0310311080001c00140e03000f1030301504014001c428000703441101c00d4203455004010088000210142c0794051000c000030640c048850340c00f0705442c01c1205811701c001c0a002d00680300b05501c9102050b2130300c00a602002511400030810081c3d0007841c03802170b0103099082802d40c00750140d1614982c60300d00600a5601c101200015002080d00b0001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 208198525 1250 208197275 208197277
    0xf06010b1e0a020a080a11011431080304061b02150601030903051902061819060f0b040e06010914010e130c03080a18051206180c06120702060603030c0c06 68
    0x480b01103104d500342d944040744010380180081346c1d60790794000c030321100c25540b142511195480c1119900c01c1000f080801d0140001180c40300029001002c000100c6100821446006220141211000000b4041003000542c06184802d0b4400c5002111004102060340c4840d1640c40c0e025410070380074000b60300d640c8203601c8010341c240711342842d03410150000710903088505403180150150f40704000b40a584d40424080302208000d0324010b03d20482a4810382c03212603444080101610703100c2c480c9055907001504040001e5078060800c03c14400007182c0b607699103200b8401d025280b458a81c1b06102c03a980d0240c1207040e50001000b4403c0c9031030b55030030202d920610140079985c4801702c00e00480000c00141c000c0c0b907020030a54842d101d038484009000546c0070203a21903441640c0041d2042021403021440c0e644c880240010358040188544078681001e81c0c8000b507076803010001072481d440105001c4964002c425560880d44a44d59484c1416a070b88544289a50746a000c40d022003c01d142c100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 208199775 1250 208198525 208198537
    0x90c0e010e12160f0f080d030c0c0501050f01090c02070501090302090c130b09030c0604080634081608010323031902010207060c0315140406170f06010b1e 68
    0x15016204601c0341c180160300741407114040f0b8241220036407082000004104540003c0d28000c1207484440c3d10b03009031140e0b151240107156007455140c41c15610280d01500341803c600750408000c0c8a14500824000c0e0252000d006880505140c00c040a8010b440000c00c0400e9804c10703102c200c0142e0442d0200040c01e18010f1050107284810000f24100590504041008203001582d06807110600030400d0700b403440218031240110070911040091007800102980c000c155001095440450744941c02c0201641c101200b225080c12194219400e5026207080d00c0b03101c22018001c00c052262031300320b92184082c44090540e410001c45c1c003801361031203800740455070464400c4918200d691018040ca0f48a0303041100e000d0707540400d09005000542c0520b40c0744c0707145480c0402c80112200c2c15101e400c42c06020758102ea03a0080d0403c2410340303aa43c81900540440784401340d4210034800410354034064076140c4482809110000a180b4140034161200c07000c00c620820710351003812021650700d800017 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 208201025 1250 208199775 208199779
    0x61814060403030c05192d0b06010c03020c15040e0a11030f0a141806161202090f090a09020a080307051209010e0901031209050607020a06030203090a06050906010609090c0e010e 78
    0x1418002e800c8008072818511b420310074544d0180d5529044d0b5001110303c102c110b40d100c1d00601d07a0500c80010868003c075a4400c800342004042d8413400d08003249080c18078807020b07402c901c0c4042e40e02680700390a40a04100c90b00746030f108800c3c1d551142c1c4017040e54540c0310301d4001d00c401400800c5100c1c921402c4142d004d60b502d00700081d803c1422050440c100015540d40c1083c0700c4450340009035500601c4072950000c0120881215800803e0004090700050b03034440492030380c0401c5032101582c1d0707803a00c1154100014101d00302ca003032100035031004144002c13049100340f6801c40c1c0065a4040801510390490b005005411404804003400c00503510003051b050420142d05c008416560f0384401d802e0103103000c0c8032500401e1400c0380000d0400107c039041039202d104184145001a5104a00da50990728240307005030f2207442c0c00c4c500b40d04d0401c0182c070040066080c02d0421074041e00024009040b0b42d204c0e554100c10565601107002100e220340410400581c56041d070501950113441c0c1c0981c0c00c940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 208202275 1250 208201025 208201033
    0x1d0d11010f091104050c0f0a17070c03090501080915090f150106050d18150504020a0909020916200c030d0302030123060405040e0601050907050405010206070e0102010b0a061814060403030c05 84
    0x10a01f40c860303d035800880b614001c40d140d402083d540d109500101940010b960030b00c50228040d58402800c100080d214050401c41c8040008802344014000c210b0100d2406061a40c2c50801c404055114030115000c04080d00c03e06480382844107410302554101e41c0280c0b605480c0c0340c400904480130300003804010041003601d02d0b6120015101c5000700c0c1004070800800a114145407042041c511032036800709a46a0a1082d10740240c0d6034803c0954000b24410060000303c001d107401a543c4040c050100c440070707207000e00f5004c100b42c0c1c085808035084100320140c81c1007411030302c0150124007013030050402000302d040900d030070000c04940380341003050000d0129051964500c0000d007a101d840c0d550400c2d0384c104e04010000d40c100106d8a40d000301c2c140c00c29600b09420130700001d507903440042032102000202e003485c0c4185d034001c0d071186084610280409031220703241e88010308401c0c00300c0c09903031111140e0180010450340c002c0f000811910001e11441c5454510b80b0202ca00c80b070340300c000b85c41d6402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 208203525 1250 208202275 208202287
    0x51005070c12110d03020c040b1509060705210c060a0234020406091e05062d1c050d030908090f04021308011508120703031d0d11010f091104050c 64
    0x14402d241070136075900c01d9004110100040701440300340c5004214190003215043e03401407501c01c1c244265076031032200ba10182c0c3c031a00b01c3d04040e0f142000b84a0180c200d200000c0d000f00c4500c000900400502415000304d40a5486080412040707100d12800e40d0311152071440c01c0c00e1446140b402c0b90b401c0381c92009440442815039000542114007550010050341d07528456204204d6945131512040a034291381000700d03282c80b0340451407106203484148241640c000e1440c558408038140c440440d04081c008103100030340c4900c2c6402c00d80c00344030262110720445161441c058424011160050791000e0700905110114061001040403001000e90081c0c0034000003805480020f101001405048000301d420038040614205000c07054014401c103030008045d03c81c96078044011140a19814980020300b0a07000e42c1703a001c0d04091001081e1207011b03050384007003c11b600200e00e01d0706076480c1008100701e200f0f05c10724800302d07030f8417020081102c01400360b00c502078070382940499031001c8194141841c102d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 208204775 1250 208203525 208203529
    0x20d030201020d0c05030a0c03050402030a0204051b22080c030a02060c0709050a020406140406090b030705040e0a0b2b15060f090501080d090311130e0a0c051005070c1211 75
    0x42c024032013800020b40200402120950385c1c0600f0381d00d1a450300b810481c0c0c1c18660017107900c907214080c002c1d0040387c46001240700700c03101d00c0c40041c04619451f00366489450119025440343c011164494080d081d0310008110f4840200d42c10f20542e03030040c02007080c40e44a9003484420741101030f4424240c0900781000540d84010700030f061203005c428070016900c0381025400b03044111040c8030380701d6900c030512081c4070b080e03080003001c42070b2440c0f071940381e469640303c07507080782e1b103228a800610100380d040003840300a0340c00c4d4100d8160b82ca800c56121048070300d5580c0481d01030100441415484052140c020003258454520398234607130b00740d10046501a11198010b44030f802e10f60042d0b240f5a1799000400c003880e014480e00802402c585051205503155480e00320100007060b036018070440d404003030101840c0d071503805150091915000d40312a807440c4e007003909200000344916030140801c0d01d00064514800c208880013503600004c482501802e250900c46100480802142d45070b403054031001c7c40e9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 208206025 1250 208204775 208204781
    0x60f04020a09240b1312061e0209130b010c030804020406030b04050a060c03060506040302060a0c0204060b0a030f02071211030c1209040c140307030902010e18060118050904020d030201020d 83
    0x500010000d004204071034041d4920482c1240c0c005030f0404c10600c0b004a0010685640504454248000c000ba0002c02e00b0088010110303006815108001004149042c135829000342900c4903040703503141c00e41c1d40100f41e4a015140c5030784007a800206402c070705900080c0588007075a04140060800101152030341c0c0c4242e1035040960f015101948590404020403540c1c1c003d1040500c2d09250600c001881c01300414042d01403400020b11a03080032441d60a428410b4040c4541d00345c009006100b11360755810102d490b54856450040041e0038869040c0c0c0081083c002c6441c0d0581c001c20020340d00c00f80120840340c2c440c1003213014169010811058081c40c0041151118031946002c090b40d444a41c6010030003100d40c0b03001c500b81842003220840540c1411001520b9001e43c540c00d02150007582807004851444c02020100e0b80b20041c002440c82d01046036100b10700c02c40c02a00c0b02c00f014020248101101d201500c135003540a072600000600508080f07401040c01c5200780002340c14a0000740905c000c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 208207275 1250 208206025 208206041
    0xc080303090c19080a0204020f090919060e0c030a020304021f0801060306050108090a12120e0106051c0c0302010e130e0c1003020c060a0228020307030801050f03060f04020a09 77
    0x254407000103004503103043d40848410300d10032150b18590500e044805a12184519000381c4150341c046212310004201d481102c041410040a0400b5460700c8250340380030508500c80d044c05131740361020106640a00400250113021810380c00c50441e0354001a81d80654402030041341c12070f0383d9044141c040b05601c0c2a80c1c00c50007080e00d81c0036003503041110050848209902c810b04108902042c080100f40102d020344029401942d85800880d640b102503410000700e0345400c202c0c62034150640340004042d803204041c0c94041314441c0b4041810801c2c07003030380f03142800050b00c00e1400c0c1c441000190701900340b0412041d004bd041c190700098070030f059012111000300702d02c1c02d604241e8121160b45414095507803540c040381011800e01e030300b01c20303072542e5000c000700806605030380040c01840620030101b00b440b042c004c00c4456402101202d400039180d401150701200030802103000482c4600d0128000c0d0745010300035008080580d100500e00c080244040d1003a600452550000f00b0501014003c4c961 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 208208525 1250 208207275 208207291
    0x1a090a15030506011215020301060f0e15040b04150f02100b01020c090406090302070602010513020d0c030c24170703021b1606020609160314030f1612030c05040603090c080303 77
    0x11034917030324289180c0c00c5400c1c181c6a80724510400c0180b1025170400d00d07181d050b8509240110300c00780d110740411910b5856440d0000c0b51280404c0020703290007024020301c1a0b9182c1000861140c5160301d01341c600203141d241c4400541c00c600c208040e0008103038840d00c0010014030480e61a540c0f10f1001c1480c421068405a07026522460703d84140f680420800000303251a04c0200000c0c54104003000441e104414000c0c440c1c2e6101500c0c0c014088c41e40000c0c409582c101e408510242e68814412010b00101084034811004d01000c10691a0268150b2020030842d285060541c0d40c3c3d03104114003c2d44110309010103180c1e14840c000d49180b00b084102000c1301d0b5150042c40a60400c00080c1c079080c1c00400014656000070540090061000c1c1043d0490780c0c00342c07514030501d64005c0201d0560007603001080c407030400850545100c9504896450f001400745841c444c511203110412401d07500070301450360204030704000070000c81d84298070410029020300c41440030280c03120748603425944196040c80e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 208209775 1250 208208525 208208549
    0x50309250311010e09060609040e0102160506010f1d0703091203020d1d0c010c0f1a040b060607170306010c0503180f0607120309060605091003061a090a1503050601 72
    0x20080050034102c440c49118242040c212030090600015201c4000601c103d000c2c1101144030005501d50b81c1212200e50f060310b00942d00c1e0001d2815104c46141c101e01c065815200eaa0000282c0429401300c5805841c10b09182e400c00ca03022002c02c001050f009403201e070400d03079918980c0c3c022604a0264100742d500c107507030160741c4020700f5104c0b100761010540a0340c6000c042c3c0c903140c4004074000611a41458080c2020760741040242821048590b10400c090300c0c583c004600c02803480800c2d0045441144100c05001541d10740c84240b01c0c1501aa000040081480d415203801440040024552180c01454110030118040d82d4490640d081481458a40340c1d0820030000b00c1d00d000c40a0f4500c84100351885820b003846619503843c01031140d0b018000f810799030109041806100c0e0458000f40c400a00041e000317003000c02c0340c081102054801616070030b2034000b400d41c4800060320325820050006103102055110500d884004140000302807143c5000b0380760020000d00c044c8100c9009010b000e10b90 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 208211025 1250 208209775 208209779
    0x411061c050603010e0a0204050907170123090a111507060506150a120f0f1a030f1923010c050304050c01020703080f070606090e0a1104060e060105030925 68
    0x104041d40c801506992081c0d040c824401445040004d100300c0154040750042a15252030034070720300303040e00c58000c0e079010102d00b140c0183c040360541000d84000e44810354080090695611002c02c201e055408081940050040101191680580c40380d00d0303800404001c813104490b087c00301258085030b012200700da1100204000c515001900d0100142002e003000c0c50306490b00802403400c0c010003c211400ca03074404041c5401c00c890350041150741030054080088070a11003040d800d40d080e2550140c403d104840f101d0600782008a20880b46202c00107419610750304541d5030b4880042d5991031160400140e00100714200400d010714201800a92100c541e81c0c01d01707003042070a01880510440c103643c4807500400008520b44100e5040c051401e2520751120300b10329003000134001c90ba004495050030402c60000401c00422406c12662103503c1c41c442c101403410501c41503c05c3d901c2080100d013112030020f41d01b540141d0040d03a0140f5200281e61200165202e19041c001801034401c208851051007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 208212275 1250 208211025 208211077
    0x8011206060915030b0112020603070f180b0306130908030112060b030d080915010b03070c020d0f03020d09050906090610050d1503020405070e03060106110c060d0e0d0804080909041106 81
    0x1017240034215070100032140c080c944d0081645884044c122008100c0b03010b4014480510540c031004000550028070301c1e1040d40c03032030540e003107030005c0d40c00c50320035500b15941c103007008818800d50000da94042c9050341035a1800b01e011520030b0201c00d0542d0b80036100c0c0c040789501e40c1c003400501040d0055481d000818100046024076003100741c0c01c1480182e031b8150062162a60f41810380341d22810310718000000340842d1001c10340032140e601009201e01c0b4800c3c1c41d403003015004240b05682100c42e540f10580c01703036200c0c20811989000c0e13511542004842d004030f0860301744510100000341c1203050440ca0b0070140340d112000ca5205941080c0012f11400051003107140600452b0303000356640c41c10303134862203c04000039210700040c803070f4a0900144d107801c002812000d1006020302d00004000c6034a5015082c1550b01070518005019440c2c0170b042072405159014a000b1801643c000c42910b04086030130007481040c20b4043d105a82c125152800c400040d5200d00c010000120a590542410591080c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 208213525 1250 208212275 208212293
    0xa08040e040c06020d020601031b0314010b09090a020901090203100302060706020706110403050d080403180e09010609020415110c0d05160608090a080f0c1603170403030801120606091503 82
    0x182c00315081704003400c44165000800c030b415039400220711a5141e00003041d121507242540e0000741080440303041e82144500660050241200c1980c9840a41c7d0324041041d03282c1e211550000d501010b004010300646071954069a44a82d000809640603601d83d000141c00d1307000f0100c21200e540d00010000100503d6009481401400b9011141020304507a220382d141d200c030008131010803100800007810700d84039408040d0384030210703414400303000d8032000207a19422045800c10341540c20143c000400305617500c00c480c1143c0c1c15080a120300c1504810445610380e421040303205600c41c1d01d041200c05e558113001c4c00f48040c8120b00a000c05011050b5002c10501e103075001c030003030100400400040080c007280b00484c2991090f841a5502546955065070340100302c813007605072252a515842d20148420081c040c3d90240f20007031072009100301d00805901c41c078000100001c8840c8010414100c0740303614481017511a100205074140c840641c0300850303e071480500c6800c03c7c0760204109005c3c4803d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 208214775 1250 208213525 208213529
    0x90105151821010605060f030402060313150e0f070311060c03040b120103200108130204090501060824070c0f0305070203010f05010512010501080c09060a080a080a03050a0b0d02010503090a08040e040c 88
    0x344400e810050f000747c1e0140c080c04010000b078042c58002001402c0c4404400c2c0301c02318181c1c000c0c4c441000c218190709500052140f0035401606124801100801e04400a210012640e01c003c0581114211030140b1205ea000342c020b0112622050001144080d80c040141c041504aa0410300085d07145050120b00e05140d03035240207042240035040c2e155070340d1041050390311403250041c98098600520108005185007900030704154688030010075819000b05001c0070311069041d9102400c1e1410700c402401c010140e0380c4001103010501c0b120002140e1004e10302d0064002c0c01c2c40390030854560086825944d0403c4186d01c0256500010311003460007420f43c200391a45200208001c2d03040007500c0d40e0311503034803502078411f07900c1307200041980e51240070000141201e403081d603e842c400d81c0303000003041e00810103040100c0e0510307000408042983c03140000c02100100316400c5040d154005440c150700183c1030841d03e008000b400004216104000d00003001500900d285501c5c0608100c01511a19 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 208216025 1250 208214775 208214779
    0x150f032104170d09050f130513050307052103091b0a03140d0917030301050f060c070803070b060d0503070318080d110d0503040b01090b01030b09070509010905090105151821010605 79
    0x102141011545890030905078004203001d000520f92627520303050811729042d01004005110000d825002c1020210b02c0c441301131504500313a10340e200c0d010b00b40c14803404216001c1506900007031250850607040050040c5034134014129600464a030b40fa1101d018160fa501d07403409900c1428048003443d0b1040141d8010811b02c0c01240c0c204a0b5846142e480e17100610442d4490458001900200c0d030710a012610744178110303401c8404060344d50104a880c6e8209100945a640e5040006402d904002c51180120b0394003a01840c0b80044950341540c03070502d45010501a03059940001c600385030100070003020110681c542d60020310640e603d480c581140e0b180590304114040c400d000020714030340b04550640b460a20081507010707980004800600c641e0801c00c4d802140001070122a40e000310081003000302c03c0e03031840c40190f15002817010790f050a10510350002c40c002410040305a882002e46010f013403840c03103050b0000c9200300180094043d81c000c040c4170505101d0144040109219010040c001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 208217275 1250 208216025 208216039
    0xf03050d0c030c120204150c0204060905040b0403080105040603030f030228020723030607140904090305030108010b1210020a140d02040807080105090a08030a0f14150f032104170d0905 81
    0x1c140710b5070b00303400f47e0050750b00038445803201e180c2c21580c2d56000500a8030078030b40208124038241c1461001c0450070795007500072810390000030420741414061a070a4a030585c590140d0346044c110308600039880340c1018046162034a1403000361404030300140c1d14100c82c90780240303412401c0c01a1134020024020103071044040d40f01040403562008680158010035500308490106a1200320002c1c6110b03223100305034000d00e010070000400d80c0190195050b9980480204010403561041c800500c3d05500340c07071625846400d18816454850f00100080c10603482c054140520707091a5000320342202a562080e25004a01440201e8041114000900c442002070009041c04451641c4640003010050203096000001445a002681085181038011030f000c202030220a200c00401d075000307480407258911801c1426003e40341c800300000301400c008000d40405841d1460180c20240281d0520f03000f8203007404001094440b0074441c0d1240140540071b400ea1318041a0007c0818010350401c9210f804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 208218525 1250 208217275 208217279
    0x9090309030f030c0d0f170a0609141306150f0e160206100e1b0a020c010908150a0f110c0c0301110a0c0308100b041d01050a0b070f03050d0c030c120204 67
    0x200092045c0d0601d40d1400c224140d03020340d1804480000901d100141c000c007488007230058021403588200100c03841d14004124150246406174042a4261030542c1800744070b04a0704007189041d0711008448203440e000e12040d50f030385c41d08107140001d25070044081c2ca08003010000b01d4a0030962039010103981c1d1000e4200e520f49200c2c0f05028006a001d0a6404202d000006681580301505000d0030040d660280e42c070394007000741c000c0d0b4840580010b41d0005010b01d400180105000802c0300403109a003900f010f5513603035851100c0040424000e81701c0000d4440306010708200407040107040c001306031030103010041300c03281c240340c00d6501124000745040c00c1005440c0481c0c0d8401000503801d80d251405015503140c07412403002e140703c150030050003040e000070000b90300000e03103600301c0c080e240c0c01e000981c4a07039954040002c01c1e40684600e03000a00d04200c0c0e000040c00342c00051140310700ca801c181c1d0516210101d49411500580844004a50f84d030380d0600e11241c000c400700f01d4160700d43e20294a014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 208219775 1250 208218525 208218547
    0x1803070f031e02040612020a150207181820010e010e040c03060308030903040914042310050a0501090506030d0e040b0105091005130603090503070b06010c0209090309030f03 76
    0x3500d803202401200054128560342c002c6036210301c0c0c40c0c58004200340035180e103d240400e4a40521081240315010400d0005003003c3c90b017a071800c440205401030803c81303181250b900c054041c21100c64580a907545050203240130108401e128131801504e800500001c0c040301803041500340412181800081d6442580b1a82d00c61030b107855102042da801700740c2040d44401034001d07040d07a0304000c10400000c0200080c8090000141088a641700801e0004007c000c0d0780d0f5800c06000d80f8041c005081600c06400d0000c0302100c4402c17204e4000044606201d000e00405080741c1041c0e0384450029103c0d401008030038103d001e00c41d00050110050860000c0704c0b50007400d50080380c0c01e141d01032500c0e0000110268001c1c002d0b1080f499000d0401c5007818400e15008096500400f80040c09140214ac04548684030b4071410031300300c1d8000020f5103044402e440315800350300001c1415041106184407600140c0301c950890b400713510180000d60725020b58104060420b000e0030485200b40c5d100340b10084000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 208221025 1250 208219775 208219799
    0x9060218150705190503090a0b0315040603020307050103110f0307090603050a020a0c0209060103090609060b01080708070206011a0d02070605010e01060c080d020706020705060f07080a14150103061703180307 91
    0x32130038000f040540e8226a180080c15802003c240a9101840c490002102d5100c8001581706550070189070850411401c1000100d40650001a40640c02003a05000c954001e501c031b0140410720080d0b50382012003e07840044cca51041310000000b501c108010070249030503000715500421112000d60402d411840c0040c076010341c501c400780c032a010700d0f404601141d01030785c0440842904800140175848041c1001b001400c07030400304030b000a84d41d41c00140391520580301c95000d440340764003071301071646040895a01c81d154005c02c1a0000004c100c1104001010300c01000483d200e034402040c65850002805046001644184144041440980c0028000c01d007101d40320f000034840180c50b101c190511400070300800f0f9008042c1c0c0f14050500c042020b00d0302c6420302c1200e0590750303070196581d040b1525040c0c460f0041d01030018007403e00032401030404858451020941850009580c99a074a2000089624065022070a0b08000f0380d1512580e05a2582c0204841c02d400404406180c107040c0060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 208222275 1250 208221025 208221043
    0x30e0a030e0103180309080c010206090307151508010f0c0e03030f03100308070b04050c1509010f021606050a081f2105030a0e03060f01032409060218150705 69
    0x100040c0c0c44507014568003983c03100500d8080303428840c40b200414038000d8840c848601480b50319104140b1540b40c1c0d5880001e89a21450514014605011055407170b83c0c811301ca052030104403170340c4550f0002e0190743d00740d051400820300c80e4000f0580411982061046506081150080002c940825030054500004403005030000302d41b002d95903a5050140c2d4985130142e00300a1002d40c0005541052003881c0070254000c0c0c0c00346064407002c120500821240e03440144100d0502207080c040592158042d504020b5042003900540381d0001c6010507208100030f02d0f030068804510041760300d4816640c80215650f026901e288121070f20040780003203114144c92841051480d0000c1295484070340e0400c0f00045a242c0c3c084212601da003040100138141c0465003142c3c6000e4070038080081e81521940b21007604032074001042c7c03124440c2503108030139141075820040750610345800c0000001107541c030081403034080541041d40e88240c0b40d001c10041100648000c90314400c1485941c02060000c81c8000e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 208223525 1250 208222275 208222277
    0xf08100b160302120a02010b01090605030601080123032d07030b010b030c0f0c070501080a1406090c0f13030c05060403110f0a17070e0a0c170709050306150907030e0a03 74
    0x500c062868201d25041c00e8083c4c0d03a588420218122400c0e940540001403408400d8840c0c0456644480d42101c00e4081204c02c903001540c200c00411030164a071281030350701c411660400902010b0000441e2600b05540d0501181c0d407000c003d142010384561014401d40414007000d04051440c54030f40780c0004006000d507034a0041d000010545030307000b0b41d0480e000172415050b03a035112081202c0300f603100d190701d120b5140890090400035104900f07134861024070f0481c0e00480101034550100780034252800030200500e01a04002c001030b204c018001800740d003501d5043d60079a0758150b261400803901d00e6804103028100601041c0001190540ca16111104c107503a41c10700b000b0018002200c507410303540b0a91100c0036511502c3da100401140c402c040c0d0b03440c400c0460301c0f603c41c46808021100301502100001307850204000301800112807054200c000d40c03a1600c7c002e0b0700c0b0400a42021002c5d5503c0006400d200c00c003ca080c10116820350388210a804e04002600c2c00480f61501d42e280310070020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 208224775 1250 208223525 208223557
    0x30901050f09011b03030f050714070303091506030c0315090507030f02060f0408030a09080f0c0f040603061b17060a030b04020d0602030114030c040509032203120f08100b 75
    0x25403603440b0325201c40d8514000b8021316803000e050f0402500500c0d4110166983c5424100003031600f41c0502d080d8180c074880b11030308610b4404d207070710110f0080c07082d00401c980d002c62007008141404010700465014500600b01840f803580fa61078817150086402c601058018140811000450303000310f0880112038010981a40144207440010342510401d03624031134506001c200070414400c0000585002d0940d500c0e00c0e0305107500c071444c03d0382d00c60b0201030700c2c0030f241d01c09140d0080500b4207100070561020040c2c000300b0b41070744940d50381c01a5842502c1414606011820104203a81d01c05030b44001c1a851510700c00043c14040013148440b646400040d21818810707000c07900f10745404140f030344000c0c2c10400464503541c541c02201a001800341c2143d109229012408034030303140500c240c9008920178030055140c148400c1411182c180740607880080142501000008030722103407807200401c2981e6984500d050940c48010309584d002510f8002e841400c0714061009030321b680c00315001c0303002c041120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 208226025 1250 208224775 208224787
    0x103020d06060b0f040501030c020f07060302180409141509030409020a18031110081e04021311040e0a0e073b0906090f060a021b24010503030901050f 66
    0x30030301511007580f10b2440403c0006140d0030290444d0301800582d842681d041c49022000d0b20304a13542c0b000709002000c00e412014040160a000f680100840c00317034615401424000140014201c4002c2d40b41030301c2d41821b40c0422050744509100d14006407124032141c0c001401c1c8008040d03134a01903400741c111125070000c3e642c2c034443c0c0075032845010041d11940e6183c059449140813650107503000020303801001c2c01e4802c80c81040c058000d40703100729000c0e040c40d03159041c2c400b0a4441820090401e9800c1a6500c00818842800340211180f000c0c02144155445191400c6070140300e1000301410a4149030010310318001002140c11011a25000c031114070240702c0300282c44900003405a216154985502d2621b42c01044030700c0036200f8440030007540c00c55520612788a07190724030a1404666508940c00291001040340d02501d8124100c02e2814103006c40300b0001c514010403c858080704c40705502911881d90100314130706001d803c080d00618103024602001038141d004450043c01c03d107d001c190 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 208227275 1250 208226025 208226033
    0x507030c291609090b0f0906120d0203030f060a03080706150f0905090c010203040e13050a06020c100c030209030a020f032404030e010221070c05060319061202090103020d 75
    0x401c0d000c0c0081060541110300b05041d00700011030200b036080c00851581c440c001074031081d521585107080000750442c19152044010020260402011136904c1000741c40300b00c024620401941042c120306400650760307400c0107810b00c092583e008104a05c1401349440900000c1c000b00c094500013544154041a41401102c41c850383e50b400d43c220880b45070207464002030156140c0c20a40c05403600030140c82e2042c0c050b5004907143c0c444ca020758040300150030041407000f07941410f21413100307001d04142d45c000b41c03c599030070303059074003c100e10991513200f18420b50061a07180b1480c841c141c00c50038210700d04078003100413940b1450302e024041c0c4242c5c80c4401c6280b45450074402c00d1101c1d080ca1407001401400301c8401d41d0030600c02c0d501500002e2100351803541a500004440c1680701e802e03804d001000326996a4010207500c00d95080380d031600400d41c00185925060095030069040b0a075170080145404805000c4407200c1c5d001140420fa55038140025071180503005040d41c0d0162845200c034441800c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 208228525 1250 208227275 208227323
    0xf06100e21103204060b06040e060111010e06070c02010504030c03061409030301030809040f1b020303011e0b0904020c0a0804030813080607020606040e0c0d080d0c0507030c 76
    0xd010110904512542507129101265010307000301042c030100300c0c00440d101c803070703c40318802c005000034040e090269400401d54221620343c13252281d1400724403400100301081264009910490010b2510b006000554ac0c000d80c80710151048076008015860901981a90fa000007134100c0301800703000d00c040301c1035901c26401c0340e010703640243c00701c6003195032890124010481f400a0610480400303022851000e004000c9038122900600c2c00340c20080c6030400c01004040100100083e1f0b03680c0d245480181c045d0300e4060980c0d4001c0d40103140c80350714084a0364242a2040d521008808048801f8800b00300106d0a46699102c00d03580141c0b503002d0424001e20b0300380040c002500d80600450700004210900c0300130300c2100c070300101e02c408007684c0b2140141c0d0707201c0554261015070003003c000340c401c1c10701d80c3c00380071001c3d0700780d040703c0304681d405c4003240101190610603a50f82a0000710108441241d00034a4240442c07450300502d40305580d01c0c01450f41c0c03c480c0b401401903440002000c00102560 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 208229775 1250 208228525 208228549
    0x6030b0d021014030c03070e06040f06031d160510180308030619080c040b040c0c0b060406180911030a08030103300c02090c1c0914030c03070302060f06100e 69
    0x483d503580da400c00310a802580d4000b2030f4a007002801014442410381010000d032801c881c06071000380310403420004260b0140c484102e8006088035400c1e0201c29415080110a688800130f210070b42540d400c0800b401100e8a40c1100b030000c0c400d007400007042c003102d03000c100c0c03080b80c3c0c00601b20707070f02c03521004005007021848120b0340103001030b03181003c1280100840d42d400c0040048604000703403121182070006070303015610000042006c42d5140000b1a00404e40b107603002e01c000740001050f503218607003801c6148107101411070300382d80c0300c0c8040c0402000d600d02c0100c4950071401014020065070b01da0805110500004203c1500c140900042c1c0400c90150101100040c03410030507011303e40c030024030f40684035409038403e0481201003083c01180720201c80300c0d52a50410700c1640d103110402d038800780404c0e14007100c000540310000140030100740041c140c0554040003031907a4000504000f0700e0000c4c060446c0c4003a0088505010305a030b54001000c02c03200c0d0600742286001c04100000c3e51b1500d50f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 208231025 1250 208229775 208229807
    0x1e090903070602032401090617090c1504050103060e090303131a0c071a06010210020f04050303030a1e020901120c0215042f060a0e030a0609051606030b0d0210 70
    0x4c000d021621040711441c0030400c0c419110a0345041c0042c004407442e000c00d114810203c0d4400468503103500b4800f0708940c0c0000e80340202c0d103010343c1e200302203202162841082d206850300418188420340e4180035400080040e0164061036060001480c0d44a11000c0c00b00c400000904001c001041404130030341503048100403d032101032410040302240e07948039070000c0b2038200452842c20090410400e2450103100180c0c01404201241502c4e540250300103240030a12010921002a0907941000298031500f404040030480302900d001c40020100555000b500450060156039016640308080c08695982c41c0b0022507000800002a1300741b940b00c2900503ea0a0800c0402080c00b0110114061b02040d50b0344c0d0b40000c600000f48075801358002420b07070b0380c0000100180314446100e0f50b10036a610500605580b00d107a69070b6281d908a070100b07a01280c168010a1800800c00900080d850007026141410300c040c04841c2c00160141150307443c000c0c41403a4204082d109544944480c041e580301c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 208232275 1250 208231025 208231027
    0x17160e0612010f05040311030c0606151c0b0103060e040f060b040608010f050403020c0315010302040e07170d031803050318010b1306030b090a0b01170115090207020108061e090903070602 82
    0x3a00c1d80d108090b02c400c44046e80410748400c0c41811046c1c000084940108c000400f60580e038444100300040c0114550551110550a2200626109020b003490b0a90160320340005100e04443c000542950f0203a8000310b442c00040c01081b010403410041c01c48001d5114000180041d20034001800418564026081c3c0d986043d10f10903185a865012a0095000341c00301da103541c403441d0070542c3d600344981880c0c9008101000410040c10140c0010303142c00341c100c0661f014141c031101030282c4561000c410b0f01095009440780d00106805214031760104d40300740d800381e01c622119100505148400340c4511254603a401d1a000e4142c001e40c40222107400051074001c070146198402c801800340d0f40002e50309482e596001c1a518030000451080d5141d101c5554411a0302c1c4c1942c0000c8140c0c9482d204945548030411300a045204c0198000501604100142c03241c81600004184160040c40307103028180030001c80141008503401c0c030000040860b010242551034041c0a415801501e034014902d41c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 208233525 1250 208232275 208232291
    0x90e030304031706030a080d020d0e030d050a05070f180e18060a06030b040b07271805240103021308011d010902060307030b010e0a0603050117160e061201 68
    0x501200441c01640250384080ca81140740010030900102543e042e0383c545d002c01e02107800982d4090260184031580d4900501b80005481e0040565043c580e4260460300009440c2180703100c0340c8641a00700c00a52010411450700420140c0101c003c1c01c2c000341400001000350a441191552a0018000c0181c204101d0304044a042c00226518655142c080c0950341c001000d0395054400d01003125000fa06510b215141d03510755558400c00641240100004003d410f00c0605500c42540e600307814140705c80c0d210f90b2400042c0c01480320700402c0c002d01241480c0c01d000042a061503984c0c40c21007045d48400d4469070520042c0d000748901d000b40380c03004240c0e800010322500c2c1136002d01070802170304100208840019441c2c0d822600b0100300294415401e20100708020320a600603000f0782d5040c142085040c420b0f00c00201c00d811940c0c003120010741c4035001440507142018180030340400c00c40c020a500350704400c845041e85028090030160042035000104c91b65100711070001030740040c0008101a05c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 208234775 1250 208233525 208233551
    0x50606061c1a03070e10030201080402060c01020406050304021309151a09041505090d170a060308030a1b0c03170c041206020a03140115081815041101050c0d050a0201020409 76
    0x80b40900c20780c2c8603005524000411200c900a01480b4804808108040a08550054544590141007a07800800602c094408130109100902c0640a240c460725100e01e0237104020540d1030380626100001c0c01e18102d04009880301040340401d038000080030555800e107542c012440001c00c90580d034421100c0707050000340b0400002050804036000400c2c00f461f0303121003031541e4400c880900d450004100d031a1200356500f9800240350030400340780300458203070358a0300c40102540003990002015a139811591414140c0301405400500305410f014100003010784015002c460100344c461914000c20001600600403c000c44024000340703810f0000000080c20000001c0d0805c100686c082440c00040c40c20315900508414100c4180c942c84a056124860301180c600001519644801c441c14000c10f0315404148441ca018003a20801000b8600c1c1509000c44420301300320406040c803400300310001c088200800c030441007144a040507070341e401500108900900c10780d0301c10364080d8900f110b8010307a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 208236025 1250 208234775 208234811
    0x9120f0a030c0b09070f060e0f0429010e0f0904050f0307081b060103020f010f030b1201020d1d03030402150712090512010e1b181003020306070903050606061c 70
    0xb070203510043d5490703072050051640ca0509003d04d00425041000410086219540c0d14142610250004807041e11300c00c041020b1318450840c000d14000840303040004002207180442c8903000918208140c01e0400d408281000c012141c124000c5488000050a004080040b041401101000c40740d0364039840c24803203103a820450000b146d04606100c03411540c0400280c0c103058903001031200920840400040d211a44414403100034142c64a207001d150780e6440b0010b0303c3c0031440c1e070300260703039403146e1038280b0308a0b42d000c45400c03c61041c4400c6a0000c44001040e0f83d8481c0e8140c40b003452104103d03401e02564010150028940740440c9144a01154081e00e207800b10344040e41c0200c82030428071821801e07554150b0f06400d240d80400c44400502c00410744a040d0b03400b001c1e0000580f40000d8805c0c0803c1c0000b190038083c00c0d040780c0c0c42003045007010000d00f68861010315010140c0340c1180d427203070b45a60015012034030800c004540b00500920002d004644880700c51010840c560a03135103e030f030007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 208237275 1250 208236025 208236047
    0xc0d020c030c03090a060807120e1f060501090603050c1b030408010f020406090510081b042402061e0106120f0e0706020717071a12040c0906050d020609120f0a03 71
    0x29490317001e0001d00c0500481220303005408035102d5060210310003510b140140400c190100052055921024121408280c3c0506004240b50081051402c0c400003400810032540624101071038403081107000c5401c2c500f5202c001c080f000b246100d02001e81e85007403943c0580e410800c0745501e4049403040c010095401801122240c0d00e034020003d68400130803032610350501d800b102117556007001034407074102c108031110000c0302c41c42294107058940b1121049486401d001e2140201070301c42e00740c0e449404001c02984a080c410001c40b03031038221401a4001081072003007409024100050300441039040d00000c00504003203d0800c00e1202840000350b807000703140306600240c009c070740c004a1142c543e0011400e0b650342100040a0710707403429407029181008400c841d05048018000800711035845502e83d40294014441c0aa6072802e104410040341c901e6403015200c0c0720b00c0c03035020b8016164001500c03000d0314100c4250302003c9603000600d0500305138149280288c02003144030740c100340e0022003000e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 208238525 1250 208237275 208237279
    0x3020901140901061d040b0a08240a0504021003090221060a0b15071e120f020f0d140913050a2004121712010b0702190e0c0d020c030c0309 61
    0x100c140d0740e40500750790340c059089882c0c00c40380c2d02203e0151542016001f4005041026101c00e1409640714221810184c42c0c07203035000400300c0b22541110321865a84002d400815401c02041345003800e50004a200c2d6000410b58249900c4251690940d078a0310081180401700311429041d10058218054460f80300300e40e0030400510f8852480c0c024244544011a140166090340b0303c0c6c559281c5404d4030b41d06000904441a007854284500065441c45540c0e1240c075458070b480204102010300139041004103021042158081e051042c1e0740341d0f102d01e440c0c00170b10a01d60750640c2c400c0c82d00e0214032140e0310100007040b4541081d0074894001712070b510445451044404404100154000042d618451803155820039480040f61801160f88062180c000480d0801400d00d050410120100300c040264445150390b0008074a4000350304008411780c094810b28901d044201b8144041c114616030060825550380b01c003c186180f02a40c00ea0413159441c000e00c003240d8540e00c804550a0307132070703002d014128 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 208239775 1250 208238525 208238539
    0x60804031418100c0c1a090301020706060e07020d2c031510060908120c1603060c0806062106030705060c070303030612050c010309080d0c0801080115080a020d0204060302090114 78
    0xb14114469013410040540c445119540c0318504151800580c54002165601c90410000000145d409100400c22648500000b140701d51800915401003403004120f2405d5400c00d05100d802694800094003070403103140700d005e8440902d80032207054107071005803054161045c3d0031003214545100c3e013800d109031451000c9006454490340200c4007602c0c50321800e48290710002030420284c910038003621880c0555411950340c0300d0900e17100603540d69258025120140d42e526080c3c4225030040c8030542c003c4081d41d24900d0581040101320798040b06444411100342e603034004c651035a9060110304001c090040c101a00d5040b03078800d0644805480c0300c1140407d00e0001c000503500c82e41c02640c1580e035044005013003044010030064000e856850403c68510004110361a2030b14038901c070391850590195644209503040182460031204600d195034400b00400104010403480080d50b1802d10380e068032540790030310213440450042c0c80346400c000d500c24072440000c118941841c003010312040084400d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 208241025 1250 208239775 208239799
    0x613050706020109020307120302160b07050105011706060f0303160614070c051002070c0e13061a0d11030109080c0a06060b0909010b130302040606050901020606090c04060804031418 80
    0x20b078201d5401d0180250141c0156a0800085030f800030910400c074003e0041d107205511189a6070f281e0851034118280b284004100b40c0d0902c44d00348119409403a444143e1a40e40701003040300c07942c59070002d01e5184218886400e20945443c14420f40c1c0c0c840c0451031104148403100c0c03410a000e0a0303a030354004d11043d01040000c140521038241d00f0031541c2c100010f8142c21a00c7d1191401a602031036040e58040344100d000150040e0218560788112407032040ccc00c803685040d01c3c00300251101380c050003628500001c10f803c01a40c4048201c00c92a81c0291040c03010300c41d500c04640504040031010340312041c08180c0002c3c2090100d6183d8080d44607000c200805602c42480500724001c0c4400e0316041111000148108640f180080001c071002d0460391180c01d03941c1c0d00280907903400360003010014801040340c21807560100019a04404202c0350000c544c03038800044112030080e88658810052460045400d150003074001d01c440014008506903650701c603101c010140d00d8510300d10780c064203040d405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 208242275 1250 208241025 208241027
    0x5011a040b090f1e150306090415152d0302030706120f060906030c0806160327080d18050a060b010c06050f10092d0b03030414031603052d0613050706 66
    0x88074071488006217003480d941c9a5031102b40807800e900b4400c10810b6928079101e44206c01407074068009101d4505030201c0c00703010380320a120006800c0d180c690041c248503400d200503980030a20b2010750354a85442e1a510009200410141c07040d83e4130322181516011740400c03851100c2d046641503902907240032800756580c00d44280d94403c100d800f291014851000f910910348240c010f00c828180c56018a101c41c0c5140b079070a200814100b8084441c03c0e0005240302010341c1a004d40ea80000d030907000303c1e010400f10746841e5190440240c00400391a035074003007080c89030f0182c00c1190400b07402040400041c40c1c4400b203806080401e840402114429503400a001c4059004514440d6041401c00201e182250308114841a4040410b0bd02030344804c941800c0c2e8404001510003040541030065140c0304071400d150a2081e00c022000e0040764030042800860000100080700d1a540c483c590001c01040143e031101c007500c81446605405580b041c408068541d8165418032402581900d4035a80d80b150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 208243525 1250 208242275 208242277
    0xa0c06020f060106030902010e1009050a0b1c050703110a05070201021009053f03160f08070c020d061802010908010c090314070b040308040905011a040b090f1e15 71
    0xc60540a0b03480340700103009461203a00000e400c3c0b0f206041040c080c2450500080c8240201c0c540c402c006824000100004d19114000c54001c4c20b40ca05103a181610719955202c1004e254011501040c9d124030203e840940b0a600505801c2c20708001942c9600c0351a10040081c0d00c41c002c02c0e0300500c54100c00f141070000038804e402c1e81c079900900402c0400c1441115603540c0c004880900613108200d183e02d40d5500d81041c6980d1442c0886218039035030f140580c00540700e40e00b260f0a8404108020581c45c1841780c0045211340c0160550405402101881c40011350701c0c548600000c05043c20000e840c661080c0050562907072500c00d803030f42c2140d02c2c0c880d81d00c035080342c1400140200080c44d1117010804100100e9215105955000688a802e91590888000c65016500c100c1d001a800a8100003541c0705200d51400744c000001e40c10640d11810308444454052030040e0800034800080d440c2030340e035654088001e402c00c050500c201a03100c091601c40e40300080700543e070054005508107442056040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 208244775 1250 208243525 208243543
    0x70308130b0f0304020d0312020c0c0102120304080913150b040e09011415010306050d0c030b1e180307060c030f0608060c0706231609080c0d0305030a0906050103050a0c0602 76
    0x140d20b2500755544c0f0740030441741c50104103007901406a140c052140c031750a41d00082c0f0648168400900840d42d560000900d4020803015a0480c660144103020000e1408005c480004d40102d4440d41c0c2d030803c0070000300051400c1d07044140d1900a0600000b9100410317000f07441115000c8401c885990b807039000c0e01303080c0da034100d1121001d980c50a000450300e44450001155100c4189400100e2580311004191a400e40c11020303070703140c0c408120030000c025510422a904c080040b003110800c00415071030250841d0050f2a042c01022107182c0030305113013000c200752003070190445802e020072410003001400401130b401c038072941a070408602050704d40e00014001d008111132a14240703032041c1d43d200d0318014012010b0320714021003154007105194400c0f6007000d0055000640700342c59007040000180601106a01c0a4010b4100c1c418041c0745a031031100c1d1403e803c2c2c07d03003030055484d034440b0509001040c14050040c1b07128a03040000c8240000010420642e5129128900d145034a82d201680d40340020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 208246025 1250 208244775 208244797
    0x30c25150801060302030c0915092d01051e0a0806130207051506040219171006020c04110f040305010608010b010302040e1b07120305060901060e0d080306030f070308130b 75
    0x1001c01040300f07600c241e0041d0f5014110b41c90640c00c10081c0703000580700f01c02c80d0003d0107141d04089040251442c1c80b6085070044064200300401e07401c50225048405801c05201d00e05001012900b440c82d00e110328000c945000f22903100d03982d1202c5625002c0c02d09203003502c4482c0901211603040800303084a100300d034001600800280141d817034104d1084680302c0010406500181c0a001e9a0741c140e0706a0401c42400f5841d403503115440c64200550080c0120050480180c1c000da204104400354020580b00058441980c01241103d61000040c07000e20440c5c8401c601c2c0d020000d000014010194403040c26964580000c0c000c1c21070910044044e400749000d001c2c05c800a10300810048960200e28507881807401e81020304006154683e0054544510174060101c2c0c3c446d41042442e142c0240500d006d080c40c4e05155140c041d4210200c0c0c152511140d009082030800004a041c50380c0c00c200c1c2d844c0740c0181030304549005072607160500e03190f00814180c0d5090160300001050715602e41d07094807400356074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 208247275 1250 208246025 208246037
    0x9070b0c030403020d12030f0605090a0f060e070e1806010503130c030618050d030603050d120b060403060204170f0a200d0b1b03100504050405030c2515 67
    0x80121041299000c031600961600c410000000142c0b0f8060b0400340044c02030b4054080802c4070b20001d020b07a582c054481e521645032074400c3c00b60b0343da85590360340c000802c0da100140801c000d010721001440180c210381400700788032003040b00e0303240e11105140c200e40707050f11851a446900f22040d800c3c1c10741600e00c40d000c10b0f401e10000d0300e09007d450040326290301500404140c0ca40d01c1e01c403203044451f4a00b80d81034040301c44070720700f00303104c0c08108014080c1c3d2103250400c0114a5501c603da100d44100074072900700300020f00c0850002c0b0790754004240ca00c4004006a81d01d81d40c07498031800941c4284200c44110034603480e001800d00020800c00c0c0100c3c1c82c03901400c03800d142a41d414910035420704018001440c00f84160b026510f8112900c4219445400d0621b000e04241040380c3c40a5804d401030b1089580410400034043c5818101000b2109d00303076804215034a0302c2c54110b00354000c80999a4151003007001a90010103009607115401d406d0014907200c42d9280c0c51440074410b1607403085000702e01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 208248525 1250 208247275 208247279
    0x703060f0f0b1f1205090109060e030c070e0a02070c090905070611150c190210060506040315020a0302040305031815030402060304240e160b07020a030308060d0204090b0f07080907 79
    0x700c000c06030002c4580c203281c40400005200da110080785d40540304511681e549001290400c60a071190340c000c0e0b189000298140200091240e03655070700c5000d00c40c041d95a02010400d400c0c416016075215560100400d05c80a072035581e03980041540e100305881d64482c040c000622140141034641040900c14060301651094004546000501416000340890200011200e42c44448442c4030849030300d60181055108503115a015504181c0116110720307010482000056601040480d609060400158072002c00d580281e00a015990003d0842c1c04002949189990900c0f0b01c00c00312401200c0c0b10300400201d098105c05408200c034001d4210380e0030008140420103e81804250644030045030007010805280030080c0d030f0041c401030803d603020407985059504506003400c050010042681d05000742d03134000507050201403202a082c0041000030036101c0d01c074841603606664028106003c00441440c2940350403a00b200c0c1c1d00851a40d01c0c000c15102031140b0380d0180103540c5e0701c008101440c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 208249775 1250 208248525 208248559
    0x40c0b030c040e090a0609030206100603020f0403060902120111070b09011e18080a03020a1d0f13020d15180912030b1c05010506090115021b0f030703060f0f0b 70
    0x40d0f0041c04100151003015441c10025059000703d080c8207100e94050301c0203041c0a0510400e0000642001080c1030042c485a44240c8400081da4200c0c0d0f007142c004039401803540085030014000f2206080030b54284400c624404550314024184e285c41520865259902d4503042e500300e50840c00c0000050000700c6106118603101d40001c00d50403004200000f03491403641d01c480b080d40c000e440b40400f0030780204201c104160880101261400603500701062088030000284250500c000d003940b0a050710107001d50b070000d1a905503040844244001c00c8404140464043e150705c0501c02d00d4444002d164040c09075034114012142140d50140000c86054204c03002500a060301007d100d42001040070891811101801c0501c44c09000b403000040604011042c000c1c0e0440581040d40079085038003840b8101a40004d0b03004420409015024041e2042d0000400741c84404084640c03610030302c2d6020040c818142d000c0601138100c544204400081c08000b2025181c2c441c912030b03407055007070305800c07041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 208251025 1250 208249775 208249799
    0x30c01031109090702160501090503031605100f020405090a15140d0f1109010e090304030303020901030b060a0908100608030702040506012d090609180b0126040c0b030c04 75
    0x2032140c058541c2e041c50040004a8069a02190040011b1340018140b0030011003420b0840040e10302032034070664035810309021aa90388141c06120b1255520900210207000d424490702d00500c4940d24184107280bc0c0b004598040e4001c0c0c054144920115404520032500e07500c6010361240c0740d0900c180301c2c1c510345001c0c540f00c00035010301c1c07641110781c107644140003a41d18941c681c056807041e40e19000c444074a405018208405030032000380e444c8400c00344419900004103542c1100d505242c0981d41d07045c2040101c0240040c185442d80101d0301282c0c0e0f01406420202c850300741d82c1400115004141c08204000907261284142c44403504200190005410140c000d02d51240040c10a102901e2890207014120380b003130444540e50030a0381c000300d1030203503018100000801c028a4084480c50801e45001407102c1c8919030340c10000d60303405010030a030340074a06480c0c0e103d00c660080c011002e02440000c8900d101202c0c200c03030003000440041142040c4800307503400b9126103080141040e0609c05d220b010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 208252275 1250 208251025 208251041
    0x20a080411040204270c030c05030c0304020f10020f0c0301050c041202190f030507050105033c0114150a0507030c0f0506100312090501021c03110307031d0606030c0103 74
    0xda020000883c0c00c80d0001000e42070440014200c0750174003031840c1441c08a43c8458007035070426081c0400c5a91840c1e00c001940e800031170008410f0ba0b40c0d100d41c80001c640000170080d50745c0140000106203d016004900c0c0000c51940034296007083c02c00134105801c07035804031580e9200740c5040c4002d02407403c4541b82e18503454800352110701c1c60b42c6141c039000c01c11072141e030040c541c0c2c0800b0031b000d208011086c014100200003c4c200941581414000211040300c10070002d040c424000d0076001640c0c410000300c0401102c44601c0b009503586076890301681c0d0b00c840c25058081d50810002507042c280c2c200458200030b8150307a505040690960307044980b16080d150070750f0282c400700d1071240400c07001e00c056030140740e040c45000d41040c954503240260440c944660801d11002c5c2d001003005903000308216010458042a03105400b243c040d0a8000303160304059420b207a02e01104104429400d41e00c1400c1304c1da4081100f8a074000742021460740c1d20811155103416070840c003088211035009801c1610 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 208253525 1250 208252275 208252279
    0x70908060a2301120201180509160210090303060521100c0c0c0e010303032a080c070c03110f030a030504260a0605060901080f0c10030603020d030918020a080411 71
    0x82000d442c400b511003150a8000301c015070501258501103681241042014450076108100c17654940340019018050003001c040c507840e40d44d038a01954030302c24070040600101c205020410000b07a0708008000700303418050107010b03145501208000c0d41c1800b40c80c148000100000780012003190310050040c3c28012061428814841c0c00d042c0046d540325003100117001c00d40c4907000345603d181001000c0d14801060700d03240e000707680c41c84071070b01047c003c1d00400c03600c240c10580a60f40741c20141c20720394841d0a00c042c003004d6a6480100420260b01c104031101c80380dca62a914881c052001c140d2514002c080040218074104000c120348c001c680100c54008884a4083d01f05580007060390741032072200c1c0d03000c65056641d002000b800d4504071102d540901201d10041c0383da40b80806805959120a00243c8d10500c12441403070f1105109130000000b940e0301400840d0703e1845850090704240c2a801a100c2004c0f107034602c0080b21009100381d40d0150044e59403c01076448039211540e800c85440c801d40e03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 208254775 1250 208253525 208253561
    0xe060c070309051008160c120f02030d0e012309100b0a0306020a0f02010e01151202040b060c0a030329010503040302010e01020f0405010e06131e0e04080c06070908060a 74
    0x32039079a030b40751091480c4e005864180ca5464460007410b058000003c040043c801c0c00d00c44100400c0103506000058012400c00c50065a10104c0c00d0f440d6000301b003a00c030103140c20800610581c10064002c1c01d19209817215602a09003500000101403004442d080801c0e030050300100b90110a580040c491214080c005898954407601c928090ba40304401240c0418a41202448543d0342445000c240c915007400821003210820702d9070b00ea1030394602c01c000741d1079218401a4195520b41d4840303000d00d0401003003140d03600c4400b04c1e45612820564025004689010703210038100740001900e01c03040884403160300c40d02181200648051304040e10a5045644c0c5030740040404009100801038940d045221584881c5002d00042004042100c040d00a045c10700030301407009180382c4d60100b5980800c01d41c003820480c1c041c0303100389181642c1c8a514004000810321040c4407400f001092140e03000e400b6101c031a03552050070340d0004403d10840300c050348800300040c4510026440210f14201c180c41c24 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 208256025 1250 208254775 208254779
    0xe0607030908100506100c030f120b03031b070e1302010503041128061403060d081c09022d06030a0b0904080a0306080601140d03051c090b09010e060c070309 69
    0x10b00c3c0c09078a01060207001c2c1d445051240918040380108104c3e81c2078680350354800034942c0c3c02444aa0301892840c103001140e1315280400500d0b41082400200190403251503c0242040b038616010b4403c65528a00804902264010040c07908c00d00ca035641400e40c04104440742d004495960004100717681d004c145404483d00b0f170f80c0c0d24081742d441f19050714400c2a0300300c418540b110318640d50f502250610413840c00d00c80c00d00329036000381c95203e2021a00300b040340d5940c1c100b40c0d2141c800d074a548902c281d0340405003606404280c0c009503042d8000d903000c4500d484010541c6c0e03400c40c021900c3d40d00d00404120f03500510701d000c2008607403190004c1d0002c99041105404501c40d2a4103403030485032640c0c00320b0f01c1410603a141c40b40d94002d1082d40000c06803940b40030094254041b95042c4640070f803040064080c00d1602a60031240940511264007803030324040d4800744010304007480101e5aa142c00e101040341c105050140401394000c0c80060242078891319102d40042d400304500f2400c0c04128000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 208257275 1250 208256025 208256039
    0xb0703020f0d0f0b22050903070503040f241b020a08011415030303070c1b18020c1c0207051306050901030305070c1a030a051f08031305040605010e06070309 69
    0x5802402215503001c141c2194224a43c000d5902c4041944e016104841182451450341d0358100d40b2403c44c03a0001030b8546070344072082e081d841450806040d5110004e00002e111807002c512004540f4080007401216010a0700b288403280078042d9080024001d100c031020041008041c0f1031624401400f2580582e92040f0300b600355213203018503200d08a0800200001200c4007440301d0842c080807000b451031481c08210140c407686105034080c004000100030841c80c07031001c04004000e01150740c07184081c021845c0d80c80000e9481a40411154001c80d84050010380080341128034851403a000707841d01c141002c0c18008068445440c2101c600c1e10703103000283e503881d201e0785180030758000e81c2c8469960100f03003040405c480483d40091514a20b6030036101d100030300c80044e203070045615100800d440d1180f103005c030020001800141c104004418000500306000801021034580c1d12a00d02c082541e00c074200b0084900510030340d4003041c418144000c00d89052001490745034400d0801e914915200c803c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 208258525 1250 208257275 208257277
    0x7110708010204050a0902071212020903031306120e0c040c0e040203040c0e0108060903030a020c030c010c02030a120213030f050f06040f0c050603090a02060901021203130b07020703030c0b0703020f 87
    0xc089001a54001024012410001c8503840038002e003641c02d61806d802651003215000050010001704000d901038004d1150341d0b901221405240201100e4031b681103100039900c5402d90f0302c200d40205142d492994105522800380c4000c003525030019204100d03400c0288006010b0040d26030b020002001c204103629560743c8040c5004034080c2000302242820010000b82400701a08642001e521400422211200000c00c80b9800f8405803800f40e291200d9010301483d43c0901d981c0140d680d400c2400c90101560300101500c406c00b83d5135140011704088007072100403407042134030040a01a19010900103d940b682c001e946580c45103049031200d0036099011070030300304e0640341117611290710303414441072000111801c1701402080741c07484d01c2c42c101403000954503198140000e02a001c08121003505a000307000c8403407402202a8255528504001d2806941c1008041140e10640c148041a1141d100141110a4135416100c600d400102d039201c2d0b00380721100904440030140c0800201640f226940 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 208259775 1250 208258525 208258529
    0x903050106030b0f180604020607020a030503280c020306040b0405031201060e0a0e07050306190b1c0f15030b0c0405100e040b091b030c09040504050f0f0706080c03071107 75
    0x340020300c4c00c0a091a005010000c0c003403401007010340460b07890826000c14016003290f81210160b598942074400325040709520b6201404901011441c0b40c0c0119103100001216040b180c0805100b01d003c26060b00c0100d111074001e50981e12050020300011141e01180d07030002d028908a1b4140904c40000d04e140b02000d0f0400c2000500198001c602428541d510101920303008105d45824078049200810300e000c02000a840f07800610f0b0b401510284103222007000e441000040d86c8d50320644043c030000e20050501c9a210145007510203445403209101d22003512290f003500145451558548820340b100150000300e2041081100140503624410781c0c2145400984540c60103c1000c802c0004031880400c1031030050801f00c04000010b400c014108044007818000c00b038583d150140e016885000b03660009420614040500c024400c00140308402d042402048070f980b00281c00340300b42c8131081c1d0310545000c900c1c9400400c1003400342101941d8094094509442d018079501c140c01c0c5003503015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 208261025 1250 208259775 208259783
    0x106110a0201033b071a0a0513050402180a05030313050d03020312070801080124150e0a060315061d011b0b01030605180309131e0603060b1309150c090305010603 71
    0x40c3e40c1d1010062101e030005014144100c101c010394507900d1422849847c15100c02c220b400076842c9001018856044007511010f0710440d111040080c0c1d0900500507103504c24891069444006514a000421105c2c9000c40c9446038902d18035181c24001e010400340000c07020b6000620000c2009650611214410403481d55034000d95450b20300500d007180d00305501405800504828100105a10703c818001c540000000c0c0324080100c1070b0807215403064400381c43c3e0040c1090b4000407000c2c4d06070071110701d00e51890310800c0760542e030f1101500e562681a000c070b000340c00320312160616580940c0500d804914103000c201100945682e802c141e0348001d030012a089030b40c850500142100540c8010030b1144820015440c1c066440c0019003244681b0001155054031030381d880384800d400201500394034441d0342c82072008503120b04e85200030300761700c03c1c419000c0d508400800078a04c3c0c0500421280c00c0c3c001c1d690300210708010b1020405000210b0a250500036800c1c2d0000000703c00b4841c0200541c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 208262275 1250 208261025 208261121
    0x2405032d010c0903150903080c0a090911190504060e04110c010509011a100905100e03030c070503010b010504030b04020d020105160302030405031209011707020703021e090106110a020103 82
    0x843c5400000d1454151401307034140e01e03224502c0c002030340123a005134101c12044101c6032600e00300304044030618070a8010703401c05410000e45014030301e07810f03001e40030101d5000d00ba001408181d520440741801103126000005405010410880c00c2c40d07413020700d01180c5030040b546000c1c03440c10318509644041c0d8504181d690b55604407911512400c0000e9801e10707089400e83c103001e581083c028501c0d41d80b0b001d214882c03c5200401001e06010b04000100c111000c0c05981d140c460b41c039001929a5002c0c801d95000354200802c00640e03610400450341541d0b800038060900e80c40b2030302881349106491030101d05118081090808030046051845407152080d4011130b5101d09003c285401c11424400341d2108001c14045941c180c3e070013191641c5544020000d1000d0790ba10300104a140005952019400c07143c4e650f10302c000025210881e0044d41800e40c3d1140d90b50340d0f0b07940d04464100030f10681903000c0d00184a2030300107600ca50064558442c254203801d4804420032032101e00001c02c0707150078003041c2d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 208263525 1250 208262275 208262279
    0x302090403051b0d0207180f0c05030709060e0105030a0f0e060a090510061523040e07110604022d06030f06090a1413031107092405032d010c09 63
    0x1603015581d0f84044220f00c06401c00b40d2a018002c3c1d0b6403440b0f80101900443c030b1280c13945210900794844102c41a0b480c07800d10810000302c8014005900603034448000032641100403440c0d40c014000d600300010306030341d1680355659804041004040401c3c805008580740d0101511090701040242c0c0a0f203c4d40c0790025601505151891400c052044403900c4d1500f030000800c180d40840c0540c808910007814000d03602601310020451580111040021250700450089120751804034442d1280c110303920307180c1104401202503582c4202c12240254003200e2151150030240803800311400c02e0485036100100300c5480d01c0018903503082142c8405500541c0d4042060300e00c1d20401081e005240102c0400c0030304889001c4002120703004280500c0f001503424240102351280481003601d0001e0360580701d8550300d840720a4041c010740079588588140452541c90081502220003089580040c020281c00309420358210380f482003c041e040d42c1050119071515a80401c1c002c0046180da183d0390903000c0c074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 208264775 1250 208263525 208263547
    0x221250908070806040b070302130b0a0e0a050f13020d06080105010305010c020d0807090905130203060f09011a0a090b21251809050c0a0303020c030c150f0c0304030209040305 77
    0x90b20750340c043c58181e0700040500010880754403100c0c0c3c0208403440d0140e613885484075807000c501445d40c03000650360800500411003d5029201010f455000ca0301e4010281d52030742082814160f410031a035125080551014054205078010240741c94402c1012400700d030703549151402c480b400d03402500c26035120340125450680c18490ba12072201d9030b0a10203241c1c00c14000003004040e060240d0800c40b5a18000300b01c20000718100703108155070027002c0301d00c1c618140c0396100c8604400ea610030455820900c4844800c1c022145640a141000d41039418007450540210040e0405419540d00b0590a0307100f610814003000c802200c40d006000200b03280c00500c81010010300e01e944440c400d60141501c1441482d42904228810004018010a002c4400c0c109141001e1000788040c0d4003c58101d0008101500410f902034840c5046041c1ca262920030411710a0220102212909405080140341c03098060840541071f01c001c940110b0f8142034495000c0703004050183d0b016400705201043c02c110786 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 208266025 1250 208264775 208264783
    0xa060503090f060f0703020a02070e0c0c070b0a0e0405150303030c070312050103112404150e090601020c0d0f0807060605030606040605152503030209090702010221250908 75
    0x610245000306044d1034281000d0140720405840c800801d5000225114501c0c404c0103c800034040c2c4820f034441030304101c0110300c030f25070010f02840060b005840e8002008441174080e22513000c1c0980341d500410010104210040400800c9030341e00c5510365078005500d482c1000514466040e20030078665560f00d030304016141c801d0000340e2004060914005000141e50354080d040840403c0c0d410030182030100704c401101e81c644c128101d94004021a0001e1100140800c000301001d040c2c44004420000c2810702101080480d8000e0241c0d20500c444005070821030303110f001042c0580c0389001019040d503109000c40d48842415910952a08020f10452070140320081c1c028500301d800300480d0380303000702099581000340f05000e141c2c840400c080344240411105407558901c02201003000199a00d8003500139001138616a0140c2c103000300203030005005108540c01549190440c1e146050004520500140010003104640c02210200a03100300440313600c00240f1041d85607581e0260419054520f4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 208267275 1250 208266025 208266043
    0x604240308120907060f0804060212160306090b1f050d0e010218090601140901020a02060c0303010f0e010e0c09150d06170a0317060d0b04030c15051905150a06050309 73
    0x3138000341c1d010004943c0042004081d01d040382800440e5a4403070501800038060449210842440a0104181910064102210900300b505d00f00074807070710b0316084000c030340804d6600c3d5000203e10251444005081d410300d607102d0040e25090340b41c81200c031300b44001d03281e810344219200c3e0b40200d10b0105600c0955210f4013900020346078050503107040b000007003100c0d02c0d00400c00c00d99040001c91142591091100303010b0107801070a6250768441114145559910034400e0301010200050041488030028001604940c070108421070603844180d01d03a10140d00c6400301585c0425114070700000f8103102c001604881c507005100064042c030303000b151100b002c44950708403081d4011102450000c0d42000c2c0280603c0c9403484510040d64a05000c03800004102c9005810340499000304820942c0c82032450290f1071207a01d0503c54186495a0a82a0b444c280d40c00d954611010907000390359000c60f406240c0c80b15200441411020902c0b01046004806030440c10000d0b80000410440d43c0c0c1c02c00461070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 208268525 1250 208267275 208267291
    0x10140109020c0a030309060b0a18050a020a020a08132601051501020d0e06130326160206090f06040f0608100f051c0602040611010b090708060424030812 67
    0x21601d003900301c1c401e0b2030302010b40f00101415a5604d0540c1405000e0b4489000e99034080c0089140f1604c440c08019108002902c50f00c61506045c00241004c51074000d8420440e043d070000c0a031844140c0e11495a0340040f2103003000c140013414002a40542c0c882203164405080c1541e1503d186560342080c00d5507001040c44100c420720700d081040741c0c1da0005010805d03c0c0141740139080040c2e00c0c070000d201881407881004100c0080c100110a1012488195610b02c1134140c0580046c28102c0d911525030066161158100380b2402c001c5025042080007020009002005081048005000101aa000b5420461000b04401014069550404121600502500e03c010b9602d4503100c0121120140307401001c1c003030540302034100b0b0944412a03440664980c410415034489445100080041441b26040c500313541c20701446c0703405410110001405a13205641e01d0400b5512082844098400d64101c20b004540c0c04c15512492046100103101440c070030380900e5a2aa403241c1d01204402c000741c5016 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 208269775 1250 208268525 208268527
    0x31214040b0d2022080109080a090e070207060f2303010501090902070203060c0715240e07020705041505060409051807121101110f070303030e190219081014010902 72
    0x42c002404804d0303c200b0131101205102c02c182c16410080c801000c1da1004805609080c1600100200e0300050b0048281c40d0340c07075001140d034a4461501d104016a1000c0c05600a11401d00c203691182c05040566103031401c05041e40c4031200960700070164203c20034a101000400148081d60303020380210010200c000701035041c0412034001a4580070003030040001c01c400018224204a0b405400c10050043d00004004080343c10301c880c45c00c0e144805000890a03540c040110b000c250003205d85004102640c01800f0082c141414000180181a80307105040c00c041070005065580000501c0580b00404011409040c000c0700d0701c905891021202001d07822070700b8148641100c8481900c5083d80240803484901034010040e990000024a5142c003800b40340700e008244030340010740c48200d034480d41e0208543c5403000945c503215041c55040d088c000d4022070980002d458000ca00d803040c405848025a003550b55521224a080c02006816061584a019031252205409000e03401001200c10039 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 208271025 1250 208269775 208269821
    0x2105090d0c080409050601170a0b0301050f042006131805090a051f111b0f1c050906040f082a0f0607050705090a0e1c09031214040b0d 59
    0x10440b43e0040c2c3c001d0681042da00c20004401340c0c411000360241c204081c1c41c803510f03814100e215401406d0790034800c03406507007003401107104118241e141c41e1281d60800e954000401c2600300c1c4100d50900d000c50a40d001e07805101c00c114150412480600400d4500701c28011056988507000c162a0000c01ca44140e0700950031400206078040741085865081c0640540d001d01110405d400400e0302040d80491040040f4407031481d540b4020711403039111041000c0341c90302ca048481c1c0359500c0788c2124151390780340f803c2d201c0c6008240c001c02c042d2568482c0149814103140d1101815204090990700c040400c0d446008524107152181681500411032500c1c0101808000000b041400c0500a0a00c1c0100300000d50300060000501550018101c01041d41a04d801d08080c05c0740605080c0040c184640683c1c0e6a40c1c0850308484800950750704280c0380d4400c00c52031504d4a0900c58408444c0c402406088050721403642ca454005001a240110010b030300c43c00550481c0d0200e40101c000704403200c03121402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 208272275 1250 208271025 208271033
    0x3070b01060810091e1a0a06050703020c100c0212150c1c050c0306011803050a0303051009050c0d1a210102070501020409050f0f010e04020607032105090d0c 69
    0x158905440c0903052015264440321803d1514800513030203c110649095002000b001e926401080c040e041060700340941d0701006481c01241002408042d8480c0100c0c60800400740500b024022890189c010740703541191840c007140c44088111060000503c1840d01a021840d200c522030760141182c00003440d2280c039003c2d12040c121800307421a00341000119804540d21f603e62510b004500c8034840505ca542020001420035810641c1c1c0b9501240324000c82c03003616800b401c4084220303600134004007116071141d14150000c10000d81281030203042c191001c9030080c464000ca600400089140a540b41c05d0380b0105070890344442e044000d800d039014054001587c034184000070a05400d000c00c080d0051020602e402445920b400070115400800d00203070803002c640c40703d4455110464800415a614180240884001d001d5a04112544404070740075041103c05041603038464206029031211010080c00c0c003583c80c3c0c0d0300f2a031942e1545c04005440c2414001c1a41852142c1004062080296a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 208273381 1106 208272275 208272293
    0x901170c2b1d0c010e091902090a0b090312040321030609060b130602030405100c05030708030f071e09090e011506120b060304020a03111f0906030501080307 69
    0x100c2c90042c0d5001e001444140440200b4a4004c1d81d101c0c0325000706140341f901c1c03e8003441d500340100300c1a40c85240e110005825075400040c1c0720104282014a4070680e081c0f10414110706020400c001031103103000c001d036000c20502e60902090f9010003100188040da02009800303041c0500000e006448000030305440c10104055000943c60303210030b030303038078480c910800303401483c84480210b00c288100c283d81451441007050780c0c548003c80e02c90021540080d1124800700c05440140464035811010281010302d40c0440c4032810500054082d201e44414488c10700c40741e03150710300901102000c0d440703894240e1005107208040ea41300c220050400c1c528041c00c6682c0b52400b400c3c080246030500c15248251741c0100200b441604559500800c1181c0300a26a0007000505640700f0088024900c0c4018540543e118080303686000e00c024240c03007060b404521590001c10040c1e001c40c015013 = true := by decide +kernel

theorem cover : BRFrame.Cov 208093525 208273381 := by
  have h0 := BRFrame.cov_init 208093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 208093525 ≤ n) (h2 : n < 208273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
