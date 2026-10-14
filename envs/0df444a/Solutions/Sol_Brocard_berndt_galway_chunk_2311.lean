-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2311
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:19:43.448218+00:00
-- url     : https://prove2.me/submissions/13c47d5e-ae6e-47f8-bbe7-9da1531c2543

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 415467625 ≤ n < 415647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 415468875 1250 415467625 415467629
    0x60a08060a0f060812030c0705010e1209030d0f0c11060c120301050901060206010303080c0c1609020705070e19090203030f030907030b091c0f0903140106051e060708030a0e07 77
    0x4035500d08803151802003d1191102800200020700f04403503414558140c20300010b016503890300c500048400402c4001d40c80303c006a004482910a500d05641c4120340d01e07008402002c2c001c0c065083c0b050f454a101c1d030a900c1110b032803503c2d03505400b242601c515440c45145a0110340020b410050814203400030050703121f00408408480d542e80d03041c181031118001e01a4000c50540d0b21400040c00040e40001409a000802c410b4840e01e43c11200d125503c1e022030091194030346102d40e0804118041c0c1ca4000b090994000c4040790302d1240d850900e2202203400319400041c441203001c21041c0003030b664004813441ca00080443e42001c074403003105190f0f40d0061328400d52030f90200d10300304200281c1c0c0e825154000c940030060403030101d40d00d940181000070140c0c81e400700320410140c0c0020780d025110729006140c02420038507080c841c91840900030006409014800c4414000a038215424880c25698491010f0801c0e03007450403030ba948000755000034200542040d03d603040000448010004e100c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 415470125 1250 415468875 415468891
    0x9020a1116080c0301060501080f0912040e1f06140c0312011d01210b0c122e0305120a140a12140420041d0a020a080303010303080f060a0806 62
    0x52003071429001c5403400d9100841103000340d0510711b081225a800c1b461595004030103000510150703031020200303400d0016100810032103010124010070302c2c4040145946c07044020525084184034180e0400c41c061686100d501e000a40e458070402e142c1d9030b64806401c9040703400d8126401d004546040030000748090b0011103240c1c0000040f8500980074020860040070036083c04083c59802c881d803a00da1840e820000342c204c2c9642e102207011116000216030318070340c907400b00c4071290800c1d143c0300072070160401350007654048a4004848028120580000310399004000300301407803481031061050b800405000c070502946404c860340d9007841d1002003c2c0750484e07680f13950003010300e2448101160145198050707150302c0c1c1400c02c80011a42d042c0a038054a00c000c41d4284000180d00150243c20b08402e012607080d8000c2010311049000a12200b08520894034200b889840d1a0310359a6804244000b500141d10381000c89d022107404001c19411a02c00303040300980350341700c6080c2441c1480540e5400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 415471375 1250 415470125 415470163
    0x818210409092a0b03130816060f0b010e030a1209050307030b072003120a0b030d03150b130b0702060f03130218010b0a0302250b0405010c14030109020a11 68
    0x20141ca58443c039145144058658680440e0704141c2e200320ba0703002c0180700102071802e0000007014070001c801580c103142030400000c030150105240c000082c0000b074404d04c505a04000664401e0b41c014409403100760360240c020b100790030f07440c2c03103216003110b50500203c14054a6403000c2600e4170b0520120000d07602605008a441c14404c030300600504000c01201d007550070032101e00c110031070040110303400060101d481030115100c0e81c1b25100102800714415506110b80a040d40740590150801c49513040f03441c50320a6420380d581d603c0b000318884c0124498820180c0e074406d000346072442c005414458000707020b080c2440c6074405403c0103035209448080a618401101000714501150504c03403c84111541036100d51400c0c000c00401d011b24280c2d42e061540205455060f2980e00e04880c08070b1040c91100007039244030742000f100901c0155800d80312942449801000b04c0d0242813989101e20303190101c24996032810000d5002504080025003c00082c801803400503002000481d01c0030380c0300d41d041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 415472625 1250 415471375 415471403
    0x1903050d091202010c120e040509010e2a280b04141f0e010315030b2203020a080a11070b0301061205010e18030403081603081821040909 60
    0x2904000007a0b0000210700460014000140d030700000c6089059402034031b15221084800007a90340d514030000070394005250404102814a054101c004c003201420180c84910004801c0300c1440c062100d841d06581d9402000b8107070340e050001c44068101280c0140340303008041e80c15070604803072195200b822680404a024088000b26024031100a0710403180818505441d131126240c002074544075405000c605036042e003d0340d0003030b000600e0a5560038404c244c055280c0c5000410b8280907100126580c510280220ba151007089015841940680007802c4820156549800c10340c0300c0f145080400c1909203400040003420003042001d800c03401d034856220342c1028001000d07120303030041c00440c0905080c01001007124040700c6580060180120348402c3d00c847c1e0817645540711b158801015030100065840d0119085446081580d12079a546605034845c00d00b00b000d44d89502d8486d030410b81001c004040e02c1032201c0613001d1000204102242000c0d690603010086800d0000192500c5407014a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 415473875 1250 415472625 415472627
    0x20102040e2217070f0c08010506150d02030c0d0f0e060c1c020d0230130203250504090510060e010b0f0a09050607111905030d0e1903050d 61
    0x803107074407521503240010100c1030101203861400c0b5203078015200310a6030005031020380b000401c44074150b4104a1074440584079240c200c0780c20b8440e01c21082107518000100345c917840c1407100041300500d114415810408402c00c600029440905652544002003102c0b00d4980400d011310520242d407840b000a00041481300c050071704000810461190034100400e20781d8032403891034003001c0c80341c0440040e21603055000540007441507000b00c2a04040c02c8070340e95400c403082e202044039400907642c07591142c1c40d50361445003a4160044020343c50307000150601d428400540c1807031040c2c2c07079020800d914266580089822078103002802e03103172500440c0142d61000c5c1c0704d005900c000e04900d580d0000b03a6260402403110307800381414240048400080c6001c115100b210b000c4007170000104040e1b0354555034a8940124100703503105901030303076402c80400040c10000c0001022209d021380a000b14100d8410216503440300045c106500484561072040e41c6958000400041d40c400d01c0203220381025014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 415475125 1250 415473875 415473899
    0x30b060a0315050907140a03032006090d0f022109040b060a0f020f0a020f06030907030804060917120a030b040e101401120201020d030203181204050a0815160207031202010204 77
    0x400b003481d994411b80c103042a110501604200d94051134680e043d4514400f104403600010f51045220703108002c10b11001950208489104c0b00890315400f8180035040000d0761140c0000440000e42d080f24050038401d008010004d2904240042c030020f100100d410000390349400191804002802001307920010b10b0f010030a0202509000004004880d110b90005400c4006070440030300599000c0041920140204030303400285910511003500ca9880d01c600520249541c442e00c0300020380145000c44224000c0307041e501042e04c00490302c0ca0928040c80c1030303000c5c00700c1d000201d40056031803042e92201e5034103000d00100c811141c01e010400710141c011411100c54107030040c00c1815140710091005030303000544c0100401550901580325a14207444411074400c9080701c01d014001c030400855034001a000802c10340d41c04031041e005440c2c03100807107543c4440b01d200000e80480c440e000f14190150303969036640481881c0c41142d84050b16a9240700359407016001c0703600540e4002c2000c4c00309040c060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 415476375 1250 415475125 415475129
    0x102090a091a120a0605010303030c080c03090c041a090103080403020f1905010c03030e0f0a1202031602040b0d0816021c0f030315050a080a05010c0810030b060a0315050907 76
    0x101c41800340d4042d01c4003491101c010312070214401d004001c01500345003800e0007a03041a44d04800c0400c01313076039241030203009416024880350004801c400012410213403202603030f01840340b4074001d140b0101c2e220b007440b000b00890076051310822450414405c00b9136603a02940d01941c85100c00316110761131841840340c901c1c01c040340144a440309882e2600c42c030300e6450744603089170340c02d10f0080c0d400000c0782410350082c0b203002c1c0f91485a0007030310301201c200d07000015522040c0c1d00c07130001c1030031800b84404126141e00801c2c8649070019190340c2d0b00009407809804c041001d134001401e034843c1e07404594a54019901420113010315485440c8041e056240c40202c45403500d0400d0003507821024a40d40d5080101d1040100070145560766844e02d081c0c4286442c0e4101900b070261518841e0b94541c04030a560f28040141120710f907003040c03040d85140303200b40401800713090319000c5013014a0550f540c81c034801c207004180c0d5400541071400000032580c034001c0c020aa1003040030004141c01c1070008541840003c1d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 415477625 1250 415476375 415476389
    0x37020c010b100503040b040f080a020c01020c03070f05010c021f0206010303020f0307020a03060f0902092e0b03060111150408070210030605010813050106090c030b0a0e070f030c0e10020102090a 85
    0x39080b182030b41c1060840c2c0e0f0007540124800c411703603942d2900114001000d1005000c2c14070110b82c1d5043c0a800107200a04940b00b43c00300c401205001d0200b5036924464012561100c2800780104070380c0d401242c100000610081c491501d070b040350b002c60700e00780807402030900061f44840010418141c0500c25500729450000c06140380c41c0702a004551110113a10005114540e16400d610f81d40364030742e000200e119402404000c0030b0800c0360303000c080711209022a031038001c1c41d84c11601c802d807598030194048a444252050441e9208001950078800d041d62049440c09040c03504940e5004009525118620440c035258030703910280180300ea11092800c0b01014140b800c0e5003400640e1b0000301d590760049454540d00e03001c1e40d0b10f141250141040c0c0c1e00c8050031170700301350396104865019040a00b503604151400e10401c1d90b910324484070a84180d07025400b05001c11641007003036100340c10424024040e42803c4c0900300380d620103d0612110041c0c1440140d5003c036035416039141441ca800020405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 415478875 1250 415477625 415477639
    0x1e032a03010608070f050909090709060512060121060c0207061416080c0f1504050607080714030604180b0a0507020a021302130506070b0708180637020c010b 69
    0x1014009840d464002d1301e40700600003090140180c0030721900c1100e140c0d00740508010392900b000140c10b6542c0f016401a60501c0341808404039640c00c2c035500500144c243c5000800e030030313482c0050291200c00a000c0031914100c41081c00c9012038403a00031190103c0c5641c0c0244181842d00070010210000781c50a0b1100705e20801c9071802d00e01c3c1e51b070000126141c03c6166507035514180301d0240e18140c1d050000040341d026070303400812080b50009030300c0d200b10f010341c007038400300e6450b04421540c94000300c03100c03c04517000c0c5809180ca00740c000d014651040f0007400000e0103c244038441042c070011081c00f159008404810000e0750140c602440350001c5046c001440350a07582c0d0300042c01041c06c04212096a94080703480040386601c07415a00c000c00e005422980e5500850400790b680342d408a03030100101d0555800314000b90000b40c03020440308a18400b078250741d1508800c004001000303082c0700b007566544804010240d81c0113014172084da03800800042c2d4540140c0541420f4a91b8000041d204000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 415480125 1250 415478875 415478879
    0x15050f01050906091f0c062306010806030f011a04060f06020703080c0a0b1f06022404210207060207080c061207030603170a030b0901030506040311010603050a060b0f040608070603021e032a0301 85
    0x40c2303841038680c0185003404c01c1e81040c2d03240b0000c070703180102600b41081c40b50309041a0302003078452044815180b00307081d50103200c455103031a00300c410512603210380d40050b0f10482041012440420252140042c0c00050307500c248102e441340d481303ea0059a100300d80e800c60040748619000b05118440c002d15031400603003041090740407403944d401c0b40b400703035400310980100c002800c00c002030b540406286441d05040742c06c03440e5000c000b5a903020328000c18025100f01e070000700c0c400e1030004070040d0000005059a1800c00c2c0c42e000c40c0800e082c042e00f52801d2603110070f0040005040301480890f6000c68000c02c648840c2d103000000c05494102d480c0c3e6020f09000320042c0007151011580e241e02c1509400c0004000b04040e000c1d0b401041d1a5201900c1401840c0c0c2c0c5c20300b08200740d080100046421111401980904400c010440d14180718550059010700800c01c03219029802400b03810140368040d03210f2100d140c4101c542c0f50300c04c0f144440c0003d40c641615007402000200c10b041380e11200f040504642c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 415481375 1250 415480125 415480181
    0x11b0309060c03020f010c020a140102031302100e0307031421030c0c150901020316110c1c0c15020f03120f060d060f15050f01050906091f0c06 63
    0x5000e07409000104002c464a1506250081060000d0150751900070070041030b0141d8001e4544140320b9085910403a403031200e1820307510500a0300c1c0074821080c1e02441400c03145e4200000303000d01042c20720500010000101440d5814064000158011a82c036202d4400c2148050308008011980f80c00e56800c4064071016054040143c9510416a01409680310040d4106c24034100f0b048581d03000040b41201045620310044d00914000d0303029014140744101c00f00c10554041e2001c601701181684841660341103440e22038440c1b0012036103880000707400215500c40ca042c111181c1c101203c01d019000403801459810060f984510300190040d6040142c4200260321440000c0c0c0120f00c1d1070b40a001040c2280d6586c1c2d43d8056042d48071030300300103050324419000050181200081900610740030000341074201540512002c0005075101031412245c0802c00005810640407182c0040703080b0f901c0044a40c00c00c5001e03001406039214178103a0b408915014080da08101c0105030b19913400d5000100384 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 415482625 1250 415481375 415481387
    0x50f0a1b081b04030b0108011b030b01052209020d0603020343150c02011403061518031e010501050117010302040203090c041d06060904080a050703020709020a0e011b03 74
    0x209a00c0c51084051440080040c4614011900094485c140c00b01c0002216501580440400c181c030940c0070000b000c4042043d02110711903008240030890401642554800601034409000c8640c3c0344010580d844030444d10891f00302e080105d910503503d900600039490100f00e200d14030308150400303d0420284d040c0426440040c0d0f103040c041d0030103010200a520000e01056005800e90802c07800840f000088003d1685150b030784c06078041203141d1200c0c4807031140202102d1191401620308100b84562040c4918a0b50100c5001c3c4020481822056040d540a1000c441e000201316011000c0544403010142150010b80c09a414071000304d400242c98000340e81c1d05411241c04690041c3c0b40d50b2a50300c0b540c18561400c548503030291511685000200314841c4d9800046211012a03166946040a214422400359005884e100e010f00014114503c03950003020032a100c1c1c4180e50901e5650303c40749080c1d0300710307100c0c07100410071501c003800c4ca65034032040e013601001307010b1683c850225046d1805048 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 415483875 1250 415482625 415482631
    0x90c0618230d0f051207060b010c1e02030a0b0f0f0a0630060e10140420060706020301180b040b01120c0302040503030c100c050a0e061c050f0a1b08 65
    0x84194a50308003d12946540030075403650031106a5005c074488402e00610340c2e000304400c45206280c080301250302d501c1281c03200400c582c45162103080303801c540880d141c0d8242d072000499140c441c1151000000303080400c2d082c05038900c1601501d0381c3c24800701458a07d40c0040c440b0a88034034142c0d040040749900035001c2c601c1a1038980a841c80482e43c4044254140030301005402c042c200f038442d80ca884000a40c0346c59040020604101908890384500141c039400e0750050401c480d024200016002032130751240301001c00401d594502110303580c840043c3e820981c03114a540e030b04d88448042d04c1d8518007408051850449007040100031100010b07058600711a0184e40f842e60703c40543c06860700030348c115000362200a0441361039200c058a0f641c1d80301d0004600402080c180304640f0090b500800c04d554504415407034a10300c2c40c1d040c1050100035008a0360b84c0d4a40050f00d8221040c1980a2140901903010b100551200e032030701c0c044060554104101451052a00d006104c19543c0c2c4400c9041d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 415485125 1250 415483875 415483879
    0xa11012a06020d06092c0316060b030307051005060103061d1506130b0d06050603100e15040f1b08090705010806030304090c0513050d0803150103090c061823 69
    0x103143c4440301c914000034106500861000b915100e18520040032030481c03190109904241c90401c05035460a940c0c50b03000705c4050040f802d0340c2140e0708001441035000300b0454000541140e08002040d20b807913282040000002d008150303134805210361941d060142030040e080d1014080b554803407000900d101051300030420111960181800b0b101965440c04850341c4001c0a40318220440c4c0b5004e40c00c01a9000c424203e1829140440004581c1040ac3c03d6a00c5a61030f070300150415490300e00e003401c01e510014071103001a80c403060310910300d80c0c1b20b00ca130500c28054104001039408012800c8985e1880241c044401d1102c5542003001e142000914030381980c5003841c00a001340c941a0100b4a1401380d41c0007150810708040324080d00ca5030000240500c01940c8400070202d80da10310030b1201740310001e000a0800041040040c1d0340c2510030709200365004041c500010b00c0e1215441e800101e100503044000001c032421540000740d2481d0b164800641082d180e03082c7d40c8020a0455400030b801811498 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 415486375 1250 415485125 415485127
    0x5150f060906180a151208070305130f0f1706061f0e040207060c02120403050a0209041407030c05010212160318180914010b010906031a030a11012a0602 67
    0x240194032203142c3c56801803031403440b9074442d08109840d0742c0500551002880364100790b10700011a01292000e0300c01d01070300200c00c40e1030910f09171030444a591040d000421003064030840003031040000c030307c0d0000900c1e820f610100c4183c28070684000e0792401d130310503500f954011402c0c4031259440c1c004118903000d00341d101c820700d0a850403060742c886404181660748140f0101e84042481582e41100640b180143c0c01d07901401414000d0a115008502000d40035611040e10b110042c1000d844058109006001803080035005071111031078861160411611611001c40c01c00185d40c0410941c0e40285000e5516400e01401d00a03041c0c0c4507030025070117020003104032550080c072511880300101400c030094142003e00e20708841c171000342c5400c40b0100c0300c030450307440c00f01c0c8904010700c11005e02ca071059603800d003520301d4294214080d00312114410380030703d04550450f034540c0c1d08200300401c41d4412051452004192030000d01a600307034401e03c88054146c40050b10000750300342c070340e4095158895001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 415487625 1250 415486375 415486381
    0x81506010309170a0311030f01050102070503190b0703111b0706030603080f070303021b1f0e031206010e060c01090605060f01020a06020f0706140417090a06030f0b0402070f05150f0609 81
    0x203d01031b02010300709180140c1e0000500c42e2100c3c6036461503044c0d5500380c080b1503039941c1d200141651340c800341d901c0020881804c114000000c00e440604c80e00008207103000301d03070880240f407001c2c901e0f8030007074904403562115141c890b00c0907000d00201e0010f181034207041207694615201c0c600507119121046001d60800a03150003014000d5060b19a0315000005040400d01c91020b0b560f51220010b0070035103031640350100000c0d035080d44d0268202e030f1107500002e0750030504034407000c1303603c7e0801038070070740c1070281c5440180900e465110190038501140400400d40030b21900b00401101c07409003489004001511840402e0f036000204e004030b0036803100006954003910400c40007140a001d0009051030700300710140c4192000a070103640140d0050303c420741c04048444610f0352038841d00641c00d4204101190402c03180e800b0303900001e14003031b00c11000f01e00d401458000404030f1b4413181049801140c400c8078078050120030007004038403003c0040c8079041420120f00c1c0d0b0021500041c0300d64814203d400c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 415488875 1250 415487625 415487627
    0xa1508010b0a0b160b010f0e1b04090e070e16110a020108010b182d030105161b0c060f170f040b1e010b0d0c020a020d0803090313081506010309170a 65
    0x10a200313494210314144070701e50312103c0860110185102c0c104000b03c050000c1207644a10004e103190000b90304181e6850a032030902e495010300070103400c0310800d02541c0400981074900d10000c7d0b22a00c1000840c10407a401e000004d0000810139006140d00e0344030030700c1e040050760002080d0381511010258079440d03000c00401e004440111404040e0840400020f8072142c0f50354480f2104000010a81070b400c419811083c11b088030400c484c18415040d20b080341c80307581ca005200500e004a1a05043e01ca001690340710703400d0802c0e0a0340404000340c1c0c1c0c1c0280b10710007940003d40301c0321404c0588540c0ba4a0030300e000e40b04440349000d04040c2405400d00085003444c8074440340751411005400006400d507940e54285101034000300010a00f1030300300384d81106200d03c04076000101d69801845110003400031303102d06072203401c01060036245110030803095000c0400c80750385c50700500d980e8000300344c0b0680e00c0c16100c1000c0c80c0030f07181505040c107041203280054840410010034109001d44242c0303522030100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 415490125 1250 415488875 415488907
    0x50408060a1e0606050301090b1c060c181d0708070e060d023c0c190c0302090f0915010b1b030409020a0e03010506030d05161a0a1508010b0a0b 63
    0xb00a072091031900100141c2d1940090140d0b04031500380c0d00400002028009205410100c00000242c0030708a00c40d00f80000c03c030781e000e032261350058940303100400c111a05401c1007283d160404003030090481d1b0080c42e14419000b009030300c4062846d21f40040e040211002e02404410701113148030b40d030046a42d08201025030b050310048002c0341c43c040f900d0001420a00300241c41d402078409d006281c01781101e6016401c204488500c13400000801405134000d0301003c05452a820464101d44007400c000003590758001002e0003850250202c2c5001e050020841c1e1a000d645508101c820304048010012103040c4070903144a089109035951101c201d00001e00c4c20b42c400c0d40c100c00c040e2407000c80c006a00940c0092950a00c0c0c40550080002e40c8800f0201940c0e0700c50f00320260001501040680d20501c060307030f0a941c0300f62140424207040c400761703800e885406a01f12510355890366107804180004e010aa400401040305400070000702000401041c29546240121a01100000344c1c00c000812010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 415491375 1250 415490125 415490171
    0x31c120b060d020d02030a06091a0108060a090504030503150a05101b0507180b090105031f0f0f140708040203031605070506040b07031101020f090d03110607030f0c050408060a 77
    0x10b03007195140001584038009400a0f68600900b600d0a00e012521020318424000d040096008528140e0040700046401090040c900350300180d2a210000d0305203401c2c010207004034400c1d102c00f6200d1512102580d00200c6800b02e107881501c170114100020346a00c544080440f946182c80c9188045100d01c0342880320700c0d00c2c002040703031180e14800240d80302203140603072103c0300f296000d1100411031002c111003800c00b0301034598981c00c40c01d413040201070107202034045180a40e60100f00616054010b40c1181ca24071052a8291348920b03200f0f0210a140c2003c90f44803c00d82030400d0307242400e8010036620b01a404a01440100300380d60b80e014040304000c8500244001032055540700d03283c281080d815004410210b0101d003041c29428105075060099540700c0030009030b11810910f40b101006a00c0d2007600c2d0070740900036880055010018240507141c4165019140030890000c2c091400c411503c280e0185420410180700034464564042200d17900700c0c514940c0420b220041c04c0b04443c0544082c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 415492625 1250 415491375 415491397
    0x1801110706020633090702120d051509090a020f0406090509030408060f221401020d1406030703030509090a0e070603060303020c010507050a0303150f1202031c120b06 73
    0xe58001480641c00188588549401541c45260361502d40c8501ca81c00c0c003d0400600100a66540102c0350030320701c881070f51150350f6104581a6501c4030400c110729520920380f40e41169103a0042100349a4681007540507030a041d2001e112515194100b04d48408080304000d1180254001f0340740256602e07017189001c0d01055800f041203080040ca0b4a5907940584210380d0640100000900400c039100d00c40c5120300940c01190b01030407404c00c000da41c06182c15900b25070031411180d184010101c00d1015021500040d08001100325120f4840342d05020001c0031103105e5805810184006a4440242e80700304105488881090302c0e2122044061700003186562040d21032100e000502c0f907455000700c0100d0f4020340903a1070a49084d0011203580c49040c20160103903201003040800607203c0c1c1e019811000d00c5521403c041030325941540e0705807070716a04c55210088181845800e600d0248a015589107075903240c0303c882618090003510000d24081c0c4548890360310710b4401180d40703841c0211f80ba03031300207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 415493875 1250 415492625 415492633
    0x2070609060c0b100b0f0301050f010203070b0f070320030a0f02040b070b040f020d0f0b0906010506040302120f03030a090b0a0b09061302090306040b07020105070801050307350a030f090b180111 85
    0x1a8281b5444560003d10950348548800d203011040c950000c8211031030f42d07170000316420300c40d9144044861064000f803c02010560740b60780404884070f10f40e5010410040d0412027a40e44e0500b0ba02c024180d64404850110b460702c100310030050f15030348000725030f08258000b0b5052810b54450520024038402d136040030350072200d816600410050075044407080184100d076004c032a41c481d841c0307940c6d0700d2500340507503034015104010900c09440c2084c503800c4112000c50407901c00c3c05504821604540055810078001501c0d07640340c80801c6224140940d00c10311121301044051a00000500c0c0180060304c40f50150344610f01c00c460700a0b141e01281c0ca5040d0150031200380342094078000300e00c4072007114690010351810000c07445a500c10350419040f6a4014000d00305181014030402101c1c011240410540e00e4aa040c180343e11a08052644801c09850241c00000d410381005894400200d28407401c01c4801e001c20301c080464001500c03002c400000484500803528801601ca444000d12000c101d489 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 415495125 1250 415493875 415493887
    0xc0d1a040501020717070c0506032203020c03010c110309011b0f0c03112e0306050d0c080c09011d04030309060516091d0105090601021c020d02070609060c0b100b 71
    0x1d0150020101d19109020f00c042e0000c03401200d410034010f540380141100040c0c88100080c0c83d100b00696040050b600c007078500d00141102520058031a41401c4026070040510048589001c0c418080a503896080c00a14201400c0c1c1c0e5545903c02c100e407450500000c05540801540342100c07501d080d0380e10900b45201e1040900740700c0711810952008039042c0311175400b070606905100c0d1081c0d041c13050290307607080710780025030403506014040d5482c0f000700343da55840010143d84100007407035118010118094001e0074100702d02d0900c4400303030846001e0b00c28800100000001c104521002c2c00d410300e14180c80b921280b908030301500c146a000f030001400c10307060094a0485035070400b220100740c1c9910400075516084d003028105200c0c41d07810103800ca00c00401c941d003020024940e00910510541e94801c544200120302c0420b04031014005038440340a51a0701601040038101409940c20407065141c603107503008000e00d40d083c000500b41035400c07021a60480004034a000504900384405890b44 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 415496375 1250 415495125 415495133
    0x6030b0f04170d0e0d031112060f06070303091a0606070b090c0904110f0a0f030204050a020f030f010306050c13090f0f290406120f050a06020d05070e01020f0c0d1a04 73
    0x113803141c1000c4142c024210520001d41c0280b041851010040d000d2905260b0340c451500d800f40402012581c00c0480054080010b50382e1600524885200b92000240d1401500b0429035000440814000750200a01800502c2d61410250350300c19038030460345030069070b540c0d40882c2080c4000701283c0c2c005141c0003e101c200000c0c41d505c50024182586c20319001c0c060082003040500841c1b1890307911014450040c170241c20641c2001e503002404000c0035260424900d03203221298270440c1d0392002c401c2800d00610800100f80501c50708034452039629410304504503010000500c41c0c5c4520f504060b9200c0301d408070b0201c01d8102800c03510000c101081030340c03110400e003018000342c481c0e00e901c2e07460305000007061858940314900c1681e2812440c100035240e681d48004c00d21f5111101510f0320700c00c4440920000b01e160005041c0e1210800c800300c0c4c41d05200c48040c18401140d0324040c199040303503d00c02d09003500042c54485a00c01194584005840c9080600c8803107201d403e0305404462281c2080184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 415497625 1250 415496375 415496381
    0x70b0d09060504081210231903060b1203040b030613180311070e13030305071418040c030c1e050403210e1203030f0a020408010c0f0e0406030b0f04170d 67
    0x5071042640428161b5640100c49a1401d0213000d5000000302245040d0a41d688a1422050f1802c026000e0b890051200c20321043c8403030207900444455448900140c40785c00c11001d4420303188410300c0194180350a06900c1d00751404004e101301d024480c02c0b00d030004000c0303554001d06d0300400d03d4480c02400000500300101240e1030030700b0721440f0b48150880020154100030034188551059121050203081c42d560880c003070b04000d043c040812403a8031161885055400007404040c0440c013641c02000d10650a00042d181115900130a040c90181c06d040b0240e04510743c615500846440d80303400221110003550103004540000d0004501d04811a460042c41403e924100d240c40d202e40300107400031410804516020045102c0d6034005002081003009458407885d00038001c00005824161100c0f082802c640d900b10040c00080d1080700200c185a4221411843c0004103071410303c520b50031034407001110107020b0480400021000001000c1c001e07a502d0298000b01140c5d04669264802c403110f5003e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 415498875 1250 415497625 415497637
    0x181f0804050c0a0602060c130e090304140906010509090903040b0c010f1518020a031d1f1505010c020d06020703020a110117010b03060301151811030702070b0d0906050408 75
    0x5144215001102d0a10b030020545040f1040d0758020112603403180700d000c40a400044407503105803100e0201250058582244a101d504c0c100001e580b0340f0300e060395001001e00142000350180c1d211b081407000c180d138040e0403203c0c048815151401c0c1521001025440c0d4462070344800d503c40d40200e4600398981064101e441c1800030300e001407044c09010507051042402078802c54aa40c41000c141e000c0f46601d5070050282010035050001720040e1036045140e0707114048a0344c403e250480e6400441c2040e075040d0700310103040440010003200301000c01d4103c03803c08038012117040c001c050f181e500031583d411060455950b444501552030b8121480c029660742c04900046408000030365400d0000e5101e01e01801140c603102d940b04501c0d07481c0c013a820410f60b00240440c0e405540f6203040001c018900c1004600400d14049504000030354650030710700f1181c1e0b803800c0c4030010004009000000d580042d8030016201c018548640c3c0b40d095100da1270061400c500e005211034288001c0100f881075140240c08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 415500125 1250 415498875 415498883
    0x1a060f0714060603060412140a03090605280f020f070606051206040206120c0903070e01080d230a050d0501030b040b090303071409060c01050f011403060408181f0804 73
    0x10301e1400001c00c254403500300b20380b0b264050340140c0000d800328051140b82d06000940f820000000313001a031194606030300661492000c00e0302d8503050b804000c0144140d40c2d01400d0502090b06501000f411100010b040340882094542c95044822070601c503641201e00448a58412680e59625840d00c00c001e0060340c030590384034a0383e00c848100402c1d004185544078660040c8034526140700d8658030000c0e44405020444024401e0003600c00341c1d00c0410a80340685401017104899601d8051000d280042a164000402000940b031006640c9462480001021b08007043c2c1d4841e010394000715000e00505980000f5942081d000000b40110140151302031402031000c0041a0f41c4c44c2d060070340d2444213a400b00c002415000391040360b8400c0c14040c0c0200c9200820030741c80c010b040d07038030319080d102c080e02d0b21016100300000412100304441c014400120050313001e00207500c0c00e07440300c0c3c429020310160442c2c100d803035600c1030480b80d42d0b0344481d0a9002030403c6000030f9544e40400141a20f4013118112 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 415501375 1250 415500125 415500143
    0x2072309160e060d0e0f2b02070b0d021908190b0303030a090618050f06180d11030904060e0a0f02090d03030f02040905011d281a060f07 60
    0x444034900709290a003841d000d034950740b80c40c5961500f4080325910a16107018215a10703009034003150380c148640d10550342020300514003084d5245085081c1ca820564607000300c1031240c075500c0c07415000318055040b01d10307803a001c58aa11070000c00002034407403010100c1c6402207412102030902d070000495400741c45208006020021184441411124590002c9906130700a0001441000a41e0418011a8401d0034082003250b03d41654004000148104980c640c0015503540c0c0362070801c120856100c3d00c449802d11043d00c10300da00d00e40301c41c210100c0a04000100714400022a07041080b540d0980014004001003540c4202c1c8120803041540c0050740641086024400203c4d940250790620fa00108180710280507658280c1c0144840d281e4000001e400f03000004d2032400c00c1c45054001c04400310440640c60458501046250005124034000c659030343c08000d9412041441c0c40600c2c4410b0f400041c2d010420b00070300300c40b5041d114801d40c0b25400089030f0016075660340203444810b105404603 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 415502625 1250 415501375 415501381
    0x1302100c110f1c150e031b010c0503010302010f0c17091f0e04181b050312041d09100609060f14130b0a080a030309150c090303080702072309 62
    0x800d10b000b06241a910405140641142074000c40503400b08620a134800c80700e03030b000301c4004000e035401c0610740c8180303030408140160a01c0b10303100300b074085000c550700821040d503030604d000d441400103000107410000c64882e0601c9090041d01a08502d60704492400034296090b490043e15502c0200240c1c01800781c241500756000c80e10f4819070b00300500c2d480c1c041011951105001c001c00001001c3c4440103401c0c190007000c07a07806044205403035800386444075818102812306181002c075503a4080b00060401c03007000081070f06103441100512003051144584c803207400851429404900050003039180c0b00c40060300648035408442101c48449100924559031000c001c07280c2407400171a0b400c41d081e201c40c502201403542c806c0340312104c02054210380a0b29500c19629081c000c14080300880d0759003c40c3c50902c1300a10403030030803102c521800c1c440390107002d40c001d01c2d03210700388001014085108007241c5814020301408018200550406458200703850b510642800d00c0c1406030b004018070404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 415503875 1250 415502625 415502629
    0x2121f060506090a0e101805010801050609010e0c090d02040c0e091b030a02072d111507030f032310090506010c1712011202040c020f0a06051302100c11 67
    0x684403203c00003400d001d0381da0b14055001c1c0c071000f00100200140000090042094107036020032100381501002c0000d0390350b04100c40e0138210303140502403610480c50b2100401861007520300503503003e09480000c540750410b85010602e0900b05d0b9030020340c40b9060800c1c0c241480e41c480541d80001ca070072a0900360b2034480c200c5d500401040c81190303060416042000502e4844540c0041c15001e1107100c0012250400602e41c05001600040042c44880b11503050014816000404506407034115440e80500240080702e80040c440c9101c01070034429080a144c0340b582c00703940204292443c1400d0310380034000f42c6042441880c8102c5210031031001039440400c076801c1510685100b2401a12019100361203901c82014882d8910000c89510b60200301c00c07403010300d0141c43d140c02013042120040c4034007410f02c1080107441500c0c075408215070006065241080000480103c00707500b286000403d6220314100e10074000da05071019402c81903c02034050416440022414503501a1072146080200030003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 415505125 1250 415503875 415503877
    0x60207031206330e091305070e010e0702030405010e0f0103090206030112052a0d0f062c1c2303010803030910060b1c0f060b0409060503010603020a090902121f060506 73
    0xc1820700040d030203404c11030103041424000c0d40080d040c000f071a070704410554a50740792010603004190086940e5004001030a054641c040e0480002d0006d1410103081c400000c20400701170003414410204c11401c5d0001ea4040d5000c0700034185c000c0c0c0721a07625a1144002c900d14210352400315642c2c0b05810103c9080c4c20075100e802000e8a41c03409500c407016104042090759544480181d035143c10350282c00c00054818481d0610316044a01031041d0a60060390b80e0f02078051080c2d000455410424a440d80002e680846680080c1c0f1801c0c0308240e1442d0801d0004003090700800d10804580001c00410910301c0040618814007440c0e0880e24a1010030a1800a41d40d062090503c3d445090040000054200c41c43c03814080d4002800a502548805a9404c0d11426446141507080000d024031250340c03103000340d2002e48030981c0248820380c51540400c420000612603030521a41da000207004568600700507881c80c036210b404076100105145503440c031140200100503103241c58000c0008803418094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 415506375 1250 415505125 415505219
    0x3030905030c0109080a0b04050f0d0309030806041401050103020307020102070c1d101206090f0218060103050709050108041713090b0901050a1508060307080304080f06180a060207031206 82
    0x803021b04043d4105035209016643c0140c000c45140c050b0001c03000307400004000907001c200040e0780c04103100c900d07410007510701040035007214011800c00042d207503030f00381d0107140794119002880c0040e5260f442d980202c0c0280124040200224030000000442d10024550f0041d1107e000342c441c9655211003810075084110b0344035074039180004803812008208154440d600d2540904280e2100c5813003540040c2110400950201d17024442c1010303c001c6503494842ca03076001e901801d10781080b03170070f106c00600811001040202900c07580750304020b04038108000d4504000010007108011a16441000040e140d065503c601440152000051030318141480c00115001c981440d040b02c2c8034804101c030340060040c5404d4052041e540b00003041e0310100010170013881144098200b4425084030075007007079005803030350340341100d030900081003039002240442c2196441040140c2e02e0400785010790701c0312070107260b08070414039100c00055811000b404001300610256410825000e2482018003085021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 415507625 1250 415506375 415506389
    0x90c0c0703030509130c08090d2c0406170714150f03060a0b0c0a061b140a03110a09080d021614011205040f03020f0604021807050903010603030905030c0109 69
    0x8400c0810100340150020106031501900c05400040101410020741e0885041c00740010400d00170400380810622102c2421541d07864040300410052074910650070960107140303280030050101c0c07142e555640e4031a100034011000d100202c502c01c0702d06661140c20a00c0740c800d1420542c14034484a1500142007990302074500c11040c20b2210345078031001560001058560031445011004c140e010580d000307404202d05540040000a1541c681441512402c40f8108a010707080d1070303c00c884580000901d0804600c071601c2503201c205188040b00a007012080151003071500003250920b06074400700c0f10050358070040444101c09250300e400c0740d46200000711141c43c1090070809020004600c0210020f03140c051415288038034442400e00c0c21907005403811100004480390000070150140608035101c0b090001030003681c98030303401140e4541200714400a486941308005402917008006491078190064000c218194517403601501c1440c0300c0c0111442845101502c42c0c1540c41604000300340c9001d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 415508875 1250 415507625 415507633
    0x40c0e100e07030b0306010902031014060d150906080c1f08040206090411040b1801020a08090409140316060f06140409030201020f0f0405041d0a0b1f0801020405090c0c 74
    0x14000d400020104007030400403c0603200d52188800c0da90402005003e000403100041eaa41040340315408104041c1d8041003070340202c0c40c005001030303079981d042d01c4c48840d805d5400300b001d00e0902c1c1d03101c0c280a500c4c0c01c07040060780380840120305400005800301c165402510300b002d00344990448550301019410110001642d050005001030504102a00ba10307900940302003010001c036000c0409540064004003540f00d0041080a0046210805005a076400303001405030640a910b580405114980700540100e03210400d110401450140343c0e541414480280c0c0d0300d901c00c1c481911803084a2280c01c0d41c001e41001801451000c01384203200450310411181d0303440e0b003854014003010385403040040c0d065550034004001803528000041040d41c43c0c52003000d030740310305140402c0700721400e803141905e88250b5440d20007104600002d800c441c8030740040d51401c0c00c0d650003050382003911700303014000280e11f01d01500061800c0150081c0c030a4030341c201e4807810306540d00d903000300444c000e112510400d07600c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 415510125 1250 415508875 415508879
    0xf020d0309081504050111071716080a020d0225030311010608031903050702010203040c0e090c1906110d0f270311040c0e06030c0d02160b040c0e10 65
    0x988414544002031207030a19803203495580180e0360800c1e00181d064072105080404200030814203202e151691141884a2403d110054544541811034a191003030600030014203040f01070140140d490002d644401d44590301e000c1024001d40703e900d0808000c0c0548100303900104a21080190400d210b007030b07840766415807407031074070100c1e40250300c958a00a69581c41c030000c680814140010404000800050012600d6812000b800c607030009040070110b9206200380b03c00036800380c03194011601c03917000c0482c0c0c90f1a034a01190414005440702540540c030040b41d801d009849000301d03011646103458443d910800102d07015141c464001200e000540c142a540c08000c0c0a01402c690860a40b04107128076032404101c0c00d10010182c03c181e03544520f00d81f824809261030301400d01512a189440400d00d8141808600c5500019010303104255002c80d04004400c00e0b0b038141c424039509401c4280f50200b450810700010441518162003444e2000c8020a502d18004080c034001c280554841545034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 415511375 1250 415510125 415510129
    0x30310260d0e1815130c020607111f06140307080d081806070824100509042705060612030a0e0d0803070e0f01020c0303030a05040f0b040804051008040f02 68
    0x82182c18220342c041080207006030004101440d1512540800c0c1c900d00481c2995400c11410007104c0d1102d420860420788440b40140d07012402c2d64000810b8145003008400c482c403c1d9052001c0c0c442c580e00300520305084a1a4144541c01540803695213111002e1411104014940c44100c24000c1714041d03401505501d0350139110320445a8460701049080003950034040e03486050900907148100012044814402c24041200382804442001c1042e0500045800007007044581c4031b015800c00e200010075110107580300ca4001d80002d800e983c0b2020004490002040404460f03400f0955403849560006102c50804449024075110000c004504000742d2107411600c008007040655080b1200700170750000034086402460240460391a401d4004000500b03000030055000001d034119800070940c5c1e201a1004411250071100c3c600005c034644c1c1d200c1c145184c6407000200000e02c4811120200004d2244902c090016242c3c110f81440c00a501004211303154001650060711607929451140018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 415512625 1250 415511375 415511387
    0x705060903030403050a03051201060c0b041211010f02040e0a06030b0f10033002030313030e030a02060703233606130f0e040b0c030c040305030310260d 67
    0x3400c8020101d07850729450fa0b8500781800044070003200030a41c040350750105456421901030250980d8a00913022030840d48510820000203800681140c0c10a00d50700c01040c80340301d0004514103100000d00c500703543d81c1314001c001c1d07000e403140403510240000414500c21a07030240a0442c0e03041f2004500300c0d100c20341b0001c1e980c03001800d540d40c03d035441c40c1c0c00800178001003426564142105003000032000c035800e0b000345001c24501c104c0c0440d0010400c004016aa180000500c660140303804d012910840c800320f842c14403c2c00000e58443c1c400b040e010105548440c102c058984d6070455104d21546c4141c19000c00d0190710001628011494101540c800d160807680d01d10070110445c00314481c0b80b000129249500c0880c5001019031b00351300511a864190703c014001304100160160365107401d03165400040405411440325160000c041440c0000c84001c3d0f901445d049403d580c1d0781d042c09003c12862059501c101004140b0044400444a100710040c03200c0407903c00203030040a01c3c0703010072109 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 415513875 1250 415512625 415512637
    0x3040212010e01091103100b03100b0111030301030807120e0d0308040515040602030a06080a0b012d06020c0f0103090c05010e190803030105040513050a022205091b0d0302070506 78
    0x10790b40e60003050400303250134002c00c0200780c05170a0180640440030301703050400319982c0600c50558209140c400d030f50380300050104940401244000345142c24030004840c4810884080300151102100100034004001c3c010704010f0301c00c40303281c2d01851029105031000c0440203001c5034044060324421010038022012507610920400903503080d46422000b420f06040f00ba1010f6691a9005c070412042081030710640020340031150007480c1c640410ba607004000c0405006140030324488008944414082c500d254070380758806910301ca280354aa00c0001e6403405902c2c1c245104841503146c9502a5000c0d100d10340b020742d0007144006090303003018019900000354038034194004510b02d408580401c107420740100607241a0000d545d4951401040009890004d401c911801001d60304807400603000044541c15207078140d941207080c100f19440078108d40300d0314011304030250a2034100180b21202140620302c0d6804500c0006420007030714144006284402401000750340161000d01c107519103c405828 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 415515125 1250 415513875 415513909
    0xa0503070302040b0a020703020306070306121e05060f070806010507020603070f0e0621060f030703060f02091f0f02010e0d110c040c050a03050a0b06071202150114130c05030402 78
    0x224141c0d1307400c442007003548010444801070304144010300c111f240034040290040001d10b03007441441d08020b603202c00e8020500b002400e440f8980f072044050480c43c054039a40d07075041401d980c141d00d041a82040c54541c100c0303400d230014841100088803903000380d00b5903584030340207442c00742169106a0269416001c1100040c18400114a0140345a89147c01002c05645580000c5a000c0c4034046141c5a5a006880a8401d11465980c6451a140042d080045940100e00400c446605c000100c000781b06240c1001d80000100d6044404201001075070030040810360b841024400901404034201da442e1086074055400c01c00c482d80b013051007281c180024503840c4055840740c160b403000040860744411000c0d000710300082406840160580302e4158060600a000c1c40380c05110700002d145486010402400b040c0110100f503441e620030000c002c1080c1c0c030042444a5075840c1e900009500f0381c0300840341d1260b1030b00642501c0b1441540104441000d468031240e0a40e00d5650030443e01030742c130764420380e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 415516375 1250 415515125 415515127
    0xe1e0705070f02040b1009030507080c102601030f0b0a05100603090206090307060206061903020102030a03021b070b0d0f0204081903021f0c0f0e1513030b04110301060e0108030a0503070302 83
    0x100a07546d802c50b1480781103d16141c5102041c03951420b107045c40110f41c400080c0360803001024589840d4146009100f0446181c0403502110007452107110003024a40d03102c04203107000001c410002021140c0103102d00070f010301640c1c1d645042c0d0502c141d4404640044d40910b01010402070a03011b40c226010301880241020f04244002c5c0c042880d1103501d50009005034003450611a0a040c880019490051034032964500c55040d50000707540c03031203005040340406034001049210040d08510020407481da034015190302075a01d02d04132590390802020140e00c01e1900320070000c0d1030110b10071101180c200c140030709907020200c665215800050b1009400303600804440d001c0b400c0780074600c090b02c12244403001903c0041b91030018040c5254060050611860708404e802940d29000a030031451014405030741c0d92030810880900e40080c40c0d08c01000c058400301031204004101c00c4034926482c0c250000c00a96581d0041403862082c20b106950300c60b00204a43d031429072084c0021540562942005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 415517625 1250 415516375 415516391
    0x5010806100c0816080d05040320030a05090a051f0315140402070203011e0c0207272706051806010605030106081f1d0a020c07050f0f0a0e1e0705070f0204 68
    0x81003142d48960302c5d0b0307840c0d20747d900708010405404c10403030700805010300c645104a100007080250b80f0301c0303855420000c2c018040303501001503840b808207070050140507122280021034410010740b40341800d4100d10100e400c01810b601e4085003040007000711400b100022054828502c1030000035801808180c0c0c06549600100c0f00e0304400d901c41c400100000f44000401014a1a00a04060070381c0c10541181c401c007016000c000d2000c604800c880d0746000c10005941e01810014030003c1c15280840d0b924040c0706038035400740301c8280c4c4018440d0800c0000f41020f88100f00c200c603242c0c6024011170011440910042c04250702c2588174030350006138680b00508401e00107605c84c0801c001540400c01c0c1c9903522880210710906520320b0b40d00000000802c0d4241301c0c520b0100c6844000314055507000d9000c10140d9805070307482c03641c804040c01c000b420351aa103035107814a9116032a42160b1103001000880c1c0c100022440c2403035014031800e0f84d40c0d1203d0801c42c4642d248003400c200881c090764055107542c44 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 415518875 1250 415517625 415517633
    0x50f0c010c061a0402071203230604180507060f020712050d230706020a0e0901060e060a1e02030a020d0804020f010c060e01110316030e06161b080405010806100c0816 73
    0xc00500e405075034924a083e11f80840101540d40200e103910107080c1c423001c4081002070380001c10b40c10100441d000300310018842da20780051014454050003d03c142480016900d80258400703031640344507825205402c1d01c528001c500c5400c0d0100090180c2e21903400740980724460300c0000c141055030400e030050681203c080400c02c1e0051042607429036400507202140d541c00805e590050f44c0107440e64200c070361411101a02d199040c0130124001c007c0051a00303031492003094200d0a00210b904500e40d540c20144c0000d5a070b8000ba50940301602c64003100e00c0ba001e0091050b83e115650003084524140140c500459101f03091003000c44c0d02d6522403141e000400e1080c099903255403218142540c032460103804182040c5070820341c5c40b091500e441c00281c801d0b071012403c0c0341e1114205901c1c082d000c407810340807030f082c10303101d68a42e500da85000c0201041001c2c8000400407034000340d90780665521150100942c1003100000c4002041d0542103030000261504054441880107078010300c1508a5611 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 415520125 1250 415518875 415518877
    0x603030c0a150b01110604021c1a0114190603020d180f020a090b09011a120106020601050405010e0903090d1104091103101419060b0c0a050f0c010c061a0402 69
    0xd00302c0c0d0a4030388190440c0c2030111071141e4030318101d092030200c0f00c00e0b030320100135600e506e800b50010340900d855030703a04070321100200350300d45005a101c0d20390042400d5012034225a41028018000d0442c0e880c51515101d00c1c188000b03140d5040d00441000d00b0720316002c404e0f00298800fa420301281a140c140851901c031b24107130104442406444042c0302c4c0c1e545803041044040032750300006555446d100250101e074650740c5115054851011000c81181e202e4280900a070080e0644003600c100448008100c0c80e0303011800301e048610030341b818011640c03a0040c094415000300d8408480d43d1003030001c2c8547e85003c02050861038014140d4842c1e46100e14007103402e6503905042640e1800c03c42010340103500342080380b0207103901c540604108070b500764030300a40a6080a049000b43ca102d40c03850004803425a80908020000801e0300d980d00c0d0441000070340c03140c100d00340a98103401800f035000880b0402082c00303014510140e4404070320125031b985420013040700080840039003c01184418a544680c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 415521375 1250 415520125 415520143
    0x62d0307030b031002040602071e1509030b06010503060d0f170a0302070302120f0f031009050f0402270105060d1404031107140904060207080903010f0c0212070507030602030603030c 80
    0x641c0c0414035940d04801d15103000c0c1c2c04802e4014840c0b0412007080b800d54082074040030b07907282c40400944039441d00c000c0c09507412075400c0100d070610b6441c05560070759008460501200d2003070300720140303507556640190745030301044440c40d400c202ca068041000035a07245080440f288210b0f0102c200800c9084032400d960070280304080829070006e070303220034160100014502c040001030000c0c0f1f42054114880d1085c05504401860104003001042c02c4500e07107401c81000d00300064080200e80303008075600210300700645059010b100c1070540580c00502c04200242e03900704068250303409910705401d00410f81d0100100810842d5a031030721705136990604290724041d03806a581c018800c6000c800850400280382c0c410003903055088058a840e031034207100300f5880f07904030740016180d900c0d908003002c491040e4040740740c0c0342d46040c00c21109030b1281e6205001c4882141c0c22a02c00c4548640030b00510720a454000d01541d10420081002032aa034008560203c03000e01030300d09204c0f41140780c0c0d29154401d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 415522625 1250 415521375 415521377
    0x61b060e0f0705031605090c16061d010b03120c01061a0405150a0f0302090a09021201031104020a210e0304060504180203060d0303050c31080309062d0307 68
    0x152092441410802ca10405010304030041c04581d100c4420090004219102e0607005000481c00100d031050004c007039550615000710506c0321103e0ba40f9049005061211110303200080204919004038014030886110503402303001054040740d2001420860341148a02041c190740381d00001c80c1c10103469240c0d800070300d00f030509581c88500742400c1208100105221509050341071002810540d8000011520890039041c01030741c5286203004034101800075001909014000250390078440310384a03025048a001d40d0340302100303202d503404000070b92054003181000592039943d240074000e44001100c09842003002c0025601d086040198210381080c1e010501203a000301e02005100c102d00710191061880f05c80031840c520341100090041013400101400300b40e96400001d030440720700c2c82180c60ba10f000984a44602122005004040b60302c0407100800c5a001d400006d00004000195000440000c0c103a604003141686000e540c000064000c0180700c108004410f0b49218620045008420b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 415523875 1250 415522625 415522633
    0x307030605041202281a2a03060d0311010b21071a070605090709360b04260f030f370e01020408210c07061b060e 50
    0x210b420079203110350400c0390783c0c2e0a42d00400780074a00c40010450030b86a00740c007041c3c0010351603458180300320b160726046680015507040c2d009010030504030502c0019a00392140510000d050b44066940c4140401d640d0540c12000540132400002d014400c3c0c0d500040011000042948188c070004800f00f1100c80c20070440400d5080740601d01720281b103074101801d003a0940c01041d44100c14141c040c0d22070148054841542c40e004142c1200003885104000c0400080c240801c000c003c01c464032014482540c00c21011038400e02d90702250303065041c0340003c0d4004940c010650780380d48414015800140e021507103075040c0da054800d5415564080c056120007060f84a481e8a003486683e10000000742c80d1080042c0103146111107154200d03a040002000b0482511030080c4180d0141c0142c0f540d000400f485500104021032284070029603101035058003c441c4900f244a586030105070310607492802c5042d0481601400902e0041c041c0301c4001c083c00100504030b0844d41c440d1422651000301c01d16040e00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 415525125 1250 415523875 415523881
    0x70b0d1a060304060c09080303101206090c26010605030d0f0c08040f090b04020909180a02150c06010b030c0d0209010905120c030d3213150212090d0201030f02090307030605 76
    0xf60209241c001f8240da80021842c50411380100b492560301c038130a48526500b0014140204000c035082408019070003200000d400342c40d042c40c002c080d454001d095410500700c150700340005205010711000c0b928090003400c011084054100c841341340c40002d001c203000f80c0c5c0300b0390030009462900030001080440180da80700303820b062050040c2c41d2124011440342c0d00600c078141c100d03581d400c00e054001c064401002510b120031618582420b20000010303603c9024081c540f0002c003500c1d002020100401c9003a182c19a881d034070249441c0c00113a035130002030b031000e00c50b0041078030340c560080c640e00e80141840d0b0b00d110745c1e4400154440100145c10308c29904200e803801d6a60030104904c040300d0300281000407810040c5050a102101c14030300e1494141c9012038000c0b00c5501c0c00d0102c0c0c8800607450706182501d616048031516484d08426000c0040c41030740d9001580c48086001e55840c080002d240c10800d80c2150011405001c29000c443c1c10b0703650030404c00300c544d94104010b030001c0d441210b01064502d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 415526375 1250 415525125 415525127
    0x9060f1b0d030e15061c0b090705090906310809120619090f061d0705090f07030e0c060d090303050a02250f050106120b09070b0d1a060304060c 63
    0x40160303100189400c0050300d03500a03e000c603407408448071a03150251540c0e03641307002403600301524441240f0100c44a4408050190340ca40c968401d400a4040f64045661075090015401b030031a2003c24036000140407440c0412801c0f01c0079122941c80000c445980841140620300303100f400000c031081c03140021034401e00d00305130788605204850f10020300040d251a540e20300c2c96030740d005c005c0002165101407800c10400300303100303424441b078100ca07082100d210b00240c7c0480c034811040c0c40c08818415080e0008030b918010762020f100f1400d030f00c04400c0c0c54039401d400340d0181031aa1a485150300440d040c0d2000d5486000286c120b8108000b400700b0640031904000d411102e0180442c03050b0760040150a4909140310720300c8800e50501c19002002e00701604002c0000c41881c000102554201500000e01882120071620b40f540500c94400840d19540700e2550350380120301c82d10403002d0301400752040740401c2d41e115512a4100d00c40000000540000040c860b500131a801c0b16540d550b20b11142daa0307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 415527625 1250 415526375 415526383
    0x1101200403052a0f010306150801030c0e0912090f15030118020708040e13060504050309040506010c020f0103180b2401020a0503070b130b0405010504060c17060609060f1b 75
    0x4442d906048500c44680410f240f070070071a42c55281c0101620550f200050344207900030782c01000405441c4000c490340040040c8a81001e00c81070340d40705407000f40416038890340361802d40108a0a8024181001c0d0302805807807070f802040fa01507110768626010400d03507c0d03483c201513504014041580e070360f605001400c40200c0106e00c440346001d2050014500103801d12040706c040d60150b5084129a507a842074001c0d0f0f4540c800ba00070140e900301801c4c001000000400303001684400c4500b40070540da1000115100f4a80c80d070080c0d44400507145d5045154040ea00100602ea2103e404114880803a200c0407504e4030213440c00d50074408112400390410159084241c0740000901c0540480540340e120190349000320140030f0110450b000c04560151219420300d00250303440103282c42d492070b05090450081030119010745d01c1a040100403c052882001300000150301180075403002e03214031040c000c0c40c0c0c102c0f07844180c0040c02040001442c485a8000d804501e403c03120140080f007268440c6814 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 415528875 1250 415527625 415527643
    0x2010905010c090b1209010e030c030405030c0607110d06020903010e0a02150313200d0506070e061303080d090602160302100203330907030605090c0301080d110120040305 75
    0x401041030b41c18007118542c03000716840e403484940d006180c2e440d0341b9825401059100074a160500c0006030101c164807000c409081150422002d8403e00002e00f01070150a11030500010200e0b00510300170000c614228040a03d503500800d401410015642e0100b4211800142d000d0b41503031101c0281004c5240070800940c4d810083e0402905505100c14034494100380c0440c01000021300d002c061818030b10300c10b0f0300340301c5d070000905005003200b032030134590344409081e103268002851030b00a074000d500384501121a005551005014003038038540310783e2541c4e040340c00c2101100751500c091202040450028042c00340010300d803000d0504503481e003c3d2402010312401605d46005002f0002d410007e00105064601c61406200420140030b05c170089184017002c1c4180c0c806c400f5800e003c001e551542c8203006880c400e503404155034031901000d10090000744600c0601d07500000a44100612a512950003034503c6400402c01200ca400c61600c660070440c80c00665003070200d010400e1000400000030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 415530125 1250 415528875 415528877
    0xa0803071205240108090a0b040b090f0d05220306090602030f0915130828030b060405060a18030c12030305060f152101080604020a0e0c03010302010c02180702010905010c 75
    0x1c450000714142c0b07180f030081c0d100740d0740c1403085040002d59828010b02080c4040c0354001e840800b107103030502d0103203c03091081c1e59101080c4070710444d407000888001040720b016445501c840b410704080c146100c4100740c01c0c2c0c051400c0398100f14000800208036025190302203110b06005a201c1c40d20f00c1001443d00001410682c00d03600584100b0200702111400642001d449041c1d5609151581060f104c14410a814006000000540b401808405c4d442d90140522035a07014020141c1c3c81e42004903074080c0b4000c1c554009800c1000000450155028078890000715403103500160b52a182c400c0d4501565002c1c0e482e001004d0001c80425a061040ea42c2c000c00c2168411501c4000602052041c00c0000601940303442c0068a000d0943c08110747d1a0b004a81c0d100c5400590303154142503480f1602940d00700d004065200b00070070000550b01d181e910541c41040102d05680c40c5800445680084d40416a08071907400040710f003803034180140d00e21582c5150000b00340320040d49070003421900c11140e00c030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 415531375 1250 415530125 415530151
    0x30601060e04020f0f0a020f0705100816090f0305010506030706080103150b030f0d09080d03060821040911030f180304050108061c05070303090801050601050306040207050a0803071205 81
    0x40001908003880e41c68640d000c1c1c1c1c006884007518001c000c10741c0314500d0044c1e080030b0041012048241c0c00140740520f01400c3c400d50b1061076480050106820060100101041e8043c0000743c40c00c0500000740c000030f18515007043c80075514000c001c1009990b401c291240c6e5124404c00c54103050030403901c0010074161404826562451703c464401840b142c10b0040f00c1c0ba15207103070003916a005c00c8080028070b4070340c0540d0194550000c024100c84020f02c99103280f8020042a80c0e0058060301c80c1604075007604000d0600001459103005800458034410b4612000504c000b080ca4281881524800d510940001e0b550341040540c081c441d10300202001450000d214000e0924040070065408980084c2030110b03d5451700000106040700d40c200d205400790035403914a01f402000250101224003a803100304040d51582104c42c20380b00b0840c0c07030034049282040400d0741c43c1003a82c01000f006001e0310646229031000e40d290400ca40c4241e0b1210005101401c0c101c124181a1151075041150000341c9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 415532625 1250 415531375 415531379
    0x10e01050a0f020a02042306060732010906020a0809010b0312090a09090602040e1006170405010213080610170a0303110c03070308040b01050306040f08030a0e0f0714030601 76
    0xc215100e600050710030081014800d80101c1d0082041040c4a0390042044c4120001c1c417448034022001c407031011400c814440040342c0c1a0504c4800c4030240c80d005903202034862881c840c410000100d081c00040d041c1c80301a050020890f0038807501048901c0b800001d0b0b40e07410002c000800c0d03214040c0001440e40d24002c20f0003501e80d000140c219215820014254803000040c0000740c801045600024042e4102004170302007040e540e0084c410340794261000729507501c80c5081e54161107014042d060200c4c0400040b00e0781c08921100300c0e5170107440354001510b40103001180000303410060f40543c0c429405101485045080c1413031130f00103041c0007080744451003500ca120765035030b1150860250a059498070030b007680074086411074031f0f100c0c07405d01265901d204030301d0010144c080031102600c1208501001061500e00072400b80c0c011a0080603502030b0040d01d85880295a002400c0c80c40b1482c0d8860a20301041c509010660710303150070b4400340c440f25117003e0310300c0100142c150000e40f081e040381c401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 415533875 1250 415532625 415532627
    0xf130e0f100905090f030f040f060c0b0112060b190e0a020f031609050909030a030b150d11130f151107060507030314040b16050a020a06091109010803040f05010e01 72
    0x1c0204a6910110100b159240c92100030f0030110034001d07640840c000014100609641d42009004450200c4c64404809903039031002c8500e294807900c000c000c0324140d00104011410002c41200241c0541c0001407108500c00014041c0d000d184030811000000250820591181840d60795002c0400d6005616005505555160a102c001c009030740c1c107400a040c3c03014451003150b414001d400042c1c11403c080c2817102c82030b59207800c4803803d2000241003540000c018103000510507003ca0102c2c2004d030804140519800142c0f4403803c0758401a181400008116107116404e080105a809202400d080c1444c1c04001c101141c010006c09110354515644070040000800340d0032a001da1901c44c1c0ca0316a00c0c90201c0140c4160121408070030703141e070f060000748114100c140d4020700d01114030220000450f182900c2e24002c44600a0258001040c1079000c540640c1003400641d20491140c11501501c0001540d841800e8000b06000d41c000308060015a0080b14042c1c00380c6001d00382440705040f4080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 415535125 1250 415533875 415533901
    0xb0301060e070516150603080c0601081b09130605130501050f070c03050703020a0c0906082e0b0f030a0f030f1b021e0d0620161101050f130e0f 63
    0x213014106400d0b032220102405038081000822901d920800c0c41459940e00348a945508124072082c06401441b000042c21000003c1103039804030191910304519a082042046a00c001454650185002e00146001031250f114140c4030b407a0b80c408200d0214002e0500c503084950003040803400d101c0100910110541107c0010a650740c1803030031580d11000da150032030074545021001003a41030340c401c000c901c440543d001032040e10740c200101c80060742841074245090898a00003001c15a84040070094041e554015400c2c0d00d07005030502e010b480c20500824982184000d00359169283c00f60a80c1c10194404000140740341030740351961000030420700b20f12011b15007440091083d40c00310305400047d01011036203131005100418911600c2e2080c20414041d03c0c1d112508000c20321a040700001c681c0d822000e44101c614041f4540310702c0e0015680e0039401b800c11420320f6047c01401d110b5072402080b040001d0402c0383c440310402150a2524400d2a00c44901401c00d4450880f28001c203d489000ba031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 415536375 1250 415535125 415535137
    0x603031116121101020f01090606060f020a0b2202030708030717070c09180b0f0703110c0a1b05090103030309020405010603290f1201060f050108090d0c020112020304060b0301060e0705 81
    0x8800040b0441d880c0c00140c0c9046c2e94441d4090555007460151010b0020704d902030012121503440381e41d0000d0f1828022038031203000d604000c03c00092080030902c05440c4c4840803c101c142011241d240001c1c6800180c90101154415141e581c800a00b107402c1150140002e5225142c2c0d01002e402c00c22159103c07007607054140200c141c20f45c1d850340d07865a111907141d17003108080d030011080384072801c01d290a84060801100c0c1070000c81c0c204152891550588021540304c003105c1400780c00320512707035030724818060a04809040c258526140c0801c441d52a6070403d8000c62003074800249005e00c0348107100c16248142e020505051403c5400d81c104d910348584081d8400310b655509165040c0340c0000760380302c0c0c2905200c40c0c0000e405030310312801083c15405607040e1120188040c0103180d81c1c000450b03030807401303d032502d0203a04510704030140d250150b50400c01a52050400046040b11400c00038101d0b0411941994090b03120f683c00c000600b0284103000140c4004000c3d18501d181015014103244601 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 415537625 1250 415536375 415536383
    0x406020d02160809011707090e060d08040b07110607031b020406080303151c17070309050d120f0c021c1103012f070b0c0d0f060303111612 61
    0x1080c00100c0040d504440d6140c80da5804030900b4401401e05081581102a981d03021544620341c2036072848041728014401c41d4140d0300c210072542070515440700410b000d00215004001104040006200c2c40094405072041c145074070b85401c03240c01c0074103148c101c2011290064004004d0300b004170f03600045442c01c6e121101c1140c100078007a440403400404103507001d912140000303c180940d000540690360803554040740c52908011168022555018802000411850b0344054441c58042c480028040c0e807406805c0594155584801040701e01c01c0480c001c48030354400c480904e0340c1d5500058000c1001c182c5240c4006503105950201d900d1104048103e004442d44800e03940401421001d602c503007039800b0b0024000c01b58004070040b081000108080a0041c91400f485100405e40d0207072021107402a400d09a6510382e950041100c4c0e108481e814240307074851074600d50240c00ea0060100a51003503503922441c00e05202e2850070420045040c04100c18645402c000451162508014440d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 415538875 1250 415537625 415537627
    0x1903020705090705090a06030b01110714011107210c061b060b120327060f0901050a0905120f06070c080904020306061b0a060b040b1309080405130b1f0206040602 71
    0x43e441007903805018008109a01c0464080d01041030b6501d50080b08020300c003a241d0b02413a0810408940e06c80705240035640e0000002d4141c45e44540c850f000d1038240540c800300f41c071489502c0b0144802d542510020082003248078101c20400c0020040742003000304000d250012030f0a1700300311104141110294050442034603814402d2285d502d8035840503440c02ea5800704e0ba92050140c07000e51502c00100b450280300e4076400c2d034035a02400c0040468003143c0c00004500d281051003401036402d500122241400c0000300c14000c203113a02c61003003052010078240700400c0c00e00740f44945507281c41c42c0240100204401012510006100c200540e05142c0040702d001da1030350746400c0402c0c014003803034003401039806940c0b0690468100118002c4030141c00b600007848440c81728410b020030b866220b03402e01d07005080900140c1904c032441d401100c0b090b201d40c0c2000e14055440300055417102440000e00c40c816035406542e400c40c80c081c18040202c5c0c0400b80700f10080f4001c803401a45540e801030002e007076590 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 415540125 1250 415538875 415538881
    0xc101b05030408160801150303020a060905100207082d1b1c09030b0a0b09010e090109080a030e0c0a030203030a12110a050901030b0103050c030712020f03070809190302070509 77
    0x4000d00565000d00002401c45513001603841d04258000841e20440c0e8a95103004c8083d0310381c050096100c001d403078040c1c005206032165503440800a11070f01200340c6450041d1118808003182c0c600003042494021150903880342c440e14071000c10f00410080c4c05002070300c503400e94a403040c0180180d0388103540c0c24554000c802d0700704945906000345102800d0680c00f8249203e4607551700100503101381d900903a40c200d45652640e07018011aa40c40d080c02ea88040f807100100b114113100492a82e000d20000300100301503171159102102c40d00300da008000400c0e2950202d4090039001c01c601400304804540700d80740c0300d00c0c41d00440d40f00d00c070346210401000103103c108001c460300750300031042c01c4842d400e0280d0b407000001001819070f0405030000340007908001d005917207513200303008803401b8400601c205891615010030a48010540b400400f10140c1c080c0104070310b43d4a031030040c512956054070b0782c0700c89103007038611a810203020104914a9865000081011a40c0080c4c280203507101500c486029403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 415541375 1250 415540125 415540133
    0x70203070911030106080907050306010302060a02030d110c0c180423030309030310060c020a15030f090809090117030a0e011106070e0907050403030e1507140705030c101b 75
    0x341641d0003800e0710604000349a0141026100110b041722225902e0340c02c1d50f00c40c0c5007000e032106087d101c0d6550550100c40144007510380b07180106445034903801100d21740a00501d1000540e41e122a0740701303203050040382c5955801428003040c1d011209c200c6038803200c0b03070442c2040200d94030054400740410709415545900c0300d0340304444c50031002c1100200c0c1c0d1240b8065a10641c2da034801c07507100d40340e1100000c000400134040c081169026a008004200c01c4c4d04129001e209000701950440415449000c0752141c45060b104109119000e40182545e484c2c1d01300c1800104041a8480072509043c071840b07440383d48011040d46c42580d6145060002101c0300001250700b0072101071804868081e4506101ca21608847c0504c0c840d4016030b6550001ea03208402a2104d000d9484041c2c0031071070303600b080109860041802400e40d40551103442c14601c0c00d44030f41704101c0708070b42082e884e070b031101074248150303d002c10140c149400c04032141e401c21244e0802c000c00418480e003110900c0b000c1c00c01840100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 415542625 1250 415541375 415541383
    0x109030b061909150e15010804050c0a0915050a050d0f02040617150f010f0e09030c0a050a030305010f0f1203110d0e18071707230304031701081002070203 68
    0x2c0c0c4044241092a100c00448005121801d0401310707452041e04002203815a21007168419040c410b9045422040c110040d43c0701c4400034801c0306d481c010340c1c91541c40341c0e603031904140150440c1c00c1c0c005401918000d81e125120543d4003d80c0c41840101010031059494001981c445035000f803100c05001c0c0c00d4808100508841d0304507401040c61080d40c0d10556900140004510340c03d80440e4009444800406c00e4294003030041d02c2003d010b51005001c400001c0415a802401220880385003290f00c03125941000d43e60082154a80c011003948418076915003d0a805002101c41d107060302413a29034101c114420f684602c40c2860040c003410024540101c20b4002c80e20340c041c09442418034254801040b200e00b20b0a4140b042080c6007078680c070400f840500c90321442ca1a201d104140034210314040210000601207010000034002c58904100000b000c01044110a6075190f12414280380180c481c00c040302543c2e8055000b10300412141c640010300c882c40f2126440700681c1d6a482d0300202e03040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 415543875 1250 415542625 415542649
    0xf061f1404060e040b0901030510020c070308041707171009050a020a09021b0604020907110703082212050703150b04050c0702030d180509180f100f0b0109030b06 71
    0x1086201050006070643c02c034240480c10b5104a80c1008420707010000c02190301000e000142141e031104502c141c81401c142d004005542d0781d0401c5958041e43e80e51140d000303900c41d4001c1e802c040d498003028001c1c404100019400b515002030a00e89030b440310030038595110303503410592980d9a1960071396024842d06100030800c0340d40207071500b030a1030f072a00c003104040d5000d052100081882c401c0611107100b0b0119146008a50044c802103090315125811107058031062100180d0f40030307002c0004006202c43e4020001191802c0c4144500c80c0d4402ca000c6c0840303d01c1d40004a00071104415500080000c5880c43c02e80368401060088806200c030400f004143d010001a04146060107201803000e005003c0d00c2c21500c21404c80720000344004048501c801300d10380e00110442e8040c07081c0050301d4404403261b4040c040d0041550a42200b980e04c03881c1001c400c020701c8881c2c0119400301c00c0e45d4994016006c4c40480c040051100c202d0080000340340380541c2c84040c00d104040004070700c1c907548455a00342 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 415545125 1250 415543875 415543907
    0x306010b2b05070e120109110f060f19080117030703210609090b01050a05060f0f070606060e1005040b090f040f0207241a010c06060504061d0f061f 65
    0x20082c83c10280103040b480c1c00d052101d101e20300c0a00e22044e000c405000b55031185500c05005100c45008009101030b0072144517003a58448400e0040c40d00200014000c0c00d4621650ba01c102450440b440018000ca803040c0c0059001440e0071520302e1017180000304440c081a4140ba02041d075545400400c4001c14000300c0c1e8800c410b003800c41c0001c09140c183c00412006008400000f226680c80080024078807861054603040b1209000c03a51031444004003030098881c1a12046203842119902c100445038550070000104d070011502d5180c60800c2126061400c0c4941416450309003003c50700131045c002c46001030b128826440480c0c6068840b070708003c46a00342e4010964440705285441d030b00f007000704104081d2044140907290b010480e24010030210400705034429082074541801120f2154000da42515a00e4982c8400180b507245d920404000f091000c807003001d000307007060842e41c1c0f0400c003410501108400c0b0090085554070f03040702c6808104491324040059115010a50707c00804181c1ca00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 415546375 1250 415545125 415545131
    0x40219030804080703060b04200d1e0f0b120613030507081201081002070c050607081b0d021203160f0c1208010603180f06051302040f1401050306010b2b 67
    0x80c020800041130760a80340f107410103002e0300303203603400380f0084a03031080e10a418008255120142c00604a000701000900e0000101d181c2c0d071440c03034646045514140011a00c1d0750755040e003040f103c562003801c4401d0720844040b0719042d103005103643e80d681c0181048042841850700c08003058061404c484000d84e2001416403142c0301303024952100682441011858060014900226441407084900807036000440e560f1340d80c2450103100d81900000c03003c96600008001400d50052082003420546100360700034142079160440c0241400614101010380103418824028159402c02048203403090b00d26080c001c0003580355040392042c040380800f40c904405442c007002041e41c0300c0001070503140a07840902031280b212030100d43c24215004087c2c0542d07030890701e007400500c140c2c10140d0007124500450710010b03401c1d0006400c581182c0c0500a0540c0c2d52100169060806080320740108412405410f80e585082046009032080d007940c0d942000840c24016000d00007640c81e0745021592003020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 415547625 1250 415546375 415546379
    0x90c03070e150a091a0301030605100302120109020109170c04020a030902180609010b070302150403030204081614060415050d0f051603110405010903110301090f080301170c09040219030804 83
    0x304695407281c00f1000c0050420003010803102c1c28110301616046240b00d000b459a0b1840d102c400080c800a0698030401112140c00409030380c8507400f400700982044000100d140d035610001d03184140c650300c10392210081700c1d00f1782c03058080441c4402441e9400c1c1e0b0301590307070000342d14100e008000010f8000d62141c441040d101443c58130b200745520440f81952a40e0b81c598071036458000f5805030401c0140140d10000c0104d8490a1200c80070750014071a0401600b000c0c0c48031075943c00c100034140d0408240d990000c08005c2c5140160880070800810f9500345e14060421890b0262280950703803d10a000f0005140e6a103090142d101284040d2808410001402c0c0303840100c502c5089600f0b0900081c0c144821070664404490459080b19416158400c00c2495555641d805280508840d903155503200e1840300440c4107800701d1030440e841101e150b50780e0f6061a100d42890411a0400213143d4801d4040c25100d07100c41d0040f0350810340440e5002e6846071441c3d49450807030050340000300821804180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 415548875 1250 415547625 415547659
    0x601052209020f0a0801120b04140c03060a0f2a08100e0403050a020f1501171c0c0201021b01050d0f1503150f0e030301030209180d050901080a050402090c03070e 71
    0x3c0c4c50f0304005680c44c0c1e60580da0360550120701c003030558030140c04120b0074404100000d0308031310b510342192000805c2d103040050003070000b81418002c443c0e8040704d07030f1203040c045541002486020340207040c80520002100c0c012501c41008942440340000f4028018046a00100700d08524001070110380c4203d010f9281c145401482c80d00074007466400740c403d206902c2080000403654103032540e42c0000070344242e07103860845c40c4c010f546c400c0c01e24030a01500c05c500208051b1800c0180742ea00700c0d81c0b21605440d225100080c90308080440404e400c02c0c03002045136845c0e07030000c22074050440f110004280143c50145060040c08400c0700700c4002e0904032800410010310300c4014645003503082c1c0401c400b4600d400138100717454814001240b55002000180010700d0720460a64201440b469692020380380c54004c245488014400d140110f0740214040e0815a8060f901c0c0390303c454006014080340c24585d01103680d03101d02404240c02540702000060683d0320611031200700040044c0384c0f6400d030318007601c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 415550125 1250 415548875 415548877
    0xa030c05042d12110a05121b04020705030309070518010b041a040510081005030312010b03070314040b01050a06050a050a0e03030c190c0b0703080c0a171f05090601052209020f 77
    0x1201078003902c002e40000859240c8030440748120391440e0003510000e505880040381c00c0908204482d804ad0b400e0000e040407800c10005107200c0d0341c6600c01001c00c03d08210400110200c403824410707201a1040040c0003c4034204192012100d40e20700c14054002c400490704094003527a08003c0c0c204040c0c1000030b0400b036005011a01070f070703400d00c3c0310100152540149138582c41403482440f1440240030041105888120040d9407045d542d240010b40744035a0000a03042c0c0d070090b00c080c0c461509a00050141c0d240440c0240300a01107410502e01c0d100c18031034058150b0007003840398400d100c0e01e8403041e107150f18144101d51615032a1000e82c0c451940103500c0b581d02c150f011740191405103245c880405c041001004440300650181c88d1489180e03298215402241e12003048102003000f0342503003c111312001c03165103000780030106512011440b070701e01c0c8448651499001501c01d000100078050241d0f04101160b61080b1064200721207000c80c806881c0910585038400701c880ca100250840d400d07030101c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 415551375 1250 415550125 415550153
    0x5040c050306210307021e040c020a0605090312060f12070f14060403050312100e070e03011808090d0302031606090b010806010b04171e01020a030c05042d12 69
    0x118000c01120f102c00d50030003c1401d00454220b568420803154000d440d01085280280c0720102d11a01c41c40c5038000401d0a481d031804005000d83c0c13000e1340742001c0000c1c0c1d014a5a02c4641c1d2001141084850282c1c10082c000280095020303136220b21800025890310003042004505540459000503680c1c0e080208040c03540c4030b036030300a201452030b01840348ad25070308603011242c004004500b003c1003110701008000006c2c0c104200e000b1524800160319170140d4441e03100b440c403a01c0f425081040ca0003414290f494060b5036180b0304001c0c00112001450100607907103502e03401d0b2040c140da0032003468103a1a501c20341c00c40e04034229038101c940007009801d03000306e8840d500c1401c03400e2090f640ca001c141c1d6101401c1c060480090b00912040c80f40c50104e410100c1e44200e0402125901c0c0d142014100075018003140010140c1d40000d040504250180a1f80e40100762611f081458a0714211000b00036291032843e2080610500c1c041c100b40003110b12410000e040e00c3c030b2610b044002076140c0500f941c8520 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 415552625 1250 415551375 415551379
    0x913210908031806090a0305070e04020a1e0b0f0c01111b070b0a181e0302030c1c151b030c17251407080c280f050705040c050306 57
    0xc4010500c224040282c1d81c443e0038020205080b42c2d000340c1040110380000050a0304140c0c02c0400001141c0104020b000070403003854402e500307080600500c04148c407650013000004661011100d41416800703540340407a0b415040300b5441c2d0180c41149003071849414002240d540c02d01c85480201c0070441c004200c3c03000a02c41c0c0410360041808036980319a00c512507001d1002c0306020384400711380600664002099985080c01401349c490716003440c1c40f4074240005c004d0005041d000d0045080400604980c04811218204603480107800d400301d01400e81801408010404a84110f0a085400011800d078806084036030707943c440d440041c01000d902c5503080010340e140c40052100c00c808040c1900409281600d1210700c0500c40000442524401c101ca0821444001c07540201e8402ca0140052600c81c60151303607120000340c106480c1ca040d484070980e5403d0409040401c44d100d2000454800394400c00c031a0f040003a504105041541584c815a041800c0bd00d2480d9151391100081d40700e4601 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 415553875 1250 415552625 415552637
    0xc03060b0c1e0f06040f08071202030a0f03021305010e0316150306060f0c0633080114130f0309050910050306070f020d120f0e070509130b06091321 65
    0x500c2c000d855460840301071407240c6800c0342000c9400b00700c2c1d00400307001007409412000c0c41c11041e9544c0e401103258118054006800204014104d00e51111006c091001d60380350135402c1407854520b4280e000703aa841101c3c1840400b03114000191003c0c171100c0c0000e056a40a5941940c0e207800c01402c0385400030310360300040e290950100e0313094000d01651400b980d8541e22922580c7c0169981c0000b00980c145016041c4c140b1804060101c0050341d0420b01d100c0d507120101e0380c4618003c450350940c0c280c000d100300d442c00c0e143c007080444480f0390740202e07005402c0b00300880c000d0b18605098810440700d40005410002c1401040741040b90018a04100c3d6400d90441c0c085d999400c104644410800700140010380011220100d11817003140860000c52180c2030020341d031022551301e0012104141d500c0951500710680c100000d242900c80c8541c041c1545680d14680f0089565921202d440208100e02c9035018001081c0320f000c0c1c1c240c03040385860b84400040d5021001c2031400220300e0b4005102000154 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 415555125 1250 415553875 415553923
    0xf0b0a0203010b0702063a0c091518080d0c02130506011409041103091e0609101a060c0729070b0402180c12011203020a02040c03060b0c 60
    0x14900c22030703048500100780030342003441d590700b0400c05e40d01010050f207010500c2000505041c040c110041a49450360700318a108507006448101035500380c0e41480f0074403c010340100b040380d10310666803180c0000ea01d4000828040c40603200f2011f44546c000a1242c0b18402c404c00c0c440b078000b180355005074000c4800c0f0001100400360a0241c0b001101c0541c0040e0802000c503c1ca05840b070090100d1100052002c22076a4030f108450070310340c004940110f000d620091454511680e803004001c91402a1800741c1103d16101e0326540e07030340f40990143d0a0b516510b6080828685110300d0709070b032042004283e1a0f8030b6200344051669003110703025240c5c00780b11200d0796420025241201d084808104100107007403e0306611611068100108260780100e0203a1450000d2000d2424140c0701f04074410702d040d10f60225503440c1c000703500142c110714200008000100c0100e600080c00903112603044030003003030802c0700c46c00840c00707003000d0341c0b0440110001045003110301c1004185d1409001096040720320b445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 415556375 1250 415555125 415555141
    0x2030c090402100309060f0c0203120603070308070803280c080702160909080d1401090b010906090e2a070b130c05130e03030a240627030606030f0b 65
    0x300c829074000b54088907052039200c0f818065004806001c0c05444001030f1f007560340c00c407a002d0780c043c0c810303990058000203416403090440c0d0340b406400030016001801010700355500c0030802d1095160107811a040800002c03003c00648139418002825003050400c05802d00181c400684a05900003004c22240000110510b20006d41d8a0610701840400c2422514004d5210000c1c0213003c010380c0c8560b02000303214840340702e0f800b0340300d44400e001a1360030326503140c0042042260030351070180c0e0401a01480400c10741d82c0c0100c011041e90810b40b00c03000320f80c444404202441d50007004041071248031900c0300f28045800d0024000c507d0188d01c040107183e4682940c9080c210001c4070003408404c005c0c0043c403070780c1040324003040206102c074030004401c00343c80c0f0070034590340040b110f900015850b52481c40d0850110400b0303c40812800c00714425150500102400c5079090402c00c07140c000002c1c20102002c4a030030f03980d41c021034010344c00700304c8103480341001452668005004d8034243c4d03400340410640f03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 415557625 1250 415556375 415556389
    0x50907030510090c030b031e06090d200f100c090503030415052212020a091803180308071203050c0703080c0928050112021e07030207081002030402030c 67
    0x40c0b102c818440c0300e51030404032600024100360894000b0140e503500c81d0aa00d48040000005541034403a1441c8043c400c100401d02c0c11000070b0100400b034221001a045094011000c000d80c0a411901004500740a51001d441c204049070301c0c00951240e84000303250710350103034011502c4001da42e440c011001c0d162000e041d503d1043d80b28808482c8890301401c18010f00c5180584020600c003a00021090f00d03c0c80d2005076070603150042c4c6c224207054803d5100710300d0700700d5070343d4000c0804174000d2020003152030b100080102e408101034180042c41031044014000c0c4014030010707540c01400e02d51a48128144140e00798140d00c14500805d00d03002c0425507402261068038407507603040d0b80d00b9580f83e403841c0316940356800c00442c0c150400c0d0304080d00c12984400e1001d641c24108034045001005184c0303030004080c00b4200004010103803040200c2c0c0842001007402c1c003824103224040030756580040c5000ca24200c0300740c3c031494050192507034420800b503158000314000d9000314116031806040c0401c21080c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 415558875 1250 415557625 415557631
    0xa0e0d0c120e0303070b0c1603120c030c0804020f01030f091a0c03060307060e01030b10020f0c010305010f03020603150d0506010810050c0301180e010c02100f141f030f0c0509070305 80
    0xf03d039009000c0d0b038000a40c1d200517140d00408019501b4102002005c01407000081d81008901040595130300c210000c40d1071203150021700701442e0500102003005009090000081c2002e80144400c924045070340e4065000309c03180c2d0612000c00c020002c0c203410a0b40106800c00d4030101030700302c2c400208090030b400c03505036400703031000402401110b072400b2000e84040ca0060781880c1410b88410303d00d441541e500098840c048601d4000e0000d404c43e1003545070502c540604450705040c6414014420a426541200d040d42e6059944580d6503c502c828207184038217822071141e0058100c4115010804003068203812038040300110b40c217042408003003e040e07842c101c3da0340c0c0c0c507030005100400582c88034502d103908151094a002030b00d259400b41044c02e4940c00305801300960b20040407240364280324030904031007800c803400800c505c40c5013030310040008802410000c0e5007072513030014107924052208104001d40e0301c00b440304e4103d81203151010342e1600c82d1144900c100300f40700c0041c1816000e4040c07188 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 415560125 1250 415558875 415558879
    0x9080d0207021c0210120b030718051014120a0c0308120a050705190e0a0f05010908070f1505040e07090302090f07080c0f130f030c1502060105090a0e0d0c120e 70
    0x280011000201c031b046420400105003039031100e44801054a042c480d0760007404181d26111610050200c03608165030010306021070003246144200f290110903072461070303030b124101e03151030012103422519443c10314281400707000c1040445000042002c000700038024150f10b40300c840c0107540d40f102d2070740803990304458032400f003201000000c140070400d005c1454140b8190510b100704c1c81c0000701160007560903800c111080c0d407c840701401a507030010b0503c1c00070507079080201206400e006207a05114070500c1186491a2100710003101140580169000351007551140301d045c0ca08000000c200324200e02c8240d009020000c04180029415a54103116080d40d4448944545540031078071410b6221440c1c0301801e0f40d080c00803401034601d28170000b00410203191915142d604609221007408000c0e481030310b59210407014183c08507008640c4d541100d104503840036950341c2c0c03030301c01d10003034a5001808841030050714000c01c106a001120907000c01d0080100780c4050311649000d80d0310700748a0100c55 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 415561375 1250 415560125 415560139
    0x6190b1305093405160506070318080d020a02010605100309030e120d12020904020a0c02132306030a06050a0c080606040b04091a031504051005060105040b07020409080d0207021c02 79
    0xf0700c01c00914914885050786030192030182c00c001c2420b040c040f800310446480d000b03035041c4401c1c070750f140c010030310580803501040e02d07c01200d503074040a510902032850306490700401d02c3c01515000394081001000042d02010000f008250014000d0004c04000c501107091404001c019003090018000345c2680071000300003400755203005680070030b00c1d049850840d80d02000b003003400e42c44600103000180415101c0c07040003011881002030880ca19200480703410b28052148103103007404c05586583d400c1480117030500342c0310100882e0a0070f2071500e019181904050500079104800d034440e03c40040c2c5603803052520707125501001b0b460320441c0f00f0000300c000144030031301c00050581e124106000c4814801200d0440103000311742041001980703502c20307880540400045c00818040060000000d5400708480e00e4100c0010b0543e02072409004454800852310100319195a801801032980025a031622081c40700911401395000b035200f00d009000081b50319043d2030740703031507100080e81d8010030b19 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 415562625 1250 415561375 415561441
    0x90806071d0f1504090228020312040507080106030c230603220b093f0d15080d020c04050402030601090b0a0b07050309121506190b130509 61
    0x40070410b103441d07a8650108211400f01c507404400380007400146003d06000d0388075914641800c954413810f540c0710444040c52500340d41c4007030380801190311195080d0b050307100603112820418503040b03190700320581e43c0d80713825030210a00502d581c003401103404501305c0d000720b0083c0121141139010515038581d0445000e0010889075550201882c803000c0f00d441c42489603103455290a1025403040d18a94202d802086a803441400d010306c00c40d420a0b4000200030500c100d20b03400c1d0011000c10443c40c42d10b4840400d03601c490300c115410082809911074192100c0ca51501e800b517440e81c00000ca600054410260140c09034203150003682e11540e0000d002d088030780e00c0c00501c04c024100017070300c441e13001020290104114a40f10301900b180c50165000b9a202c041d0f041c144120080c076100c0601c0310ba03014101c00059191a2004207a1101c81943d03c901c00c2c00291781240c440c1e111a0300000c03e040c20105000064542c1d940c0d5a40859900311004182a100c42c11085026032032109074200c1c0551003003032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 415563875 1250 415562625 415562629
    0xe120f06040b09010209041113060809070e0c16050705010219110405070e0619030f14060d03050409091104060b12161206121101020c03031804060e010303090806071d 73
    0x1501e54000f041c407001600c1d021884c2d000400b140c0d0000b00d02e600d061b0000c94100f90000d00800c3c110041c1c2600e05011038a41401ca20041c2e90744060310416081051802c0001e200b9080002901d00300b02803201080080d44045c981a6180e081c41c1c05043c1c0103110f200c0000e0658124030501e01d09064004190ba40131440010511000c0e1000030091424421011314814050300d61400405003413411202c020301d4076455400080540d51200314545d8680d080001c442e400a41d00700144e80c10520071140030486d524680b4050b0f07070074025503205402c0c861804045006000c00303039212402410b01103508200d2103850715074083c118003407074034800e42070a070301000140c031001076012844102c0c0c00350905d110b40094104001c0140c84d0b690308040a0f010101c0031450802c128400f1000f180720b82400a030100c64030302d01c0420307501e00450030034030b00c2c00c4410000c104860301c2c1d5610500c0900f030418600f0081d5078584c01c029007045890710138101103100301c200003060740d0711806c20340c0b00c42e481480c05184c0c80700c10041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 415565125 1250 415563875 415563893
    0x10201140613240b1201120201050904052707030204051014150c03030c0703021605031b060d090813060e0607020607030e030109050d170f0a15080d0e120f0604 70
    0x160140d4080b4075401d80e683e5100902c03003c0014002e40740e08594450740d0503061081900113a0000903140d031089240d40040c0c0e0000e050303428184c03064400050680d03852030240124144090a28003501400782c441007090400305007603003501c0c0251024821922100c000c0c840400b00fa02c0345a108411342d265202c0385141002c034405020030b80b64400c9050580780a41c4074110f601c203036540a10410001a02010107030140300c05240752040c45070031034003940b81c000800c1e184e07440a00407003149820003031003080d40c0c0d940b0b000791131900e00291000c03c80900306145c0740e045070b40401300380754201401c0c000004040c0c0c800c0007160301359500646403c1c142001da0342404020741103032400700c09004d0311194808880c1c41c00d100c0d003408076004200500e0300c01980c0c40041d10300c1c80940444003c0b40181000c00c003614441c0e00900350232445103480040d8031001d0524003541002e094100ca00303e030081c030038a03290082c3e000308284a004002c84503040800451080c2c10703075840800c02c84d0146904174400003804103007212 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 415566375 1250 415565125 415565141
    0x7111e06070e0105040e04080c031b060628152001050103021c030507021c0f2f0a050d050a020d0308011e0302010e0d050f0a08120105010305070207090915050108030702010201140613 80
    0x122402d0203d1420300301c1cbe9442c504002c064060744079004000c030600d400490007600c2e404100b0448101910041c4904200c2780c280651400880c250303410540c0c00b44100511091070711a9040940c5c0ccc06500380380a4082c010a00c003d030312400791407900c805821a6000c00c5210980d168480602c0c2007919802d00c00c00107145580d001da45114140320300d0101c0d030490202d26485100303540e102d000c0e032803100b5034554120712112a58090640300d0a0501c1a40300e8056110640d40100c1c1c0c0c3c0036445507185016441e0490203040290000c0d50601e040003007581140119050342e41d014000d011a85540e4150030202c4c0b01440080e0010740e21051001040c10001e19116040b4090b4090714454121403020074030742040b00b10304a807100d20002d070350200d07601d6142d082070240c10246005d01c041e00708524003e54402a43c003070842d6569a8104000c2044a080e003d4985079600610600196035107003c2680c40390400d42c2d080e80036509001c05568081c6400c1d184e030380308205c010080c1c0c180e00611400140103242c41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 415567625 1250 415566375 415566397
    0xf090c0311070615030803090f060a0b210304030606060507030215070c0b0a0f020a02032101080607120f05070306051804170a03090609060608120c0607111e06070e0105040e0408 78
    0x1340300840454081d00045105d20a044000c0240c0500500c800f494404e00816030f940c50f03072070114114441d9903021103100340300304010b0b4001d00001515404a0940c031441e40020003040c5041d000140700c0d0307000406404194026020380355109440e103c1e50300e424004803400d030005601c2620041c00a11121626500b2030200c030f2000420203203d1003268100ea12640c4540056070002c2030400c0c60b017041d9080d561800b1494000704004c1d504d80300b0304c580c4e565000381841061001601c8828051800c0d584180031406400b20140014144414060010310440c0070f014010b030a424a121900c400c02540280510b602c40d841c40d81c05a0240f200c90b6140c0c01c098a101c042507128510301d00880d189004403c103680c0a00c40c002040c61909040e545405046080880900c209028104510f034003c03400c16444181d034106804524a4904410700b400e00541c960000b05100303e610350052070000402d54481e48903501c5442c0228400e0f03005480300d014034810701201c406100700060014010401034001c000e05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 415568875 1250 415567625 415567661
    0x5030d110d060e2406040e1815040311030a0f0e01030902220c1b060f06080303072a0206040909080915070c0e0408030f070e0a0f090c03110706 63
    0x503155141c030998480380d00491006070154140320640780d151028400540840b000c01e02080c0800010918a02561107114403c01c100c070000748108003180a0180204010300c2550009000070b40c0003074070200c060780d00343c0010750300355008074003a400081103a9002000c0e4a07013101400d92140b01b00e5049070b1081c8624105510341c51040010784502543d24501e0802c000e0010b0300c0200c41e58004201d420100700e420400600d0542e40b061a211081114034545d00403801161007410013002c0005041154011002c51000004000c0c029520410a2444159203803095070f00000d034910f00c0c0b001803801000a58004802c000801c4042000e03071003c00018882d00480d0300b0301041a000420600903060002884140083c0c01401c00c44000c044002800c00c0d0403103840141042d407100901c034000244904500f011580119640a000c0d403000000801c00a00b43d5290680307648a100181c00c241c450003000b51302345030f1044642ca0190007070307100038012038140c607040810035198407014141641e881c000b4122 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 415570125 1250 415568875 415568887
    0xe13050708100608011a0603011202031912030c020115302301090b15030a02041d0601050a05012a0203011b0810032114040608090708030705030d11 65
    0x8020700a1000003074420030009039803131402d00305501b51502d072861500103070340880004032103680c2c2e50242c5c0d054802c01d0f00f042120200b240301003480d25072038401034060b4040031078460040207440e010913182c04441f0b0f6002d000c0010125800d82c2600e902c0301408d01e1182da8004d05000c120700030065000618255901d90280c00c03030710090a642d0b001c45290070b580c052048910a28038103401448211040c2215000708070038921a01c40702c80c4002c2c007a14030024100d075036446503203940d0108418481242c00400402564030400d44030400306414041980c1540164000000ea51501820a00442d071040c0c543d14108803000d80810040038201246080885500640f20b0168409205410202090121131355400c5c44050002d0304221000f8008040b0300d60541c1c0a00000d44c201079061102c10040072000d0f10b002c41c120b0b050f80e800c43c4400250034100303004540012641d503c01d00c0640654040303010354622980b507042c2c003078891103500c801070b1680d0b2080001c21218410760b4001078104681d01ca003070703003400303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 415571375 1250 415570125 415570139
    0xb0a030b0909070303110c0607030e010e1009170105090c0d0f1203060306050c090a06030506041103090c01200607080403050702041b03051003020108063d1403010e130507 75
    0xb5111542c2e00e500c4580d05004054100040e165990040c6004202c00385034140040d00c81c0c030558400504206110328041c0041e401005000030302400107010f11040d004901c40180b860809114800320000d1041da1049000811300c9003c1c0a00c2204000d80032503220001409003807000e0010803510f1054840c50b1402159808420301040a4540d8010464600c5c0d400c2c54015070364050b05c01c05880c40100a40103203070392800381a500701d403464200401c0a03940d46001a0041081c10511607903060b0000802c102c9020200e0001c0740442c090300e803400c007418801340b4040b40e802d00b078640c82115400400071444050141c5102c03540300e8445e00d045440c111a940c04203083d6030452074070143c66186803082c00005ca40500416500c4100c1d8400f4980c0a85190002814080041c1005005136a8150701d007005480c48000c2c0141944488100c558419100d0f501560807050f002040e8001081c0c121b0b41c40303203250b14404590498000c42d9a0450382e0311440e0a00d0014101a6001c480754440e8600c002414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 415572625 1250 415571375 415571389
    0x2030c121e01020309070609060509040c0509040f0b031c09090f021605060420031f060801060b0403120c0b0a0f0e010e1e0607020d0809030c1605190f0b0a030b 70
    0x24070100c000268a03030409840c840e01e00400c03078004406210289009001040d070010031b850300c40301c1c12100480c46c51840142038075a840f030007403225040f82c10f0940c00c1440c51b40980014840e0341050b4100e40b0520329400816902144035003c4a0019035994030070032100403950085c1040b403c600100520300314508810300fa80400b8510111210b0300002e080005100f00e48a0280d524502100d95400c0c01a4003000661540088002c50b09240c1110742c5401da42819039100c10045c00c81c0d040200700064803140241d00c0b5410a102c11a4145101d08008a840e40f007518842000c982c01001c0350001c0e00c0d810354440c0a4a60a03014404041e070b5a905088009824051040141c0114018100c40002040d560607108075030110022190300031001d2240d10395001502405020191610701d0171500c1710600c050440c846c980c2c1751405413003001300700a40d81d04400200002ca800c01c443c284540100500803100190a5108d140500c64101508000342c1110318010031043d00149400107141d0007020028801d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 415573875 1250 415572625 415572673
    0x3010b0d06081b030f010c020309060c0c0a030b01080d030614010e132409020f04141302030705031801090308010b0a03020408100b09131e060e0d020c0a06090302030c12 74
    0x1003003a0304442401400c06014140c44c440c174044c001d212007421140040e5582c030980035154003410307001681c8e1400748011301c107107072018a00502580ba8141e0b80c1c14004102c85007070140d000070340105284010b10074000c0c030030701c4102d45124040b045c03030720341c0e03400107503040d28142948680002d40010200d01e030355800d200303e09080d8460502502c2602e050010b17126130110070b4100784e08181c0f041000c50079075200801075130101d0300305084c060300c040390304400b040264031070382842180325001005000c41941c00201a43c4103540390103c07072000d150805c81e102d0036201c0344040600420480340c010b0040100e520005c29041c24542005132616550b188242d10b000016119001c155a03250600007071840c0040b06141c0141c1040b4034007941e030b55152203075240c0c8521007010208042d5048400c1040011507005070310b910b07820b80f09440100c4501c0001030344036180c0c6840d261280d00b1010002c00d0700c6000701c00342c8044c0d0340c0181c020404525000c003403000284540c0183e011610555500101d0b0310704010f00000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 415575125 1250 415573875 415573903
    0x705040e040f14120304080c0708030c011425080606040b070309030b0f0402060a030203250f091e05010e04060e040c0f0803090d0206181906081b03010b0d0608 70
    0xc1c0c00603d0500c3e001a5006800ca4440d903005a10201d00c80c0c0e01001c1602d801c40e0300207000b16a2a00b131101d101c0d1401c0c2407a40440b0281c0404500700d0000c3c0c01c190311016510240c0d04400d8101d64606142604400d4022071207617800e0b40c450200c20200f0b204055241d80141e01030b1206250540f14030240d0042d80008000320005030500300103104212040d42c8464000a6264486116041680c0000e102e40100382d215010164048000f03103041210381c41c0c0f2081d42c11201001e41c080702c400e80006180400d01e1b032580b4045640288000b03000307540c0014103100d8040310b1410f400c003142880011680d1280c28410035520648840c8081680b0480071226409a0300c01c2c1000c400303080c6861a0300c0e0a14401c0d60208025030030a005d4402c00780c550b0f01401000c035504a0b16a0b40d20f1200c4a50b90a802c60380c1041d1030740008003038841408180640c0032100c1591902d0321088210354803d812489a50201b83e07880c03404010500041280c2c0c05940c020304420f0407110030200e5529110507039940f6000c15005a50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 415576375 1250 415575125 415575143
    0x30f030a03060e04020a0302190e011203081506090f130e0d021b030607140d0c120f0203091c090b1215010e101103130801050a0c1d01080705040e04 65
    0x8140e15014858140200b400040c0c070001440c182c1c001600600f014400680106014811203920140c4c150f0010041d10421900f0011035031510000f8048040307030b1604501140080700403e03000c9142d0703050b40542c10300050105240c101d281e0144800c03656407040c0c05421416803000300030301c030b0264054031540380441c04c020030714500c1c4440020311300341d15032403001105009001c4210349a1404500164441c40c01c0c14000a001070b81c40706914544141030070300c00e05501d80200c1c1e070720030f55000210b01070185010380180f100600c0c01d940703182244010344415800e50b00400702142c0c0100c00c4200b00c40a00c02c181885506c46507146030000442c0c0c08809011000044a0104603410942d5202507a080300c0030720b40071400e245004041120250980c640909001d00d081c2d4420b00200304000b114850038924681743e0400ea92104214040d20040d2043d01209081140c045407a910607a585101c103214162401882c00d1a00c0054907440c0340602a0000c101d0104004501008003007802405548540c0200d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 415577625 1250 415576375 415576387
    0x10303092c01442503060c0e030d030b10031401030611090a0609081207080307030b061308010f0515010504030605070c0c06050c060108060108030d1e0617010609060b0d02090a05030f03 81
    0x9981058540e510000078440000c600c2d204c806407140c01101526444800061106c0039643c00340d4602c003004000aa044c8124855980026450703001390b4514941a198140c03004240d420681c280c03030308001c542021032207040040010408a8100322a070808082c006403a0480c103c02185100a42e6001040421000a03040000840c02c1120f880516400d00e08141070007508e90302d48156220144c0440304064444891103a1a60303000704569081c103400c103858000f99610880e56003c0d00c01440301c0f0b02c85614140000e482a00b02c802e202c0c07003e9005a607050314090550340c0c9c0000a10340900341e8010804268820030005000008034000b5022a85456446032281d00541e854180140c1000c002c42e0070000c0100400e15000040e54054680c400d80810141d40042c0740e83c68074030400d280b00951030306000b800550500c00d200050448000c50000340a03c0e82c891030040180e5220384a04200c2c00402c01c25403500c5103050740a03100c404001000420384035900c0c000a80384c03550180b44003103690000104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 415578875 1250 415577625 415577759
    0x19120b0105060a050901030e0c090a0e160302100503070c08030a060938040e031206030d030b01021009050c030a0303020a1b050c041d06010303092c01 66
    0x200340107040c1202da151410000910062007401207952040c1030680755500001d1400c800e004162070b00d1000303080a01d0070f1419943d0400540105002c0794404c3c017038079015000840810600388280d81e005000c8140100304814115043c0d44020880000c2006d00d0352101d0006446000443c0030304580107021444508000078070085401d0b440780407803108920b5a00b042030b552030490001014480c2c100795107001c3d07050000b09024000d07003d00200740c1c3c000001e42d03207181414414014001c2001b5003c80722168014078040d42140e513909082ca004d84e020301d0301c6d518202aa600641041e5110314242c03a013128000010a1400d420700d501103010940208550700c0d0584d00c040e410004442c0d06c81c2c1e90701010300b180c40d201e0301c41000d000a540180d480d0b442c1010f4a039001c1406290460310641207640301c3da0b69040091109a807405480c4502580d041030340005000d42081700000100e01038885c030aa480d09030300c180642c1c9a5542201d5060321941c195842c0c01000c1c8403103108000443d040c03180c1c00f6950301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 415580125 1250 415578875 415578893
    0x6071403041d04021e032e0603050f150403020303060d0f140615030c0d060518060f010602161520030406090f060c030206150f09011d0f0c0a0507021912 67
    0x48400c080e0020000345001071b0b4002a0701100344a1298050304185840c00c203c0d400144010702d44540c150403d1400410003500241071640340904a09072041e48081510901c0f905400351400f6006a00500c040703000c2c1d02d4501160000f0910454070003151200b83c0e41d8118049175840380c06103c40c1c100c841084005403c02043c0140c001c070403800341c403c400015000505d00154020007404180d510b00008200e030700c2c034421500c2441c0c07070103086410741c1ca41044e001d0700c1034009016000c010f0090070f600301209421a02001d0540b82100c136440e00d20700100c0c000b00c07104090f0701d15903000400328948408181e1b600b40000d00240c182e42c4c5c1e40104071401c00d030f156000401180c0c002410411141038100200c2d43c04209140c0090b000d80001d64644200300014280011840c0110743c00000b050000640b084003442480c0b20744495000d200090b581d8040050103031504480c2d501090000b0401400d0980c4114001c108061006001600d02481c15201303906c2e040ea05e400905485071032880c4c1a0500550f61 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 415581375 1250 415580125 415580149
    0x4090c030e2509090807170408120406082a0d060302010908060f1b09130b0111060403020d11030409050405010b0102250504050a2018090606071403041d0402 69
    0x21081007000002c007036103484003034031445034031141551804100100014007003103a038015000400504213180d505e44104446d442442000e9540c81603100c12071294040400303a508603070044d16003100760750316000d0107158003240d148030303140205070382c040c095501440102500ba403401d03803140043c1c42e40c114070000d0102d05084d005688a46e0150041008401440704001e40c0f0a4442c9080d20450070040d0440656004142210b0742c094240400403080e0340071a4080704c45810266500c00e22480b0705000d0989511042d10f020700160000c58505540d1401b070003205600c070061008403842c155503062407900701d0720b01303490889280e5103d10400c0003641e81041140104c1c40c2000c134010720803a94500b03d030900c0c00507210383c0307000d9a183d20018100190f141e00100b00d03403941c450384d00d420b03100c00b480070b202945c8050002030717817089110144045800d0615500c1d20403500640400c0c0b40c40c499898100c095001034420070801d01c000c21000c904003241e40003104028250301c15145560400740304000100c0130380 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 415582625 1250 415581375 415581403
    0x50f07170307080d02070825061a030d1b02030115080f0f03070f030c060c18140603040b1305070e0412050c0c040f0209060723030a1e0504090c030e 65
    0x5102d00c00104841d50115a04020074903001a90b0b8825864401014081e20401038050500f00251070000528014400d900034400c00040010844943c100c00e06219030381501a050351050382012402030140d2148a030784440100c551010591079070001c0d0949035020683c90401501900800040104102d038843c40b80e01c1c4405822481641030101ea568000d00e60003508004061071200c09160060090141c0c2d150459000d001d10080b5210141a06624115016044045601c0058803d20109180a400c40300034041865501c4030f03114416283c8018040101e0b4040d0708d0510070025008012140060480b01d8080100c0e15082c14070360070b01007000c1c85641c10710000b04803884d400b0700c000c54804001035040754001800d44481034608003c0c002c4000654200c01d000071440d0034080340107901144130464403c44100c45005100c0280c50303005009081005c5118016600700800411030110782c40030007840c01c241441d5a915002c03080e58141408040400d03510407007000c140d441031200c03401130100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 415583875 1250 415582625 415582627
    0x9060904030c1a090c13020a0903030302030a0204081f051b030f0405010b040c021005060a061e032d0e06040c0b0a0e10091806120b0a09050f071703 65
    0x101101054025000400060402c0b0440060000700102a212441c40520301143d014091900039075581d9508104040148100e03034083c0240103515981c021600034882d5a580c002400741380d56020740c003a400c05440c1035142a001c0c440841c84031002c20082c0d180c190f500c1e071030100d0031400c00001c070115a00903149503500c03120700d600f4521000003001140d400c500400424407040c0c1d203a050440c01481110700d00e0f54000d0070b115046e810382c1d5001400d0201e8841d010010411a140d00c01000b0700c803603191040101081c6001d03070300111141820000d4407003038040e060100382010803000d084c450b009400c422404074138000340031604443e0a84a03045103001c1440041070242000d031910400e0540521031301203220305c00200d580104d403203003c80c070304800c8000d882c0c4440c0200d400b20180110300706004000e110100b400d81e0250a800714042c4074112a4802c004202410841d21480c41411008120850654481c0400c00008070100b28104508610701d001d446500e045c802c0054605407004000f00840d40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 415585125 1250 415583875 415583881
    0xb1306090e04030c02012703030503180303060a030f14030f130b1c05070309020d0503030708090715050a051b100e150a150b0a0e0a0b04030b041b0801020d02041409 72
    0x18004030580301c3e0b9170302403e00310f400c124004191311209006194544401c0d820311400810150007001031800307012004083d42c40f1188a0080c0d590300d000440e1902e42c40312149004101140c4142e0031081e0440c01200341c01048009030041903c0d503840800317814040c00002900c241400c3e02114100064004a200d080c034003101101c1c0c48900c0d400d1101c070b91070119918004541340038065440780c14020b03170192210154208506200c0d0701c0b500102e80030b001061481d00007410000000c50b200060300c8101e0407a081913040b0600494840d00649010024058104117288400c0c002c030002d05040706030b4000400b1070703521440c0e0388026207d07056508030316580403000042c80d00701c88081040c1c2c4034018820020f100c1c500c0c01c1482c0042c400581c44944890f20000c2d807081010351000c1080001300e029a407800c15980d803080280c180b44901d21014020712100c0010400103112003400c1d05095407820b05040309180c880200a08a0b440311100700407072540010100040d0140424040001c082122074020b189 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 415586375 1250 415585125 415585127
    0x30201050711030f0f0a02180105010909020c100e010c0909110409090c090903021c05091f410c1f0e1608150403021002130b1306090e0403 61
    0x200031510300a1081840303000e195a942c904208003140b5009050482e0300300142c0600d251b0726880300920980c082c218461000b5450074040c0c000d14100c540c1a0b40e03011000b482d0040100080d0405410440c1c40d0080c2d51a0305000003841c080e000c8003100c000d00014405007116400b078100402603005e20340540c240759203100156224401c3d1011a8405400810104124549480900c4542c0c2000c1c0100d460b0043c003030107140d40043c0201c004102103480a044800c1c465040e0f50750b0040d0352044d0751000c0d2450001d0392030850f0134503500c03182c0e1b40da0034501c11221011070010601c00f0201203c8031804003190070040403840c0c1800810485032142c4225180042c0000b074241c48802121b004681e07102504080c1d04c903d2000d078071081c0d000002c5425200318190f418100e00c02180e480c0308a6002e84183c22114108240d0000310a010b10303410f800401c440c1c1101d500d80b6019400c840c0e50000b92003820000044c80c2c48054008000300980702408031074042c20944098805142a0410340c1c020142c1f004010000b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 415587625 1250 415586375 415586377
    0xc03061e0f01030c090807060801080f0f0c0402090118091505090103021c03050f030108070e07020610060f0e04050406141828060c0c020f0d031b0507030b07050406030b090103020105 80
    0x8101c0c2031902007074440c0000c0c3c06540000040d801812944108540011000e83c040f4003181030301c0c40c0d001659042100c104149949081d045d00040c425004582000880c3ca02030340100007240d018140144402c0140c0510f1700070200a51002c00041c0c0c07540c05002c0c00041204c0d001c0040c0c4411101c80340694115008902e001d11182c500c1000801d8021881c0241401082521030301711110414030740d20340c1c40e1783c40c00c0e0310744540d486500e810b06040e6011582183c00440c01511407964000c28a03403903450044201e0303508443c04010f01c2404820405844140c0310350050601c55801581d002c00c10840d103640003800c0c6000146002d10508c04666450781208002c50044001c208154001010707400b00780c50320302c09011051004240c50303e00344400c56065040b040c00c3e00b110303008070342ca5400015035401b0b20441c034240c04030050008000e146031514004032144401d60685c002e1080303503c2c16403a566440c01c80c1e24180c07211000300720702003410044654140202c80e4616021f03200c15401d94903690001c4c140d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 415588875 1250 415587625 415587649
    0xb0403081b0d2004060f0212070f1b0519210309060305150a090f0f0203060d080f07020a0e041509170c0a0506070e040509010605010c030c0f0b0c03061e 67
    0x4031921250480d024101c40d142da50303403d41180c1059a9520303680c0380050000306c61403003010090701840840040185d45101550281e031707040079442a201880780d642c1c6038071507091071164040951100002c10075445171a0301640688a0508156440d818021144042d450301410b054401038130840c07440009c0d900c8962641103c00d00c0c24003151548811414548242e0840c2c6859003282d1101e80000304016107800c1080c4c007252110b0104400305d420400c2c00260b03c41150500c2c0c202808400940005042000500c2d500e4540c40b00c1c141440d140b540082c41c2d1030440da02541040070b2032030511003449043d906030015080c1240080203602d8196840d2011303658011403040c01c543c000309103560690014007001c501c03181e001055070340a00d031090b005131802c0c80780d00700103004034035000001d07019003014403c220079a00705844440c4d03006540d54003140d84c40e80320a42100c4070b01e0346101590006041d0420140600c0813550203a07201d00d0030f00240700500c45490041000407145100744c140c2c036100d9000d2458 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 415590125 1250 415588875 415588897
    0xe010f020a020d0c050a0519030e090411010f0903080721020d0c021c021201020a030e2b050f0315040b041401141206090304030501060b0a05041217070b0403081b 71
    0x90051810b045c52030070800700c0f00015005021340804008208500b48055001038800d44400e003410381d40340709120340b8803400c48005044440360300060401790302690101022080c0c525100321560746a940d540305a0308001800c41e550060091100b00100443c600c86074911840e100400b2400070402004010289110010340201e40f403a00c020b046c40d209184c9000704680187c070107603d401121580034000d600030404da400107444c01d6540401ca41c404a02c80e00c0c00356002002600420080c080601072601158401061020420483d03801d100807401540c801d411040052040b540302200740000d949015400520403854140740f83c108542800d1043d054604507808a640440381e0b801094000f800784014800074403501d010409407403400401041034038030a000900100303542c2c8000c000c190007801d0080010500030300052022002c1c20041c020090301484404111820070f00405c00585c1c01a081030318010009404c0200780341d00301d4410f58000010100b040d82141e00c20140020b00d018100c0011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 415591375 1250 415590125 415590137
    0xf03200303031b1e0a0804021e0102063d05100c080a0807021906050105030d03050115140702040f0f0e0303010501090e0603010615021c050f09060a1107090e010f020a020d 75
    0x1901c0501101d249444004d802c100c0c04c0d92800440409024a042141c00f24411196444100c0c4146542c820300e581d0884180c00410403926034041c4540c0544441080110f404004803e01c040900f0010795882c070b036220014800e0340c560400062120b80f410a440c154180704c503a078100b00c001f89010b070450b00021701600c0d040c42d06482c0c0314012414441d058014003000064500e000c414403115503c818120b51703086044580001d0f8540d02501611070074441c0794919100401ca2150250003a00c03200c40404c4a4605980340a280d940003078122146512280c8055655448401c113a40d00d80c0310308003444901070300035030456150100007030041b003060040d00b914141c06d10104019407400d40240c0060b20b100e4100142e525200000203503500c208068045030f881040031100301c0e00e405101200c0e4001d5084210a180031a00e2060002503400400b12900300315180144243c8040244810000f5052803140481c0403a2102242c80c01d42d454019070b655542d1040202881c0150001403011b1140a141400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 415592625 1250 415591375 415591387
    0x50702031203150f03011109011416061a0109050a0605071a0103030206070f050a1b02180702161d070e0607051b10030c0905011103040f03200303031b 66
    0x400d0811409159907042148088144041c540d0380010b11002d001007500c615940c05840c2c0109800c1e07980403a07913004810010810700b60745510401e5076601c508070440c0e209181045603410300c4c050040d00c0317a040d20450b0f56103542480300001c042106030600301c2482e014129900748000502840c456201d5103040c400d0004688080140340f108100d00d050400030060403960352410081e44a40c81100c640001600d100a40d03050b10b4040c0c016903151941550b900c1400783c4880310003040100c51460281d9000044409140800320111812817040c030305540a081c5a00d04192442c080c0c0075550003620b0610140d15451103280310031a0150741c0503003185810840d5071801c3d030108841e4440c10f0000703803060080b0044003554a00c2400201030b0500169070290300400b035864214200c0314150328a9000800d00c0204124030b61240c003007606800e0700082501e1809640e02e075411813001241c2e00c1101e12807c590500e03c0041c1c0101c42030416440709401541c5586020b5025072099100003000380e13030010001c611 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 415593875 1250 415592625 415592629
    0x80f09120a0c060212040c0512060f073501080d0e0405060109031e0201090b0306030a120504152003122805070c050c032e110f0a091e06050702 63
    0xe0301100b281c00a500b196555141d0f0514064008102d4045e290030074400000603140c00c1440702c03030743c818641202900d550b4a460860008400001d0490002c200500350503000a88050080b03801543c2d032000400001c0c41180c1a01880b800140e1001c5a2900603117000e01c51690001d0051070121030031a800513071640c0d0b020050b101200c0d5500301401011904a541181d12580303210030310b40c1c50003602c624281c969508075040d00c030f00c030489265415070402c4000c0300018024076000e4104040d18105241015210410038003070174090300842c0001a2003641c904040002d810500940d404054051860201c19100c1007281d00c2c400350815402161a103401c8006500e6500c100c038218160110901040c01d000c0e10007007009646140503151401004030765003091900082010b000300008c01860640f50000244e440708078110080d101c505601e81c8403605003000305000814001031039204103034842d494070000501c01a01030300404030252280385809448401903042c001122480c1c0741c07065991301c0500c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 415595125 1250 415593875 415593887
    0x7030e0c0108040f060903050309010b06070c0311040b15040e0a0207110112060b0d05150108040c1202030106030501181e020d14010209040c0201020c010f02130b13030803090d080f09120a 82
    0x1e80940f05078504030f9200308043c0e2007230085000d000700034024400049444204000c40c03084540c0140440b40d03000301000000c03003c03040020358000003440003c1e00074641c40480c024a15440c0d54100120740001d06100780002c05001c44d804c03050310003045003000030950713404203181022456a8103200d100c41050314100c003980c100308064960a120303035032a0381d0f13040400740140000340c401c0030b40c9445140c0c403010203511810440d48a180c10030b800402d2185040007100c50110640026038040d5214072011020074024010900092034000b400c054000c0c00b820400e10f4100202643d605002d0121450000750780c81c55050142c150b044904c03242e4040306445894020f104409800e1b400904040c1550201078041d2301800f0120490f00080c40541e00341c8d00140224825070b01d1240c061519903200f4440440380502421183d8050f6031440c18090f00e90b140c0c1c0c0d00c0d070341044444000342d900480c08070346c00315804002c10703421025064030817046090845003030791100ca00c04101125400045000150a4030440c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 415596375 1250 415595125 415595153
    0x90c062c0906060d06060f0e010201050f0a021308070e100816261f050907060c060c0302091305040c1d06041a0a0f030b060306040812040f060e0303090607030e0c010804 74
    0x13901089441da81d001c002d40154080e802039400300d13a8141202e11203500602545106003054040c540c03442d640d10859400a420240c28602c0c0c2c006030030030105051100b000100058050001c40c141c1d00e24008100c0303104807135140c03c040c00e50f40025080c0d01a8808d07101d00c05098070820a150b40d070f900e80c2d00242c2e52110401c400c5540062144010f084602c0100039403c5078604401c07500bd1229036240e2121503901d0a240c4101c40015401100150110340c0540c4210209002032401624141d0071200081900b05442c01800d40030b65208240700800100741c040314028079000003160904141a041c60044030002130940d40aa03454140e0300e07036240000910f41b030404400a200304030860702c503401412901c1c0345000c00c58440f141000402d0062a0000e00c0f0352040703900c404158070780101c0500b002d1581401038012210300107510341c0000014072a01410000a4020300115100d02d4403406c0c3c10701d13110014000c101414a0400900d644900126144100110078248990700e47c403907103000d41c80c0c103e0306 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 415597625 1250 415596375 415596397
    0x50408150a150320091b0306060d020a050408150f0705031e070f02070f08061b1c02070201080604050408090409020604080616111903081504090c062c090606 69
    0x841400b000b0002030141300000035582801d03841c43d8501c2282442581d000549a0307242c40d151000440c108031141000841e40008060a801d052080c07054660781030340c2142e480000801d00215003405114400c0195a28185807042c03506150305101c0450400c0c404050611003c01c0000400540c600310b2045c404001d0f4104d104250701546040e06004054001e6a140c500c014000e000c1c3c00200c00400c08425400d986601026207010b884840107001c911100e1111541c2c00c2c4c40c180042c608021010013908500e415045026035034501d02c1c40018522a001400345204e1443c0800740b00201d001c110950b000781006903000a076814a500008203280115401080c440c8200001c1117008903a8280f02035940c41c15403509550b400d031049949480e600341440c503c150200c2040ca0402080c420515560840140d41c0301d0320074040088049030948410380000c0d5000c9a8506c4104002540b0154900a8000e4407061580c00c6120081481124000c03646031841030f080200820000d669401c1140d1810840c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 415598875 1250 415597625 415597661
    0xc06390904150603050a06050d080405011803050d08060405071b060e010b091305010b030319031808030907030302070501180b091507060501140d050a020d030504260d050408150a 78
    0xb6944008010780403c1303038191b41050400c3c4002903a410161303445405d99900140442c00c203070415004585040c030502084103800c64034480000820300500500c01c0c2c4d40d0065440e80d1417443d02000380420b50703001810003020000401003142050300b00c3c55910a07001d5115a0110780c2d00c40c01604603024251030000076600c10031010520207400501503d100d4880c0c8a080203210203401001010b442e405144900c40d0a12201005000d2043c400d501081d40910320000002842e0030548074100181c1040718040306035400a5014024560100150030041809181c0340b0b000107142002c001e00503100344608a01c2c10404505240141d4840d030b80c545101c0380a9030502c1d1110007a09010000c4d00083c0718a17130ba50b40100b0720000e020b050040405c541140c1140084c8040b4059500341b100e400d40829065080200078400482c60003088903043c0110380d08001c0103100c52001e42c0101d41000030300780108091000801c820000440045000c0302900d03209001001caa0791039100d0240070340702249a041c4580d0f4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 415600125 1250 415598875 415598879
    0x20d0c0206060a0801020313060e100203010603021c060b04060809010212040c0312030207020f0913050607030c020f060103020307151e1d1e100e060c0639090415 71
    0x30380040d566220340e6088a1904074940e480007050700700d1101355204050103400548850229006401c224000300300c1400719000c41d040c0303485520480c3c00a803c50307030010f034001a40288296416554140030b10000c1c40400c683e81c50101c0d441c6032803049100310700c00e021440c0d0010704480300a40c1920003950420302000400e00d864a001e0321803403c80d0100b15109a603400181c01c000e8484d05c2a44e15175a03010b0460490076109400300302c68017500400c00405940c803400001c00003001808924044da14540f00880d400f1515000070303040020118107000e0030303030040c1c00400241ea000034000c0121418018160348540e20340801310745101a40881c11041450350801b0034107950701c1034600c8075207080d00c0320322a03c510059007002030304510039072200801440c60300151041e00d005500b0181420441c10441c5c01d21040c4000b00700300343c011403003400b0560400d8040201d0b4503901440b56401c1044040400000a5980d01c204280115412018130764600401d90f45000c1d00da582c8211940c043c0b059403848005e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 415601375 1250 415600125 415600127
    0x50a060c06090f0b0f0108030f0f09120d23030402090c0901270f080109032a020d0c090e060f0411121c030b01020d090527010806090118020d020d06020d0c 68
    0x108040d80d041e10305c1e4040300000500f00c6d4010041da004400b00941e6146080c50030540303540c864210360111548496054084210100d0402030501c1c2d00a1685804022607910740302c8082c00382d42601403c81c2640300700704000041c0e44140d500b80d400f9a1000318680c455480c940100e03240c04e031b41c5609000c44000c446918400c2d100c981c2202003204c0030364090010954840102c0340c00e03150600300041c0410011181c6404a0034544c40020900d00c000c04c84450000c41600010032081c00345006895298141d201408041c00c1c602078660083c2601c1d0090116042141c03080e0011000104041d0184041480f1108695642d5980859a00c103540c219404007164140c0100131601c2c034503890021030b160064440c615400030415014400264850714840340c0b421040c4500c100d60007542015401c1c52404800984c4203080805001e85601001441d80f840c11b0880c1d1402c688920004246903041100ca9070010395400000c10304080d07043e03c444000c40300b1464150301038007410b82c540c14200d0503c01c2c94a40c3da = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 415602625 1250 415601375 415601393
    0x140114091b0d240b0d081e1c020306011b140c0307080d03180206070803090d0507080307051e030117070e0124020307080d1410050a060c06090f 63
    0x4030715618401041500410108542c0380d00c84a00200b044850030070301e003480c00f0001e9090f000300030900303008078071900b0500005141030a0f0002c1192071480120b811001080400722041c0012541aa0b00703180050390100b1030070b80d21000521890050b00040041c060343d1107200d990f0b40d0b100300d921005818146030319061381c80011036011a1800d105081280ea901e190014040e0103c9113040003030146030030a41c40c00c40240001d40100f21840c1d80c1580720500503200d0308000c02ca1140908a070301d440307041c01d03520607007041840c140d40c4041042c24005500410701c40b4007202e4001665040140d0744100c0d00213840e1f909001c1d034610840750000800001060a03800d462000c0410210080c0c40600d83c81e01100f0781e80180070700404a8040c0101c82c0c06002e002303203448039500901c0600440b410b00e9100d90340c0d240d0703942c403952a0640c0151550790b02007000d22601b6440e50440f40030516290558141004070b12100c0607842050b0802003002a82014040268402848650460244107040129080c03c03402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 415603875 1250 415602625 415602643
    0x513110f07050c04050408300709061701080312072003090a06020102160303090507030503040f0905012102040510030c030804061403070f1808032a03130314011409 72
    0x10501030381c0d0703462045113410300c10244103a9200d04852304141288036180041e2a03d2200800800403031442c40c0c000031207800009118940700c0d0350b00f410813400d04400405000c904501055144079580c0140901c1202000782c03008c1900243d201c0c0c505a0702d8540803610b0105486400284d4884080d0401c0d100b038010000b4074020b070f810744e0300300076071986c41740304a00300d00c203140100227040c03001311542000910070b4001c0b1501c980240704843c0c49a80b01c2d250a415540701354000010492405010800f843e03041c080c090051408010070001c800618820180ca52107a1400a101d2551100003503c410101c0c08810003840e08000f01240c41a107030302c1c051040d41d00a00880e4041040d00d60f001c4003000310302d02180d00c02c00d40c40d0388000020f00e0846083d501071640c42c448212040d0401c9001c242410104082c01182ca007038043c8184a882d0104d0340c0003001181c100d210500d41080054580052010440c40102c0c0c0d4003154607584004080c01c400d00400800541c4100e03281008188020700ca000204081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 415605125 1250 415603875 415603883
    0x81b041e0e0c090112020d02040b0d0c03140906070f090f14130510120206071406041101091d1806040b0403030b040c1b0201030e010501080d11030406090513110f07 72
    0xc1d5460744411469240603241d080c40c005040b034440c01da41010150041c00e9000e00c03440015003020349a507421200c1d6042421a50b18840e611004100415410300400e03400141d101120381507824002c40598807010020040750078064950079101c80548542c002c44000d126621076040d140707031540388000c59842e9030040c886c8505c410a807a801041c00a00c60640103402501010041c0d92030141c03507100180c10341900780d9000e03000b446000d0114400c4412004498101c13805008946414074040d8054601203002a0412410030001c0c45510b1341c1401640d0080c40281c0402c00c20742d0f503031015100203079a4000790303051401641d09110410816055103805144a91020701282d20103030f0500013100c0d403500903800090007024081c0780110144c1c2c1c1c0340c1001c0303006150100c1c40452004042d0b007074540a9014403002ea0003a425510150340c86000001000c4403a4090343c5001e00e894801849011180212480380b05500102074030096070303074440015000301d00e01850700c64514107030059581d0800d00083d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 415606375 1250 415605125 415605149
    0x5161707021e0a030306170703031409130902132c07080f01140c13061b120801060f03090c030206030c271002030c0a0602091201050c0304051507081b041e 68
    0x8109480c000c0f11812030040c0c050010312030a449c644046400084015640145800410111a1945900713404101c21102c03c600810701302020b00c1800003a248044250f682c40b07140c0130004001c0300546d01116020381105040031680c54000d580c0030305000095002c00707241d124600c40c0944171041908000c01d042d02511f03100419030b64004900d01d0030710030400c00d0741e1103017000442440014007450010190310a20407180070b0310080c85d6a448152003102502202003401c100040001036880090000c8045681c901030014526507a0307503c0c0c0c410f441d80030081c0b1503440400081c2c0c200c05548103680c04400c140029003258212010a1405c160300000c030a070240010000c0034030002c2c0004110389082a400e4010310900f00c03192245c00c000c1d0030000503954822104184149424030900556000d034048204440c0d40781014603241d8a04414101000741111a44c410442c500b81c105c02c90744e600508103c91002c420b0440005d0041920464000600358103000c000d41c0411038043c440b130019216500d2483c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 415607625 1250 415606375 415606379
    0x150f0c10062112030209120f0c0a0e0a0c0512101d0115110705060a0207050a150c030e06210a0e0118030e0402070b0103030c0605161707021e0a030306 66
    0x301007281c280b9455200110014501480007614a0303000318841081c034900141800d942400080d84621101414520b036441041201508041400002c07440320081b0b507001e0303000c2c1c600081c020200c4001005480c1c0c06036141e15130849240544e007260f080c1103642c59140d0452920051041e1a1122805050740015640486000070000c4031001c40c140c1c0c005c08400e0030181034a000c1112651a84503020b1494003644a000801d61502c6010302858201a0060f007840c80c140020312649101c10381c011509907030604920102960400011045180c051810740700344403c03000401c00500c25000e08040342040e000c10000d080304035031100ea02620f8580c80a00c03482c24500012426100040c0411a1207428110040000303400b40741ea92582e607a024101506001294442e202015000d03803094000c04c0e0000880c5c400c00810740b1440341e00020740ca50340c04403458000c3e0010400d83d20b000c1c0d4205210f80c0e21010540c0503008106044000c4083d0001c1801040388002d00c1341c51b840250801c501103401c00e400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 415608875 1250 415607625 415607639
    0x14161b0e04150c0e060307030204090f02040f0302190f09060e070e0a05060d1b02061605030c030c0f070605040819141204080d0e0c0108070201020711150f0c1006 71
    0xa034502841d04041d50405001c1c000008200401c142c0340d1034401d00c00701c0c1081102c01d4036208041e43c811605a2401620303030f0314015282050b03540443c0700404003881044240076801c0040040b0017540c3d01600c1c0c04011010b1008864444007841c0c20030507550000250002e650340d0550864020340d001c031f4076a140316440b07000065904107100640135a010b11251000d010358140078016107a112602c0001145481c8024041064074400b890000c0058100c5010040203040c01900074880d22100d18021b4030394a0000007510b44d6000181c92008070a10009145100a2400c0c007510032043d00700c9400c1140b410189821145644020300c0760703080f09141000350309140d01034080c2005d09000c0358846842c0000f809801c180c3c0c010003c1007210986014408210b071050140f01d41500c3c1d02ca4031000f00b400345040c0307001501208004050104580c01040031100040c081341301141144001da40d80d291400c1030484a080034059607a0140400001090b0203e4050f030010300d511218134040c008024054a5002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 415610125 1250 415608875 415608899
    0x150a120b0126070504020a0e190311120606011b0503161e08040509070c05070f06031506020c0d081e0904050609070f0809120304051b0f1014161b 64
    0x602c15003181c02031407040106050a400803e40e07655113180045040401310001203517a1544403118021601005051003001880c50781c4045084044a00c419045520060140e41c0c25005046a040042c032074241001c101603401e425400f1584003003520744502c02814030140502c2000c0040d988941c103c40b4008241402241c2a07a00c41d8000148614190601060140e0800058004000c0150081d4040040b0f001440144003030040c0d507255588503498400c0085c1600c81000c4050f07030104c05020200011500001e84450240b001e40700c1d40501902400c2843c01405000c210001405142c0341c4903002d100301c4e10003040c81100482d010011038403107400b40250440304540700408904a446250303000da0041c10ba81e648098440101c0721300309469004110743e40c00c1a41d0840d1301794030800300641c075014020210110071a003529114040014400010718401000941d98180401c800c03c4910b000190000c55803d10300103522801141072500d0010381c2c50721400d5080c110190200e0010581e015007030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 415611375 1250 415610125 415610189
    0x7021005071b03180302150703111b0d0c0f0f091b05221d041202010504050c1905040c020c10090501050d0b030a0203060414070e0609150a120b01 64
    0x424942007036501030b503055075050400950a014011039800003c010303075134600409040d42c102d0110a03111401271402403e00d09001c6417203006500640020909001c044420203410702003102c6007842c0040e07a01781041401e0181c5c001c0140fa031980c2c1390114184140e45159412195620b00030032011a00c64909810f0000b03a48507440080c170200700d4500d09982120101c0e14411050312402e40302a640c80c412600c12082c00c00d90100c01114008102c207110349207000d5104611680001d11040c546659040d4961283c690800d00c244030840503a400c5080c6001d01c60003818018208001d10004424082c0da02c907032842001d84104100a01d0094403889181c00c0c0044580684445040c040718400900280803010902070b00f43c4100703076000c005690100007243c020f9010300d001d140301d034080101032800c00d0140d4008142000401c018440ca03500d46446290b4094172072044413040c1c80f540c5c2e00040081c102c0350301c40b43d1068040810311003071004078240325040b501000707048075038030240c03406e40c0c1524a014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 415612625 1250 415611375 415611407
    0x10905060c0c070f080106050a090e100f060806130605070f0f0302070816060b0306010602011103060609150c0d0305010501033806071112060603061602070e0702100507 74
    0x880c0c04168800001c00241c05008007010076240c0054451082c0c0591441c036921500340e6a450740010806402c00350020000f404041c50140640401d51521566031102d01017841c100d03680e0341d0f51200d2200301d10b510203c00341c1039031400c1e204c1e541048081ca02c50281120016100c00d4940400b240c89640541d0188041c01d405880d1b82c00c10342007400c4160300a41001c5010b8892401c204500c0c01190040d0b0200c0100512070f0f0300000d8204030712028980b801a0503000b46055a150225000c200070750075040d00c0e030040003101c0050350780483c0c06c0400d03a05005582e0440d0030742d00c00300e10700780e0030b05e00819070710842c01e071954040005130b80e01d030011819241c0307500c0b074110200b80c20a4100e140d00031820300d2040409a01800c459038200880109045620241040d1880d030b940d140704d10010701e0090301034460301d030041c0010304040c240000000d031500c002a01c124a00b920440449650034003e0001070000e000d10000f5001c5850b0074040a51244091140042c05502d0b00000600160081c1700e075102902d05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 415613875 1250 415612625 415612633
    0x8090c01050a0c030503090319050c010b01081506070804080d08070314060f04051e011403011503081603020a060c0305070809060f07030c0e100f02120903102c0f0708010905 76
    0x1013501e003603c2561000d0300020150104203c01100f0b0800c9102652000a29a503600d82d114848140c05d4215800d111070103040010301000d00c0700380504c4080084000308200e0b02c03981d0300c1509186c40d020318429a80401480d004191024a403d03404c0050148159069101071100b504001201c0e40325a000f240c10303580c00b440314001403455040603030207180d00040c0300b0300d56040c0303008030002040104804d92100010000e04814041103083c03c2c02100002200c240c49441003a0443c1d82d8811a80507640c00507000c903187c0c290701c105061080100240594025408100340b441900d8000c000d03200448054002c251142d01013200042c0000e4010312520881d070900661b40c5600200310043d008004001c2d040005812450701c89607501601c12440c1016600c0f002200280e504c4064100940c4958100c121603041c0071060954501040c80e0202042d12240020340000034880c1d908400543d060345207026000c0da0401e17442140001c0c801600c420b001c000c540d106541c4402c2d007400c0e200e00c1207008100da00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 415615125 1250 415613875 415613897
    0x1b0201080a050718080c01030c020f06060640080a050a03121e0e0d08130b0a090605040f1713120218151504060f0f0306080d08090c01050a 61
    0x40354002900104a45420268450030a40c0c0c2e25141c111381d000000c258000820061056800d07110f5800562440c1c00905030802400a146440c2d2800811480c041c0c01c00042003078401c4226030b10303180c0e50020124181c02405118035040b4400703082d03101c184101880b100c0049a44d800000300780b94810382c060b0040028400e03660381110440004030071200469169118050300c8402c810358050603c07440e420000f02d021040503414900403840d044001171016080521410400d10040a042e258100380703c1500380d191601d980b0000c002101c1c01030600c510381001d000c00c00030b030107040541d414060011028134082580c40841030348079285041d00a00381604003007003540384514109424a000901488014588443c00b110060702141c4100b2740c0d0400040c8855a480c1070b03050340000c032240a0203203007440d0502c58081c040e140821950340c01d00001c040e680b00c03000c0c441d07046030010708034400070b80b0402403819001520a82c82a0b414405ca030050384c03c0360b80194802c1041d1022403000cad07038858840302 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 415616375 1250 415615125 415615141
    0x30c01030b04230a06050409030f180f060e240904180501110408070f1214010906020d060e0a05090c0108090c06030411030c010306081c0306030506010e04031b020108 73
    0x8040884010b801548525079140c3c2160031800c6401c1c011a81c0b1140c103000d1501e180640c0c115100c54000900c0340d4503151074103001c03c0e40450b4081f00d2139000d04018070135108501014900360501d51008000c0c55010340b012070300320f5200401c08100c0009541c44d08150641d0394100780ca443d9030340b0440385040303401d0001311010301e00b642004901108100508031031240544440e425503081046004203194006002c02c40700900308060801070120b01c11381c06031a400c0408427007440240e94009002414454030507264000294082c8a8040d4000401c55545401403003202c0581258402c14603c0140340c000030b42e42003528000c5904c00c0744200042c055070217a0000558890101030013424803440352210454035901d4034001103004a028a00078001c81104801301481c200c0c080c00c1c024101801c02104010a840010b17000410201e80034034041c20020700d060840007441103600190691144c9800000e050780c1a08c0c0d0180590b0196039043c9205080c03a01d014556888890000d00082d115070001f00c01f5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 415617625 1250 415616375 415616381
    0x2301021c0519050f1308060106031806020a0e03070303090816050a0303030c050f07050102040e060f0a15110604061d0a1214041d07030e010c02120309031c090204110702030c0103 78
    0x80482e50038001c1c2000300059480d41150032010680e803110381c0041c03091080100401069004002600d810b002d401101550a14600140714000b0859600864a620840d000710035482c0c079a0b401400700d900c0740f5a20308000340601380342e119001c0e10740664108108200c2d48032190790151500905416602071441ea0101c00800030310102d0410084d0130b20007503003039400342070040c401c843c082e000240e2100d09148520101100c0a40924070580d5131034011951500c811407810215030085c4441d02d00450008000e0300c04000d000351030301d0b40340125401c0204120303096020016603c0c284003140b034881c030081c032550713642d44580310054110001141e02e841e12500c507070303d9024030301860032005042680d6040b0040d1300095034902011a40d82240400c0002030303242c8940c071142110302d4001e03c084101d80c00082d41350814041030000e0488004001240f420b820012102c91003500550204000c1c4640034110081c4114502240705034209102804410203a00076620f203260020701822501946c0320042d002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 415618875 1250 415617625 415617667
    0x60127030f1a040609060b042a090b131703040308030a0e0705130c180b2a0d180506130509090703150204030b0c120106050309072301021c05 62
    0xc0910041001c44200e008030760464015803050300003140c0309905140500a1f50050f418507030042e4503000ca10301d0a505024000d070010b8525070301c0040040744105084460100c203400103064003800048145400041d000070104440202000720181071000340c040d42c49104074800a071150700f0600100301d211105a224029001d00703103003244c008540d01c80104540000054171240403c2d034030860241c8442d000781c41000d00c5804d84001402c0c160900c000c3c0b0b80103015400141c0402003007800b4136890000455020010411503100b00c4498400950008100e8403103848421695207145000007118102a41510f0003c0186130030201e10038140414041c034808018200d0600d842140d0f0008042003c603000d000c0c45040504015079110f00314100300010500c050a5881002010800040480103410b5a02c0c151105494401da07282c58004c109441d240c1340b80c10100d22031001070790b82d10245002940c8070302061800e03002d607039514504454010410403080444404035800700030a841c1490040084c81e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 415620125 1250 415618875 415618883
    0x4030f0207030209070f0816090603091502030405010b0111030708070212150906070e031527070803032e150504030b0c040602070f080c0d1505040308060127030f 71
    0xc0d842e0352a000541144e10aa0b00d0030041352540203110042039000c440582d002d0346060409605610850004040003d40d11421081641c0c0d000d00c00e042000e02015801840a141c0056440c1c0c03c180c00d1550007440c0d981740d0980455030340e0f40c0c2c0030008a408405c1d40c0d00b80e600446d0843c2803809a80a1143c80150f0740804000d42c01400b8004002d00144c184040c0280f050000a0040385070918024212590008681b4030a5206912246e0700c035036039460160b070250540101d4104070b19440c4089141c5602c0149804150160b64400714451400002440c8a0040600703a100702c9081c4602c205200501c14040f40e0441c80101c0003848095400700c0c000d1000740c582d00c0c0c064940380d078913214540d4404007643c4001d002d0b94005130810001e541008403074054050510300380300b01890884883d640f080aa1001401110354101d01c80c20322001d64000c0d00001200790b028007042c0780c60b18004203513000440d0182e001c81d1203c0190b1860350319203403610b40140f62030000b00001d1401c688884002c070714412400c47e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 415621375 1250 415620125 415620133
    0xa2103090204051f050f061b070302031c0305010b03190902060c01240905100e06010e0d06020304031d01021f090c18200307210c05071a04080304030f02 67
    0x30340142c5491194910038102c050f640c207180c2d000207800c40c0303120080d940001d105124080500c003456840c0011288030200891403040100090342c00181080569440a503040c040c201491130000711814180103550701c00c1d9070800c0301c0d81e200d041078901070105440029083d1100e000119000c8001d0b48580c205500003400a82003010500d001e50a44200c0805080c00d0b91b54000e8000c0981c0e2014240b0028110204040c002498081007019080c00d141c03180c0300ea8054101c01080450b4000c44c2d0310365503004064035803c3e89010f035092110107540145da0031400528500d5003803a094034010740340000004141d014100320703000040c4100c000d003600114070003e00e940b00110000030f01a03083c85002060f814080c032440d180b941041604a48413030800c000c041c0c1200c2e440354030240359601202c0e4403010604040c0240d0b030455000544208420880d0b046d0385103405108a0a590810007508a2512078291440300c0c2c13104084450244030142c50040c152041031001ca80040d016041d480e08424442c4121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 415622625 1250 415621375 415621391
    0x3041a06010c062904020903030702270c0a0f0e011211090603040f0210030605030604030804031709030d0b0105040315110d0501060807030b031b370503010501080a2103 74
    0x402218803d02e0102c8048282010b88100740e80c02c0101041300d080210b03000c40c02c2ca43c0000104e6102d2285400091161401d04a0401c0c40120035600c110810b421020051203881d110240300b600d5030050f9241804100c000307103100c0400d03100d030f07410002644045c0d5078122082c1c03011440700044c011035141440c2d03030b0505001c007aa181d00ea100c0911303c01c5d4001c0ea809443d03401140144071103c0c4111f01c403c020941004018084c5031000168a60050751510309100716542d10300b0200c0e090114000d904012110107024001c0740c000c0003000c0c026a80f61a0000c2150441440065036184600d20009000c10300b50303101010b40202591050000004040400345040a0300311030b0300481d0801d81044003c0380801043c03114142d8035204060400d01d00b54010800703111901c2045900700103044401d44950640603504c00f82079103070180381401030744080e501e1001c0003202e03e20041c007100328025113003c1e600e00b000000301d862000450302c403a5500300524070420352154a20070b0050858003140c1f4240350b01c8082d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 415623875 1250 415622625 415622633
    0x3110d020402070c030c0501081014061903201c020309030702060304080a031a0315060102010e0f0f0d1407060c03110a080f06011e08060f060a170106020303041a06010c 74
    0x2041d03d40d03c1500d04038402c0b42145441c030645840383c1c100e9030400c040d03141002940140c00c9202016104000c516100c45480840082d01c288603a50100e4112050b03c40340900b03094268000e00f401c0080091081c00203480f1900c490b41c0ca02030b40401d5a580d000c3c010510b01c401050f0341c0159040611101981d02d8046180c01150302540306480803141c042001030f40c450f807a5070611607640600b0030760205e41c07510948140060b556095100072660f03903030213110105410341e0007507100c3d9002d50450800e8440300a544501e503610751248502070310082c002c04a030a44020302c00c0c0226039003440c02c813508034281032960f00c400d4001c0c0400981041807507590004103004415400142401001d00e03079030b420003442e000034a03041c91240544040d061000920071008050004003a0105442c0d09103000c295541e80c20740007908100203407401c3c50b0400d5000a40c000b020b0351105140702103001c04421030f00f00d0303642d070b4504036903d200072a0042c0650044d0303100f4a150080c04e240341504208149070000e030550207519 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 415625125 1250 415623875 415623877
    0x110d020a0b1e04051b06040e07031a1f08061f05031b0d050105040e0a050309010c050a06020d020a1d060d0e010f050106180b0403020a030204050402011704030c0c080604020a03110d020402 82
    0x5010790300da500c490405c1c0805c2040e2410807900039402d5914a04203803401c0c0380b504e52140007400c01c100341a241c45101481124107407441c80414401041c00039a004903078003203820710356941c9600001a0004000681605002101c40103980d03a00c90b40903521600207001720b42c26007010301012565210054110035a0312003101810a0a08504c8002480d501d40f40802c01150158201c260140d08207100740804100044141d6001c1907080c01c010200542078a030960078041060401004203102003003400c0c030848164041c10781c40b0b0403a11030384a101a00c4800101e003010f00c1142540c040002c01c03c048801c111070300003400e940403413400461015a1785284c4401e44a00740c1004c03002070000217540744040c424902250003000e403280c141d45001d081d40c002c2102e1000320300010b1b0056840d100402c0440e40b0a51808191446512855026040c02d01d80201f403425010b00c192103451219401080500300418014015079004000e00c0e819441c550742c89001d00c2c20613007502e50040740d810504c40035880d140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 415626375 1250 415625125 415625131
    0x504200405101b030206100806040314090409060f0b120f100c0c060507020a0203250b0c0a1b181e09020103060f08031201080703051b0d0819110d020a0b1e 68
    0xb402800c6c0c68900040106030b80d220315400540701d680070609000200783c00c0040310520b464101c8001d540c400d0b0010201d03026128440000b0100c40c45c22610064107101030b407041c0320104c0212020310401209041d5150ba0700102d11155000790007c2d0140c048020541d0721151001d0040e083c40b42d20102c4a440d9401195003c8401c41c0c05600b19003e4501149801e102d0b5108da020060311010000441440004906101e8000c605021100007108800700108010b01c1c00d0656100282003500c040c0002060320804440c4114082d01e1181400c018161055000d0303451001c040c810104070203d0207080000c0540382c20f40d0241d0606540361000f2401ca0030181c07400020300003440081d07603107041000d42110500302c140d0081c405600522005d2001440209546843c000b138140c42900d080c440c100080d500c91040007000b000038400041074480912b49031503418240c0d00a031903030000b00010000c151388603030310304043c00d006030040411440081c41e00c0000d690484c18406201d007810f084145081c05101e415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 415627625 1250 415626375 415626377
    0x6070c02040f0609050618070905090406021e07050c03010212270f0d0206090106050607080d0209090a06030506070201092604031b0312090b0d0b01020a05070f0504200405101b03 78
    0x5c80c1082801d090400c2e500340d880c880b002c400711251410f60001031070042c0b680a5544101c0c018030200307003030044c0d1390140c9004c8a000e142090010360003500100320ba030702440c0308413218011460390403080e1a040c425202c0343d01c11440240e015541c1c2d91203c0c4000e024058000110420200c0d08407010402000007070f240140446c014485160034030806868136500501030006a81082014000307500c0780000d035800194401059a01c42503c6524140030340618098160042088420840e0001703543c1c010100702d81c050300c180d807070075214460224241d8203034031000b404001142e0196500c0885903003214000203000940a41056102da0717a480014581c0780d01681100402d08041c41802160810005044090700385540030340d150040c02101c0d805600e6142c80342550702e0342003a650303900a2006040290b88082502e03000c9445104406652140b80140d6000382d1074024409250602940840110640140901d0800d40f401007040132150440769020f0400040c0d1020a003403501c08500e5400c01c92003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 415628875 1250 415627625 415627631
    0x140c01050106021f15060807050d0e030a140c0c330403020312041d0618070f1d210c090a0515040903050a08090309120f0d050c06070c02040f0609 64
    0x12001e0f41301e062101c200c15844010789014070079200340c1d42840d0010110398040c10030022039650841c00340d681e8003c909034683c0d180c1c20f10f0504090030300d010006001842454554005000100301c1d0890540074020112109a0040805079510700c0c0142141c0d0029a4a8200b0b0096448040a510880490040c058a00341c0089400e00451505200700040c1c20106013609090501d800782c00c944041c624250088000c0080021a4007a2203292a040030f1588409070380720301d0f0400c480d004100031008550340001881c0449045101a80782d01101d502c2c0d6001024404040304420307540009011200c0f90300050b1107500d0f0b04030041d4441240715445840c807410300054900c0c1c03020010b811519821041032049260020800001382c021040da0300c1804907240451159070362911061451003020180c030391000b00002150302003040003400a00071070020b0282d0301d20003000c82c010b640500807001c2d20035140e00300d00e00180b1160310507030401142038002400442c0600c801102d2808503101c03500086103041e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 415630125 1250 415628875 415628893
    0x14010212040213020f0a03050405120a0509280512010621150209090c07020a0314030904150620010908040e0901154a010513090305030601140c0105010602 68
    0x42e040c9007a00706043c60440651510258440000c21131290605050034160344601140604c1307810810780c242024810301683c0d48281000000c5c11a8104082d501d10401030701504035a00826124803525021410354003420306070511f401c1120900c01407100030610343d655403000807100d040b07018404081c071002c0030204a001542c00c004860340c0e0396410001e0000c0c01000744060a440d00c1102590000352014400e03200d240c0b620020721145400d6002802070401800d0f449030220010004042c800821241001040178980f900c1c1c1103d1254410080800c90710094140c8510050310724403040b480343d000010710f1108a58407454240c129800002e20f29403080200300056600348980703084286090380f000215890100410000345030302e82c2d605002600268011001c40403400c00c0408c0807141032580c00c104054080c014041d20017403181030b124000000515500208501c00c5c0c21080307805d503507a140b45580303d1005591800201019410303484c010080c0c2c042442d030a11a250203400180d001d405854 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 415631375 1250 415630125 415630129
    0x91a09040c08160e130807050d051305030a02132c10050a0504051b011b061b0c0c030215040e100509060303040803040510031b020a0516080a0b04140102120402 70
    0x250050981580f61500190140043e0034181c1040b50300c2038604020000310307201c1b494441c20a024186d0014076611038504084000340d0442c001d013031100310000810400700da584081664411003005d011f50060721718a400544100c2c123401c81138010541d502d6100e00d0000e05601c0007007001c0c0000e2600d030160072000b07040c1c0c241d40d054020160040003460090110b400d00f511520380700c02c4100c5843ca4002d0f00f04500304803d074019540d13000f82c001600040c15001e820785c104000078100040c1401a40100c041e10045a0340c003510302e0094651700515281e488504581c203110103119011841d0040c40403d20001480b160038030070300b51040422004050180385480280024048080c0c00f05119400c00d1009001c120350010550f411614110741141b00300050450a400500300400981c000100e03a00724403007020340000305034050034410012140d0403201c43c0d10700100807415025075150ba40140b5028004150305140064010b405850b40710401c4c00c40040107422a800a00d00341c500b8181241008298 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 415632625 1250 415631375 415631383
    0xb18040f1a0f010e01180903020c03010e01060915030b0a0c200102090f0109181a060408070e011a0f1b1608071517071e030603140f0304091a09040c08 66
    0x10882110713540c2d09541840900c0b480c100f400741d50a000c0559900c042010b040c401c01041ca803191000d00208443c1e210100c10074043c081c2c6006001d421818401989001d5040d110800c085907004412280f540d16401c0c044400740484940600410070002d42203c00045c1614205140502d01400140e0b256074050a1000e000c0302c5803038036414003421136010130000e06442c144200c103191025000171300b105190441c84e0030368116540c054002001040204415800141400a40c2d400f051026000d030b80e500c0889000038002144003c035087d00b440114500205500581031000d01c51222028180d480e0700031501e440312000000d504076407000b4080080403024400d15000c0c2607580011111905c2140c005090002a64030341040c4050320000640f10300e00c10b0414616800072084640300c1030301300039001805411180002c0d100c00c11009042c0c0220000000c0c000000f258410140d42018500000c1c00018102d21070040d007410340c0d5180250503070361410703401071203180b160303028000d11402c01c4070081c54 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 415633875 1250 415632625 415632629
    0xd030f030e15270d031d03030c2d040e09100f0b01110c09011707031502031012031215080a060504050f1612060f0218030c0102010b18040f1a0f01 64
    0x1205000f4100740f5030440c02107190884809213040114100418046250304c0000f482d007502c840d40808020300000014000c000c000242095524014a61540b0130b4012402c50044c040c41c58084200300811101d0140d550950348907010031f0983d805400101c40450a4400207514404626699001862650780081c1100d26600082009010398254500419103441c0103000d10803018003000060400c4003c10007000b8042c3d94030412460b00c04e040041070102039001520b8403da2101d410f840826411000280c004100703401d541c440400d01e00502032100208500703100d1450301c0800c1e882c0414211001c111020200307103c1d01d0001200d2501d82040e074240300f100c0d24006860b400c9023070b1a03c020070b0000c100c030b4251044c04100d8183c45020b40361210080840c52242c3d80c0d094004070b07021900ca4022814946262010380603030b01c0c0c8030490401242203075a11801540c0c808101030b01d0442480081c03401c258424403584c1d000d40c001c0c509856507020030850b120014580b00b0300750108045404e0f04401680 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 415635125 1250 415633875 415633921
    0x408030d09061a0d0b0901110a030203040b01122001030209060408060906010b07120f050d18111f050708040905090d180509040201121407050d15050d030f030e15 71
    0x60050f034641c0010780400c0010b1300180c802d82e8000c0100349034440a51094140b402c520002a40e512088000035019400845045c1c84800c001400001c40010f00c442000641e41c0c071500140d1005c0c0b02040710160924101c05541c1010760030b014940032a11904001c0003e480c0d080c00600722490304182051034903005820400a1030700a000803400150924000c641c1c2602c076052003045c241c0010003c0340c1c54001c408100500707070f04220075081140008881c9045040c043c0035043c0c205c1ca82031042c0100c0a108283c0b00f071076089051111007110307206102602c0018400c00f03520f07207003980e11582e140658509a8801145400101000055580000301130610002541c00100130500d8440080e43c00c076001403000c1d040c40f115000f0740c000c160340c0358803545c0c0c0360708075004d40c1c0b1440c01c10120052490304000f4808040ca881c00070000181070258071300c001100c0c401400b18003801c03110ba90440d100c142101207101850b8980c403804081e1003040c8501c0022142c281d00c3c1c20350a1070810a0116003039000c0ca103000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 415636375 1250 415635125 415635161
    0x60b06040b0a050a0c020a24022d070302030d05040f0801060f1412010905100c050301051c021207090c03110a0906181d060907081005010f050408030d0906 68
    0x8500070080c0c40e03610226082164440c01c10340c0d81940c1141070030100960007070702507401040c00c625524160703981c080c103004c0c0c00103140d45016080e65248101c6d0510f541c00c1004e100c0601003a04a913886132800e41d0004c0944082e10365943c0883d01e018201c600600c00300341c01007018851840c084005e04028580b400c0248401843e206500d0344243d00c502850401e010b24000c01030b43d40d1210070040110b009148002c10010607503080194030b6844120b00c1c0d8001604041d102c5802a114000f6a4180e800090003103001d03182e8841e02640c55004044200d0b0050b030600301210745200c0911044004040c44140401c0401038000c00808035600d540b10a444a80c0900445d40c1c15548a86200182c03050750a01030085009010003942a0505078440d8021600101d41c1c2c151901494000a005010595511040743c540e031000b501e052800311410b038207401c0342c101c04001c0d641c803035500081c600007141482c82c0340503141c0042c281144e2007140741220301903c0d15035400801090744150314a50183c0c80b00e01d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 415637625 1250 415636375 415636379
    0xf0c0406090317070516081902030c09130f0606080d0f02150403050d0e0106050405090705060f070318140a0902030c070f0c211502040b0f030711030412060b0604 71
    0x7404031965800040c0c025102d40f51954988a550412684019081400c5840c40d2400312403400486840340581440c40c0555440a1003400c503400d004140142c0c010007420b442c802100030300c240e0300030003044446000c0c0c40f82a0200880d01c034034039481c82d1a0050002142440c06d04100034906420340300340c402003010441e00941000c1d40411030040e484091300c103c4441c1e4959003800c45803401390712458506c2d5864a844680380318415486601202d10640b07043c80f0f565510321115803605401d1080070742191081141c0f84039010a40d0040c80301c140b0070304216450484004000312070315850307084564001455008107110703240061081c4014186400701794075610304036000100314081c0440007040d01d40e00d825000704110b00e0300918405424510042c01c0d101440100b401201403290201341c44000b5614000791401d140d900840701540c500d0500c1c0ea1900700801d10f211101e83c4028030010400011403c01010f903482031000340001c04500300b412280a0950501c10129454078540c00e00c500001c0000f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 415638875 1250 415637625 415637627
    0x2107140109021f020601051c0f0302070b0301140f19030b070908030301030605060f030d020c10020120040f150504030b09010e0106142803030305041a04052a0f06030a0204031a0f0c0406 81
    0x5030004c2549d00c940c0c200c142007907a01d0168500f4070a0342280c48116404000415184c2441482c040604003c40e151528808880c0510a003a0741b80003501e60302c40c030904814004038410300398540d001106031800c000000ea89069041c190b420a0f0001ca5020b03884d2401d0045a19107444070070744d040412405050701c151103400203592500030800c03140c0640b070a1820500c13818002c1d806001a00c1301481105c02c8140042502189688103000b000008a24900003080c104c45010300341200420035200e4a103002d09503200c0300483c110043c0743c1400c1d07640394113009104540c20700030f4070001c02001085000d0b0180607801c20010750107541071207009020319441c411000460314115022a0740500b4001038684079410442800c0255001c105080b1819509120411034009034402e0b0701c81207081e10740e1100d801086400c0d0340c03403140200c0ca40e00c540d0038a0038240c10304d0024011038001c0030101c00186025035030760320841a0b261008003402e10004080130442d810b18448400d6501c81c440d0081349240901b420b070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 415640125 1250 415638875 415638919
    0xc0f06020738070c060510030c0602070303080c03190906060e010b0f0403060b0102030915120a060501050a0311041d011505040302090f0603070b19022107140109021f02060105 77
    0x14801d00403001c00001c903203c18094030015201c180c00c807400380800d1030302c29030316030402c030080c4400c4644284080c400a0024800f1598800380c0394169942000ca4582050000c06a000903042180f850b01081840c100808203214903000c60344281d10100e042e6181a683d0000058168410071440d8005c1100e0300107414864200d50a6a600c00000500300011a004130720714020038031801d03044401c0c1641c001d815a900b002034100041090450481e59032181d04070019503505128590200d28280981c00820f030203600440504c121004803c0e09065544171000d07110200300c100e07848150075220060110740c4155201020003060b50038100e1605145034041103070802c0c0100b40d02100420700010030000c2c1d505000c44002030060400007a19800c01ca848a038100c407080032084090300c03961100404d408250000c009000e041c039605103040980c10340340c80d0030074002c0c1078401500d55603071400000103982e480328240e40050b000c401c07054081d50160000e441c00e6010f801c00392060314086800180220018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 415641375 1250 415640125 415640213
    0x50c1f14180901030305030115020a0b0c1612030c1d030c120102190809011409030f0708040807090b120303010509060f130e0c0a052706010c0f060207 66
    0x31000554420070018448901400110035a5000507607100020602d50b0040142d41070382e4107501d010f008000f43c0d0f03001ba40e46204480d401401c2500701800141019004006071049921524502414600c0b541c0c9010807c1c0c1c1400b9001701180d034506910150030342c00a201650722003a0b02070111303011491400a0355405101400724410840c4000b40c04001c0c0b42034054900604001558800309292070901800407401150006429880c0080b12a45442d030040c1e058080e0740c0540c090342c608a666003110306994000102540d40090410001401d40003c108400c000c005590000540343c22490401c8005010313010742d03050341d44c0203100521007030352007003010f0f5000f11044411049110305d80002ca000c0501000c0c0c108c0055140000741500a03002060503000c044084840d214126210300802c5a011030704102003816040f08280801c0040f19040d0080d00454141011241c0403910341e601c10444407500350480c1e5a80c1c01050450411640c1505402c0690b091a5903408400100d236240c01c3d144040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 415642625 1250 415641375 415641407
    0x23010509071715010e07080c120c033105010606050309031812011d0d05120a0e151807091b1223061503040c0905071b050c1f 55
    0xb41c425542e181010000d120200001c00742041866940700320922401000300c942e03001091229002940c449000d904031000000e4129901c041a10341003042446a00005c0041c10162200e02a42c5521071003031011021120402c0d0304441c811849190103400d60748990b00410a02400f48107002c1245400302c1902c01c420728101c0f0110301d1410000011720004000198003030309500c2d00c001c10301c103030002e82c5a048494026808440d08070fa01e1020481e92403240c1d215a0200b4404180410940620b68120303510700304840c0102c80c4c00040c440759011000905507944812100d00610100503003a09219010042c00a034404000c2d10380e01c400180040a0003000d03040402540d240c3c4011a40c0ca50751100032140031614129142e5140341541840700345094070002c1c419070104012280f401c41900440c0e104650000d1455009450700c8060360103003002411030010f00c401d40440117134100412182900b1240150020803044501e50280a0005101a2440122052011050040d41d004040013040d4983d13 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 415643875 1250 415642625 415642649
    0x1003050609010e1b0c030d060f0f0e0415050705030f0f0705030403181707060e0301112b021204031e2a0f0b0f01090204030b0402100215042301050907 66
    0x44003101c0b60300401c0c113030303c4070401c2a0200341c8094418000006d808560540c07041048a203440d1070803003200800030700c08d40c2003c207840303123051101020070208150400e2140100e00c0f0303243d040b00152000c0c3d4104480c8200010070110400144007030051702541c100820486a0b000b43c144a00300600c1440014009014002c10b050502407046a03c54254002c11070340002140601507210082c0d1140e9079441007600048800e2a07450070b074641886000d00706500c03000341c04c3c600301203101440d00c6c0d0b50300c0d140405203078264240e01c06801d2500d40011305c0082e00b081c000c10000d00d05071502620701c274509800c03d80300700c0a0f130113003102030390700501e000b92100861758100e0809012008420840b246200c402042c1c1c1f41c421018008021480c0400ea0082c0c48061002803280e8903071525104034005e5100241101441d180403502505103000541c504150510580c0c1c40f881103100b400400c90000c2e00c0480d003081c0e184c1c00310300d0841ea41d5102092031000710030080c09641042403c81c5d03901d902601855410b080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 415645125 1250 415643875 415643881
    0x4030b090a0c0305030405280302040b130f0f05150d06021308070b0408061f0614070b150f04020c03030610020c10050a030f0b1c02131a1003050609010e 67
    0x34080000c0d0000a500034041a0040d44a241054403a005480b40354020596110309a41701281d400700c4030301c4e05a0341400300d0100d528580030003020300810241c035a00003c58080844604806000b0100340b18000880400c1e0941008405011140004d21104180d414407400c400960342e183c0200d0042500694050f85504010410004008072580411001d1003409000684405904082c00171240b05d201500c40d5565900060b01d00c29a515a1281d60802064824440301d030060485060710039150806d01d050030b035207955480400b103040d140360000004a400c4140359103000404152901f105035401e6041000c2c4880040d80c901000c0d014922410505140f06032851003004809001d0343c0c0240108844264040060800c0e4811075070703640003c4c2410039400d0054150300401540f0000908400f4141c40c3e41d808009001d0b400303000480c0d000d1808100758011140d02d0082c010901c4a50b0031000b4039030400401c200000f00340d4a01d04040c58100b00401c00caa40e14440c850341194007841044005076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 415646375 1250 415645125 415645141
    0x80402040f0204081005060307060504090e0c120a021002121b0f060c0a0e01092403200909150a050603070302070203031209060907030b0604020f1c0915050c04030b 72
    0x10800c1d1004003800c03807010500041c06880003404c0000b100c090242000075803511028161203046900440011590812041203406481c0d44031081c0c070005607080c0c60003114104002451a4064005100d0b90b9011800203019803a014816001c6c406460004020550350b52103140101d005440011a480c5080001d90742c035100217000b01c007200004202503692614000060a605400001710040000c0b68404644015401400104203031140307844000b103241c4c2e0b158144100b03111040103800030135443d0790704ca40d02420200d20a5110640d2070311441d841d04d10034001d03c0b04652008103000c071404180c110080c51922200300741425a035040e80c019131303a03694030502170f0040d120318440250984000128461006003001c60356014024007003d80712181c0350954441d50303402c0c1601001d01030140120108411740740950081c0301c000c8500c004203003044140254003d49880750500348040070b840c4c1031168100281d03c41d03000a0780f601d0000070403460910014000560045d400010310550350f02d40454110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 415647482 1107 415646375 415646381
    0x280b070306060206221202010c030b040b0f0909121804060e0402010806010e1c05030a1b030e0105090f061c0b03240a021218150103050d08040204 64
    0xf90316400c0c0507642040010344081c2c01c0c00c174002c01650000e03000080f185441e4070140c000180403002d901000d4155601a1601441546030038040c94988e503c040800d014514291150446590754040c52842c06820401c4481883c0b0081181a510300d00000300c26100340040d038091224541e90b004511071028255002808118840c0014016520402c002c507810000208030050b580b00004090a41d01110344c02135401d600002000303544541c100c1030b91490800780c840000960001c6403002062840c1a078002410803c0000ea012402d6452062a90300c0241c01803282d5911108000d40b003860075800d900d081101810595120402e1402080d01c0580c500082408100c07007291661446007e00000c16503824168244141c004a9406500c01e03481400c100f46003006ca0903130340c1c80c80da2030315120001241540c400b0800500000c0c601154802c911101c1e414143c5a5840f03520005000d = true := by decide +kernel

theorem cover : BRFrame.Cov 415467625 415647482 := by
  have h0 := BRFrame.cov_init 415467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 415467625 ≤ n) (h2 : n < 415647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
