-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5293
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:23:19.814055+00:00
-- url     : https://prove2.me/submissions/4d76f92b-a72c-4f98-af7b-7f18075e5087

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 951798561 ≤ n < 951978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 951799811 1250 951798561 951798563
    0x180a05030301051c050a3c02090601021614010201110d0902040f0507020a020d0c0f030f0302060609070c021009151701080a03090b03090c0d0c031a190e0a05150103 72
    0x81000408000032074101041013083c406019074201200581c007140001c40c15807540f41502004c100c444040c810030070000c60030400301e80f844004607004e060441c980700d003900740c0205d400d1004080c1c038900014400d8000c403451041d24000d06030b10380104090790007074000000c0c414800c0c0c1c0300c6868204c66480e803c06800200300480c0300d00d1524030703a582003a41911034036000303400c0360b40102001c1016030309002018080710f02c2a903d103030140307000080340e040b02901040510320440c04502d60300102c1c40c1c06131805402900080c41000c01400b00810b044d0712688641800790101c4051503001001c0c0b1098401181a030007808003800c500541010803904440036103010f0308c1d1240c0d80155aa80c81c0d1126440b0140e00c50001d00007407441703608003d02c0381190051a0007000c0d031000d9581001b07411b00080c412000705403040301c1301c0c2e42c405010018048007944541e00031406082c1d05c15039150054030154000b215004601c440c65540da80001e000c0d10801c6407820312a071050840b42003020503024050340c003400f448 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 951801061 1250 951799811 951799819
    0xd0e030304120f03090816020406030f03030b1c1106090103090b01081e160b130e0106080a0e03120a0c09050303070b10050a03082b02030a140a0e15180a0503030105 72
    0x1602c80f40041c442d1040b10407240d000a452818901c00385500c403c000009501030343c0c0a9107444020000c551003004c14041c05109440c002802c0300080207020b00d10401c0c0b9031180e0b010300b00031029070106800301d090254a003811240d081d52808480d005800511303003405e001d400c840070700002092243e0001400031000e0340c145911103100702c900fa02280d0740d00c1701100341c0e110b444240d07104200d40c0400c030024203528140310005e103545585441c072801d0001d40036486000000c01080c2881032492851140c04505c0d000f004c003551030518204058041c0d0900640713542030043c0e44a008805203440303480300c3d0300642402401e60340e41e69200d0426140804094450001038688140c0c001030904d402c0250908803640702101c2810591304981c2d60504003c140302d601c0c00040729005601d00c04034036100440c442c90100000088203150140d4031800c2d00030082c43e000e4071030714140304050848400140864040c1c202500c00c0559920020260301001e40069002141d02c5500d50782020480f0210145d8142ca005403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 951802311 1250 951801061 951801077
    0x4030206150a0f1806442d0f030c01052206020304060209041b02100612060b0303070615140901060504031115160204061a0307050d0e03030412 63
    0xd002c00c54070700401d100d030345000070501c00100150725500d009074800c1d540103c80060303076a640b00307440040c88102481740c050425200344940d540d80d00fa24010504c0051002410510741c4070303040b8480e1380d141c07829240b41080489040004e401d0641400064034507201505440c104060350a001d42d40b40c00505480c0d800c1d50030100050882c0c0c2000c140001d0604e0805007000310314190b501c5810083d403000d841515155002c20441c1e000f030b2918000c0d02640d5410b50303140c0a80c03800100b0005d082c070f02d000e041a54540e0030100200030703a404c129a4a07150310307081a80010204042d03000686940300b141070090045092501884552101c5514503040300c1c01e61303d00c9100c0a440d04200b0012034024022400461000d103c01c1c004a8510711944c0c980380005800301c000d000444080d8034880c0c02c103c02c2c0000340c0c0d06040881d400c6007054050701c4000d0425110211401039548a0700303c40e4000200502c040050125818620103810342290b01100410001e8960328205410b0440040e03940300008400714001c3c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 951803561 1250 951802311 951802351
    0x70f0b07110d0f0b04141905010c020606091602030403170705070603110a050a020a022e0c020d03080613051015020d0e01030c05040b0d0501141813020409080304030206 74
    0x1080b000503403550120034907a956590b030f590190604000752050b508440f0850740c4a103424070800c808151038080791910001c2c50709078506542502e0f154184501150000001e01c1065110003001d80d41020012502e00e265605071a012491806143d00182c80c601c40f0400c2c03401c1c0601840000d140850080703094442c3d2070713187d610581c25662100d56010082e041001440002885180a000c6030f004030310603240c1002c40c0b0b40006010070b03050300c40194440c0200e000101d4181824a00800c0007142e4200907241c200c05030005501c82059001c040d0500100300d0000d0f61603500e07243c40154a11682204100034102040f0b20503c90919005003030f900880510404c084a0000404c203003132002c2c40d56480300411f080b00044002e000009008014807005000101e290340d403560140c00100050200024990307d031100b061401105589018041c0d07454500c21179005421700d6200754420010001510400b040d44003140c004c00440340c018290745004814001090b5010696070b00074450050308d82580c060f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 951804811 1250 951803561 951803569
    0x9070522050a150801030f02120a060c03050703060308030105090a06051005131d040f0213020a03090c1217130f0b0a0207060306080a14150906040b09070608010512070f0b0711 77
    0x3c800300e00301085000004000013805096508000b900c0905081c0c4403503024000c0515100c03084a00310b90442c4c6900c40420300584c140316043c0d2041c0b0600d003d0120b1855a00c0341e00c203511043c010180135000c02c800248048400c1e8001100030880904080d014003500308004100750040170b204a0b20a000300c500060308050041007201401a2000e00c20039500c0e01d58441203007000d060402c031380141d109640c030181c0300c2c0c0d9031001d0702041e80710752004584d841d0b031841e2075082c4003910741021103910181018040454081460601f030031504600e801d9943c1c0307980c2201000c03100b042d8429a07146051041c0072030380007600c8018140f10f40c200e408407086151103007416419190785001c1d03810316520070007003900402e0440704080d04403c0708034103440d00e22591010000554404840c01ca0f5158025028801000038030010517620100c4c810240c0596070400320001d05200301803013154800c01200340480700840f818070003d0010006a1b094443c900c0e0b56103105600390300891825a43c21a41d81d504401c0f81c20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 951806061 1250 951804811 951804839
    0xa05161d010501050702040e0303070903020f03060c030f070c0c03081803060919080d0f0c020d1107030f300210060302030304051005040b0403060501210302060609070522050a 77
    0x44051580e8209a0815004540a4000c02e4060703034055207816000159420a1000398000d21540e503c50108a00b1f50051220b810702c205c040301d0090340100304010710251342c4000d0300e810003078070005445941c5034084102c2d01d9600c1c8900281000100480000400a50000072701300814a0031104540340d89600406845c0c0d0821a4072804a0304034888180d0341017418040c20190507c80d10312a0704006040c5400e200300d0304111401c0d407825580760312051106404100070601e280591030030320301c051130207071000307071660803603c001051540024210301c00c002035100f030940403075000c1c190800240501c40e420302420142054440c09802105581d03003d500d454011242a00e8018000318034091401c401d0005000c00c0b41302c107608002081c0b00102c0c0002d140e80081004601503440811a03505200f0301442c20a640901c466110045c4070440000030340109031550b0090045660311940d9460b028261080c0c0b0850756207071107501c804401489003110945a00040e50300642c1c1c500a12600c80d00d01d410860 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 951807311 1250 951806061 951806099
    0x60702060711150a020d0605090103201804050703061d033a09031d0d11190306090b010503060907170a060f020306180c0f09040e0a0516 60
    0x40c100900042066001d8401d52805412160441c2d0b07010007003101e8000c1da500242d64004182c0d400140400340e5644500501003e0130085a45200315490350390b542d00548203d102d803034010290008468405d6403200d042210f004242c880751080b9103003902d401c80d10fa04444c081261410315040c10b90794400300100c090102c000c2550002d514004250170083c00d841d00b000407848908000000c806c960400d180c05014030310040e440d0204100d03e9510300508601103c080380002c205d281c0c20300c28100d40d5891010512150081e003503094090008003c980759051401780303006034103030600b800030800030250f00c042c6039680200e0010015036251400c142c0c8442c001d903001c10007070f4018041031202010014210661004890495100e0301e8956107540070f0344c0003107841e1104c20340c0c0482001121f0030304038400e500490300c4226a501500c0c0030244485070740035100c0c840820300008070700240b25898a078407040422607080200c03002004a0300d0300c41e03911101020004900c1110320000211620428030402c7d02c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 951808561 1250 951807311 951807313
    0x1401060f050f0c0c1005120f0606091212041409090307032a170903060604060308160201050c03040306091a07090e040302210a030b090408070609080d060909060e060702 74
    0x1c003032451182c4805400554001145000791005000680d07100801400e030544240c5601340c43d000c01c032545001c03010008000002c410306000c00c003d49175848004590014104840c002e031401d45440e201c1d072030445003004e00d82d03c0c803a0008000c2040440e00010f400b070790b2001c850102c007c2c0c1c0d0b8080000d4032170103400401800719101100c8001814442c0c0c0c1c20b840c80005110010a58003800c4e103c45182c01031580c2d000b00400c500043d540303100c1c102840b007103501035030640b02072019525695414040303128085100502040b1130b82c01008580c071401c203d50880c3e2881080700d444640f2070820500420740c0000031204440704c1030b503100400c400b4415040c032900c0d6680346c0300405132500c0c04640c242c0754028022000c42c011540141d00200d10070014966000035552090344422042401600300c4024142c0b00c3e100314402e1082000080507407040320215540b0620100b840d071035600e840101e500175060404201424604041820074403a48900840c5020308002c1c4050031107465400d44a54040e500c0e4401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 951809811 1250 951808561 951808567
    0x1020c0718150b09060a1e050306040506090403080f07110106150e090f0403030504020d1b0f082b0e12030915250c1502030301080709020405010801141c061401060f05 73
    0xd51400001801408902d4100141f40c828a800950448600d21030690085038020007440300e141000d01c00d15512040542d11003405050948010f012a0001491201918514400561400e00c138140301c00c00018414002d10180752103c610980041a00d01c2c40800990603a00c807040034a4422412030050740600180040e41e05c9540b400c41c0600002030040e81c0210307a81c0c85100004041c140100311070086408011000e605015803a03003484000d07809a940c561224403c1a00344001a80310751001000444105000040d07046c2034800152254801e035012100e80e290300e9140401000401032010708807800d4a12508640d4034180d18012040b49020140c01505c0c00a0700d511a40f96250b09140980542103c07503a075003540560b00100a10760701c0040c1c102000410114401b00903040191940c20b40039410103080c80c000a085413414414940c007050364121445460316968100c2c0720030401030100c00c01d04100303030902e070010b8900c2c20300da14003004001000007259407240e5110034001c11140d507201d107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 951811061 1250 951809811 951809827
    0x503070614041e0f0209041a0708102d150f020319210507020f0f0c0f011b05010c0f020d02061b0c010605122a13050901020c0718150b 59
    0x207040420003400c41e402c03131424542202680d00c1c1109184510320803d01a112048a2901c184804001824071b506000d048020b020700501185a803806503600802c00880700d44412400f2841d182c000ba4001c0c541a544640c04607010101440f0600016441d4035114900c980c0d00000700e0b1380344980147c031042d5041c4800c586541c188a00340240396802e14100601a5810b05e0036500c0484005a9214015034480ea002034000c9401744204808040010301400400f040039010580034035038404014100700841d18100e00542802a880341c1140d00003000304090030802601801c8401b208010030054030030040242d0f42980f002410900c83c0c2070400600c070304401405c48031a000e80090402c1105e0f55201c1d100403801c0d4907062000c460b41e0b0444d4000700842a251300c00071600c3e059109800c85014807001040c6540c0d20f0718081c020307000c041410300181c19030b1000d05442c024002c0700c2da00c1c03030540640000058000900c0c1005044222080402c00401185828a40302499a885040c0d40d03d0001d002e80740d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 951812311 1250 951811061 951811103
    0xd0f0504090b03030c010c020102190c0c0509090f010608210c100e1906050a0e0a03090308130806040b040b010b040509060d02041103010603020c0c012105070e0d050307061404 77
    0x40000031000c3d00300c81c14018000622401c0d5515a8901c2c00142c1d070220310103540254441404a6840d010300300140382d9111900c07040490307801400381e03074092621140441c0481e0001c00242d146481c0a900030440182c865282e91303101e00b00c40c01d00055260f0289000c03190515444200da00355034105004014807400ca0311040003a10701e5440c400340714000c98040e0000480290782e40501d40d41b043e400054145826900b00c8110344070709098814551040107114002a0000c03d21401e40380c2080c03800392a10402400b502c84015190840d0340706010344e00c14442084840c1504270701407882464804142e80c1c132041c429405005900c58260311995000110303846040c80c2d00c601d402e260000c0c03c0440c60340380502d8000e0107584282c2c008070010b940060201d14401090044045d00c80007440d00d140d5600700248442908810b0034080140d90b55544040784040d030092018030405940030b002e00f241404541030450300ca8010340c030700355285410960b1b2100103900080c1041d00c0b1b1070303001c0d52079107405500c02141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 951813561 1250 951812311 951812321
    0x90a02040902190f0e010b07030f030b1f050c0606030303150609040e030a050703090905070c2a090f06090e060c031905100501112808160b06030d0f050409 68
    0x740d0f000340c0b81c0d0324030903d5002069410380c0945612000c40c1e10440c0b422000640d0380390160b000e89880101400080000ba500c022061103600c804c0c5400f0a100000b08001040520140f81401c1081d00c012140107002ea00400513003540c000c04402d459aa68800e0185903c0b4802158902c0401c02c0d4408000d035185070041c0035042b2540050700020350060941811071860748030000f5034012a40c085500d80c105036200314400c1c050560500c007840103080240028002c0003064a0042000c0003506441a84000078400d00319030a659010556845950350301480c02002c0c60180031041c541080004900d4541d03600404281e0a0450020003007540d40240c0044076402c081c19000400c0f1a0101c1c1c071101032840c0c05814052500c41c2c01c60b01030070380ba1000140c030000031444c1a2078181c1020f50b80b0b5000000380102107555140844a0965800480c94002081d00c1b0f00b0400228500741600d641043c0201285403070300c580c4050341103030003c981401c420380e03110746a041003400240d000c00c418805a080e503041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 951814811 1250 951813561 951813563
    0x20f04050912180d050c030d09060f051606052409010308031302011205280c02060106120608011104050306062d121f1a060d0504020d0c0807050315090a020409 70
    0x70040c040e1081000103030342c504c4c40800c02d0b50241d116840c1c0c810549401d05c59402400000d0034902c00c61490310402602403504c1d00c160405000c0d021818200c01078002d40e00c0d900e000d9114408000c0c07441c0030040d404280b000c00b48840301d0040d901d03107100b50a04005a025041e0381c1c0110ba118159580c030b0400e49021500303414124100600414221805074240c00b46074044d0320406841188280c0c5182e8010048001c555920341c100c3c2080e0302e90720b20781e4001c40c4c014103481c0c580c0b5000c81401e62558238180a4001e50f480a41c2e40e610b4007020740404440c40002d0b000392402202501c0440d261202005250010208510ba0151480803a220007074607240050300c40100140c01001c400c41d501c9116030502264840b04154074481d00000c40380801c1c58031548021046006060500701031160115000d0302410009042c41556400402c1c15581c5100e0031072846580b011180b40000d4440103040d0300d5201c5441060b005e03100314081e4000e8032500760b045078482c0e100300e4028001c0d01000c0d0200400f600100314 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 951816061 1250 951814811 951814837
    0xe101202041505090a020d0c0507030e210d03051005030607120f0b0a0e060405010f260705040204060f02070603180b04030909111b0a05061b0408030a0c020f04050912 73
    0x10f0b20f9120f030320000784145060080140c803a0302c0c803c1d09909a900010f030120800008011090010307801004050420fa015141c80c00700342000c42c2d51044050603001003443c02d01c5207610b200807855146c0c20143c0324030f00040b14046003c2d81c0e00280741d500c020903030309100440d2400198581c10300180e440348030f038601840320101d00706c0b0f8a0404100d440c08543c011210ba010304908000060816004290040c81061403c45a20f80b4090604440441516158044542d003845030036910310104554400741200820840d035455440d41c015201c0301e03626030b10002500810100044041c000d219600b200e880190140d40345144561740c0c0d007041100200308030705200c1d40700f20100c0c116a076032154100c03160001c00159580c0a1255540e580c04c503859801651303560000414800141d8041f40c01508984401404400e12140031202d100a001d103400c030440921001c07030200a46584905111702080c020394015982d910a00140020b855003147d0b40502e50744446a030350082110300004003c0ba08243e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 951817311 1250 951816061 951816101
    0x90c023c0a020904030e0108060315074d0c0a050105220b13080703120305071709031b0307240204030f0b060a061b02090c0904090c0e10120204 63
    0x10b40000d165100c10349003680051035115040881e56007141c000c0d40c01c450b0450007444d22000091801c8060000148040200043c000a030b070041003c00d1211244100d04000c0d50519800d0600c17002e17000801c03080c444010841515811006110120304005401800f4050524690074240195104da11000003100c85907000d003142c01d100d0411b00752440140050308840c0e0b980e079401c40408075030060b0941001001d0380100f40304100051000d0b0612a0088080c1808140c640c0c4680003524040070355900c5102100f40002040f0443c6000b00040c125074400c590403042140700c4001c102e54078014104014620703140702c3c6da14a620314000925003414100362101500d00f13604c0e66291502003a0f140011616030810805004280c0780021066000d0002490f03d000c1c070340412400c0501d091580107021340900c8820303001c50031100409003100c60b2284c010300188169803280c50b008845091510401c0c0401d4001b5001c01d49042c00b000d4070760708542d01c101c802c4901d090300c0d40801004020342c00e00014004009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 951818561 1250 951817311 951817313
    0x4090203090d09080d051c060b030115090f08060609040618110901050123090102031e1e090607300504060905040203190203061306090c023c0a 63
    0x50000318031990700e10001c0c200112000c1c10107408a0303000d40021140c3d40041120b032a000d98020709903803030303900640b50540315081081d00c90b80007003400d80c000e00b0038501c00000200c1c8130055001c003417446050550f0b90b000160360365000c8000d1100c0074000c00301e40340c000d0340200368036260254920f90401d000351710000c0e030340c1e40194818100512503030080301c20629034640030820b0319145102d11b0040c0400e00700505c8900c0301264404c80010070901000c1707030000214002c2ca00783d1080080d210312020748445090102c144c1e40558020b5000041c11600c10300741e4008101720341c1a80c209494004401801e01e508008035031761030009500541c0d18034000c401c807843c16903204207010880d400d40d23440640c84655956062076001484803015410850003980100180096002d840f44038140713100250500503140d8441c43c0000719480469911a60081d0030f048000c03a000901c0e6110031034040f40c640031902c005c00c1800340d210402d4251034461074402c00300e0200845400d00074101c1140440c0364002d40b00e2100103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 951819811 1250 951818561 951818579
    0x803012309090a1a072322180902090c0918010905090607021b09060d0b09010501050a1205190807062f07020d080d0b0a03060902030c0a030507031704 66
    0x402c5901501030b60000451a003441842421007071035584542142d0414a40100094200e500048031300a00c05031341200001c845000304243d9640d4826185401c00781c3c0c80b0903a46080103d0b0b5802820252a042c80d0403d16400c005e208100e40c09601910300c861550386d0303401c82c624a03080021015000500101d540f460401880b00e501c0c060401c03480002160304016407414a4040010b02d004295804800082c3c1d04010710380c031002d41030004440500160303840b4000304c1c1c50500c50110003091845540c1c140215410706422060503204152004440c0340d6848519040000c041c0310040c2c00c5410001c400d80381009004080070009000b940454507080c1c680e03a5481c22900c0700baa464022000c0c08000c41422120440c401280b0420340e04a582484519000105105a150707001041d403d00007070200c044440075041038000711401080342c81015581e05081e4054030359190304a1090054420241230340c42c0c0038000506803600040140145401d5645a4810f42c0e5080c11444046134240000114406 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 951821061 1250 951819811 951819829
    0x90111011404033f200301030b07050903100e01050c0a120507090803071b14100e030c0406060804020910030f080a180602010b130204060509010507150e030a180308030123 75
    0xa121344c10404404404032081d0101c6200b502d40480074010303074030488a00f03580e00050380d065940022401d08076031030300f035002d032600d02c600c0010a41500581c50030011a050540c45000400b0a41c0020702140da2150780050943c41410260b001050340340d05031040d151001c0c3d014551054450410700c40580d241e442d12071540d0001d1008072500c5a0310001c81401e845030504030001842d8081401e400940b40c02e00080720240e203054458104040c00d442d0203980ea40400c605440d00401410070400261580340003000c5100032103060380140c502c0c001041c00154003070240c074126034101c2d00801d00c0d02040e40d81c0d042d05621284c802e1b4100401d207a258141e200c04188250300508aa800000d03094144105100b46451751402409050744180010020ba5401c41c0c1110140882481d006075a50890b192032410b215200300b441410b5807030b002c810942d46000100614081c0f020382c80340c1404020034030f4819881c108074000101070038424070042090010503420070003030345120401030001c2c403804000b040c0004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 951822311 1250 951821061 951821147
    0xc0306090818040c05030606030411060f0421020f06031306050c0714010b130e0a0c0e06011404060207031101030b040f05180601150c080c060c09011101140403 70
    0x200000c0e1440306070070560142c0c0340500160740038400f030031310b46001400ca03001c0200352900400c8d00100203400c21000d400216107985000309900e40f560003c01c80200c140d0428000e403400120300b0391040c801c407840d2800401c0302c0c590040801f5074000308501404100c0d0070107820b4002010b0704610000018280e0f0140d00d02c280341e07280140e9100c900e0341c2000701c40c0111a030000e01c02640f524460300310382d4407894543d0108180b404404140d01119000321443c7c002c2e608809003039059441c4011a0000880384c2050080d042640d0760400c0c0050241c540720503104174455000560311003c020000107469080344074890405041c000383c842040d50111741682d030000f4441e58266502c03c2088001042c0c64189403414005400401856040c08603942061183c4070100050280c00c1705e8810402c00e00b0b9007122072402445050300c1c03041c284901400b8050b007200d11014045519030042c002000c070148501c1704201d407100c040b06165107580d10161416110065012103519126800c010b11140d000c02c0501c500e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 951823561 1250 951822311 951822323
    0xd12050c19030e0d0c03140a0501050c030a0c0207061d0d080c0601090617120c120403050a1509120806030f01020a0206041a0705040314010b09040305130e01061b0c030609 75
    0x1d1280c515006103180c040240c40f0303200c0c0d0128910040894081c80082c0181d075800000780d0301050804404914200b40c00c40c0082c400e40c2048100604882d14901860003030f5840c0c01e0500c9070b41d60001099031206014018030001600c01c40c51000e2640c682d41c07581c0f42042000c2c01e118103588260712a00750780c4e801441458513a42c01000100700040c1c0e6441004002c2c0f0b258000740c4042000802407980390300107065107038001e0101103180d00c03240c0003c0c071001b082e01c1c45058505640f9aa0b074070b841500c03180c0400301521b10440d1140da001d0071070b80d58000c285441d0750020b010103907002c00e42d900703076004003001d80125054881c400294040000910081103024210b400500c11403500346041d000d50000c01c054400c1d040080c0b014001d2940d004015a01507075070292210140c19910404e00f030040c10b88130b603021740c0650f800c8140020b15410000500701c20640b46c603d0318002e61604020382113824203102c1d03900083e800c0151001e02c011320094145071644078018101e01c00341d4944a0304244d03040d048042d111 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 951824811 1250 951823561 951823603
    0x803281b0614100f0909060209120a11060a120504030e12010e120a14030403050f0a0302040302100305012102130204240206010807170a0b0a0b04060806060d12050c 72
    0x20310001e201551082110803c44151410600c4004100301c1c503208550301e4a4480540004002558059807d1100040c2000401100f100c0880343d81d115002c605070781c1c000c0d00c44107142c0c232410560100d885884140e1600d04813210518010402403400500550802120398019a00d955400c10b5400010700e6510001c9400c1d111204514100149221602100034081000fa4030441d000403110212890b02060b4645a9590f401e06413034a11034020b902c00090350001342000956010780c094000c3d02e000f95220030311669a0a815800c94800b07005210481c0780210311050010301003d042308500f132020340700380890a4040070100989e04107410500840008921104000a200c034080d0104105840103040e03952501015544840c03141c05804031443d0020015813895908001c11509031b42e001c00c20030001d14041d40c0c80f5004000c1c1048444c40360b8103020b000210f00a0009010340101c00040c40702142409541d5012110314400540c0010300200f4400070070702003014420310082c06103500800b42 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 951826061 1250 951824811 951824831
    0x5100302210711100e0d0e55090e071406130f050114030106081f080312060108060f151b0a0f060f02030121020111011e05010803281b06 60
    0x30812031545101c000b08100d1841f01c09156a640c01008092807004401c02901c8607030b00c50301440c6030b03188010000d2050719038001c413100d2a920380783c480c400d110344c000a8900b41d845800d188280c59018446541950000313905000744034520420885c03240c8018041442c0c011011208100c80c40315601c041d424403c0f0300030400483d6000007401038041841e81d080f40c81c0d0f40c1003c201801404010707240041400c060003072950701018400b142e101030710042003225220040015220030b0036408881344c41c0001d2252001c03560398104074241c013842c102e00a01415401c54602c01194064000ba4222603144070480142d02e0712840500100180ca0302441c42c44402032505e0400000341c40300070a03a0622184101300402044001c03c0003401002405c605540d00c4c2c10103800100c81100120241010710751810390712181d00c8009511140009007180814081d580e03031886515164002e2646181c48040184c0b07040c0700080a242032103042e0006418802d078201d80d4100000018400e0746800c40da600c0c0d03940502c0b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 951827311 1250 951826061 951826063
    0x102131710090b041103031620010f05160c150809010b01020a03090b0c070b031305190804030314040e01540605041505100302210711100e 61
    0x30004080c000c28820006143e5482c0022200140082c008002507100d21003145c0d020300448010422400880748540710504250400c0603a450034040000f4444480640c15400b030319148a0800c0180c55880c00c10600102c08070707507031a210004031800c07406640d003c0349071140500d00d0401d042041e907036034001c0e1030488082821aa4442e1000303042d98002d080c070a00081e40800d844040c0d03800003e03000d80ba03d0940c00345034603100d030b182c00c01d12046501101b00010b04141d104501006030061f01116024108124046c02c000b010714400351490710200018000f1078080d00c0b9915a002601184602c1c0135990704a01908100a811002008100e81c0c9020412140d01c8a0300c02c0d1484541080000c2c54402415001c3d0306454510440c0400108108120110190740c840700c014100039100740318074004a035904010740605c0c0940352090300b4000d45420b82d04c0c0709200740d601d0b04814002446c0c003404e80c14885c449180380100140c04011041e43c2310791f0201c034280103c007103600e80a20b0116524418241c59 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 951828561 1250 951827311 951827323
    0x9040204171e060601030e03160506070f0513090209010c1e0c080d0906200a1a07080705090103090204020c03070c05090604090515091504050a0b01240e0301021317 72
    0x503000518015840c00b402c2d460200f44280c00c003209007400100c00e0884100d0600314041c07490011a05c020840d000814421f020a4440c4104010f0350b844c803401d41008002e4446000e10b0f080c481101c4501c00082c021404d01754001c01d50100141404500301c407080e80d84011810800c1408405d48100300da0b02405c000c1c2c6c0400070005004080060300d10004800001000180c0710b1064400b00840d4084080c0040258002200b42e140301600f0f9607010103040c00e00c484085c10300c42001060301690300029641d1442212200d0184842c4da65842c41d02f060701004401a0400c810141d0740a503003004000c100c80010402040700f144500420130555143c042080001070340101198012801c0468250024101260a000340c010704031481c01282c841b190054070741039000c480754414910000c01e02042c0440010340f041650b00ca5841e42965030b0700e0b101c4030700a00500d104003a41440c102014840540e01400c1d814202c4400900014188100c175103a02040c2d044030340c4001c1c018810b0070844510000248130f4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 951829811 1250 951828561 951828583
    0x20f060c0c0705012a06060f0b04080d0c200103060906140109141818030c16050a030201050a0507060f0213031103240a0204050d12080f0c030c0903030904020417 71
    0x404507a00405c0c607000c00da4015540d035042004002c1005820001c10350b01132009411511805180c141d142d03910640c4992003030003001c9051040443c410031032445500c0c02d4042a03404002c1140302c0b00440220f000710700e4819000d42c141501e0360004a010340a5115031070090203070078084040c5145103c0050410000d54108111580c0c602c9483d900075200d0704100d804505400242c2c6005075286e079061401980100895441404001045c150141c000504038030f00c200e072003241c1842c55a0381d8041140c02c46072484024041a01400350f030707081e18059070142c210305010703a03808140901c0e040450b00880c0d000780355020401080400510600c0303e010b00800d070168068004048444843c1d001540d0000c14070a0491008070340f0300001c60851035901510010800900f0143c0b40c2c2c009803402c3d003804001e03158020f000030b50000004109a41c0701007064015031511406500e103032181c20134822680c0c840c10f542034140c031080109070125240c910050004101c0c80300c8070078240f00f000b81843d040c203001c03a130 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 951831061 1250 951829811 951829817
    0xf010833010f0206072003160c030c1e060f0318050f010f11031303020304080d03051506070f02010305060301150b07030306060504080309011b0605040b040c1502060a0c020f060c0c070501 82
    0xc10850070540050a061400440e204140406002264214914815501c6075150a491141d00a00f0061906d44407010b80c1e1280031a10260740d160070b4841d84a64ce00700c40000000415102044098001c640c200c41d08800c5180c04104250310741208000c0d0450003504a62075440607c00c1103130b0030300a125030296022a10818440c80300c2094100c202404050700c0c40b020401003024007002c2500800840f03009000d804123036808149018030183c001e01046031400400b1304011070b030060610b0b10707008a0348801d0b4801c5184414075099001100140402040c0c03a0709503694070038030003021040040000042140013000d070344d40d4107103240080903108944d01c00c1043c0070b000d10062040d14808402d6400310b1900b0f182500007403048100c01401001105002b400c91851b0000f400280109004010312460048805984060352423419100089100041f0300058100f4804540030180c10380100a010386184101c0c0c4101042000c51414881709807124000c0c1d0000164a0790384100502464000380400d007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 951832311 1250 951831061 951831073
    0x315071b0f08160506010f06140906120414010f0e010e010510030f06110a021015050a0b1e0307080f0105030606330f0c01060f050f010833010f02 64
    0xa622240e62203440701004000c0440030403142038144010059020840d0444221180c07035a4070412003c140c0761a0086400141c0d4101d14585002c141030200c54426801030500d42c604030358a5683d280040c4041d00c01c0b100c3c103140302440c5021090900070309240c0b00c080040043c1e0003032070394082030071181c02c82c2c3c48000136410901007144d0740152407554002c5a420001001191106107483d00c000e001c216a04418070380701140d0b03404515400076005c45050001d250400025150802409003503507140f0584d648001015028881100c0c00c201400720128510780001401c800151128880e801c2107030320710006040001000b0b030b04100101c6003401043e05801504060514001068154110542c800c20130240401848100441803404010030180e6803032454540408184142403a030000741d0300c03d2558240768010501880419000086500007032528800c0b1451000540e290b04008124a254003101c00c0c200004012a4040300351054400b00f4009421a90034005080c030b0740c001c151401150301c20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 951833561 1250 951832311 951832313
    0xe03011b110c04050c12280902060408010f152420070806100509090715090306050108010504021008090d03110f1215030f101a0315071b 60
    0x401040901880614181d1144042502454980311003200701d140c00910300000c00401d102c43d200544181c0e800801400141d8650070070032540c80c44502000c202103108490342c580a81416031100065900c0504003d05181d6a222824215a0300400c644805900c40001c0e503c0a9149449000a0041d10801c0d0400381940101045a0390180c2a0b500030710280d60183c24032180301841c0c3d143c98520620448140c25164540e480d100c440c10340c0c0983e84420044004075441c40d22145180c496060700340282005443c00200300d06140c8440001c034240700441c038001c40400e4032401141d010301103203000441c4504042c414400d5041443c108041040160340a0219809000c590200c103504030380f60214075403012807000b40e854400c600c2c42c9403040030000384019101e82641c0550707100b0036845003441d512910071414503494420405080c0c1054010180c1c0030140e500f02c3e0310101c1358075040c1e4510341710645e2860100345030600c1440000c6c17a0f00c61081c208019594840e02c3d80c12014126401c000322458a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 951834811 1250 951833561 951833591
    0x90510080706050f180a0b1c1b080615090909030a1403071b05340806010b030a020309100c0201020c0606150708091507031e210b04060b040807060e0301 67
    0x107258001a994001e500c50505c0941c2c0d00b940500152050b102020703070b24200c40e5084c80c03034681c00c1c1c40410041e07070400080c40d020100c0c44007184030508043d00c030202156500c1c001c105001000540d440078072030302440401060b071600410f16218803c07001c002c554502c0f09600141c9819901d46926403488010020401e245502c084885804116008800318101d01860618188644042c0081540e5000140501c82c8803100e003014900c403105881c050b580c1616503035080c0d1a04001d0050018450040000c0348541d00540c0c029584514500162088040c0264180301940c4a85401e080185c0d00070424212202041c800141c01520807140c1c5c0188040304c15007038038103001c2c00c2800303002d5840101c0d040c0a00d031118207007844941c0481c0d03021070369080c0c286000740070022140d10091200002d004101055809180c0a02081c1e8911329400c4104020114001c00b816070b0803050754006440d01c2e0001107030054400a80b0150540401901d00d841c109840203048100540415100381c0c1081005020448 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 951836061 1250 951834811 951834817
    0x41802040612020d1e0b0a0b091c110a120b1609090c170c0a110f0627060106020705010e3a0c12020405091501060f0207090510080706050f 61
    0x10300002c1c056143e59540c1c001d440101130500300f48491094a80e0402d865194039070007664614021150080199158130118003640138100c0703e26003001c0c20510030204a03841d000031071480d510a0751030700c1000440c00d01180111450b030f0b211364070707102c8446a4039003000704203940c01d0391009601c440a6804011300704010400100340c8075005950790340c0e01071406514030605054070425091015200c3e41d0410b001840c1060b448002a90300080d541d4084036900000800c1d40320710410810020041501c17072117010607540c440c50346d80c0d4403c01032208420b0b404038800c0c8506802010550003030aa081c0c6011300140200304c140c20014444e00c40240c0c01c22242e03000c00c1e8615049030b0b02c1c107118a422a04c40381c0d00740940b042042c018068540210000815881020034848400c1c82910207100d9601e41480d800d540b81c161111100d500303560040140302d018441c1b00c0603514044184101c4110607550307012003080f43c100340d8130302e140c0c642700500c148408034080002d00300400f05443d10300c4ca00b000c401040680c0f80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 951837311 1250 951836061 951836087
    0x3121603120c09030605090f0604110307050d200609090f040501060605210a02070c031b141c020118030f02090105180f06041d030d110306101103041a0418020406 71
    0x640d6450200b0b0008200702301e201400d400c248115809410141090100d80c3d0710824014480e1041030070210711410007135000c05d44103030b00002e28046200900c0c80c005050800502c07050700070400b40200c2d1015903914003840d010785e424100311110b0381061b06016094440310382010007808410029000310300c03e60340003110701864030115545c8644441207140f0103442544005080c40388100004402d001d1080c40d403031032170b001c11481d0120703640d074a41c0c0000d544021070305a640c0c440850f81010307420304814142c0032026481450b05140764611a880c420f08903d00350015500854120280c2c811401e10400142c050700007150407074800d007640c13035817445100e000038443ca1900c91000007060480d00d07940c00c02181840d408840041c0d03480b10000d00d07952a00030240303915101e801d22843c4884c4040d0300c401c40f801031102030040380c85624808070645504424130088480f5110170440041c448000540b10b0a100b041030b080071359a0b918040201142400107601d44000c00c1c41084108100b5411182c10f201072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 951838561 1250 951837311 951837323
    0x70f060f0e030a1b1a0f060d0305090111010b3015040f03022b1e0504120f08070b19020a0c0b040305070c0602061609030b0105010e03121603120c0903 66
    0xd140b01410140300c51942150040290300501a041170b00000d902019214510018160700f1a076210350800402d541d1405024000c51000c0064190340c2d446081051010f14100001144060301c180114448180b00d00001020485405010036484058034146945290100043c20460b001c44d0242d500ba520180008240324040e03c519008c0500920a20150503084c103140c0d000003400c0418160310b4004e20203203000043c16820803007041d101c94400000b2000d4640d5030203007041d040c803509568000101c0c0c0280c1c2c1817103940c01e0700d00020700c003000201556445100481114100b192101c0074407165100c01c02075031401844000180c0340e004ac54240c010340c00c9100c100e00b9031258201030b10310344240d00020301114901030010070940d0300010b140b0f01840000c504040880907940c4100c0e5207000da130000400da1340300a00100181d43c443d0000954000009003914131108130901012060741c4205640700c80e21800c070709004241034201000c4800d140a0003814010460076000c000c0a54000e80002085 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 951839811 1250 951838561 951838577
    0x2060f0a0903020a0609080301051221030a0b0d08041d1303031d010e070602060a0c020c0d031e080a110415110c1e04060803041a0f0f070f060f0e030a 66
    0xc1c9403003082004c1250b504404100001382c43c5040c406000c3c0d03c24009c10f80a601d8542e0100100c603000100c4090440307051054051244444c09101a0399101500c40d1643c5500e56401107910313038410203031180d06172103608843d60344c5141c50140716060b209042c0a054a20404040103410014860006019985894005450130000c2150010701d0381034101400c0940c80c04900c10807964001a00c3e1059a9061b000c442850f51840a16019141c115110700c005070811490711080781450b840004e80340d44241090440e149034a00344210350050454007500282e0502e062080c038244902c03c96203400c1440d480070b440c0c5070030810420141d44520305e0b20740812050f40424607211038244500700b00c10350011305d40c0406019840d10700100401c0401140c0c032491516070700041c0e2150003c00c80c1d08949a00c0c450355203000080003000e5107508a440780c01088241000603041c0400c0340740041007014030500600a0201c1c3c02d042c200300710303105900e0045040d0310700601510003c60000580d002c0040925000300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 951841061 1250 951839811 951839813
    0x109060309080d1a0901080c06040311060c0303040803101212120f021803060604060501140a1e031b080c180a09020703170703090308040b2208040602010b0102060f0a09 74
    0x5000c3c407907043c0c1040124a0f000c81200288012012101101002c41c0c1a0034941d032035031200c9480d202c014041070f40c044030030407007080004da1182c0c0d01c02e071894000300081e08041c1c400070041e00f181e00858040b83c101e240041080040303134540c01018050039144080c600ca01c3c10702d076140898581c0318001d400901c0b2900e01c4a061144540d01310b510440d403030400030f54a58840014094020202c500b401e8441e000781c00c005240d80c182403248400b00c07072050b074544141c507580d0210b060241d40428201c504000301c80c03070305803500406100c0003400c00a0f65503000035450389005204d0040741120010f03c04120b040380602c5590196242038400849982005440744a00800020341c58a0360b5030240503800d0001c2514405d040e00113130010036400c4600d072803c1c12991004805c0707084030030b992030041c0801c3d502004107003c02da03014151076110b00c3c100076030f120510600d40310b408003d030f142e48125038809000905100c0580d0a00900203150401e00003840789041440d004840004000c1c0030640c0c0365070711102c1c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 951842311 1250 951841061 951841073
    0x506040306052d0601021b0d08090d0f0b0421170702030c0a05060402090603060112110d05010e16080d09090f200403020f01090605390303091501050109060309 70
    0x103000f41a00b89801850814803001c80c001030441140d00b180540190607800413401015118228070180040921602007015541c5a072035400c540320254100101c501070f200041e6001e881c0445103070180d4442600c6150614000f041220511080228180c44c03d0031b100d102508181e103841030b8044820300004d9556090412450742c0942d200c01d90300341c461220174409001010603860b01460017515910310071356600c02030583e0f031402880741000c4124210310020109117091f4241c0b409200c000c0001c0103040c029181d0600351071048a0701f01864010500c2c42c030010121915100040030210b001d04144183c2d201d000d40b04155510906d54206d8903080b000c40041000d6100603240701d4542c944000c080b281003c076800075000760004078081c45200e60600c90940c01a050501190480d0b0388440c030740303411106064000341ca01e6922052029840c010000014040b042d0008001d00301c400868891908440003480c0143c801c4405461040180062209980c481403201c150307000c60401103540410fa1400c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 951843561 1250 951842311 951842341
    0x13060509010e1e06130f0b0c03030c030a0209061207031505030a1104060e09030304031101050f0402130608030c28020d0201081e070f030507020c090a0e01020405100306080f0304050604030605 84
    0x80d0341306100040744204144145098025514441c030100b404d181c07100c0b02401180300d84200040640d1040c8001124642014000c5038080005c10340507040c00c841c500440c089030414a02c06440800320360801180650520aa10309280102804c481980c40c00c000300c2d445410a4401400c1040281d02d201c0d11500c0c0c940048005056811728002d2502c0c2c20004152240c2099904600160303100c84986c500035414081c2500500201e4181c9551b40c45a50802100307200381f80080501645032000000c9040c0284082e108a040b00809403403031424007030382c002c0010507045401aa0185c0749000b01302503154140c011800c16428202508281c5a11042c40c00341c078140c03028401d41c0240c1c1e008016036a507120004184070311043c3c400740202c1d16621070a17620381d2441c022050304186001e0026203815401e41000c5c3c4032041401c0010b2400ba22000890701c54003100d00e41c60081380e1a00c03130401282000304010304081c04880302460501c0e042000040552180307100140101c0d4403140031402410b100407030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 951844811 1250 951843561 951843619
    0x1506070201051b0705100503070503070e0d020406150e030f0607030203180105090d0906020c090a020a030207020a030c030506180a0305031005030d02150108030f12040302160b13060509010e 83
    0x40503140e0880f00c1285a070700d1015024203030240c6424045040c142c0d00800039280281c040751070781402c540d5080b078220b031800d494140b4680e00020140740440075032130b6807003200080c00704039014101a000e600d101801921140c012503001e9031000c0c0c00703486e030b110f80824107a8118625140c050303625103a42410381c1c41080c500c00a01c2c1d86500c0c00060082c5c80d2800203060480c1d15598885071401650344605984610001c58082e401440310300c001061440c256000304441d02c0c0381d00f070050812105401041c1788641c02d07042128108181d940904c20301c4070400131a584640d01903c1100b0400d440b804c102c2d10740c0d00c03600c0b00405108000c808581d0030840c0c290700402801e00035013111591100d40000a59070106513030740000400c8a600007003400d00001c0116440d50340f40c1840103103000f0711000040e50140d402171050b804c60003000140316440c003008c00e0002c0200a69800f003915070003e40d0314046000340d1a80150f0500504008412050760000034a1105150443c0d2108040324114540407070b210300310603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 951846061 1250 951844811 951844837
    0x3030902060c07030b070516260a08010305070b091302090d06090b0f01090b031e072c090304060c081c111206060f032701090309030b0f150607020105 66
    0x5181c48400000207001000c50b400350518000300e46940d0000e4a035480b5000713421500c070381d510700323104049407659040b86040c541c0304002c01c00c0052070849002d11600801100800a0b5132580104281300b001c121110151816001c107914004094000034146800511000b041a401203902245a50384d40800803107590410024003a424803072600b440c0c1e03910200d0340490f0b86400640041441d002c1ca104034086000301a004082c41d00d6241200404103004410300b0445110f1104042042518559410048020117581d480e1050115014a142c04001401c1030000d501c00d020030020641c5c00054201e183e03400c0316580f41d9951062815001a00010800c0c101280c02c0407030940a4480b0032004018096656407400c1e11604c83d030701001708900ca18050000103540c1800071032100e9103600d10103900b1100350b61225042d50300c40d562103070a443d00080e0650124840c5281041800680c500140d0310540c060004000c0b49403c034105040c65010402142c0201c101148040859004004503000900320710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 951847311 1250 951846061 951846067
    0x13e030f06011e05091c0c0e191a060a020f0a080301080c010302030115051b2b0c150c030b090a020703021e1c05070f110f1203160303090206 62
    0x30010300003200060350058001070140c540100e00c02004100000080d0040d558103242280c0b81c03040240300a0ba40d0b031244089401c40c100c1ca400a114014080014847c4502e01601c80c038124099000a0845503a0020f9140c1410400f104409800b2080349168030115540c43d201c403e5118200d1803c070410b902889248514031000040c01f024602640c1203c0c80042181c0d2400b0a08004409900082c81400a070714504040d2140980c0104080c181c1c440c00c1d168103407080907008002ea0f28010160301c02c000c00310b241c0c010a0f80c000da881e4021240186007810440c002100c95038445440c1403103586800f04560b52250f0701d0782c0c994801d401a8040c0280200104011309061300844c00a50020204a02500c91700d00d8109444035107e082d2003170341c01c031000584246c04ea03029007000383c000c02001d40320401400f004504001a0100c0716805240c0c081d00200d001020b80e03a09114403515444596842800f846c829030103081000000ca8540c107084a85c205c041d030810345000e401a1500020083d0b11000c08 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 951848561 1250 951847311 951847321
    0x30801120609060f05010f09090803060607020f0a090e16051804080d02070809091f0306781518060905361605010908013e03 55
    0x85c2d04210705890f907036000ca0713554039991110030045455000b0024450381041c4005003540c0f4151001d0325010f80003078640a1045011400141c07c601d15801241800d55a40481140b1401c1002400426902c0580d80322820f1306160000301460202c06942c4422083ca000080c200055102981c4043c944000b05540300c0040d40f408019541041c80401d014601010000700d001e00d07100c0315541c10b068090002d8000c3d505589540c406400c1408200302c411810080360402000d001c0101e40c0f99140c85070900380d11226032400310303c0c401c880e2050303d411703210310040c1c46103012013001000d2070300142d5070076038401c2c1e101d0170708401f0203440700720400313465003190b60400a038054511500c104d00c3c1003840402c00083d0b88a5041c507044500556a4182640307c060b52401010441564480000305891808800d4801c0b0604646400e646c24032021070203078015020840d55811802c26000340905078028054080b00b83c250030940120009503002c91100c00800401044101a40c030b003081400005041d528986 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 951849811 1250 951848561 951848591
    0x30615081c1403220602070210050d14190207030201110703030c08070305130b07020a1506050112050405030a23030103060c0f05160803072105041e03080112060906 72
    0x794152507404106210400d50350081001e040720b200350f00c0213000c80d0005003181c2e44040c0704509038004449484c3d080200c200541c0d586421440d62184586c2c8140c0c0d10120110480300752108481071b03010108003242880110745024003241039507482404016207541c05405c040b4058040c9198034020010700140d84410300d03506400a00c0c1c4051183c9031001140c889080440440e82c00f00d40e5a007038070b01c421081d400081c0c00d000c03c180d00b001440c411200c2962041c0c49804202d4034001d00f40c800d41755540020006540c11401c4108010b10050007044903140c41d44440c0d45a200c0c0d00d818900300044540b120541d5803080c10071003560f004003031807207031207603124500341c0b001380140e52145c0c01107201c001541e85824495422105524104403d40c40c2c40b43d1a5500d2030301d1504003500c480c0903c06803418000d00d10768520002c000564080b100413946041034180b040d1450300c008062a160b01012422001081d000b171440c0d411100b010f8008072240c100c6003841c90040910240003490542003194595080003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 951851061 1250 951849811 951849853
    0x10c03050c0106032108090d050405091b0c011406030106060507020f0111030c21041d07050912210f07080f13030b070906231e0a0909050a0203010308030103061508 72
    0x5c680c481e16040e4903620301540d610042c2440d10800520100018000c0c0e05141d0410742c0c10040c80009012244d0682c88512003640050703203040803e07950b50a00c04030703052207404901d07003011050b00200a40750070711074024114403840c10041d0003031400a00c0380b15541d00c036407a0900e00d8a5240156900c80391204500c0e41c450070181c07010b0301070039601907001d00800490fa04885c00c407601395111031200e031248100d29624040041424084c010305110b00902a01e403020701c002c0000c245400750200d0051510702c0060f000e00003403500203081c5e042c4400f400131003114044400d043e410441c9151a450410b001102c20302c5948000d842d41003030420004108420758618900805581d1a111042034503604211500c0419105410302c0780d021504006101811500824452001503c007450040c6c452251030300592200f604240040c0034040c3c1003040c602903224a507001800184150315652543e00c1c1c1a50b20301042c0000741099030780300c40200f0310301241c3c984800240980819540003040460404c1c002070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 951852311 1250 951851061 951851123
    0xe0f0109030c05010b03060c09010f020c100f14031509100513020408061303081b16111e030706050333100207080703120c0501060801020304110d02010c03050c010603 73
    0x90701701004000c1c1d0303107008114031f0b10480b803c800c0503003040c0b501c00045868405140101d000d50040380f070485a60f4441c4d0003001104051034403485400900032030024a440500107441700421020b0045c0002c00d4070781000404812001c4401ca5041e8540740c07640030101d200c5034800c95020b07100c00010500c604084d0044e00c01c03140b2000544050b55258503406030003009008000b80040e280390f00050710240e207940c029410a070450b502a04003840144c12900000707020000755403040102190494500d00307440500b80d03500103a0300040c4001401400f090780c865490143c0310512074040b001981051800300e81e011514500b203130b2034186c102e2101007403054001c1d0340c950b00d0040f000200c803008a1400010f04000b281d48001c01072402c2480c5449a80d0a10070410340241000710310543c0c1c0c07012a2003409650301601400f40010380e0b9080034039107110050503500c2c21502131035445100d080540e800c02e518040f9180c05040007030340c422a5600703003401081540c100400c1c0c00f03984510020f44060450500c1064 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 951853561 1250 951852311 951852313
    0x807290a02151501080f1306050c0304020301060f080d0f0e060d0e06011406030c0a1701030b0f01090c230d060b041e030c090b010e041107051e100e0f0109030c05 71
    0x1d91034118450f080d258001e02401e010a4044000c140b55050000445a000903840d88040e0761001030741d1100d064800a541c00d2000d26004014001503103420320419006000f03145000214074548003403941c1796801d09120000744002c2c100b1003090075000d5030462500080003001742d80e65100704032445008190b00d20f0001d22a202d00000400e0010200000901d0210000c0c0700608540c0d940c0c6600c2c5071903100019070750070010041102003080f20b003900110702942c07082051005e01d00d00002c43c0003034494140c1c800d04140d41091044a880c980217411800d800104003810f01030120360800408162289a41001005261180005452080201420a0711500380c1140c05554815140c03100840c02c6d404042c0000a40b01c0c03007001881c0203944030794218030060501030070040441c0000f40860311081c100304d00303000001854074104541889041c2503503080c01014800070b2180c0c400e00740c2d2101d55807100c24910303a443d0b03d2900b861804012031141e13900313910002c0c4400c41403442c5c000c2100d5500d0b4022605 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 951854811 1250 951853561 951853603
    0xb060301180b150f130506070c06140a080601080421030c0905120718090c03060507030f0507020d0c03120203070203090310020a0203070314122e0807290a02 69
    0xc40c0c6080100e03156829040c150341810000c0740c1012140d1075011a205c00100a65001c0000345911404040c004490192100e03115007450804e010f8060600100c114044030004c00c6003c200303d4002c5402034100d40207190940035503441780303030621981007812001040c0d241c1ea1542009444d6050f000403203000c080703a480361a51507680f8203020001803001c8040c51280c000d100180482d0031800801d40804c10307884004110306050361940002c0a00c0307900244c5050740ca5408001915425005041405036100c40030800c40c07900000003915545450303100e10812007845d480a0a0500c034114801800e01070800855990401101c060b56170b40c800184c03c1d010b8002c00c110301e0f0b50405144280c3c1c00c02c0f11960040c42c60b003451694200d070024203408055500420138010092f46141c4440701ea03208004900880380350740d40710b0510f283d1a0014007100300303810b4005907042c40203140100e54401150064030000704c3c003840b00d107010711415010380718a640300d020200c1c41056460b0700144200081c001c031350507183c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 951856061 1250 951854811 951854831
    0xf0206120f011d0105090a0222060e090f06090f09010b061914120a020a2001050103021201110405060f1b0a02091b07030f12021303020a05030129040b06030118 70
    0x2000d20005d01c1001e601c108203074000352502c03405400524407121441c40003413100b0303003a10b0441c00403901d80e0001d8000030340c450307195111424620012034025421140c41041b920f410b81c00034001410060081d5142010300d80807900d4040250000480040001d19003512500340140000440420740007190000e01c0460030f0b000042c0e10b98040f661031200165451242e95070b003801160180d071040000d01c04000034200402c4d01030420000c0340825010320b80001c109545540100218601c68400700c0305c0301c0c3d14050b180c10300141d8090855040b03610503103120f51a0700d600300c2c4000c0347d405442d84559001483c402d042e45445c40c086080c449a5108540a020b90345820a1100c007118018208510b840008c00c110030200e406015000c40389070480c41c3c800c0c440210300303060030103a800c941030b41c48d22040c84070300038411460320010301e8014040681c000c0100510243c02003081100191080d4915034030304245942c16100d80d080600780c1035000c0d18055032035a6880e060903600040c10000488070749020100c003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 951857311 1250 951856061 951856109
    0x30a0605040c0c0f020307030b070512061c02010c02180403020f0d1e1b080c100e0f03041211032d010905030a11010608060c071407120f0206120f01 65
    0x50b00301005582e604086511541d5031102d4060328150581c2d06204038080000000c0005c000302e0b20a400301c1c3d94481d00d40c200c07060392880803040545003908c0380d0124604400b0f1011205400b042e490740910b003415150080e8004100007010200038035801e41401700411060503000a86200701c80320344421100f8801d2030000448111094400c48100000060a10701050740700751200100c0300c9116152449449160380c80c031404da4482e1410072000d4100111a244141161203039080115111001d003283c1103042d00e07043c1c0c50340b103140540c1120001c0e221000b000e0000c4121002c0807032a0240407203000796500802022011117a0403640d50101100c0d00f425503c080c107014040c0043e50110081d8100302e181c40060b140444111101141ca40d61128001810807040040f5805502c07440001940c0305114141241410f14402c00d541c915809401c007009125419a0b005070b00e55000300484481c40c100c0c2c40042c807a8424505050000c1c9840003d0080d540740441400e03040307620b414410790100301445249 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 951858561 1250 951857311 951857321
    0x160305010e06040507030212090616050c0c040c110d091802091f030b1f181a0a14070c1809020303090d05070506040f06020601050103020301050f04150b0708030a060504 74
    0x1801e21101c000200e40d090425801c001e401841c0d604000d810030080003c03003c11410125909030f001c0d8001e00c14005441e68a05001c01140c80c0c1340b511510b8447c83d961010303624bc40c14150707540110707560a00c041c549441400141c0340c0885910a0b1170180c03c500a0007010803100f030084071500296845151040181031080307410100000d003d00400700e902841030b440e100c1c00e1020542c18141c075152003042039a10000c2440c0b4201809092920000c040507006010942c0c103110800c40d000307007103024801140400c503102030081680c01101d603981c0505000310b07401c8130341c0490345a15140204520003045480203106041d16142c07810340300390034040740c1000185d5406840180d019001003002036201d003494445115514040c40032154000d44d43c4000c240681d002e0392015001c5007800ba0300784160b90341030124500500e0246000d6003913506102c0040d200040552010340b24681c1d9116400022004024500052021050242d100d8001d8145130000e030f0320403034007440898508840819546010301c0b070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 951859811 1250 951858561 951858569
    0x6060e0409120e06090a0801091106090a1802071208070e1906140426010c0f140a0e09090a0201080c03130b040f0206070f06050601090303050a0e120a030816030501 72
    0x480c01d4030390264505481c3c920602c00d0160b00884104420b001c00d8540341e605c24020060340307000003411207150900700b9000380c1c8805c80511075041004000025a2940e2011081c2c4102e40070110480440031858002440f84100050941001c0d4902c0310070207070041d445521405d10342c1c46070024940d03140304014090140440040a24103400c405000300c1d8881c4810345c00a00b40000b05510b803544400d40d90520403e801e0607818144110030020426110078001c40715000807230700b44240b1912506002a1a4030900c0e40c2e00f90000764003080c0c0119540c1321b41811090400040e02d014203904208007843d46918445209a01150611020614640e244c83c1128030407142680d52504500f0307139a0311a0b50280000c0d005444444100c07244401603603401008ac810355208103110304006801c2c2c0340101c280e5070001d140c2d034140800c0710300400c00310b0f4021084580305215441c00300c507070700d079207100003a2588007082da1000325100b80244502010f800694186c011440d44d1840c0d48a114984000c4081d00c000f401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 951861061 1250 951859811 951859823
    0x3020f0d12090c0504050f06130212071b14060a15050604090e070825050d0b0606031f03050d030b0a06120f0902060310031509051e03041806060e0409 66
    0x70901e028021551000d0800b500c60b112400905503130f140004c040d10702c1a81c22003906198541400101d140112030b059041c18601c405506080751100c250046031401451402408100d40714100300c0607170320a0321160700d0f1b0702030300c410f140c81074144103155610421507150f9242d520f0441c181408941140d0420f040f80c81c021300c0709241c03030b0600c840b000140c01081e003628418031a01c00041486141070100007040d000380b8203402c00d100d000200442c2c03883c0055202e40d01071401c008400c1e01050300c054500d03a00520995036030795240c5408080b00e40c4d03c541d2a00c242c00600c0c0b2a20080208980403c6002d621a203994040c08603141030030030018006558814030000c04c6440740101141c44171900300600001110100050402c145d4000c1542c681c41151444440390344e0ba00c003442003040c1020f024442d440c1c00c80040061584d10383e266035071081181c0e09207a642e0034110a1120700401041150302515079410150300701058240f80b44d0180900b80101ca01103400d824107c1042d046c544503000c41c99030888 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 951862311 1250 951861061 951861077
    0x90f0c180e06100309080a08100e1303111903080603070e060904260a050c0d02012306031e0d0e030303061509040f150317040b030f070c0c030b0403020f0d 68
    0x8100320f0b10545805101c000e250710fa44098002c500c4030740141c0021440c81e00c030b1a8061900e8416a4625001c98000c0203c0303124050074000d150f01607a02c03484100341d050034240366001140004603c2c0c00807640300d0142400c7c100031640200343d4800003c2d80204000d0702112030940d1149a007180741c100c01c440c5590040100310014007c07030074003602405036a1130b048203455102183d04890b40daa902248807400450000150100001810048000460003a01c001c00c6413800041455030030008215104a45444c80d0010034110b50f001d001c6a0521070349040c0c401d01e0050301c58119901d03041c10000d00d002045604600074818180401103911401c0000c6c04005150301e4840d44d261a908041d0604d07401c0340c0e80b203295204141e058880d12601420703001c6d1884155196280004143d01400c2c000c8070380d840d00380000c21000002d4005e480d0820860b00340c40c000e07655080400c0352407046580d0041d00c902d814480c00002e004c030110505009a0095080d5000700c030b1403154103039072841c40e501c1c0840062144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 951863561 1250 951862311 951862321
    0x2090115020c09040c030c120209090708031b070503011a0a0f1809030e0d0308010f08120703050702151303060e0d0c02040c0c0b04050f061308070813090f0c180e 71
    0x82141a40c054172812030566802d4403a04d80710038034426a040f00c0000b1250700040b03000e41c81e21520807640004018007e0000b1410039000c15124014180c1c0300c90401c1c0e50784481074200006218250190001400070080019a4080401c590130f00f24000d501a01c03420901181e00154008500306440f9400d4014132000c03200c51404004007a5140c003502000200c51010810b69225041c20a265000707a94094035941070001c41001c0002a602401c003540c8068940360494500c03030107071042070350903007440b5440d01000d0011400ca5005200a0031081400084440500c444500d0746020340b8081c0300200030040c03020742c84540d03540f281e01c8104041803007148440014509908425420344440c078041c04042d082e580d80800d2768609460865454002c0c0030603840ca103030200001c1d42e00100c441000c41017a000c2d52589480d910489001403c0008006801703646810100002c100800d0a4207040100c0000c2205181c014050698504001031000042400301181c142040302514418010f601940d111 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 951864811 1250 951863561 951863569
    0xc0306060304060207020402210108010c020604060218060712030510260c03011d010e0715080c070210030b090619090f15030c0e0c0f0d09050c031902090115020c 71
    0x2c02c11034071560200329000c0182c4550024000102032001010320702100b4480e03843c20f41d00141c00c0300b40a6803500c11054112540003490359082600105d005a8844a980c46a0065403040442641282000450404000044401c0401060300f41e404202c03544902c0000d082000c504c0c03264030072801d0104440041160100030400101c0c1400088078070201901d0042805c2d41c070709104400802080041e540e100c0794003801543c2a40034908081d10301d25042c12004841c1500c802c030400700308040100015070307101e040c6088866440d00184038150070700d54103c008001e0400d40094a0041c1c0324100881ca01d4203185a0140203105665004043e040c00c001e036500051024038443c0c1002511015401c010070b27030072080300340614001d41600800508140805502c0300011b800c01e890460104a5040d00c000302030241c4011030031010300424041d03540d0400c9442c02c048818020340c54014ae0700d00c0080740100480e0002d030b46100740d440601c1a0703a00c002103c001c808070360005c0c1c00b58115244001c2d01d0300c0c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 951866061 1250 951864811 951864817
    0x3020f0d1b11040605090c09041823120304200901061202090a0302151306050a0e0d020105090a0e0711030717220801050f1311190803120115080c030606 67
    0xb5001e08005035480e0340f540004d02c861020348455504002c00a0201c01c1e9080901a845584050400d021152070503562044110203580c580341c6019841c1c15104c6082240a110002d8001154030940382c6a041509151154001c441d40d111001900c810b0500094241060306504840301070301d444c076580c100785814070065403140d0701660703100340f44c040040b0040c4d030754030099a100f4500c041c280d81c80b00702816800354103040d90740028040c04414000c502030654851200184460240e8490705402180d20059606014025641303902c0305400306c000c603078a104252002d109035140c0da00c52403a144200d4443d0384a106540c0054500716218800c0425034503c40010f100001025818602c1d030158074600c052030300e803030342c1003124265120b50a00c429228421000c03904601040e510a0f042081c40ea0b510003d80c820515881c017440c50010415041480030300200014507807482940e50350090007002195282090103410ba00140c82c84d248460680703d110454841c001c002a081e1550311540c08001c0d00b90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 951867311 1250 951866061 951866093
    0x509060a0c09050303040f030218041e0f0b0406091106041d0c090d060209040b0108090c01270603050402091f170319050706060b1306050313020d03020f0d1b 69
    0x1102010000f900c0d10100010401007410094603841e00d810351040000400c40318500204018081c814003000c40d100461882d076208030298035403069221031070300c2040302c131590700d024101c1e0b00030000b040b05010041d0080c101d094410f07510707083d90000800c10490140a98040c0340da0a03e98503040e0703040e616481c502c00b0307040400b001100e81040814800501941903c0c0e0040b00c00f44d401142041a0303003018066246544001d003001700003490040e0340c0590742d01d10500702034100003503519051400c0013400344003140c40c0b84100380c4c0302d03486845640240291000b81c40c200d0241c0400400144010819a00540c101d002984034004d107510f0300000300c6c00052640102c119900040140780340c00203450203800c01541c0703142c603125210398442c1441421644541e01c000300c0c0400c00c00c00c099090b01e461280005813001c03400d000780c03079481c0d0340c6010303a00c1c1d0954107000390441000e0082c20300707250300050007509091182c01201d40018484508403450b2085c100c43d14420030301c0c04809400941810813008a107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 951868561 1250 951867311 951867317
    0x1d0406030f050f010c020109034802010e090606030f07050c03040906050f030714150c030d2c0601140d05101a19050108040804030b0718090509060a0c 66
    0x403a00c039155240c0d00090346500326095032110054840701c000a005085910409000070000044207440103403240c1802c0708a5501c86900500c111001c14001000e1114141c0e624000d0481c03280070f40e01c80078a40e80400c4280c1c0891340491010314980b82c0b08140920a100180c01c02c2e085846100c00c03c040d0120182c040303014404180600301d03244c042040a08001e040c0725902246403171508061040005442445a01a820070001071003540b900c80c1d0206000181520000210504034441001c18015a94881003500000406000c2c0840980040c2c1c150301c1140e94000082e2844800c041c0c050000880d110002c0d003005004002070f1402e4040c4801105002c2e0645602496640c0c0f00c9041c10004818000150380d00c00241c100e22800b84518803a440c010b444040340703041c1009800310b102420780314260401c82e642001508203c10b0500340c070021540a03c01404e5810720813000780105140c0d49000138100004200003030950218000c140c01150f14102400154945c07020a002411081c1c0d00d020034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 951869811 1250 951868561 951868571
    0xc0902070201090e0408040e07020d02060117030d020c0f0c27181c020601060c030206011502160f0e0c040308160c08120910080702060112030e0603070c020a09020a1d04 74
    0x40c0c1300810249034440c0e445000944d50315402c0038628419540c02a0554086502c004c5400c0c2600e50001105030655060cc0070b50400310b003110001501d0f41c03160010707610300e50b4000324034486010800504040a19640e41c150380507444021b05005a4085c40185820354071859558002c0c4030605021940e044402c03142003400c4610254a10744c030b86001020802c2d4440007000c9104075842e03040c00b40c0da01410304d924202c00300d1307416078500960b203e5040c00f94883d1441083c010f0381a40f07008020a5010340680020008281d9540b01c0d010700c1d844243c851107420240c5c040010348100c0b4140700b2a01034903440741c8407c0c101942e2010f070103046000c51004640d01562107002080848003003044030300c140000b0704c0301940c41f0300c0d840500c584490340041c10010b1149401c00c1c04110364011030094156588609088104c072113600b811107001248031401500b0080000c00d000309140c1c04010704a59500a1390203110340c0d980c171032040040b0b20441900070000b503403c4550030030858000181c172841803401403010803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 951871061 1250 951869811 951869819
    0x3020309060c0f07050103020a0c1b03051509100c0c080904090b16030b0d050a080a05043516170f1c171506071509080418090c090207020109 62
    0x41982c00880d030000c040c0e111543c429100c10b000c0066401808082c42e080d800c0001d0840007401d071425120005041002490030042001c814400e04801150004225011110103c2c400c0984100544501c81e140c025500e4a10030328460740100d65441c81e4540d20300c1c075502e00b1622506400c0e0800b1402e00c0e0700940310044100421540f0184900a4450012041d008010b035203029003210b9101000e02c0c0103400c14169440031072404620320740300740c1d003026038580d50b0740e10644226001e208582005600c020300007480d1048013150b01c42400840001c000c0101800c4506501e80c0e5100340f06140c001081200050906c11881c00c0b01462111210050450304550241c030401800c000501ca200301c0c0c1940018450800c16510290407003600c0840d50040c04181440304895000802503c401d5024520004a040170005030390701c002210086440100304000c003034904101c0d658098403907114000f54010402c0880f03a254800d103035140b640705105c0c4100c0740c984035140d00a50010340c41a4180071090000107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 951872311 1250 951871061 951871069
    0x60f021c0203030619030804030b1f0621150611010b06161a0103030c03030504020f09090d03110a090515120c0c010501090509030d09140f06100501020120030403020309 74
    0x18240d5800390003864880c41c00c0000d221160351807040c6511a103070040c1042010071088800c44040d40c0e000300300300c005030341c034802c0c40100020306140050240d404c214000501540c070403500c55a00d0440445407901551508029007a0b0300105149421052000390401c0b940c0d01501d42c031903410048030004181d001d010360000d0b149030007401c04110106031003800030003085440c1ca000e02003030505107208880e40d410358500030060300304032000905155980002c9029940c520002c417511802c003c0944c123491422038089500c8401d4034191401180c01c000040488400341c409603013081740d85a5410402918103070411150b1b0041f41510542160100041c140c81c104c1c0f50303039091140560800d402d5980008403581d60840d1016400b819005282c1014001c030300c00b01000719101d1002c40c00700454000c14908020b44202001012440648550252a01451f80205101e07200d00c142406e00454544c2e0340006a00303031540f00c0100514600c175a2240c80c04260410b0145400a01910451b801d000240d8045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 951873561 1250 951872311 951872353
    0x408031f0b210c04030b0403030203071205190c020f0a08090d0804320d0312060b0a02150105030a0201050702010f09091104090507030b01080c0702040f14010f0618060f02 75
    0x20701d14000d44600818840c158070080e1900007003440072030f40c501865a25081340602010703000608058001010811892040201c5518580320040c10007807810003c03001400c001d91b88140e9110141484141e4102c1d0740003042e40403881c0840c01c06800ba1141541c0c5030303041644a03030841940f0060a028941c00b0426240c0500041c00703451205055600c80d2007200c44039001d00000c108002407001e624020320b615000124003965502d41441d00392100f10503490805002c207504146808400495240101940012451400320008040060598849040c5521a8560900a404180d00f00014001544551030b4040700e000c26180161aa40c2c4818214041e540740300307032a0a1020780483c0602000d4003502c00d544e000301c8241000c200f04017a032030019000381030007000c04103181c00104450b400c1d512542c0080100c250a420104100c02007a40341c042021000e000704010360b030308a100451a640115101409000c10619503080790b4501003048580ca4402c0d9a00c00450140d080190f80d040000380345 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 951874811 1250 951873561 951873577
    0xb27010c090e0f0408040501050f0702030d23040e0705030402010512041b15021b060d0f02210118020717030403033303080a03111303020102060606030408031f0b 71
    0x55080580c5400d0b0859181003000d000c1002002a600501001800700f0302241c089640038207006480c1c8001d4402142e03907019140d0040e4040c00307035000f140301250707110b096280074102e00301141d00039006801e03c8000f00e010314020841c03504511800f04041c00e002c1c1010310360044c4140351042c540020400244070f002e50944003101c0c410144166140ea4036460108000a4407140d100d0b444100d52501300207545407441404c40203820f100071050501512443c044038120f000348d03102404203982800c0a00000c0d8405200380c018858620103180044040b004c0c824100e80400c0c02c0c102850b07841c0c20007a0700a62110501310355482ea41d26000d120342e030100c8040e510503800b0341c4001494005200160545d14a18804a81407940702d180c0071042c45818400102640d4118250329118003911307a0990040c4218040f880135582c0110f900340c4042c80c084140c400313036403003030b0709480e00707601e0390418010700380010764004203111000c0c00010f0300441c09610038226441240140d4090a42d640c0b1a40d4807903102103c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 951876061 1250 951874811 951874817
    0x70f0f050601180b090f1008030a11010b060a080109050a090f060518061e18030f07141b19051216050315180705130603060b0109030b27010c 62
    0x40100814410101e4681c21500c5582e002e10113001400300145c161400201001c015200c040e010a040c6824a250000503020300e800310baaa900d2103e0024040090722403440d0159070074252070307001904200054543c8203000782c445407016428201d000c8084c0100400c24850759030b0364030455011030118a2401503050184100160300c3c1480000d60155107a12003120109030b0018090000c0340c00070a15502802202082c9030b541903e440140c1011440e603080520704510002c201c201090907000d006280240c0f007410b2010071840d03032810441e292040c5100e2000e035018510f803001114140101c0f0500c2408019603806811038480740000c8005a200d080d01c501c0ba80000025625502075608450140408074010038401850b218040c030340150017020780103103c040f4121102a20010010480508001494480e0300b01c40d18010360002c03d001d04c41070740da83d4145201d103c510b50150403802e00703581d0080020151903580c0b0300b201c00c082d44042d508000b1550809541d000c0801c0a200b201da201000756 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 951877311 1250 951876061 951876073
    0xf040b120f0402100e030c04150503061e040327030b15060304080d0b1504060309060f021c2708091f0509040b01090e0a0b030607090302060d02070f0f05 67
    0x100300c000004500601031110107400905110259a5802040102c4411807505008034611074000c68103000d19064090340007070411140c1310303203400703243c85a43c152a8160100c582954540340c40c50a24042044042502c1c0c00f044c0c04900820304c204403840750b10380c07495a8041c0703090035441079001c102c2c90780d8025230358020241c0500103030500300394003000449402c407040d43c1141800e1311001568490308041c2450181d0f154040c076102d4030342581c1c0040544640c000644c8a942d50300c006000b41110060440b06103103002d480143e402c41030b00c2662200458400b015016062140603c40140b40c02003a050704500d11034200c04082104011302d02c902480b810f1095241c40c1010240404644044440e2848000c403840c842c3c8030f00d620900f41c54423003004550205400d0f01c54001654402069002200050a0001001008051904041010942031307040702d847d41e545c0031086a05202d41c0c08020f600182c1008a241c000c04590007824005000340207810182407a030341e900ea07542c07207d14811140e0390031031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 951878561 1250 951877311 951877327
    0x510030228120606050409050901061503050f13150e0f0d020304050a0914040b1314010c080705034003210603020f12010b1009050937020f040b 63
    0xb40d20000541c84104090040c5802c2c40400340182c000c40c01000112030f5a5070010b2001c0c4425040500184002e00b045d410210322040000e020300000c54406000c80d60140c0401c07600c0500c0362290301044d4018141285c1080d044030300101410410070742d00990302c15600c8410741d5007018060300c01d48015035001980d449260400b840900842c1e82c1c032404806103010600c0945607440c0c54004d43c803a5100b40c80c00402c1d80d401c010503846c00c6c1c040c50041d2800d0028107030056907403415032040151406580790b0310003580d1014822240c5100c103e07800c2d0b8203031300e0040720135000043d5a41c451680049443c6101d4022011400d00410036840507002e030002104540c040c0413228018001403060800413a09021107402c40d000302c2ea441e003603186264020f00b26901c2c02c00e243c031002e500001301c40fa4002e0404200002981009103600203c0c020f0741d10850b03c11000c20000000c0d0a00d0351a048810541040100e101c005051691071b54500d0058885408000003140d5006480c01000074140c4488580d44070500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 951879811 1250 951878561 951878567
    0xf18051006080303041403070632090c06130302060a031b03050606070f021801081c030e0607080709030c06020d08060105070f1716110f0306010f0510030228 69
    0x140003034000000d00d001001d1040c40030120850740c1c0305420045602030242103603605480c503c00c7c020003420b0ba500e01400760b24604400d038a00c465600c440d009614062112168119000b8803e0b00e14104039070001c00c0d03100307040c2080d5002d000000b090780100b184942d501d8010a01541c000f5500c40002561518000c4040c054031040b0154180380346010800e620742030340400c1061040040150601410011240031581d91405c0c654900e00c0014054600b940c0d40d545c80d950350300ca4003880001e240449900304007418441d200b0140600094001805039031502d203010b954001c000b810120801074490000310114070781006810090100d44e00901090138410b20040440902a15640c1005003c000f407201064207203943c0d508141c0c202203440782918500f041e0340ba81744a028403181d07039003540340041018080c0ca130369507890001003079651603c107071090001c258851000f40129082402c034001d0900540c20207500d5030841c040182001890110136008080507465040620015008515000c0000d5a8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 951881061 1250 951879811 951879823
    0x1c03110709020d0c1107080a230a14010f0b0f0402030406020403120203070c0f060512060112090506190e03160213091b09110a050c10020c0322030201170a0f1805 71
    0x2180201030010281405803032500e40001da18040c2c40015400d030700d00d1840440c9c2441c56014111041116080042031609078282107051921b030040307501c0c112031200c410205001c1c0c01e181c45001803c18294455407400c001c0250800392003620226420321010001400360039003c6981c6080747c0007542c0b81d403903600d000c0e40d460040350031406040704c1202007041159000b00607901e0b241c0701c0c2c054100713843d960300004a40a0340903184100d03800f402c00c1900070501c5004a40c02d0300035100e80c6094902c151211118000343c030285550940190700c10004000c01e0321004001d1000c4500c014445061112410801016541c03035400076200b6051a02c5210340c16422840c9880051501e0b4409112140920004103468001c00c0004014440005650301c0c0261060111095034080000c045448202010b2880c0c0c1c0e0360882e881403a0800c3d820540030a400c00074458090460794141c0d10308160340880d807141c250b5900c0141008030416124116040640f146005121442c0341c04092150030140d40d0034054a884 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 951882311 1250 951881061 951881087
    0x1204030c060c15090204090b1303090f050a06080a0b0603040b151806041e020a090501020d0215010924080c0f012d180608060f1c03110709020d0c 64
    0x310705421100091980d641100401110b2000260035220f17400414090210610014480c05205080000d00c6903242510f004240c00796035240b8401d91540d0220300302c0440e030b0003040c2e442a02c0b1217007008058442e1a80c664444910302000c0f451410507400f00740d29401c251030032036420465608000c1c0c00071721145990284042110701e034200481d042c08200b19401c005e0400790240352501248002c000c0860002c08000b20f244400315507802270391b032004012444900600d40180140b0070a1007074640300007034030301c0301c0e00540340280240d91804912200900204801800391141e40d45610038941d1034a031080001d0040d04040c001c1040c000c020024114a20b2101c141030010400007080201196003c1c041c191040686034440950803140641d0b01d100e40d0014140c0325140c4041c045142d03548440c4040c01007000361000080d00c5008800c20840761056200c207881d054008261001003445100041020242d0740140c5050300d45604060050360300c0501201d80d015182c11010402a0b80800400003207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 951883561 1250 951882311 951882317
    0x5030c3304060e1e061608030a020414010503091c0c020618010305100e060f010c081603081303082a07030207050a09020406140307020c0a0e07081005210f1204030c06 73
    0x1882400865400c07000307180071601a41d0046201500803c101b41546510f60700400010b4032454030202c000081c0d4041e0103a41005500a400324105500603003d40e0b01030480003010780000600c0b00d40c2422401c062170744484c2041440210a005a20307070000500030b280440861b800040b000c5000507050711030251120b402c0c108964400c11601d01500d1032260458000c80f00d082c0c044410b00300407601d01300381500280807030400044070008403900600e018086846912040768941d2103030070658070002e13601c0c4041e0224038003100044211020344100408821441020301744144049201c0b03440c1d400140003100940c1c0f10b1841801030341b628604200090040344015858103061800c0240100c1d00c80c0b020105102c4084007040c06240244501d80124034050004c0c13050381c6c0d0790424035401c0f12042e5241c402240a02c4041500c3c940c21141c1c00c8259100030380601c8580c00c3e04d038070041d0b04048102c907820301d038000c0850100007540140911021080c03040f411548460441c1801c8e094101640d0000041c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 951884811 1250 951883561 951883579
    0x1502070806070c02150d02130f06021911010c050f1018020a12030504151709011401140613121a04020906010e0d02040e011a01020705030c3304060e 65
    0xa220f07800108003c0e080d5041d0b80300c100d100e00c1d065103120140210703040071003440e00100740200b11500302c40c000c50803111046d5954141030b542d1441030342c0701c2d0405810241c210302c1c5141c84101064020101c46003880040c0340140d001403240d1103d60074050f04009011403038000c00e00548409203540290201b8030141003400b01002c010381d0001d0580c3e9814820703021504800002e000a15002d0029140181412034040002c020505030080c40001c04d8200d14020390700c502c011a030031000c14030401c420f41007413061051040c1d00709001e40f0300010380e5a40443d44664208001c1066038090403e007001042c014042140780c04044c0307006d400c030018000f02e24040c20304650400c009603945840f0107411240a01307008804240b0000402c8070104003a1000e5006410101d5210080d04154003140b8a0006166000108030156004a032201014410303141d050780800410342c0c0780d2501c01d10840440020801e000b00c416090038142e10803140c010900111010003003800c10050303420801c04002070f1412526200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 951886061 1250 951884811 951884821
    0x8180f030604121110090201090e060904030e031e071a0f0405040c05070501020c060a0e07030213050702070807031121030703180803070f0203070503010b1c030215011502070806 78
    0x20356100010b2010708206441da000090640c01030f5040d48000720034001351140d401d00c80010070302601c4118012400200c8003d400181e00d08c4482c0b050b27009000080000c0340d16212134400326000c0062110305941806242d80001c3d801c4110a811407030055004003030840d661800e80a0f0000b25842640c0c0c054503c0c0c00c001a500c1c10130004c3c103d500380c1e03104440020710090a00300c120703000d0040e103031700608661001904074680480001c41900c60303140b514040c00b41d00502c80480742c850301c15210003034000040c0440200c1a0303502e5005240e10646d14270444503960394945130145010b2030744d40142c0e001108a203440c005410100d0b0074881c1c04004c8402c0d00d11421f00110703010754038441c092026080014280c1080c40200d46005508020000754080340c1d01c9640711304191581c0f044002c4100d10a00c1382000008940c2018041c07400e4a580c01044107008001c0da0603100407407502d5110031030860207403691140c014070406e0b9400f80a40806500c10f02608614100a840c021013508080203035800b10301040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 951887311 1250 951886061 951886063
    0x9050d030e06042402030f10150215040f060203010f140603010303140714011104051c02010e011d030d2f030412140a0302030a090b030c0904020f090d08180f03 70
    0xe412550100b0050021800c45180441c1e9120009100c524180000288000c16290f4400b06000d20b0b09041440041682c51076003040c550889d59406002da000115072088110310240b180ea4401d0191294000c105000c2e0342d10001c07a48240c01500e0101000c2105010040d02c140820812110603902145154110345002c2e00c10200c440c102541c9000001e00c40d410014904590ba01c1021400e00a0050303000100140d0000c1c0c0040c0507850140c0071244000e448441035041c214252038060b15255a640c6401d00111028598030408800d25454050b1403502c5071020040c07080d07000415603c8118602c42c00003004290014400050810744140d01c072904103c1003c41160101c82d0300340c031070285a003101c0c075000744040300c040704c100d0b100d010f5090480f00b41030300400104016030f029903c2c5140203403269401041400107603502e5079640414400b01e6441d00701070340280b66085940c02c5807404c040c0703c500081d03c001140802294483c10210b840c100c1039164400e10f059083d1b048503400036a503580070200e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 951888561 1250 951887311 951887323
    0x8071403070314030705010f2f160201091820070c151205010e0f160f030b0d12030905010b1c061a030706050a1701060c0b0a1e09050d030e 61
    0x10749140700003403031604500f104008484402c0c2c0d0000080c0301207044c2010074401006503043c0c00031100d4215068022650540c01d4455224040030041c40c141900090308140808949500324140200c0300404114950100f04994940d62a51404a030940c1000d1040080410542c214a8844c0d818040480081d0245011809640603c00c0e10a410040720b0700442d098048120302a0b09039103400d0000c14030ba01d401d88001d10a6029801666140d00c034420906401c608004100340042ea0b4580c403506d496102e9084900c00500040c40c0401020254580c110401e4074042c0d10800720b40c0d65001101000401c1c01621006002100c10841582d03069112850550300b508d4014041031f61454061a81881c0c11200f07401c1410240c12540c1d0300f40c50750300191095100c02601804555002165503a000d01101c859041c3d45680d41c071070400001d00c1d0b640c400b4414010304a000040c0d00d8088030345c460010404040c40410340e980003c205002c260529a040000541c6d110042508081401d8030b444000200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 951889811 1250 951888561 951888563
    0x1d1b0a090608191713090b12120c100212061f0e060c070b0a0c030909050403270b032d010506030412030b090a0207140d02121b070906080714030703 65
    0x410f5440b10515140341ea014441010b01840f0070042500c00c0c810307162041c070380e0942c0c00709401005903201c48401c001341c2c0c103980c03e0b00039459030000c0c070501402c40f02040506030048110040360b884600d140144800d903003210648000c0c0550349010040e0614000150801c0091381c107150548001004000a00d1a1040c1001c1c80c05000001100c080d400410001c400c020701070050056202e0040c00d00080c41211025415800111401004280c40b64580318290085900d61144000c03102e8040548950b204072400003982c0340001c420005615500000540c4140701d032660040c8190420303040d483c501d14900b04250500b508a8005000030f03220b44084030b401940064206200c2001148201c028103c4081401d4200741018180018100d181d00a031000b64401e03582058403102c411000ca50b1120303401d51743c00042e4010401c3c988109e003007100804a2a042e00070814440c0001d420447c42e22420307030300408507280d444104003c107400034040d0300040c02c0c103c59552858110803001980d80c3c0d240707004c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 951891061 1250 951889811 951889843
    0xd05030d02090a09150515120f0618010803190816030b0a030c0e01091a150c0109080f0c0f0d050403084b0a050d1d1b0a090608 56
    0x9411601640c40a00100040501e441306201242c84250300e180d880742107100b802e010b00400b0384030000540c0500c0940c3c80422001001038000c0d55650000041204050415a0800714101550011a01110510b03028040071001580d940c00d0302c3e07120940d000403c00c2503c081000380801c0c45881001080b060400101616010694608060010b00c8880035640000d00700034110ae40000c0340c0ba074201d1442d040780c0e0840010445108200010303401e000102c41e1455010500041051895680c02d000e0403080703040d000009000081c3d591040003680c0100000240040041420540b40104000c50f021128403600500380f0401d52190141c0300f4021804014030054001c0f421782145807818800d0300c0b0206181280280b814103040d0b206003100310a02d6052101e841050304003030320100f61401c4450b0103449950b2a4940342c11009904001d00314801c0c0f01600d00c1c1d15101444241c20204010800794808900086081c00a002002203000040d4410415513090140c100000c0d000402c0c0700019180a40e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 951892311 1250 951891061 951891067
    0x206090705180a020c1015050d1a04060209030a03110d0309020d0311011401242a06020c06040302060711060105090103031d0a06020c030c1507031b120804110d05030d02 74
    0x190f08400640110f200c440c000f0f12481c00c418102c66065003000d02100d481da0b10b4941d003141c5410500c2458201d124000d0807041d4100740007107141c6412030366503038444c0c010b190041c2418241400030b824109506415000201501001e44207003c06003e4101503042505040001c10304550200304a00020325001e400d000c8003800c0d020500c4002e40141c07407418200002c046013583c40300100d030804c1e03d83d46080d255680c401514844c400d030042c122594041c000c0d034842d142d403a00c2d288000040d0390f1900c00032100542c00340b22100001208025950249110ba000340803185440b150040070880903c280350300580c001170040099489201701903040d2131f01850301485100c0f5416030707001c1d51401c4840c0c1e00e0700440c0340000007684e01d90110302d200355820224141c5141001943c20030002482c03420491100100c00c00200740020700031007803011070500355082048465841e81b02c0d85140700840c0e1607400440c0d41d15007003000b080040d9031071030f510500c00c0765a01c0500520340c9401e543c83c000c08004a219a40c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 951893561 1250 951892311 951892321
    0x8060a0e0c0f0d090c36021e030708041a040f060c0c05120a170108031b15091c0f091a0403050105090c01090f030f030c080f1306020609070518 63
    0x120103d41c020307040c0e00400d008482c02898082582c061a110f00240218160800300002c18000c640d0030311049030b0384180c84000300302030300e40000303600c4503174480b80d6604610f15030400b1000800284d88141c0081d256100c040c0b4043c24105410a02091550303210183c035802c0000245880070407602094101d840010400e0a01d64151030440d0140e0014040f84a142405001071301c1d01ca009201074061580c1e1000042006180380c1b101c04000e020b220669003007032001009410303a1507414000d0500320011030310700300302280024084000030740303403401243c0081001c03440d120028030700e41115130003c0c6400b8100035900c4400a040e58403034000c038403c010802a4611603c900384068801540d0050020401ca00740840001d94070441805024040342c01940b00040c00800d1100d040f0850b500405102c00750410360fa402c44960f120840203e40c0c2400a12041344e41110700005041c0c041e4418142514403428038001a10b003940007403801205900000d024002c0e0313243c26192100482280800b40c0c516194 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 951894811 1250 951893561 951893587
    0x12060d0b0a09110109050102150c090d0c030b071409090709090e010e0d0207030b040b0a06090c02010209180c0904331805010b091c05030301080a0308060a0e0c 70
    0x10840019140c085014180210340c56268003194015129030a50807a1280d410019651441144225400f41c0c00640203941c660040100f490b81c081c07e2900128507060490000440c40826500180d640b010080342c140100006d01e12000d0304903140e401c000b02e1061284000c00c50503c6206100341c003c1d28000302044180d40500402c1c406000c160714103102d4404c400d101d850090055a000703105c07170f2081c0b0040c2c030b540c140080399440aa0380c000c4004203055039240ca56410402010700500413080d922400010415503910524086a8155001603a145040400c00c004d03a142c092080c490a8500b40c240090001048212020f4540941c3d021455880d2100444040c1040c9406550f40714040c2308048006180d0310320a409480300c4071800c017858420001c00e4402c84030240140c802820040086040a21b0b015104134402b44101c001c148103120310f5552035095800aa00031481580703c035030141700f05134100302106d40c0070a09607101c3d03080c1c3d031070401e940c0716006019102c1000008009407800d5100c00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 951896061 1250 951894811 951894829
    0x2a0315040e01060320030606040c02060f04050a0b010f08060702011a011b0b04120f030902130e190308010f0506070c030206090d0c06090905090d0e010f03022503020c010f02031206 79
    0x14010340102c110004521024109071080302e9846c1c842c1c0100c84c00910b06180510601400c02c85a50007881907590f00b00440045000240c8140e6940c442c1c40002d1000450005c6585d0103130440c0c5c40c0701a542441c00c0f0880380303040c0e0003406410a6904101c01180520254000104001c00c2407810b40c05070b50003800c50503080e03030144102502d8000d45500300400d010000360600b26041540da5240410034108030201d044a00248009600540307249440e540d10746250030031018180c1900660340c218806880c204941840480210f001c2012003004110505443c00c244000b49801e4680d00d00d003080710340d01d0701c0c1130b00750500000744070f4640807a010009842c0e00480c3c4660316807145c4401c20542d162100507181806501c1001406030034580040c410203070100720000d40902949808940d45141c600540d1100d0501c8102d1042544c240014001e062076000f4054442800741941c9140e01064180207007800060007115040c05214005c41c0140384e8000125044050204007940b03c50302e80600051443c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 951897311 1250 951896061 951896063
    0xc03062c180601140f0102190f0201050c010c09030203120408100e01020408070303020a02042703140c0109240207511b020705040f02040305062a0315040e010603 71
    0x1c46450b00209054200c01090b500340305040702c0d000e14500707098004a135940044040d0200d072400000d540c40002d69400f01700701280f40b05040c000d0408000406250860b042500410b0004041c02010030a6041c00d00c4220092081090460720b05410a0704080c0c0d203951041c250000542d907000b15410203042981680c0190490340146c2d40c08a699040c02540c4e5608404281c0c452894028540c1081e071042030850008218174580c51a490010b8906803032840d160790780001007440401c52040c0c0d410080c800d80075014410680782c03e40308036151007204804a40a80540d5903881000440003003a00700740d4600b2a11818074040c071425422005503e142c1070f5500407030903110001d106410700c80700c00c0141171009451f113440400c000d000007400e560240748512505005a0000c01060000b0709003030700141c60f08005041c0141c070700b0b0391301d95070146000c2c800c40d101d052441c0c07030301c205484602e5040c40c18149002e0030040c29045003040b10990364107942a0844510450381c4455011440000307401420041d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 951898561 1250 951897311 951897313
    0x60a08060409051e0c0102030304031b0f140a0618110910050a0303090503010c0207230a03080c010501060206250c03120c08010510030e070e090304180c03062c18 71
    0x121960503d21344620742407065800f1400b0b00c070540c5130194030000c242d900c03442c0c01d40c2d1100c0490300820950380040e40488800ea4540440303548510129812010a00c00c01600800a02c115456420b2071011a800880910441c90944407580c012a41307401c411550f144049601100130340b00c003c43c00750310352010303400340b03421040d040d8000040c1030b0800c40302c00c1282d1050b00244040f6100000c101d0700d803815409101c03424100c45ea05011030001c1e003100d415088030003a2038224041c1d00d9484145c2c050b084800254a83da44640041c03000590522040e50800d803907940c0c400d06401c0070780e14040c0824801e214001000080611042030500c60184050341d81c40c40082003007502e18025008213000000d00a043c01003041d201c2a94049100c2c1c411041e040a140740076091041c14030100381a5a90042c003000d105200c24000440c0b109060308190401d02c11003100081c0900c040c44010302a12903581c0000c0707000d0741c404c080b51492400c0c0c80b000501014510003045c4190749828010141000c0d941115880e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 951899811 1250 951898561 951898573
    0x904150e0406020706060509060a14120316060605270c120703050402211002030c0f030109020d1802010f0c052103060a0e090d0c0321020d1109060a0806040905 70
    0x207100b0164014515180150010b01c80300380c884080c040147d0701a555140c0000034403070200180040000c601201d240000e01c0d1b05403807c15041c240b407440c3c000805900005401410040800007903102d101c0041c1810395402c902045e046e038445042c460301e4030040040b80c041c040000d01e0510060101d4864402c80c512410a82c01c00c0c8078020020f0a045a04074003c008801d150203400c8080414000303a019040010700444944c442d0b00d1010b0f4001415550030b111051001d01003101d00c09021394086c0030700f000010b80302c80030b00070001c054540318440c40050000400038034000d40da000c0c2156032580313002d007040d80c81c01d802454040d10b4a141440100488100ca150051601c48803400070b5010701c07000c84d90b10509a80341c912020581c1010348102443da4804003190004e14041c040c0686128041c1c184a54a41b45520988002e5080103015401107640010301d11483c0d000b5100d040304000c4110b6103030782010000408966544141a0b01e9000e00c11003e0004034140c0c0c46070804960142c1c40029104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 951901061 1250 951899811 951899813
    0x4180c0c21140327011a190e0106020d0e0f061617160212010515100203070c0e010314010b0f01030207050712050c120a030806010c0819021b03030f0904150e04 70
    0x39902110b00300e0680e1404113041603180c18001406210200c0c3ca114549026100380700041286c00100c0c014409100d0200e0301c000074032a80003601450003400d150300508108008404000c00c40311008450501c2402c0b0b95000c15001d485040c151081100640450180c101d40340c140300c5c00303030010000c844081407400507004000e4a254200d11445510a9411408000116011a0986100322105100301040c101050f2031441c000031182c8031320a083c0140d070f10b08002e5032100f224818031500308104884809004008110030009080d01c03c07006c2d14020054071044000003038540d5581032041e810981c01194071380501100380020802484440c0c0030030501c1680d0300c1c0a07500d905851302818402d805030280d00d94142800310740360043d03682c960303078aa2072955010300665004158040503148070740240308240c00c2c120440130840742c0c4180c540040c183c6910380703061010000034558155010742c0041c2300380b40c440341a281c156010b0190817180850081c1c1e8500070007451502f6607210310162f0501c207083c80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 951902311 1250 951901061 951901081
    0x10060914040b030a08130b091e0d05010606020d0905032d0709050a09030816080106030f0204090c080a050a1a060c01021303030e03060601090302010f0c03021204180c0c211403 77
    0x54201243c1846c206460b61750414581e4038001d61480a030401c14000f01084240d100300d0711403602150080502c1a07070b02c0140c40340c600f1154260031020150348002110041d840d045411301004080840c02040d070721000c0c1d80d80300305440c1411054598680303c00c0c0913854000043c04444050003605a04210519017100c400c40900a440c0058000c220ba0704003060076180a0723403113844c1e00c40007600c400c4202d91816804400030000030010b1500a035003840089821243c42c004c0d401c41c828240e039801c41d0780c14520002802c90703a000c1c0411520b94540311150021310078001c58807080150841e51540c0760810303000c185000e841014891100070780c1c0741c0004410103800030700160b502c2c2d6003a002c9603096501d9200540702da041e6800080d0203d200840441d82a0380309040d00f2904038803d1058038840d0015524080d03042c0c00c07542140c00c195040059807149496039102d00841c0d0246850040714640c6141c0b0369000c86c90000a0200e001c441c00c60f0701c0c4840502a20b415031203010310391030b0035030750b07262aa840c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 951903561 1250 951902311 951902317
    0x20303090d0809061210050d032a2108150a0e0402150f0d060e07050d0f0618090620120405010b09010303110c0306150f01030e0109030c02010810060914040b030a08 72
    0x402003484c0c95506c081901d00741403007005401941900c1d2a5405204099600b4001c0300682d0344e42001038030344801c2c00010300c00030309520b40004000e5540304a14103011000c0c0503032100500f000110500049401099a00c00d040039048a90883c0001000c0c0c40d00e00102c2c48483d8403c07041d81000c80b00088400440282c640205440c80341b103031301080ba590300c42900421012099405400090741444410200307076a80d40000d4840c210391000050056a030298214010340384804e081c0c82039541c041d40c8051001e24010110200400d0102c1344100e203408460b540103006007c00720420f4802c201c00542040800d61022080200007481442150b03940c0c40c00030700034108900c1c1c0031194080d0700440c0c1e59504000a406009289441c0c518282c60000014400501460700000e8101501c1c0c00c84005001002c3c862540c0f0340d4043c0c0d81e01d1220101d20700001d030440d80d000d011401801e03002c0d80304001c040e91101b401c01c1a0394900c101244810001d40004024010510319a42d15028820b860000c20000f0001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 951904811 1250 951903561 951903571
    0x3040311060109020712030c0e1801060306090506100804051e0a02040c050a09150e040f0e12030130080c0a0b0106030b030c040f3305040207020303090d08090612 71
    0x40700d415a0300c9441c103200f43e0180090050074401c680341c2503090703039009401c038203403c41f07c43c40c00d482407500200c001381c4460140d03c45104000140d20040c030080e540b43c002c81028060f98036003400380741004070101e900c074003001381c07142c0400c442c03900070404001040c0000035400400340c0c0100043d00000c14031035180d59a041080348103a00e44401c40c800701c0d01420070745400101c151100c0c0c88a924003020351034605202c00302e000130046c805100c108250744074855086c1c82203500c007002500600181440f0314090a00d01c11040750b202c18401080f43c0c650a036200c0c68402c00b040e084c000001220241201c4103041400000c00304240452030200c102c4002900c0c0312080c0c0211114685640c7e80c880607401c0341c9609412079010303001840029242e0400780c010b0601c0000702d6034001140c22000359540004910340c030310b00e060404c07508160f0300c080f190301ca21000a400f00311011854802c81d41e0000e0b5407440b9a0098038016400c00d11001c0600601000340c800012001e414160348001c100416070109000f128 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 951906061 1250 951904811 951904813
    0x90b070c05060d0b211b01110f010204050406120c12050319050c0705012a050c0a060504090b0105040e01030b280b04420812040501080604051b09060f03040311 70
    0x81c010145c406152004104131091006000c904014020150000c60505642030510050030350308111450104407016041a03400001a151410981000150356466010b6400c170440c00f0003d102103088050a9022100703080185a0350501074500603046000e551080350034103960441d40307404c0030380181c010a03140310554180c541083d203540041d5030340049a284803071508040c0d015101143c444c01040803285025000b02c0d401c0106075800a220f480c05900514002070020a08100d06000e0f8055660440000d090050416040840c55000c0c0315051101600b96082000407801101c001120005000b540010f645600014100780c80b0240c032030054014012490003408248820181580e80304086c40d40c460700c940080f1100a07101c04d404080086560b000201c04002100d000400441504c1c0b00c040f41d40c140c5445c64000090451100100010700490810f01040a1405070341c0600b1111060300c100c03540c848800b203000c00d0380e5020700340c21080381003400000d0000345500114007048040c0000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 951907311 1250 951906061 951906079
    0xc03050901060b0405010302090a0f0f0f0602010c0c150b090a0501171518120a031d031e03090102070b0a09121701121403072010090b070c05060d0b 65
    0x400380d030880724603119484041030140410b005a6100790018207a003040100403c026540728021407900c00d41503880b2681550f100e92040120048034502880140641e000030004001d641401604040440a00070207403105103141200c8107070b03590b01020100c14023800548241c500a003031400101428082c10300d41c803850301480e5001e180002114003000038070041a50702c545a800018a0004100f148030f4180d005c2e042444104a48040107890201c11680e0040303a074242c0e0046250341c04541071a610740d40e402c100800070f03074403007424241ca022100c007009030b80c0c1c0c9075103254210780280580c200080c545c00c440800e002403480c69030068686240242018252206d401c030301541c100c0411801c804071001d00700e0040002103220310720030706c165008640c060690301840440d03a0941e44814002c94020740c1404075040c0801c02d02c0162040c3c2c1d141596030080000d400c18014241c41018400c11088480000e0200104094040390000800c006452262074020105640020309000e2050340d010385459 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 951908561 1250 951907311 951907321
    0xf1e090801022208070803070f02030c13050a05060d05031b01021911061528030b04030c1101021204090f020d18170909010e04032a0209010f03030f050304030908060a0c0305 76
    0x2c141d80c006c5880e081c0c015441c1c4025551081c1c0c03007510105042c1d80c18011484c40019586490040d00b83c40e1414250014061401030121030440c0c3c0050300e075138051a420345001000071000411205035141031006061a0071460181501a1150710902c80b507190ba40a0b4102c5026008038004000c05504c0c0280d0f010399030b1701c1c401c102d440002c0c2ca03a92507100b41701d14004a603802d00300f02d220b110040c0038a2100846a2691240e080c80d00082c0e804400240741d80203520103101844088075200750b030910203401c09541a8242c107420380154040e070944603640c0d149108540c0d2059040300e6a401c00c01c035052103032101208100b00e80e00c4000340240c0b802c506600300a0182d6118408455200340000d06600c00b6900b448090030b40060001c00c101d090003422200f9007030b18000c441c0c001410b011070030000109060148140303c8059010fa01032a21044060000c1c00081c1e04a03000c51800c0d062441d0030341d20b980c1d840c00c00b218115010750110300e0fa805020140302c203000954200c603009a0040d00c0c28482a00c030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 951909811 1250 951908561 951908563
    0xc0e0112020903071a0d060e09010e0a11100c020a0906060206130c03080c0a020d0602090f0402031905060a0909050c2d01050906091e100f1e090801022208 68
    0x18001c001030303144c4c100703100c180402a004400300c519020301c1a6a02c2c100400300000c6422241c80c0c0e00424105554901000343e184002d0051210741c0e001040034150030070240ea078000d00c510110000394070980c2000314400342d0610a522880b82075400811203448282d8842c454401440c85000f524010300074400050440030b60310340d00000c0700e81d226811818503032541c1c80c0c680140c0c000600030034483c01004074060150b503a503c403140c0a540240001a5180c448204024000d604036003098015030040c020010307a5903044104154208424101046030394800000514038600c0d03820640d403051401c0094818000300051300070a45805448030004046800d1400842030000c07801e140c8410850341300c1360bc665104402a081462015200320b017040710080000e01519503882c9050b00c0141ea02108441034370381541d80c0e2103120020306089909010940d0010a50300405112001c0d60545040080180d8800d0329041d004000c58002152100c0341d03a94182d42e070100d0040c00f04148904e044002c5000c00b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 951911061 1250 951909811 951909817
    0x90d02060c030f0403032421080f09030a08120a0501060e031c021905300409050702280c05060a0525080313060e060610210c0e011202 59
    0x89207000d8507085503588440070410000050049040507118408500c4140c1d100701110740c135032542c1c022081e015080821400450340408900503c4035403000c01d610100f10007004030b541d891900c91074155079250b41000300746070030040000248400c00000351000600480401140200b01d82d040510059a0382c50041301e43c00b2203a044070741c0c550402c1e03407142c0031220044410034660707550707006580c032044d1282c1d00400080080d080948091f0040e1070081d00e00801d00c0560800101c1110781210220255540c1140c0c0f8000c500480c481140c0c0d4101140d011402042080c01528003444161144090442c041a980e0a002400c803034a050401000ca071500e09070081d156079120710740d986070400c42101c1403c8036021a005080c80440740341d004000105280c1030080d440b452800600c0200070351603141c803030100c5084854420442e0002c0040c84000e9640b17249420700d2110350b141c4808130207031500300c415011100c3e13010f00184614082c0e05034a9240c01c0a480340040308240c864040220040d03001009901c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 951912311 1250 951911061 951911071
    0x10602011b081003050f030a090905070c02060d09020604231f2604050304050310020f0304020f01110106180b0315160507140a110105070c0501030f020d1103090d0206 73
    0x354460300101a10802c1d600d60b010705031407140c180050781c0303481c1c890415400c2c0f03290317800790380000845004043e04030f00960014502010104910720b003000c8000d280105045000744901c100041a040104c0349802824090f0703002030840d9079407641c48042402641c4c41b100d410140707007241c0c6481c0b640b41c54528941040b0402032808010724042403141210b400202072042c198500310074860903405002210000d219911030030045a807641484101442d1000c1c0840d00c80a550040010720020280101640c2d00258166011600302c805140161010189600c40702000d600e0000000b8901e07402d1000c03881c0a080c0d17002c0c10811142148249900c1d0052030451100b00c0360207001180d680411b040010786c4007c0c03d85481800c002da0340c0e5400000340032810454896500000d0400f0a01140c0d000008021100b402d18900e00031913595211101d1240e4131807907046c0350350b40035000150009a011501141300c40c070b50070060381c54102d440d40c403650020f03104400341e846421150001e02c2d0000500a000da = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 951913561 1250 951912311 951912341
    0x1080c1804200622140907021b010905030a030e0109051815060f03090a03090905010e0a09060f0c0302281e1b0b04061406010509010309061103010e0f01060201 70
    0x400e680c500d000b25890441c68100d400c0034040004405000c800380240f402c1043c00458808034901c0e10044080d6031002c5804d1a102e190b0340410f20a195400080c40d81c40c1c24840f0301c810502a682200580c0c40c034170681c0c09540c250003020002e00816a02281c041c82c1030b08240c80c0c811007541c8a0041c009961544c001a60415030b045d400300d200785011268880c9003020041c01a4684246c84520100a410a0324041c08551060000008141e041143c00d409010342500401242d854440c40e1082440054004060181e54a50700307418421503400c8003d8030118180c0034800005d41e05001070095026400e12030a102000d007200892000c404c2c0d02d000411090350300c0002208010145814162000d40e508052240441c030806984210b0b00c0250340c45405803411010314078080c1040d00a840460052109000b464001c1001030382e00101640e10070070080c03900082da00e030302c4e181a800070702d007840b507103129007001000001d800b0042c0540a40305a0810b200c10310140d90750001030707007650034410144042c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 951914811 1250 951913561 951913583
    0x912060f110a09060c0c0504060305060921071e21030b10080105150d060b180a260109080d0e071d0a0911040f0b2e03050c040e01080c1804 61
    0x120f80c81038001c410014006c0c1e52489034980d032140064102d40080e40121500d8002c001042034032002404070007889850140c0020410b411203c2c50f450a11a8020060180c0c4440748560803000203130100761f52441c0d10640381840560154007481041004410090019080c83ca00f2101418150b440003212006520342810b1a400e01007080503140020101203a100000d100444800900f8003d950040280c0600d40d0b96500c43c4040e0400f80c00c1c40151243e0191180c86410045101854403524010446034109030714002c2360f185490151100040242901801084210000b80580d0003861502c01039012640345070340e51205804501103040d10b080b00700b00e1460000307031054400e4201250700e511414100354100c3c52500010b084925000000c0c4e105582e4070070002071414583d03010034003081e490742c0c4007100b4600031113100b00301d460031000d01e07082540350004036881c03268000031354020b400c2a001c011250360711a80c0e50340e81c0c6d504641c4200d2003490380b550710b140d041c86003100c49402541c04c8502244 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 951916061 1250 951914811 951914819
    0x80712020f0c0303120711101518090203060f060613031406060109030309090b121b09010f0e01170a020d03050c060f241504120b0105010207180902010912060f110a09 73
    0x1404840a0400c0704048c00303034281090310300f4410b20803115400c203519030000c030a45c28400c1c8c20351051000c0d800c80000600e01400c0d400983e0b00054103950203184441c54005555800c2d0215155000709400e8200c002c84080e80482008041d022042420241c0c800301c0e070507a0344100c01100c601c8998840940440c184001c1408405529080308240c80c001501216500c0300c0508841c1c58403500d2a03c1c4201c068580350025018130382000e01034010000001199041030600084003894030061180032a80071010800d445400e005002240405030000c0010000c43e0f540e0401400c02d90103148241484c1c018403000803901005100d0b2039000d00c0c1303c0501c80450301070081c84402c0140101003141d0b40000500e52039441440350b0070042000e040c442c540500b242c02e003850000b80340541a0807141c155008420b00740813000700641c0310040c091100b200032600700d40a0005840c00c07500382d000501c0b2004280602c3d418030003075401a80e0303c6c24041600f0485050500d1600c100c50140200f004005820514100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 951917311 1250 951916061 951916067
    0x1c051003030c05150a0e0d0e01120b0d050105070804030210151403100507090f080a030c030c15050411030f0604080d0e2803021621080712020f0c03031207 68
    0x180424412011519101c4d00c07100040080c072412540e22200702c0c2c0b615081d4422020512018543c1c29507410922070070301451001810292721078814505a030341d9004003030900e50356041400070303040e0050000c00a074103010000400c1d0741c80455090340588a41d2051540030341a85c45032580c6140300548607100c0030b04201c060240380700c12410407a454070860720309503140d051a1013002d010300c05644804032541d01d80494080140442d0740034103125000018a4400320350041e0290940c56031510300440c01c25444c0c9407045807012150080141c10745450200b200708000c1c0d585251200804404407554813121140595492070110740c000c040700400c5c8103001c035844054214208a400030420754025007181c0741c440c1400c0e501c041c1513034405859048141e05064041c80354112a4100400c805605800c000b01d00415482402142081049681420003801055401d403409964040c113080742480030782000039907400d00c2041c10900b03406402c8500c04145000000c548006480545101c1141e032214420703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 951918561 1250 951917311 951917327
    0x22101030f080f191e050705071208040f15090b090f01080a09020d080306041d060114010306090f0515040e0a0f06090803090703110105091e150f1c05100303 69
    0x38400c81402806201210f0013420031012000c001c03641c8409900c01410b100800a905029641c000d01c401000b00b070001c2400810f4030019030314401d14500b100c100d00c0c6464001842030303a00400407058603130004114140400c42e10080d000266440c0c2c40100e4070743c600140380b482403003511648852070b032003001e01650141201c01c1e44513007403000c0040c40c0c2d0001d4011441071300c40c1d8502221241e00000c20405035240c1445100502810a000225154901c8c040103603940d406000f034040e00748914448a0a5a20070f422980160402075803d110070f400a00960000d00b02c00d9a11039000740d81a401030116007090b2242d400c80042840040c000342c8016158260740302507c0c0b80607900d56880e03013868004640d1201c019406800e0401c01440f0542c80c5003441046400c44c0d40000c4e0411408118000302e83e514075284060904855411a40d0190000001001e10304a8105040c0484c070114041280041a901801c0007074203494407142400c014984200445030120782c40709400050b00003e1000c81c0c030031b00c11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 951919811 1250 951918561 951918577
    0x150207061818110408070f0e0a0b030a14011506030504150e150a090b010b0309070905060603071d0405180c0d03051c0f050421231804020706022101030f08 68
    0x14081c43c00d078494200c0d46c140041500040341d003c04500c0c04124180c00025010ba210000440800095212000103a25062044006406c103421400780c0c12250400f948551a07406002c0811000c40391307a00405030103820701711815980680241d10700046992280075100090580e10040c15245000c2c03208888007900240010040c140d0318000b4200003030303401c05500d01a0114441143d120320300002014a099041c1d00890000c3d801e2500b40080ca40341c000640790402d101d4102452862140228040c030508240c0325180e006060800703111a11038220b100c0e0b1507504203030003a2050042c03018240f03c5482110342c0000c0000e03108108143c0d44071000011004000300d0703003034007164245d60100c4980980b6401d9a0556441d00200300107907075909140c0d501c0480f09040d0400c040703000c00d410b01d00301d111800c550410403018000174050a8050000360848010280244210740b2214641800c0c0c009410400304094142d00308000840c000c3ca089908034102c07a800400c2503807200c0302c0c1c0d4403d00e441d00f082c01e07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 951921061 1250 951919811 951919841
    0x3051009021602060301030f170f0a0e0613060e01020709050c04030611160305030a0c03090f02010518060301120c122409200312090618010504150207061818 69
    0xc8142c00681d90600158005c3d8000c03100120064030700d042039140e0b9501e0203d40e081502007008007040d480d0702d02090308d602c0201030400c0021002d800c00071445512515008582c00027180f100070480a800065000c20107070700b07900321025103031980518021100184c90b00c0e40b00c1d140038001040001c000b40c1144444c0c00e042a90242001c3c040d00c0705140b00b205040c2c0031008120040204440c0303094503c240d242c0c015003480d0a00500c02c1c6915850074041ca40038010303040080004245012443d11001c410200030098070041d900d6079515002c1124424604044401482180300020318903851040c6404c042d411912400c140c4180c8050038a400314039806981000e611026100042010080518195000708401b40301c8142d00b04c040505044103000e40d500045824001032000791a09810748500d503106022540c808408030300160b80307070300a551149034090303064070020700110b9010407444116030058a42c0c0904a402880907401d00c00e00b400745003c80095600c2002c070380b402a0300040121038580c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 951922311 1250 951921061 951921097
    0x14131110030917181c02040f06050604030f12030b0a0e090106170a030e1e040504020301021b07060306081f150b040605120c0306030606150c1902100305100902 70
    0x10307070f8402610300309401408400c040480d0410030803800b0b40c1d500302c42000c22140d06070861101c90102c494400348140181c0601da5890b82034554401a5114201412000380000d84603956031070880c03070740e02e01030108603803012036141540724941c002c1c010b802511400400302d502140c28109400405c0740010100c01c244c0d92a0800000c0b5000b0b01343e010718045000d00c015000944075428058125046405c0e1107005101400743e81c603160761002080c000301c07031080382c0200300303900c0303900000307019004000c030304003151a042640c28009040041c03984212070007501e041c4010b03541c0710f0205440700076003e41c403207000085c0d90041007c5829540208010b01203e203560b4080394591440690541240d0049070209000080042d014000f090300f06034044240800c5038a10b143c1003001c69220503004d00f4003030107081c500c1d40031215031058501b1768a0040e201e10480344611003811912000407001d0205a0181180501342c1c065035109020302881030303a07900001c844d10752030042400700130f510440f04400640348071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 951923561 1250 951922311 951922313
    0x1101090c060e09090d020304050409030e030d030516110c04090f0c08010e0c0d02030d0f260f06030109031d130504050303100b0403030c0602030a1806141311100309 72
    0x5840c04901030001d0b9603a0103044807000c0c09200b000c84000c0c01410329580242090305800794004215015180241d0300481c0010452038140e4095207404580c0f0b074140203c0120301c142c550302d0380c0140c1c442c10b950b10f4501c03c0d0303104404060b100c0f0074068100c05055044142c0d1000e0600785900100402403244c081c1099105050304c901043c0711254205a08694491100c2c0c0c000c0d60b403c014101a40d00c045030490700409880c0e001907a01c01d00902c041d0300741300075058148948e07802100c200c5601d032010303800d85a440b84c98000b03034410303550300300d03811118401414003080c4241414480c055a05905403280b0304001040081880c0d400300c42030b01d9540c403948024610314003002034051107000342c0c49400110f807641045040c0d010302010940011040c000240710400209610815070740720280c0111005a41e9280c41c0c00b031901900c48000230218840080c04602d0030130046500c0a07510120000c2048003035240c40901b071f68100c483e001d000d400035880c0e4141175a47d290440402c81c242c20710b810001801c91079 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 951924811 1250 951923561 951923573
    0x903180b0306040b2b122a03141804050a0b060304060b031f0e0c030c010207060f0903020d0b0901060b090d150b0d0c030b0c0a2a02040509010b010e0d0305070201110109 74
    0x8034030b8501c00c174181c40715180d60400c01c040154080540c0300341002503c1c14003805e969412042101d6007079020540210018060602540c110003641010084181d90340070703048e006002d01082e007201240160b2805002649401241c410409036110082400f440c41e155a16804042c00350000507660502640d804d414040100120801115813107510108000f1820302104e4200304052000c103000e900181081003581e07074007003003030415030302c3d0341c2404946062f071034008840c1084590002900603000c20300c201e052001d420aa103205030000402400002d0319102e41e4000c900819440c82e400100c0c00c4001d10001d10ba400c00100050100380e00001e5040059000502c1a00c202900f900c0008542c50705005020f0505c1c0315603842491022a107290940601c401030020b65140d14980c0e185c50b410070301600344000d031800aa007283e00140240458242822168020b100e16119680401c0c549640c02c0b0550030030380000b9141941588800d03040c110143c005450104400840382ca80707540e519035080010b40c3d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 951926061 1250 951924811 951924859
    0x350601230d0b030f07150f0915050315040c3002032a030f06120c220b010215060418051203010e070825110601090903180b0306040b 58
    0x41c000c180802d40b02e1040c0c0526007088030301e40e2509500e8010361030030b0041051503510b040c41440b003031030010221001b90300c0c00ca4841d28107030440c0b04020382801c4980c2d00603520501860045410084584c2900a9542000104c40d100c09090001c5420444030116103000452180d4802c00c0c1500c1080008000100c900304a038130031038a44040d0540003c0f62221602445440700f00782041c111001d1660030070300d5120a004070000c046034855514a00c500c4000c000034072654500180c09403001c0f1541c1403030301d819074030078404c40303503c6030300c10b181c48441a4036610016521100c80044840400070303440707803070521010301024413840d649e000030b841c031110000d178082014021810f0b140b0100d0707459504054000c0a00b6001a0003101000507041c00d10100c0440902d441611941008120b00850a04e031400e8070403031145907000f01e490194000001e0001040d4104040140c030942d10303800480f02c0c2070f03402c0c582c4030014081c0540e424024030004110741415071142210840040c800301071440c0344811344032020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 951927311 1250 951926061 951926077
    0x7151110020a02010b190b0711061209011b051e090a030b070f1d090417040905041104201606060303030b12060c0906070206090301090335060123 64
    0x1940002e202c0501942841082402c0008030359246144001d0202800605418001d02c90401400540e036000c0110b4486603443d1824041c1800b9101c0c2c4c42c050b0201181c41e421500c1c2c03106035082c6911a1b10001501e44420411405512040d00303000d806488080013040741d00e04da032040b800401848100f03545451280d00114842c41020126103801440201500103100d40d180610030750000303105021404001d8143d0f414019595100c65656900b000010008000b00034100c50000280c00301c3c14603101d8120f527100354001c031050f1074504051024401251800d00402640c43d80c4000c0b0103d15034005401000c076504050f600204441803510f41c80c044880c01d44c000c901013640c2e401c0200540c1011011030100c0146000036040c2c42c0380500804103e41324050300301d4842c2e800029000b04558030b40342502c0340401301a008000b0100b0b9031a015040b010380030a2060180e515040104480d0100362820240d2000060a2841901c41d0700c01501c5044240b800725044850743d5099030510428074002d80300320 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 951928561 1250 951927311 951927343
    0x18110a090231240210020a051b07030602190305010506131a0d0519051b04180908070605062e050f3703110a0e060c070905071e02071511 60
    0x6000d0f145010b850495030181580500c3e00500c40b11030001c1c2c0180a4883d050301c009002d54142c0e2204010506201d00c80d0030042c0300b184080f810305401f4400c892080104890754800300266600c54082107100d000701140c0042101e001007080c0500a0544000300350310352640c09a5007802c1e0150705041c1940e100701e03644040001a400d14031890001405007541004140d502c1c90000e9212010421061007a400f600e41c1180c1c00d080d92810342e42d04c07588a6511560031203d401d1310384109140c0200902000d6030001d1262201010041d00b510740d1a00c000c0890841d50a03020000070052030980d1b240c0c0046020000c02c080901c5034002c00580c081c805542102c102881a09040f440c00001d404607001510780f4040615022268074004100001c80b001c580c01d0781005074401d82d0850009881e4031580881e00500c1c00f80e0071001a40123103c1c1c109a000d0380c05512401580c01c4050764100c04804040304080040e84100e00811413400c515066580d08000ba24040c04080741c1e4410652a0080030360701c2c1e5040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 951929811 1250 951928561 951928619
    0x1b030d09060501120c03060216050f070602061e0610120f0516050a02061f050a060e011d060a0f020304052206090509030a0e0418110a090231 62
    0xc0011a108140c00b5284c0d926602d01400360580390022a031642d4040117110035800590a01214802080c041d10903034008112405c00c80ca03a61203d85654413841008054030549010a510b01c040645e00c0001800c0d65034004110355842c4108400d01485a10380c0090001d418004030890300701c1e0007407581000b1020004142c509200f40f089200030500c114490404c4424001515080d6002c1252034020070145280400ca165010000c040e0042136409550701600400c000110a40c21100f040300f403035826201c9000d100d110a110f80400c00700080001e40c0428100442041d480c01820f0b0050100c0c483d03c11241025210f02c04545c15030405248042c00c55038100300c450002003640a0701001c1c000d555000d014a0a085031041d41d40d000c2d98549c031040c40272001d1500070584507503210024032190702d208000d14000030b05044120220034440d5500910703118001042e08242802110a443c0410b0008860940581c2042084000c0e000a04018142d54640066076490030006c00500c0905842c1f0008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 951931061 1250 951929811 951929813
    0x9080409050f0907210f02130e07080123040201081801020a050702030105090a420504110405060a050d1502031e1014011103160c050a06020114040204021b030d09 71
    0x49014440c0d4850481e42040c15082d00103c0e1800715035000c0303030380d01c00c00100c0160401c7c800160240b10020305400303281c5c81d02000d1082c683c1c00141280c00c48542000030044100411814072000c25142d50101e01d03099048003040041d40315100003a4484001444400b4400103441c1881c03e81c1d0044041c800000d030f001c10300d0f106600c1c00384a480e401180320b1005003825005542e906910301002d40c0c405454001c00a80340d030b01010541147c502040c07010040c0d81c10652448141401003809944c00d495007011aa0418280d003800d01c11907010703036001054642c2c12407404040240126006004803140450400307450729001d09400558002d807515580382580903916155001d14500003400d010f8140104801005000000e00c3c8000001d0003e01e0550350000c00c0c003e480740345105030b03402d100c138444500d4007150611400c3c110101c10740b102200e2603c070032641d42c02e08a00b80c88814044881c40c17241c0c0c0300400c0062800d54020000c1080111b20748403c41c2603900d8039421070301300a2090403d40c0d1100300b504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 951932311 1250 951931061 951931063
    0x80c210622062c0112021f080412020d0909110c12031f150315030b040c0905070311031914070801030b0c0a02030304030f140406050d0501050d050d0309080409050f09 73
    0x1e40029048001540310404114103d07940d01418410384408186048205082d91141d400948528221180c00032180e411102c00070400403048905484440b9404031100d5140d20110b0070101040c2d05640d00038005007803c4a250040052444030b4074032071002c01c0711200e10b207c180850301c1d45e1031003885540d840c3d1500e00304424000010505102c1646441a014013000d91041c040c500044940d140005544141c0d803410364900c1119000a810070302d1407402c1004201c0c00510400c2070354180c82d030900a42d210803d017a810b6405504810700c4984050000a1b100031980c14480c0a41040d0b18000c54210f8a289040b4918007082c1c42d01b0300050302c200018001c2c4000000c40b15084034250707009074038010b0059402901e902001d080202000110315404400b00c2c42044220100c40001e8503155483ea900c08010b0b14a031701c0387d2986030a45091100000e4185007100104103101d8009005c0c10040c1c20f4282708800400e01544200c56a40c000d22001c80c0c1c030081442054890b000c00c1581040e02d04084402c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 951933561 1250 951932311 951932339
    0x306090a060308041406070c0306380108040812010b041a091e0a030b0901020c01051e01120303020c070902041d0403050904021602060a02030703080c21062206 70
    0x840e01070601008000003240304084070102d60400c880d01c0103a400d003100040e06442414806400f1003090080401480301c1c507800f10038004042c407000004903011040465080e012600340e41d0fa44075800400240c5940030303401d202da000e80304060302d17441c2548010402c07407044020381241c00303800e00101d818010301c18941411b08680b0121480c1314140242030001a030400c540300c0320003135003c012142c0d82700551200820880a035a22441c0032440340b500a0300d50b4004c0d0032105024a19600b048003184004003030080d284038440d50404000b1043c0c3c02d203a04000800c18104044023050382c01c100d0714075040340600440d406061180c00259845180480d0044804178405100c4c1402c1000740510000940150483d443c0319421350700941c55911280091020f141e91100294000c2d10004101c10740300d40c088002c1c000b00d807180d15480703015282c0810b403903031600840c0032a283c4181c00b031031220b649c0401c64915651220700244444815920421035080c0280c506140d0800d47e40c8695041c031549612a80d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 951934811 1250 951933561 951933571
    0xc080f0c01090f06240305031e0d0f150f0302030d081e072c0f040e030408011103090f0d02030a08040f12120b01030209061b0106031a0402030601060311070605060604080a0305030609 80
    0x2000c3c01c0e0f9811342c7c0710703da102d101d80318019181e400c103002e00c4131000004409940079060b2441e4100202245414000c01401003041981a400160680410342c1c917000303074801040e04d4020b001806000d03c01941039030745078005032200d203080120009008086d40104200d501c9003026a0f02c01c00d40506100c01c0c4041400b400c0145101120390002481c800d444601440c9640c8074220750108040141d4032105003980f003030f44c00c6084e1950800c451132402200c04402180101c0148085520000f18401d84a8641c00c06640500041c0c00c100a00c0a600344a4102c946d0024090700c650749540d2841c0c1d440e81d88103440c6032442c6c03000c02e000c0850b28a4a0f80b8030b101d40c412520303003030034107500c0e0107a80c000003120352082c40c401e440c0b408030814110b030380300030254001d2001c0c507400208401400d4142d4503400c140242110100d1207413207840c0021a80303d210307010b90000c19944214407402c2c1079441c2d40300005040014105504414103210004d0320b050108004900395029446503943c9040c00c5050000b00000140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 951936061 1250 951934811 951934871
    0x4090807290a1a09060a08030c01020712020f120c031c0c030506041505210a080d0605010207030809100e090c0a110606030a140109020a091a010c080f0c01090f06 71
    0x2061485003180383c0d055000c0500444409a1030368916002808607115a0059009440b0200300380080d454154020282079010780458040014841401c9944069500c502e0314179820851000c500f16105001400c00801c0f484240c905007641140340d1403e100000700b9441d88291284440383e110381e014402c0350380141081e03405106044c0b000355541da45600d244200c07030083d120750105484680e41521210350311060342040d20131410f4a410400b00c250041701038114a280b0788a4002040e600010b1224201c0e5841200c650800e20030804101039801d400d070403a4207000d01005074885940d52850814400c20035180001c1d1180c0300f510300240f00c03108200f100c10195000340f040c072034070340d500162003000c60b94011210b045064100300994050281681c0094220881e141701151056a54203d0074550210050200c00c08108400445252580b1407001d40f0b802001c0015600103410180140035914502d4000304030320030035558041071942485ca05a03811903461022181c0c4005080441c4010700701c0394 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 951937311 1250 951936061 951936071
    0x120a051e06010f0c1b050108070306060f0e03031c05100e061e03190b010e0a0b18070309020a0e0402010207080a1a1e1009060605120604090807290a 65
    0x419269510006070007070341846000401c0d0a0b025109001d000005540142c0b6404900c00599080b0f80c2c035001402018086441000040c4000e44070b4402c11089552559610890a00d024010b50740c1c50340d00300300c8ae9010702003000300c4849800c4103d140070400c030142100013000e01d850201c039002c0d41201d401192003001c03510103000d0140d60702e05d000359910701d00c1c44549420320504000131b80340c02282049c118174244c0307119071201800700c0c00001074100d6900c06036104040d51a18824811201040c40555100014621202840f0151481150311070031a0800061084141e000500105c445501149145485804200443d40d05000750b900403c070300c030001c0651005640e00c40080034502480e19484a840c10f0008944501c1c00d4400440d200204201a005c1d081001b0001c1280c1c01502030308111a0802000107290b074820800c41d880201d03c8030201c64940c60301010440601005c1905492181090048ae4003046031504900f020606601c1e91120401140025120b000340007440100d02500c1c00d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 951938561 1250 951937311 951937351
    0x10e0102030d1116060515040912031a03250f0303080c0a0e10120b0916031e0c1101180f1e0b100302180c0906030a0f02120a05 56
    0x1c1e40c200b000c4111010505100001141c40c1c3c6004080008512440c0d5100c84010b018081d0301c41e500680310000890506078008080c4015258900c40080c0381c07640e85601404040d2181c0d1003149180304003070284450300d08040000e89001805400b0402c44412070754094004192440c0c07140003008520304136070701e8519548001c4e2498100900d10f50200070001080100c440c0302d00c1d9035503d400002860038410316481040240032032003082600501a20b00341034000309140000c0c0701486115450b0420f82064003000e000c40140034101c0d0f50700700b88660303161109201d420502401c20402c046550b00380d84c5d100c01003441425180001103105160031120201340109032010120710119400c02d00c2c03840c00d8003046031040c101031403002c1c02410b488148428400c80800c6058184102e038001c8440895616500c0c640f00101102610f40a800d40c008024005140c2800c2000e5a8030203031110000071100010110282031740c1c004a40b05002c0807e050800c020480184102c54028100c956124040d40407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 951939811 1250 951938561 951938563
    0xf011209151a0a140f1903080a05091804050616020f120a0f0806010c021c0209010b1809090a020111150708010609060201090b04030305060a030206071104050903031003081303120809010b010e0102 86
    0x2050b4030650013200c652035914409030041d0014001140d00c0851141c0e227035002800203215400000d10988110b204802c45803d886095181c54000c0f50440c0c0900740300d445540d07034082542403d803140350960045006130f5018040501c055110109100003080d640c100c8128000d0480c0440d5490406104d101001c0c004142d0740418100032540d4145c1d004402a82c1301d8180301088100014025440b1031000004180002100054080c07511948140605e640030f4404010602d1070498014941c0e5200c51482c40142d03101341070140b041d058a00c2a1000210104074840d81c03501d00b15201c0001c12200401000302c954001c203044010900d910081012610541e1400d84c001c0c000b4102030100364a94000c10110b40d07520306110011035004002c80c7d519002d92600002c98512468010b00c69403800c8001204c1403004800c82e4464176404e030b03202005504540e2403c03a02e0700300004600f900000c0810120005240c0900c0206502540e10344000502d0440e62041c02d5420500d08a4100702d604001e03981e079039030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 951941061 1250 951939811 951939829
    0xb010b18010903170f090405041506080a02011e09210302060f07080f270c130b060d051f080c09100b040605030415091a060f011209151a0a14 62
    0x202c0580029a110064100d0205e0360050b500b00039800303840c02051100300040c2100481c100c01c00c1c200140203103951a8089601d580c49654080d01207001c0b21817010b2041c281c13000740c82c0103206a040c800c00d0f8540300d42c10001075000f240c20112074007145801120a154042100682c000851090740081d4a4030f04001025404003a00b00e45101c54802c010400240111075450700f40508082800d94402454042d19961114240114003aa260320401c0384031103018022410750b0303a00600081e02e000c0c40f1126401c01002c00500c107080301d5540801c4080356201c10003401005080d01d60003046617901100400070340000152980485403a0034a0400c40c1903d41c20617074084072500d00b05541c40e503480b424103c0001c00312445105440d4a429030050412040f0015035043d10f10f204148456603030740c0c0c02030100c03040c0792480c900e0110300518aa1000e030703290394010401052182150060074045418458142c0b83c02c40031402019a130529968064202601c00c140140540c0f1040403441d0714810110305408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 951942311 1250 951941061 951941093
    0x18090c090e0c04120b040203070308131d0403020c011202210106020c0f013e0d0f17040206070602071b230d020603070c0c0b04091112220b010b18010903 67
    0x8a41c2c2c5c400501550b4050022900454101d0079079507551440d1112141c0080c158001e00030f10160600d80d0070b18200884020300d1003031360305070010b165946400c001174a1103000d000013100000c2c2c007040508202c08820345001007085240303401d000b040d4100744000c4c0c14484111180c90060008c52188941aa1701080f2546464a08211170f10b032111481400c3c6800070305c00c6c0303500d949162080c1c08900c10180c00a140c40200c0c1495660b111403962490f411106052004141d5181e90701e44c001140140c81c00e10010710140b48260b0b001441e2107696510041c2000c480072010b1010b0070011020080c0e08030300440c085054004a062003048540720780010801c100182d4007900803440440007072400e5014107910a500d0380c205030500c68407507480c1e01c0740010f81d1190103aaa1040d04201240098188520a0718609d68440b0b00028041e9245d0401c0e0030764902481c500000d0484900c604030200358019010303806800110740480e9280e6400d070000d420441c0b0200d040b130401210074801c101040384000d141e5810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 951943561 1250 951942311 951942323
    0x7050a020f03010c232101050a081c03181202060613090206030a020f0f03090c1822030203041a040306110403050a0b040c0302180603060a0510030318090c090e0c0412 73
    0x2d1a010840c00b501406005002c0e40e4804422911105055200003000c7c12580121260050076854031819500c40c100c0540c402c2d00304009824400c0c01c00d0280e00a0007001201c1c41004e0340ea611a40c0713a040030f001c1400341e244003607045403040c42200d06158544c0542e0108411080c840005580d000c211503110080842e10600e5010904200d41c040340c1007102e2140c102c4c800740d02e031030341040e039051034940081084051040111000e80e41201035100b400c0d600c10324001d1019488006401a011920341004404404501040002040c40101010721030400c29170400096215030451074420101e98500c050132821080600c400c00c001030340001d8486200e40d00100c1d142c0c1d03a8540e89001030344003015802c000d51059008154803a0b010810428074803603c411011240c40d5101c010600c812600191000d80300d0507100c00d024000301e40180e1082c03135011008080c1c004030943d2004201c0850300080c081c40002000000100002d10105190381d80100180369102e03e8070b460a8201040c20b071406100401d0307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 951944811 1250 951943561 951943607
    0x3071220070503040e1e0609040c140f0402191215031205040f03060c020615012307050f0f0d09141513030302030c0709090c03030810080307050a020f03010c 69
    0x10050300740140e8005041c03008001d955400c20700c68542e020144038151a5186c04100002003440c600b08a0480c01140c11501001400c2d0a00111004240c15a5a0107070001000b8059054548035131008242055010071a04124084040c0c020035001030409030b080082c0c1170418480103843d24903005001c0360b500c40320001e17130040000c80c15a000d0003030384d01c240548462000b0000a201b40c5070000a250302d0710340d00341d5070030742e0703510001c50303181002e14106a002640842c4100c011480800c08502140007003610142808540e650f211b02c0e20318080b1091000c0c0c2c00899054810007410080c000c44c079881801c08580d400d040c14164184403542002c41807041c851031301500f1640c1807120484400741030303110114040d2910703401d000e903907039005112624603031040d45030020310180e0b548a42d0b9075003540001c1400a003031942d10101c2d07858401908201030181071a0740000c0804080000344075030380c801c901a1134049150300401000541d140da000b03000b64105032090403c9a444034009103455000002c0e014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 951946061 1250 951944811 951944813
    0xc021912110f0106090b010905011b0303050601021f061a0c210f03281a04020307020106170d2a0f0303020c100501080f01090b0403030209030c0d080307122007 70
    0x310b001040c5080b00303040d520b0316001180170b400d01c1c0c019580303030780342070f00e41c0d81c8519034540c01158040d110a0100089502c1d14280c0c00000b44607800c40750f08000e05204075040e0740c184800003d10010780c00b84181c801d0303584620410815550b0302414480c07014083d011420701c10720356411b9854a00060b41014146206d9104101002c0c82c00c050310130105d10703005050307180d142101c102d8024004e007903024003a0030b40c40c030100c00e5000f05a00440f1601c075505002225001e260b03a06020194001801b84d0003955201c40001c580c0781520400b0505c1810f184c4020300054441901c082c1000b42500070300d090f5648105444413800c0c000061042c50741c6c0d07103d0400b0007098405e0408030b00a000350409026940240e080c001c0111507160007003810780d103440040d19200301582044900f00e51400a005040030032010002d0046402130707020b00001d500141c16280c508800350300084840442c200d00b110441408030602008541c0917001450342c07540c0f1601041100300141e400c281456003400a5203110300300140c504 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 951947311 1250 951946061 951946063
    0x1d1e070c0c0e07120b22050a020405100507110f091807170c13090302061f050628020109082205060301080f0f0601061209031b0302010c02191211 64
    0x10010000b021009245080000004203c0071508074040a901d082801006031850a8105180d0500342410b010446080c8401c0d11005801c1c000d114900ca0f55080c480065282c80b42203800c6415611995000e40d240700a10b410080300c070401d08032901801e41d0480c41d00e160f8484400b06500550307555000103060300040c41c03003031610007943c10400aa0055130184420411f0004804122107000c85130340c01c100643c4200c1404540701d40002400590200e0b001c1200d40b4142030402c480e5141210200400e15118000710304190302482101d000d1041d1504842c1c3c4261103d01d40c0c6020b50701d00d1000f0700034a00c1c6625284894055908001b44070300d1000075041b9031488880c04840148005000142c0700c0d80e590340342e0b81d02e40740c6062034540103001d0021039145080001c203240341a0760054484800d41c01e1803542c20002452050701c11018000c508801c04000e20000407041c031402c2c4640d0010a0030344c0c040070000c2c00d29098103100c0c01c005500f94000f10001d461146d2082c4501c01506d060901d03101d06421603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 951948561 1250 951947311 951947333
    0x2030a0902030f0105011505030405070509040212070e0105040b030d020d05030907050a08030702030106080d12020a050c01051f140105030a0216020d030207080d080112060b0411041d1e070c 83
    0x70b60622880404101e54941900020304a800403003904c19083d013991000d071840d2004803001000e81d0401c0c90144924900326102c2c62b0024000f8008515440c040c141280c60f1540903000030801c0d11040300100251324050080c201c114400303401400781860280306c0030355114880d04009d400c0c0f06001c070025100c45030400c24040244002010400c85c10354640040740c036540404000c0c0d019500307102002c40d4000c400203000403002e02c6960303440c0d03407901c0716004c04e0300070340060a159003000410080214044000d02916000c0e01604840780c051800c0039542800740401c0c0c0e8000107203030720800c0000a26030b0b0405c0c00d9a5200c5c0180030090380d109902e41408280540c45000294407084658a01050550000c0c084058902c114100c9001d0242c03504182c9a2078400d20898680c2c0f452241000b00207915130308580b020f14400340000c64000300110381c80910381c0180e041100c070079014220404001c1540404260000c80d610300610320324607c0da08001e10780a00504407401c2c424505610820070040340d00c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 951949811 1250 951948561 951948563
    0x1b0903030d050a0f2918040809040921120b010512150307081605010e0d0f0311071e0f1a070c090f0903031401150e040b060c01050714030c03040602030a09 68
    0xc1003510141d1145091030702e80c0f80030b000e28114030821001c5690900403102941e00c5c0081114101c1503440d48e44000c0170707900451071a03030401d45521003c00000c0c0ca041c0d81500400755108469001124201d00a00015002421100080c240210b410050360000116400700300899503000807980e6221440351000901c1001d5900b41c0300388400007070042004100f2a003034544999891802c250f40e5401111900306500c0030540c450710b150780c0c0c000002c8420354504a4907120b8203190621903c0640e1650a2007100c3c0d01a41210340c1854001303041c1d030031f11441c240182840010424241d418540281034444110103070264070389001461106024917148180000c208500d800e1084a04680900000d08000e003000ca001c00e052051a0200a800d030300d400e4165482620402c80350303034460504841c12000028143d800070380d1040d021015403aa50000c01c8004051800401c80d8140004003c2070746510f9030748007940d100b0a1041c00410741c070080840360003640041015840f030b11109400b1700242804a4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 951951061 1250 951949811 951949841
    0x105060a090e090102130e010b1b15040809030d050c060c1e0406030f0f02030712240f0e090a110405060a0e04051c11030412030e060408061b0903030d050a 68
    0x8100402c3c40415002049004003c40c00018041c0e511000218031300c40c04e016100d8800414018031052000c082e46109040f0800c0c000c564000d03101030400c0c1c8188005903010b4810950008603802941070070406c0405400d66440c10901d05800f10030429216a00544081e201c1c00e000288610b0310b44080c80c40100e01c40868440aa031580d403041c001e030061090b01380b103202d190b042204c1602d144e0f80301d20079248608615110081c112401d01600310061003542c0ca2003440d00d501c800c944010840d81d680d40e1010f4202c01074404041c508001e0f01d00003a040040c0390810036400565a080050400d00c0391030b00185040da4086000e845190004c1c0c00185a0b0b085004c2c0d01800100300024804002a45c414240c448038013604032414481c0220f4107541e000c204100940d20801c410070801d03068110b004061030081c58840440b1944a002031616801944030400c0e81e400310341441360081d201640c03441b41c807070104651490100320380d0109490f8044c00c3d1310084420b030b94200241e800c0000790840301e520703800d41c3c2c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 951952311 1250 951951061 951951089
    0x160f050d0318080c0a0b0403030f0305060a1701050f091f0924020909090607091701061214010b01210b0102010e191b030503070b04060e03030f012c0105060a09 70
    0x11400700e0340e8103940150b0130303ca402001c3c000286c801c0303100202d0381135030b4040c0e0700d555004010340c00542c0500307005420160000c1c0844400124015081124040400d510002040604058903581049203019080c0d038001d802c040f9828000140c440780340074400c0f0726104007140d84043c50500c5903100d021818280c1c60003000500251310180c3d150300400209004582c040815145c4410040c0d6440d0201c41c500c0205490500501412540850004c03060050380008204280c90302400c04890280000445040c15064441d100100c402c2c000c1c2291070b00c0a10b0016000400103494900e1580c00c1c000d076000c000c1e41c1d140441e941d03034800c0d0400c0b030242032060304884002c2040003415104006d8498140c071400e1281d20701c0010091400321800403070b500b00000314107180307a68540350600100900212102666aa40d40d0390202d014005144600101c2441d071490758980a29a0014080704c03260021800d1a6110560b018002c0034005066a1050307598545852441c44255001c070559040104594400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 951953561 1250 951952311 951952319
    0x20d03120c0c050618060117010209031002031b0c100e21130b1303120516050703030908060708012d03060c02070b1e030709090507090305160f050d0318 67
    0x1000010300340c184240d0481d1030740d03940c0502e805c0141d0101c00300016950410303401089915682c19401c00000f114200041c5480c15940000703180c41e80001410505a401000700301c41b852480080701d0404851081e05468500c46054030713a212111000ca58011039074030803010714848400c002030544c00300c1e01d203004083c440405e0303400c410540000456007100103003010040303051006078007500c0c1d041600d0040030105a0841d5986070302003c3c6800903c0c00c01005010f1900c8895520740b90b1120280228080c1c6241821402e000f001c60000340c21491039640503900313000c0f0f0994088640c604403004084c004040300c5852501c481040d80740100d000000044440c003005121240d0300905080410340c0880340c1d0199148038111050054071221000b04d5410b5030b01c0681c6031602c00007181c0c08552494079414090b19800c6000484600741c03480700009600c48818410484104480e040d130f01e003140c134900282d6160a9451004c0c1304c8601038a4050415040c2071420580070709014401c110700c0c101c07064000394032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 951954811 1250 951953561 951953567
    0x601120207081c05071d130b0303030408090319030e0f040608100e01050702060403020601140402090a170c010e0a09232a0a0e061b01050c300103020d03120c 69
    0xd030940c402c081c1d1605000c101400e0098081c1460303802c628942d070880c2031b411810408404040d0a07050f8107186ca810542019960600c0214481d0380301e071505545602c104802e2516100c400780d1880740c8113a110502e4000b01e0340008420803003a00407a141d490210420000c00c0252100703901001061041c3c0103105240000781d04050403a84c5004020407003542e0b8100700b2039030f8640640b0054003607088613005110300380800220159007200a00058070704106400414402c8030700c2e40c801d621201e00d0040c01e400c0840f081c444140450002d1810100c1510380c6400240300103828414103585c41e0795020140240c0c0d15000b4071110010350303010301401901d09174400921040000381300c41e451903407402a280207a50014180c031400b81080e134070300280b03040c01c10a02c4100c0d40016212018404010921950040c0034005d49101d260b02000c041d4031340c90300812150030b0602d1810484050194455100c0c2d2005d520000b10303044980444007842a54801e0605464014030807040f0b00d685424110102107540d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 951956061 1250 951954811 951954847
    0xf21052b061d16170702012304110a140607021c0f02130c09030201110c030f0705010e0406050609010302031314060711030910110102040b030a0902030f0a0b060112020708 75
    0xb8114070800d0391800e007400b0032550180030b224040342c11a03454150b18105a40b01da40d2001c440e000005414190b4a42040d801d03aa006240c1e00a108020801c002c00c44d1002c3c4040701c824007640d400b51254200030038520001c6090030284e020f807602041038800d5560751060601d80e000280300c1c1e0300d48141c0302d04002410040859080e0f0242c01410421034540b8081d1196240c0c80c0310b29911074903100c0c19035004440340c00d40c48012071080c0c07040455080036940c1c2400601c605030341840051080e1464032002400c4075500c240c0c40b130320551615108000a4841c40215658140d091800580d280d40d181100b241c40d003006100a84404020100082940c000244c0140607500c682c50701c0c0da601f010049032558138861540010342050b00f181c1c410420a028068000c1c41ca103200001500745511907041021582003210100c1906450303000000c19400c1c1807002001c000161000340040a09688400001250160030070381048500080c4506034003259054a40440d401a0595900d00780d040b0004d079545 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 951957311 1250 951956061 951956099
    0x403050c0f010f0c080a0309150606030c02030c07260d020c0901050f060a030c0509030a03021507021c12091401090c0801180f080d0501030f21052b06 66
    0x20600841d1032298001c980341c400010007076552480711910703aa2605c009400007103601080c035485020000c001226000719460b88410040001502850604001c003039071030100014045d0b4004209d28020a81c001c40d94000f90786140c440450301c1036292001d101c52440e0456003101c0c078026020041ca590b50302084200c2d100904440c5000036903220410070507400010f80445c0c4c0d0001042010701e1340c09000f41c0183c81030300300d6401c005050000003404a810700d1803e02003240103030400c80c0e425071040056550b0303d41001a510040040c0c40d15945101e114084040004080c407010003030068003d06650803160f00154401c505644101c007034011640623100701c183c1120b85900c5840c000c40e12990500c41c1076003561150071601100d0f1002d440e030100800007102c051342c070840e040000e11074810321400b41038000e6109580703552218402d400c0a4181841d10404007000d41c0100040d1014103600006540c42c0e01007046440d0285d1188042c4002c84138840742c0d03031600d4070b8101100007440e1032807061880540c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 951958561 1250 951957311 951957319
    0x6010e060f28050a08011e0902030304052209060e06132a090903081609080a020906240903010f0203060306010e130c140112090510020a0e060403050c 66
    0x551122000c22007902000c201c0303290010501645500560200b00030010385600c060300801e00942c549020a00d446080d800c40c0e48981e446900381e20590300d011000b250080c00c0e0744410010f185140c2e0001751280700303034400c052084e101c65100d00c1420103584942489400070842c200180e06062400074040c0c0680d443d148294007034080010074406919040401c070560001c000800c80004c5c00b40118200c1404011b100741120a0b00c010416040a00c01c611906000341c0362416a86005e9030302900e0604070b0b40700102040140751080010707000000786080f071242d0450b05018036641d80c901140224800c402215004118407c1c10084415410014500e9810550003400b043c1c051040c11000e0f8030013510b241d5015481800108102c1d540d041075540c01c98081d1a06020428490301c039074500d900702d80c004c004002651001ca5016680100084003d02100c0005225541181d2180d5441c0e070300c00f10034429016000074122084510542211f610094018800c60301d90303480b0304103142d1741d00c0f440d0304460013 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 951959811 1250 951958561 951958589
    0x21052107110c01090902031b0417011515080601053a060315050403020f030a021b04050c030402010f0e1008040203100b0d0f0c050d08070b0c0c030a230c0601 69
    0x1a00001254032002c008041c0c44158225107420340301402544006c2c40030405107800b695800090010f10300500040c880a8098610030081180440c210760380d0341c002c480c5075070740346808205054003d0102d401070002810302800e80da448074010303602d521a03a42c40161a60340e60f0000940320318a048101c141c14040340c0050980c521080d41d00381101d030940009002d20701d420016401d65100794000942c00351180c416540c0c482125507403146150070280d0190003582081c400ca507403206419402d048000f10884d03040c00a42080c551140d001d10000d440a410040400c0100303440c98081c40181007a40300c06092030a032008031480c010b05115080d10100d1290084031031481d036903c41070007000c034111802040361004080d95901c8228042101c0000c03910801c0320803000403241d0b02c04049098040c05209071a50741c1500e0b1604a8012600905504040b01e0900c070f007007280f240010507100c20401904181d122003070300e025034000001c080703c8405041d50000030080041507020443d03604075a46c61400080d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 951961061 1250 951959811 951959837
    0x1050702010b21071e0e06030703110607020a150504060e0d0c121a0703020304060c020a0c0512030c100e06071e0c1b091a090421052107 60
    0x400e03075a02180459001c0350f01001900f110040d02062540040380008903007034aa0f40d440060b03c2c4500124054000f4241d500040294a200300c404591210040780645003880c116a40d44007001c5d481d02d4482e0180710003181d43c034219240d24400b0000351485c60305e400c420b0b800d1540002c02d5a40b2030f007d2800000c4000740200c6090400021001101351304c00011f408040c1464031100051291103015a010410708100245004a411940d13020300340658000d40e8a191500781681591401c5c0361a00465103e010803030040381d00742e80303108180d602c112120804242d1155900c1c2c03950142d4950800c4c1406004040011007a965105c0e4078122401c40c2682c455645d0088191100300c40c0000702d022011401c1e0030100754a1096180c10040b51140003142c059030f41c080007010390142b080d0010b010503542d8540d40410108039500503203100c081107821403001d1900b03a07581c0d111000b419408480d0f00d8100b01492800502030001e45c0c0140260743d5806000d8401404c0785454035109031081c0e0041014940c07050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 951962311 1250 951961061 951961063
    0x100c03020705030d18120807090501081603020307020703020a08010525050304020616140d12021813090506240103050112021905130516020307051002070507050418030201050702 78
    0x6803865000702c051400e1003040d90502020b0180d248910f45803018000c1e0041c0000c1d08552800448140755075500d1039031400b0f503409090600a50412414440c1c04003c00403c1d001c0000b10800e04a203c0c500581c580e16640d038164a01856a00300944c8401e0500e404142140c2c150f100500c5004400312401190006403411400350b504a84241c00060040000030b0160408100500341041004c200751000c90441d01e49182d40803240c6000b200540029214001481d4040c000107450010000708601d0008031800d22030404c6d01d006051409103204d8482c4400324034003030f4044200e06801806850340c2d0301e003400080803102c0c000001051210311036a90419554480c3c0b29a5043c1c903003e03800044601100e408018200000790341ca001c04107440320004c54241c5404196240300c4001030008215418420038401041469040003000c5500906c108004540300203004ea00c0201e028000603a50303501820181c0c01c2ca4516000385400608003203910088100c00300d04800a00c0c0a40c4c000c01298940150403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 951963561 1250 951962311 951962317
    0x2f070f060e0f060f040e070c0c0e0402040e010614090a0e030f0d06061b0311160602031213030f080a020f040f030308070f0e0f18070201020430080306030c0a08100c0302 74
    0x3124841c0130501003440810003200501e03401205c6d40c184088450219a10b40000340c3d080d070807000071585010103000840c2000d01a003000d02c2c00ba000240602400c15000c4101c62103e100d842c0c2c03141c8203075000310f00341140f15849101c4ca40e482009482d43c031000b60016003911750040c040030134000c0c40c040340003c011340700d01a036078955012014403290141090701c044910000946030144a40502407400000003003a081e10380c000e00050b006582c03290b82420380c010f60801d0040484250711407454029001070f034000340400000307549003842100b0380c0700d00108400a004c0d1228204107141d000a01041904225041034112403180d507035008681e070f407081c08840d03c00070f88021102107503100707600c0402c6142015211118020103446a0224070a07000410683c0500780c81e0f020150354009420700590054003504181d44000e04007130740e42d1014a0110095070019080c01605609000c004105035039818000100c0c0c01ca00207006203052074981c015a40c680681c1504400c03500c4c41d03c0c1004021500a0080d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 951964811 1250 951963561 951963577
    0x180906040c0f080304060c030e030109030e010311030f0408031009090f061b0c1401090812270303130f0231060b09040b040216050109030207062f070f060e0f06 70
    0x82c600300b500e404000d4417038a081c441f04506121100500c0ea0b803584091140a01090181d41e40104806440001500301c4888100c0d146d1b040c0300c10020010204944200c2c250030641c0440f000d980c80e03984842602c48142960440c10f46141891546400d01c40303610300140480b40504010030551340000f14000c02070b2800140d1501059903150780202099407000c4011030034007403400200301c001481d941c900700c5903c01c11031a00f40b04d0081060042c02c2e41c00145182091020340c038400880780303040350056560301000b42025150440b05004074100151070002070010303603020740502d15442203101500d8a0400030306000c01c800c28402100c107400d0725240100d13000ca46240441c2403178444200188405441c81c203680f260056020041c00303444000d00c07613150340d02c00d004d1400050b05802d186002070a000f0b00703074003007810804111024203512460360f680054041c3c0e100c11411589a407003c4050404200c0d80c8024080c111090001070780070303040381c01c80c5943e4408590b240c10300c400c200100401c601507061 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 951966061 1250 951964811 951964813
    0x140405010e0904051608030c0f010b0904060510150201090201183803010b120c0a05090f01111222060206010e1003020a091e0902060f09180906040c0f08 67
    0x8009407003424801103494101c0d010718241c0300003102c004501c200e400d00e01c3d48110074a41c030000c3c00100302c0c00140f101400c03181e030000091150201d81e00001c0c50740c0304042c1010748a0b56440c00400c1446c084d017501c40d40105824882514801c110324000b0703000301503643c1d0a074041031165900300b01c40902400c6501c25204040e20415034040800c12611108100e01054030306c0c003220348881020110000d021318020441510000e40c1d40300c0703511450104101c041c1032101000da0a00c01b005403d904a01500c95040058807a6000e804071440100d1f856694001d0b081c00383d004480030032000042c1c000c010718626040312042040505a0004004040344501c2000300580000e00148042c0c00d4410400c0d170405c0100307814030030445e22900003903140840c07944820780c40ba6581c050345400041f07101411100403550041041520308580215106100b000d00045040900040075140b65495042078070540c0e0100b107000100d894085072003a500c00043e10240c88456001c074001420548030421003040e105020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 951967311 1250 951966061 951966077
    0xc071412210d02041d010f23040e01150605090406080c0607020402090102071509060f021603020105030613020c0a0c080a082b0f0b100201020a0503010320030f030a14040501 76
    0x1610050301e50041e9100b284140d8007003000180c241d4080302401c8001802c0340c20070031194981484a0340d000000d51110020241c0324108040c0d03188000c40d13100b0a0030050307034003141e40881000410300400902130340400303085950700003081c01680300e0060310300620207036404c0250b1601c4000c0e95a031880c5145440d42d201000301300110050030300d9000341c801820180120703503103645c4a100c891850207005203060002070580d00308200150340840c80241c3c2200c076001601102c090400041066801d90001a0500c80c000010540c152900c61070282460440303041192a100900103290303e031156400c0c1034980e00076680000c1140030011516120710f9178800d0750b075480c0000b9414444540c2c4010109488441000740126804030140e0059403081144c007040018000320b40000c01c40b101081018080c00c41e0700c18400b9614894002d0212410345c2c1d0012640004580c010f10702101c850003d8220740c0d094061a4682d00d088540000502480c1c3c4142c0c0344e64080034462400c0050b07d004501c2014006038403d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 951968561 1250 951967311 951967363
    0x91e1104110403020d0b2a030f0c0f04180e03040b0d0507020118060b120d050a0e0f0a0f030c0519030b04140d0f14120106080a020c071412 61
    0x26481070203100040c0d10414200342d902c1d0001214a21111402d5401000318400c0100c0c03021290f00d5000010010001d8100400d240040e000c860b0100802603c503458047c0702240f440b003075410a94144800e42c2c0615940e403912075002c043c03203010b008000500b0904040f40c45e0540c5801009681c25900c81e01e1800d810840128a0040071f07000c01342540c3c00795543e901d25045004032000b403010b4614002e0f08081802c103c00c2052011000c40000ba1200540000480600466000303003129101425840c021203510755010002d4203489a03020105d5000304140400909980c5c400c41000807a4007e0200c46d1a859844060204121140742c8010440b0700c0410144005603006000c150420700514264203007030118081c41c3d282004903032068021170712078180740e0700c080e9102800980c100d220000c0c1d9414242055072007018042c3c18090142805032010000f084140386d40d042d5a082c0180744122082c09a5400401001444800525014061030890b2200f62180098030050110140110104011607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 951969811 1250 951968561 951968569
    0x20307290c160203010510050f0f0f010c0516080610080106060509040e03070c081608010b0a03140f06041a011d01090216080f092b0f06060b0d091e11 66
    0x318405100850320800d40b0310150300c1c244a00c034410f1020701801030780c00c2c2c201002c102c8080014810640304000006444180792100010702d622400c0c203080080c200082480c14904041002c5100711400410200000c1c190800155441c041d003200c42d124000795480d030ba1030314280c8007240070308404070720200020300144c1099808452a041503809070380c01c2a0390750340c0b0910b62507030390360252401b40e200c900d5200c2c0120f0b02e0710481008151103402000b10f00e2a50f0003040d8508414400642030100c0852218082035050040324440007104058403410314082c6130044c50001010911804150440c0c0041401c1c614281514900104091111407682c03a05044401a60191b001ca12141110301400740001d007074500503004070200301c142c442e00d42c6e00d088144070f4611407a86080d0300c00814800210b42e0701e002d407490801440d400c000c0100b201040f07810b01c20054881c5d41d02c0241c00c9440080d0640c01d01100b540240c03540c0b481841c0d80c0301e031544408080800070200600207011036401412880172850 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 951971061 1250 951969811 951969817
    0x9020a0806040b1605090618040b1c06111207030f060515030f07030e01090b09060601090302100f02031b0c090f2205240f0609010e010b09040615020307290c 69
    0x403803074803500c2c00c1c2003140412a543c0048c080c40c940e54044981100f6a40342602401484c0301040c0d4440c001032040841080d0308055943d00600181d0362584000406202a800c4030300a041045090000d42080394004005003a407440050042d46803d070701159601d018180d458000e0040b20302c4e45d0440d1262807044641d4070b00503005205042d0780d50041d0907a61803c1c02030b28031030b43c0030382211965071500d007900034203155000305410b04000700c8c54000d10059440000c09424030841d45031082158519100036441c5100380c01050345a540b88101d17090419400149a4100d00d0054850240c40c1c2c4600c1c0001101400545488800191446144100e03009440030044007a01507001c0f034016a0f4034200c2d909001000d008401c0700349000f04104042c60010b440340640103102951810750380d44c90401d090600b69018001d01c0d10696001804002540d581c0e00041c028041150004c5000800c00304040d50f26480150111800204040038010488010a8480500a0142919840c0d56a160406000b54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 951972311 1250 951971061 951971101
    0xd090303080432010906200f0a0c0f0b0601110c2803020904080c070b040303080408071a150120060414120d020703030e010506010f0311070b0a09020a0806040b 70
    0x201c0040f851000c0c1c00e075001e15000c602201400000c1420f4107080940540d40c1510941005001940880603500b81c0a0200c500c041c9540740d0035a240d014900040341c250902880207010401e500800005114502d9440c6000d0f0100f41c035030320007a407101e04126440320313140e11202e0352200030b05460003500381c4441032801621500e01f000711003d64032070b40014101e140a80c1c05552008021851000c410401c000301005020500d00e5142400e26566005180820040c0b00a043d400003045900400c240645e0540104004c0c1d00200001d24108248130304a8100c0e43e4010300041411100f5900c500c0392680c2e4281426030000602141d80d52900e80c0038031402c001588550034401e0859102c0743e40040005040485420440541e807030070700c2d0400900f9200424034801c91070349040248159030b81c0054011250b8449410b020901860300c4c456a40e5034040d41c54064408840b500810140014a0b4004010300e80300312014071b446512406040d60f2078800f110028107240310103012a02c881c2c0b817018410144 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 951973561 1250 951972311 951972353
    0x7181e15241b200a051008060405061c02041a0616170c03030f060a15020304031a0c030a15120f0b07050316050f0d0c110d0903030804 59
    0x15580da45071070141405108032075242860301c1003a404200d501100342c561454a030501400ca000700c80c0c0f101840c101c10700d1224400b8610405071020340b920340c40d02841c0180f070000c0654016140c0c403c8060482c0c1e0341100c405216901c0c180001d0164500000310906c814410449d5034241c2c1c0140d8248801000c45021131404d040e9140b117101441d998010080100c0c012400c0d207e05510407a2a0410b0301d0340b060450030785100b80500c540c420111000065a9011101241581e21522440c022038a610f1158220300c00e401c1c4920f40026560b9000001481141d101e540c4404411207100c0c2e29000e001400c2c1c4800c086640c08202140c0000c8447e0400c94984aa0140d01f5600716620800b800070482003650031249104c2000300c1e2424004d180000032781c48802410814070303510740503110381d4004e1014856582801b902249007078040b15040107aa2018aa014080017045000e20700070700b541010440d0040c161107052001c182c000e100349201005c80b540364030b070451070b030304e80e50f8565040184200c140d42c44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 951974811 1250 951973561 951973601
    0x3020c0907120f0b190e09060f040318050909032d19050c1c020105060d0b16090806010b1905040501141c09120306050f300a030207181e 60
    0x20545d19000c41114004074a100040d50900e000c800481c00d04000300854200c1d0404020811214905011b066000358145409002130212801100b0110711035003019400001480c10004856000401400c500100c2144040c502c83c4141c03581d200d100e819000d003054040f0030300041e40030070110701c4860b0310606942801824034420580315803402100780c0c0040500700525440a011035020300c11300f90045800c0e00d03085e00015150722010540100075040a85038449265007240b403522400500000c9d00100c0107980f100d50b907410300401141c010042440800c0031541c02da40750720340070300102c0c0c1c12120180c580e55007a240c8022414401c0e0004080c0b20740404401e01c10340912042c0344100c0d03010300d20444008c7d0407003420103401401c45686e5045180581030000d81c0c07030001d98a2881c9001400c5034603000c1002c51451000308901c13080306141d007503c0345c0715604046041507000f08078041076406580740314001e04925402401030740c182001b42e10800b6030600c995079541d24181c000b41d10f10521800103a0f4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 951976061 1250 951974811 951974831
    0x905192414032508010c08060a0b090f0603190218030f03130b0313020301052e03030e040c050909010e0403081b0702010c06020f130311010908030a05070201210903020c0907120f 78
    0x30070354082480340d800040b2101f04001c9189401203440015001c45d548880c24900e1503404210800352100e0b2a510548000c00060240000400312010310000c0100540d194405014a00c40c0c42558440d03443c8030340646100490130340c03000802d5942801407134501cbd01401d07107070a51020541e48054101134440d0030012401025842c240100740c003a00d800c2400203081c00d11052a4804212122440810b50001c0603040000c01c0e4084214225020300300d03000206140302400658151240f51941900103071b8900000408002508003240700314000d4680d07146030741c0c81e50001141c82400c1c0300c8001a48805111520140d4414031030060070304c0c42501c006180000c1903000350080c1d007281ca01081c10340c2272940b0500c06c1003041d08441d541d004003820a40641da050010480d204d0040f900c2e60005c03c04045081419a8410096007440081115200b0603d61000040030045c00c00340105402503c10050000d5082c105000305520900d01a610036105038410144040640340c6144000348260721017550903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 951977311 1250 951976061 951976063
    0x3160b0a0615230f18010305060406050a03020108150a030c08010b010201090b040b18010501080c030c090601090308130b07080306010e031b0103020a1707030204080609011103010905192414032508 86
    0x8900d007803401380902480303540e1400047c15250010092030140d401e00004100c913848490390f90055a6090030015401ea43c1c003400c9075051712072410304640c803244c0e0482c000213000c040e01000c000d4442610003030141d84138960059003622000f6000802602c504030018010444021440d60002030911003800d050840070712075429603030f00380c02554941e04603d002e1640e510301004a0b079441082a80d10701881c0c500310380046c00c150b0040c0310140c41000001100001c41e400d42ea1424058400c03140c203640c99103ca410070a1290300110761441c0407075005040c090b00c61070001820b181342c0c4281003000c281c91008400440c065000310108509212402d8400b2040c0407120070b24500c202080c0c0e40042e26140b60602551402a01421011003a4500166004454250011203040d500c000c2c00201d20382e2a600240103944000903600e69000d4039060b90695900d500032419101000703003c0751048859190040540550409604e1950543c01501818011850a000c9280d0303c210b604e048030803166180c0c19a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 951978417 1106 951977311 951977317
    0x8010b0d0c050d021804050f06030c1c0b090d090b04060921050303070806120f1c09051005190804020102030d05060303160b0a0615230f 60
    0x10300d456002d0011182d608120701d908640d50500035050170440d4103c45c003600d00c01c1b828000441e8890820702c62803809001c0040c040d120814544040112010001d5465503918824002060114a100308114821400040544008490f620004021000e40d80100d44045800e000030300041d680a4444e800703450030015640310032142e011543c0c07000310300d4460040042c03100204004546502000c0c01e03001d000c042d03580b80c03141c03c0e0600c3c00c00c2e281d18654142c0c2032544e00410104621035468180c2d800c407040542486104183c843c0042100c00c0380769441400420000903140c21440d01c001a4501d59400a140070034450406a0000351240318144040f54030b540c4410109003990380900031035040d202d03da2208140102585003085846d03104032a1071100d40c0c500540041e082c0000d05200c003802c0e0491380c0300c4036031010048241d2108010b80504801d500d0082c44080e0900c0b18007002 = true := by decide +kernel

theorem cover : BRFrame.Cov 951798561 951978417 := by
  have h0 := BRFrame.cov_init 951798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 951798561 ≤ n) (h2 : n < 951978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
