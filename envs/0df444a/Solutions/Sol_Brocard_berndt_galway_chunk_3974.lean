-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3974
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:12:27.18561+00:00
-- url     : https://prove2.me/submissions/f1d8ded2-5757-4a71-a0ae-85af9c7dab8a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 714568345 ≤ n < 714748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 714569595 1250 714568345 714568417
    0xa0f031b0515060103050c04361e1a0d052e050106142a03180a0807050906130b06030408071b0f06050d021b060f01120503 54
    0x1604034a5542002007100104108a482c0703030080500d0055034405004405441b019a4914211902040140710544001203804000c8001d2074144124210030b11880d040c1c0c05c21200450942a034651a10b29107400d240540c451380d04081c00103001921000180c2c2c1031102da00388205100d5203003180310300c0410000707100c0e0016600a401600c1c1142d400083e0728428030340341034a004005451300d4008114a801111100c3c0307610070b0316503040c1c2440001104c41e00c64541198402540d80000003100317040d00c800304003d01d8040400380329654000c401100307020300c50029401400080c1c00520007030040d80c8583c445240d000320b00f00c54002656640f44005002400b08201194001d58000200401d2000c10360080000503c110100500241021112001001036010f06401d41e185002c003000035620030005802e1003c01c1010043c41c01138000c2443c110044851b400070742682004d41004070f0b10704420051401006000440e90b6248096030303950b0340349d2040704004403400381e040c04203151307803100340e403500341c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 714570845 1250 714569595 714569627
    0x60308041203031503050c01080c04080a020607061b09050a0501030509060627070804020a290d06051f03050105010c080316140a0201090c050f091501021903170109050103050a0f03 79
    0x110f10b17510b0b0300304a038443c0c010141c03c90116107000c0128081002480c2258111802c0f1406400e00e500f03a1f5003007150325848501d0075101c1c2501c1e032880300341000760003007000400a0a03450340640b0600c3e01e010b01c8200c0c1144d03408641850b01d00401c00c0085180801c080740c2c010710898a00c0d40032081d0f18080000380845402d43c0010052080400c000c4d903401c0a0b000e80203500131a15a502d41e40d403440b015507000d40312484041117602c110104c00c6c010503504c014000d148102c138008110720f5243c00109056408002e46d0f002400442032610f40070070780610907140076250a19100e4001d05081d285d01615102c068103105205049030303615148144909900204140340030b45490361903c51001c028080c100e865015925141c0030707000080c0340e01d004942d41c00703890340c040c21800c40c0d6070310256202c99200d02c04100b0750550007001030145403500c2c0200816580d511a4a88011f814010003036500c9450050300840ca07002c1c1780a00500110303c000400201440d4040c4107003003124101d2070101d6681d241d000d42c1e10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 714572095 1250 714570845 714570881
    0x2410050c100b040609020720060d110702210303070c021818010b0f100302030621061906030309170a020405010b1804270c03170306031006030804120303 67
    0x2030303400700d915004686440b004030b0b0140580d40c0c4844a040803482001c400074184c0d03648210203004071070490040082200020405030901da13060b442c2030242c0d1411a40d01c600781100003580707811490082d4240343d00300c039000d01800401030740840865992001074008414014800c3d012400c540c3e64105542189040320030101160505452040c5010803500c0c2d0790940b94203013458202c5e5030800d81c11082e144880181700d02c00d00017256205038020741c000317420342d41c00c9079254840265148010318101c1881003460002d140394907001c4452411964607200c040c0381982846400c00c0403c2d070024603081603900d1a03031140300d50311102002c5c526041104100a4119003008000030b00e04544402404482e1840382682c501c854465040100f21002003d411050088001c03840341c110b5028504032401e98419042024a0743c0c6a4440001002072280b2881c4058000006c1141074241800300c03414440030b9040038030070300c0e041d5642c16106004a004806402c458101b180040c144650440f0101e480c07081211 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 714573345 1250 714572095 714572113
    0x1011030c0d0f17040210030b0612010314160605040608070e1002100e060f0a02090a08011401050103061403070b09011b080c0c061204080a0507060c02152410050c 71
    0x282040500403402d07000705004051001018503034104241c0b01d10f1303005100c40f0010441c3d600a80007480902c14080e0408018803070040109510100c0502030360243c140c03600d51ba85803548480c134014030580c4c451108407040104102c01c035004810b643c00c0d501981405072107a032b140401202c0d58041904200e500111115410121036004a17107413030300c000e50b60340c18410f061400900d43d071707a458252070044901c002c05c000100080001c0d03002d40040075005200b042c4c01c40d1303184561400d66820554030080d219050300108811b42c0c00d072180100400340041c201d2400706231400003e0700da01d1584520754041e040040c4000c502e030711418444569038501075458041003040d051414443e00f0400355044940304005041d000f600c0c007581500c2d02410701031003014587d82e665603038800b03581106850900380081440305ca00060024040c216925080d5402410508018074400d50309a0000d0300500014015018042cbc0d148000b0035144c075400c00075200d0041d960040710b0f04596511410455950710300a01d100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 714574595 1250 714573345 714573347
    0x2809140d12171b030402120f0703060b0f010306050d0209180d020a050d08040210030f02040306060816240e0303070209040506150604060e010c030908030a0201060810050103021011030c0d 82
    0x711104072440d0444002d0319a81c1a0300100d107200304032140610780405000040043c07030308a075091003401549045c1c981c64042e076410340e454040380c1d410455207180c031030030311a903103003099600317410502c03800d00e000d11041349440080303150700e00c10341c82c068024083c4c200003d0030305800b014009001403d0008840640014030303c000e4481d0801d84003110380d4000d64000d00e9010384119032480c040c60b001062031a4204c10b9031000d400034080c4045100c2c0f480d80a11000001c07c0280c81100003c004c1e140181a0f02c0c01e41c0d0280c1d40358030b01e498100b00391241800003401401d641c1e414201d030140c9042d0400c140d4207110903000900d14010320000039844540309041204100001c43d1050050402144400385240b800302048002e0040d0b000300300004055151410306907104842c0000203601a0410441803900c8040e03250031580b26114240c0583c0d1282810080080b04200b44044000707444020041541164002078030004003402402c100000840841d004841c28000c0700c0c40750105004440f51400700c2d9030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 714575845 1250 714574595 714574607
    0x8091501050a141206130b01050307051c03231819150c02120114092a0409061113091505060c031b01090c0608100608130204020f2809140d12 62
    0x441f60040c1c1880000303a10b09001aa050070b55800600d60304403d03003c002c0c520034a80c005141a000c009a60b03214116180e0048030041d010500200320300c0ea511421030641001c00c202118560042d0841c07500c2440b00382da0301c958041a1040d1028244070b00501e00000c8540411408000c4c0d0300c18401804a00d500d201513220310780e0031041d8041c5580751303070700d41c0c17025911203148090712820040703011994503000100203014100108010000900040182c9401084441800c0108040700f00041c03428015408400201e0040c5503003041842200c2d031481d2409401c805a1044902030003000c18892588882401603c01c1e000029080300c0440c4408900280a0401c401d410740d00d401c0e90090216129116143d80f030b100d0004902c5019400b450818111001800101141500b9003017031851b100580d41e600040ca842004502400d460b80e441c40103001c040080c0c1d54200314600c022072541041c05400a00690803201b016208404509600000c116070340c0084000030a62100298003040c1660861 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 714577095 1250 714575845 714575881
    0x41d03030c0409061508070806010c0803090d110c0f0f03011107050102040302010f05090303031f170714030d0903080906040b070308090f010606230c01050708091501050a141206 78
    0x703c41400300a5450000030078128800c401c03500000e00580010f0803c40c0500401c0c0c0d001241898400c4840c1780e951200b00e810740040d5103050164103c007400042195204031030360300d03504000c4d001d81719003002030340096903003516400780b2401240780c54010001c9980a5100d0564000168255950f070f59083c90614000e602c50301080740450f0112810070049071085060342c003509006402140745449a038114812086400701005818030798040108109680760b1200014040030001028a5401c04c600c8525040c02c80c00260301030b034807601c0b1300101140d02210940889420150003680d0b501c41c100402c01c107120340d4110300e1b680070300001c0d04020150300c0110326100e01c8900c4240ca1100301110415401d0710201d201d1040040c1040c5980000b40100e010311250032099a40d6a0b80b03002500020203003541d6084440f440416510820046058400d1101195a40c0401410710300c5604000004129201c103006115443d202d0b00c0180412381c4428506200103c2410215001c600c3c0003594101120424 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 714578345 1250 714577095 714577109
    0x5040306050a0203010b03010302090405120c0f1b152d0901080a0b03060a020d0b0d0c0f0602030a0807140c01090506150906241b0715110c041d03030c04 67
    0x40360002d01030042c1d61080d28103031150046204c1c556441e5400b0085501c402030700c20341d42401038044a519540700e020041c0580440c0760003a14a241c0000c009074104045660480c414800103c03982c0066511002004544128204290384848507020b03410141012100059403c107191009214000310780c2c0e0241115420983c5c554029568008210b029240042e200540641c445070205420352041e0b0007424030192200c80c0040c0c01032aa5000072510103907c042540c0e88101e001d0144094601c0e410280060145030001758548504610002e010000091107141000b030a0043c814850b502282100d54005420000780003400107410070940758175090319540100586018903e9407824410706091048000400c0c40e084c03640078519a541d44541100c6000142d407081040c80380040b424800068814a000024010a4107200044240400d5034085c1400e000000d10000c0001c800064420296141510082800c0071103d51003803000000c0508240d1500011080148480080d8003400c100d55003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 714579595 1250 714578345 714578351
    0x12020f16030b2d15060d140906040b0609190f0606120c050f030c040f090203060102060717040201140d0f2412060e0a080301080109020a0501090b1b0f0105040305040306 74
    0x1584a2100403411001901940040100f03450300110025502180e030003000302611010150750701001412a60014a22122040d61010204800c001d40e541c450b41c000c0040c80205058106521400c08001c40240310b50300c1020707078800250b001040884c0c5a074000004003400e021448001c944100a005a401040c00150001060340f100500c270f801202b42c124102d882d01440c004819001e800c0742d41c401002007850050030000090b003100048200e50040c40505d10040e00c03410030030002800c006025214204201381d48075000041001101480d40190342402c040884044801d42c4036010b015541042c5c0314585014100d445500940c1c12401415502000316001400740220303c5103000d08600882107041414510071000401c65403103608032200840481e000010342c0d80e0f03484511f910903005003013541d44030300e2980118109110345001030182424021a1035090810b03411f01070160100404280b03403c5c0079031010300310003440550102e48502000b40228909800c000d081c5900900c001c442c0186 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 714580845 1250 714579595 714579601
    0x60905040b060117060a0b18060c0307050c2b020d060c0e090109090b0105150d0c0e09060f090c0a091d0129030406020a0e04091407080a02060712020f16030b 69
    0x40091821845084020504411b49042c030247c5602d50300b2040c60060500d03000e016482080d0b5850b000780c00c07000c040383c00940d82c4031214505142080c4400011600400d00b0000054003000780c0c4540c43c44d044100034083d95604001e0002408010000501610681c6440c0d0081c40d4198804d08010442ea400e5035040c00c240d0740e0b440250100c941c1544094203403452400180600d243c114091040743d102207450509081281e81074100702c5440c1d08000c800329091201c1e40f00c540c10403000f4154083e4088901c1d10120030b00c400814415840100a080141000120841d415004240d07141c054114010801411142c411800383c5054082c0650540e22a203038464100c3d04010741e680c0508603841410960540e2a03550f5240043d420000f5508244590700540c103000c0d4807a845140705643c002e010301403003c204c480c90142001020740000145070072244000001d62070f6030048a03080c9500c52000690103c414408908104071803030361540c40d02460079407013007604003d2148400c0c1c038080c00d02c00300c480d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 714582095 1250 714580845 714580877
    0x3091f05010807060c020f010e0105070503030a050f07031a060a18030c17060702120d1e05191a09100510020c031b1c08160305040e091908030406060905040b0601 71
    0x1303d42400e00030347c00342c5410403100b442d511480a03581d80400605040c0e0400f030803561440c1c11900204c40d0740000903a14410480c0800c076456010340c008000c0d050410096158003040030740c2e8070340072100c18055000000c50242c81031140c01000c3c01d0b040c5404023002000c1d00c0340307010041c0c1610352056100c1e8410160030880500c20108000d40034401540040560b1595141130080f103800c40d08010001640d01c10911040c81c84d461000c4e10075858480c0005100d140506940e054909002c18828505180c080048a0001d6092000c02e25141c00c81d542c0400b07a903501081c03294503080d034228580101d65034000d0450b45800080302a501c0200700c09a0703036882e1400123009210a00162207651141440344030320038209500b80601060740c003d60324540342055050390700600c80d1107004110001000080c041101d07003890680c280c8c00141d41c401805900c0000b09200c200c583c516240039100c4903000000c2820001c2960080d001030100300c0d014000c1d4601418005003080c01240c0c03503030200d2007200101c1248 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 714583345 1250 714582095 714582107
    0xc030e0120070b04080904020c0d09061d0405090c0301290d020d020d0c031202032a030a140c01111809090d11011e020304031d06070803091f0501080706 67
    0x40d02241c0280c40c2481560388805030102c1001c1c1065603a44010031000a207a1180d000420f41070b40c5420040228006c1981300a10310801c03680500f081000c000e100e0740190803211608001d50070110750100305900c2d00c20318070f82004010211035915600e0503810882c5060a48102440c0c1d41d44402140e422001507010b012400c501c000009501812003510a401803400180400140d401140040b129680b280e070f81b03040c07901c030015261025910114008101444040f1680001d503140c0304400c619607056403001d580c9020300ca00d5401445001042c1c0f60890385070500703503052044060001d0080070000002e50400d0307400b060320b1500d85030f141521046282401b941c5035020b5008880100300580d10041c1c01c07910344c001080115441d5403200d602400e0080003003416141d20030030103001070382c0c0d04152601403c114131030090050350640c03404442481b507440b0740958013a55040a4103640d02d0365803003800c42c00c0001e6a02905a00300380c1800e1711012a11a44c0b00070b0585020320229030019803103a02c191b40d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 714584595 1250 714583345 714583391
    0x912080c04030503030c03071725050c070b0928141815030a0602070809030115080a0b04080405030604060f050a200714060f0a0b090603030307080c0d0c030e01 70
    0x1c0f036841080803c0c80a1031100003950322623454507203020055009485104002c00c1655034640003a045414040c640901d40807411000c951420824901107502e6031340ac0e01d680b0381d0f10491034803a01c041200c5107262610014460741000c2c5503035a82107040c1054451003180d215006051000703008000305140c40c05c15107000c0708200100d04807181640e59115090300e1040b8251040c540500902c0e82000c00100c0d6800508551481080d0840d240d00b0060103042c00c4030400c0071b00c281d000b032140c1c10402c84070030080f4849041980200100410381d071203090010151185500468040c8a0b0000f044180b000950000e1004128a001445035440c2c5d5000b650035115800d00d54160341d6440300e100000c04003c20002c0ca4940c0c484c41c12050104000d01b0f04a0034103a0888400d0000007504080090b1502d80303210300b02191804a5013128a03083c0700d00031a0b56400010802c4090144e00c00c0410359076411074064465181d41003d040c4100d2406510007809000c11607801e42156081800039803480c0000840d100c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 714585845 1250 714584595 714584603
    0x703023127050606040509160602070302091e040b06010201090b040506100603020f22030218010e1e060f04060b030108240c120411060d0c02370309090912080c0403 72
    0x182a1561005c2000134180540035002034070031b4130b150780f40c1030702c1141c007a0b0010004d41d000b61140500d10300500012040c02004034484040d042e00c1070440801201c0826041030308180c0d501c606aa402c401030340140590f58000c0c0010310050304000402c0300010b5500d100e400041140300842da6070b001c0c160240c1c0128203400411120a1103252841429424911580b1201009210031169683c001c80c0c2100130100950052080d40001405486480c0e03401c290007201d807801168000c210615001440319014110b580b044087d1f6418111907650f40d040000034000d007100240d07a9581d219201070360750481e4594100303a01d9590702e0034560b480d020200644502403e040b00341c0303082029a00b000b0050b40080040701c60f44510203441080e07449071070282001890450000035480c2e9003401c00303480d00050301500701e1651001501c851801da61440c210800c000c18104031001d4501900d81070f0349030103042c0c11440d02c051410401c4410300540c07003025042c440c0c0341d8803101a9526101c100030054482c60002030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 714587095 1250 714585845 714585853
    0x303030e0f0601060507151b141309020c10060801021902060610111002040602070614180913020d0f030e2715030a0308010323070302312705 62
    0x241809074005141d654400d500b40747d441405080c1d08412900b110700c01c41600c89807031210507a00b60b0402807402c900c1554541e002d0034426080a03000c0c25401e5805500c29403500415644a80b540812100c1406c01c1c4200080c03000c96111901c0d14001e4101a0382108103094400c0700054240c00451402d0040c1c801401e515013001000c0c40988040030724038414016440b6004ea8510b846000384080c3c40030300456400b0b0000c9918015000781ba801c1e030903100d50b0722450304204070250320041da14000c1d5040001d48429125503a115413190140e0032000d80070f50404014400d40c000c1040c1d06100c11241c0f0310940ba0400c04000040a2050351544800401d0200d03111400c40d484072b0617506140c0c2e82c131501402031002d00030785c0034000ca41800e0b80c9002c201d02081100005004001618018003601d5101503d40c00066856a500b82d5981500c1d01c0003901444070700007d0112165402818846c12140d801c43d0400304680044500c0200907082e07d0b4080030f0280384e01d0100f60261310344046151a0018014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 714588345 1250 714587095 714587099
    0x30306040216050f0705090a020c25120f0b090105010506220f0801051e07020307110301060509040c060f0206040f230709020c070f050d120521010303030e0f0601 71
    0x2000c001c0d0300254240c100901d050b5003840c00030f04200405405624284040c2884519003014424000c074054a412820f03030050000e6041d8903400608034603403040c00c2c80720b4054102d880c94603c0c245013aa41004031700f82e030200c4a8005101c0c142031190b040740d114003c4030256658042c1038a08a803c28040c079544070300204a007407030100e4042d4001450000b40803010013011358502d4514050b082c0b583c027645240e511801003011480040c181c0c141013a22500d01c0890340c1ca02010000c1d100e10501c1002030541c00a11407040d1151800d40c001405003102410b8a203030341c03e09040c900040703107407445400c0009540c00d014042180c408210a4001c0354088a21141a8181d03078904054004020740080b242c04460400001c4c0c402c02c00002d801802c104c1001691503e0000e095401e00c2d499400a400a401c0c3c8002000340303444050480000030742183c01d055038808508021076040c440e0660016a0303103910000da80c0f60440c00700600d8100d0344a078034100309611340c1542c000c0e00c50114140189064103c6001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 714589595 1250 714588345 714588349
    0xc031903050717040e06030c030c010210020a031b020a02030f1609050421110d09030b01060f050d060e10061d01121107140c09280e1510090608030306 66
    0x601105445481d459100300030300c008120080d0813944c060321030703401d401d01071001d5403d0520a081110100703501400c1038001c01c1c00040d43e5101e0007100006002d50015003080d15034481e90200d04040c01595500c2a00200d140c0000e40d00d030480c02c002c2c1c0c440e00807900000c9040c6d0f40014403083c1040f00380d20703c0424038070b0305070400002c260080044e2040f580c245401400090036200c0816840880d440780950404002001c6241c06141d01c4000e0502c00d28050500100701042c40460440e031507481c05101c0440320171000c5400d0300800c100031003501d00386840441c0b0002d411410303a220741205000716200c2d40d0381e110f044486007065480d100002410a80e142c05035442485103900d005402c47c0c000c11082c0d041441c2444a900800c2d05440380e070a444441210158140300c500c3c14804112020766941c10104070450000561440307981c640c800a0010484051140e080203501403c403400707440021400c2c210100400c0402c40c0e041130b010141c0d04c404100e42c0a03e11450064406800095056a5450003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 714590845 1250 714589595 714589597
    0xf0c0e13060b0f2d0105070f0212011b0909290904170409090204050f070906110a0c03030302090a0911160f02040608100513110d031707090302030c03190305 69
    0x1d1070039003010301c0c803c5000d019110007000b850300d51003d0705641c070500070784503840a0300d0300d4441e0b95504200042021002041e0306202c0c0103189070301140c00503503507081e00e046c81d4010702412040b0034550111980401021b0b07000b00410b0b044548010084c401008041240d0010b800525061203945d44c5803241c011007810071440700741d03005114090380340403002d48a4440c03a890f0065402882c0310b41d202c046110841c03c0c240281a0400b0f1083c110a070b03181071800c006400c00707040380180401c00005007010161180300b080b0813645030750482d442c1c2c1c0c0c800f5180e0070002c0213584881d8240740100a04c003400581058603229a849c1b140e0141610382c200100020765a100c440d44003070030348946080d40c0c1d003c0050395552082e40024074521000304034104c90854250143c40000341a05080018240c3c8280461070310a45c00072130484c1240c0020f03070a07501e851305443c00003d03401e0704a06441c51108100c03040781c000165800b80c074022003c490003080d1101c10550341d04220501020001c055001520000b03000d20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 714592095 1250 714590845 714590861
    0x1a0c060106090f1503061e090b030309150a0e1e0111070305061609180203160804020607080a050c10050108070e242101020904050606090f0f030a0f0f0c0e1306 70
    0x40717030104000da643d0300402d42c80203412400d01d42051081904001c00c52082c8180d045140d402d80145042c1440e007800291101d201130600080c0d4840040e00c1c0d00294800c07841c000f01d02c3c0c0c00406503800e2050001483e0141ca8000040d28085090380303000e4030b1458000265501226071084c001d080300c1c0d45420300000702810000c06d050500011080206071088003011888200950140041c0c5034500121710040c0100084210b005004c07030b8030140005625604120391005820114130b664030361107180d003180c080c4074026501005026202007840d1029603500b00c1812101c004d0304813011980c548400d17106040e429034440c244224002a0010604245103e40d41c846000810300c8950b422442010380b11400b030040e003040c40e41d6000485500d546014410581c00140c107a03a0181480c0c140008180c1d40c54000c20514840c5a00c0301e41c018265904014080c0f41c0750388203201a0500c195071400d4101400800f1046444524280010510207078600249110b20401e5100d080c0c141400d440f4640180000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 714593345 1250 714592095 714592097
    0x3182a030721030f0507110103110f0706060306050c1206040c05070f0b0106202a120c0301050606120c030601021203010e060102070902030c090f0a1a0c060106090f15 73
    0x96000000e4440c1d4401540b001c03800c0580510100042d01c0ca0018100c00a0403200d0040c0f2100344040e10125903a019507941001d8203090011381c883e0714540c0240313075005d2200601d6052500141c50b0042094a400150840703100720403c4c0900e0301c80078100d4402d40548010100740640c80320024000d131030150000005040039040c260315040f415150030304c200c00700c003600f43c071050f011500421989a1046051981d4000180c0c40c00c03d08503103500f15170315403d45a105181142d1000b0f104e592201c421034601c1aa01e82c000c2401050b014032b810312036100d402e000100c503c69440e05001428608046040380c9024650345180c10151f655800903020940014013118118410a00d02040c01081080110b0282042c800c040b1040d15281c400240703001025000781c3c0b4114010320078004140018400d4900143c000c0384c4050040c1c0c100000300c1c449032020707404103200c0343d280c240c1c4070b1000d040140207000600014065400b6070380c07a8401074403440300d58801e42c4030354040400104031048000d201102d51103ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 714594595 1250 714593345 714593353
    0x60a0302040504140d0e010f27060f03111204080708070b0103030e0909070f090906020c01331404050402010e09070203041d150607080c070b03182a03 66
    0x22a0042000c40e0011a81100e8281060004d43c41c12142040500080c031803524102d49134000c900d0000380f904514010203014811501c7c420105c1c00c0c040390740d5626604188448041c0203940b1000140400c1c00030080e0804a8a0414036411006035582221032030b2400386500b541035261a03552207080c1c0e00401013901ca40d5002e010100028024072100c6000390701079502d200c2d00f00d4820080280000c4085d0940443d07900031035003002240445201281180d0317070800d002680018604140e0007a2040c034032094280c0d4a001c0160b080c00800c40c8144440760310b0302440c40349400a62140160601c91400f51a8094100c1051078890381341c180c001962103403040c0340c24034075510501c0106c0c0307008200351503010158001080500507040f01030315100c010080c40c14060036600b400526610b8101807040494000d000018100d418080520201e0303100d035030140225407005907140f8000009070008d40f40004116a0079500488029000800900c000200405241806001d01908207210212075595400d402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 714595845 1250 714594595 714594599
    0xc070308030402180405010207140105040201080109110f030f090c010f120f02091804060f09030c02090417190e040212180c040f1506080415050405120a03021803010614040203060a 79
    0x4001c04160245e8400c40000d41c94030000d1500c0380c9a80c0120713407000340342c0e0326040400001d80c2e0304c9140103044078106040040e580e2130f1094610020b1180c0c21040c05201c0000050140c03140310034410b6403003000708a064a5089854800445805801700d44800c002648001e2000180d080c5a100c2c0b00380101d40000149000003240104000030309503c21810034031110000c00081c01114022072544001c4804100304a08584c0e40c00750041c9804000a80140c003076000003010003801210144120f01001603081d2511180001d0817640d041e0200054000b80ea10622801ca50410f0b0007550280040751020040715900e000700c0054000c030134400c0000b980b02c1c1010429035600c40e4421190040304080012600303070190b05540351001c00591107a020421500c0800c030205050780209100360030000303000310300b0380c880e81841d034074102402c1d0750a221800000b51840c0007507050780c01004144160442e07140114500b130304060032601c652140344001740c400c80089032246401e60056500c104020120300250b9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 714597095 1250 714595845 714595879
    0x141c030f0c170a08071806030506030c09091b03032502030a123606050f070c0b030402120d02031c02190e0a0902031509220804090c050c070308030402 66
    0xb0303509003081c0881003000101400d00030ba1181c050303540050142450442c400c01400590078a92180c07159400b010345e10400f040381683c00f8004120f0f240e1009110307105034141442d015407102485010204007070031402030110b80b41004801d88250030b0511082e00d5401c40000b0f9041d010f4085000200d9250007401010070014007130900c1c0c0061f03484d5680c1e640c004000700010454141d0514200c4805102507040b00418181d51180e485082d106503140036a00c40d90000740702040390040360070082038050f003010042580720b0020044c501c9a4000c440040c0c02031440e03e03c4540301c00654a5420050b0800c2256280740741607403c142e041038002d0980149400c8800500c602d2100c21000104002003503c41f01f0115403601104980250817084800c40c59828020006202140d11349a1316002c0c00f4101c000510395052031810003426541c0700d09400945e02289010500c07607101e0f00462007a24a0a803500060503c5038041d65000e45010780184499429921503020940009100326800401038201c02410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 714598345 1250 714597095 714597113
    0x110f0d03021c0311091009030533060d120504080303010f090c0f1209021302030f0405060a150b0c0c06161208042111030c07141c030f0c 60
    0xa0196026124000715001c54014480511010b5030803d41000c2164003261012002c54a00c0042140c0281106070320001c1a60703410710f00e90002d4050700a0302c0b01111506407110a030701040c80b292071340b07403c2c1c2c00c6804001c0c0b41d2024240c8486401c00707038100c0c19100081c98402a0700d00390701c05003401402c007035a45131454a1607000b40c120314900c0807105020041d00220740269900b1001a0801248400342c90200400e01d140300240c48203090346039803444065490390305001c0612041142c0a564a103092500d50603c05030544049503d0311400001802c18010341c07180c026001c03550000d1800c0d5038074103060100d054000c0844401c1d1800b5412100000d0740d030302001000000250301d00410102c0c19810700c10809d0355044c01a40a10098508100000d01107002003d1405541d22143c607409008182c11103074907100303100d0300101e40310006219100c000001001022124040c52140c0107840b41418000844c010201c00c0e40802d41d110054000a80a03466001c244922480c0001024086441e06881 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 714599595 1250 714598345 714598369
    0x201110d1508060f0c07110a060e01090e060d02060f04080604052104150309050c0319020301061a0a0c050a0b0c040312030c02190c0906151b020d110f 66
    0x1000307944000c1c40040c103240c0c0c000c800080c030140b006881c4a00d40650500c01c2114010202072221100054460401412882c041413096014200210035a25810017410000d40da18116001c680c000a000502e10300001c0d1044c4158000307081030400103096400e022054001c0c2a2045404c0400c0c4004981118100052440360740544000c2c12528500c0f1000300000c884c000b6041e0301003070100018000c0000c803507840400c0703204d149000201c01c02107081a5007000382d0340c642140d00d4040c0c401d61043c2c8924419982403483d000700d0081100b03640d285a40b00400d80f180c3c80074890f004052000c14030040c017603200c0403440d5000d002520303c0c0e45581e581d0b40d44400c07021102030501050118040c024040c00c485c102812003650b0404104d06012607070041d54440d04500031406002070080d01408008401c0411001007143e0f490034019640c4a8814420b418900c05400001070b40301c81205008000d03218007582030980203003400c10300c204943c8800703000310b4005a1b1150080414240b0758a103440d901c0031110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 714600845 1250 714599595 714599617
    0xe04020a020d1106010e06061b010f0b03070906030c030803040c03140a060c030c09170705060d0f0c0203070c0b1b0607030501050307051215060a120507081203010b19020111 76
    0x80e07004401c0b1009007050303112400e00e03c1c0981c06000144640c2c0380c0100300d56001142101c00c5510340301000e03050810903a80c80c5054007107508140c070b0481c3d0100e5540000b8441c007011004d440002c0d4883e0071403000c4030100e05c809070856101501c2000841c4a230b0700110b07001400345c5181d41000d034480c0c654000340f80303007051080c8266101d60000c000380b200c94807840042c90300620703090007202a80240180041d141c1d001e1010440c038002140340c2030740020041800140700252500d034481c1c1c10078039244020305203003140358100c9051852040c00680b011044848041e0b0000c02004201e05203d4107000c40c1d00118030102e0400e821107007506001351700700f202c6072003205103681c04a103542c1000c0605040c0107080c1e2095001e4a000f1070440c5041c00007245042c105048607049158a64945001030b1007101d42c2d42c0802d4500045008800030f001b80499080300b600d01c080110703200c40c4042524400648424840e80301c4c090003c1c040c6828400c580c00900f02c0304a558800401c1038200c481c142c420b00c1c2e02c10030b1140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 714602095 1250 714600845 714600853
    0x100507120906090b0403050307060b28030c08010615051602040f0f0b030102190810030b0906011a07110f011809090213093801030b01140a0305070603020a0e04020a02 73
    0x443d844040711000e850002d88850400c0d146548069403401119030092820f620f8510111040e110103441040e403107000c65114007254110316140300b0740f190340d010a40d49003013041d5011620ba407050040303c04403480344621151440c90014111243e810104416a0f520220344060003d17903241e0040d00b44003001d1010014551120f20748840446664072000c1d03000340d00601203540000900d11081d10740c1b0001d803c0c103c1d041c0d50345541c0300480c980190001080b8001c0a414451800c0c00007035681d040e60100d81500b41000e06403540d9900500903c0f00080c41d00f80c860101c0326850a0034400d00c6072822060600580c110540300e2440da165140d42c0009401958460442d4150702d8003941c07a8901c2495a2000c02c0030868035129070022142d07104500c450311040036282c60a0039140c0542140410500710161059612450035108004083c031440c480c40c1c04080b0041c0c035920301861010202c030740c00307401411a50314010f0160080d4010001c84001d2110b030024000035030303d03240000d00e40d80d0096400340c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 714603345 1250 714602095 714602099
    0x6100c140d110d0f0806040e03040302031c020d141b010b2e1d0628020304140102062a04081f0c050309030901081803160b071701051005071209 63
    0x120380f60100d100c04071410000c0309807503032040540004000d60041c0c1c00356000701e031aa001c0d290681c60361203180d1000f505486200c0302895010340c0741c400045440a00d50980e003140d10707111741c221a4220903121000283c00c0401440304e0400714a1f01c083c007540948400800c61100c03c000041c0407498941500d611881001900c034015000c0f450b22113200c0900d81812480340d209641e994000d0540021950300503d00010800b1942580d80c1005401880c0c9440182501c0e0f10355034003c1d260307081441250150082c802c000f040941c00072444502c00c03005400e60310380043c045407924084441802d4440748840080001040c800c2c002c0c03264901110304000c0c020702d50348400420004a500c401c0300d01c402c000f0140706003e8a81f00c088100c85110000740307003184d00c2d43c84040d00440e00042c110701615140c0b1000490303140d800e0760390b0301c2507080c80d0080020320255500e1304800d079000c081001c0100d000606003001480783d40351100300310210740d9403031828906101c00399681c0c01c002c5080002081c0410261001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 714604595 1250 714603345 714603377
    0x610050406150206190207050a0c08061005090412030b060705060f0a06030f060c020709090609050c03010c020a06052707080c150316212306100c140d 66
    0x107400c0040c00c0c54085101c400c560200300035119030016000e074120050a514030600c11031640c0644442c150041d00b60780c882c271098980840074441071301c50304c0014090b0a0000f80c8000c844182e0034101d40002e0881d034003658032580c0300000f0303449007150001810350307500e226641703034441d039018009043c0b103407006003601e003030440c400362024030000c00d2408101e041500900000d42c4580c185680b00b5070051000c03607404c3c0000010703400d0a0b06a040380b0185c031315101d001802c0c4080d80c0c20110b18240a6800c1d0340b100d0b07a1800501d130984203120080005a881910080300041442d0301c501d0b803002080c60041c0d03a0001c16420343c04503400c4c02c50940d00360361100c0001d01480c03d0500c0259203c90049580c9030031080410a107007024000188010490b02011500704609030103088520200b810985074103040c42d038000160b03170081141000c40d80c1c0031824156200d851710381d80844e072401540018003180e050a41b0f4074048480d0340090404942c12440e0100d20007141030304000b0300c1c002e80c000c0c4d101c0d400c140c0c2c86044c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 714605845 1250 714604595 714604601
    0x402030a15090b012a02060a02010f18060b0a0605090d020607050f010b0a0b0415120e070612110c030409021605030712080c07150b010225050f030607121a0306100504 73
    0x800782e170060304440149540b5035041814140f5030640e001038940c0400c032026401000c00300c0791009100d00b8810f004507030305004c0d81d04d0a2558483c02d41044075003910b605002031045140560404180308008410044c504501c2d00852584002e020b9490000d00365500350900c50b0f1aa08098161f45400312170500b0719100c004500035002d04007500d400c0a1411840d80c0c50302111032884002d019840700a080402030580001e86019071800448841c15a00c1c60010b01c0403524100e868845454594404040141003088070600c0942c800218101820600b00708001d50006203500524404080c04c07000180c800d0018054036400317140d8541200c1c548a030023070700a0100030320080c2c1082042000800103480f2a900518200395240000f450700b00c0742c00181d241c17a1a081e200c12072000388603844030b50094440c0040e0300341c64065a008080030009003e143c1c0e0b0305400e4401c01c010801c100900f815410303480d40110864000c44600070102011000420704084d0142c41c10060710044210034086410240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 714607095 1250 714605845 714605867
    0xa05130f020435030a0503040c030b19050a0218040b0d021201020a0813030f08090c03030f280215040f06020a0518010e011b0f0c170d0201020301140402030a15090b01 73
    0x1c07022019008460011076104d20400c4480350901c10048089001c1c011181c410800ac1c55010103c01340d03904246019003340c050032600569801d081070001131201c0681d000761102d10b07440c0400031890035410030401000e4401c8000880d086482c03164a5030241e6500c0c5809012180c26400050743c0310031030103000302030707242c001c00c050242000c038042003001960000349072003584254980394040741c8541d0661810b04142014207a40346c03002003504042c2826020007000e40d0502c180c6050440d1740c60140a0007540200c84080001d07800030405051040241d0281540c040c0c4540b4400c041d808940d600d120882c0c102c2c500c448001a00454001402d5007029070502c8060000d0034481103030015140024598800013811140036022204c2810400c0480386240034001c2d40032005103051a1500010100d895140d2900007440c46441c80712561140184222410385484d80342112070700146a040c031000c1d6101421100510340e544079030100940f441c6410720050f2558010101d01e030420f12000411a050003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 714608345 1250 714607095 714607169
    0x111305090103020a0b0309010e010c1706030a020904080307210506030114010506040902070516090519090309060309150f0507030e060c0307140d1b11010b0a05130f0204 74
    0x910300500c00f60b6501d500020440321078410442da00e990301c4084502420780c4e01d11502c42982809803502d00036401c108101039001042c420804250748803c10503540e108034000103500121858086400f05001000841d480005410482050307215420000401094042e0808100c3e80c1c40080c001c040c9021301441c03803114501d40030160154102400603099201e544511481d4580c0000c410342000000c4c1f0194020b0607070040000031055940503c400902406c590704050b00ca0307442d032102d014417054420084540c0d0540d690491540c100601a00207046a40084d40c400d184081c41c54080900350060501c0d09180001c0403039a0705207020040d059450315104060150401800c0260081c00d10054950044051415411000c0100e00c4020907203b0585074001660030684a41940d106444604828000ea951800d100c0b61341c0d0316145080b0344404070f00c03940c4480802c1d004c12040c61310081400c00d01065820015440e121702c4a000b049174480d6100d5000400b800a41004841c441401c0d00524084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 714609595 1250 714608345 714608359
    0x609100f031a070519111002070602120601020a050304061b0210020f0f0a020306040f06061226040311130608101e0e0601091a10021c180513020d111305 67
    0x40c00f0006900314001d4170440040025080da104200982001015070b807495402d0119640ca0035410624065070108042c050307510900740114229510024291003c10340041c0654141800d00740d0465040c854a40c0c0b07107582507080300300c1c00056640c2031280750b01c080558000300415590075070a5820700c0c0b20720210401d00d800031764a42c0d002da1008598240d00a43c060021824131455103070000003011150015031002100481c0d0100f0490021650080914048403041c0014040c0310383d10b43c44e1141d070000808820031810003040e6401e143c482d0300301e10b00801c840811071a448101c071301c1c40d00c11044904419151981c110500306040901000601020a074040c480340280c00301d45992410b041c801c4080d9240e84003070b0302ca6003460340320310b06c0102540100020a40591254029030300c3d81c0705203074070081501c55054103100c1c50007140c0051044100c1c03810300134224903200802402d41151080c0c01d0215800300203826504c00244a101104040070000c26103803035a03c00a0007898006420440c007a0748 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 714610845 1250 714609595 714609607
    0xc0c0b1f050918010c1b0308060d05010204030f032304050d050a1520030106080708070c02030304030b07120605150a030b030d1701060503060307121103010c080613090b0609100f031a0705 82
    0x312030a5205c0903010300305050103456800101302b42c8455100081c00c90351012070003008110007143c0004115000b95244a60303200d0100c4100c106080c8852840d409110804c401c00c464284446044170443c00317507040d50755007806600c075881803030200e443c01c82d0015501d12141216104002d0181d00000c0308040d664115030400d440500708150103011041444030480c0000d00702c03407240c480511a07039030150649450f9907691500c032601007070950f03c0c140420004022200c400605100c0c0710119000100342c2c00781703400a1040102164004031101c3e0400d070719201c110174180c07420014440c08174a180d455112166000034000c50383c04043c3c108400b0400108203000c0f0365a00040d1090698000840c56018040c0b0380c5011704801c516200082d800d0750810340f0686170b680d00840942d00c070310000d9903518100500d107031104003290a8928000c03d0a0601c8001c00c410303060251040c0d0f4403c100c003070030751040780d12400c0014205107194170484400c0f140405c01d40c03c4d00305454840b0f0300300b105401c0c0142860 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 714612095 1250 714610845 714610877
    0xb03011d0c01142d0c030a050d0506040902030a061d15090f0a0302120901030e0607020610090b01090902031f090e010c031e050c1c0b040c0c0b1f050918010c 69
    0x210035500030582a0340c258010625038001101260500c05c080000c8a594030502140902103030030041d00c403070480d480c200005203e410940a64580340354020041d0068401d030395590f000601640e502c105009034041882c1205910400202400060241e100d451506e04403294a20f04a0011660b8407160004401d600019400003078100d0b4502c10300c15140c0d21003130110012401803a0b003590a480c0b038071403d0240a8420780210360300d405010801c800c2507001e61114005019540385106880c001424000204001c1065034055a08100b2040f07500c0e1200c800c00940a0303144a00380c212040140e50f62050071903c0d5424400c1256030742e4503060600c01d18103445400c5e402000394031040120700d91100001100c0c424648204d0f0080c2e551620f01c1d4803922412145440104101010746014500c1d001c203e002e4203000b481072408903a4403444196503a510000e052080d103040f6031340031a101942d000d0125042c1e40d5608000d00c6800d490300128042d401d1140240d09480f4031790208420f00102c0d1655640e01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 714613345 1250 714612095 714612127
    0x280603060f091205212a1c0e010b030102070c0f12020d030309050705030d0233190609090807051902030613020d0b07051201080309010c060b03011d0c0114 68
    0x102e8054104030b0344800003c01a41c4441c94251700e0140c04c0d002c128100940201c1080a00c03d03103940c0c4051444803070303045c174005091520510501c6480d00500040c0d10341c8045454009000c8154174030000700e0242c403090042400c0e40c01c00b035401c48819050010034804a01540d440500410100349800d0034a029500425841410080054100741d21814080d0502c48100441f800422029003101e40040800314002d4071900d45548140e45488030921020070540f685102540781c040f11040c14009481d00d101c10701e030046043d200d040d840351f129140003840e108140f0410610300d00480005686d0030051812a0611819030144c2c104006146a00c0b405600c0c00030f00f0592004090702c3c20051003c8a000240d91341c98203020041c0002d507110200542c2507403003006040c001c03019030490036059072140c1c0c0030342e00da02640320a40d000560648000c00070a0054101c0c80c01040301a00003e016451001c2030040c80c64050b0350f04083d82d011a201c0b4400e0750380300007199041c41c80410460704020350714402d0009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 714614595 1250 714613345 714613373
    0x102040509041106130303030606030e0309031b01110609070f050102060405250314010b03150c0d050a020903010c0306050102100b150a140703030b180c030f280603060f09 75
    0x3d800d211881d080241c1c8a100840315100e58015400c079010380d5038900100940400d000e100300007418000160304946001060755507205c801400750640d4401c0c00c86296007501154201d60400640d2001100c544006002550080540001a148607814400b10454602036030b4400c0b811580300500308004104007150400c4036803500c3d40880b0520426030b000403080515030304040c03d20640c02c000501d55000540c400e442d002826000c1c2c4002d0080c0d950483c0c5441021100102da900c0200450000e5600c1030384115803000013080d0040c01d00100e880420f013180c00c0006140c010a5072003606120039030301004581c1c5221100c80d418403120404501003200e50001081d00401034401188256465000743d2209031412000d104841d100c440a01b40200540380103103140d4042c3c100160b00320034111642240381d10600e100900c241c5540c0780c464011684260040032680f054240250b8001d103220091050b0b00912400800410840d0444c00c240b000c540751181145d40e054a001c141c40c1c00550b03256505c0754 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 714615845 1250 714614595 714614603
    0x60f0804030216080c04050c0a0801060c020616081315020309010311042c0717161818050112020109060c060b0409150e0622030e10030c020609010204050904 69
    0x5116100c07480c040e07141449001044030803c3c0d804501059041001030700604022080390207108589031000c0710703402449400071400001e48072000500400d40181080c1c4105807014018501e082d40080d034400e2600d1540c10100c3e180c100004d480030000c0b44524a80007d0650444c1c0f8801c60b031704240c3e01a549218608200d8141902e80d41500b10707403030020058400422010b0180d220781c08240e403880380307044070b04160400c0c0058400c0c00b01d60168403921460380c00c0c82220103484070700d40b6510504e4469901c0d61481d00b00700003414885610390b48020300788800801070140c101a40540c20300810098400581015504112401083c40540e0b4040e41c002d045402c0b90508840a00303d60070203001a11074281096009414010344c10204504070f404001000f8903101c04004401d04044100c1c1c89000c15160344501000c0003050030f02c0031400041a5482904c03e01f4030249501180b00401c1550100da0a1000800e0b903075150f8030812a0144809a4845100c10007189802e0030b00001595000020f48050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 714617095 1250 714615845 714615857
    0x215072102040e09030a090e09100911100206060120102f0a08010b03130602090103020d1104030b0f0c0304060f0b0d120e011106010314030f1306020d09060f 69
    0x28905000c2541280c010341020701d03200c0d8080c80d01c2c00e000c0d1741d00d52064001e000018044000000c800c503401710303aa0301440b140d0f03014086440d0102201c0c00506070064040c0c651075074a9a40410076a0b4115102c10701d02c2058000c2c4c6402e02e015400502002c40da034040c40700342244034000861000c0c0108074071403810f0668400007010141030011844084003036480205000c40d804407958440c0321540646403c44aa50710101d40c1d03a220410034620340000e40300d91824010500206000034000d4019044c01070b0189001801c01800502c0401616510407400207290400038081c000e002d2122920341d484450019401a1824400c4ad40b102520000344013a01c003030b64441928419454640104c0d9003400e00070a00e0248a84505004070000c041d00d450401280c04d8200403034040d40110090359070300f201c010103010030f68a15201c1c880e844500c5120203041d400b041064014020445001e40045aa4405130311003403424100c020749030001c0c2020760014014811002c000855012000200401ca289425 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 714618345 1250 714617095 714617147
    0xa02040507020a14100515010534081b0a120e031501080d080906090a031211030405060a0c0804110f0d0c0b270609061315030c021507 59
    0xc0f030500a41400007014031201d003101198290002800d104095001c41c0200300340d8584003a186040e1590000e0180480c0d01404548481c40b62103001c1020f04c01c094100e9110480c0700280d821700304500c07031401c0318412808a6070013900c051554442100c915084024500304000c4c1c0c4404110b1440700e20440c1c00c11a4005240310759450501105400c0303104071118440c1c9585614030f5503154400c042c000d000107110341d0300240300782da0000b0b00d0900400c003260141907042c603251005c030307440d411680c007070301005403214505500308414000662140f4024400341c00c16003007498204080e00c4a4070007040400c5003a00601c0302151103400d501660365822502521110080008103030038000f544406459000c000200280b41d200102c02081c03005109800d0b40e0911900031120650610a61a0b490f0400b0741408032085608002005010116804560180f2036641e80c003403103585000ea01c50400000c0e107545200501342d40400c004454070403600d4a83c504c1d4a40030301c0081200d2440818001440304d1030307400b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 714619595 1250 714618345 714618347
    0x10302030a14010e1902100f0503070c1703150a0b03100b0a21050901111c02131203050d06060e130c03020d0f09050606091603020304330f0e0a02040507 67
    0x803a03200b0440003010345e0340a4085400c510794000081e0000da000c1c0d20780c1c0c0c40c400040c0d4855040188840c0d0203880b0b15085803180c01c412a102d0b09944001c6071020310b00001051381c84036080285118020748599003060202c20024028202400d9100201000045c01031115843d100c0e1204015580b11200b040c3d1036441803101155880303180403884071814030804444180041e030341c0096209503c000c3c0203120610340ca420b464020f00c2082e1582001c1980b50032100c9040030560010030b408a032030311482540c20b40382ca042081c51401e44000b01c000c60000101c5100a000f180101e0f07006010714100814404075550111ba00400b03104422000e2a94179009011807500a0341601c03610f1801200401581c40002481401000b84030030907102c52041000007080d620b04041410b10072103072100101112021060141c020390000ba104540c03103544001005081202081c2e81281003d800314200650b105034601c2d04101c0b00790001180180d401e154600c070072000005010015680d040e600010603558281c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 714620845 1250 714619595 714619601
    0x103080a120f0f0b0a06020c04090201140a1211070515220f0b0a020702010c0b060609280803040812130506120f06030105060108040f030c0503031914010302030a1401 73
    0x1a00501c450718054601501d8180c603800445200b0f283c20040001640d032204022016106104100060744440f10020300c07814103401014006d44181843c030311071402a41c400d1502d0300300206030000100303c21000c0740d02c21018022007114244420fa0703145071042545440b038980c001c1903c801c4502e5640c10115a02c545c0701c1ea021f0b05549000e040303844401426280802001c03c0040003912007034402000300e8800e0265200301c8540681c16107034904084d80c150382d20060200014200e0764442d5051014aa9680300e80b00c0e60100d405682c00e42e01d103440602e1940e002c0340c50054109040c1a030050000344400000000d0280200d0b4083c280c864948210144d408082c8140760049a000100840c2442000c1c80a884003809281010701d000c0b01592202c2c1030608a807403c49146000404240200e40821001019113815500910380f00d18490760f00e442c1e051944e84282c1c2d40e4085c0030320303002010034452564490b00301405003e6064207202c0d40745800083d41c5107510400900407000150354145440e41c254 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 714622095 1250 714620845 714620867
    0x30e07050a080d0822390312080105150d020409020a0c0221030702120a0c030b16020604150b1f080105041409060c03070c0203060103050f0d080f0103080a 68
    0x401d0309505540322040d0b152500100807105020401420100c1c4607400002c03016004110042d10402008005460f0704403818078001c4400502d170510741c201480380002280182c0007001216901102900d140b0300035034044c011884610401043d0001800303103984000c02c80f4201c6c02ea840249480e0900201204001e02c0b030f0f54000608144000f410a03903450f0007020781d0407a28000c07030741124840101400141a40c145688140043e001082440c00500d00110a1010f0b01180b2080b00d118102e02d540b46984050315030002c2e150340b84000100250000c10034640f50a03100d0700e01c0508445d08080c0d8400c80c100caa11400d1101c40b98881c0d40e90343c41d40c0c44010121030f008110a005034001d6000900207000480c0c00c0c01014051800c058600391030150a418041c01403078490002c05845d511b0245080b01078001410490400181500e0500541c1d02007003244c0c007841c00344d00036104107420854083d103804104a000001c0c40b2041d800c12103110f9217984030b1811079412650150340c4201040d0200d480c96036003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 714623345 1250 714622095 714622099
    0x405070e090405070f080a15020d110325030c080f0403021911030712030c0201030504020f03030f04150306050d14030d0e0c0a051f031a040e0a03080a0c05070201030e0705 75
    0x165007080700f8090b00050380b0046603000d4241440407616502d805031030b140300e55400b5050850310420084480d4080e4024102c02851010008800313a0000003246640d209440d41d0f00d04c150940f01c032010b81ca00d1600082d07220031542c01d080000e51030175140130700071100042044e150181c0c054000380605009000c5105050702008500209501524201ca5503900a805050007441898408611070b402e00c46000201c07501a00d07503d500e144035900460140400500403a00103110000e140d94903203080000d000e0945003855074130b40b0350342400c3d0161003070300010716031400305800c02204000c1030702d5080c620500150002008004ea460a180b4240345124003202c1d10001841d0110348003100074003080e0b00fa07240004444030311041d0b0341d0b0fa0400c82c0246148a0405c403001300b4540300340c529402a030006101032207000211020055242c0003804031400301582c0c10264102500103010103a001d48525801440301d00c0410000395201e1008005008062009050643e601c040e10741e10703102001120000e00700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 714624595 1250 714623345 714623359
    0x6140d0b061513090501120f0b09120c0c040b1503010e04030e130501051221160605010f060801081906020a051e0a110309090601030b1503010905100815060405070e 72
    0x500414201039022038807607000e12610703207400800d040c407c640140182c1780c5c0101640034240030b5500c1c0e403989820068100e1046222340c00c01d03001820000000b610b00c0c0c2a03624090301901c40c1007818032095514074080c80d440349180c0160400c01580d1002500d0540d03081c0c0311160305036503443c60305503020005a810175511840506401c6000c01c03d580105041c0d0f882950410120b40c0d149001c5580c91a150300d840d4100d24074415413901c074600c5c0f60041c145108410402c00d003400c04948940c3d040b140700ba044102c181507440c005110103500309040700e004019510050001c01c10880c024042c08a43c5d1000400c082c2e00004d40c1e581191144041d210f0312003002d5115100b500011030003120681c003510f45040810002e80b025001c803a4044183c0e41d012001030714142059880c040114018100692241d511507501c481c0c0760006000d000c040c1d4040c080300c000000b803d052007051101c0e9149160721131025a4010000e540040841408480c0c00c0f60303041c0c2d070110380b40d26420003c1d1162003418040a0700109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 714625845 1250 714624595 714624607
    0x90c140c01020304060b03010c3e06010806100b090f06190908011a24071208010302040b040221060406081002031f030506070f0201060b0a030f06140d0b0615 69
    0x3006500540c010792050300e00f080a07501400a1500f660b42504401c230220b4038a20303200e401c1d01249a04601c1010780c50541c12445504030115106140114100641907070040005000342c810030050103820001c400e80161f903983c40e02d41005100c0c424071030143d0084692400d104056282c003416215003250704041017042003040078000b00761070301c1c91060847d250b017041c000c03a080220f00450300b032540b800502162034000e420007000000c240842100f04d0303000e608110800201d0088001c0c008440140e40e190b18032135165004001c19079543c400030500c190300c1004648203c01c1c0c101a8452607201104d40850f056642d4000200202580c0e030000010b03000710881d601d02a26207034002c511400900070318841122110442400122047c00002c003260300000c04500c21501811000c03d18034801d01c000308403643c40b0745101e00c05400100d0300d4000309488403503403c0042018000c10f8080d01d03031032007110105c50f190b0001503560050b0701c2019050040003c081034103602c40c03048000490321000c1c1c103159951 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 714627095 1250 714625845 714625867
    0x30607121508100b1e0405090f0d0206040b07030615030b0301090b011409010f081504062a2705130902060a090302120a050a06020d0b0901060207141207090c14 70
    0x682124801c801540c40c060540d2154a0b010400380c0610f9000c20060710995006030606c801058050251484c92050f4100d80131030301d03000c200307440b807000aa0b4054446400c1ca0302d4885030303410000d400314080c1420306a040c06840c0c0c01e81d42a131080100340c90082070410740203020a0040c16500300203450b504201002148221070040d2190301a00f003501c10341110781e40d81c6c140d07400c1000f031402811101d130059041070740c03159030030100b150b08140181000100d0402c1c0c980e0291013600c1c2d0020b02030f000d1450b0440d000740b06800c106004002c0425240078928083d02c1c5d140d0000e82c1e0040d0058034422070804060207000c02c2283d01240c90607501614503170303451002d6880078289503c0b0744003c9110b20b00c44840c00f2846040800c061412540c00802488034945030707901d00c006500f011240488056840c00c1000703060f5203c00041c0d00916480d0041d026860414204458200d449024107025960346401c411341c05000050f110b048400e03e07040003030b40042050007111b1800d842e111060400c1c0f0040786c10402c01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 714628345 1250 714627095 714627103
    0x31b0f050c0615130204080616141306270303200102030f040c0f0308040308030c16030809011a030303010911091203280e1036060905030607121508 65
    0xf8404860b0300440302400e00c00300c2c084e031141d0300a030007072500020041307107090809000440281c1440e061201203114074460407909500220028041200c1025080144d19040300040f40c0410a040f103803161840301074210700c03d0102c80d00c401007c01c110034641a289481100c8000c10300203d940080d5680e0510b01c001800004050760140d50001c085040041c4880303118a000045075804068181040d03d16203c0c0d045940008040340c0420740204280750500542501d1281c401d0b1003500c0d94400c0d8204290205d00712204010042001911420612003c3d50000260707411500000303400719540da0310a000860900070803805e1500a50040310740418040b0210190911681c1541301100300c1044480c04461051214406004603200e0140103c0034142001900f6801ca940e05128000e01c448400340e1121129407041405980071119590400c207148040620041c0f040d0320303046030b0b81820300300007030340340e0801415140a01240c40004602540d20307030011815400c6603524540c5082ea0b4142a42d05c2d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 714629595 1250 714628345 714628381
    0x207060603050c030f070e04050114010306330b09040207051504120f14090f09011d1503120315090a0e0d1404090c0c1b0303080106031b0f050c06 64
    0xb50302401d90303e414070342800511500050f10080042440074500410411800c07000361050702c05540358080803c032503405000c0640214454040080c84020880e8140440181603210640e046c0e0a044d03c000c850280c1d03040c0c04180c402159003a0f6891400a0001d002881286c40040582c0513100c245d80c0ba800c00c1008440c0301d41d004064450304409416000c40f5542902c1c4240300105001d01c0b82154040c2110025000183d000350440c001480000e0002c0c5503100300b40d05c03d80010680521200c8100b051010060b007241c891882d141d0042d0781070000984410898170100035011010000400100950340804e0b0f010401400c5035409003822500c00c40a00131982c1e0f5982c40340b04080c06058454800e58074004010110b0030b403142041d00b130103640d00c044e0071030403041ea041010100f00140850000c24140340384600e0039440c015460715515001d080171005a11071001d040c84c140c1c12002c041990b0620600d02d01ca46d01d041c2c2d0183c403e00000ba50b45000d542c69844080c481c0c4410460709051400c081ca603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 714630845 1250 714629595 714629603
    0x522090207030f0305070804030c0201051e04061205040206070b06060d0504060c030b0f0a0302041a090a09030305100b040e1e090d0809120403060c1116090b12190809040207060603 79
    0x1a8010043c041501501c03020744141000410b040009408079220740341c19000644149001e83c40e04a001301074070388091010945030030170480003904201d0582c2100b003040c80d180d80040103108524058000030180d024807600600718a2030000000c04075600c0c402161041c541501c010000c07801c01d810040d005013103a1441d2070208c0d00e8503181090a2502680601c0708041c01000314241c00e04541c240400b419290045010312440c02050450360780e01c070f8110907c664106d0600081600701820004e0a481014280b80c6110f210b24505021208460b801c80d0151404900e041445860750112681e1512454500c0c030b01d2000c0c1e071424000054004500100040e0081d640c0180540b42e110885d6240c1403a0501001042000c01c020000254a034102008440c81e5007400e0380b144140c8000e20b4141480c1281c408040001c1c0b60041c003035008248106c5481e01002c0d250804011040c2450703690300c1c107002f403002c0800341e000400790042103801021503000500103401552900c01c145041d07000341c00d090000f11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 714632095 1250 714630845 714630857
    0x190302040f081b09010510030f020c011e15060f0c1505010905060301060e07020316170c100509010504020d15110f1c2c0a02031e0d090501050a052209020703 69
    0x924600c4d100c031005046c1c440041c0a80c881c001c58034020f80041010354000fa103426001c0c030520b924103c003840f03002e4080005c1058080e000c030360138014000721003d213214030001c1100300200744255a880174140e03031240c000d410402011440c60403c8003280e00845c4800107042d09000c004500c8001a401840c0550703001c0c0c0080c0310442c3c8803041e480104d50112109030059009010315082d848244503a000e140d0702550700040c0500400501f286580c1c0116809013403607100600000340c0800e00c0c031031315900c01c00300c00081106080660000304007440b4814041c00b0b00149003185001501e86902c1000160b002000207591100074454191194100b2611000c551000f0701ca40d081541c000d01845074002403002002c0503219107180d01010b91005a64407500da4841c9411040050710108010f0203c4101071040342c901d116181310300343c42c00e80080700c0d002c10060640790401003640c10034251091f041c024140705445098a16132804e204a010398071090740304400e000052800c0c0654010181207020740d44d40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 714633345 1250 714632095 714632143
    0x25030b10020c010f120b030304060e09070903030f120e01060f1403070521030f0c010207060615140c0c1302070203060c0705060f1909030e0321190302040f08 69
    0x80e6140c9080e0300c2003070f01203800c4161201e921391040c035440460328034688000865054030000f00e40b464110f50441c101040c03041c183d0020b03134503080c41440e81c460740a14200d0306a604581d03004289000c82c134400b03000e01104140d11186a1443c2d00007010321540c110080111595801c0ca08152648511a103c45960640c440c0c1e82ea601b8003062844c01c0c1c41e0040c00741c0c000040040c0c905034400340301071001d0184d030000b400740e411807042002c001c0810405401c00943c80302c02c03e08009040b5845a03000240c01883d104c400c81040d40c00902114400c072581c0c0e4181e403104070040100f410f00c3d01c01000d280c0c0c8180d0000c401e5610303000582c0604030ba079009408641c40b99441d00c1012901e071003222409099a44401c00042c020282c40f01c140c0d07031200e07034100c105070a42281246501a01c0c020001180807441d03040410489007010441010441407040000e1003100380d88440300840d20520880805030100c04501070a040d00030b804447c0100700405019114543d128849621401c0640301501a00040400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 714634595 1250 714633345 714633347
    0xf040b01090209030303060d020a0308070602090415050d0f0201030b0613140102060402130c0c021e030f03030c0412080c0d050d05010510120203071e0e0108060d0c0e25030b10 77
    0x80d81e00026001c0c4c003d501d11344400c0104981c1408410080740d10501c58480403000078040c02c0505401c920039800581c032240c3e44030401083e40d0b075440804004110361081000181d658030801042d45030401c0c0c0854940819000403400f80004d064105d070410300c00079101440c49039655100381101c00b9080d078803295003500801242c8400c0c4c1968041e6026a5041101105040a03800360002c408103051a042045403035000c1000c04108084a44440c1c2e41906000e082d42424466092401503c40196140d0b1500720002052030140e80554007103100228020070410600000312203441c0ca140c42250380e88064244010603985c810402c007100785d81070100019543c142210050640303455a225007c1c03c222804c4450025040103113543c041003c1d5021403032114040b0b0641ca080e000c415515004030002c481c0c005030000c1c40141203240a007640403042e401007240d40d06040c0607180000c03041c09050300c4040000c003c81c0d41d001420020350ba214040d500c1c030b203505640a601c2240c4207071144100b503580840c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 714635845 1250 714634595 714634597
    0xa0513090c050a18211505270c0d050c03070e09071401031503050319080402030a03050306031005010806060a090c090b0f0403050a06020706060503120d11120f040b010902 75
    0x41d50404154140401601a40034545004280c60403404000303d0700c1d940d221100f94440b00c1c000300804654541400300510201d0b0100642448100006001c1810200550030311006006101c000300400c9401d00d00500c02e0600810b0220b40300105011524502820030b542c440613035807110392191054820000d00f02840100061042030a64080c0c96650b24190407000c880c00c10301c884a04041d51030503070014203000d02164102440c010340040d900d54000155990005420000c001e091001c21700404c001a5000640101643e0749460415140d45071000401d16005500d910008810300701800824040d170300003031051040c001200c6180030b41d43c0d5440030004650301000c80c00e0021b01c5a1170180400b6400400411080c0b01c0617025030f142550741e4440703038208225141d00700c0d102900000c800045c8102c40c090500900401c17005000070403609101d5130000e11a64050b08441e0f5142d00b4882d0303070001c140040c0c2e4114a4969201105403416200024144408940072a030803200100003191b0310400744 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 714637095 1250 714635845 714635861
    0x906040e0a2a0e010c06110304060501261c050f0f071a06010c06270b0f1501080406050604091e02030f030a1b080d1d010b01080f04060207050705060a051309 69
    0xa21a03e4012408000450b000503032240140c5030070740c071031940e2074114042c080294851401550000366550610610500e0502461108040e14810080c1080ca2801c0415801703d40001c0100c1c0060002810200303482e49d0003200d04c40800700b04081901036500c1400d4000f441e00342d00c60380181400e01c101a059041d80351041d00c01d03a000504010500e00007403d00c0e441894010114480708030644940044003070032803c1030004071b81907000b0805000070420407400068000e0341d0310391000c04a110f120002405500010000f5140c0c903120340120341c140c0c559503c0240c034250000c0000b90382002414460700300c1c0241c0103040b030183c800d002103260002000310690310f08031081d0b62060505000405000c8c0c0c1d200c100c00050705c4010003044609410030b06440f80a601c2d070105a85254031001c0030b04000d0031180481d203400c3c1071002000400c03030b2445010b00b820303030b0055001500603102c4c034490401514042c5640c000ea9004070001030461105c0e41c10501a01c0d100c0d08100b0820380054442c0d803480d065540503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 714638345 1250 714637095 714637097
    0x10213080c06040f0e1510020705010306081504080a090803070b1e010b0a032c1f050412141603020c0411040e2707120c0e100b0906040e0a2a 62
    0x80d0f04d0500200f00400081a0004080140c0e0f41520f80c420b00010f0b6840540554030026034040701080090703580501a5100038021384004d881c01d40070302c694031010b1000052000707001e07000c0041c4140314140500c2003040a40080003c494460a9511b0982c110503800d075000d5440040090386214108440310880d816034003080822420321030b0050059010303152a8406140d054241034120b2110240380d01241ca08000e110014242140601e0240c1d802220070040d80305824200f50070440401e8200f003170009481198a07048820f1000a462a1b4a0340202c211061003164580c103940c09140d0300041502203844103e80411000d0030030100380304c940c4540c1c4129001d0401840c0001e80341c8107405244100c1c40304840d00b004007a18441c9055003444010380040307800414884468041c8003003030082c00f0203410032440120090410780190501169030b40702e000000000001d640305151150419903005040490b007030011818616005005052072503130207014811a804010200300102011041c0d110301 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 714639595 1250 714638345 714638369
    0x31802010e01050d0b04020304060c140a08221401050916030f080306040905030309010e06060a0e190f0e24010b180a1508070206180309041d010213080c0604 69
    0x710a0041d10303284c00414440d01c1d03c1d55a0030081a10391114001148030b1442402d000070b20304011035010b00961442a1144060300c424464201030507005035a02d83c000542c09404034080200003070704641039064580040c40c0140b4000311040d10b01c41500700300e0045604000742e5068a04040a00e15601040d10010f0502c250b08003d280204441c10029500080c010340003050510711501c401c1d00e144e00c103a642904681d0f45405090140fa010b0000a401c80003c44000d264207141040496196a000e802c1130494001c82448003040c520561180c11004001c542c103111003801c040380c5075180c42c204040040812285800610f9010200000134160b82c490840d46003080c04ca11003444120038015246501f1802048011400714000305003035504429075a2100554030f04100001e08240f401380200003000c00c080c0c3c1c1e0999101000c001d940160030305940014400035141c0c06c04c4100b09005564603901d5100144000d115403500180405482d09002102c0e004540c030020301c151031243d8814409202c1ca = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 714640845 1250 714639595 714639617
    0xd03110106063908040611010b1507020906030a1223070521040b030f0103031d010801151206030b0f0c03060906040905160f081e030f03060d0f0501060603180201 71
    0x34050103482c58400f05000d010428015913500d1901d250f0264000b41301090220034180030400c401d02481803000000d07682d542801c002a9201b804a009007030000b485401d042d40041c105403400c0008a01240d0083d440c0801c21000d00d8018202c100c0816998902400e41c92609244038661011603040a500400625240050700c0445414541c0315440440c00d00b010800040c00c0207209010b140180380e9528a64119451751078081d11a1003410740c10b28021201801c0f010080e070700302d40c030941155155000040c0300545420125100c0b07002c0c150b00c2e5003242c034024000c01030005c0d859030244904100a5480c080d0788601040501c1408110b5400784d220b00140300103005400d1603000f040020b44103c040f1460503070b0044402140c0c89035034100780010555142c0402104c441007181040c43e44a41300c840300d401441403040343c0c40c0c4c8917500c0c07410320114002000c01c50545a02d00801200d9070000603c1c031050f000c42c0b401070301030a220700c1a4000241019a0442054001d41141500341e505171a4551100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 714642095 1250 714640845 714640907
    0x603040b100e01060302040609080a0506190207051207051905060c0f0d020c010507030b1008150a0e091605010f021f0e0d0c410304050d0311010606 65
    0x414000d00100000500001c00180744203000c90300d501800c2c4a890141e10340d410107100521040141e403140000340d0060b04c1007400714401184098010441040c5460811400203080b0064418040e0041440c414015121404d44100c009050104d02c9101906c041c404900844410b10316080805049904080c01180c0306641030001850510500241c80f428804540c17040340498004006d4010b55944407010082401d034580b0440c499001c08031501d000114000c2030040006400034100300380b8040040c901307101aa40d000c0c43c5401481a411140000d1419020003911100b0705807800307038001a01ca801103030560140c00780041c1c003c55070f03004006030710b0b10540c0780c0c81908501103421112595098101440001840035005c19055500e54080703500c01d91410180c0d000d00d440b43d006800e41f0b241c10407010304c0c0701c9a09070100b4590780e24200344010324162505055100d143d0040342e026000d1030380101016004041c141c01e044100008100140d501ca000352031280c0703554840f400103007050491400350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 714643345 1250 714642095 714642113
    0x1c052401060c030c0b041101110f070501030b0f090c121506031f030b0c0c060a05100513060b0a031416080a021803060103031707030e070611010f060905060a050f060304 74
    0x100e0080c94a0320700080103448103c0100c20566040e1100000f6981b149065600010019a10180c00f402480400014424ac60302d405040c0a82c070b0415498111340301a42d51011602c002032078000380b200b141403c1803402c414150384800002c0010544590000f0b609c90101d02082140b00c2e4007034015440d651700d50714107035020350f200200342d4051224894080045004440b8080c862090880d032241d4a00004042c00e203040002071406401e00d0810341089034440701090b01da0101c440595224210640c90b035102405841a608803c1d2400008a03903040c060790b25402c40c04541e1030400c1050b21035111000c01d1240c4110440c00040800c000c400880d842550b59801071412402c42624645001d021400090808000ba4001d50000300104400b00500d10b8042d0215008440c604041003032a81d1406201c1d1221aa44146001c4c400c0303040050014400039040200301a0440344100304054440c40400024001038603039a005070042e03440892242410081c11b50411401880c881c1146c2c0c456540100c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 714644595 1250 714643345 714643367
    0x108071209050c030c06091804050a120f140304020d14010906021b0c1909020a050c060a0c020d0905090c07020d140307020423241c05240106 62
    0x30405080d10541220403148035154001d40b00c0c0b409882d0350901d0400b09850441090500c0740304160411860314195070f4410494000386100310600d610350750b6403d050f401c1130860440503040008140d8031800065220614055001090310340402d1203407100c64008140c002102c00030741140301148840c000c2207090500400d007206e10000800c1b60f0809640d110280e130001071600c01e42494984855070700800910491000311030503150064182d44010011500040900c207900a031355000500c664224820f100700c410100c0306000300c40309070803c403500344001c0000008800050081103a840c0d0594421441a4110b0744010a20b1489450b01048110a0351100c08100d0f405281c0f021464005821044c1c10181080b1040c083e5456213014010310003604c80203c4841d074200c0094450f00580f0200182c21070b00100400c11194140610029000688c40c2600619510031401c8102000e00000621030740c3c0600d10076010741c0e030488010314519109046000744032801c108050010b1205900c5030410280b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 714645845 1250 714644595 714644597
    0x6020d0305041a15030d080402042f03040606030215090102011d0c1c1b0306051015081b2a0304030c1a0f040f03031d0306011e051216091a010807 64
    0x1031354113200710003c0d160010b07111500000c10745000c20402075180612a428140d841a807502405000313030b07a130407001100c180d150001613000201c042003e204480d8800809154081d1032009117145580c41a4440c2d00280c000f60300542c244800040d0280a44030060f42d400c611b0801440054500707810803540000400c071030300d441c0072110720303900110b9018040350140780d0040441036441819420840199003005090448142100b04201718503401192584a109503624044607a62a504900d0941c0c0b0400ba4941c203607964081000001c0e10151030b48061029a101703641d80354900a520340c56201d00440c440600f170f1810541c801c0280d40100c410030400d803203002c82201c1c600340c1407054881c0150415002072104240160080c800c158025114406800c881745442c102156543c6c002a0f41d241c050080c607110560080b080440c102174500c847c000f9000c020801c000a14031050b031a95108a2080e00304000501001d0006241000c0d20030301101500e07000046402c00020801901c00e4000540694 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 714647095 1250 714645845 714645871
    0x504052406221203020d09082805061623070303200a020a110121110d231f03170c160504270f050102120a0606020d0305041a 55
    0x8084591202c4108042c010b446041d2041c001e042c10001d10300001c0e1900c003810320031100300600c010540010b901200b45680303818171010358042c0400303a6100009200c0181107109220a00c441d0742c0781c030050a4641000799443d03051f0800551080310400c980c4145050000000b004014007183c8250080c1c4c24100c6080c421841c000c0041c071f06034101c0da2010600070016040300e030404041100720071844505041c01d103001e1100c050143c1d10007103100f800300e8800c0c0ba03041e0b0721700c90f18001d80c0000c42507403448110607000308040100d00d0b444054000d0214540d18010389007100003003290441c110004108000040100c114a0455440070700b00c43c08074404111010b13080c48400d002d00020498200007070307101c1003140f6040c1d152406100984460301003100f4070700d0708180c008070300e480440c840840c02031b04080707190304002e05414020300a1080700c61019500f40200100004101d160b00003904545495080341ca0300002c40d60111f003100d07000d440c014580c141d40c0603440c00d4284450300058004039400500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 714648345 1250 714647095 714647137
    0xd1a040b0d0605102303070608090c040b010e03030a031a041e0207020a120312050c09060a08150a03081309020306100f0908010c021e2806020d0203010f0504052406 72
    0x10391000c003000410b07201e074210410b0b001105c504082c0301150040408c0e082048060504003000d90b21203564031070a6020f00c0d9242610b28483c0e114407420340704400041d00b926960900440f001703010340854040c182c80c01580501103032007400d00b440343e46070b9808447c03030f602080251401120041d40c05007800f40e911080c0701c00301190040d1640d1256401f40d2194440e04a003c010007144070544000034160981004280311812071b640b12402103a1001c00c140c503101c80300755a44c00b41840c41c1c1000b025503076080a001080030081000c10001802200544101c10008540e2980b40d001684003c407a403507003122014000c01a81802066005001da000d810042840e94645044500712014824428010b078404060309080308070346603540c2c0c48800c200010340603100b4074406c2c820349a8070582c159500600124284c6080c49126410faa044404460040d50741c0d580d150607181881c4220701445e8411442e0074041040030001c5554040c0303003008440e603080c808600104010064100142e000b540180c16062 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 714649595 1250 714648345 714648359
    0x80c090a0b09030f01052710090302011d1204140f040c0801061701051819090f060b0618060c1f05040c0b041406070201140d1a040b0d060510 62
    0xd4040905410168242c9554898040500d00031403484071080c10303450901030010903a45840c0031101080070024009001d10891080f624040000302c02c1c8141130f00d00307514442010b40c10f4205500e41d00c407008240c000607007605462911208186004410700804000c2044900c0312500b0403240746100900c02c10b903e084001c04039041c0c034074140c1540000750031030006101940d0400081e020071481c41a1400d00d940c14100856025034203030b071103d0440b001100c0014000390580d00c101c09040c0011600f448282d8203440d04a9940301e00143c219566414072444041d03905050090b500078584180c0841c1143c254130b0b0602c10386900c000c010780e00900513441c2000d103008500100076a0f5402c1e11000280c1450141411110203c03a60000a01da103c1004104280101c00007440141c00048807000d50b1580e1600c011303214005018002644040c002c201042807641541c000061a800c07007680c10848070000081004441c10141202c0e4059070000380c020109002c1e50010f5070141c48a018500c0c45910380304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 714650845 1250 714649595 714649609
    0x1f0b12011a0915011209140304060302030906010e0c070b04051908091309020102060106211b110706020a1e05160815010e04030e0d06020307030902031908030601080c09 74
    0x1500c284200400d190308007440c242450255444941c403c9581c107462a0007000a1004100881c02d054254a07006070505001d1144001001d44142c1c0089954032907641e4400390294004484140041c0100c40c00016542e2465251034412440b84102d03618120680d0340d040d080d20710140080da0640320b02d01c0705030034400003140c1c0320300c03c0c90117200d1850b21080340d4000c10071301c0680444860890b50900c60708400507600003461a0543e00c05041c51071a030301102217000354078484a601c2c01c1c91941002c1416015810084c0031014441d010759520341c00300344108840d0707540e131010300c180401a400908078401280340090200b05103d08492444803a6100e80c4400c0d1820704071810084005103030030010099050200103900c1c4000c0307810340210329036240008080d096400100041c0034015000303441410360755500d98030425a82d0240c0b0854484c104000c5c001c000b4540360100701e0091003000010441c1c2d03280c0f40043e500b003643c490071301c500e181c3d5840011605000040c206200c0b00c0000c0c07000742c80f141d484034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 714652095 1250 714650845 714650861
    0x6070c080106061d03190f060908120402011701180c0c02030a050f0610080d030c0e0904140d18050d03180e06130c120b01050c011a0907021f0b1201 65
    0x40c1c1c800e16400d480c01407000d1180b40c600130852103580700c21801c84001d80e20400c5010260303000315440350280c220b802c10a001e801c0036030009203490000110754030030314521509140941d000707a83e06e4001c01d00c24021005c07401003c0c00703a050000d803980010b101d880800c1d0403003038074104549040000c0c01210340c0824a0524840e6045840c0d800a500b42500024100320055203c100584002c1c00c4d40d18104c0107507210415541504100f64445c06200c001e24050f0854803a500c1d400780c0180840c0c5041d007420899040c4081011a19004050000241620906480c411b011410800020880c80c0a04102a40710304801c01c6050166200c80c1c660a4a44055094010f207854030200c3c1840c07a1000c10060300a0000055002c214500a80012142ea00a034a0346031b07414100c1d800141444000016039103406010110815523080603034a1207103080f0000d0041ca03400081d14102c5013526040c1040e40c60703400c12103030b214015048000c085248066900100141d1002403c594030315119400756a094503110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 714653345 1250 714652095 714652097
    0x40306061701140c091c1a070816030f091401050703051602030315120304030b150604061d0105040f1710020306310e03090a140d0803090102040807121202060105090606070c08010606 80
    0x80407001456004c642041c0d90710202d42c1c40e0010b140e14254140f640a448841e20460030163346000c050a800301d941d020b4504507401c40c460f4a4468011040d4a02801003151004002810040480d440c0125504c001400b89200c1e0044d40c199625000a04500d0600b400141d5102c2c0c2c55800c01140c4003800e1004001450081c1902c4400d4505020700e02c2100e9102c1300d005000300b004000400490390701c500110f90780350599040012042400c801290319001d81c1d00300d1650080003210014224002555895a150400e000e40b60481034400401e0200c0c00200c4030140c01615030007038414240b2040310b034040030303205407020000418030202d009801c0b030b6140c2c0e43c1d810060b48006000320086c40c01426031401000200d210004090081c0040b4202c0180e45000904442000c0301150300752900b90140c401420803507040b01d04d816030720440240c24802c05c0c14140c0341c03000c1400791741000520216201e41616405080490591219130a01000d903101050030b0ba44026003880108500e40d0a01a0200070005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 714654595 1250 714653345 714653363
    0x20402030915091c020604020d14160915121227030b010e09010903050a0315170106180501050f0f06091203040f090b0310020c070308040306061701140c091c 69
    0x40d501c000700360500040130140540d8080000c100050351110600300d0400d5000a01e00300b0800e000c1042482c02d1140488207911019081c80864200080c0e840012240d03a601c03403007000300c1e0b030340c91140c00d844140e2000503082c0319500300d0b00012140601c00808203000c826100304507902c46c050b10341e04035501c00c0c1c000316080f003c41401040354440902c00283c025650b540200507a11982da0090402c2c0b0804464009064a8014291843c900c000a54000307009943d8442c802030b1001c0107581c028009409500c03800181941c4101e100034081c410f41d4181c840c003034401c509554002d02007005040364041032a138444820441040d00c2e4890f00d4404c50400100b000458649081c003c880c000307070400d508050270362864014141340a58000403c0021031000b1100141c0d6030b24050515414460540c002070036402c4002000000c2140c141d000208407441d980c4901c00d2214060907031401e0f19079501030403007031660a1000c034492580400080c103000d1030083c00c01145500c140d581400301112040e055980c2c600e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 714655845 1250 714654595 714654613
    0x4210212030c040e0705030f070311120f0a050903070c051302090d03020606010f022a0409081b010c0e06183601090c0206010e0c120a1b1b02040203091509 68
    0x2113100030b40c0f9000703541c604046041d881c140903100f181c2640240580d0416484446001c94200305404862142c18000017941c554030b040300c0342d0300143c001903504032003507031800c0300041e0301100c04400d451500344d20060803603089150904000050a01c2c0400301d4a180d82004452199641d550721061602d10030740181040d40740a0001400480c44100204199000b03000c02d0750030300f420a4024050042100581034405940030b000c5030003000c240300018100200001c02c00520001c4562190740003a104009014044507080200d8510305a601d0554101c0301c01e11882202c0180075611170000b08003d09040c1003009401d0210901c81040031441404600220684000e503030310b000a140507041c0c80350144058454000c0003940c90405110b208030118030304001c01c030745500e02c2089401e98680c0c44c0e59414241000c686010090440e82036078040000c14094103a0054003400440c0761030340c110800f13035051000c65000c0c000a5800140300074200d00031031402d0090400f02c2c602c0140500040002040451 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 714657095 1250 714655845 714655859
    0x30209130905010c080f01120f08121806010f060f0c0f02040213170c060f1605120d05160206060f061611030f0102180616020a0305061005040504210212030c04 70
    0x17460191807400c840d440c0b1001031007041b0b980c009114131154007142c105502203890410704414003a8a1000800070000c10901c24420076038003646103030a03030038415224940d0780d078802030400c2043c500c10b91000c030780c01c00400b413002d60041352140c0d14103004030b1a207180030300130780d000504980c0061002c1c41e241e40d40120030307c2aa00032456580d2002242c100500c140300300e036000900207009a009501c040b5030001407049445110900105000f640442101d43ca40d004a60401440c3c00c0f12000f000b441d03103801c1c00246180584100411201400d0f0044d0010361201814420201402129030390072140400070301445d580001101d1640b180074004118005d60120101400e201400c2403484040c2e005012419404040c00c0200c500003104032180d5a40f80729080030302c0c005190a82000c0c0d070180b030403540041449004a5994481d81046080f1040162510100f1040301c0341a20080c0010081070b0340100c100c000303039000c48007031401c40c0116030b0700802c441001c0c40650b204964085c1e0007140841c00304859 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 714658345 1250 714657095 714657107
    0x90c090213051c05370c0e1b04030602040614071a131a040314040e060103020d0b04140402040c020f030306040c02070e0703091101050a05090f0609120102040f0501020309030d030209130905010c 85
    0x14416040b0261742d2205888820400b0030071b0040700540c0d14002c011800107100101e00720100384040c4440c81c0c40e59600c1c1026002034125100d901c0124140e0115450540c804100f02d0b400c45510040841d040c2031440c500003051400145030b4669000400048404110b81c0491010800c15221400d00315140c0380c0380c01040030300880346000d03109000340024458606006190740d4001d00c01e203001a100e4020084900140c101e0520700e541040c980b2002225000c1d07070b200028450350090b03c1c00d0000028040080b6916961081102c0040d001480030495138502030704002d035100000d1040720f4440b0307140c12a071801c041c402d80308440803e0f0745031180c004022410003240c500704402d080081c2008090348000c2e24a10540200c1440b030480d1040702001550785005a40c54080042e081290041c0c00c0701c02c041c001d6216008089250700c0b600000113a662000084660810000c1e02400f003007000c01206401079000702c0744c2140e0003403001c40e054034000513901c0b850424901441c00801c9541440d54068030b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 714659595 1250 714658345 714658423
    0x13c11010914390a0f0b0909310f17031006030204060e010f03111317010b060a0c05010e1f0f060f1a070209040501090c090213051c05 59
    0x48001c80d0300480d06843c40081969000b2440125006182e11101001450100d4140c02481e80f907681c403103001c19145486406042100000d03074003504a44c030740c2008004191103400084140300c01600c000308180c40090424600640f188002080c0c4030282da5421a0010354070408007503544c000301c10404046e5168000030001c0003c0e0404600d414202180101400400d000c4a0705100707010222201d04c62080e48108801c00031a06140d8481c0211450b680b8184c0d964450350048130240c000c0416443c4040c40b400e140c480340101443d107031011004040d280c2140400341604d9a559400100c2e00f010707000e0041c1c055010044600305410aa403009560842e02200c00c0b10030820715010003030103d0780300c4502107002c3e901e03d8001d03030403502c5440401d400c86d40300c0e0b40d60003500310004009200411405400c401c548074807903c580da1005031107101c000224019070300d200c1c46194090314100a541000381d01c1c40c8a159003520514400c00301503e48515107120070024840c143d0b4001355841e4200691600000703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 714660845 1250 714659595 714659623
    0xb18131205040602120f0c060705090f090903090d050f0f0303060a090c0e04020d020c0a05071d0705180406080f0d09120302071401090302100e013c11010914 69
    0x3040c5410003200035174801c4800ea10720880c400000b0034001000301c40c01503841000d554401c0f1005468550001011a00542c0c003060191406011402c40c600e002100c49104510f51402035052051000c01c10556840075142036801e801600d0348507403006410f001e90f60a200341c00c00115900d08192050103080302c225032000c108686010001082164051a070407c010811100903807241160004c2000a201c1c2c412009828860302c0c0c150001c0110100e45081220441c441010341107003040c6012440c081c08941080004404005418608081c001050b22030714002e03000040841d00c48204030300d001140f1000c641030b54000034090703000303a51009444020302052403803101100050b50b00a9035076101401100c008201001c480e031050b0b442120582c0007076070003d1515005003507008018103000c2c80c0315001c90010b42c100b40500c0c10b020122850540f01da91241c013a0b0100d0706d28103103199101c0304000c2135004004039484038400c600c0090042d011524002e488c0e8450801c00c8407145440d021401003120 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 714662095 1250 714660845 714660847
    0xf01120305070b1f12050d08010f090e010f0c172d041e0812011e030f0c05220f2a020a060c090509060d0804090b18131205 54
    0x280041e0340242641e030300c5a0701080b03006654403600303401c9503c0801c00700789000c181d103210400501884800a8000d115010b1400e86441025001c0102c4102c90309005410140800700001c0001035115804a0074000444000044c603074406202e400c141d5010840e078000080f2602c1c90010090303a03081000d0741000507c0740504048800f004401d50f040600f00d08140c90b021040002400c0c01010024039107004812034400c0c03605c4209107408001500000f21212030241440008240a20488102c118001010180f281f4442c0345542e1a056140300c1602120400203140700040e65480301010450355180c0588a100020744090b201c0e02201c08050481c846035041c800c4440008080002c0c0c890215203106d0b58030990000d58074240d240c226040b50080a40344ac0c00b00c040317100d0303a003c1815002c0e9501140e008880f80c880504101c0d0f00a0242400741c000c400420041040048540c40075202e0b2a028004841c2815034105110034000b00321100700c0001c0031003090008000c4030100b01c40c00f044072407e0407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 714663345 1250 714662095 714662129
    0x50601020613060e06010305030c070603060803070206030405150406061502031206060a05040843060305070c080d050609010b0f030103020105090d020301020a030b030d02280305190201050f01 84
    0x3540d4a0014016102c08003403a44500144125504606a104c1000044444035607580c50410ba80360302100e002c000d140500340300410400d11901a9a0445100300001e5003419019000c01c0000e9001a02c101d500b4400d0004854421074a40403603442140620400034400c0d107000007440c40600580180350440d0420041d001403100001c10080c0c00c035000b960551b4880d103100100b51551311a907003001484d03100f018510843e0050240041311501161400c085092020310100c050f0380b0200480c000b8480048070080c480d0382c1c800d5002c0c652240981c6002c49019000d0344400c00154400c0240481c010b465400b00030b20360901900c0e06004000b4440f00c5403801e001a603400c05140010f0200a04109000035840d4881d1307214400304045580046c0210b58413007041c0303070180044c508801068041d009240c0b00c1811240046001c20b8005220020494481c0c100f80c0c0c00115442d002c0002c40601c038051003040e07004d903143c0c802a0f00c0c94400b0340000070303242004461140594016400031030841020948 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 714664595 1250 714663345 714663347
    0x120207050603150301090b0c0c071208180118030b0f060d08040306020d0f0e0309130c0903020d0c09061818030f0f2c0f031603081b010c05030415050601 67
    0x403264072180061034a0003e20034000001d000d8184203001502c0c00c0c4610f000d004404040324014110024800101d580c41540c0b01800d45210380740200140820f0000d2000080080036075203203820801c014980b00394a01d5451000e03044015050b041038410191580400407420009000603401100031518461690645d0340c404003103120701d00005150340e401040101d0490f284e50080012414044000c1c403000d5082518140e482e040100c007503125200e0b21081d286101d5903440b400c5050b500a41d82c4040c050300315000c3c0003100c400c218044a42602805002407106900c2c410900501102103145c003802c400383d003040003074030402c01c03400c40001880510040001d0300b15030030340a844103078100030345c1e200c0d038185c1705441300580c180c800341502e009440d40b0845841c0c03210b03401901c5030782114580c140c08890428150b403940d07180306c0251401008038040c00401c4500014080f4400000125003101c600c640645094614040a480c0442c2c004424042040034200380002c1c010f100c0d0408000324a00180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 714665845 1250 714664595 714664597
    0x100c0806121c0306050a1715270712080a08010b04080a1203020c100f060b07050a030e030a0f050109030e041a0906040e1f45050d0206041202070506 65
    0x10710524002c031050015554a000350881e80041c0001003c80000c40d46c2c03840e80e541080b80240030f1403d10b0146407014840c10310080440c0d401803440e500e0f203001a03000740e1a1400d02c64007011000c80c0900c01c0e00390010354444d01c06844c5080f14400c61100c0d45405192002400d825010b0300003240502c4140000e0103007010001d05002c0082c0c11013644c4803001c1c00f81c1000d800a120740010f00c950390140035003984035504103800018012005000400c600c0e83c1d01c2c0a90200c9004078100200b1a400a405207c0804d21071150112409001010748050b4080750b5240d031100c0080300022296a511240d000040c50303005081c1e039009620965047c4505007006d0030400710104811215440784003d000400e40644071a481440014800803c50b111042d50f000e0703101d082c1e000011200c0750941028242c030f003506a484281d2440311080702210258842000c91903902005440b100c01c001c000352541c40c408a03008101720000000a50080c02240c10141027140282c540b2a280c10259408403004001c2521520 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 714667095 1250 714665845 714665863
    0x90910060215040303180506100f0b040509091e0d030b0405041101080c1e130f0605033417180714060c0303071e03060509070c050f100c080612 63
    0xb41000b00d50f03480349000c1d4000c24243d2032841c11442c0700550a010810006401800391700c4041d02c800510340d41707402008007000305004200d4401400e110800050a040000a030442c107a542507810314800c40f61202640cac070a03564105581c3d400f40300c12811184c1c00d403148007005181684c060002d40b030940c48941080c489410500d040121800010714040a504251500c40f001d8580f1840c621805600640d426081100d101440e0000114000f0b0b6a03c1c00111440032200c00f07803035141c2103941d803a2081da10a4002503442d6143c079101140106112a00c0c03188590a03c0d19442c0c1c41d00c1207111020403605184005d080c182040c0d035001d140d14a050300092001c0c100d03a1900c0450b5a03000d20310300480d48034094001c02e24050710004c0103011143d41c00102c0f04040e4103410341742c80e8000b05500d0044058030802d00c1041d8000241101042c0e07101d209544000915002e941101c0c4030428141500d45017031802d404107040c0d10b40d10301c10250100c0e48551425003051040300e14203004001ca01c84992100c0e400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 714668345 1250 714667095 714667123
    0x17040e0c070f05010c0f142a070f061e03060302030705060c01020d050a060312081905060d02130b15040308090402091201230702030a020a1e0c03080909100602 70
    0x308081c01041900c22103070010366400402032000004044000d400101d00c130030982d0210769a12502980c0e540709105591104000c000d040b0080d142c0b601d003070001943c141c010000940170360403020038048903040d018401001699104074000004950b14126040a8604502058202201000903030f400080340d01c10b0764412100c0c20741d00c0c82008001402445100e9403200d000e4104820403158220a620880c00c0700d010382c2003080d0440484004585101084522040d55250040d0070b10305c440c05030b8881580444090f14488600f40a40c0001e0094030420710700c401d0340c40d00c5140642c02420402901e44021141083d060305060460380d4940150250500d854050780d404204441c1540d5240318103000030216030002c000c03101e10719450951544080b0142c1c9210007080b00440d100034400000c039400e1001550140850600c6551040032043c004001e4a12401060f4688008152940414001988104101980d0705880340a0010f1810001d003071104030f4100f0b83d0104080b91700410007982107460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 714669595 1250 714668345 714668347
    0x170105160503070306090f0b0f1503040b151e030f0118080d060519051009050d020d060f0c121401030b0408091f0206060f100f1805031917040e0c 64
    0x26502c04a0084c8016409040d01c0c60a0002d9021f105c851544010f81c00401030711000f0981c01410203105036405900401002000c0030000100480c0300e02030503541010b0030000315820342440c0d60010b44900c020310841e5030000d504081c903003200c2c60100160307440c1c005410020302908110b002e50000242a0140181a1207000510004410801c0d0f01280181c80002d0144034440042c80c0f00e1034107101c96000340f501a03c519146000018020515402102c00041c03080c000280d15500f03200700030704103103002c440581c1c5680090020a21901400c40011800c0d540c42c801c80e801a0325010940d84124110803c441d042001400403400300c10042c0e51142e08075001c107a0f20304246c000329004c0d0140c41c819031501e40b0352103005440c09502041a50081201701c405000018000d42081508411031901a0228a51401e20310b1258000d0304d0720680603442d400800c1c0ca45540d0000710b0704001c00c0000a842d400c203c500700204001e40546c2c1d041d06e26400151584c103040c2068107480d807200000d0b01c2d903510110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 714670845 1250 714669595 714669601
    0x3060102011b2705030d0c1a0c0409180c080a1712070c08040803040f06030f050105130e010b03072405040510030e0a0c0603020c07050f0d060905071509170105160503 73
    0x105030000c08010013001e0101c600e88210b11380014001c2c11800001c65450b84449140b52a4817520a03000d1300450180001b03d01d042e1502001000400e505003140c1401d006070507408011840200000d0020006080508000204e03880d05054000c01c0086c801c4842c0800e00c00c0c8004d00c02c4c01c2c00060390010481c00c1c0b45142000743d0901c1348950103036502c1003054bc400020301203039039000740c2d03c00c4045652684060114501030352074942500c01c01d000d1540c12418040a541c1c06008603003151480b01184000001c611100502203030510400703030003454000e0440406e140c010000c02c000b13540201014601281400d0070310740011030290b03182811800305910340c2402645080248441040907a01c85404540a6134402c0090b010350423014034552140183c1d08005218100104429030b9800020300280c020b1002e6034801300208412074068a8912500c100803a04002c6400e500e070902a49440b4034801920b0542044984420314041c20203a034101401c0c082800042d189030070713060185007031440d10380d0b0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 714672095 1250 714670845 714670907
    0x203041a0c0c01021908130f0215130b090118080a3801050a0504110d1d060108030c0c040c080610050c0304060c06150e2a0d0203060102011b 62
    0x2c0500d409600055100288500d10002482c00100750400716441b814101d03518410006140e100848020f450484c0511903940180391070315400004401d42c0c5100750404900e40900700036000160025454107000041c03140780356070480d006401c181800d0341140b001310b0600102a48803008484001e214500480c42040301200c180170032280002d0031000742c3c215520140d2202c8102501b032248038041e4060b0680400c0506050041d6017010405080707070391400415080f594001c0c081c400000703202c400300d200103005103082030008074020100c0000441d10b6a0301c42000c10305000c042c602da0782c8582e1070480221000c580154519510210440e120321078442c6000c0107540612034034917141c10f0b50000140c00300c4c030f00360041500b03030a040c000d5504000c01c03403010b00e0010800c40c0c0d40c0203132a18024144006007440058000b1625010005604009184503100c000021500020300e414042c68020082241c6964240b00d140748806004128840408507901e0203449004c0b03c03100300e5820601c0f070619030112 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 714673345 1250 714672095 714672097
    0x171e030706050a0917031506031f1503050a140f150a0632071202010e03030a0504110301050c0906090a18090b0c04030302121606150f05040203041a0c 66
    0x203650040c90034091480d00c2c94943e03000303004c0103000700c0c3c6030a80490840141ca032840c05980c4030300414041d000316007108108019090b08000c02c045d80d13070600c2d00940d0342e508d41130000d04402040c2482010048104902e0f0103415940000d00b0a001a4030703283c07121142d4003c500181c1d40180802841198075192416200d4201804001d01380c0c00040c0240700058180e8410080c8144401c0c8a400c03035000c4e501e68110024140e1003c00f000303410002131103000082108450b0301d5000c1c1d4060b00000426045019004e400d41d041141c0c82c580d1107035100100420301c914002014283e1204400812062030140c0414003540a01010b00c0c3c0905d4000c80e920a0760340314140c0300e0b0040c109520490f1400d42c0d0341d50241c4058031504e44100c3e000320080d000704184484840903202170f654145c0180c103070540003003902c000306d400c19561200309140111030790003c1261442aa152541c07500080c1200c2c41c00c0c4252280b03001c1903075001c01e0240f0300c108208804907807a40e1803000441101602c2c1ca8803038995001141c55 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 714674595 1250 714673345 714673357
    0x240603060f180c03071101090c060503090f063c040b0a0f06030b04060e060f070c0303180309090c02030702060f07141504020a1403030a27090e0106171e03 68
    0x61821082c040c0980c04080348080c42c8561090303030341e40c1c0b41115140c0c816820b80e900148010051003029100b4400f25000f00d000e980c0c0300f00c2010803030b80c800c0819a8a6890861300b56405a080c4052011100e60142d006510f098031103001e052651038110b2040c51031280e11030061001d043c030706400f004502d0062040d00080c0309201c041c1c6040c85030070307100d00741020404030544044400c1450007216080801e00818051710402d4107901090059462450565a52411240450815684070707600c0b24400c000a02108206019a031690500f500785840e00c0304545542c00e001c41550700038480d400043e0f503014111506160500c042d20f880e601c2904c1c0120003a4400d010002c0c807400b44550080841c0c41c50100684121300071541c60074450340d644040c1581044010503d070f0141c20402040007094003442c104503011070410f4100c4c0004603c0d100c2c2c104400c0075500100d0200717403201c40680d81c00d01d09004110150401c3c080c0f000f040c07185c1e442c0311545c601c500200c880c0c0c00e82c8850104001c2800034415908 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 714675845 1250 714674595 714674629
    0x40203010209040f1d010507080a0b0a05041d060c0412030c05190f11041116020d0b0a02070516060f0f090909060501170d120b0a090603030503240603060f 68
    0x45130701c5804524002805082550380b8650700082810030180384c0501a0728081c801c641c0702d82d00545c0359030380100c015181502c14a500074490a9000030503131928030560b40300001500c4640c000b0619844c0160401070041d02e0700d80304040502c0240001031249046049540d4035040c5010150300601d48942030001503d1240c12036413554518030244521840c82e440064031500c00700203d4624401008220742010800403c10801804104040070010120400107800189200300c3e040c881c1e51030303001000c01194201c201c5034000c01d010b000c22404010324129000d0145e85c4600f01810314000801c040f620113190300c00c01041c40400d000361401150550013401c40710800f4010504142424006000c4c01e228481e255070100a02e40445c80c404070f68401548425034500160800c000030340030107003201c01081c80d8001203e01000800100b688640070055100b900c84944a14000280811280341100700c061452900d08010800d80c0d1200101c0f54010f030121046d0250782d5218020410181d161003900d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 714677095 1250 714675845 714675851
    0x15010f1103042603070b07030f0e01320c0a2007091b030c0801090e1f05060906103c091401030207150504020301111209060709080c0904020301020904 66
    0x4030b905220709421441d01046100780000b000c02c010072169692040c0c4178068007154151000c203044070710035000503051160001e001b1070581e0025018608540162801944075030001641c0c003c01c2000405010310340304162401442490300c411140130314812803c8a00c00c02580090300c000740d80003010b01c54078a6602004454040e61100061402821080407001507100b9543d841c141151203070091402401031551011801c0c0d207043e02500240000050b00301d11800703002d60343e20924442c120000c1008d0115030b03020803a82450300a000482c60080d107154015002802440b0b101904408080198804081c040b18008806d282d0001250541c100400c4d2003150031000600c0958080b003c3c1e001c0d500c4080218000c158140015070491080741c0b001041c0b52a4441c0380d004451580d440590702034005400031030300300014141d4560700e07440007054001141d0351b0000c0c485148070030002e186e0703c240b80d402c0c4403000c0c0342040300d010b6070780c1075000350366218034601c074005002c548003034042d02c5141c08050b1040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 714678345 1250 714677095 714677099
    0x150a12020105092b0507083703050c0307030302130b0a080c0c1615020d080108100b0d0b0c0418140f040c0504020307090e1605030c1b070306020d05060915010f110304 73
    0x51601e03001c451040052900c10810011008608048e030136004280309100c810802e64005110900e0750800340c0140d00384a001e222041e0122420309c018000f2038803980d13005a03500350700122152440c1c40c0d500044507117071060004d080096044201c46401c80031030074903644c44001c180035003450010b100907424801c1c8104c22000440b80d050340c20349103651a1a4080d01c650b02e10300300048417004405d208550250380110401c0440d11000e500900b0b581c08040d1402c0e861815940b5001c059000560382040100c8000500304551001c0500704c040c1120741600500403448070a5207040803805c0a03002881010b20800441e0411900e506403100600000c2c04c25034680c40d0030003001d400440c06100c0c05e4004071807000000d84401c01c220622540d070010751229410340d15451885101600261044101042400030040e9200800c000740d00003184540c401690b942c11000005040d02c4c0081d14542c000c00810081c00391550b501c4280092000003845d01408110001c00e0480b000719140c1041c1c40240800500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 714679595 1250 714678345 714678353
    0x6200c03030d020c0105180c0d050f010501030c030201080c0f03010509060d12030c020d02150103030807051b0703060b0105090a0608090c0904051b03151603060b03150a12020105092b 80
    0x5821601e0402000700020b91f62110803120610500303590b1502608415070907a89407804c580b000466502400444035200720596003503084441c00e0b001500c07a40c1c81c4150410444d1390003585141d004450a0b030071400e107129075080c040e8601060007214490381b080c00001c0d4207038441080300f40001c2e400c02114244505442c40241c010000c9040c1c0d40010700a4525022045000040c1000d80000b100003107040c0ba071031764404543d150343c0502a0000c001c0304100f00340c148a0300701c41f402c1d0030440b80ba010709502851450f16104849003440a503060100500141040b13a4034020341700c0485c0c106043c035440c140c2d41c0c21080d40c14080311141655000c1e103540c081c0000d00c0300025190070205560549014181c0d2450205951200c03043c039a40910b2400000040c28008241116607a108446c10081030454540300014075a4004455080304c41c56662000340d246c0c900000348200034500c02e059200c2c0c0d10101c1d0002000c0d842007500e100e004910341030946002d141180c000d44203050041d5610459500e417440c2c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 714680845 1250 714679595 714679597
    0x10f0911040b1e16150c020a030e040b040617010213051509090405120c07030b0117030711010c080703052d0d050408040503031207080703050709150c08030a02070302070f06200c03030d02 82
    0x2a4016070340d20700240c0340f0006d1300010316036034083d826071114204003806000f04800703040300d60380c0300d80c1090f10348400066040d421640c4c00041c070540300015884216004080201103801d038070191082030b220100c20f104c0d041260846110143c1554024019950350501514000c5005031803100030800007501403041c140840e8171000c0da440b607110786400743d036103080c804400c000300d680f40c020940007000780300c0000c1c800d44070f90b80c2d0454042c10011100340044d110300400380c000392030a80105200049600d080404d4040203450048242c0858142e00740c5080c070042c060261680e08030026aa0341c0205088c8981401038a00a100003070859a541c6c010384140030402005807000300104001c3c40128035018002e014003441641207070340c1c100351a86000c41c6034003861306110b9040140000c0c141c4880108400c80019441050718038401740c3d807030a081c54000d2800c5030a52084c2c0d080c1d1035042080c0000b9034050a8800b00c075965103c00e452503078000c0441800c050100b41c0c032a0b0b00d0720001401f4416281d880e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 714682095 1250 714680845 714680873
    0xc15110a0203130f0b0319110d0203040b0f16050901030902041a10111b011b03030b01020c151206120106060804062f1b06010f0911040b1e16 62
    0x1260f120b09581e0f5038442d1000c101e066001c1d07035242d99018000254482c145032165148000c58101c003180c024000200946a0352024618424880e000000c000c1071188464055801074031003e485038035407501d0207409047e00c400384030142c00c0100004810000340e03c039400c41e16910380c00078020002603511102c000d101000d840f50840c05500010340240445000310900d40c04d81d1688000b414640a00781c0c82c0040d0020311808043c1400440721014007880002200d40000310301c00d8a00107803642058001a15100c10042d4417481941910705660300000c40701e00b41c1c1c0c80d240d0058000d04c1d00f40c0f1014000b40101c00314a201059030340c070746000012029032042c4040d002d02c0c00f9810810602740501094041280e0001a07402c00032100c035211039015500c0790061050988806040a115400e20180307400c1182c01e0748440161000c050301032290014500c40d000b0320409404d12241360034078141e20248a4020b080c6001105450f20742c4401c2c11503a800110369500e40100556841c4044520700b0390f10703082c408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 714683345 1250 714682095 714682117
    0x1806030f09010b100f0e010912050709051609090b0609130501060e0a0302060a1d1c0530030403120608010e12030601020a0209091006081b030703030c15110a0203 71
    0x242c90200f0030b0400d810402918941130341e800c50701c400800415100300703002d0500030741000400680041e9200170315907154202440351000c0c0101602d0140e1000a0310307405040745409010004c0015059038020303491200310340d8050004141c40941e14000703861400ba0368415608142e6894001144880b60ba0129058942c15143c04e5140d216190504c41c0404840c003000b5084581002141d40450050b00502c0c800f007104001c15218210960101e0805003c2c10550900a1300c400700e088204941401350201d00b2209202841c285004a8484c6421002c600701c0380c11860800404070342414400d00d5200720a400d03120342408020b0b40e8000c418020000c110200030780d4028403049008409840c0c048a018100590041081c02030540070882000b0b8003414030f12551251104100040301c0784e01a0760001c100080c007600c0c180036100303180d940b100d0403401001d200c1d801980c810700000307421002402e01c0c1a004000021043d2205104000800b4400341e403040c2c0e0300d00460120850f650000c0286102821 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 714684595 1250 714683345 714683351
    0xe120a1e02030a200f010f090213110306060d0f020301060c12020f060a15081c1119080304053d06050a120f2f0d02010f051806030f0901 60
    0x40340404a86038024205442c0000d0b80588401e90001c581036030b4450520100802e840b0305081600405007140c0c4414260901640c803035036680198507101c0d12030030421050390070030300c010611601c01c01040c0c4402080e541c40742001103420000200c0c1680081e50845460350210750304d50f1540406458029194003c40d50b001d50340b040b00355038520200c0c4820324040c0e9a0b00821480c0c881c40f00c100060074911811041c2440b4400380010511010401d2020510300302e4000d0010100342c0c40018100c01c4046260240c582c80481e501020405010801c0c0101f50440350003074494803140380550034000120707000d00c0c5415054192a10310846112482d8061540c0c0b00d43c0400081132030346003800d039207444c0b1619a1040c0c401c10208000c5240c2c183c0720f246a44155070101d122a0070355929591954211207818450f4903c00c0340024445840c0c0d088621601c044511510840300c960000300036144002e8014100b0030049900903184150030750320085220000c00880c0c60345400c1648843c4c03814115248601076003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 714685845 1250 714684595 714684647
    0xb04031109070e031005191407081608061005040b0a03142a16140309210c120c0301140f060906010903082107020f1507120e120a 57
    0xc0910008082060083d000d40417000314031654100600b00100076111300d88a0403254030100145100300400044440c1c0d10600b28140040000c1950b90300414410141e40000d40200800380c20220707040e4000b03000c44861221000c0c1110407229801154032492070548049140f5041c0c03509034209000140d04020030480b103541c1c03203103020b0440061240c0c201084001451080c4141d232001300a0840710009101e910925420b9074642c0c03916520300b040820243c1010510007407070b10305001d0701015111700d403c0e80d0240c030148007017494441e02400000382c031401c2c20f03060083d4803c1c018400008503800017802000311020342180c180c5403c008486120b4441c03031700c00004a05103072502800b8080c030010b039200800181160f4442d421a13020500c0f0400100a400c2200903260720071a840b4800e9007540d016099404040c0289454404140455019503580e0020021f10507030120b200c591004c0c2c00c80000c00d00034840c1240900300085900c4441c40c0c00c10001d021601290000358400101c1100d07101406191 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 714687095 1250 714685845 714685847
    0xd090c090519051329010f0e09030711010302071104051906080601030f0b090c030601060f12050705180d1e0b070305010b03070f021504050d0318150e070b0403110907 73
    0x243c000c89007160003400f0300d55820003080364500071030808561500b100e02140740d0a043d401c443c1c54264404c02d2078000c09041403098030034400300d40b1b03000468540114140052565200e5201c0042d02c040c0c2d04041c0d0128030003040c441200303489a20002c02400c10021800d0814010341c0c050000000001c6d40780c20311000282c0500300085003412283c00220002034000c803651603104500000d40050400e01c680008512142e4060028074003c3c072003616048940080c45034042d281c1000c03607905030300441c64001003044041e088021201c00740b5040070078800307442002e00043c4038200582e4000d44204602030640c00c00808001c00c03039100c14000d140400303131566110421003d54100b409480740b0781d001840800e510790300541e03030391412001740d005a428424800742c5000e845a011038060310780303a006515020100e500b5215007a10300001c4000b60b03908003602e450781c244144c035005209408a650382c05112200c0003d0050f880540100043c40d40d40c1c5550f4184039281c20981c0c1c00c0d09224a8134200854445 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 714688345 1250 714687095 714687101
    0x327130e0d14030a2f0a261512030f03061206100b0702061903240e13050f06090102040e0c030411130e1e010506030f060c0d090c090519 60
    0x600c0803030b0700da8074503070318099031001911a400280080070110802040e0301100001c903404002d50940f03c03944c81d03031900e843c0203060f6400f074141160784440845080c800481d002c54015400700780000542c1030f10f0780380d03008070b458210440c1090382c1c0d5001c003007000c1d0500340481009501491040b1203440c10103a000d04280d2302c6a000740c0d46401c40807020754040280510020190007010300090040b801c242c00d07110b000e82c400c4810f00b038100000ea65881380002c0ea0840840c4003039031440713000031617030082c1c00c25454040b00d00d4007410000103005010111010410308009070a501a650801e8840342d0a181c240c45000c1d4100b401050260740086001410a00c1400103980c4500e4100700c0a442c01070030b00c41444020a869040514040d442d40745454018008004050401c90700240c4013031201c10f1540c00c0c0382160406400d861081d04045c0d00911420170000781d03940c101d1080290541c2c1c407100c40b83d903c4003c0001d140c00500340070b0007800010304140140d0000e4401c400002c2d0003401041d40a403004c00b1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 714689595 1250 714688345 714688367
    0x1f08040b060a230307031208040b0108010c0c030e04090624080d0e010318020a0f03150506010824210105090a0201090b0a0e0402070b0405120901020327130e0d 70
    0x2205070001e0082d0f500c0c6003001043c075001c50340a400c0e581e6280d00c82e11090407250402e503460002c40c03c502c0911080100e440708260040007000e0007004407541042004020595841c3d0103010000e80c04981d101319581e690051010591001c4c04019000d442e903d125552080c80200140000d80008001040c8901040300a2300540f030b5560301035800003200041d0010451160b810180e0449a020b03000141c48811000f0080c002c5442c040038658518541216040100c0f030794615028182010300c0389503604240003d4005a000c00c01c01c01c440d0b80590721031000b03540c40e000180e0100c3d800d2499541d031481c821900082a6880d00288850f984044015680303004080001b40000c2c81c46000308441c100b83c03409000c1c0c0b600303c1e03d04031480b800381000150603a00190780603685810804141720400c1030400010300740d00d116034085801c00380f0940000c1c0d101e002d0f4000703110003604007001d04048110303012000070f0758003c0100200007000d1500003070401010110032100b190b108900b12810f000b4052019454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 714690845 1250 714689595 714689609
    0x30b0a0c0f050a02010e0708160506090a120512040905060906012f070f08030c07080a1e080c1c090503072904080d050309060a0203040b070804021f08040b060a 70
    0x7250007050034080312240e201c90384020440d503954403114200d200900038040285058402130412101c07100d60321580c0440c40d071055100c0c1c40c040220340380e15100c02d801d001c01c5a03100c0301041c4401a6504189041100b42c8660103440040002e0100b03290b1003a134002400b541094038030307444582d584001921542c01c2c0f4600f040c084641d0760301554049041c40d0420252607001401c2d00d04c0070341c3d2a60000359034420343e01300d140e840d0408201d0300c600314020085080100800c0740103180703040442d00d84a410340000040c01902184282b60f10080c0000c4001301c44800c0030748401c40c0d409071060224590309400e1920403100041000000050030b2a00248000076641c0125401b0840301120802d9039030803054401c0051600410f0200150000c014045003042d51100c5e120036a481c5000d01440341001e00c002c1902d50701c0307817044c4244004516401400c40d404812410070f820203854600000361a11511102c81c40303846d40c55100d91807841d81c006602800b0300e02c00e081c48180c50321080200490050207015401e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 714692095 1250 714690845 714690857
    0x15020f030402040903031b050306042a1d06031510080603100203040507120f21050d0b01090e1e011523071a070206100302060d020a0512040c030b0a0c 66
    0x1c0c0503103001d5006800030340c481d0800144402e03401c5641c146400c01c000403a004220302004025040c28640a051100a00303004a4940c0c003001ca00f1000d0b035407058104440030050005010700c0c02009500b001030f13954034000d01c11034403840d0010501051010400e0f0003070080c580d0306410024240200c06940c01940c004019129174900a51003000940000b0010380c0d641c03003100d00005141040351084001640103580508105c415800c001030451a03061220100310410309030f00d4006540700d010b032020101c0710400420340711604030040310708808980004000700c0c505001e110340e00000410380c6510411103410301005aa0f41c159220801c0b101e58440001305020b848050151817034509080507040b5040f076000e0038800c007512a0082c914486a40281800c07000c4103200f4459010802180d00808036140300340c0c918150380c00b19500e030080c4505030034a03e030041002210341d40102e05a078400303000100160700a1070a400c0c41da103d40c0c0c00c3d00c015600780d485400031550110f07042c0170701583c114071a02c8107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 714693345 1250 714692095 714692101
    0x5040b0306071b0206091002150907030305041a0909010602011a032a130e06040c0e07020709050901021c050610090e1513050f330d0507080a0b0415020f03 68
    0x383c031107200129800c0341e100c902007216142e203a40b20034040c214104143d0041000300b1031842c5c0e0715040c8402410464290f80103580c00c000080d80314040314180d07030b06441003034840c40950442c0780071030240068417584203440034000b0034140da055001e9500300b0707040310b404042d0160107410316443d03004400a0039005a008101c900300300f0a409003110105038080c03c1000c0d601250754038601192016041c101b4036030040014032061050030010900a002454500e03000c44c1411200655100c0951040d0008140c84030300080140f1020f5054903401040304c8043c079407914010405000030b02e4202c940303a20032034602c04c928400a121b50541426900140619510354541c0803030440110254905241c0c0041001740d665001c80c01802814050224054201c0c214200140c100400004511243d01c02d94119107c410329441808442c20410703009450301500d2062908000c0c3c100101500800700a01c00e90005c1803c016803540780c2e0340300d0340c000d04922814a420030701c040168031070b500781002044028004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 714694595 1250 714693345 714693377
    0x30609151214030a090509060405190905070b0408070f1203020a0308090309040f0902120303090d0c1703011e05031519090213090201080a0603030804030c06230105040b030607 77
    0x341e6030701d1900486085121181d00e10540d40342d940301501d01000510b20480c1000281451040a034000344100e40901c81c514083c644001d012a04c0b9414001041d00c9101d62014002e0610454014082d00710022703543e540c84d1405142e403401c9071310610001d00401d02d40001c0f0b166460140040c5240d060340039161441c80c2c0e4500311a80f80020384084814001002816010b5882e88190512410040c1010903540600d00400c1104914094400b545400803c01c11082d407502091501506105043c19a189203503800d141000045e10b0900e02c100382400000494103444071074150b44130801c0303103500711400780d00d8005064a6004030070340f02c000c501d6803a01017050a074040c1002c205001c0c3c00100000c01043d070f90002011441a03d00c2d625526903102c031380c0d9056503481030180380d010070041ca00b440003615654006101c0c4400510203406c00151200003001c002850308590040c81d40400012800c405603107601d403091000f0f100d003910441c902146c881007801c000c20305030711452719511162000000455 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 714695845 1250 714694595 714694619
    0xf08010905090a030c140316050c010305060112180501020a0801050a08120a0f0201150609050a0b0c03030f040807061b0807170718030206040b041e080c0409081b0d03060915 76
    0x1008a91120003820b807007080d003400f00048c008140750b120b10341c40340350f0648c100030f130401c98502191410141082c0400c981640c008076035449240c50548000b80800d03800a6001000303922840c02400c2c1d500014840055a5000780882d060302e00403180c0b08441036035242410366446070704920f00300c0c8280a200380088240074188900b040c4215000200f10400c030180c20b41402c0e9255000f85020030b4480d4001d03c4141000a92000540b000180140c602481008a59603c1c08000d0032401d04c0c604420004003008085801d5441d03856111105000301c0d20042d501d8510702d0600a000310004070000d0024080d2071040c4030b00c1e0002028054942c24075152030504464000118180040c5800440d50000060b22800028401440c20440079612141402c0c11980b4001c03405110344030302424a40700348491000412805801a07044600045462552a20b01124000c0443e80140b440c0111200d40c2c0e842c00205213424020701d542c1d410001759441e404c61008480100c0d401d5a2004e192007400c1c812000403007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 714697095 1250 714695845 714695867
    0x304120b0a09120801030302061014150412080a0e0d03050714160305030c01110a0512061314042a030f0510290604050f06090d0c060f08010905090a03 66
    0x5039000c510402e00352241e45042d0704103507034907000034052001001495418080e1039002041040c00360351192400b4901521000320071b00d001d126400f4004a0320f07134902032804543c01412454a48003e590140c20090029000044800003040f20028500240d10301131000c485c401c1e40c1600c0d03140c2050080e4941e042583e40c81310f01099203110312001214043c10000c90f02d001144102e004580e5045c0000ba814299401469480741031001841355005040d00702054400b82d51403402080400c0c1c1d0b0b0000040c902c004925283d00455151030348a080c0400e210000c02e100714060007110402d00781c001582c0800d0503c00300840c012006e0f0304010300c0014410502510f040d4014412112000c03180544d00d000c41c0c00e4008854500381e0308d241800f1403250300e051407940c6400704603111401e00e8070b800e0100300c0c20f004e00b110044c424400042d940002d56942c0700005582da811200c10716000b512000043d248a40440e0a58041050a4000208400381c0d0007a548500d40b4a800f82011180503502950400108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 714698345 1250 714697095 714697111
    0x17190f0507032102150606120705130902070605100b0418020708030703060312050309060105040c0c21110c0d1106040e0c070c0605131710060b0c0f0304120b 69
    0x10710400008541e0156155090200300142040103461042000c1d2038125036516078044c0369480000c02030195154420380c4c110030074001d0b40d5103e954030324a00310345510820210602e40311b45414046481d40c40342e4013030031141d8411074080109840f40100d49a0301d00092080404c0040c04010510601c048035058942400002c27001504060761542d840c1c1c51a0421581280025502c01082003440956410b90100112030b0a10740c1c5142041141103465100500415014513140d80d41e5216252007502c200b841240c0040900040300440d10394140343c0c4802d806000e00242c0100e07011801c000e808150000c050b100109210149130490741c9944810441c40d003070304d50002d0b0510001400170520200c1c5442942901c07a83c0341d40c1c0400346020003a82c0300c0754103c00204801404003000c141d10800301f800a1f107030b050095501c081c90750090680341c030224040d5640120f040080018035811285c02809061a01c0c60076210340004040c400c03541c90066124040b03820344810321140c042a01040b0441d0004c4c0f80c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 714699595 1250 714698345 714698353
    0x31b011205040602090103140c072303030403030e071a07060b040605030604060c0f0f022509020f0301050f0102030c060c070c090501180e0106050609011202130f17190f05 75
    0x40a0300008403401164251000340e0000b0f030b80e200301c4da071610032101601c00b88a00c0802c0b03400c08600c4d100b400c2c010032500500b2400220340c42c2e04108902190704601c00403240861b0b98906c0c01b4500107020304410424418503210710000407510400140e110b107000c20301103031031034103001e1a52540340280c18454080c50300141d4490021881742c0f8140550740c41580280c0d03001c2810340700400d00829407040c080c020300401450b1030146000c641e01007410503921141001030415a26140c500c150142482c2d8804040c09200140760321000c3d080300060340c1281c508443e2001c50342c0022006907141d109a000c0351100d5001940001d007403c20420150144038058820254038689500c150300c00c540081c0c101d000e5004081941c0010440680108010b42c14010000c0c01003502d000c1c049522800b40555660600503910500d10740b07031490fa030603203210206e0786404034000350741c4418010744881d070340c02003050107416460426038542000489843d00410703680410744407922926103030003c0c480c8041c103d0389801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 714700845 1250 714699595 714699617
    0x260a020d050319021908060f0603010e0a2406021c02030f1602041503060515030309121614150f07060f090c090b0a050409051b1f050d0c050702031b01 66
    0x58078400f40541e09100c0c403017440700301c0d400c0001404960b4010103603803061119040003a0716072201c2d01682c0c11254030300d034080c00c2602c81c2c0508801a14409190800d04820850b0001502c0481c1070805e040f6180c0740c0035508804a041c0c420445070341f4420407070015900c100142d07040c0d40c080600a0003010a100204c60701012140d0020b02a1100c84410901a941c0703002c0a1003489100c0c40751581042c0c0341c054559004000001181c0c03603000d0380c0d005a1040084240c1c2d400804814080d0b043c8446179001c002941c070740c40d000400812011488160700503200840104200c0c1456000c40d0040900c03480031504181c110380e03c3c040540803004d06c5c00489034403511341c0700003e041c03505606c02070442e00c600820041e5201c0c0c1442100c4545a011a11487c1083d4001002c2400403915a4032401305605103d47c254602c004a038203080010210180714024419418010b90301401030180d030003400c4020b000841c1c1041e0101c8560099800113503064000011103520705c10f07210448100740506041010f0f160f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 714702095 1250 714700845 714700891
    0x1509090f141e100c17010e0703061d0f10030b01050f061c06180c08130f0c0909110907020c010c050c13021801091a090103021204260a020d0503 63
    0x2151004401c10303503100f05042440005540106401d0309280d00c0d10b081141c8042404400c4c1c405d06210710744a00522038081800300f4402c0d04180f016181003a88141c10300300d000f00c44995080126018580000d480021036412520b448445c0200ca40046103100c8613403d180c10400a5843e407245558000d074200100362503040031902892039075150440001d0304a180001c5002c0e101c0400c04c2d004404c07454030f01c2d03007640b0760303080035000f500a0101d00001d6146141454000c900c440000400340c003004088070002003401c0150040481c20b44603041c00104c00c00060148007201d003003a640c0c603000da0401c10800305103510455440708514012000c45c2c1e0b81d01c20400200300000b003000c03204124140c0000e044401d000705442c642040000a103010000c00740340000ca283e3310031810b00070648283c000a03085415a10a4043d1032019114003003150150400d4609601c651120b01c084a90035004181c0448602d02ca400503200b075580f15070054402c9510912040b01d05a0005062414513221120450414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 714703345 1250 714702095 714702133
    0xe06061818040302011a010f0203120411030319090e0c0a05070201020a140307061109221b1d010201060b2d070b040b010801180201030b130f1509090f14 67
    0x1950103500001450b038a03480e146d4600817121440c484c18086442c032000600c42e800021201d0134602c09583d80ca40e40c550349440001c443d48211501e0b03040c032001ca203102c0d020070614440508000f15440312414240d5642d25840c45110480300301d00c64500511603580924011001402103501c140f060703501601c559070302d010342102d000c040b601e542e40c4003183d66000c100e550700c02c0041c43d540d0360310040d06010090000600b60031540c036840441d012903c02e40303c40820306400c088101300082a5110b19556040001000603280510942c1c5103000c2440d030181550041c441c4030281c99121002a103440c1480d4800311080d8040a00d60500f0030302e803203548080311404c80140ca0400d202c2c1c000c0b10b44c00d0800c1e050140c400c42d811b8122160907403404041c000c1100c1040d1000302011750a0a011442c0d00c3c0e0340b0009440601c80c1c02070599039030300740908140f8001035540815403e80c10310040e050459162084041183c140500041081803441455404517040c00d481c2c6800baa00301080303e0640014001681708 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 714704595 1250 714703345 714703351
    0x80703021e0903010e0f06010521060f040204060b0702010c02040209030a0602041e0812160309091b020d030b0a0b031302150c0c2e05190903020a0e06061818 69
    0x21401050440b05440c080c013030f900a0741040030042402202c041203903a12000b0621403907204021232030155016030801c8004416120400042c0d84080c0b4201e0100d030b252640c1150101d200354644031000c01c0101000e0180e4000b190180d5404101e4441c0350b003444001d502c8018119807501c500c1c0d04070400504140020005400359442c000103d1701d1184464a840c445500001c3c459003002c81e6600c1c410b090300d0182d6400b100c552184003600d03a92070400365240f01403900910580d904000c039240c2d90400c43c074000760745031440d903007107900d582281c0c00300b03d00b221030030340d00280d2200c06000c04108011098000e16085041d1104550440400d540020513541c0c3c0008014424403011941c001d05280034060301c540c0c0042600d8103050680b91030507880c0b0150304c504860142141004401400c070788514196000c5d03440306445802d600340040c0018080c0c1c041848100d109010082c0081840f0681a0303026024180c050805030034207241c221603100d10440780c9a126007100c0039815040344031490001942c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 714705845 1250 714704595 714704647
    0xc03020c030705100e01050610120f050106020303070801170c131815060506070b0c0a09030503040602010f0b06130e0c16240908030109180f0605010f0f0b040608070302 74
    0x132a908a00b55607098031404008005170380d00d0081001001d40300c40d040d40101148a141441800340a00204030003403203c42242121245800008a2080d030000000c50260f2041d1301d8601e0307d682d031806403030f440a01c0d0b81405083c0c0d401100480f070040c142003008802c903041740000070460012800b107809000c401e41c1e1040e03862160302401c18040c9081031049401411040e1070039841c0c10000d480c2c03034201c0240034144410120b000941001c90340d104a120b00040c585c09410382e942c50342c2c1d4100003401b0300f0b01000f240e101940303032984088480c0307000d82c1154031070032100c0722070a5090301d80f880c0100c604200130504500c5074003c22845580b800c03a02001a402b074800c2200b03410480110300c002c0d0100c400b68244108a80c5014215008a1001402c0d60b0444408010128041444c50402c01c008240414020b00b0f40701d40c80014802c100f83ca0b0880303030680b200d0050401359a9510500b12243c503106105c3c0d444985d104101c24014140f0521200e6400f4071305041c007502c0d00d000c5100e03a040044030202011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 714707095 1250 714705845 714705853
    0x6020d050103021806010f080405100609020c070501031e02031009091b080102070f230102030c120c030118020d0216050c0406061110051509070207061e0f030c03020c030705 76
    0x8000c51803c4401904d190301e0601c00d461407480c040300043c020b14003980035041444180c00028080000c101b0001c14039000c10801030013041e650380e00d198040e4101c8081c00c40e0a02410401080c80c0d4428410803100801d50805090304084084c0c06c18001d61015104100c01410900302180700364507802072161143c424403001242000f15078030301d0f0b000651070304009260f0340100916004186008544600d443d00f1070400c4083c039803141d1601c0b2410903800c00240700f42d40044100400c202c8018040d00c01040b5109049607075550303000100001d40701c240540d0b01c440d00e02c800742c0c81008455070f014260b5655600c00041c80c0c010340e418000741c00104103004070307400d6119182101c06400d090040f84010222414090030644030754568613110240503902c03100d45950b44002903904e0640025a400b90701d800f030214455800d2411000352a80854000d44000c144c42c030380325034540c1e07005028421010415a50f07a85400400d06021000303001548a1401019024001041090800e0008019541c4600b00034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 714708345 1250 714707095 714707099
    0x1030f0c03050a0f060f0606120c0324080d090501020604080c120c0d090509060a0315060506120f160c060b0a23040b03010e0307020118090203150f040c14130306020d0501 75
    0x170b0040d5181190000001030a0101c2006000c0d00050407824503814000003040040303d0318802c8000780f0a50132210031221602d181d10221030741c0380060710143c40381c1805560641c4411107098407940c81520400380160f100c20005000b1400002c058510f050400080e2018000c025500102503040008440040e801c951816826140c0000302c590050000740d40b80032441c41d2201c0002e150f8003403848064560188910b04002240490340080090040100010f8452108032160701d4025000c40d140c01d610608100070a01031125140e565100250964485550324459500c44018040d0800e10a801400d8102c002c00c00624080d0102854003030200f0004846162600700415921148442406645006200c03440c04a011080b180803640a007045045c9292001000c440e031007460788020304640c070103c24882c12040803c502d50448200712610504585048108410dc90281100d200840d142441801202c07081c04040d000c914416903080890560743e445030b805a82c030102541752003681d24401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 714709595 1250 714708345 714708353
    0x13060803030105091015170a050f07031505060301151205010f0b0f0c10020c1501030c210f0b160e10140702030703050a26030705030a0b0d050703141501030f0c03050a0f 74
    0x11507000c020323200c3c28401d6080950400c03802c0003016100c1e200309038a0704000200d5900c0300380341d84024100909a290f8a680d5000a01c0001e1290070700d5500040e032000c5484020355180c011a81601d0090750074000540ca04103004036140c0c00050580e0703c500052007000502601408800400301000001507600e2010501003820302040d00071041a50700d8241c01403010605a1100b00c007a10159a5400300d80012590350303c0040ba02d00d0b50061480c0c0c0d102c00c0320001c0000b00c1214a000f928200d02e01d9010b404d001d9403d4400000c4460b08035001915150b0b411701c031a1044413850a41d50000b1003d625011154001c0fa08181c0309030411b0360703194040c65071203003001903030841128100f080055041c00303d01c2c000000d4645101c050304c2181007210110128410b05e40070303401801c1500006001c4440d6003072615200e5103a5030944400d03910710302c0003495049008404603550341c14035403540d124100c5070b080d55655050454025826102c2290071100400000c1301000004001c034000d0010001744889890 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 714710845 1250 714709595 714709637
    0xa1e0906050a03051b03011401030302030a0909061202040906060512010b030616050d091b081608070f380d11040f031211061513060803030105091015 66
    0x840755014000032202000070a01c00304800341901041400d000ca400e80480000b80540b100c4501c03c051902044000010550000000c0c0300505442d121404550755800c3d9510031a01e852181c2d0780c110012101c4040103240650000160310700c01c04001a6507600da201144985c0740c804407042c1305070b5441c08059205d250030001c095200111940e1002c41d0300640310000c03c503004406059110039114072420081003031071a1501007000f0340048082110380e0380c0998a6440941618846070300100391400701e40440c0c0800d0403c02d8460b101d801d8540d83d841c00700110340000c030040c100614145180da0400c0341741d200d0703d0b405100e038140101e103d4075486143c56002c1250544c0d02c004103220400c00c0100841c43c038400300d440850380c00c440d0001c40803241410135694503250728038103611400340504008910100c10440b00700d40200341e5852090401c2c180d1060201c3c2d0203409900d030241d0003840100200c5c83c1c00011a0352012551f41806062503a5042081d1a601c605001102145c0c0c4454020070000e0400c3c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 714712095 1250 714710845 714710849
    0x60c0c080d0c021c170d0c110d050a0201022a060f1012030509040c0801080f01090b0a020703050c0307110909010911150c19031e02060c090a1e0906 65
    0x50301800d251107070680301a0a00d0040a0000d000303d107018502c015268191040880941d005000d50341a0061940c00d425a40c0c800f012248000c0c1c6001000d841280c881c012001100035003178014080c0030b855410aaa654000b100c050007103640800c40301e0f07042c02e030081e1f0300801402c8201c81d403890082c030410414204080100710300030118481c0308211200701d2822103442140c040c1e000c4c580e6407440c0c90400300d84510031038114581080c14600c410181c0c951041c441c134122150b41d4203a60a0801e0302c0300c29800c5c0e900b640800b4105544201c003148030082d40d5802007006920034180649048104d440003400c54110407015101c00344425102400c81c184a03650a0f4441c141c0e1008102144045c2e0780c060030360080826003406180b44c482c40a401003510350460b40304614190859150488410004c80e000c1041101140001c054002d5403008503514000440c51120baa00900030581c0d81c614022030a4000c081d0455100d03280c180c0024a44043c00d0072080030329441207440c00c02504041103070003581d00329 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 714713345 1250 714712095 714712109
    0xd110d14070812031e0c070816060615020a060b0a0e0f060f0103020c0a1b0506040e01080c010203091c0f0b0708040203070e0c04050904020f041107050c010305070f030e1204060c0c 79
    0x10410010100c4465040340d603540401002214142c5480e99607001c0e038040c1000080c0388c10350010b080c1c44504910000003c60511421062244a4a4500a440d9103e0880c03046025a2045002c08001a000e4004100440010b4180c5d01410396403006800c100e40c0565200d4540124281031107003505000d1030004100e6007e0030198a4640f4124a440d690441c00c840503100c9860196010040780992542e000140b500400315a12240c84407010b03da1414203110b060044c2c400c90001041550000c4186d44107484000c142c9401800c4800702c4514842d6103842c00c0350146c00050040000807040c003c460b015862907541d505092410f071050502d0145160084404400700c0001c10201205110455007a5201541ca0000548407407003c10a1402804134007035000c0c0c1000000a80520302d4000303055680c1c010811038160680b1200150100c460030341c0e46500103a070000040c010f4a0194002d01d9400c2c040c2401c0341c1c540340c0c03008845205900613801240009408003614030030b0180c0301c40c0c140c01038010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 714714595 1250 714713345 714713347
    0x2040507051801230c01091203060608150d031b0602070c0e07032a021501060215010b041a1b12030a06090b0306070c150203190f09020d110d14070812 66
    0x1c0040d142204d03a03641c12100b040744000a0301750b92501081d003020140c0c990241c48060f8202401d2800f4002c0e24850040700d002607402c04c0000c1a40801d00900044c2003c05000034200d861251011189500d91040c00c44081840c1e003202000110b0904c010031000f4007410080c6a0f15045c04100310710084064048810103007000324440c140c1081001c1000fa18920f4042e1803c00700401c00107900f803440c01700c4221038525100c1c00008440b0f0700407440b580e42e0582640c0407401c0b80e03240c003a0032245024034010441080105c00c441c4540c004079900500720000c04090080c0c5800004601610340140c0031119451150080107100c1c2540c07040c001e4070007400d060441031004a44103008030790341340001803c0a0400c80d0b0416541d040c805943c00713803204d042214906640c0c0c0d2400c0810f007030f48074004410200e546407501d90355020984c00740c0b00f901c0101c1c2c1d000b00a441c0217103060311410054486040030951180f018980600007a586508d82e04290030440040c004040c40d09401900f88607101c03910301c2d000c2030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 714715845 1250 714714595 714714617
    0x180b030105060a15090824160507080a0905030105070c0203102d02040b04060c02010f3b06070b0a0f0c1205150a0308070b010f06090e1302040507051801 67
    0x2e58030f1a24800da80481514500395040c2a0084a034005280d2000c10a4003c00380e01e0581c10604c4030085400d0b01ba880100282600c4260203141021034443c80306001403014443e540000d41c41500802d6440201d00e05400f20540310030001c5d08503042511960b001ca6500442081142814440300e01c6a2203807000411144411601122801c0d8015201d00903031050441002c0303906c0a10350580e4080c011410440380c40d9901d41d80c01a00760f004400e000e9004c241000c0403250b08910894180d01400c3d04a40c3c5012004408030845c048543e02007002c081c1c0e400d26040c0040551186009800024080d079a51042401c1c0b1010041c1100c02e21510002c106003071518640b00103402582181d00b0303000c51800015030707a444a01c00c4083c0e10081a5103507100500340000030074070183e03401811200e40511500201a41c0e0707419004800c1d2541d01c42e00c400b00301c13031040c00c2114000034081145c2c0b051072090400550b5007103030b0015040710700403210440031401c08100c6c41ca001c840c0700001504e00c1c0007800c01030018a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 714717095 1250 714715845 714715849
    0x90c041104181d060103260901050d0f05070203130b0403021f030603050712021f0e060a0e1305090d0f0c0f140a051b15040b090118180b03010506 64
    0x481240103641911840d9207403510710282da64841607010010b000c2c0800401c00020845446040038442038980030000786403101c081c20808444141e9110204404d86000c400c000151045e41005013080c000f950b488004890040181c002c0f14850314141e8060340c2d07280b0703010043c5e079822840394200b169081014081400180c581d0a0124402c50f6a00c0981042c2c1100042c110080c0410380c10081c40350280840001d038a02d025101482c0c2e0328800c5136840c9968001141c00100a0a01d00c298000100049e0f00540141042c8000b424642484c0c0303031104111900c0c00c041703040107905442001c90507036a2405c0040300f1030284201001805145818814415200001000c00c006100003610005901c04000f0400421031503940003a041030381036401c03d8996007880d58940c40b101040c0b08030340828410a600a10382005c9030302242e010303103001e98100f03410100500080c3d081801c009050041440503901020002d04911008015211300031025007034481e004c005a40c007208111340203031304000c02d21481e9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 714718345 1250 714717095 714717097
    0x1e030204030812040219080109060b0915010e0d0816140304030c0504270b1503010e070b0a030b1c02030106051005190201020906071a010e0708011710020d05090c0411 73
    0x8200c1c03e0380c0340b010303240c0740000f800c003071108048000103840c40800090502e1041d044031142e43d0107082d041000300c103540103006884608840114581c1c03120070301150301c0e601540c00c4030707143d01e0301a19421203212107940b0810203072b01c0302d491201896041f03c035a500b000a440c82c043d1050480300c0c080d50500349143c0d10700d2807840303a601986106585400144001c50060032801111074042c80c4655101e422606010802c41c00a48100034010003803082031120342014043c2403003042c0031000505136030f8600f07165101d894004044940400d40c40b00b615809556800314910108903c1c1e94541e126105240304141c21a4265407000340117103800c0c1080441c95400c481521441280300c0100341c000e0400190407402407080031202940003501041003414004100c6010f500c8141001007440a40d032620034841100b4011a00e200c00185284010301030941c40d5818940c11045c0303a0221240b00096584074410b0742c0201c1d85a2480c51340e244200400c44004024000f005142501c040000c815803044243e0f00e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 714719595 1250 714718345 714718357
    0x3006030a08030106081e0a0b0906060f0a0e0612092410090903030b13020c01050a09050c120c0307170606011805010e210f210702040e0a050d1e0302040308 68
    0xe03c4400c50001c1c02030508083e1940c40220f501104000c0b601d0701f41d105100a240a08020b801160102d00007582400d008080301c12904484035050b0074848210340c221030200e041d00301c5076007100b028842001040c054145540c0525803800c058078030b2001404aa044030543c0c02c082c1e130a20345d000c10a01c40c55820405e0b8401c1500c880403404980001241800e03000f07010158007943c0c00509410000c401a613150b40600740507042c0000a000d6034540c5034044059030202030300545150400081e1060030b24200e0240034102400b042901c68640c6158006800d107555540041c950880b285880c102c015401d1000c698410000d0a05041030540810303031035000f520f14020103041c4141e140545d8026aa05100f901c1202c0c41c0c94070b160200500050f5184c0c403000032141507402c40c80b608200000ca80c645c454201c015481e5030f40001d08280b026020040030707118801e20212507001d2641c0c00c1d004501c0c140b140382c002c580961a400e03000594101d10141440c4a903400c0c9040500c10310090000800d0b2100302c1301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 714720845 1250 714719595 714719597
    0xd0b091009030f0e1f031a03030711061b01050a1b030515041d0105150907080c0f0904090f050a140307080f090312040603060f0b0306031c053006030a08030106 70
    0x1221030604030110b080f01081784120355404800b0300b11500d00e0355058100300506011030b104555002e0038942810365a001f1503000400c0b001c50b09450035280d00f40030010f04556102e072115803113010201781000d07084072002c0c0c81001c5403d07204c4403403000c25400601002d5424109241c108801d280980205c01c0381031580e81542d10443c0c42c1c1c40040340010381c40c1c02040400300c0300c20080145007080a4140400041910f01ca4002c020590008030360600070100a4460041100e82c1c92900c903201c690340c81d180e031241c0062035010340e42c1c04258001c9000b81c1d01d8940788604c40c2c0c000f800c9690050420303540080d41400f03c145a98010401000024000b000f40c40d0080c04036400a501d90000c98000f074100308035003103c50500e8101082c006001075050304054101d0301400310104003551580c808881510040310b1558141c0d0000c03800800c101c0c1d00510041101c81a4070740503007015145031071520840900c1c1040c2c1062080f0090361601c1420100d02140c1100c0220004e1180c6445a81c2e41c00c9280014841d00b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 714722095 1250 714720845 714720857
    0x603010303080a11091c020a06030c09090e0a0f0f05010f05060d060e01060b0a0503070f0207051005130b030a0204061106040506040308070203090a0b030f0601031125020d0b091009030f 81
    0x5010140d8050b07910410005003549400600d01002406c4000c2c011001c3e4802c040048000602c54000d00c25030442d00c007190b9600c1c00e624241510341d0050150130044410a00c196100c8802003410190804901485440000c035072500d0b50414509464503054054080e51402050011503a0742d01c44240d51260f21147c04550050700b009a50b0040005520884158400040d80081680e0000c0214418025525007104d942080101240e036003e0300e000e00c2d0b400540b0a41c1000029014401905690410440e140030b01c584803036640b1140d0b00107031082e91030943c021805000d00b980110100c035003500e03180000e0015190940354642d964401400103801d20880030045001e01d8421300c11100c41910150541c42d030b0a07584e2000c40307840d030f10450350134585940501c0410083d42c803d010b81c102d580c04244001382000b071915143c4240038402d007a1800b04220301096040140c0314012105480ca004440302041361405030315250405a010b4406600381d0725000c1c00328000f1b03400c82c0c414074030080589852 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 714723345 1250 714722095 714722111
    0x93b0705060a03051914040609061514040c020c090f040203150f07090501050c060a0510030524010e010b040902030c0d050a0b010e0111101a090907090b0603010303080a 74
    0x105041151540109070095000140c07801e40503090340000d80a040c45010207100200380a041c10704460700c0c84008900c03020054040b40c00706580350008405940284400580c601c02100180000b4180d40d11254003036001c1c0c9041e0a507031800c0d210744204420280080c0c80c2c103c14150003d4000d040042898140518244c00709042d92401c020f01c07104640e0f860b0b001c02080c20940407001d21808111074502c00241c2021000c11254070230403e40369607a1038100200270648035400f112010b07110041500c001001150b10000208030104168100910740340701d840d101c612945124964040705030000344030f05902d60010405036000300120360440300302c05001620380d100c80c000c424444c801c0310000840301c0c0c10130701806000c0000e54401c0f408100709032641a915404880150303152341104045c0c445680214100c80708815164000110310302440040704240c052100004800c3c04083d55039540b02c1c3d002d0a02032050456a02c20009280c02c1250760509543c0745a40040156000400e035080c920b46a02c10703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 714724595 1250 714723345 714723461
    0x30610030b030d09090c0516030c02150a05030f0601030b01052b020f09100201052a0702030d0908100207020f061303200103051303020601030f08071a0109 68
    0x1d1080355800405a03000d441070403000810070300e154007469038030905e800d10b0000080d00030302c1100c0b050301250003c107615800303684003564180742d4490f0030303a0410030703004414290800d0100200300480b81b07a180e0507120300342030714544540782000b803045062510b8800c00e8405a80c2020030340716040000c40380d48030102241445080c400c8510800024203500200c2e0100580c0d24403409040d0b0581c003941c1c6503503070704e00c4002304074282d41c01994800c91a00d088a00c1d854001c100740d05004025618240052402c4006c2d800310b45801c100f140c0c0344000035440e090502c85a0000d012140c08205c0ea0786096007000c1c00380e00040c0c5c42201c2d0310000b6100700d0000a9800300c059000d9030356801035400888441c008004941000443c9039803940d07090000703181000196280d01501410b010103501a801009940c1c21071b03945801c07070340d8400804d94001605004d110001484840319020764030f1407680301c0005500d00700c1a80c0540f0481d8103c42d40d6140004580c0012031500c40d191035034152502e000c080103039620030b2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 714725845 1250 714724595 714724601
    0x1110f031614240c0f0415080f252703030f08070f0809160b03011e03050d0503061f02150a0905121309020c07031103060907030201120605040c230f03061003 69
    0x35840584c61710204000505510030813107a03031892400e03110824580c0d0f4801000b05d6000e0100c03085d5814004c8030580482c181c1c0c00d1a0300c0d5428400d28201244808981e2906e02c00811242003043d6040d8001c0100303100301a405500d07080b842100d41803589070750815030b20140c1300b005051603100400428800082d0811810441c2800d415401002220041d845822101035540b090296940340c1c0c80a04031221802400900101101e80050148c03821168100d01192140c0c800751150b5030110064201514085411080d41030220041d002806d5509120000000c07240e001080e1022181c40c0c2590600468000b00c0e41522203200c0300c0b05180e80755200d4142c00d6012000340c100e800054804180304840300c80000e03001051724040c054400c2c0c4540c09404240c0d4500d42102c0019a036084100b0803c015405408031803000220700c640480c14a0315100410101c0707840310242c2d80021208502604800844101c505490b100040344600d4a814829681e40ca440701600c102e0103420311008203001d6601caa8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 714727095 1250 714725845 714725857
    0x6041112060c27060a02100516020c0d0204060314010207020a061106060d050712030e03070503011503080901090e04260a020d0c02061e04090b04091101110f031614240c 74
    0x4c00040d107822038000002e56a0000750495510b044c0341a001c2101ca0603c0101004040400e600034503102196000b0701c806104010000c0360816290300011001441454030b6607040c55601d400161604554010030101800c91390242081c81200d5500c1860618003159840c0d200805a684440851035494540d107040c00d0341e40404502c0d0302c890224020181c0c0050718115440046040742c00300f80e00d8000309800c0b60015403c00e09c2d2103403002c1c1c1c104005800340024001c00001410300c03c40c5990394103045024824121802c88000e400914064120360251035030401400c1f00d0f80102d0300341148444043c0d41c403020396000209121001d003e01045665050485070920209907841e1814002405884d405800074058203640742e04040c40e8180d1130a0600c03d8425094000302c0c1041107030b000400569a0b152002d0016a0741e0140a03903c2900c0741041000703010003007090f040041c1d58500d074201030401d44059982806103412021032032001500c046482c3c403056500c059609615140d2045c1c0446038800c013 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 714728345 1250 714727095 714727099
    0x1d010c0f1502181e01021519021201060f1d06070f1202060601020715080a020702040f060b0306120313150c060c0804020901090c1e0203040806041112060c27 69
    0x40098403d8011480000505429500e6074011034508a41126816140d154103005900031034030049000300c0901c1712a0040740300c105c0084005a0f82484506980c099480800c80d540c810f00100502036020b000c1640314106480e02902071081594154844441e045a40d445198041071400c2440b11100003410029407100004000e4020340c40e000e5201e104c00c48103640540540c541c000b6500d514070699824100e00c0350b075401d04a5486c100171700700075000880242e0304156182c465401c1d10302940709810240c034012102030384a141000421420114000303001e68250014007282a0411114620500380c92003440f40c1d10b807812126004852010001c000076101505142200031115080803016000390f000b40e41d04c280981c1c85c1c0c4031440c1501e10994414002400090740c50038034590000010388012800e02c192032130269124880d0345403000c2554280c2c0d100004d443c0c401707014509070030f2607502e070000b000c041d245610b0880c0052146000d9181c030000580300340c3d00702c4204070030544000c0c4d00d0350f080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 714729595 1250 714728345 714728347
    0xb03040c0b0a0224070e12102d1d01020a091406251112150702102c06040210030509011104060f081510260103121d010c0f1502 56
    0x120b282c044e4221415034441c004a030186509000b1801e001d010365403c941c03102c0051008007210202c0c00000d0001d07c1302c1c61484d441040420700404c0c520075001c0c0318900c4040f07000c070300b0320000c0345ca00c196150721b00d0703c0800c580c0c810451401299007020408080314911801c804c8102c2805010a40758031070140b1440c43d225880c0104072401c21455a04c0d20308902035100150301002250074080385a246603007040d190fa01807401c2c45883e068040c0480d5015005205449010ba4071001280550384144205145602c140089000c81c003124450719034800c4270300004003158101030700850b0b401161155100c00b01919000081c0003038000750020650096032112071a510b03941c03020010300d001071b00d40083d4001580003000c54282c50141d03640c414900001031021405980c11081a0352051803007010860421000383c04072891030407070348040e0080d400740401501c034282d01c4000820b440401000c56428450096100140381da109020515840e481178560b002003140d414045c3d50781c0b98819414100b0740c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 714730845 1250 714729595 714729643
    0x301060f0614040b0d0c020c13270327150509190e0117010b03160602060907080303160e03070f05040c020a05030d1d030406180b03040c0b0a02 63
    0x542100c03440032146650342e144001240101c00845603c964450481684820300c019250300034140d004160b240201d00403503094600d54400b1038841d1801030b0384410020342d5064030045124400c1c11051415201200c40c20564113603543c00380115040c001c00011014440045801441c0e41d0307401c002c0603114419050141a41d0300c0700003001640404a11070080031941291020700c1c0000c4095020b81d0500703512640140c9c00d10a82c00054140031100c2e034002c0d174031207501c106a51414801d41b2801100c0c0ba8468480c1d50504a020749440c2c0d0241585000394000034080160310008000d030b130340000c5c0440525000c21203501c0d00710b45070603402a14139818010308500017503042c00303881c01400700e51050b00e042c006142800d200366258015402c02900e160010894503514030300d20750004100f0075402c00d10209411104981c10300d1a0420380001011a05010822503e0b5000040600c0188a02980d0380e20390715155844c061200682c0c4600920f004010910b000a80e00030301070a81075580c500148100a4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 714732095 1250 714730845 714730859
    0x110616051c020c180a090c0b0405040507090e060f01050c0d0f14040f0e04140f0a1a060102030706090c050d05011b0302130b03040f02040903020307030f0e030d080603070302030106 79
    0x74040148114000440c0c05014400d9400031030600f000050040141800c415030021828071101c0c014140c0380010380d81d00b440f20002e04403580030700140145d602e1207529281410280812100090014003d000e0a1142008811000c03800d0940c48841501d190000c0b522040060782c407400703078004401c080e00031044c40c1c0d1555640700010034500c000c00c1da19002c10188004014905200f640941d1100800d580303414885614080c202c02e030030a109950782c482c0e0401a40065090010100f428800c5412010b2028180007451503511102040c200f4070003054203101c0e0010390740f4401c40c0c0c4010034007511450b41c40180048114518014100a00320182100c43c5150460003011070741a14030b5882c1400841029080c8280300355070802e2088179100c44890f08020303806541341c00c0103200712204460120a94016222030040002d203c0c400d0300195222200b62070085c2459003a02c0b0003a082245140c80d0400c140d500003140710b200442810300c0070325a03e440c00468240300c40394102a42560070200001184 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 714733345 1250 714732095 714732103
    0xe0c090103030e010906050c070e040804050d0b0a0608030301060905040c0309021f030e1501291b010e2d0a1205071209080c06030a0f15140607020d11061605 69
    0x30030f002d07690b039888030ba16010241c955004244543d101e980c40f4010030310003103040d4608107800501902d110f03800d00740e48a00281062500040813034039500e1b90000c0c804010800e00401c4044c3c404500590304540c1880f50043c0904241c1c8145880b031600c0f544c040c0000707802640500b1303017aa0043c081c071886094000564400040a804020000303113070000107004603e0201d040c1c500e100b02c54005600903440c04030074030b82868903100540e040c00d940c02c001600f40013541c0f000b0b00c80c400030402d4074a02c541c4181c9040703085a1034111902c16035007100442401a0740b00072248a0726004004070440d54249140d2020715141035840006d2200c900c0d04401c14040e030f0080060120307544151941a190011104d00302c1c0c3c0c8250ba032103540300551021500103228500380f400b80d075020241540001e52419143d03450001c0e82c5942e45001c00c1845401400d003c6420003070290515020161001446c1080b40e5010039164500750101034294240300940c1c28075035489400703e03070400e0841c2c25090000342039401c5c4a510303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 714734595 1250 714733345 714733367
    0x1080c090d0b24100c080d0509071d070c08130506030c070b0105150d0504031e1707090509040204020c03040e070e040510230102010209030d0806101704060e0c09010303 74
    0x180d0200b108410080790001c405000d03000781c002e007030302c8100c22140e50140c1c1c07045c0c203401003291840414070460000001510502d44a40e440c1401004420b2408240b2400c0b0580002401905a03800b4108004a41c008100011442d4449980b540d14108980c0700c101444070b0340c00256200000205100000c0941c0e0007801403507010f03040c541c1d2140d0b40d40f0300f00034001208103d04032040c041884503000c3d951040d41700b0b59000b4080d090a0141c403862002c804151920411183c01007070782444190200e50000806a40c03284640c14081401c500b028009a151b65008100912440d00003031200300942003441650002d00c01b900c10465141004040940006001400e20b8016840c0c40c0001b480b20101c890088101c5900c10b20244075644103245020714186494401415507408000b005140c1c2c83c200f0014065840d1a50361038103500b8640704000322501c0b80a5000c3c100030080703184514800c0751080c42508a50720681c00542c0d0b03030209111504103600f03000000c0d408400c1c080004185a000003948407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 714735845 1250 714734595 714734611
    0xf0c02010f0b100f0809011808121005010917100c050408160b19031b090608011e0519230102011808040504090c030206030c1c061401080c090d0b 64
    0x602a002400f2650310905400800101d400424104180c054a822074001c0003800c0041100c1e400002e00d21806420403800704d40145001403118015107048141d550000003141a065441d031502d03000030100885401510141061010040f031400300030071505d090781c500310900f40302203400e11002802075000340c4203a1443e801125050f0610182c52411201901e00c854040b50824440302012200800712500d60014990766130864000030854244541c01d504641d607a01d0001130a04000400340e1006030700c00100701050164030701241550200d0401030342d83c181e680e001c00203e134207650017914000342d01188511080f1031503000b181020302d80d005600d200a80091000c0c010100e610122044103507405002c41d5010701051259150a41051303804500900e81d503007009444e500003401c40d40c4252400d200082c400100344160141003841200e4a40040108220080c81c2080c460000c42c051004281082040800111056000d4090320200300c03020f0040716243d0b52038a4800064107055076049 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 714737095 1250 714735845 714735851
    0xb0d021c091505190b04140109050a0c0908070e040515010b071421030711060f070e060f0409051b0a0c151e181e11010801060509130f0c02010f 63
    0x100c80700b85180512806040d060401d560710000000a44c2c1c01084041142d60f841919403849990650883d42858080c000c030302000a51420180030690071200c10f5120380050140001c405c002d40800414408100c0c0c03000940000140e88629060b81481019104050345050100c00071500c090980c1c003505201d440b41541403610f414007241c265541210915100d44580c801880000c0b102c1880060740d000a40c50501c4000503160001309801c0410451702d420500c2980310800502c5070380140ba01c10140e0342598410f15119501984c4001442a401404031560301c03003000c2000800f00c0c2e6640100080208041e1782c40310507259009105031001e00080e034880c1e1903645441c9000b103591140403040201c8800038031094042100c2117001d09a4000d641c40f2040b800803072031020500e40240f200e4140c0d5008200c081e068603d00e8214100b01030409014108640321005206090700001190f8407054115001d0079644c12040c0213a000d04002c14200c41420b042a4002508540542002801400703591040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 714738345 1250 714737095 714737123
    0xe100f022109190f060c050d050703020613170d0c0e01030c0203300915091204030b060a09020f090102010e0111070209070e040203100501030b03160b0d021c09 70
    0xc48108007404121541c8000200981c030010b01d4225101c2248030110b0b00c1c1000d03515960003003c80f4104441c1c1c8550085660f032607030881000818040d201e040805800e0580c1000801c0e180203546001c010200c100030580c0c503003204c0511403641698207a00b1001d1900d50341d200d0800b441c401c003402c00c4082004c0400d0751240d0718406580240103800c0700003415401142040c0c08181c500d09101c0c1581004211600c5400103030800102c00c030782c85403150301c1d000010070604c1840440c40801000051041c0e1594000300c55803c1000404e004907412640c0042c2e80841c99180d10340081c450400075071090122501c00105008101c054102508411100760002c000141d10b007006203084c1d40a0030440c0e0640401044110018a820080150040d10700c1c0b40c126600200c40c808101203a1055a0451605454240400031740da070500502d8211001034003c3c00000700c05c4640900d04480f9406032903541400410640d50707010030340d4161207401c40302088444507081c6080740d05000b011030f071006503901c3c0d84490107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 714739595 1250 714738345 714738373
    0x10c08010506030703091b080703151a0f13050403030c02150f0106030c1b05010b0a06051216030b030610050a06021b0d060f09050c0f0409021f0e100f02 67
    0x21904031400034019510356500c00310304400404038401c04076910811031000c01e01c2401c01425420240c060040240b0845095080480c0e03203101a10709292500d04100351080311000a071250140e01c40c0179510341061140c22000038084015441425616624003400c00051540c103820107841e040590302520000d110400000d03448a0085a02c000b104503501e00400006119a1051401040302c0c40c00f043c0081d15500400840100c0441c16101607460f06207003400e900d0304141180c0104038601700f2500c2c1c800b40c1481114103040c002c00b40e00c40a0440302d2045251406900030266020b07000b01038900502d82401032880c10a507074025030f4002c8002280101e0403500008280001601e440545030301c151200003041054160324074115140c60319551818050b5100703008000d0f01d940f09001400c1200e110400b800310712503070060424401c6042044110240e15036082001005550344048a02d002c880d5105440d41040640b010750031202c100261642654016810010b4040d15420b44540c030015801c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 714740845 1250 714739595 714739607
    0x8180f0604060c0f02010903020d05150c09102a06050a0c020111192102270a030b180d0203040e0f0106080c070c08030a2d02070e090a0b04030f02010c 66
    0xc400c04621400d080a004c280381c0c01c040d0011364030515048103400e0703d99000c9500700c00002402c84056209815008650051125240c4d024207440010382c182440c41000400c40c04c0c03a55640d400380038480c21015001d42011070744098051400407110300c030080354a01000180b00480b0354202540c900603030319840c00d1042c01001c1d0b2056142c0501814440c840c4080c80b05840c07407407c1c8106001c00d48200da0030541d0f4202003241241080f1200507160380e4005040001140c41050354a100307405038880c04142d54400c003641c0152500400021500c0e07654124510f642e1811010150076480b45500300319215500000900940c1c03049880340e41240c940d100c850340400804e014110100798110006045516224042c00006000d40741c04139070395039604803003820341e13201241010001d505104103080d003180c0d051101309000c10203120945510070061b0001c0d107866550062103529a1800c0116280c80c2c400c110030580d0f03070b8001c84058210b0420b03240c05486804485201009942445030242941f80910 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 714742095 1250 714740845 714740849
    0xb07020f040c08160c051b18010f06120b030708280b0705032707050a060c080d020a02160801060306110724021e04030501061a0a050d0908180f0604 65
    0x92203d1901e600c6025000040c07801503041c210400c69418407550108104102c0c182e0050001c1e80340240082c4540244040c2417055140440804000801040000a4004004210748851920b26261210b140905001c3c0500300e981c1c99251141c800d010515104c0882c03200451004855464001100c10303024000d1a0309100020b03000100441c009003040c0e00035801180e12007a1103290b4580380082d070500051844d0800d810350629440740000f4805400e2590001d0f02402031030908982580b540d035595903c511400000d41c00300d98000c5041001d6034003c1001540400c0c01c14210707a10503440d6003d00c0c0c000e0080d07110075156075060103880012185414122000c05400440070f80b070a494812201c0e2883c140d608140c01000c0d401c01c00c200007201c1004004001203c080320301683c03545035052940c01d42e000e503002001c454458010078902c03002c40e2421540e405400d4209113483e4100005003000420394168041c0401030001264040310403e09240510018102d540c05132000340c51007440064007a84c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 714743345 1250 714742095 714742097
    0x1020307080f10062f011406012a0f0b0708090123150604081002183109120503240a0303030b040216080c0706020109110603090106050a0b07020f040c 66
    0x840b5062100381d2148190792409002e10800c039031216a016020041400601240000d503550b0381f84a40a013528009455000842443c0c0007407442e0b41615010341b9015001c07d410907c0401e51100010801c044e1009150ba030703000038102105141c502da01a0605208484406880d440c3c0391982c1c001404600c628244180c03030205441c06595801810710410000c9055280e020744c05000004058408102545c00a4044c007405619900b021619811841412140740e200d07079950460130200600d03500044a9070118500390281100d08010400010030120390058020344010040e50354490f08080114080c103c2e1a0341d907000750000402540c01038600000701540641242820800700b4132075004580b64400041006282120340e000210800b410301c1c6040762070800c08a0b102a03003070b50600c0b000008011900083c00340307051550f50309501e0110aa600c034450b07000440401c034261070950010f03001d0718010f007022440680321178075400035420601040b0300ca80b0714240108141e0801c2c0c080e1220500f12 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 714744595 1250 714743345 714743371
    0x17040b0301031103071a04031109010e04150b060a0c15050705090f0a12030c0209150a030b0c0d0c02060603160e1b120103060204183b070801020307080f 67
    0x856491100c2d05609003d425810712990001040f00c900c0d056600803007000c10001d881d95607146107001041c1c0180d2100561044c40c0b0321004000b03400c921200f15030f12551160f02ca4400d03955500c0d0140c02041c0c00c40d1515009500400d0b040d004981040c6c5807040e0341d024491414014107803100c400d003a254121744040001c0d0082c0200903260811480848001e103000341060b0720b203620b1301101c500142101c003041c0c0000c1c281c0b055140544c1800c20001c0e4114240740c2c25002c00c1c40c0d040002c2100c004242c0f000070b0440c00c03181c000a203042201811b031810040d0703c203404d00c203c110400000755501400c4d02c169220b4080c000000d0719420a40da40c51044450b00710302d001c1155542481c40441c01d05002040a80034402c200070081c40402a078150b0180d8411a8010707121800d000b280242c198002c2410b091881c6411102125030600c0ca01036654000c84102811102006100004510326030340054542442080d0f000b01d803404045d00a5031081d0180e640c0c10b01140d660078004c4071021030075540d01c0d0b80204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 714745845 1250 714744595 714744599
    0x16030c1a03060a1e0305030c0606010f0c0812070c050d0c060b24210106050301060e010302030114090402060d020c100b0108250203090901090c020105070201021318060509100317040b0301 82
    0x200411403040e0850242500c54600c4c0d60703d440f02ca04550080d020b00d41d00d038100e0b5003044265a042186030385004c00c00d28021126124555800c100c0b07200d000c140420400e4080c000070b055920540c50030400c540d100050742c0c0705181d82c01c005000301890140440d5503606061100205007841300a0750091a80c909041030140035000e0b4100c020b912038000c04a0426102804214411020b00454000d04141d502c035983c0b980342140080080508803809030416004100420011601070440c01841c0002c480c5555a5182c03440000c070f2a210310140141058000b1401c44000040424600b0b82400c0072001484904205401100c04440031204403040c540068080d00c5a9107079208070109984050040b00e20f031034800c40c0001c0e643e44090b030025100e0394848400a401e01d50a000d07690704084580001c1d0b08043d0450000781c09100c2c58021450310020311320301d11103c10b0781504018002c10000d00345c1010350a00076004160444140825954240e00712110f04019103000100c2d4215401401380320b045074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 714747095 1250 714745845 714745859
    0x30c09060616060e01180b070206010f0b362103120405010f18210503070302130315020301261902030115080102041e12020409020316030c1a03060a 65
    0x2e000c084054903050b41d21880c07611040400d1051540c0002e107020700c41c045242c0f91900c0e80d08104000c1c0030b80d045420400c0100252485103601405803145860403503194180c102400940040846602ca41c0c0004401e4213030b060022804000c14805040c0d81c46040a400d42d180c9181d82c13107003070742c40d014103900400c220400c2800c0543c0c0d05810a10403c0045206080c11124000f9510400302d038001c3d11041c20108010003454050402600441d0011400c4c0050400c80c058030f180030080c801018150001903100c00780510749200d07409198442800c08200d80c14115150094009000340b43c4964035603484c81121115051010002d0340d04000144585000941d02581004001100b2a0159210641000f09044c0000404064103d2000060700d4914000e21400d00c00964000c54550350920381c810f01117142804500703c07032280c050320301081c003040c0c07072020a1800b41c802c0c40a408568401e4000300401202c0114901204d240355462510801c40303152480461205844556100f01c1e071036001c0102c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 714748201 1106 714747095 714747127
    0x1050105040b0906100f050705011e0617060408280f0e0409030c0206180303030a0209011701120609020a0b120f0f01080d0e19030b06030c090606 64
    0x1818224081076204205940e45c0080089030030b020078078240680100c81c4081d6029008003c4140c4404100342c211525040e8241c0e0309003801320008400c0300c086101c20515031031001525180e1215030ba140d00315070120390f400300c010b220409200b81c00030304144074000c462402c1d01d440c1d000d03c40c000390042844801d601c0e8107110f6440c024441c0c0110313900c203848036180742e4141c80040d0386181d00581e0102d07000c1d140c0321150780351000004110400f58642c01030a03500340c003032300e4501c1512080d00101c80581d01c01d01034151203085c4040300c080801d040750803801b030050010b0403007200d0036102c81034000c0c0c55100001c0007005121001c140076000703103c1001540e209140807840710f400c4d41003c2c8900d40701d5034044801c0d0100302d40b00c18820755541d5407180030100200c404001c90705007a40c0340741108410f401126654428020440c5071100c2d41400c1c0c10715441208000c00d414648190600c2070880 = true := by decide +kernel

theorem cover : BRFrame.Cov 714568345 714748201 := by
  have h0 := BRFrame.cov_init 714568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 714568345 ≤ n) (h2 : n < 714748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
