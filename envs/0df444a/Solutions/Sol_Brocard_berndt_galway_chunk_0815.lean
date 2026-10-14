-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0815
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:57:20.943428+00:00
-- url     : https://prove2.me/submissions/f283a633-80c1-4b46-a303-126b00716bb7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 146402877 ≤ n < 146582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 146404127 1250 146402877 146402891
    0x7171501060f051207120605061e160b01180f05060609060a03060f170c04020c030a2102070c06200c01030b06070c09020703020609030a080606031911180103050f0406 73
    0xe841441120b030400046141301d460790400103002080603a400035072a094520382400410549000e408444c882981c48102c0e441070089450210310039448001c00c041701d01c103616810300001c0c1d018900e450003400d04501412100b030000c4202001d407041c0c0201c4800192a003c00c000300d5980d060103903030070b402c02070310055100d0110200650003014590000c01c5e65552102000079100081031010f1900141c1406031b5005406400c28070059004102d982902600140b00d4000101c3c45281201c1d244030268120380010381c03440700d03848100c0c1e10940e0242ca0401541000b0f01c40d0a82161800301500c030b403682000c20302c000f07548107503484502401c40360b8109a200c2e02215416902d620641e11803035001005100459a98070b40c6000a501614088016009a200203944949c01001f501c506513100d855000c03850f510402008115070000701103090094084403d4440144e45100e00c2e5000b805d940c50060ba60400e02aa0441c50038804031210704041c1442e04000e49114201890744d0485d40c0080302081c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 146405377 1250 146404127 146404157
    0x3091a070e090a0c031808070204050606040e09070f060e0306011802041e060201110c060a0207020103110c0105010f0f060e0607051203070503100e0403020c0f011b050717150106 78
    0x800410800d03409082c0e00c0c18042d6850781503208006102035500c08005042851803003414500e0212130140035040144000000f60030150015584180c001700818a001c0d12050b81000e5102c00355406080d0340c0c4005010700405410290060282080b820250706000360840025034501e41400b660410302070300680380000e220550103480141c40d083e07403c00c18150604040032424496441240010b42c00c01c1d10703000e0324200400464595201e0500540119540c02003400f005e5840b0000490402d582e5036003020364980101d014083c07941d252000810030b0b514101124103114015009040d901c0c004035001c002854200b002c8030700381d003000d071046a21050135017401c03802d1055030721010070400c40020421010302d134054011881485825401d07802d04d6251107101e58200780441d130050140c1e02064a40a403803901c20300004024105150041140d00031700c2d0030760345c0c08500300b00440c0d403036201010501c556940140c4229500c441000107120860400c09010150364061041d0824400041d1801c407403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 146406627 1250 146405377 146405387
    0x1110106121a13030203040e1f1203110105070509040509120703020d030e03070f0809040608190506160c030503092505130c0503070e030304050307140a0603091a07 72
    0x80000140c1824640340ca0700303003204112410290b090021081c4000500c81022100d80d032240c040e00b69000710f00340790404560b0a10303800041d0841e5a000255034102d1840300c1191382c0c0c0300c0a40300c0380c0b0311082481428038000c0c14070301c3c420f801038010380d050004001b040790340b020a6a8100c002140c001ca03443d04e5091119007030181098150f80000c0e80080e50340281900083d100740b42a5482e41c00704080e02c01c035800701e40c903070040400c0142034041140d00000410442e001521142d40c004000282c1c1903500ca00c810314048844074524035009040b0320140c14000103000540d0f1041d461300b020020004003590041c00c2e000d0414006060084c0400402d801107c1003110b03a02000e0103140c0c41c1c5e61540b40303540440243c00b00703100b018401c518800001000c40194003450b40100300988840d82141c4685509840409881c25240d40502c414800002c1e04da4040100000800d1040920454020048140645031480d230f00084281814107509500164010300c07926182041c150140465407a007074401ca0b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 146407877 1250 146406627 146406629
    0x131104050a0203010f1205120a020102090409051b011403070309080f0307020619021306030e0111030109050402120703080a0c02060412050607030515010e101106040323030103080901110106 83
    0x181052820041000d4440303a50b00860580d908401004c110076560042e0b00e03413000856000420307542005040603990341551019122416403400090308000d00b10010404030b9158041c155010f5201441140a0080f5252992404982882e00950300780d41c01c00e58210900c0003070820781c00c1550b50300c001c1c0c1c184940c081c10382d44100001d0040369034a00300684000c0d0748a1080c0c901035a40e8001c28180c122160191084403010100720300a4802d90f17213041d0003038008240400f1004040c0d502c070218903400c216080010342c040c1c01d01c1040020b0724286801804001c05e03904426040682c020081800416110701c150341451070301380340040c2c4114451000c2200381c041caa00194203105460010000c20001003000351140e48075941c20040c999440c00940038841003030036080e0224051028003581411300203d041034003010303800c02e000f00920100c45507141c000c04036401c1d40004e0380c03940ea5940e80c100c0d50000c080d00e0040c0c48916411541580c032116014403808076114103001030900348a21b224000c0d00110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 146409127 1250 146407877 146407879
    0xa0f0201020313080625020a0b1801020a0809100e030f0307090b03090f010f1a240316090803030705090603130c080c0405010503060f0106050a050c191e03081311 71
    0x1d0019941c404400781c2d1950250380b018002c0d11b0703040f59241d00c50a1004024150000c0d64000c00c0001c04548403550360010192074003080316a00c082c5c502a115013400140040c2842c0d1703690b0a0341d803411203501820301c0702c5030002007043c60602c08003402c03010000041d91a0102400301d016607c3e00c0341c031425100c91040b98010311401501200b080380c0d940000c40d804c080407110030001d110700441803100804031010414040e120303003e4007414040600f0b0038140c03030a1034840900107442481042d10641e500c2d82044480c8201e0b0480300f900b4890840d4480309060081150784002c5085080c015406000c1d17014a5000c04c3c002c44010000034801c030181000080d00c039420154046806071900e907420345600030324696030b0245d40ac180c000102410006000d910500c0e40c1c0c00c7d000d24076403d14034116440c0c0d0004031440c042020920213800c1016062003499045004442356545a00c910320382490004c07130781a01c0c026080c903104205001300780c0210005611042500c20150348602d645041242d0840c240318076 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 146410377 1250 146409127 146409157
    0x7080f0a020d0f0b01080a050c03070c080f071b06080114040504050307121d09040206090121140712020c0604020f03012c0c0d05151003050a0b01031b0501020a0f02010203 75
    0x510f84541607031101c601d020081e0380340d000c070740c0d642c180e01800c0c0e45094074512000315003000000c80d028452840001881d200e140100e00c1c06104010710840ca070420b150030b80301c12060000000901c032604000d10020050780c01d0518039980340c110b143c0042c2e84104482e501442d0ac8000007000c12409004489520b81e00c04201d080020071524000c1c0900f4010400704060340445081c2c0c9864600040094800d5a0041c03249184c0f20003007004643e0a540e6a01080201001058010052106005001c1301401ca00480d035101d00d0244401003007006c0684035402032602c10400510f0000001c0740741c992264041c0e5040142c0031020340480d00410315502c05020307480300305080342544502e148014500c2c004550440383e04082c8102000840c81c20034a00514039805001c4000d800311705170940a41c044e000c940c0000083c0d50f01d85a2a0030079182c100701f10307503444c035400060003000548030400040000706225001150306150001c1d5403804541c8020b0220404840c0e240c0441e803003042110751640d0000d000b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 146411627 1250 146410377 146410391
    0x609030905191a0909160311180319050a02010e130f0204050f0316140a0302090103030206040b0108010c09120602090d03050c0c010302090d020d020a0503010c111507080f0a020d 78
    0x325080c81070b240282110703032144103454507008072440251083c60800900c10016030b00c0d0190461000600b1501d4401417603101e04c20924685500000340440400030070240070f040352900205401c000b00b000c03c1ca003c0030a044a28800300e035002849001c89a420b007486001d000405001444034811940d5101c100d60601c4484410380920f034000d8800c03a00191410314440601c1420151070f54001c0c000215002070500c0d08110344041c808a810541402130980800e0319120340105020106c01d0708141c02680c4403105010810125020880c0145500e0008000492259400404010f01849a10702c1000150104010310089504441401c03000400718070841d000e600d0047d15541184e0403145035030040303c41c070010720b50003070080301d81400c4001c00c40c40c6100450350170040702c008500390070780c0c11611311000407400e5102480345090608194075035440000160441600d4511440200f03c10b07403c2100c01d120b8456003110080360042101400c4c146a41c1c0c070088060000e0095031075000210b418071030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 146412877 1250 146411627 146411659
    0x412030309060e010e100212071b05030d020a120c09050d0312050718080106350d030203060f01020c090f1b070c0e0906040f030806030703080705010501051c0f0609030905 75
    0x2129800b05d41c0c040041c0c800c0880c400c01c3c6841240540040c80c400070304a00001503846d4450207008444142214490f014601c181c0c46807450340d040343c008429001d03800a004001c03032b50400d5102c0c000104004050003400d081d0700300108542030920840b4000c0c805644888201070103107a03807208802250708100020b15110030004c00032401d542682d10705000712130380071a00d4001030240c0070944003a0960610941d0080c403c1918122203140400441c5424080040007600144040605501d42da500940c6070b003050800c0042405009010605544c4800002681c0c1e450701c10805601000303000070110141d450382030300c18000038001044845102c0c0000d288042020b030b14042c0058849880c104140c40e900c91120b29900d034000d07600030b031940769600300210000748107029850384290050180d61815540c0e0391030401c1070f007141c001150342c3d945540041c0038900b0b014030070440d04101351044d084030b4001d90300da600c0076001100002e402151602518400c0c5070107910044d00034000923214040c641030141e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 146414127 1250 146412877 146412881
    0x302131a0306090601020f06012c070c0303060801060e04020d050304030f05060421052b0603030c0b0a060302011403100512010f050601020f120306030f010c1805090c0412030309060e01 81
    0xb103038148100b4900c0c0109003075510001e40e990300311141100400071642440c20304043e0b03070100300c1c0e518143c03070890103140800d000c00ca9142e0701600340d03600c40040c40718040c60060165505a045101640e00d400382c1001450710115070140c1254040d80c2c7d42030007411609001c0d0440c03103035400103001c0f00c0310705040000f0003800082986c440e03401006080b400001c09002d10480540e2040b518000032001d101c0414000052034891781500800b00420718031004541102094604030741c01030300450000840d2201340701c2100c40761603001d0070b4044100002c03410360307002a0020014002e402c051010100c005500b16180700054000b030a00242100c4806055a21030340c080e000c1900419140c0f0b0500300403840c95400068080a0a440c01004c0c04a445402e40c2c0924030f600000c21069140c4686d45003030b0b030380f03440030320480401010a903611030280c02080c03140b2a940003241c1c405409980d80c0e90400c11034074110810317103054800c19900700881c10005c2c10210003030202d04001410f82450103000f12082d40c415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 146415377 1250 146414127 146414131
    0x11d09130c0902090f131401081006080102040e1902071e060f1b050702041104030606081c0c06020702030c120c040b09130f0f06050109140105120d0302131a03 70
    0x1404096040c58503100c203030090b0300a00e01155044680c405140f00c562411010701da800e1b00303008a0004810104200303a0586820a9101130403981000054810015550042201030510780009529203032411020b030341000d60050100200140300e050302080b0706441d0301291703440c94100d4003210030030b9021041c80f00320300e2104008480b0f0f02c3c43d00312102490781407409150020700400058000300552640280c0d0039500041040364000d5407100b2213111170600303001520145024803800a4443e050400040c90102e2403c4180f80c0c0200b4243da0104555201c62500c281c1a407000000d62500c2651010a103132030703900c0c10401d40c02080d156840c440060005101d00d66004102d4041c400300040009201850b00c00b039841842010b4079114080100f8030b645100c2003618801c20080100a6890f1039007021180c0070b800220065403907605542412040c11781c494050b1004484088030b910f0300000c040d0341c6142c1515007005040d00840c50811400482203010b00604000f2806d1980f0718042c14528010b82c42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 146416627 1250 146415377 146415383
    0x209010906030c0206070302160503030112050d1404150509060c0c0306070302070f41060601050c03031b04050d03020604051603020907030905010f18030807050a020309011d0913 78
    0x800440090070612901400d030712103005401621881d1592201100070391300403c41440b40e1440d4516090004004200450080c601e403a00408105d185140c2139007041f01d00c0c01002c080003892088a13201d11014030440d03085407081d10401029424440003a64103010720500d007940700d40c1c042030f202d000300c9001c90003031281c40d0118203485091b601e00344150b08074010042c025116003507030040e5900013100c90641081034001c682040490780c0c21000799114010b0b43c050060300c2c0d40240b1030301040e51042081b88a4100c142424942c0c1455000307103a103540c0b808001c20030450101c0340d801c003510030514002120041c1c41d0140080d251481c543c01c01a50f1084190780464441c447c91002d028544a002007075800d03a64002d2001c40581c888007000c40103000618410b031840e541c1c41302e40c1d80b1200c1e894414600200c0c1480341410041c01c00e03040240840380d000344a481401410021221030641c04421154844c1c001d0900124420558400c9400004070303101a40d0851030040520054039000310210340001c1c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 146417877 1250 146416627 146416637
    0x50c09061204031e26010b0a03020d20040f080304060e09060d1b0f0905060d152d0c02060c0412030509030d08010e090a0c0b0706090f06050702010c0e18091c03020901 73
    0x21004085c0001800d00c1142d009030303418024100118030075002003104034203511000c5800500c0303d080c8420040814001c40c2d84000000e020801e003060b0070101801098440055410103180c801d0203044010758082183c407404411000489076502d0b4400080b25036006154a42d41c0251405854241c600c0380c024100103a444290000d803004080c0501c40c0300e0070018290440752806540c0d0003882e600798803180d218064891041102c1901ca0340200d4001d5a0b003c8294407034125403143d4642210004c42c0010111341009d02081440c80490707048904075110b800c41000000406d0604440a00900105640c1401081115484568820f0070541604c142d01101405600d43c0001184c2e00c8400c90341c01800a50031040c00c00c0141c00303010141c0300b018020303600821002400d6031908180344e074a0b94108c9907160b90b02c2c00d01c0b56082c2d091154412203d41410b006408680ba0030000c0c040d03426400c41401004402400525510000c1c0007045000e200e0b008414507651071500041d020350015030031b00303000407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 146419127 1250 146417877 146417927
    0x50a120e031c0804050f060c250c0311040e0303090a0b100e070806130914100905071401020c0303040f031a010b0a0309030e03030703020c04050c09061204031e 70
    0x2241c0880c01d42204607410345a040a151010402d80700c481c03004005468070700404403220319045040c4071541c45494504a415500c811440040e03000d1001ca9003035100d5032074000749503c0000d000403075450940350010740c07121209840c03100040c0900200f103000f003101c0c000403061017500c4d00002003190381d0301d21403002c2100c556100c0600c0d5450714104d2280b01c107105003641c049a41f150141c000585c101d030303014020002011004048400796810305800321604841e640400c0030348007040c06503803000c21101500380305d41003a40d250340765106040d006032101441d200c40010314580c0200001c05085c030014003a070351501d41c4c50180031000c90807407209075211620786c0085c3c60302c28400f4014030705a440f100e12050401107580000c9000b0a04400b003142886514204d0b20346665040001d400e01a10990045c07608080403414002580c501601c15140103d0500441600b81c0d140000e6038000c030300340c0c0c0a26032030b50780d1410b080354244450b41e20090450360303101c440c00000b03a100c100e09100c0d014004000580c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 146420377 1250 146419127 146419129
    0x30a05010603021e0a0207171b03011e0e03370302090901090504030e030708030c2a100306090c050c01051806061003061701060501020f0102120601030e0307050a120e 73
    0x44d110b1100c030045000040c5107080805820b4070040c124030031031841221042a12007180240e040036400688142d9440306500c0301810750806000e05441c54264000d00060710411510b4010441110050030a152280d141e105030304010020f903424040d903495020407044920b1f13800625035410341800304555003a4588104103e01174005c4580618014000200607881e0615502c010000540100e0401055601c44140ea0703404101010143c00084080c50340c0d400345800145c81c000500c01c4074010f0144c8004031300341c045010280c04440700d10a0f10180010b07400b2007000c900400c04e54201564882c07070b001c3d00307001c4c0d1036201014096416103a0020882d586554070280121030b4882d02c4824142c1c002d13000202c680c1040d650407070007000603040104d18181c8030903941c0c000d9211004403003c2d9a41d103400070040c0d50b80c10003e0003035181154000714a0718401c8848940c40c0b10340241200d05140c0c403043c005019500800450b200182c212017603444507151703454820042c01451028100240480400c0301003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 146421627 1250 146420377 146420381
    0x25050709020325050d090b0a06050f060409050903040803070b01260606061e0403050a05060606031b030c0403050a0b07180e0f1503060903030109050a02040509040f0602041a030a05010603 82
    0x541d09011000a0300b6561441c50f80c0c0190240824004014050102c4c8600c40107038010b08402c244581480c0c0d00f10326040590200311000c0707038001c9106d10100d544581032921a40e08480559942e210080380b0342c0c2e101d00f605455407155034005a06480001203000c103201c03900c060305041c3e8134950580b10070f4410002074803200c203015020145468124801091045ca00580181a00036505011a0020941d4a5980829040341d4804c1c0c4140d00b040a000c000c0040521445503c40c00842d1114254100440c0e450381c950394100c4000140703c400800b03d443d180a4105403801154071104944000c031251400b510714072030540303501c030119090020a25241488902d20415100492464210781c0e698400f0581003d40160602c1070200702c0c103400800e87c0d141401300e20304c0781e01500d00440d501d5250600c3e403411550300500b81480f083c0305000c02c1c0000d90b100700d409900560802e88902082e2010b05001d0000e10490303204421003a407a141000d29600c11340701442c072494000b0400c009984e41c82c141681 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 146422877 1250 146421627 146421631
    0xe060f0d091104090f0c0e040b151804051005070e06091e0909030a0806010801030c151710030c0e06031513050607030b03100b01020d050a020102250507090203 70
    0x5199014040041203500941c0300301030581c081c840c0e0360041c401c5507011030100e50415006071800310b040e1154106011485144a004021449500c0c895103803d84484424034000381c1a20704130b00c0d41d089042c0031543c0d040840d610704000001c00f60341c40d040900d001642d84140311118003080d230604000610f0140560881307504d500015042d6850032034010304104400d485002005050300e007002005850383c03280b40480d8840ea018000444e52502c00f031034041c02c1040000c10550400156000510006144014000460381741030140b1450040b00315040c1c0303010702e41c00c4000d1078072003c05080252941c640c3c1c1c0b10344112030003250381c010ba2948898249500310403c890840d015844000f02131081c5112130078003907003c5491281c15020f881103940d100e0412600352049400203444040807000e80c94140081920b180d00907008009080034080040d44401d04040c0c400c1c140440401c04040260003034044800c0f0b15200140841c010302007142402c4e006c9101001647c45126a69010400b544a40b00b124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 146424127 1250 146422877 146422897
    0x30c061b0f0206040b2a07080405032503031b150507091d01062f0c04060504150323011508070e100510030609090b0906090309060d1508060a020a0e06 66
    0xc40b6036950300d0b902c143c1340d503002441a0b0b0070038401100c046402e0441b014203c020311030b18200307a40702e1502080618114007202d800002c0d848410300c0455418617400600704032981828480c443e80760390313411400e0048003820080c2100b4000700c1d1b1310690955a80c045c030310505035500d031403c1c01c0d5102c0310b4141c601030f210801c0c007195180c158010310000e4050156400d001c031924295000c2505407080c5c84032010f03003041f1828825805a00000c0c0c0318501401144050321090b02d0410a07840b00b00040c540f000d01d544405040c00e47d008451943c0c040e1100f5840340c0041083d002405208802490300e002040580719131409801118004100c6140c0e0b6a01103000e120344491088080f030804080101d1819225950000e055a6000000c1e100c8164044c0d0400280100880880da1920300e041604260006001c0710707060304108529400b071b5648801b03a900c9042e03040400a5041d5003880e0550400b0a6034010898910a01c42000b032044207a0700100026445a6220000784a507042406680c0c041c5002035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 146425377 1250 146424127 146424143
    0xf0c01050d0e07031505060f06120609040213020a051902060403090308030a14091e070501140c0c04020c0a033e070b13050901050306011d04030c061b0f020604 70
    0x1070101c50526002480d00003210819502055605d03900c081c644141101517111082c2c6a5041040500d070481c4030039503904041d10120314100b4040d2095032a103000a05251061100074080f9080d520360704040303050301140900441d9038880d0000060106d8100354800d403c45540254103890440c03001c40d00c1805160f04d17407200c05541c1d0855a40042a800041403844078076620b00075142c65040e5412107078011a0300c000980341c00b106d08160b074502164000000c0b041540090810842079900a441c0b521020501c01010380303820954084d43d003046440303044030754800d0000c520440b40040c0071608108462198660840c08941450003414000245c0540c0707070006008030b0441c0b1440c8452040700b050070b03003520a59078100d46413022095660000d0f0825030942e003000307600344440d003802d840c510702511302100285000c1d8502800d058101109080110614030044c2c04102018000c15010801c294004030902103101401e0307400b080c44600000070300000300400c0315080c030240081800c0c0d004603046159 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 146426627 1250 146425377 146425387
    0xf0f0a0308070809040603060905100603050309040c1202040b0a080a0911040e0a170417210a090f23040c02101a09040f0308011e031101050706020c010e0f0c0105 71
    0x40540342c1d0854070007581c51820400c4004d0780707a0f55512560000c0d41c80b40e203000500801c01d0804078a003208084140d85028a8a4010701c04030f0400001d07581c150350100c90210320110031701d1048441c00ca0603000c0250b081d00105021650a40c828050440034015031b90382c0080356200f5913a00165142c1407000390003482010a0300e072003420550414040342c0c800030101d400c0d0040c40c2d641d882c0051624010f2031181d103c0400c0601200c104550703603400ea5805072000f4445022407089401031541d05000300c525950000850060341c130f0084101c0d000411060b485045c0d22a0303640444c561483c20040c41210414070300c04802030038030f030510520003280e5080d402005000f280d51155801007200060b4001516840016040541e4640c0740891003a4482d00c605c3e0401c40c0303246000f801184060704844844030b40d42002c1d44003600c41440c02c0b001c580e040a221b01e5150842c03401038a0901c14503030041d10650000032036a0404005410510051950b0300445036111000e441182d25035600a038198009041000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 146427877 1250 146426627 146426633
    0x11803030c02060412061e090209151f0c020301270204051b0a050c0601090e0d05071b0308090f04020a050919051008160206010e0c0a11100b0f0f0a03 66
    0x100e0319240d588041c08403890a074403a034030305d0414141000115074081d00c451411150248845843d0a0354010031024414070003540d00040c0080d03002080c800325040b0301075a07031005a85944040070782100a603502c180c0d1000f4030b00300920030055800c00ba40250708200286a00b040c2c854070020000c40e014a2180e4a850254204009014083c10359040c2401030509070f580e0001e440000d00b8503421544520342d0301d081350a4400d090850517407001d25000c0c03908071054002c02020034450307140c10305490456a0351450740740083c001d580c4c1034441c01c10f41000c0340010040080000c02004500c1c0100d903030001005010342008164412501e10b54009481031081d585a81000c101203860507102516401c5195158000310300041c034805001d000041c1407500b403240060803c030010440000500c0903220541c10060a50710072107010340300c100a00c100240000445110708400d0a00c8414181965904502d07040d07004054580e158030700c4d00c030b01c9005c90705002c030f868298010780352014080e02c52034095240d91 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 146429127 1250 146427877 146427887
    0x90303010e0c030702070e1f08030406080c030a23042a060c02040906092d021c02041b0f11031e0c1e03130e04030e091503120901080601180303 63
    0x2a003130f402540b2030098042242c1c11441d1045114064850301042020f030138210a800524517039004640e03a402c108014003d0603800480300d94070192460505560b03840d002070105c000c21121001d0f0307171801e100c400c01d2400c010044d05068011401818000405004402807444101808c80014446044000300700056030199501480b00c50001304001040002c0f62180390545407040c01c01c031050000242d5249041e44d03068a107100180c080700c0040032900e040d6011a1035080c40100000168214002010455480350040b000c1031800c03540551020444d241d0103031141022400305000f094404103801d00ea0f030300c0003050710940005030b003c98160090040c1d4150081d40f20038901d140c503001c3c5400f1a001c4044451600c620890306100642d03490707200802210b0055125007250038549890028400440ea121343e0401031118201d6160703540361214440301d803c0b4118681002d400d4041c40c0d1480c801c0c40f6007003024113072070413080e00c44244690780c500c0111381c0b001d0625281040080003002c2400868410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 146430377 1250 146429127 146429131
    0xe06060f01020a080c06040c060206070507060f0b0d11040b010c0b0105060708090306090307020103061d0402130b0d0c15020607020d05090103020417010213061803022202130e090303010e0c03 84
    0x10b0065440d612a00e458000c40380d489580c81030010344c040424081002928240700307005000b544040c00da6404c01c580000d200344540200601320a4607041c0c0c20000d0308681c0c2c484050318000030900d041161007440d0400381e00f41d25003030301403050f854245040301e59400345091071542584030109085981c01d020801401c0e410000c401e580509003030001c41c0c55520308111450103411083e0066859822510005080d04c0f120340050104072906120300310382d109103603140344e04594100d5800600b034a0035109200102183d4012b90350084140f810300c0305000c00d04200c241a00c030600c1e00550a82c070307803d0b0240c0c1c0e0342d0425500700c00142e020280c01d00c0712903c12405080b89002c145405440c0c25a0b94419011030100481940d403140d5001074081d0b0700e0188141824010612428110688034000030385406008251001901980c010810800c0140410059620001c00310394215100c201c05031003200195954040d40b48580203540108031001400010303a8101c0e40000129050b960703c03485c0114607a000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 146431627 1250 146430377 146430379
    0xc030601141308070308030103050f15070e0d020301060906090e010504020603041b0b13080f0c060a030f061d041a1005010f0e04050702032205030303040303020714030711130e06060f 80
    0x302e11004624a80c0502c01c0f50010342c0145859910b81d410750414a0038060007103c4078503150f02c0030180ba040c080c80050055401841800e2140049096902003250741c620940000d42c15482e2003c041a5802d8a45c40241629600c20381040071501c3c04030b400b800c88d5801c0d42e000c0d611079424000100012070030850720601000c03a9102000300d658810300c80043e41c2080248190708110f03d40103208003541084034400c6400b00e40c0091212a284c100031491034414811510304050300c8034070305550400f0541002d0018000810318103400c492250720502e4008040d40c044515441d0424500315000003142510300690008103070f444031518080c019a4030343c0d640b108400600c5100050300300c082da02d600c10244030741800d4024542c2e600f4440403400ca45000008904a48083c403181480282c0703001007601d07401545401c0040e5100501c1c00c05c401c4a80020300c0300001d80c0700000b82d03481080004450003009100640320b910101c409031003507030140c41940c1c5130001c0ca64000c600080861810400440320400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 146432877 1250 146431627 146431657
    0x903070506070305370218031204080d050301241b050d020f0a030804061109060a0e01082202040908090a0e0103020a0605041505030402130212040b0c03060114 70
    0x8199564609080c0c007219541d0200340d540c0c0402c03134804002410640e4121416003d01000840310300e042100c21821106a89059408a20038946c1c0702005c083e203644100003011a151f00d0501400d155403a842070141c405240262a044802c040c0150b0075281a52000791403000c03d4403801e6a120440000f4020000803c00a9800d44605502524081386600d0003103015180704080020041c0c54414640e81c0202158030900701034020130390220200b60010350115010a40422281002a440c09003010407039111400040c84214280c00034422034058200f038842006682d180542d5981000322030002070404803c5201d00001841d0a91200d04201d00c00e1204034141505440880c843c64500c1c0c00420002070044018415450000e440d500108020301e021450142060140140c492072011440300344000400441c0465940b040c0407078006001c2282107403160b003182030140c00c81000f540e05445001401c00410188840041100d00c5140c043e103074000108c03449100303611198000c07001800184 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 146434127 1250 146432877 146432887
    0x10090b2206050a1706090f03070f1407080f160501050f03130b0a0e0f0a05210c032110150e010c02030601120b091b01050706020705060c1b070b030a050903 68
    0x3d036030f1180c0c05025003142501c0c0c240d400f2940d260145414000f8011201950000790490360907400001222603c42c0e0000d02000c0303000c2070385015049292810f042c0d00f8070b0300492a0226403c040083c5101d2000140350442b40c00d1980d540e0781d00780b880744a001c0d20b400201c042054140480f0300100464010b081d00846000328949511a00090b1800355002400281c58906c000350201003001045c81012400020b070030a814203035a0259581d4856001440e02c280c0c800f1002806038800c07040ea15500c1c1803100340caa0300d001c040384042003003017210b20768950322001d88085403052003030003850000d41e0ba020b40d0801d488a0320b441c05454444184840c541000104c0411200580742071204600030030f40070416040d41d440302e2910350882d4400500c907a4842c0c1c071a0720a43e90100c2c070f9101c04280e8250a090103a42e0760302d941058000b0b44504080039145200d024180709401806200030205a01803190702103402c90b4445517141c590002e4401c0e1b403083c0c0b02c240041030041030181c1c0312540000103013048034900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 146435377 1250 146434127 146434129
    0x30403051905130914040f02010903050f07060807050a0f031a03010906050403030b010c1104020f0702180609100e0118060e04050304061b0807200a030b10090b220605 73
    0x1e40031041c6800e00042010600010000042c0c03e48006400d05640030f0201825031164a0380c0200010009030010b07903030009903815640508a81005503400c1f409554035075540c003925981c0c0d0402c40c410040060104400a03c005200700141c0d0300054580d0359141551181800c120042e1051020001c00f10004009520741c0b5a02481140319042c0305000105a41c03415041c080c0c2110001c0d044541030201c4d81e03169400007607030300248140789001110010380703901c0b0045010080c0e00681c00000d401405241000300c0311250084858401c1da000c80340420250f13101e003140d014414852044d1014514400c0050025050005d8211982d5541e0031b4001410359540529191095003913038140d80c03030341002034140070055016104c1c2c00c6c0280c40c5400d146c0c2c4075450340d0341e0014030320414001070640e4815411305c0c803094440380030074031400b00000c01c80c1d0b40403030302c90900c520380c803c066915072100491064001a0921140101000200010603c0d15000d102100110300207182c1c050180003da5182404562 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 146436627 1250 146435377 146435407
    0x20106150306080607030e0a140709020f1317070e0402060c070605180103021201230a090b12010c02060f1b030a0902010e0d1502070206040807030b09060f060306070503040305 77
    0x308038001c1d0340c08640c0302c2c80c007640781d81030141c0071380301004250800c040e04803101e02c002a040d50040d4010081c1104d02d140a19840c14154590058180030b4000541468004000c002411811444241025044e41e0b5080d129503d101c094034405482d8200200420049034007507002d40c0d1103030024200c20f1419041000d0703e4208900341c1c000f03102090021a851801b04244a81c040510000303080451622020001400c0071303400c140309402004042e0108040208640755044601c8074000d840c4040950b100c811031300280035103050360b60080203a90b4803400410014010f5010b9445607801404540d02c2d00a130503084284010f1210100c5c2d0742c0b00c554565030018910003180700c4d9503440c10015107880e892000410000c000403405210300c00b090081804140d04241812112005e610010303513991240c40411001e00980c0e020b0002405000380000520a2500009100b880e01e40140e9140e691003500d9440c0c00841070798000d4141d03000d0030000c0c16943c00f4900840d0052302034140241042150620808 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 146437877 1250 146436627 146436659
    0xb0f040b031e030309160506120601020a0f0b01090c051603050304030c0515100902030403120513140106051c080409090c030f0510060f080c0f06040b030a060302150c03090d0201020106 81
    0x500f503000000700407a1000500840c0042c0d5902021a441075203040300040b82c5000e00e091744420b01d908240400d0b403681c001c008080071190710140350510b0700c8517400d05c044039403000d2040c80491801c060310040c04a00c41c1c8200c07aa59030708440c3d9150724200755101220640c00007030044041c004030305442404500100f1294902d0382040f1b400c143c03c1d04d0700c14285d048000c61940724040300d03030050050200080d00729101903102d0b182c072280020f03103507918111403c01c5c1d00048000b8000c07040000a9030421041034200505440081c4c0b100407802c10750b540c10602440301030101514018040c041400400c1070354200c0c03168140141040c4122513101e445603a880d00780c003001110540d11500d1a60b0641d282d502500e0b000786107000304090218644910035440d440c2081d241c91140b01e01c4800c4e003820382d0300c0e10b0690f8040d0200d01d003059242e01d0440c0003c0d00a0138907010070b0b4400e90684400c1c23040000391030120f80341c1100c848041c5080038000d070240089260316480890655407244404540c43d03020110340f42c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 146439127 1250 146437877 146437933
    0x1d0708030f0f1201030c05271521030d061208030106030906060f06020c1807020c010c021906050c010b0f100e030a06020f09040513020901052b120f030b0f040b03 71
    0x51a43e0b01d040100b0080d00c107230b1901c0000346044081c1c4101002c0e5030300c003d10fa118440c88250040000c08a001a03060360354a080e2603410444059000e50b01d90000014000141506008100460302c5102a20a00341c04402c000d000c0c0c2401c00061000a10a400450040d44100c201140b602e40b15091058240d01d10b0300141c006038018020304060345030030240d0780c61070710a600c695041307800e01c100c009488481215002e07050104121745002152a032803000350000c140d250300c020030b16890350b600601e9a40070713002c41d0503258240702441d800384ca000c0000740c0c100203009200c51000000b0203401d4480f401204a025030601600c0b0502011403001d00060440c442d510340300607901c807040340400080707031000b03014000580c20120f01c0350700603202e07030f95418151401102c108040c1d0080918000c020315240440c1c2c6030151904018000b0850071000c0b603103684009450f68002409151001c9080354110040d07280c6c80040145150740742c0c1003503800348617401c60180c180d5422140c4c0c3c9085d202e500340641c1001b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 146440377 1250 146439127 146439143
    0x19020c030f0a2601051002030f0d0507020601150f0f0c1b050a090209030601060516050703080405010306150c060b010513030c140603250903151d0708030f0f120103 72
    0x1c40e080d03004801e540000c00c80c00b0940250f10350780342a103502080501035180140007414000400b5030007081540c0025410140440c0d17640b1042c1e41c11702c09800b054075410054403460001107100490345500c0601031520760b4841c160070040d01d90440d02100c0048140041c0410200c13a440482c60400d0303042c036488007402e003d000040c0b0303203c1441080b528580c80f0440c52407050006488554001c604103046503118a03065071144e20300c5444000d000950a00103090344030f030755400410021000040d10450744e00f42c07000c200d032503a00e0a018043d0441c400a080010351641d10060024a8543c41980c17650010724000b810403103005c01681e01b03140f054100f0f8400216480301001311001121054494034015100d081c118103052001180011460350301116042c00310740d070548041c2c8283d44080045070400d8903909494810000800200340c00003883c1a1010128903c11a00c103000541a007215440d600641c54556211070300d20b50790b0410064a206804104102403224407441c820074007841c041c1c520 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 146441627 1250 146440377 146440387
    0xb0a0b210105012103020c060a050c03070c031a0106020d08190f05010503120a0c0f0f02040507030218090c090d0c0e01080d030609060e0f0901061a04081e0619020c030f 74
    0x51a048103007058102440030011340b0f04500080c2d02285081c0503007029141d0549640783c0c00c03416941c030300070080980c01a10001c6100428090101d800c403084034029030a1031108450382c40800c1c03074400e00f4040c141c00f40c1d200c6500e90080c2842a014075038484103001398001c805000541000580e218000d8800f069900d600040c04141f80900558010f501584138961600c110385201a01c81600150054420281c5031192028090b0007130004070801c0c0e0041c4100314910b0625806802500408a11b07004040428001c045a04240c5002e0340107880d020103032410b1498034000c014200685046c200c0705072005040002e002031a00c40f81502070050003000e44001504540002c0840c1d01799400340d031505081500400c15a441582c0c210b4010042005084041e0340b08015580500b41030b0b8032450324501200500c3c1d00010540d03000e807041d07ca40ca01a1a030340c010501d041c2c81c614101e81d205203030f20303045203002c80c0c0003a008002604081400040150034841811034150468000440000f140040012 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 146442877 1250 146441627 146441639
    0xa0b0112020301030c0501050708090604090507170106080606160606060504031709060403110316092003091903170106020a120c050d030b060d05090a0201110a0b0a0b21010501 77
    0x15916100c0c2008840850643d07145440d034203242101813241a040c00400100342c400d00920508840350f0b610091301c01a0340b6640d890a00c0000c05040315154005800400700400c507240c00e5010750b04841041d170350406a52104010042682d000006d10000d040d040f61703d1400080550240400030242620303002e8a6515600300a01000038029441258203010043c4110b25a554800d480550740c1004001105074a480080707494004d00d802c80302070701542c00e0340021300016190440d5080c024410040e42c0924403691944040b40402d440e440d4403a00160340003110352548416900c0d101d80249002c42040280c054140303140300302a00007c0044e0407401c100802e014000038440e400e0101c62030000c5050105459080d103403001c204901c010103480e9181861a90340e810161204100c1030401082141020340d8880c0d940c1c02a08800c1740032403200c112003050341b200030503807914607604101501c1d011b03640c0140c00710050142d1100e42e54007400c0d0781880d401660200843d424041401e600000f1a541480 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 146444127 1250 146442877 146442887
    0x40603080901082a07020127030606050d05120c1203070c1e0302031b0c060c16050d1509060f05042a060903030518030319120218010c0213050a0b01 65
    0xc0c00c0d60041c100e8112000d9103032551404d207104020101003041d403200c80d28401210300001c0c3c00c2d103140d200d9141c0c100030081a100001c10108071307807183c01c040110301da80300c060241d014140d041c05070040d04808204420381381154001c002d49082082031302d1406034891810031940d00183c0f00080003030181103000c01040320484c03100100141d5035408108010080d41d00960724410304140c00302c468841c08040c10100030400440c810f01500406850700c80c1c06051006a50301c0c01c84440c00e074045500180028503080235400175440f181c011712800008606141d0b200f01508149604032000303580e03100201d40d100740d1032280c41d003e140704425261b0321510150141320880c40d1399031641403600b0401000c104d502d41140d2160226a41424890b441e00b001103140f15030404103c6e001500f6010000e103581611401a105c14481c9100b80c9508181e0f9042c00040012402a07a8608101c2c0041c0030f501001e41d03004001c1302055910040c403511300b0b181030011117419200103580c030304881e0780c480401c52074030342e080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 146445377 1250 146444127 146444131
    0x4061706150604031113090b13150e0604170c1603060b0a08060a09110901080303100e01060e0105070f020d0b06040c030b030c10050d05010311150a0e060f0904060308090108 76
    0x440c2c580e4186400d6860304c141028042502500c100c00b400d1400c03008240941141c01e10700e42062034140301c1e1900c0c803400c821003903002c01300310f54004811019019540c114070440030b2807403c00e070003041d450b900c0d036072192170482014002c1c901d43c00c0c080c031244903c40010401d81034181880c660040300d061840c94590240c0c2c40641440c3e01c0b806000b141404220000583e690b8489a081c0c0c02290b2400c582c2000c480181c00c20402a82080d25a00003282450340040110b004502c00c1c1c10036040035648480e8445101400e0003030b40001340c401260340703c607584108042c10340503000e0840f210142940d6400a85181d8840c01d0072644c245074031080010b6441d02c0d209580d24103109007403d0000b40c00314000a600da041402185220304408008140700034410000da0f07d00c070722200c030308001d20f503142e081845d000506000ca039031041800d070540c4010700c02c0720b00940749842e9590719a01c00e80342c560030820049411007400046942010300c010107003603440d4002c56000314041e0300200e03500c0700c1ca0b00c00145002c0b00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 146446627 1250 146445377 146445379
    0x81b0715020a12032018030706020d09030f1703040f1b0f03080708160b09070b0f120c0d02120108010c030e0a0b04030c060c03050619230406170615 65
    0x44140b00c2000301c1e01966640500c54840e250004600358180741e07500c850700490307204000c24607022603101001c144656240c84001070031401c5400306550380c0d4040780c2e00c5005154242c00590b00300b00070400100740c0900c441c02d0074420119941d0751010b507084140c43d60000c9509a070072608a07801d000501184000c04c180601c09600a0640d039410410700a0303503000c0c43d200c01401040300140140600c6041015501c4d600c19007040c08080c12028240b840304604d0039514880b02d0700030000b00181c80910705080342c1c222910000c1c1ca0f401c100701130000818980c00240b0b15414403804003c00c0c0d2400705c80348000c144562598100603d07a505207034440f82140c0f6116858001d0514002810050401c00511155020342c000107140c082d0ba55460100e400369031a902c0182002d045c420504461501034000c98450072051300c0b4000040600300d8068142082c0e40f0422070f0100500c00801500c030034110300581d01590241000c1119541d034100001403c0e1004400c041603004082070000c80c00f080a041029058 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 146447877 1250 146446627 146446633
    0x40e0c0105040b13090504080d0f0603021315050604270c05041203120516030c030c120b150c070810020c070902090f030a0302010b030c01020303011d04081b071502 72
    0x494440040c1680c81a80501011000082941e4190080b40b00c0f0700700140000c11424025400d06240c0604240c001d41034520480e805e2400300d91102929110f81411a500113114694207000f401c42d2301c00510700304591032610001c00781c001c0340e0394581600a00080c141c43d0f0602d08222039a2800f8007140c820120b6086031305041005020b002070380a02a5401d450009540000320059890190b42000305500d0740761480d400c2c03108200c000c100c800e0901150b0111624280120301c9800d00407012522003540603408511401c10048261005134801150888060100001044900c11504a580004460f5002c0d40c0c4003010510460340c0901c040500360301c1c10007081d420404c40c02da4403500e0308158040e4491140e0302144264450f915000c0ca4405600c000d01602c40d02d030200e040013406005851801030003403003019144c130b4003548000100c0e03040725181c11900340040c0e03115500400727042000d0302c2992001001e1003180b195110210f00005e1300381d2403400801440c1d18203401180c5802c1007180100540d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 146449127 1250 146447877 146447893
    0x903150f07030e19080f04090608010c090503030a080103170417070602070602060c04030b0604110d050a06060908060f0a090b010e0115031116051608060f010801020304150533040e 79
    0xe13110954003094039901060140c0c440105d124600c8141c01903601c00c2c0c90886c2400c000246501d0194000616840160b846001040d115014103940c0d100d0615080c000510368030040021a0380d0241e00d0403da1505e240c00f5103011750740c03410000d07070784500c2e10f0f0f010070f44c0c10420040045c541c0410101c00280300d103002030f105900d003100c1d80584c0c82c0194030020f0200c0e0385000001b0059910755002d450204a44040d0948901015621000a03c000c6a070440c52a140c800c3c00316890340901d84010459007040300801c0c0075a2408034506810070050070684505031100c0280c40000d6902e00c806001e801c0080b0340e000c0c0d0f5850300552030400340040f0b07804c4060514012200c1021081801114120280b55822200f41140c500c2c100d0318203240300003900c140100040011902c1000400c00c980101c59030407851441ea40c841840f14200e200503100107001c074642e4040300c01484000d801450380011240c010710b01a079a0110440000e10317510021400c00703500c1154442a030714161040303c9601c0f903c10000c103005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 146450377 1250 146449127 146449153
    0xb040606020a0f060b0d030816030b031e07050a23060304020a03141515010228020904080f0406030501090e070e06150d020414130504080405060903150f07030e 70
    0x80c5691200c080c140390b410f084140305110b15500700c0841200d014029139890811410001c05c040401c1ea913000000d1000d0410b03410f0b1500c24040c03404142c00007000b91240528424244681802012101c4441c2c0951200043c565482c040494000d141007200742e030b0310100606030692405240346d04240301f40381c203109010241c0c80d940654001d60b644410602d540c1210300d00d200d03141000328080d11600702900b030100007141e450f0541920441400383c00300c0792604940d20248a80f14800c00c1e44a4403441c01001090240c5890700c0c0307868000780114403003840c14000c0c1d40b201c00f00b0707480740d008140402e4895004001d66000c0f4410001c048a902d001340031070a05050001810410140501d482801102c0015800030364850403141861030183d011956242d0300c15405a0300030744e010340140328030310b882c2e800d246441e41c9010b114812a07201441500e400e00f490100610740d0054208903815110340c00c0c510725400d034052112401803582c0b48121312140390010b00141901c0c10b00182c0d5106401c0340d0008441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 146451627 1250 146450377 146450383
    0x1209030f19060b0f040507030b0f06210705070507060c0c0608060906060306120708070f05030703030905040207080702031f0f02090105030a0b0301090f110907030e1f1104090608010b04060602 84
    0x10650707001c0000719840b52640c00003039613840d4612504da881450711051200c2c642d01039011030f400940030384090790700004110402690b80120180c10690788680718004c005a440080700395880b4640d03003802800c002c4552125440d111980e001040800c100203090720a02c200d458180d801000149030104407898036a000c1041300c070300135207000d01030100880400c2540c1d035103450001c1c0d0245004100c6081580d02c00c0003d965004520800b182050300650120b01d03418045043c0c001d1304d8164031200161480e00c070600c4001c0d40000c1c42580c200005020660042c0c0e01404701142c2400c82c0303c803120f000e400080d0300d04102d500040030070481c030f441005007500590304442580c0e484001110000380b11255000460301502000301c000f4060351070552002c003040307030504240c994500300755a694540d42c0c03200300507000c4424000001c0d0700360348a100f6203020700081c038171016501c0400020100e13180802d10340f4010f40e80c026400034140a500d8540500140d2424811007002e510200c6040c040680f40c4000031351 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 146452877 1250 146451627 146451673
    0x1504120c03020304090f1e0e06012c07030509010f060f05060306061303051b0a03020913050f03040b090f060405090601080405030408060703140a05010b0f070c081209030f 75
    0x500560030014020315000748159001013030514400d004689405000038014103040c1d07410707852200854207400f0f05240520500729885820402080680d08121045030302418a07c01900034404c0f00703d184a22503040c1c00111700a048035100402d075810510703400740c00d43c0c004141d518401440c015040002117841079200e4100c0e18180e8009560f525003801041f0342d8403d142443c0c440d40700c1040e0010402c0000200480c00c0070704240034200c080200b03001c11130301403154803019610600a4010442c150400316902c06004d104004840c02003003800e41513411a08150702a1944003008100f4040505107407031041407402c1300b02c0b0401d10341818030002407140140900070300d041010040009082103001c20484003e803803000c0031a407107854007142c010041c041142c9042d81081c0c160780030800c0ca1880740501d0f810703158140d000c1814100d1a04140c0015000700c0340540300c080c00301c003000803101c8081c41481c000c400c0780c1d00c803603940301182c03001d1629280000d29403e18681c080d168400d91201000b039594 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 146454127 1250 146452877 146452913
    0x1f110c03060a180804060f1403010806040b0703021c0506100228030c0f0c03060f18030f0302041a0309060c03011422180516050d080304020307120b091504 68
    0x1602651201d8103840700d004400f000b015040002400300e141a00030b000c030820300d42c840d60f42d0082000c400b00402503500081c8903000c001d40c005400700c2c0000300b48004182c5e1000b280e01d401400c2c048140d61085030049000300d803408990b6141c060000c80c0c108a0f001e024003542d640005d10481007013141c040b88202152103140500852041d45501f0148601820810680c000e4090300c210441411b055089086c24442111350350f141031101c0f0303546403890107607111f100b56103a02c0c8111140319440035640c802e240250401010f90800004c56600c041e59107182d00d016401c845503480b40b8000f130701c2c5c510382440138108004140307082c0010801c0c49001c04c052240002c0940750903200d03190b24101140305281c1940b880075050b0400e07034401c03403020703501d50450342c040e00807401c07210070720f1083c80442e031111414000c40342c00200c03a079600f0300400c00401c000c44c1c1080c409011140c1c03c0783d40700c0044001020440e802c032032007040e01041c2f20410104014060f2129040c0e403820b4041d003090340c2c9020707417a86108090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 146455377 1250 146454127 146454131
    0x206030f04022d0102060109090803042301090803061c170f2802010c030605060a03090c090e150603060105010906110f03040b040e0901060605071707021f110c03060a 73
    0x10219111400111410201d00c3c1094540c400d03000e2044103203084003044980144200c070000613a0f01103130300650440e0764100403c5803440e203458540e0404610035440521440b4190003689038420424440e40d4000c0c0d02030002c480d200d0415000301700d1014889400794040c00c4c09980c0303540205541c21103840011760142c85243d62540d113a0700b03030980c60007501c5d030500340701c002d403030b0085c80c506001e1075011011543d55008100305015000c0a9045528034064284c11032001e000400d9410700076803b48c01c255024030150680941d80d03e54030425103103500040307480c54000c512010103240c181010140c0003002140034001a60500c00005c2c441d84191142c1010040c803c4081100c0b51401d00402c04400050005e4030b40c3c40351101c50270481a0710074450940a4109080040c02c2c000061044509a031a25900c60740b403c0d0103625030300a0140700316500319803a0010061000141d0701d0340c040710402c048840c6115000054100c000d0401a2441075103c0b4503004861a02900e640203e91f8540c810031031500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 146456627 1250 146455377 146455381
    0xa14060306061e1305030c0109060806010f090317040501080a020306060f031f0b1b010204080606060f0c01050a14130302420a0501051005090f012d0801060201090206030f 75
    0x5410715180c040f040d1030768568000803901c140c203450041c0b00c0c0a40304190304071042c0190b544011a0502458030543e0001047c0d81d000c02c0d82c540c4a800c80d15900278a41c40e010002907100d45401d001441c1d94110148c0c010700c005400c20582d40c004080750b41c003241c01d003404c500b14944031001c50000e1141461900c240500007000070000c43d5000034000c0030ba8184c0003402c6c0c1042d1551440b44e41a8002c0c160019220b20486010172142d9050088805030740c11100a442a5118241400503a030042d01c4114550b00061090442c1d4200c24070030703140701d110881004100c1074902208203000074006029114074050155140d008203400280c17010704121042250341421601c1a0480e503182c2d049101840b4085480c00c3c2044452807034031a4500420b440b50081255903616010007015000c04004140800e00510092006240411200e41000340604041c0c0c250019580a0420080d042541482c07a4840300c44080324268003c00840c00340006000810288a1640000d100d500004011004031581400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 146457877 1250 146456627 146456647
    0x70819030f0e0601050316120807030c30032d02090a03030c150903020d050d1503060f14070e04020f0903030f07031707080c03151002010b0a1406030606 67
    0x12040e40c0c6080684020000b11000c0da07241c83e00ca000a02c2110f100384035034492000000c00c910b100d8021540074060700e148141c10f81c3c0d01e004081e00000c60940c10702854101c0710780031a0b010401c28034155601042c0004010300c0410810300c032600026090100361500e8014103485401e4a109001c00f40940c2d80700c07000409906004001e0b2281d507850540240b0001000130030140c11400b0000414440c948104050f00042c2049003114019503001d07006900c22103040c14158001d0009001c4440910320104000078040740260305150994822a60241d44000e041c004120901c2864100c0c003440d4810901c9040c071180c0105226021600c080c800d60f0300181d11800507042d4403c0715a500400740c181c3c2e0f151401ca0501808542125000382c02041040e405001d061a101c00d82c40d1042d02c0d9a101c10301e141c0c0f2031a2030038055401c000e0280e40031134070a2580d002140d603030804028050040e9400032621003142d03c2030241c404180e80c41218051100020215581d89140640c2c0c5d004006850f22901c8240880c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 146459127 1250 146457877 146457881
    0x50d0905070b0d0f1b1e1e0c061406060921060a02040302030d020705061606090b0405030c01060512190201140706090201080601020604020a15020703150e1207081903 73
    0xb07400500320010010344040180c00030340001c0000803003140100065841403440954030601c0c0920100006d400e45454041c10a441c500b440d492500c9140098610b2502d0106144071119184000c3c04201c1110b000010400c003130060040d81c24000070585450b0030000c000c604140101c800c1c0c070f445141580314800e1845009401124002040320440d04981013880b10341c4000c0d4050301050380280244000c92041900000300e000840b04080d003850b107044140c95240c403030030080c4c0c841100e00c19260021240810021100300b4042c03409079024640d05e070030a8180c035007121041e50286000700703241e6000d030b8861400030580698440e94948102e0844e0014030048a0608220009065403e00813806900348201c81e1b00c0030032014403c2c0c849a15545800e40166552181114000e600503d80c0c4000c1c03115018990341c44142040c140115008aa2070355038014000181c48045000e065a0b41d040c055003040401001c441c078901190a1454507140d6212042148030f11020a611501080101d0420501c2a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 146460377 1250 146459127 146459129
    0x10e0409081c06050603040c09020306060f07050f10060810050c0405190e060103090f170d0f0b03060c0702010801031b0b070809010801062105150303070506160c03050d090507 77
    0x81003400359251040400641803882c00c1158800320b07482e100e030115031420724130102c90203030343c00454115451f0b06c0d0040070300181d031004240940040e01070000200700c01e805030240842e207220754084d10714406410740c2945032a08810181d03420034201a1300304000603020900c01d007000345140012400d03a9406c0404032252113240c2c0140c1d000014041c46080d0850300e40408400c1e03c0d504809103d07161641c0004405035000180050000340d9100300703040c002411841e900318203c500d5802c45003418100c075814412501c0c0f0b01c50385040c0c961247c00b001b00619003400142d074045480b41580342026a6070300001c10032101404000c00c031082880c10031094a02d08400c2c000104002c910040d91a2503514002c0d9141d04680c1c0d01c103011031754500c004a545400752000f03200c2c1c3c016241c401080d0f6001c42e404e50014090181c8800c44a48050058070010344040c4020440203010303100604150403d41c1540e109800640c0400c0e08010b110500780000030380c06030840d020380c80d80c0500420451203e0606509103486 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 146461627 1250 146460377 146460383
    0x30102040e01080307051606051c0609151d01080d0f1107170f0607050a0507080f040305060f070c080403030806010210051614090609041e02130905180705010e0409 72
    0x820000083c01000000100b00b403e10441c1601c1e440c00414080302035441041c002e010100f9010302c050401d03030009401c95060a245541c01041e5640c0c0c8603030400445134140c040c0c00305010103260070300907619030401c280c464841490b044a00c07980b41011541c0c440c802c000d40c007820492480105c2e50030314424403940842c24201c0c402c4e03422441c0d031840990601d4a201103403e84901407042c0402c0b00d9030011030002d2161003691151407424200290841e8030750311031481165854001c0c891301e200f0a5200d005000a1031041000704050300306160600c0004c4001080c86c0200448001d48200180518082d107044a0f0f041c00d2043c0c0940398940181d0030071600e0316030044000d02d020204200e040c105d0702e061440d02101e88403101c4180c030080d1a40c0703440c401c481d90560000e204214100560400c1d40c0112100c00b0500b00400800010000a0041c0e9026201240d00070007a40ba051100c070351940304940c0c0000800101c3d091001c81440030355180c0c111845610706000980c005200c040c0c4643d001104c0d410780c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 146462877 1250 146461627 146461649
    0xd05031207390210030f0504050d170709030f0f05010c0e010305010b07020105040e151002011b0507020f10030b101707030504081e09090f060405090106060e040b03010204 75
    0x181001c80201460030712803070390441030342c00c1d444a5a52001240c0d0741c8003100102e441d00161015940900040c00c40d036140c00d20070195a40c005441c00c0016114103801203200d42c024140140726081c0003009400c11052204482103400e0500c41c019401083c40000c0b01c3d4004603140e071b000032070304101c01c1124000c04040e2465081421000c3c07032650101c8000141d09090700d04000c81c0e41ca52901065034040e08030000c2c086481080144a80e00c0ca102200b680500da120712078410300c12440c0440c2c060079400c042440075039140e140c81036058648446412001829145ca10b04045040e00090914612002000e001e9065041d4000d50359100380c10003800d411000d020441d0840150800038981c68500021000240c2a07202260466100340181800b40e50041a6641032075031200428031444086440240341640c1004280b00c00d4503480f02440c0308001d007a00880e11498140306000a403140181040140d03450900c050054582026125658140079640000c0589110000c61700a116541180d80101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 146464127 1250 146462877 146462881
    0x60a050c04030f1e060b040c0f120203090a0c03030909061a070b090709110405010206090f0c12150403030608061b0418020909040602190e0f062101090204080c010c110d050312 77
    0x2103803d4116103015441568100107a500400e030440300303d00c141e02c9c468005040d00c40002070a00b40c0360060340e0012800c105460725043c81da40c41515006180e8001c0f0302103080752900b000901e2032031080c50300801050018510b854016100d0b00e80c0d030321804070700500c1c264401003c69000c020800c650350140c800010100055450041d44180740d40041c401c445c0144604400296a01c2c00800c00c4140719080000820344003a40104100e04a46101c108261901c1407282c080015050f403404079002e68001e4800007403050078029003904101d030003030001c02880c1c000080400c15104440880e4101c03603400302d0002c0700c010400c41c404080d21902c0841a071294020040c88140196075009054000c810300c4501c2c10300801c0507094407100680061541c6c0702c580c5030000140e9042400c000c000a034220603103010a142d40d030075074030500a0280c00134412103a01203000d1059503402c10080082402c04d003045d0140840669581804507080741c00c260203030b540d6507404002c01c1820001d039102500f0182c00002c00e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 146465377 1250 146464127 146464133
    0x60e07081503010e160501020109020f10050d020a030f18021f030902040f0e1e0604060c0509060a0e03070504020408060a0e0106080303090604020915010203070303050601090f06050408060a050c04030f1e 89
    0x1d0310500002e00c41700030f940c400c00101580144200c0034890740c044c20380d11105080f1810054032840c03d003034003814810308100b6100e9401e402d100800e407452964a0002d68241d45d200341c141103c041d8800307140195680c2d2250800341e03440303e4081100e0014482d420070401d0240b01c0460140010f244001c1d081410502c0e1038040e094a5002611424840021a40303902209804007014030300c5860304607241e07000034010401186054118000030306090400c2c0e4608162200031070303000d0b40845500e0b03001a041c0310411500d40f8060050500401e011542981010b003000140c80d281c0070090060681c2a42d075081c041e40c0c6000a4026000820004094940313903d42605065282c240c2190124030032040180024580243c94110142111040c1c2c011070030001e25a0b0f094000f8074020344140c0c1440103000d0b00042c02ea90b09482c0e4009480c9a90b070f0f1170f40359131900380c3d040d20300304d8041e00c82e010482c1401e0400c4440c10b401d1099804594008041c412100100c0c1042200340e007603503c0c0d624034192000418428 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 146466627 1250 146465377 146465383
    0x10b1c2915031204091409070b070803040503090a090b030706030e0d0305040f020607050d0f020102040f051011060109020705100204030f0807140105160e0d05030d1a0d03020c030709060e07081503010e 88
    0x3801b2225020091a55030001465155034040c056500c40a405000c2c22000c00c01071030146a1040c442e1088038030b40380b504e400080343c000d02036108224464845141008600301032040310001c01d2541000d104c11404625401c0d1100c4410a00300c0c205a514400507050160740104070310003580103400b42c0e41d07031720050030103c0c0c440b5641c000d2000401c803680c54001c00c107841482101c0803140c5030380c08036100c0c5080c4010000ba4400c0e0905d071408000201e504144460401d00516000707003c14000140d0f207841503d403d60034a00001805846a40f040c08108007058084908040d910350160103950750300182c0c0341020310210350003e50040c541c40c04003040f045903c001189460b030582502c03080100e080700003c1229841200400600f00d400c10f1000040c0b60005422414130b0800b000001c0d6000780030000803500c180302e250313810390040e401404c00c85064117003800450041d10302c010092100904004841071a039a000d465081000b102800140d0012154501001051801402408800350303840b40c941d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 146467877 1250 146466627 146466641
    0x1c0f0611040305120c03041401020c030106090605010e0a051011100e06060a12030f050a0e0612010f0b040308031b07140a060c03060e060d05010b1c291503120409 71
    0x18240300d00340004c10300051141c00c1e9041d450303248000b1803510381000214942d00b94203101041c10340c41a0300322110259001e00442000c3c01410500142640c0b07048001806911080915401480d120005105a4880780902c6590207a1400c280010f0000c03904051310301200c070110708074028902b10707500b01c0c4c1000108449005a8045030342c031103a1038480544012a901101c0001c0115040492007000d081c042e20103082090403900705014502c003aa00030075115409100401c0542107108010b0100180d880a070344041c2a19040840c02c040c215134409a0a20002d0050050703000324440701d074600e006441c00ca402084d48104003044003004250400e03519001c50b0000c89030706080a0000f01c17030900c80d108410803205500011000c5440b8030b002d000d00b6005900c0c080d2159521910300ea840d0b5150b000580c514404000c0e06540c240e0014106041c12070001d00300000590307031b04002c0e18882051903410f00c0d0440980c0300401d0178031818400007464456202c00c4c0c42c915010204001404402d10b5000341 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 146469127 1250 146467877 146467883
    0x6031e040506010503060a23041b030606090c0f0906210608060901110c2e05190c03050c0301060806031e03070311010509120a02030c0703060f1404021c0f06110403 72
    0x2c0c0c01174407507c401c0d02c10b40308136000345440c07a141a40c617150884100e0790388070f0300940103003995100700f2101060200000c5054006641c011749591013040400218400c40140c601ca40c03520504854814a004018012030b100e40340070401c01516210411401440404006508000400a40d82d03a14601611104101c6010110794640b40d00d0301d03e010f0301c0100b120308461030f0303070080c0094040c404080c1c00080c6103e0000d542403d02e040c0c1d556100d890340d00c11a07029282d06030707540040d20300310440f0741c00740c07908490b6040400d401e040600c8251f40310b0200b9a41502d00030f040a10042d956880846d2038000366801413280e145810846025400002c001001c1041c02640d0384001d01d5002200942032368020f440c401510350080c80c805114180c04409400c00b0040c52042d42d00d003202e04078403145400940e40065840960366500003d90034003520032444183c24014840d1000d01d040e4000590ba44034100300c101400850100080030405000d140c0b41c101580f201e420082c0f080c034100040c140345c100e03000807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 146470377 1250 146469127 146469133
    0x8151c030e0414220c0f150207060203041701090b011e2102010507031e05040e07022e06030c030f02030c0108010320120d030515061806031e040506010503 68
    0x1a210905043c019001d002d06405440388403034407085000c4805010010f0f080c0340e80c46100c240b040000d80c030703416540010440c40b41015406800e00003400e10360468440c07483c096500490041006c5900801070750122814581905800b218141d6040d024290340355004000304d00200002c10082011025194480300c00c03114131038016120b08241c440c450b01d0503628640c0c0384007015104019803142c03006008040c0700e07240030484aa0003401c100030b1709241e441d070580400da002c54203210300043d009441d58040c00d1440241102d900320703c0042c5a500c03460740c00205a07424890a40e103802d01d9900450b0046900000d440c040a40d40e0618042540420350124400e0003400040ac8a42d13106504050503030345c0080f03500341d0585e840e1a42900e2080207180181d045031852150340e04206050000601103000307038601040d02c0c503181d03a000440085910105200f60000c0c800883c01e00110080b41208210984110b0394a440307408480340d100c41162801d00c848119501084200100824007a048910503021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 146471627 1250 146470377 146470397
    0x30501060e0d0f110604080d050918071d01180806040507080a03080c0306130e060a06050a0b0f0708040f08030712031406040504031106130b130503040608151c03 71
    0x40005035000c1010152100c3c070f00703928010100b0060b5264000380301004080518095407910308606085c2885015030100700049920001424000c243c1405800c5484031034404d8501000c1c09400c01250108030150300711144003e04050f4080c244101c1010021400303c0c40301560764100d80ea4544048504851302d005184002844103000034001c0311007607154070350382c5c4140e846000e01005900000d050750707444010f4400c0380049103218820f040898411401170f0005140c407281100030344016610060044407415004c0008800f55806d5803103c1c80142c02042daa1b842c141041c041d14000d507002864028102c0c85c0010310294000020700c1d000b84a800c40c0010059510740a4080740c0001903a4044003023180d001030401d03c2d243e8083ca40c464400c0c01c1070a4916150b800340c4e4a010340458004120006d40103028040c4620b00b040503030300a6801003622041c85560740c545403640640e1156406001101c000b10b01c561109000961010b40090071401c0211851100d01d17001c4015050154042460955 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 146472877 1250 146471627 146471629
    0x20c0303070803070f020c06130306140106050d020a02070302031c08010609080a02040b060c1f0e030906071209080d02010621050c0108070302130f03062307030b0a05030d030501060e 80
    0x3080c0c603012900001060700750394940400303844c128004010300f402c500412060306040c0c1d484030050800031301d071079081c180500e00314035020048420042c120744004008038010030540b5407003803c50700d411511110244c1c80c0e01060400744c0c503040d00e17500029030600400451305400c880340d02c004410f1032820347d41e003090361341d8925003034840b0002c40c002c16280c0c2e040710502201509050b000843c0103c4040c1c500b0f031800742d00c5800d060400f1440b41031600319120b5414080100040c5005120940f04c4c000040d5203481840800250f10f0302c01c111000b0400b145011500e00800c1c041c0c11800c004202d0380d01640e80e0f070401c1e0307000240204078038025041000f07410f0521302c2203d00406140f80c1c06070f17800001050b1703403182d00006581c4903500410032400c240c2c080012440b60025404200d000b410b0074060006054110303d404420b40300e405a00c100901010750381910400c00d40240075812107a1420b000031440c1c203440120754036480580204c1e40500c036220003845407650542c07015040714950355a880000016038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 146474127 1250 146472877 146472883
    0xb070f09030f033506010e12030715020f1902060f060d141207060204030209070c03090308070302011b020f161223070303020a050606040203130803150a080d020c03 72
    0x4040075184016940d0340d080082e000d0342c13050000c8582094001c02286210086115182528a1340803044019005101c1d403941c01c4030140c0f414030412120300c82d018001b10741d807a07500e0194440103001043d00a040c5042c1500313560440d0450440885c0ba640e681d120b04c000d640f0141074400010005124440020319a4000c4100705805158000c201d080051f8041e161981052203043e9960428001c960410141c0c01c0c1b0a401840303410310445000da00d541c914010009440d100404030014412010356420019a2112015007030381d601131822511000740b070030128010502202d05070040240108a0402140c00242800392803031000111200000d44055051156803944150103c3d419040010302c0040c9a00c5410f80c01c102040ca407560032510383c00a064608070b00c980c42607002d600203121a4050000031b1041c154040c009450942c40c50a219444034075507c1810300190a800000c030225130b41e0302a030309080b442414000c0c40b0b500103586424407a610b5642011014004d0300c00d02c44070312034505000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 146475377 1250 146474127 146474129
    0x50a03140909040809040608071d0c090f13060b030408070203100b030c040f0e0604140601060203040f090207081b070807141c020604080a0318061704021e09040b070f09 74
    0x160a118054959a132019140c0d0828140c00d0b5120351192804039050f00200803240013000c82d55010380f19103100e41ca5030514524040c1246070000c00c02c200c002e84c3c5490768805101042015034100b250320307550f03000300f000428081c1c00002024500006000c10b00110602a084181c0210151501d0041d01c40c145022102e151069a80640025161407182c0c81e0a51001403c0110f4060108070341d904042081c0c203101d01260200d03080f44950307100d010300000800030b59014005a000441c0392a0605600d28200150740c8034000241d5000078919040000382d0065070903079802d00000069001d0b11016498580032a03001e0108144070b210340005603611a526010f41100c405040c2407045406610000a40684d000701aa00468204000205450b04100c0190624000d039a803501c043c0e84000d807035500070181e40c0010708110f00211030590f4011401a6103400076411140c0b1100d00400801c60000020b00d00c030041d51040742c1d5410032041c0028080300d18403034801a61400d01e0104401d20607a00b224103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 146476627 1250 146475377 146475379
    0x50403030b040c020a0803060d0b0f090705090114150d02160210020c01140a031e060905010609182d02070611070c0303030509030906190801050a15180e0103050a031409 74
    0xc04485d001c0303101c450056030011070142601d04c100f441a1100798400c0d409031280c44000038102c0c10001400418002c08003e400100da0f4000e25501d0070b010441002c541203245481810f41c006010740c100031520460764000342c40001591500c0005d600780301a00d24050003a40a1009441800034151000c504404c103540142c40d50807004541101031106a00007401c1c4100341542d0b01d044e15011980307d0f5240820132070843d004582d260904501c070082d0380c0c040c3d20043c20f01c0401c072414011140c802101e106689040400041c00ca00325060541515581e440c140103800c803e1484050a00029002450044d02501050003814400c010172186131080d000040c02070200200b051000a1080c0c11654210a203242100c3c100103810340040c00550121071b510a44203039803045401c4090304051342a004240890340c02161a1810300040040b0940102000c204120181202c400401040405000d0440199840c005607124030700680c0e030740c414941c10b0300031488840d580303151040d18030101c0d200050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 146477877 1250 146476627 146476633
    0x61413030c020f041e0c090317030a0b090c04210f0305031902040e34230711031603020d02010503130f0501020406140301050306070c1401050a050403030b040c02 71
    0x4055102281c1c1e00300c0c1c0110407607016501445009156561340035400c240704061320048410b814058902d022070700c03520580300902c080004200301080b07080b004031089405100350ba560361741d14a0906001800c008425961180c8043c041c0715100280c40042c205455a111a810a0b00021240351803202d8070750600a2558031500c02110002e44035401841e041402c102214a104102ca01c2040907600190000404500d4000030400c07180521881c142015001413403042c100c004c0707d9a40510340100f8a010800e0000e0307840c1c49011030000d0702042c0146920000351940b121428a809031401d049401c12912a1152101c640d8210119038480c0d0100d0783d0040400080140680c0103442c030fa00020440780383c11201ca042000494050201000414030400c0010b959500f4000003924400c2c4c00ca042e00c00401c810320040c4102c0d140050000c2c0c1250316410711103d5050185010007170410710102009035542040140404502582c015901980c441d03141070017220b1015090204550140400703400680c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 146479127 1250 146477877 146477911
    0x270619060509130c0b0c0109030801051009140d0506040b09010c051204030f0903061503020109090b060405060f0c030a0306060206070507050d12150608040606050901121205040f03030c0614 83
    0x303c42c98000c541d0043c428403d4203081e90740e0b80c1c400704890300901c003810450b07512071042d8070801da80300c403c45024040407a042070f84081c100d00700601240c183d00602407061169040d04001c4d0740c5030050300004c5e5a00c28111030f5a0725142c40c1496031904166000c2000d5824581c0e51203105006800751110540914001041030352562400c5600354a40903414040c402d03400404004110319000d10794902c0c2485648a001d14a14400140032030303496031242110500d82044038040c2d94a05044904039a01101c1c0207448203103225042c0ba0301d00c115590042c2621000880b10f69094041d0490030480301c8640a03180c595844603001d40c0c8034824160001e025400c000c51501d46540a98410a000100c0b030700000748102003542a042c81b034034690400804960b440003040304011a03805010040c05042d1406083c40d403602040d50351200381100002c18850101d805c28121901c60402c0d10300500c446080d8813840c42c0d4a00700074194a0042005480b0241440d00301e905042c812100c3e0742c0900403c500c01103d130 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 146480377 1250 146479127 146479141
    0x60a0603080f030a320903040803070b0c041d0a060902030609130309030b180c0a0509040b0c070c0f05040f0c0206060f01050d0509030c150903040509270619060509 72
    0x40da0005000c0b004241d541c554079032102c0380103050401c01e0542c0c07481c9078084920440402e000f2480041c90030315647c4c01040b00740080d003800700c02d0302c0c2e07201e9010410500c113803500c840340a0036000d6a04010000111055504040031810300d005018080303602d010002140c890b020441070348030884815821190040204200b00812615400032900a2400300c1d011703902c80d52001140081607941c29000340e480319614142c0300d400d200760030a03034200b280c6a8119915010109408460080001c0d00f80040d03c00042d040f003011348211051180d020101c03c10150701c44840c11300100c05401900d000c3ca1401074601c52210a43c4262000e50300030740c00900c45540d82c40c081098040c0f00c0d80003641003060500080c01c482e0424000e003805400b00c24050b41e155030070503100c103240001c1400110310a209000c00d0241000020044409840040e40c140202c0d0352050441e0000341d9484480c102504807090b020010800b01280c035a003d4907050340c0020748003000340605010303580300d405956403100d000000700c1c0c14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 146481627 1250 146480377 146480407
    0x20405120a0827131505030604050a0b1305010e0601030b07050309070902090d060608010e0f0d0e13090b070c0c080d0801090504062d15231f03020c060a060308 70
    0xa40802d180607070070b101d07483c00c0410700d004c030001c0c2a041119100c54400d900d90140e00e081e0700103004150010b00181c80c254a4683c0d0f038501700c0c04060869125031000c03490100f60320012a80701074200b4000d00c442e07240300c8071166945c04c003440107443ea175460030086084a841441124020032001c4000e00c0700d5414803141c0002944000a02503012849540820000c1d6807070294174020018a000003450f1040c0e400020f00b00020184010307a207810020000c0e00c5075070000c054410240013034901d91000f440307402059000340500a40a4030f1200c23114100424598003598001d2994030440340c424205a80345009581c03040110850008103560300e0040c440840d8541c040d82e803060141001007840c52101c41c0d03420507400707151a11040c102d55580d18610400c402d0165130300306402001c41c1d943d21480d00011001d8100b65407500c400704190360200c012a90764444034114032038034801c1c00008410070100050700950007404650340380c0c0550b0700080c040c281144a080112500440d00914280c012044181 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 146482877 1250 146481627 146481667
    0x4061410050d0e0303041412031f030f12090503010618150506070f0605060d0b040209060102010f060609140402030903040b0706020c0303010b0c010b0904120c0303020d0c0201020405120a08 83
    0x104026040c060700b600420700c0d010381820101071030003441d5241021709202c0f4410807035020003899944904504200c2d414107804490780022024440624400d10000300c24449415900c0603000346403012a00c01030058800c0c51900050090b2551102190b98105050a0311030b0f9200300e20461a8045940c190304002d07800804a240e1800e40d4600c04645810001300c01d5004803070240c4041c50307000c182c0d01c1089401c1c0314168001000315442d20b1a403540355180b800d0108001e000a02402140d808602ea40e4001d400404d000c030b0460800388400d5072590801451441c0a2040204150410b5020072080c2403500c2141c7c01036010700007540c98541020358620032940014800c0312859400c0114400440060015501804804049039900c1c4042500c080c2501c4480303543c3c600c218100002d1100240b11051f4601490031581806d4060000c1c1d401d0550003401606070340707040c160410003042c490701e03410750092043e00c0b400c48811075964260300000344d46910715023000700581d030300b0040b0300d040800d41c00d9861 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 146484127 1250 146482877 146482909
    0x109020a031b05040e13021f02010e0a060e0c040908030c0307051e040f05040b03100e030c1b040615080c0d02070602130f08012a02011d100506040614 66
    0x100301e1100014000034110712851002d40014000729081c040708039400c20540c0c009100c1c9484540c040055000960424a501840b420aa41c0900c015403218000e4114a070311034603030000d8030840e1145082040180280d044000d18600644c245a000c916203403040503d442d03000340440d801c60b0780e450030701d1510350300c003500000c00c0c03100c1402001c0d000080117412402c103a25085c41561507030701e052040300d441051600054440c90821800014940b800180c031801003006800c089403505140c1d110078190b20032204285c480d400340314108003040c1840c980145607610162000c008071130b0b8500741d140d800201b1088050008801002040302e0a0034000a050524a616001407070040944d90b01c200720390092040b44840c441c20007080003c003141020300c8005117698402171010751a034540340d01228040c1c014841001141081c80c00d0f0542c800d50155951012a05010184001007040c07a0342d60030b0304040c84800c180c140000034000c0e040502a910464a410468884a680b69020810aa40144005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 146485377 1250 146484127 146484131
    0x10510050702031b03010f02160b0a0b030304090504021801210201170f150a08030a081f060507060b0a050a06030c111207020910030206040b03070207030b0c0309010c0806090109020a03 81
    0x8201582d01032244c0b071040b04e84145038003400d09440c0f050509545010680d01803007441071007035025005015454401c0d55a00041c81c00701a81d580c0d217848014400c0c00324450301448045000716030303c00980d00c00707409140200e91660b027602d00c95040c00102c000c2401402c42c4604418032441408201f014a070ba1481d01c1410b050100240c80030303d414030218111111820f03c080d03581031003545c100298109100c2c542c240c81c6001c1c1c0c0c1d0304201d00c0030342d01e110355055201084025400501d4000520300c20045051054400940d2143c3da00c40040241e04004819210307039190101c40e006c180b50031032581d0222807018082906417494100141d0043c00421440340600c00440c40d19079000e50184001c02003425101c0da82622070400f0b0041c081611b000612140000c0e24201c010700141e030750101514200d450398130060340d0300c0e80e40f04400c81c01c180307140c0d10061900303410b441480440700b009405140700340b9489c402000704001c1c03510216009607090352500c5c1c112000744014451415a5001090700c94024140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 146486627 1250 146485377 146485387
    0x2d0b0f0a0e100306030b07080709060e031c0306030209010e010e0402010c020102030d090503040612050903190216030b0f28020a0e030303010e0406050f0705090f0103060e0901060f061701051005 85
    0x305820310400c0b0342c1900000d558a8051040020805035503400540501e44039a451426100140c00d1a6650140c50103000160354899440d580411556101a522100c210000700820748058050040ca01007244210041400424a6a826040c40e4102c0e40e01000051880e1110780056645109424043e81180010000c45e412140540200345c030a034810b2000315a900e1600c48000c061000c030f481e180c0203480c201000d000032010004255089002c48400b07040034982d01e604280c0c981522070000c50300c0b0003201e4400000b8840c000ba803c510482c2c13030a881e246981d880e002105a1541c1c0541181d008500c2c9100f940b20a10b2030b036020301082003150a00100300c100030744c0042d02e141c00980c009139240380c0c00820003082000502179030750429000084040c00c0d05080c0b0740034016004081c4080c1c014807080141480076032080d00184010320400ca00141a4180034142d103000e0921405024000c20710f800d800a61588202c095819000441180c1480f690900003001000843c0001c00804c000d01400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 146487877 1250 146486627 146486629
    0x20706050403080906180703080309070f0605031045020c1e0604020108130318030303021905030c0f07050a0204020c0703061a0114090d0c2d0b0f0a0e 66
    0x210303460069020340c5412002d0714001052500d02000100b5000d510003002d4444451000001034000c00c0d00d0b80700514903103a03900d503987c052500da190740c042012044040340004000da04240114004e241100340348600d144c49840608440d00601100900e50102c219844099004202100003102c5102450342c1c40794a9502400180c0c1c00800c82d00040c0d4100c4000110f010080c0d0828452404008029000501d09900041c0c140d401c010203000d2401d0090340c482c020184504080080303002084441680c05031281130042c025080354071010700c4000c42c103050440d14ae006500750391044a4004200d4681301820340100d0094120b49012039480c4501410035005a07158000350210440b180000c0c8445407460400c1d1095640c001ea0303600c0c0d203039641029400c059a2101c010404134080e601c4442c1d0f03d1111030b012035014080000003411400c440300b40131031180c2840d4815203045034120805002441020b266010014040c803c150720903134100090581d1403600f801a0081c103065040401c0d00710f000c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 146489127 1250 146487877 146487881
    0xf0f05011d030106091a030c0901060507050a020301090317090705061b010b030a11100801080c2b0b0114040b0607110d140a0327030209060d0f060e061f03020112020706 74
    0x41c021050702606e962501d01d1044010341400c062004c1240244501d007001c0020807100541800f0342401c11000181450510000b048407401050340a4020060509a418024115101600c1c60500c0c0d000b584080380c8a5040010b0b240156070b0000d202d980341510386038240410744a10203021503d9500d9075000070141c1c0d003e22500f0609805402010080c2c403401040003220080d1044070402d0196403c0107100460b000200003125541c160b0b845c2e5031816401d0741e4040c140c1c0304906260070001600e0680c1c4104440f041800d41294440f400d00412012004200000e0307800000d1a2500603005010f102c0c082840610045500a006031180c00303462400c1e10340907960210041121038907030101440c13200b015442941902d880130340340308003240203000691907090500315101c081c1c0f02d1210007003c00c103542d6405461001c1540e02c000d540880404a02c2c020024103600c0c00080020700942c0d000502d1000784249a22090058030001c0111a041d68015914041001540c0410550a010020000d1124 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 146490377 1250 146489127 146489129
    0x114010803130503060708280203070309110418061a0306070201150f03020603060d0201141305030705010906080414120c010906110c030403020105160c031b0f0f05011d030106 77
    0x119010756640c10b48000c118082e0b940550065009074401002c21070707103031b602200e02504155800d00b0036030018030a181074054500012103000c042d40c030000a02607002d4040d44840b0311240310b000c11109684d4000c040100311a140c40840b0300b410f61034407039100005c2c0780743d0107500318030407100081ea008608040841e20700502100c0078005070395a04941501c4a40f140c02400050040180050782c950465011500b40d00024040c540221004002c40c003c41e07000d0710380803241445e0707180c010f6214107560500301c00c400301501c1003601a00a90a011809512640c103540c107030350345074541c1601c2c0c4e1601e90b100b800d5840c100c4050340950103030380b945030002c256041c024088244181e00104c1c020485040000446e00b0709a0041d40264080000b500445004000c1e242129024248540c442d04903402100c0880e01c42031008190a114940c04010049605c000414840a0550b00c0741074685407114003104046a001e4000300ea803e5103020030656201c0c041c280c140c100c1c0104109540d0b00b145010074295105 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 146491627 1250 146490377 146490389
    0x1030302070303080108010b06160c090c090f050405040803071b020a090c0f090807140f040603050312180304120201050714010b0415180903140414090705070b1503011401 75
    0x1c0c108109156100c442240581448002000700d8102000003603122310071440c50111180c4920348034030030722010700c030703c18000d14803064180a20056110018058041b13030150056005580700f000c1113a0800d0f21070301d889254440481451629145010341e840403591948011075000506003070016150002620010716110708003203100b03529140050101000d12400500304003041808101206001a080c411101e801038070211048402020031903007000502c040b900141801c070300008000000008000c1070200c05985280d64856841940103c1100d142410303ca500500041c00581c8140b8000e040e154414103240b490202c0c0d0f6940e040510350a07041a04213a552003c952115080901403511158040040d440d80941400590082c14803080800348445030360300600306c201800b4420141d058045018030548441e13a500d0781c01d146490201c02c0340e00500400020a542902031401c1e0b0f01043c0d440040e03500140d43d48812440f0701001c40f0301203645503488291940c031a001000c0c6031030290503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 146492877 1250 146491627 146491633
    0x9110c030406080f070c030c02100207050415090c080f0c0306120a110f0a05010c1202031b06040303060501090803030a0b06130306050f130b070e04020909010e0601120c050d02030603070e01030302 86
    0x19080d41c0c11101d41c03d008001106018140d003040700007035070004008c649690b0440f000c070322010000c08102d14000c6103030880c607002840c00d0201215000402d110104954100009106020044000702c416210030b464101040081901058000341103502540c0d00c0f00000d80704146403841c1119032450704a0040041d07804031134915200007d070802400d01c0c42d00c260b06960740743c0c6107440c0c070f00000d18180c0c641d64040d098001500c80c19040c644240115004502071104044040c8100882180c8802c0151800c4001c030713141103400200c43d402035035000c08682984001d50308541d58018480c003c1c055550006500840400403140900c0d404607600000c0c41c024900051070b840d1201094400d800060241c105401d401c8801030700040840900581c0100f003842c26954168851000c10064082d0300880d81d030060120001050800300c04020502c0784509a07140580d070460b0301c0707100044540180d03441c00015410004203200d10340d1a001107410440280881da0b03150340d039101d00a800f035020b802c00c8005070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 146494127 1250 146492877 146492881
    0x31c1e0216060b0103060b07030c170f03070e0904230a1704090e0a231c050307030b01030911190515040315020901021b06070c14120307020a09110c03040608 69
    0x100d0f1180101c840020700701081414103201d0840401d01481c400202046005407074032082140b00381c0b048450003071090f00d0304d441301c1045401c41100d4100300e84050009a0b41e64000c0e01500c0d040a0103405550842c4070b0322807020121030032004142d0f03911811045445080c1c0903200261070712140014003e20b09005644490600c20420291031307a2440128440d4400d1081c00b010034403103a4505525045044010701704004c04001a0604c58440340d20540c01400340d850800198021009510802190358100041104500150700715040307008050010b50b10701c00a00035a003400c01e01130340941950040c02061039540d80008020406141041d01000d0011900b04108010500410252604c540341035003031141c5080001d54495141c0d40b40031114005024000c003d03103810089403000780c0c21420341403410761240c0b11100084000b00e126400703821228220810240040191104650b0003000c45030200d02e0302445002900314585002c00310071040040340044074080000b440105501d449003c024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 146495377 1250 146494127 146494133
    0x207060905040b131e0903020604021f0c0b0c04050607060e01150e060907050c0a030f02160b1204140d0f260604110d06120c08031c1e0216 61
    0xc0e01103580428002c0e400d1a0181c1119543e00780c0980600c400c0000c006160840340c0b441c0c50400c0f14078808040628a0718074408241603011807018821402038858101d0020711000e681d0544240403d50400148442650300000300c10102254001e51500c100b24105511000058810381c031411040350400c0ea40c100c0340740f4041c1c00f8007074940100000300040d24990310300a144490441d00034001031180e00c128002500b0b540c003603000c0e01c0404c0d040008440400300e052401802070f9001001d03000251240c1b0480c8000309502502450a442c503e484080c20200c91700c00410018501401c101c4a20007503e03607c0741c0c100001c000064a281080c0e071550841d40c1c0384400a807940d5000413801415644000d08291038400f0100019008a0103403070011b6280e4803050104414000e02c03440d480500c0c20084000b0b440007000c0b84958850b03004d0601690420790328880565030740700c0c4034059080d5140104201c002810198440e194075a0001c1d0008403160040442c1012640419003040103042c424040c1d2080c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 146496627 1250 146495377 146495387
    0x5090c101e020f100209041e090203070b0306030d03090804090e030d0515010918090510020a03050609040c05060c030706020a0c050d17181608010902030f0d08060607051507020706 79
    0x2444454009040b810300880e08203916100482c210441d00f940000305541b40e510340f580541d05003011044842e0030841c410300c015001d442d003110103034424420301c44042589641c46044a001e0781c80280142010441c1c05001d0f00544440981510010410b000c0028400e41c00d010b0388200c0103001024517034403120744034403a048440143c0341c0b48803c40724001c0d0301c001e40d800211503815680f181003446004240c00c1102c03c0038012102004150b4050400e6108a5042d0768020f005142810744003400b007640c6000602000ba5001c07540917107032429110041100d401c02d00000d003981d100c100b09881c501600d50f159942a64009041e510010361184103410921009018030030350345080303160181041c81781001260504001426a0920f600d140070070000c4000304000e4122034000e032902007000203a403044654003d000c07070401030b0301034001c045400c0c056210114943c1035403d10317074491010310344a200c2407140d1a001540704031180d1166041189401b1030003207190340f00c0c0f034160b40248803040c00c00c01c000f00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 146497877 1250 146496627 146496677
    0xf0212040f1205090a0603050a0f1a04180f020603040807140a120f02060105130b120109060b12030703030b060d050f0a0c0201060e010909050a0b010b0c010507170a05090c10 76
    0x401c000d814002d1500302d41d10764005d0021110300d8075002c91282c990301290001407850030300386a026440c0180c0601000502d0440701001001160200520440d54400c442d0798030b0700e5080200a010341d45c2440e401813508401a607000390081103080e0804045540d28154500d10503c681065440100741c038042001c8588030615045081c07070100381075586c0242c040d540d14810300865129440d40859215040312541c40030f4200500202010a80e80410700c07600e0080c2580101624500c0c100803003c421400d00d09440c402e0f600f40360004514004c1e194170120000c115004c0701034ae2020080040a191142500130b01d4013500305130310500842d0a008000c80100c800051910040da41001d8040011154050b803940c11515000000f00340024285070660400fa03c00400a008007618000072441c403481102400541e5080c030300070405511007071070680e4140f05020480c042c4090303580003c2c40300485900040c0d0020311880c12079409407132200006484030f4886031280300082004c1400c0f21910a101a124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 146499127 1250 146497877 146497913
    0x3050a050d030e0c040905030d060308040504060603060501090603050a02040f0b0307110606010906050309070314030315090f060103091410270302030412050f0106060507030e03010c120f0212040f 86
    0x181e070b9442c1d041c20b4941c4c40c1080500e20541c2d84401079418000d080c001c40f024540b050000b000000e0f01c030f141805064219018690140740f501c2404552680644540015250161106245d031850400201c01a19000300f9003100d03079401b031200041d441c0400213013401529000e80300ca0746a2074005002048041c050f14031034141e5201009105959800c51420b0098440d0ba1414550342e03561703100075615105d203590000340080300e004050305036400040301031030046203481d65624002440104011050b10151602c000621594001c0b0301c50398040c0d400010301a22a0781d200c5000c4000c0d42900c0d003000640308500b150141c40d0001100740011003861001414480d00c00301582c00d02d183c400940d240901e02401c0080f14030b61814400b8003a00f0841c0a0300340064800038850a40c0f920310003009908030620841c0840e40344400e240d81441c3c180115104400c1030342d508810510300080742c0020f8100c0644c0c40ba0500c0c0e08000c0032030000744444040d0f1049000b0700040e2020b40180ca00344c0c4410300070901c80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 146500377 1250 146499127 146499131
    0x4031b1a04030b1b0406030b0d0807050f06070804030203040b0d1e051f080a06020f040e040c1706062b08070c0f0503060f0601050d1b0215010812040302040c0e0a03050a050d03 77
    0x80540c40200c1d41070710286d481903d400180c1c800310b0310202d034810340c0110b000381001038007140040c20840c00007030a0314a40054016070700340c1d440b4002c003a205080c09860040150b041403009000307488003c03002e86031014480401140d040c0201c06031000e0500d2a0315441003558403003003000310381c03408840c2c0d0341000707160103034070a00c585e1605480c152901d205110050842e40c002484084407119501510064825814070101600300791603c0c8160346400d00c1030f120000da11140441511002144071031013010060040408074802284281c180d400300b03070b10f03145e6018848050700041b800030000381c4450713841151512981030800c6440c150440c20360348040d03c01da0115082100c8061240000398200d01c00382440e40e20344442c42a840c0c050100010201d40500c0b6480b03848880540c0003a50481c110500201700d0350326603d5200003529a02c0e200b015000e110020801080142415840404150344c00e02d418170030803040f540041d40c01c07103a0754419105540700120340d90500c68140310007561602d15041c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 146501627 1250 146500377 146500411
    0x3030509060706060b040603060510081e04030201020417030304020301110f12060f04020d0c0806030f031b0c0909030409060501051606090c0801110c010e030c0304031b1a04030b 78
    0x400034410301121902851020500208000c0c480c0c0000340501a0710f44020f490300d4032900c00500409203440350a1017030100e80102001c1134000d40c1c42c503008454401c441d44029001003441502414003500c2181159405c100006a0002c04041041d54030880b0002c0c55584c1018010107003541c1c0070f41c80040404808025001c2c40c4950392080311080f2200b0060b400040e52800d0000e03881d00c0401007003603001400003400d2240941c040d885810341403002c0e01d869600e03480b100145031703880c1000043c60b08036910400405285801c06540d02186444007800c60301d0780311040b408100090b4040d0380f984025800404d05012603403490107a400500401e20b0101e0601b56034029040800e0200c8a0180100c1d0b034072000003090280c0700b54510048e201c403900a00c2203e01c00740750185a5070288143d407185500c2d2010040200e00c0101c00c80e08105142401142860f040d0b8454104502104800209550540313000143c0040000c415510201c110b883e0240c03264558104102c02800082003040000c0712128 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 146502877 1250 146501627 146501633
    0x30e0a060f0c150501030f0212150112050c0a030f0212010b0a03031b0b070e0a05030a0b0f0601300606050901090306110702220e060f07300506030d0903 67
    0x8480907000c4262034404011202c80c1008045460455100c10000e82000e002006011103210100782c00c038402c3e161000384500c0d02104984030031010b0300c14010080007800401c04400b045600003003050040050380d6680f040400050703a80d0344150f10441c0d10001d602c101c2c0c0306514102c08001440320101e402405403005800000307078072084038040141400a120000030076040c222030341c02030855000c000c01c19982080307080601400c080448032031081e41c240f00003160344e0402140c2e0448881e484a408a25621078078580001c2d07240c010940f504000440c150300d40c52007114114401490b90b04000c00b10f60021200101d010f4070100e8209005003e010403082c0780d180d900c0360503581165042031000403040e81d0800050700c10f1141c5c190196012081000c080d904240303400c2c6031003490301082004c10031f81120b000b40c1c5031a44421900341d900d401074840002c0400e4000c1b8401c20b007449049041c92a900010304c480130701140072080b0300e144266100100f0695090810102401210500700b080d90107196039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 146504127 1250 146502877 146502887
    0x106080c070b0c1c0e0f010f06050306040602030a020c0304060c0201030b0f060d050c0c120c01050901060b041205070902030403020f0d0203032406130e0f01090501030c0306021c0e0a030e0a06 84
    0x19090300c0710b00b5000240c44800c4000b0b804e8284036502065014460280c901080da0703503841134142403840c19403070702000c041c00c2e81251280404846028010b408280c1e510b1300c800700203400040407910500d80810080140c420148020005400740303440340f0201d101030380001011120890728150180140b100442c2d0a40d680d00103842602142d06400704e1681d95040c03002c4040d004a0201c840c43d81315607141c00344034000f030002900003004180000c21040c1c1d5049120390a8843e50301c2840c00d9a4410001800f001303014491440007076004104441607142d41c1c2204d0000c80c3c4c000c56041d00140c000e088000d000340c00a201c9902d00380c1162006604506020850001b02000300c1003000080000c9021014242c40f44800d90780b6010780421890f0000d682d41007030301e5402e1400c40f404558207400034008200c11050f13100d2141620342102000560a040da561000254002c000000b208820346a84500c0c88000c2d018070744601c081d800103044154064900640040d0700c1c11002c91142002d00d00034840e107a40703c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 146505377 1250 146504127 146504131
    0x2070b01031b0329150a1505070210091809050c1306050303070506070206070516030813060509070f050105030c09191502030301210b0403030b01030f140106080c070b 73
    0x1001c00310100d0146100209100341c0b6070301c0104561002d00c5071051034062a90350500522400e94014225503501404190046091080b15800090801e0600c032440d480045118400103030f081552504115030002a04151003041410010700c200c2c0c0180901d030140c10001c66800e400120510128034541d5a080d02d510100b08424010107094450744034403c0b8a40040e0002c1c880a02501d540d081542071454490390100d4900700544a05004036101c24442c2081760055003104c0d00038800015180e41c1152200390240c6412801124540700e900850064841c40c0c1c0150854030050000d5071400b2100001c0c5852584283d06101c0c00744104180d0303581400850320800d0017140c4030500425071550b0903207c60076580281d0800003c5400000c400c5400000660681d510b02c0b00d00b6030398180140280f00088000e881c004c00c441c40c0400440c1c0000c3c041e820807650000d0506000c9482e16040038201d0480303510744061074180c0d03090401000015084103c0d00d800682c0450707028582162525030781682c0b100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 146506627 1250 146505377 146505383
    0x207021305091609050906090607020309270702010905060c04030804170a0b041505101206150b0c07030c061115090102130806040b0703051e190606120e0102070b0103 73
    0x40784009401d07014180122070720800100c18410106845400c07450040c203040f174842505200e100040303064203600182d40c51060030769900440c900345403582881480f41410042c140503840c1500b1240c1c4030bc1007210480d01c241c2141e800000c07429981e0a00d94902071003d031a451107490200401d0007c91000c0302100c05840a54420880d000210840a807503c0c090310790280c0f401d0b80f1601804100f103545669801f0315100d500c03041c445a00c1c1c000c0f0b0071240303e206228460051206901d11000240142c0010117004254400c0c601c5240d40c803c0407200350380c4001c60840d1160800b84041c01001080c8800e14040c160910b0034607107401d94101c043d81d43d01e01201900d0050014100000c6000d0f2007501102e110b07100080d44070001b90b80e2007032080e070703101c0003541c080701c141c04050000303003003a4860300c00e0700d2140c0110f4040e208100800200c1e0702d040030b4040d0008026043c1d890700d89110700c80601517035009181c290341d108103404c8200f042d2000c1740c0c0101140e00c0c003a4010031900020400382c1d1205819290 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 146507877 1250 146506627 146506631
    0xe0d020106142103090301051305010e03030f04030e031501080f12160f0602130909060b15190c0503030c0c0709020f0406050306060c0106080601213801090b0a050402070213 76
    0x243c1658214070714010100e40c59459800d00c020080c01c030152800c4c403038070b40e07110790020700c0080396a070001a182c0c0011120032039040000f900140110b489080c002410780310180030f4800500d004985241782132001d80003120580e002102032445184200050880340310341d005403c0c104107189014410410803001c0162403007d01d089000e0a02600e541103a03074013038244040803039403642c84c03210760050040c0c01c4041e10050726082000890382030100203c0e038117410310301a05140c06c0e81c1221060004c0416003011007044505220308001481c02c00c0114010b61f09040d0054880e00000341e4640743c0141c90700079949075401880b8050785014490180c80c19110541801920780e5039907004140305000e030910a00310f56082a400140025010440303a040e03034003041c0d142d0500b15044041d100d0440d80d242c401801941c00c0e0b940300f1a003441c41c6030604080001070051622181c03440c000078801c4a002c2e0400000740ea074450f00800c842c607003481e032080104420b50341541008082c1d00000c910500c0841006a51a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 146509127 1250 146507877 146507929
    0xd0315031416080d08090a020d0b09010b0603091b030a081c18030801081209031009061803020c0a0504140a0b120f03040504241a0d0e0d02010614 64
    0x806100e203000c800c03440880c9180300c076590402244d54015155480000c42c0f10b41000c526901e8000c100c440c5484e4010701184102c0102d13a4808280307000040c61000c09540e54081081c86960741e200540c0900c13034000040c1080400e081e02044031400c00b660551099001845010004500b82c043d94000d04095205480188001148001415001080328130f000c90941c203010405800c9031455041e40c541d41d0840304d201480c00d400d095244200400700d517269000c40710788480209103404c8480100d11904020440c1300e080c00f4041a4942e003054102c0141e0491213540c9142c0c2080d40c0304c58000c24084409020100710107904815845004d005100203541764400501e003529000039070121138010400302c0f04d1401c84030329101d489410030b01955100c0c5082805031a401005c440d00703868206030400e4001740203485d2500b144481200c10000820703100c403d01404c00152014410301400d200a103014000e000300c0d03500001d00b181d80c16000f8040c1c3c80404850f00c030f40e980ba2010039441d4030101c0c00900c007081d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 146510377 1250 146509127 146509163
    0x4050a0b06030109080301092301120204051b13031208070503180c0a08030903011107020907230a080702010e0d080610030f060b0403030f1e0c020f09010e06030d031503 74
    0x2404c00c610f00940340090000000842442a03070021440442400104190215850001141003070a01c42c0380300c044492112003003d40b50030780c4425002380d403172025103000300c02c42070704c90400d03400400c191030b4040c805103c03c2082c0001d031214220300c40c03068070b40b0481c289403200015156020140000e10403000b00c445030011404108008524188020641c0d1001031351203500f9030340c0764400d0030410302a5090030b03c00d250244e40e440a41e80700d91b500424048895681110445410002102c800000d80d1f0391004220340c502c030400204464882c1d40c0e43c22165250194001c0d0940741080240b498541c00060b08404d4160703ca030660380c1040303007240d2501c0ea101c8602800c4018011040c400b111180ca801d40014001c0c107100020b00803079200351960501d030018180e05807020b500694091410b0000040d000070558882e41a00303c11a1000b047c00d010780f5082c0000c902c1000098000100c286e240000b805030920b010048010301205602d000d102030f24246200409030001c5200c003c0401600195080c80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 146511627 1250 146510377 146510381
    0x506040b07020607150213050d050703030e130e0304090612210e0303180907051306030c051209070f12020310020901020f1207020406240f0306051c1a04050a0b060301 73
    0xd04c1e41048482c10390351400c025110007944208400b045807050341d1000921810304840528489400001810140d0f10715101641d8010400c60800c0e03004800c40001090081d06114103040c542c0d2250045883d68204000101110304079001400395148490524002400e8400000300ba1006010700f90882404007000351030f800f0a42c1480b55140c003010500c038985140208c1140c0d180070b411600807200f91076105040d10648500d803907800b0100300301070092018038002c0d0404052003c07903185c002d07d814440050900d1a480942d0390345100d80024408004000c1004c1808019191910402c03d43c5c00c1c0c43da000030b50312400740d0042c0c4842d540208004416038001e011409182e0445001d81d64029448402810b4942c00150300300c1c40f40c0e1404001140c800826940e034603031481e6220007941400440e1070240c503110180b041c1441016103075080400d00f611050818025003c0d070441130f1450448a19201400d41300c0700d298401009984000c000100c1e500040c00b084c26600328502c400952607031004240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 146512877 1250 146511627 146511637
    0xb010509060d090506160518030a0b01140a06020f0312040f0807030c060c030501031a0a0603120905130c020705120f03120f0702060613020d0209090c0406080c03010506040b070206 79
    0x291101d40481c150403030040c01c1c0c10290030148030b14240c51140c0e503120a426180003403008441c001410601070700b00c00184c0001810998640101112a00401769880b0010702d4001d8121700c49607031400480742c1c50f5050844819000c3c0c0100d0001c0e00d0003400341e000d4940d80340a140410324860700c202000c42c0078480d01021454200341c001400740d80d500050305020f0080c01c02c904080b20140e04e080401081d80e1f100f480340d54143d035802000e41c804038082d11100408800040e11120450f80e440300000001610b281c82c4a00c55105070701c078400460b29050410040e00048040854500e0400c003140d805c13168041502d1007515021201c0924a071100c03000c05181000901c0540e00e01e21001031260204442904600e01c00c203902c810089440d5194003040345c40300c1e401e0746c0f4035420480016092494600a40240c03003161841e103001070522110400181e0f07804410b58440c1e0450f08001802e1160300ea20211043c0e1140321000102d2540d4034140c0440c03080e00c00d91081c8940004041034140c1190740e51001c4070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 146514127 1250 146512877 146512879
    0x10806011e1b050a02010f050705060a0207030509100f270e04080403081804050a180204021c110901140c0703030e0a120b06030105060a03050c041812030e1005011401030b010509 78
    0x41d0000103180343c019510074554009a012580c100d800c2d40030180310b01c040b1003010398800e01420440e100d9074226006500b004104500f4000148042075403611101d01105180140e90f4552400200c100005840d120b046d0441c103000c41000860a0f4034003070768120000455030603050742e005a60322400e2102160180d80c000511441d400181400d019036404403020080c403049030700300016180c0100d080200c5000a440320003200c908030140c030143c9819400340c04800d000141c03802484120703000002c102c9000c0020719a8641c00410100000c0d680880e998444000080c04140b03415000f403d00c82d56441d19200003070800c015004280c0d0b05880344c0c440c100003451030a17100d4640300014034090203540802c4402e54029888c100000c1e60034a44507125104032600240a462100240000d00c40548202d035542c0c00030350828035001001030301201c000d15020506a40000e40e00345d0a003480c0c0c0c01d24010310245219a4103100050201002007180032600c66000d01b000110040e120380103079001d029402d402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 146515377 1250 146514127 146514167
    0x2061518010801021e0705060a09060608030d0603050d0503040308011809080d09020102100b150c160b070303050f01060504060804060e06100302030c091b07081603030e010506010806011e 82
    0xb06540150081c00c0b00022402c41c4004592040108074054061820041e050380e1020011800e046250350151810b01d014400c003140c265140c441c03840c9194421101921076035a0340700100280842070104030b04007000751034942c2c03460a05840c002c0000d00c041c041c00c900b019241c104c408a01045602035588261720000d400e44400d804800c3c00700406550f030099001d8040c41d07840d0340e108102c902c00c64901c4403000300984004140305400150b150001c02c030602e101c7c0b00d079100003034101c000000c4040041039a1140b1640d1210103140050503198050702c454144449103005011590708041610192205890030440c0c0380e80f10f043c0900070b0030824160180b00e000d0b0a082c01605503054205100345c90080d011035040d6000c000500c85008000c4a4070428042081d512200d000841c10050204034000c107680e904104043d130380c100f880001005e00702d012a90364202c1c089207200a0187c2540f2000900b080030701407504c440003a2070340c1104514511100421161203100c00e0040c1800e8010440e50040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 146516627 1250 146515377 146515379
    0xc160509180f0118030e01030501060504120c03140601050a0b030c030403050708070c03080d140c03010b0903120a030506100201020a14030a090c0902070c0e0907150912050a140309010206151801 85
    0x900b004820520b406030006100c4403420101b55010f4001c040c12600b484d507c0740e15144c074001244e150803410a0b0100c42d0000240000404034410210383d401d0b076111a40500350760b51601d030803c018901c017a07002080d40b4506004100d0662090016607500035003604005603580060300e0003540c00c0c881d60100503d000a4540088103100740c00000e0309100200f04410450b500034055a444902822210030291480401c0144041011240a03182d01103011b41114410003c9820040361500605000b4000a0b0380e00304008143c030f080c4000406500710350008620308030451400900380e41c06250308011385800000800e40d1910558046d61083d500b15501015042c1c0740c0c10800c02a40c84ac0340c05585292070f6901c01b150544140b801940103142d0007008202c101d00c0c0904a6078003101155504085c031a0704440000c18400719106001e45520400280c40c10000c18a0900c0403803603a80d005c581664403d0007061500d90700016030541110103042500c0a2170f100c41c000503109154030800084040741440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 146517877 1250 146516627 146516651
    0x90f0803100302092410020f0708010203040201090509060306071116080102030a0e0105011d04260d060b0a12020f0d1401031a0606030703020903010f0606050c160509180f01 76
    0x12840040d0b0340b00301c5a210701c035260120600d50701189034201080350314100740c50202d0362604c1e104086100d1840e005540024450484031401c0004540c45000140d40001c2040219030703210305410003425088401100c00c2c2460310120b0755504000380b000d41488a81c4d29241d00c140000c124500d81007003800650740c0341076102d080543c085e4105450042c00581400348000e201c45040c080c00d4140d03035048a18544c0101c684001e0700710310328094400d035150b000030360000b650f48012100c010300d4580142001c51b500c0f0180d4000408641d0680c0c851840001d05010b501c0d8010b5000c0e2200c9220703580c202015859806450188400d1f100c1da2000c2ca500902d8040f40040c0f0b20202f41d5014101c0f07000358516403854080b0503203150002000c07035040398001310420005040500a60103020f121402400018008008101c03140c03c8880c150000408107d001c2814248507001300000301c1070701c102d1240e20951030724180124000b03039000350201d1060400706c2c1d00c3c224400030801040c101c01c0c2c2410028440412151 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 146519127 1250 146517877 146517901
    0x3605070f0504050a050705220504090b04021e03070b0708041503140702010b0607020907020c0907050415020a0215030c0d0f0915180b0903161209080f0a06090f0803 72
    0x446902d0089050600150b549616403061038032078102902c8241c5080001c0368803204032425090744100c81620114007140a440b103101e51141948107400c000058181401040944519000d0303c0f0541c1c0300c908004400c0740c901007180301c11901404510f540310b621526004150340074640080000c1c9400314400c0c00030940c15003101c6e0451800600c0788016403103c0008a0a0f91107041406400801c00c0202d000141400400264086010710568480090f40e40000d21842ca003136403000c000540108041c402c026840351000034011032800200403942e19540850040001b08011b010404008030010340c02e22001030450301ea030b826000c41003081c034440c0e0003d48010f001420f42500e0303414048190015001041c811440d40704800910925540c40b140d403035500384040100f28001d540014080d0b100740c00c0690482100840c8604c0944101ca0b038000001014a03240340d00801280e40b1a50840903945000f19450780c0d00c0c4c1e040030000c10300b201181401d5000603a40c00009103024800803c115400c0fa540d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 146520377 1250 146519127 146519129
    0x3120d0c090b070b0c0d0204030f0f1103071802070c0803041d010e04031b030504050d03030b10050403020625080c01020d0b0909070b0d0b030f0a153605070f 69
    0x240c80310692030340c803031699000b540286600104015034500220320030002e002d000c0c01401d2040c4e8400352925883c1e80d18002c0c1010b200c00700b1904494180841005c0094003035405041c14016001010491310b449200321850903000d2200035503550005c0c2040520911043c9080680b000e04101c0741d581c1d603a102d9032401e40c800f018509010f022114004100c2e52010001103005940660707808090000300002c600100754158000c5052000070040011640c441032000c4031007501985002554106200a200800c410b0242510421070100001d000580d00e041c280e600b40050b2a0910030228150b0400d80044003102101410000d000306010344d60141c1500282081c415902040c08030f00903c0e41400324001d07043d40c3c16500d50304000030510035200c29501508050071120000318a581c11107000c04d007814107080c2e095400f034100e0a41c40f0140441e4039000810a10035030010800310707d2145140300ca4031000800407180d6014a056208561000503120070140d0700002614542561031151742018042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 146521627 1250 146520377 146520401
    0x1b0a05030619051b0d0b0a0509070c050601050301200c070509010b0c0114010810020c01110408010c1b0c0509090c030d03020301170f0d200607050a030b03030a09031103120d 76
    0x4000015094400c00740071085040d00c0042600c0c1002c80d95104170016000300024150000200d0070300040e142c3e9092800d41c0104541d407201902d20030b29007000c5041c00c1c016000301c0e000c0e07818404a40088030002c0c20b00c0d065250129452504d42d28241030042c1000029802607502520b0a0000725030a0130400c020100411410b008001e02c0001c0083c000b0032800902c6400402c1c1c00414920f0449080c6800034002e041c1400d00004e50341e440c1d40000c030183d0700550000203071a0342d41d10b0206001038211508082c02000c983d8011101c44047c0d0320303292014602d0042e10701498030360300424032a83c000c101015030b1001c0101a82e1450390b16420040080d00248a07884280440c4a089800b503d070200b40c240389a02c0c2500a059010450401510303d44a03121001514114458901c6401d40f0280304a074040c034110b944042d9901c0a50f01c0041c10358181c1c181c5039202c0e80013004030300560b0303400901c400b0889a110119107005100000020f040c070024122541c2d00b0b440014807600440345590281b4014a5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 146522877 1250 146521627 146521631
    0x306020d0f0e0c011709030c0a05030c07080a0b060d080f0304050622080d111e07060501090203010e13020f1201090c1e060804062a17091b0a05030619 66
    0x280b1241c0065070341d540e2003802400f1540290960680300b81d114111a0302c0564102142c0c942a00b040e4000d2910194883c10b4039a41c00c045440c030007403441441070b0401402d2440082c807480829807104000028064600d5108a40544240b420070007200d00342d95284071100200d580304e10f042d0400b242c071034004035640d100b05001c1030108004500c1201400089070381086d0381505003008100070200820380741d850321030009000e000b0914000b0405003144503034070b05440241d03120b506074641103083d100b06800201c006070051006101c0d46503512400d80e0f01c41e611070481c440000c481d001140f035060308084419081001d040360010002815040071000390712850044400341d50310f00810800031458121840703c07a002060070070050340b041c11501c0e007250054400252101d10041e00011920ba94242903484444403e503080215030460003200c82000c058440150030b01d02081400d44074040500b4403490b220210101d441c20340c4550402d04003a05000d801ca5405080407c00c1c601414149201c101b2118 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 146524127 1250 146522877 146522891
    0x4050601110322170f011a150d090b0c070c1203021e19030e09060a031e03030605090403081605090a0501082d0a060602340306020d0f 59
    0x251203240c64482290380c06018505000d00310096002c1807803d83d00d4401c40144003200401c0c2142c052141043d00d94062000700900b920307680c0501c0c2520807903103c5121a070b61000208246450742c084a5410000c2c003215140d4500c554160b5070001d040c664809041280014200708100704154003c280d118015003401c0c050b140d44144064001c01860302c01401604000e1031044090142181c00c44500d2095007036400c43d07214010a179160102ca407605800189400042c9801c9007460041503401c0308054440d03540403030646c0c4840c11121002c0202050050103880c590b0241031281c1d03c08030240000805000c2d060806003001050400141c6e010103d0081d01c200d244c507807901540480d500c515018203204005441d0600542c2d1401009084c44c08045410840395041154000e00415155038021a1205400c01c1c000c060100d8030150441d800355481001ca140545590100c00e82e0001c40001c4844000b20005200a003000a950703c0108004e0000c20200180d9600340c0040c0075042c0d01c144104045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 146525377 1250 146524127 146524129
    0x20129030705190308030403020304080a03090e07020307021f020a020a030b01140a080705090711061303020607050c12030a02071b06120c1e020705030d0c06050a0c120c1b11040506 79
    0x1070301400e6005641c3c00283c4100b0008540d9030266511030702038015242440e903520354440c245034100d03800710001403100c2c406001c1401c0d803041982c1c015510b803004504110003035010981c0c60440c09200c2c40f41c00c040410095955108004003058036a0207040344086ca41e4912348001c554901380100144100e2010004e00c60781441c41f040801c880696001708095490b120070302c000b05c03101030440000c011441e0130704811301c42c080003d28002c1131403c9080410f2440b90030b00a0400d040501010300b0840300700041e406001c400982601064900c203103513552610f03002200c41c020301c281440101100030b04640e4010021580c80321038110303022620b503800c08920031029a403c940d500d203194004200a40007e4509035080c1304071200c04d07111401201c0c0c0068440b000245082005440324001601d0070400b281040960b002d41a00031340e846000f0700039000d00c00320243c15050f80c01c00100c0442c1d940c0300c0c0f810306039103e04003840f280b1600791624810183d81d0305100600c0030f1103081d094000e0f41030201007455 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 146526627 1250 146525377 146525389
    0x3051b0901120203040305130e070906030203060a05041a040905160515070303090f02040f0c03110307140a0302040b13081605061e04090c02010213060c050a030f020129030705 77
    0x94003416901c20041141280300840250030190042d020400240420ba00b010300301e06000e80a803c032000c44034881d00e09000000c11240c196041101014010f0044c04415114000110b0585004460104100f5a481790702c1281e200d49211940d405414582050207100d4007240061100751100050540700d030310344085c0700307a01c007502e2000301003040c040003820301080c07003a071000d0141d80c4243c50b403c60807841070b00000c05030791720a804500e441d0388c0d40c0d0205102540602c926072121f646001c05030300310718001401410008141100c101d004a000882030302440c405d90441d4094100c1482c2c0c50740b00c15800789103d480711158042c001c0e1a20074412040304c01840d407503801c0700b00d90f00104020701c0c00c50640a2034180002100c0011010902403102154120304c034026142840019400180c40c2c82e04200c8908402a055001105000d4034074008000701e400030440311081354040c244a0031101c0c0d07541c41240182042d20a0b8030811a6803070340051503c41e4002d5000c00120214100c5165648820030404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 146527877 1250 146526627 146526637
    0x40e010b0a0207030308070219080d140906010902070807120c020f06070b070f180801090b1e040201030506060904230a11070f02030102120f010f090b030c01200a0303051b 75
    0x400360f0b100c1201003000910522081c1d90003400391054a0700c2d4a8007002104d02091168412540050049003440d208080fa2107501202d500990341c030301c110309004640f0381e03c0d85018050030725800d80000b51042403208035811a174041d9482910900c0e805040e9800400e0000180c1c4224451400211006018600801510036258114004040d9510303030131400d41d0303c8084d407107010382840006113880da00c4014040116000f4400700340041340456040ca0f0a0002000041041c40c03010120310300d0b120000201e000d045c0d0f0155084c03c0014554841c3c4000408030f0007038007040d5a120303080c503d02450002081f100c1850320f2a1340445032241d51605c80c50310381542c6044006004d840b605014080c0400c0304603042c071041c940040c00040c500300744884501032001049440c1c000403181e9000400001c80c2d50802c2d4001007080c03140c100080211040020b4076070440c640340d5410400c0c041003411070000000450009402e0100031910381d034441d464043c3c0a440100c840740103c1503211031364010320400c107040314 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 146529127 1250 146527877 146527897
    0x14030310060815041d0a060b0f030f060a0b01030204050604080a03020d0203160b13120503070e030c0d0602070606051e0a120c170f0601030f02030c042706091205040e010b 75
    0x5030032909003d041c8001441e60050302c00042c40c40845c2000d400c2c3c0d041c01040b000f41d0154202048001c00d1707009216089207a0f800301070099014811403001c544000c10542d81001c5c00c00301c0880c05412003030040300a8002c0782c11603940001c00240c001050701c0c000035000b04040c402e401351161082250402c2c0d07101e028000100e00544c8605a0810002d00a111400d0b442820401108075024403900c404003112a1001c0c0f44000c58000014081130642004d068183c5000880046c91095140c602050400f50008802000b59801140303030f00801605800c003a01510002d407200c03940034241c104164480b641000d54500960502202003440c90203400300d00744c20340d0041c4c030800113a868400c2080d42040b032004565640c1c0503a40045104020a01ca40781c002c45c001c3c41d8190300e01c4c103980105400c0c213100c1e86891b889140b4000007900e03040c103017004401c624407c44808103144111410000081e0036090300c028030318580c85224821554103d0f010b8020f0356000c030407580060b070b00d40d4201e0749103120f854803035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 146530377 1250 146529127 146529151
    0xa0f2102030304060c0203010e0d0c03090b030c090d021305090601090b0303040b1204050a05120304020a0605161103010f020f030f01050a03051c17100305010b01030c1b0c03140303100608 82
    0x307015007800f40c068103d2946c4003400000740d0384103080704582403c0204c0301c0e600006041d81100400c0c15800665030020349842c1804500d18200034107050708511600310700e6401034144070044c1040d5074446c1130840400f00070210a000618041181940b070b0300b02405242c15151501e04107180605000054805446115040f2458040d254100c910f402c032005200b101c0522695040800140050019041505581035100c1d228103042c41000307414501a00507a0030008240001e1003540b112904011216030000d5460701e00054940209004d405200d10300344d503140c00042c603030072028004d9006502ca0b00c0c2104151280d40d8a5104006200c1c4e450301c8007400c40c0e48200c51159841d2128043ca03150102c076403d2550031071100b020a0802c40307004540700422400404010801c1c0b040a006800170310f1401d2030b041000d4545c0f0070740030300301ca041f200d0755421007050380c60001c5c00c210103101072502954000f6460103001c140381601070307940d43c4102c1c0d042c0041e20250034006089806044428000c200040c64 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 146531627 1250 146530377 146530379
    0x3060a060609290705010522050c0d14121908071706190303030c09090b031e030c01060b0703021c08130204090b0c07200a0605031003020a0f2102030304 67
    0x245803440c402c07884120f1040d007807449940c010305903820000c3c0403452140001045030300d405981d655009101c841c406c4000300c00c401d685000a0701c04035103001554021503601103850342604191410405800c3e0784801d911a402040e1409001074028002c0e480680c00c0c560325000406008446e0200d05403071070350205d110010000c01c040c0d0304440741b541c400406891302c6007200b00450748440b400400c0e0300c04c0d400320741d54151400c10154404010406010342000501170740c038841300070a580d942508175414000e42d02c600c00d000d001c50140112125249500000e02a0f20f45031508424a50b000f07520450142c8268080e0511030145000018080c426585800d00d0542e645d40c0100300150384000200c0e0300c00d984610301e800181c05081e81e640203495038030304d060312050949050711140200c41444c02c094407901d00e50307113a03680d0b4070001031003503440c98130b802c0f078032034a400803100e503450038a82000303512403400c08011400340300800031401200c00b401c2c1c01135175800b580300c1c13034520091004c0360181d095001000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 146532877 1250 146531627 146531639
    0x303050910030e100f050609091209030a0b090c10090506030106030c0c050a0308060a0902070f0615030507061206051c0803070203040b120601020d050c06060d080715050603060a060609 81
    0x950003528030701030a003c1162484a040700d0b040083d400302c080e060b10340c0d80404880c2e210762880390070f038441c0050394a41810b00740303141029900c2c0c0d8004500e0660030340c00201004140c80a100d41c044035580011905c89074141101c225444000040c5881d01840340c03028185085481001c60f0011600040e1590349180d00f09403044015020500744032092102402182d000500104040c2000ba80a95100e9400d41042d10400c00d0725051342d03000350305003801480b01c400402e1a40e4960721031503520a800103540001c08803000d5907400c0300d600c060b10501400d0f81c00030b0f8058201515641c1d807891501d04008861b10b4100300007100c14190b024448500c034442440e030000d080d139001507800c01c19900480c0c2c10302c0c5ea211001407042d400030b0100980721481c10705000955030100420000b03040d090401d541401c0b0041c10241d90307000c1c01044a403184085c0300d92007013801550022900c40e150400000e0040b50f071a414648091300068821502a2058000040c0f080140c0d114400a0f00c0796941d86041c9945400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 146534127 1250 146532877 146532889
    0x60f040e030d05070503160e1f020d09094a010e0d08010806160509030f0a02041803080a02031302060f091011031218030c1f1107060c0c02040e07030b1003030509 71
    0x44000d90300801c4409d40461040381d03061841e40c4a030300e0740d4000c100e8a0500b220007481c80c106603000c040054113003211812085e107038003120030b141032004c01403255070400c80d003644151460442c91103c141c0c10030350b0100440c41e81034120214410200c003c450076002031030800c81d02007009204181054200d00c0100d0100b0121566244c2c0c08035192400a09202c0c288002038244420115102c4a65102061040860070103000302c03096095490351402000000d44c4024002290050100c40750341d600200094070a400000340b80040d07234028007400c0d122010307a03944c054581c1c000c140b9580300f803590b01074071001580b14200952500400a02540c100140510410b021002c090005100b107440308100b100c024104101074240301240800400d10702000309203080c00188170b101008405070404400d00c030450880d07801c50f04503171707805800050800740d02c0e002240d01c6208480001e50003420850071104e5030f4000501c0c00705513070242e41c013443d0070f441d01132512200c8112803200601203a0180680030315031402d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 146535377 1250 146534127 146534147
    0x60b0102010f0c0f11120a050d0227041416030b01020a020d080403140a03050a0c05010f1b090b07020d020f0d05060a0c0801080d08060405060f040e030d0507050316 72
    0x600000c00d0305040e00b902c4070251107a04498000060503804c448102c280e1000c58812035107410380c00f40a0b040703102804040309124850402081c040c0c0081c1d00315548029138100c0350425589280149400f041d9201d11045150b1029080c1c42075081c440b160180080c4041418054070103075172031040304c41e00700d402540607003140060300d419402083c0c0071001580301c40c504480036600c604c0c400c550b04c50440c42c0c0703c402c0517904021402581c3c0301c0c0740381d0000a0381100c119604035005080015541c411072034118058810598004a854100810164a41c14142841c0c05404141d1180342545031501d00402650046c10700c06540402c4010740403015003025604460798003c050070401b001400c40e03c03014608207040d80e04c0d00081c3e0703580460030116036200f50054050321440000d003000301007d02e0020314403039001c0c00f1584226a51404103c540d80c0301184001074007000307802400161150188513860b500f003101c91041207400d00c0009001c5e0351007034041fa4031a071260800c1ea0825030120004840903030348 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 146536627 1250 146535377 146535379
    0x902071a07021e030405150c010e390607030c121d0409020d120507020a0512060a0c20010539071514041407060207060c0203070e010806011d13060b 65
    0x1041001080b1511800701c00c2400412a001c129901c0b02c05201107403c5418002c1c844041c3d800c0101004050820608051000600c04403000c980591850301d45580d2f00621460b01ea00038000515402015001034181000c01c1c0998030078107048400e0101913a0420701c817010004080110018203c091034a5070006d10154006440080c0c1a03200d9035072134007a03000514480000c10300205080c07085103030603010100500003e560f042d0091081c110000c1d9110b2014280700640344e1103000c0c0c0c104080c8159000305460140d41803a16090005d00b00702130003000296074036440e130b0f82844000c0004102d203241e216007840303035840aa10340094103241c00c00b80d40c204040031500101b031034804204142d402d02545a110b01002884000d504061818600040610150440541018600700806500442ca00007103d4803030070064000d030828030000382408120340041d21040440300021447c80c200140450594100d290f03942400354440d514911030800885071502a80c41c0e00712108000394540d0403600c030902d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 146537877 1250 146536627 146536633
    0x305070f080726090f0105030402190b0a03050a06030f0b040507030204020403080d20160807080706021b01020403020a30141522031205010902071a07021e 68
    0x2090750744580007607000e020305541042800003800456012903000a00552403468014502600c413004144110380341c1c500d2a05006010001a041d0744400780804140b15101c001980403544424040525402000c0190002446c3c140041e940519a10424040c0c80e007110009010480941d10b0310141d480c01401150f183c02000c00000040c0c03a80c0c0080d00245d0f1050314001d4903905240a81070803134110700c10310b80803001c0c1c212801642110340001c8440400c9204c05090b110b020343c0c1003055051094400040c0f855100040c90030074418507a000e45129050054000480071094440c18241c0c0514000690300a0200c481008185400540380602c0011040c00380c45081c0d822140e21441e001c400025500c10f1011840d4464440060140d1394101010032218007080c1000c00180e8003041141c01c3c811072001071004074070181405040e40045144601806101039038541d6003000194001d0507040b40c1c90800240701900880c0c2203445188610701603401450341d40000010080c80b9052070403e0b51040c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 146539127 1250 146537877 146537903
    0x40221010303020c091e0610030902030a0804030302010501120b0c0a090504090302060609010609120803090309030a060606140a02060604050a020f0a03060e0c0f0a080c0d0912080117030403030507 86
    0x86014640218040e4000c1c0030081c082d042400750a080082c1415a046810101382da24001c41d2118144c01803002c0c3c0d240d103140300703001e44140c0060099007800b07903041c42a080c40d0420020780c44020420380703129a000b40240e0340d0b1030074484001440c401c001080d4601c0c00000500d0350f00d4030b10280c04403541502d80a010384c7d6480010404584a400c0160b00503000340040194605000a0aa00400741440d01c0c80d0068a030050714149075200782002040918000041520710fa0b0400585440c04001000d0b290129282e28040004004a00c142c4012980c0e0107040f4074100a18000d55450007102d0b0007605c600d40e10013081000a02004003080b03501582030001c52a0844004040c11003980191000541c1d40d007802c4200040b0500200060041300c010012050382034004805d580481b12181010001610307024082c3e00b09000300d01c81c488400d40340c501c406051082c51050b0207003649490312604005c1e41c0b54203101c00640c1e4001c2c0300c2c0100d94020081040002e02c140024802c003401460040507503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 146540377 1250 146539127 146539177
    0x13060b03030f0405031606020d260901050709050604230607080c0a0b09150103020f030703200405010b1e070f0807082808070507020d08040e070210090b04170910050d0605091003020402 81
    0x102816550010be60703540320200300f5625000480385c07001d890100e82c61401c00d8540884000d4020f1045610012100303040000403003a1901c1d010398403040c2d0310010641e01c3c4d8110325145941c88e6400c10341603610754001d2020410b00400400c81e088200c84048024682c0e80c00d40d000c2c0401b41d44000c1080750180329280340040400c040f0342c141c0550009000c1c201d002c900f00101004141c5206030403040803100304018407981d6a42005c1003800014804000c0d90b118581c0d400c00c1c0c2c812200e0703640042d0000200040000400241c81c009100440d4141490b264200240c5c1000b010710440504000114980c40d01007500c46024001510810f40300400e213450a000da640c803c0041e400540c0044413402c8942d09102071142c051254007007105901104000e9490f403521740b181c0980018201034074064901803082c0d500c00307c3d2002c4a001c03e6000e0098180b40100d080001c000750300c0000b031696110718240380400c2034a44400d1071402260808805031041d0300b59000c10000f5070080348000e0080b10704002d05514 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 146541627 1250 146540377 146540447
    0xd080c0a0605180705090903030a05060105070606030302060f0a1406060d0f0212010509070c0302030a180b0a0c020103050a02040807030b06060903060c030115080f13060b03030f0405031606020d 85
    0x1003002d0049010340c0c1880f140440a241c1820b40d0042d510580c00035003001603104c00001507a0380300031411008681c42d2034400050f1801d03c030b030302809050b580c14100088241500010070a0281c5600047c98029036101e42c68402105c0350100d110030303500380560118a4500d401000380c03690400c480000514074947e1001c07181242d000c0c1c007480302565044401000b891810b40b858075800140350420404422840d03034000e44034456071a0140038004400c5020400019410740c08024242e00301d24241e48084171f030710242007000003000481c00a820f0000150002200740280e034101e035a5203004060302030542d80c0394a0000b0009201c0d40c0c20a50034008d6010075030341000362a0103010108081592541040012000400743c41411403e100604041c0700c1070b50302c4190508d500005442c1007407200001c03864001d010b8001c0e00c44030766040c400414820751010101d1b0041044410031800c55800034407030502c1807160002482490050b03004220003541d0540540404020a41c104005078907107481c403030780469 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 146542877 1250 146541627 146541631
    0x2010e0604050d0f0b18071a09130b0a0f05010c06020702060c06070503010e060d120e03070306060f060e03011506140c0703030806010f020604230106050a0303020a0c0b090d080c0a0605 81
    0x103521101c4e04c001c04180103490390515000420050000c00840c584802d85568101c24814074020298040710000841d02c0c2c10140c4511f4080101802801d00c2c0340c9016401808030023101c1403041c00045000514a100c10742c1d4203040f03643c1a111800c1d0903000383c03030b4000250408101070381c00420811000050701c0080c4042403285100c3d486107030316941448090345c01072400804442c054000078501030b0104944081001c210442d5181c101001d62191020a0a1000d141d00040900d03080160100d1107205c0c028942080d290103680e01d600711807166041500342e40a220408003480800141408002e11890002c142d00e140b08900f03e00c2c0c0030440b1100352401041d41c1c029400144824180030303056902488104000303800c1d10040c007590800b62117003440d280f01c859101065102045070381030798442c20b4220303800804000301904012507985c240a9102d016400040381c0b655003050f000b003513161441003621640d0300d014000004501c8d1940d10220142c0c01440003060501c02c0700044c100180c002d0048038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 146544127 1250 146542877 146542883
    0x10216030b0c0c0304031211070e011a0a05090301090b070e06040e01050f0a0308040b0d05060301140106031e141e13030507021503040606090b12060a0b0a030b0109092001020a02010e0604050d 84
    0x40715002888c645410204150021040da00040b4010411a64800c0004c810f00850300321140e61002010400e40c2d007803007000d8079a6055401c1c00749440a10800242c03481c407070a0640c0351b042101c0401c0c0200035944c480c501504c0d0000d0600c50040c895814007541440b200c03c009050044031680741d80700d41c205034125910855440c1000991050440030078003942d0380141c400d500034002d0854400e45009810301c1409480d0415940e2009206041c03008003580c030402e0500d007070802004544402d02540c042e022140c1c0d4802c002004103002001c072000d41003a00c603040b5084010120f010a07a41120141d00403c0242ea0018201c1ca404600c02814802140140d10507200082d090345084c107950251500381580c0ca120700342c1c0303051b68040800041080340d0f000e0302c205000125010007000003103071015150409001200480000f10320181542d1040d81e4083c05010310300c40703410161000d000d0703005000d02c40600503000003403500700650040d101c1030078100e0003c20321420542c4510224002043d0b0810603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 146545377 1250 146544127 146544137
    0x181005090c061c4b060803040e1302010c0b0601090e0708061509010909020d090501110a0206090a030f1809020c0c040b06031e0406110d0902010216030b0c0c03040312 73
    0x70f84616140d441400c2e0003807261040d40c45841c454000f041960041c1100c00c04c480060543c00140c51180200c14030700000000300c0810005442d02c100c2940c0750060302030000e00d24103d102052604424160001609905940d42c0c0070b13507042603451002101c5c0c090301050600c00a20400b05070822005c0700c0d94803449203640c401c102031400c0e030100300589900071030000752200c04104140d02a640300600100303403500c1c0304015a403030302c0801c0c1c0721004200e0b00030050119440d01d03490072107a0407200020030b1450070b140d0031100140c503482c0d2250b8680140400c0140440c90300160140b125024020980c0b14044e90b80003204e9180da60400700e020790303110354030024254000301e2101e1842d00d043c1c444e414107801c081da0b00d60b00350310348601e003c0c3c0b8616804402c00004440180000c00b00f05154100c408016114241552165609546000684408a012400b500903d0503080e1400175002e10b1404503074010740116516118107022107503030b6116003440c45445c0010007022002ca0034419480300388205503916 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 146546627 1250 146545377 146545417
    0x203090306040f12080709050d050f070605040e010e01060f20011a032404030c0f050a0c0905060f21010e120c0105060603090307020103111c06050405181005090c06 72
    0x3c070b0003051211409240034072502509100b0070030740c00502102070b14009e0720a0f000c17550311800c01a2501c2c403403840300c0445101d022002300d800c5500c03502400c1103c12031551944180d80742e002c501c084090074022080014070304699542048e00c21051008a2030000c4d4140001d07080101640e42556110710f03220303c03004001d04422245044c100480a0b400c03c20301c0415007141414011000900d00281001d000c00500c0d40d003000c18004214503000c21154004101c41101038280b41c038052220052140c15661490240060780d68144200000c00c4004001c09402d51000140015405000c82c41c01c00390302903503111100e40b8801410041e111400300015103540d111540000e880782502da0082c0103600650080c801d0000a100c0003007580d0700d1590908003c20b01c0c0518a040072402c0c01000c4840006041c0041700003400761056000030180d480c1a1028441903444203849054100e508522440a40c4841d0ba0100a010998400d070381004240c0f050724107541d4081c000a50f10342048030844521040f243d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 146547877 1250 146546627 146546633
    0x20d15051503010e1c11030a1e030c2309030f03030f091c0f0e0907050c010507050a05090d1e1b0e0408040608090717010c080a0605060301150203090306040f 69
    0x20011288100b200248200e0310003100141d12503120344503039842d0a08101040300309501a134140b12940b001841226141c00c8124001040c2c0c051620000e0700b032012200e101d0000038880d0080618040140d10741d20030b404402d01614550b0345900305aa0003214092001080503034040c4141c88031040000d00543d22030a2214540e071510724040d044d01e10b84c3e4803400000c0d0240d4865003a100c802c028504006060f00c140c114180c2e13001d103c0140303065000c8941c108101286030010040c04000c2e810000070402c0740e0314244144c0700c502c1118641b0010a800b4062003004c0e1401c40a20031600c1e100310111038075161a140c218011110f0b00108403160980d1808880700d1141074108200109a0691306925600301612a0052403003640a05c008001d103410000e171000c0400c103d004001c00104001480400c07248140707600038030605480d44001507100011800b9207c0701e000b03802c2990350041c5111b180d41d281c842440e4661400d207220105501060256a400303940038801144124080c031200e1030300910030301d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 146549127 1250 146547877 146547901
    0x606090e090303100303140904150608070207060e040c020709020f070b07020c090412020c090c040f09020301210515090706030c05190f18080c0307050d08070609020d1505 75
    0x245034a209030702c10710030407511000b01050310301140c2c0c01d0b0400c807210049030348000c415032040070b503030b5504103050002e503180c12812101090304452007551074040584a50504036250f501d90303c1883d000402040d40d4040030702c5d0a511503d81e040b414012580b000e99210074142c203036000070280c00c01e00e900114036202481140b841c49907108020384050030240040600265103010040c10207800b00f5030b500c4110035203d008200c0502d43d4007000304943c00b289805440d8501980c464000d5a000c03445041000807450600c1c001d0741d050b900c6021518001d035034420f0403540c0700e6590b10016143ca20614002c04200010021014026050000508076142c184000030b804c0e0b401c01e03550317007003000806c10000503c40b6420443c0e00d200d4082c2e150a805103e1b41032400c139280710b41119205c0880300081030000740c816001480f45c0000009800ba18141b41e84c603030400252035500080545540010032041e00054060791000ca812071000740b41c50840c3c80c07507403502d40b44042015000703081d440ea64014008182c0c2c0d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 146550377 1250 146549127 146549131
    0x1314010b0324010308030a1404050c0102010f090809040c05090607061a010503010b22180b03060603071208030603011b020d031406060a0c080904021603111203010e10090606090e 78
    0x2c030000c050880d03400b440031010080c144000b905082001c004607184004c43d800800c04140d5010141c0814205801c14036155182c000c01940590f10f0070000b601d001003035009000e00c880e004140241040150028403000d00020241d1904205d02004004019a121805091403902400000610704035803100c0e82e20f12100141c0c50303810b0060910042040d1a130341c60031250544901321940805420506a14544e501544c0040741070350f1040750010103603209907009030b0346410102c040311042d4640c4403e164481d8542e01400d811104595422004a10180c00643c0c1100c0090000180a48036030b90440404002080080041c0c022242803480c40d0752502941218800300c00a18140703050407000240240b02e4600503909020615010751f00344002c8001b03494101101500541d520703e408100e00d844201e02040403004220702301a03640300803074005151048514441e0407a46142d007031407503080c06440001c0080880301c004420100700b6140501401c00107000740e0319640c10080c202041c0d50110000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 146551627 1250 146550377 146550403
    0x190f06050f0415020405090a1d06190b10022a1c030809010c02100b0f0d050102090a08060402090403030e030706060b041401110c102a1205031e1314010b03 68
    0x45c4820700455480030f0500350003d41c096800514010509040d400c044080f0120004078083c00d000c005614400e41108095400104400c200d443e10003c01c2054a0200c480680010383c0a9508058000d00d450008000740200641002c50300e00020b0001e5600410080421034030480c1613078040801d0740140c0c8c80b64100095000a000008600038020f503540d200c103865045440c0c45021448854482c03c290782d002c0800584801e0791801a8107055000c1c1d030022040d94001d1161a07c002100130020500d01c0c007680d402400f058076078407283c80031000f4159800741200180410030041c40050414411200100303103240c0b01070740340c4d4500303036141c0c40254100c0c00705814041e5110300092014800700d82d500118034200d50710411455490b5003104d1040d200d200d609403190801804e9130b42110b503020007051044c8030700e06085070b081584604a443c0d01040da81c08841d40301c20300826000180580d00740381c4c0078807421400100080c1d2521460001c0d01358000c002c1e02c9035074501880e48a428280050100881 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 146552877 1250 146551627 146551631
    0x2515090b0a0c390f17040f032009040f030e01210c03060314010501031e051504020111070e040203070f0303120c03150602010506130509190f06050f0415 67
    0x40d2002010b49000020319240249900c041c4041c19000c99031440383c540c603268840c00000c44007180c54500030400c6101002d5414a00741044042070034061000c0b90700741c402504c000441603266507583c03084d1401c5403078601e0b80c080080749059800d484104885214174041c0c140c41107030780c5c00c3e0300b0042d2403a0b80c4002c82c01e0400509215007504115405025040c900803c40c0001c0c0b2120411412001407506420042c08011840c10441c0300b0f107015007056040e81d009000e140c0c0c4a200d1031082851114580c200144584c001600d05c058150442c111180d005006060201c216000c100e105070030911150021107080308110203210075420100500e00281581d0700120302e0442c01c0d0388002c0c241d80840b1809441e40c0e40c0f141c12003080702d440f0341c2120745101d08040340c8a90881c2c9804010303000e42030854009004d00303105ca02c050255030b02c80c01100c1c0030b4005000500030b4020035040040d0031914a0401703075a40a40030000700d00040140c880d8900c182c00b20308000103582040e24081b124244001c40400c1a54 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 146554127 1250 146552877 146552891
    0x60c0e0303070f02040905031303030f0503070c030c11091003050c04180212150708090d03110a0e010905090103060207051c0e010c05160603060512122515090b0a 71
    0x910000215400b058104043c0d200516461000a010f019454401802d40c000850f510120003c0700c1d40700c00580b4800c0d180c903402c00f0105503049402e80002c03a00030000455680300c000119025040500740e49024030146400b04c110000860324040c0e0a5035080c1c80f0446405003001070000a000640c002e0404a4091101a403880070070058100e0b070850191148081601c1681d1054041286100580510681c1183d9181802000e0000b14044480100d40d002c0e41c55080421031080c402c11020b5201240b8690400301000c10407601b081286003001c0c1071021204001c034603503483e82e07500b41c000e5101e0540540d480c000d81c500b4a08095460401505a07070004c4070b0210203035007014004064417000e10f06074600761001e0402c42e14101204c40c011030498a46a0041061070303141d0000001c1d5001035a0014401500303c14843d991209002090101d00c800d21070030b0791182e20b45100d0300e80d00900740b17114006003456072070b00100c040241c01002ca005a03540130078130802c64245c2403070380d1103003085078204402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 146555377 1250 146554127 146554129
    0x301111e040e0c0a020f0604030507020a140102061501030e01020c0606011404030503120a0f02030f010816080c12150109020a081509060d05070f080303100f05010f031a040203070507060c0e 83
    0x2c02800250521001003520214a0b00c00c000e4100c80341c0040c000ca03400ca00b014100a82240d00188050380201c00c0480081383c0800060700118004e83c0603802480d041c0c0c1d408524402a04200168604140d203e860040780c10600340044c00340340c50000003908140c2029000904104d0584082002d84c030010700c010004241d01005846c6644241003582009075900e1039994010300b100d036a0b0005031072012041c4200507100a11740c42c1a1900401220204000031000f0f003800c078040c2c4a0202e440d40300081c0307500c1c9030030701c0740500c0200c2d083d00f4100d40c0304598002d1020884107090b0803140d445e503404215070144603440074485400c4102180d03c00e5030000360314046910040b00802860003401010045020004200807001c0108005134410700c1140d145c3c02e80701e0316544280d80314519042c45070f1010030352104a0701740300b04480b0161100f0002c00124103040c0c0150074404d4083c4d2241c841c84403103501580701c07400154411175080ea16180d9400c4645400811a1800040c410404c1602d840005207 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 146556627 1250 146555377 146555399
    0x10f1a0d050606040909060507020d080907141c080d110405060409180b0c040512030412021903060c030b100207030b0106120b0402180907030c081308090301111e04 72
    0x3800c0005a0114080d40c0308000310f0800d20666100701541c900e01030301081032014550005002d0641c550949000b900c0c950300c00c0b070304814281d480000d950003813841040684c00c0e07000d8a40c0c10b101c1c00340900c1c82c0c1d07000710b20440c603d00c4038141094622110000301501d05401c18460700d180f010340031800506041c202404500c441c000d900500c101d0315690300c040308102024118072242544e1294074a881840c18a880000b02e8119203e51409180094000c203940f00d40071050340c0c2501c0c405c803043c2007403005607000c1181501000142c040c154100d81c42c003001045c414010135003003005580b8003140818500040c00707e40c2245840d16011900041c000b440010b4000d9401030440d041440d201d50070390582504075004052852540d54410310000d54215904080d2051160702c070001c49001542c0d5642c40403c0d0241c0d2044034010707000400c0d42d4009045003004a950f030b03256030b0040c840e407820940da1a01080c21610910600d0180c03d8002c5501c03984c00031019081c0c00f0250b90601a5410a031800d81e484607 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 146557877 1250 146556627 146556637
    0x20601030f060e03070213060603150b0702091f080c0f030d0210020a05120f04020120030304120903020306070c02120d0c080a050c0607030f051806070c03030b1206010f1a 75
    0x80b59544a0741c80640d0a0801c005031884d082d00100b8081c000a01e03d01201c00600c3d60b4400e04002c01e042ca80038a509420b039035810b5003119540d40d5024a00143c6a00300080f0728002404c00499032940f1180384002c00007200c08501900062000300300c00000308080048480c0c119540f6840380e40201c1d122240140e0202c1d0b032400342840d08502623122070150805503450f0040041084980d4540c608102c10b025081d030f04580594002e8aa01591a44161302c40a00c0d4008086c199650380c02000070900142d0003902d09070807a240e47c0303442911584c40e0f600190803c2d505890100005e402c0c60400c1096203040000d81c248411000002c00c1c503c01114400b4144c03940d030060107405054041240048603001d44200c44015151200341c1c4d103580ba0001c800380043c1864400b1020041c5800c000a6000c00151521004800907c0040c06d00b5070f6020300803508508415412000c0503110075000a640d21403010f882101c0a07600050030066060040c0100d1208440e40600100054590203114004170b15049407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 146559127 1250 146557877 146557883
    0x702030105011410031d030a08160c03170601090306050118050c2d0c01110c070806040b0a0216060204140102060f010308160501060b1305011d0105091e03032107020601030f 76
    0x49a01c030501400034042d46500701b406011400001034080c1c520b84d10140441c0310f41c0b12070840030010101c41d402200c140102d040c0007402314640854a002c2c000c91022400da010b0414507010500c16240c0d40c4130380658100384d000e40510200c007404401200c155006040e0b1028040403400e04212650a00b044586650300c000685055092001d680c2802e400e011560340c041d41d60001c0c010b00030f2007400b0755015880b00006103402c2c092540049032000300400d20501640e0001003100b4640c64807640f103c001d60101c4580700751459100c44178400602140054001001186912543c0d64001c0c1c0004e410071030001d0508100041e0400180b00040200c015910721020428854044a0580c5081401841e583d0084402d23030b880070540050400c0014054004c0d607100380c0e207000c9441181115034000d41c02c4003074202d011503014080d2900c1e03410711800c2440d0000c01d003200705100940080c080f80c02c541c088142203500c58014002203610798500f0034459008460b51009100c90341c5161107130101d4094080b002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 146560377 1250 146559127 146559131
    0xb16060b180a020711030f150f0712020c01090512040504150e16050d0614130506010e12120f0d0507050f0a030c090312021e07060e0d02010302130b070203010501141003 74
    0x8101031200607800c172100198003404a44544448010702a50f4421b05001c1c1584450000e0000d01203a0101040b40e02480c0c180d00c1c1c82444580b4070380c841019421608121005650390003126011070820082d40410600d8903007602d50340c40c20301c414442a00d03512000034440d860380100410105075041d450a80c80f040352200c481c00b40694020440306441201e0902c2001ca041001c0810040070900810503415411944003400d000900b014100382c8004031a03aa0118198008a2100f4104010810312010a0a0580b21350461584040d10940c0203410864040c001c00710300d42e80d03c0e44081c800c0b2604003890b07061540c10824400c3c1100e01c07912135000741c0c0080540302c1c40e020f0780781c0b07024051004c0515071114a00c881556120300003907071058841508c401c6400c400d03c0b0303816040d901107081c00607601c05517901720001e8035a0040c4242c0130000c100881c101075003045802400d8007525130040180154541c0340e50303500042c0c0101420365106812101c03a440e40902d011003659030b42c0e0a0342e04c1100081c100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 146561627 1250 146560377 146560387
    0xa0e0a02150a0e0a06032301080a0f020102010f0f0504060b030f03160203030904020c0102072105040603271202060a05060d0b04030c02190e1305250b16060b180a02 72
    0xc03c440460000007a07507040f400c903010201c1d03c0c50b010340080001c15040300c0390a51030781210340e040c200c10305c003845010001c0d00701c0300c8002c000c94511a03080760b03441d0060001040041c554880c02084401c103d01c10200d55503184240070401429016010301d03400d0440081055040480d40c481e200d100c0d0481c8a42e00c849501000c01c115203091050b03500394080140b0854444040800c01030203940641400c0f5001e100c03840027a1a43c2140008010010320250394040c05d140c140407060300140030980c0500448542c80342a00042c1c851703190141c20300c0c0c3c442c1641c0401e01301d002801030716009001d0122401030707041800f08a01500c440c0541c500a94000605942c81e0300d45060503034040d04031490180d002544030b0926120300141900307030307030490b00f0002c0003107081e680308000240417001d61040204a03800101282680c0090030241d5000703d010020380c3c403401503503003803003141d01d03401a0b040280c500074280b6940140030883c8030b91004d00304240d4903050f00e50101c030780c82c1700703110070040c2182c01495000c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 146562877 1250 146561627 146561647
    0x90111120403030908070609230c0607030318110901060203030105222316020102040b0706020310150207090606022b0c0605010b1206010203070807030305070c020303120a0e0a0215 79
    0x200100a0b0408411076851ba4542049806000070300f100ba90468405000302d003911952180460703403514444040c0c101c0c0207038081040903a510880c400d40030113841b146243c2100d032038846c04150580c440c010500c49035102100703110108030141c0c00442590001c4c801041181c40307800c02014009441440907403103440c88480c2100a00c842c1c01c901d40c22900501000d480340e04840100da01800288145004000507850100e00b070380328501441b01c20120a012480002c0c4087d006076400081d84062840c64580301d0302502c8100d0f0001701c10200590020311300300001d2500703210f40700242000f480a00944184507081d64015004034010900701030342d924951072351500c1501c55002c4030743d000c20140640d503505c6040d0000713600002503240e1038000c0300b004151035600001c102c2e142281d10521660510859890a400920000f8507580a05c4010071040c801079900384020060040c08000651140c02c00d08140402c9916020840d0304945c4080c0c40900569a02d4440c1a4100910403070181e49180e654 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 146564127 1250 146562877 146562881
    0x9071b020114192003070312090f050f01050f010504090f2307030818010305040f080c0309040903020303041b05012c040618050c0732030316020609011112040303 71
    0x12644a00e03180c19070380140c00e1590154404c1042c1c860300300c0311303048801d01d800b0303240c0c9034410050001d011031400303584600d07145811381088000b1405182e00c003182050a4503254106040c6d24403540441c0d5462041105042c4805500350240000362001c12030320312103603115900600f40e1031010b410030300c0c101050038010240d41c602c1420b42c0202e00503200c54507601e00e45490a50024100380518070f108108542030ba51103440390b54032803a0003890340b20251000340c40d000119404250300110a010070401e04d1500d894a0280440701032080d0700440c0e8916050501e02ca0016141820f081820324000302041941e0303200c8401c04400701c41e150300c450f10f9a10900d900000b5520142c1446c1c0260502c080050410603201400d00d10390b891450520481e070344d01d601030926105101c8020051504100c1c4808803101c401c1500449540c084040c2034a0309480e00c01900e103801c201c0b16641c49140b42c14409006c15414480d891704411014000e002480340880021300a000d5235001140c02c211440000b41494465 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 146565377 1250 146564127 146564137
    0x50901060314070302041103070c200405010617060301060312030b0f03150718030206071401021608040f0b0c03030f040f120306141008070807120f05010509071b020114 74
    0x55102c40c261072515612a90244000d078030a614060040070701081c88005c880c85048241e07140c4401c01910754504034181c42044410f203c02c00480c00c160107175122441885c0c06000c0c55152400b0016044216041c00341000f4030184c013990602801700002000c2620341c1c5048005c03424080f51508582d80450040c81c10719084580c54032492a07011483c2c40801d54203806500160741d00901481e60106068082005220003074202c10100103000c040781041800108901510002502e04011481e10121620420700143e83c00000000c003000000300340040100201162003001e4100301c4401d0b6029201d0000808079055051503000207010042020740e6240f410750b0180220900741c0305541d000f001000c080c0a030f0116003140c003501c0101450f00d030890403180022540c50411345d555821080315420000b800b40c1c801d002d01c02c000e603c8091070138002d441e010f540800000a003503141030200f1030314042c040c01d2201030142c8030384800700402d219503030612003d40a00741130703600d02440085104c042c803803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 146566627 1250 146565377 146565383
    0x30209030a1502090a061e0f09090509010b030c0d02010e13061206140f24010e060406050d1104030206031b13060216050301020f040603111b060709090516030509010603 74
    0x20208100b4848441da9000c0c202502058440d103120341c0e220a41641c6180c41521200e484417100c1d4001c40c101882061a541011007038900a040f5aa0740c5034124180da4081d00c4142e0241d4507800c606010381000c104443d0a404116142902a90709400182a9041c01c144160141c0b500c0e2101240484964116130001d0260700c0c08201607006504050008058445000584800d980c022038405c1d29004030349801002c00b1951855007004909d8041c828100b40703e4902c3c1803003100d002d003241d20703035030301c40604010003098560340d0b9141c981e40c40030011240254140110303004103100c14000342e00c500d070603668402d03608103104008500b984003611007030090094407805242400404500c06e6408035034880c7c030311405044018107075154000c01d801d0b806510600104401d0038002080707a548680c101c840703800c0e0a1541c140c60300c1c20a141000317002410140752409540003209001009030300c0302ca074200030a05120200102d0801c106140400f44100308600101900c1d000495010003080d4040002158 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 146567877 1250 146566627 146566643
    0xc080f0702060f0c121809060a0b03070306060305060306132904080a12050f0703090c1203020102030f09030c070501031d010e0c0117010509040201050f12090307020a0909050d030209030a 82
    0x4445010500c551140300090082e000c0da41e0086101440c0b00140c0704648030140440100c0030106c401e000d0001002004107074000c0043c1400038034020344100660044a650342c01103545400c061001e416114040c100d5402640070380108042020810500c0a0b0140d03c02c0400c04d450109101c081034001c6001c8440341c1c1d0100090500c030820403c04000c10b0300c1c81040d181c3c50341a04000300950b048810468060f551401010300003181c10b4425403041140e81e209031512824151141500c81054140d074500301d0150303500209004209280e0303111158428184030086140c402404209a00c4101074804d003030605440d89070081514030007640d0000b89240700c1000300010003940354416554402c10388a1070202c2c4040e25014000d4000140a9060b02e02c09014480b9a0300d56500459659001c41610100070700d0500c00303820125420058103001d214540700a580301d0399540100558509540d006c1c048081c900032003e00020408200040340c000c1c0b03404c0c010f844040309008641080710207000107213401c0e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 146569127 1250 146567877 146567887
    0xf02030409050712050703020717030601030e1f1107080d0b040b2701060923010507020607031d1e10110a0501090c05040b090f040602071e031e0c080f070206 69
    0xb640c000b0007041e0403004d040e42808a603c80c854203404038491b048001e030880701043e203000f015684400045400010601d00041c1c3d072001c209909c0e06207020031150043c0040e2943c0107041c1c003441f0b4080d0789101812100041d1621640b0790341c04000744035001c205100d82c1e843c2c0054081c80c0d900c2c0e07030224004039005030681115100a07132080e00900369442013041c0c200ca0300030011440e20710660281054844400381c00403d080c4040f00e2140c0d0b1205020303040e041180c20800b01d00180c507081d000d003c1151081d00e03001a85c2c00c665070380120350b0280416150083e82110501c1000070a2a483d00c0b0b1032900c165212140a07042400c101c0700c0003080754402040c0c2c410f580402082200550101a9150250801c59111603e8004002c10f40320008091503002251303030007246ca020111050310f42c000b4420f000051509955a58007051311000810034000c50045000d920241a00114071741e01071102002c000c244012102d401400c01d030648400500309000100f9400b90f82074000c2d0403104603a40040001344c882c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 146570377 1250 146569127 146569141
    0x309010207050d0207180f11130e061e120a0b01140a09020a02030708030705090a24091a070203010609060905070f0c02060904090f122609030a0f0203040905 69
    0x10798002003007240c2503c6004860304249102182c243d0030b560381c10344030440c24440c110440003c0d004100c00c0340f0207140e444901c0426041114010901c454020b21a002d84603d402404c0c5140a0020203041c0260301c3c040c1c0100d25140c8083c440c002c00c0303c007240d1420220440c0da0040b4540018001c0007805600f14400100322201e00c0c072502901d00104407544a02c55407100f071f8400507402135102d0000940d01c2440702c4800580c8400145900480c14981241045201c0c40008c22415059102500200d42d0040c00f16040402c82c484280403011030038240c82c118600040203074082d400b02c1081030b01c42c5000c40c16400b1586e080d0441c4005182002045c0111b071781380e02c00c0000030f1005807840000305180010007109070740a200510401600206031502303080c0c41c00d0920020300807070002114481c10016480c00000c0075060011a004420740e10200599815506035440010349184500312000c41d50801c501c80b0000803c5802000f50740c0f400440810b94003005074510f000d550070001c1300505000c1001a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 146571627 1250 146570377 146570381
    0x20a090e071b14071a12060102030706020a08071b050703060b010e030102070516051008060d15020c060103020a0803180607110a08030c060c1c09021f110609030405060d051b030901 79
    0x2108007200c184c49040740d40310031280328441d0105402c0702d040c90038450704203551008207a0640c03061045c010b80e4540000da0f5100c00481c0d120004580206014100b400b0090354094111f555407503442e45089413a4400d074558507a078050714400100381a0b251b8800070142d0340b2503400761a52503c080e000755101c403094070b03003030352201c2d040f0b50304040700b903100700c0005054074228224048040311030311002003d48422046c40444003a8920a8480307140840005840700210300c014030700c1c0012200036020035410751040040007034855104c0600780d4028841403014504031081c81c5048a01225002e541d404d50341f030520001426000c0c4c40b03610120b01c410000f59000b0110003000000701c04800e0b031b40140c6ea1480000028003801c00e1660303407110200c1b424a12004581c0c032144034940000d00308160314030800c01d1140c000c00c803070340c40744002841c1401d0b075104080204132084c1c0240219028504103030510020900d00c6c0a800100c1c0c220b2900d034000308103407045070415070044041e00c0200c070b6964a0080200780c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 146572877 1250 146571627 146571653
    0x1091205010603140a03080703090503040308030412031a01020316020d02040513031707080c0c0a06020d06140405090c01140d02070308040302061b091905030307060c0f03020a090e071b 81
    0x840070031200e003034244e0f0103022446400f074541c191650545c1e61140e10086006010b049011200c1c2d100421000c40403400a00245214070703c00d9410799000d2491103001400e03100e8201880208001070b120008043c0e8002c01990074120400c0c403100d0180c0340d80c0c00000c80d48107500300d0180d00b16180c0000c1c03080400017450343d044c1141c02501e4800e4207101c0189824000d0354103c4030f03031000030304401c04101c840c3ccc803034801030403c004e0050449104002d10b8aa28089a01c0062000c10881c1c0d200020041c420318a00f9441c0e42110454082019281084040741c40b01e40c070a0000741000a0f40c06042c00c62905a401d032140070a4400b011034032200c1c140342c040c200000560302070780588103c400080503080d28100b000802841c20031000d0a01c4401418007903d140c85d0700004800d426499808070f110380341000a418034a028034000300c0c038001240d9000d0040c2d0200e2039035904040c010400704100c2303500080c82508907554040696010740c0c0380135085500d0010821224480407207402820107020760003401300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 146574127 1250 146572877 146572883
    0x305030a021b03060a090203031b0c0f121203070c1e0b0114030703080903030c061306060f0803030601050708090d0309080d02241e01060507050105010e071d01091205010603 76
    0x9250400704052120520b96000300c119416442040001c1d1140740c01e401001c8400e102804490500788984100700301404c1814015034180e00c0030b80400c0700ca20f407080307040841c54070580d00e41400000c0c0d01d010588986c0c0c0e615043c1400140000800c1e001446941100c00e185d410200d100407007401282d41c401212540c0e141940c024201c0c0c40007145080310302440850115000f4014501c0504d56a00c10403141c008604603a8140410b001d00e03000e1840500409214042503034200c0000c010502e440c0c4111409900100240086081d017403086003c000f0859401490901b085601d9000d980b07080d6000384070b6980d605810900c0c5101b41b104050f00700000074296150a41a500181e183c0d940482c0d41c0d060085011043c60b81041002601016050100350000050703903105480b82410000f01c015154203a001c0c60004000280380d000b44002845a00c1c094924840daa01c0903091110b0700800103616036105c200020382503030700030383c0030b80c014501e000081085100140140000f800c0c00c1e4000d100c0e0788015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 146575377 1250 146574127 146574133
    0x1a0c0a0216050306070e01090b0a02010b0301180b07120f0c0f030e06060607020409020f03070e0f01050f100f031b120e03070b1f052d030601060207090e030d060305030a02 75
    0x9a000c0070141554101980d0000d4014612a5620310b01261010095602a4180702e0009404075150383c100c0020720700341d010380e00042040d000000c00d050840d07500d10200e90070304000f41902400161400d5078513070040b0103450701104c0040c145401c81c001b04100c0c0c460054071071a140c2c9003031915402101450381e4444903141000100d20000c0d100c2e80b03c9008850041d40171108020440061410350b1200901d40d0002c0d05d0851204a0000031a24106036038002e051a0010241046444981a08814054041900d0000304282c521000c2548690440b901d00c0a010b18114900e000f00e00c680c0c804d5440300d1803000340c0840704d0101c010150102010100400c036007801d140007000401000012914055400007486613540d0321902d00a80b090742200c0802c1d01c4002d01080025155034a016800d041c07800d40280205c10300c0c0c0c0303c600000e2102940c00c09406500000e004001103500402d688089460210001c610410f10600c018154410400e000142521b011030200a211001025000b20034440d022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 146576627 1250 146575377 146575393
    0xf0703030804030e19150e09040b010314030a02030a080a14040c0801140912070f06060f0f050102010e060a021e13080c01080907060c11091501020c040212040f1a0c0a02 74
    0x40c0441c0101e00b40380321195024280302001044010b160010f603086c40b626000483c40d04150000c3e007049030a440c1518404030f2100140144506407400700d98200e0707c00000c51601244a80c06503e03400340300f80d20401c0c081105c000581c80d0910360083d10300241c0048411009151600d0402030480650058800d00d40c681502c02214103c000005400307142004001c0c071200c0f180d16000c09941c1e01a490454900d03c2c03070201c0d1360014074180240c502030f01c00d20803a01d60450515110200b4a00341364002811a8101a0003104002c004280a6080b0070090000740e6928242026005156090800c00b1070b0000300046040c0c015000c9284001a0344964058441c841140d1004682405042d030303907518580c01649c01040034074004c25405005030311901e01d0749400720300e10000803250b00044941910310702090522510540e4103100e0b080d2402000c41e01181400384801100c91010401040182151040b41004051040203505004c0e482010342114aa518000c1002d00706904900c030003401601c03503840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 146577877 1250 146576627 146576629
    0xe01091a0a020a020703080310080f010603110913031206050a08010506040606020c03060a05070219030f0f030c050405120703050303090708011802060f1305130c02100501080601060c050f0703030804030e 89
    0x702c0d4003499244e03000b4003000d41951190601603002a110f0317603000d42e010200180303d040034021240a40c00d0403000088141c91030070240041d0040c1d603040e6108190300c0741001410f030345101c11a0062030f05890401da21a80b1a040368001b40600c0d08910740c0409400340000b403100b01508081e20a01083e2001d2084541d80e07801641d03a400000040d540c550417580001d90000100d90100da4010030620455004111840004a140f100384009400103100700003014002038001e00e1401140030186810004a400ba5100400c18091401030f148030b409503004481d4007580400035070024603004030560380d807401c1c1020f5082d0354100c14460031105500700700c1410a80c42445501c0211540c001e08110310304200d0f00c0d24a025540b12141000e41c40200074004511510340340307444068076030440341c00100310450b80c401914164800d0a4403c2da11f0614005220344032000c915a81120b245082c0000480c2c0945403035410082c00140145081c8540c42000060581c01210717240964081d0b103940c0c0d04104084 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 146579127 1250 146577877 146577881
    0x30d15140306070503040c0e070509100e2101060b120414030c060c0706142406031501180b031f1401020a1106090910050a1e03020103050a0e01091a0a 66
    0xa150340d5455041075001901560003103005580c41407140d01d10242e102d17100c0910100d08103051341d058000030300120346090740c2c0c10840350000d409100d50030031001c0d085621000803d0404c441000304c0c4d441c10311742107c0500c4042508920094801a50166100e2183c034000700c920340001c8400340c0c0c103024816604101c0c050040b04498130030114402508143e41c1e01e294000f420342c0006400c80d815a031f02d4030098a1980c010020500a0350050055441e4655100b10840c2c01808600315a225203001c0007804481d00d507607541c440c01000203082481300303180030b5130f240c02508600d81d0208103000700000030003241c515503010028100c000d0304c42400000b03031214030266000c2880b24000d80542e2100e1200d02c0820441144440c110000030503c074500001000070465132042542c2d0b007041c04040040c207004628094403200090a8410b805500c5001c003c002520b9402040c03002a060540e40c401003a030703c4106422007420309500c04028410a4044d150010110302c1c0b401c00c0d1a07440640a000c10b070821514 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 146580377 1250 146579127 146579159
    0x203090c01141201141809010902100314040f061404030e1903030806120f010903050c070e070804060506030a17030703060b0405060a051605010518060903040620010b03030d15 77
    0x82c0d440314005a0926220400c0361071108851541b203040b64016603041d2131041d107400e1081c5505c0002141303950440c414050004140b03a0004241828144000e075109175032019280e100d6082484803602015a0500100615011144610351021001000140340e0086404d0800610659031102c807a1210411011495401d020060010340b4880c081029441c1803000c0d02401410f00082c2d49841005422040c212450028224042003010524000d003810038400e41009107600c60504d115403500610060100a00910041038071f680d40c4003041ca42c0d14104042d0b00d20503403004076030f40108c0b440c0b0400e029070b810444015000905007440440c103038076a4010b460171208050111820302034103441c2502c0f40e40090003c001c1142c1200f0074080410f4090142030700555107000c640c80b4a00444090505208009100b001540d004200400c50264440c20800c480c0c0900c0160740091201344130750501600e01d45c1411342e454400424504400310842e4005600c0081109291812903900c52070801c080c141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 146581627 1250 146580377 146580397
    0x4060206091507120b0406090e010b04060303140705070e010306051503070303050a0c02041e06050a06110a060518070303021b0a080d050f0d02040902030406050c0c0607210203090c0114 81
    0xb1100450000d83c0a15074202492412038408075100c04141d0110702100c02603444106070a0f103940c1c2d0304134928402e00c0b90314000340c016241407040f20705540f4050061110014990303040c240c0081c10000b070200038020b00020b0320780103501c1c0075075594a080c8080503050540e204001e078020141903c4440c600040d01d00110399041d11110b0030081190b40035104d020200c981660440c0e00c030810040600181d80c44200e40c89120040040d9180c2480213110181720307290407407018088203580416540d07800140380200c040c2d1002000c6511f0355010305003082c0905001d40c04650748100315000c0101500401c030a44484107007052114103144034001c000d0814010300c00c3c1505600503603d01d9030418815401000c0c408100e840861074050341101003000c907801130317015181403540032007031100b00552402126040b124080c83c0038141600040a03503117904002d8001d001784500c8405048a40c0d01244900c4250984010308540300c1c5842403220341c54034454180203000a40030b8951100e1a5101b1042d180f060034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 146582733 1106 146581627 146581663
    0x90e19060218150d020901111009030e01090509040605070509030a060e070608040b06040509010b0307140a06020304030507060e041503050c15041202010804060b1002030406020609 79
    0x1e140594070903082e80e03003c4843c1c0c40d84002034600a0391020001640ea0018500585013644a01810301c4c160040351641800c1c1c169030351000000300d0107900c5000d81c0c0c0000f20011038440b24540500e40c3d0000c1402d0126000c01c10540c842903001502c1d040c8189491300f020006440c105103404201c88230b80d100c0150794614441480203034002e2195040031200c508103903940b6a081c04005003268001e55445c4002680003009401c2804440c03406801c2e00c5150783c40321200d1845125040d00749000d00b51481000901c02c2c4000110b80449420801408505013450000c0f0345101540310455442502c401c0c584124603132840014004610507002010305c90602400c2c4080c080480e0400d5241000034071040082810348000d00d901650b0918105050381d4551500d10300800007d50b03055080840b411148600c160000700800940c2c28940032505190b40304004a9928010180c04d550011 = true := by decide +kernel

theorem cover : BRFrame.Cov 146402877 146582733 := by
  have h0 := BRFrame.cov_init 146402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 146402877 ≤ n) (h2 : n < 146582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
