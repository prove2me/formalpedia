-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4376
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:25:15.043564+00:00
-- url     : https://prove2.me/submissions/eb94c9ad-3844-44e5-abd2-a9c87cf116f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 786870503 ≤ n < 787050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 786871753 1250 786870503 786870509
    0x106052110060c11040c211e0905071e03150204050a0509060d1b0501030c0212030c0a2102091c0b190f020d0b0901050105040612050612060f06210c0d020a 68
    0x1c5818000300071b8075558000c050084000300d11040d00348021a80070070500b910f101418900182c404202d410904000d0380d4050040ba80c0300e041200d00669440c070914903001c001d20302604400c4e120350000c00601020aa80d0b0450790480d2008500c0d10f414803000a0788000c0c05e0141c0c85c003c00c4030400084254452131484243e85800100079050300b05545a4401040c229010fa680040d0070901242c007850b00004801c072082c00201011130865031605a406401e40044d101c05003001640e100248036640290300c982a4404031740405686d5103c0c403030030700181d046002000b50018080110741e00200320160501c6410145040750120251100501c4402038080804442e21080c4009506151801a5030103503130384000580301c001c001d0384c0c1e900040d03a0500551040002103000c0c0d10b03104071182c4003944032980c0080000c01d0f40207048414010700345011000c40706820a14040000d00640b49004801a8a03013009510588107030020001515190f05200756007a0090040121604c2190744000911000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 786873003 1250 786871753 786871759
    0x2303191704062708070f0201020c06031305011b0c03030b21060109060501080f01060806030a2a08070602070b09130c080a0b0913020105031803030106052110060c11 72
    0x10034146810900c000340b1204812144035104070781035402a0311002e10b0340f40d03115001910079051410035280e04000c43d4004000301c0c1140030300c44e103150090361031501075030180045501104642007540341c51421204c0f5a8045800354449504000c011541302104181a5525280c081503100840c3c0204003030629110842d030142e154450b072046107500002d9071604032003a140b41445001d0395140152840c03d82a544456841c40c80001444202c0c0202d07030054100780040c04962030b0845945444803600d90207005c210b501c1c291603032007034a00381e0b00100340d40241c19508058120185090f00184d038a50041c865159089004070b0f40c40c02903a1208503150007481046000d00141d44540d0000704100800c40c0d402603158a04486188141800c481c8a40301d4103001150b46c50b4240150019102c1d604014030f00981226003410341054a50144061070083c401e42c0c550301d450b100074030f01c05501e00301e002c00358038035a00b1120100314941000c2ca003c01c04498150400018800c06c50409a090040d07142d50039030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 786874253 1250 786873003 786873047
    0x21011120a0201151a03130b0c0a0e0f1f091a0c071d0a050903130e16033c110d05060f030715020109051504230319 51
    0x4510003030200104408442036008105848850032800a4400b05000742d02102940891104490b0081402150444900708445103484503030341d20b4107900907003125400f48011000c50411000790f000000400510005c40b801544400b8442c041806035110005030100300c1c6e080780c1c4400c070560041c5c45072009020203050704092051a01100c10840e8080304440103d8440c2c40d00c000b80000800b400181c0c581c031441041304084e04d4810803140501000b4040d00e81d140410041c4402c261f00443c44100141010003405081e4580605c1e0300300744081e0803250b03109050506100c02c3c04403440481c440710700040980d41e505160801030711100303041e820ad42e80300007007880c3c16900070b0302c0058000942400130410900f40000e42c0c1d040c052190700c0038800580c9401d0b1740080028040480602020700c2c81070f0880c030000840c45080c1d02da003440c220b101008418144002402d03c0140322000140d04d03441e0700c0305aa0071000c01003129600d6507074414051000b01c3e100c4401884800036119824400d4140c2e506000c050b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 786875503 1250 786874253 786874273
    0xb12061608060414040606300b0627010303120c02061b04050a03051b1c200a030c0302100c0c2d0602060618060a050411040504022803050c0403021011 66
    0x1c001c211a000d4071003040302d160100310500d1b455208058240d26220120807848d41150307038082960038050000340c0e00080442030a240401200d4210300d1180c0c2c0c050446826524605010f00340320491002c0100703040c1803001e528005600001c000b80c10003248000c502400c410b400441059020301d41101d035000b054480c0000034414006119019107500c0c89481c032141403d1410001296444c02940c1d007106003586000300860340e8204208814040f1388098460004001d00180c1d07448000d400440301200019000c0c025801c0170b02210f0141c40300e41c02c00c075881822a45585180c0b030394611800c00c81c0072080e0341040c0382c0e00e845510100001d18201d4012001601c80038046c0d12440e08032a020b004600c4002503e0070011a20a03040c041c01000e00b0425001e03040134140400760100a844042e541c0c0100400204d40c0c407684014139101041c41e407116402c000c0c000d80801d8802c1014071200406041a061000e003201d07001c216011640d04403194a1600302e070040c1512128403011010401e401040d05138 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 786876753 1250 786875503 786875513
    0x206090f040e100e0a030f0e01022508060f1005060a020a1211300a090b0c151602030406031a0916030c02030f09060f0d0603060b1206160806041404 65
    0x100c0c8449050051110303011300c0c0d50403541d07031542d018040c0029405520701100c241c001d880381000e4030f0301803054074407a411700404004014020303c0309540d800724003079007000000400e01005070007604805040229051104e000d03400c6e00034a0054521400300012210201d500030440c40c0c41666000350800e0407401007031005030202c0e45e204443c00c582d014601c00300c0001c0500d4594003828242c1041174114040200940e003032603400c26056201840301a26010a2921001c0c0180150580c4c0000a2100e400841c00207074a03018082c0400f46040030185004402c9074000c01510142c50f9a8900060340044d0f201164015a0103103c0050308803c2c0d45c0140071849050354401110040951028440a0316240007240c1c2c0348228071403024040c43c00d11850909162181c0100851501c100341942031822203181a0300f11081d0b980110703421a0346020a811318140141030a00c1c4403070340b0300681441d10700038489003c141090310080082207810f2001441642c5d42d0350120b91201c2c0001141960340c0307002d20740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 786878003 1250 786876753 786876763
    0x7020114041d040b0a020901020601060e0a050307090c180f03150902060c010b030c0604050a050d1a090a15050129210a0b09010302030a03110102160602070b090115030206090f040e 79
    0x1500c4d030340c14a1000820003c410300840c1c02032041a4000e240580c0703000412100241f1b2190312035889408034070001101d40e0104290070113806005000610407001a00103420f808c580510031444d501e180d84200b12112031080302004030380c1c0000c1c140d410405c038409850010010340c03a0003907002002140c9061802c4055201d640b00350016011240412081803c00c045809148034090780185904410300c158145088030b007041a20510a4100c0c0e40345014621410340000c40f5040550f9120254000a20258600f260319a00d944e2504100e203504023904c480f002c60700e1000c41c43c40ca02002c102050101010401c0300c02141c43c13039080c250030000701e160001820f0015a08001c14070704000e140065071900200c101d0482c1d9005004012600880d50b081c0c81c0c0c1d86a111205034995800e020202c1c0c401380c4040c01407c0d40744038540c010b0b0742d9401d03442d01c1c034540039000e000c0c0c04a90b8500745081200441d41f070003100c162601180c100340c480c0f10060005860700440304100f60007600301181e00ca400400012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 786879253 1250 786878003 786878011
    0x2130b040b0c01060e220f06062309010e060405091c0c02090f090316030509090115120c0e010509041e0e0f0c06090f180103050d022107020114041d 65
    0x3000340441da03552417030743c1c48241c400d03140d800c00500f08210412114072003003619900c00744288031071a0864003e031204011510f0541c04050f80c091990441110440310821313002c048907049884070704e10b504064940d40042c0000f02038a0040b0307a03803c0070840c0d000c1c0c10031213141403c24025080c403000c00d41c82c000074018074070004200c2c0100403640c0030801d05485084258443e0131030200450802c10f00383c090382070004070100306900f80101084044200c1d1543c8150a029094104840180300302d60742000b0503030a101580c05981030315000400c0455540300000d12814142441c0c203135160102c50f00010001d19904964040040c030031484400f08a046402840c100d0401000342c8500d8049001002d488100d284812940b269003085801e02034a46074108016014010f4848180d55500d034078401e0259000382c00540f0540d2040040c0300a0b5603041040203000e82c1c40ea59000c0d0340707040075410403102c2c1c00ba172107000f81805403d4198141d00e102c0002518003d100340074180e074a105040c15502c032900405d80d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 786880503 1250 786879253 786879277
    0x130020d1713050a0e061915020601170303060f011808010e010504030e09040b060409060f020a0c0c0501021f0c021615030c2f010615050903010c0903020a0902130b040b 74
    0x1500040780c0c40d02c0700000b000c450740290005c802c2d994040400044031001942c80484594003e008030701d80b180d01402c0c0d054054a0340090166504060003103404a0390014919220b51041080260076100d410510f1103c600130700b8802c0c619510790741003940c8030307013281c100340c006601c1c02c0d504280401c030541020780107901075100c1e9843c0d01c007910140100407000b02d9010b040d0542601c0802c8050030140d001d0041140507000025280c00e02e4481c5005903802540550001980910b60b01b0038000c81c00301e40402803409000415003041c8101c0c1c03100e09070000310000a62140d645010843c000e0088c4040d0444a4145c116134142c562120f11055011402c002c0c03140000385403440b451649070148001c200641c183c4042c6c1d054244030034103400d02500c130858554005540f40d0a00003540d620b500c024018003074103a100c02c0e840d90498024035007110040c40585003040401501007000d6100c0040c008191b0302401c10140c2c0d50106040a01c20035403a0b44d00c0794003030410000780001d0111002019103840c980d50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 786881753 1250 786880503 786880537
    0x180c020139090b041401053001050a06020a140f0d02030a020105091216060906020f090f060f030402131107140f0a051018170903060130020d17 63
    0x7400101c400e01514015001116800c01040c800c0d00000fa0a20790305a105140080c501400d001c4e28050810386180060a2054039114410501120500301405404c0c10b8655504031450601d000b562050341000c0901880503502075001080c03014805400408000070031902d00840500009649a00040c00328005500e00780208050304004103d00d4030485001d4007035401c010340b082050000c1202114120759580c4d8038001000082c0b5140068580c0e408a100703042c2d103541d180004d00060864210a1038464001003010303510410314101541e80007901a51650740462008000d40e0003081a80f00203201c0c0103010a1030310800400420302800b0603408026900350f814000212950b8159038907008ac4560000202034070764034206e9006041031803025541241613000c3d9205c0c01c1c600440c900c0f03180c1080000265810540c00c00300f1149004100d03002829000c5030660002c000700c04800c0382051b14002c84d64058405640d181c8028802c49904209510040f06082c0d00c0350360182e00c12420040d01c5005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 786883003 1250 786881753 786881861
    0xe01120506030a020f1914100203120408070f2a08060f0115180b090418030914061b060901110c06040b0903041e0603050a06180c0201 59
    0x10a000c0c05024003405001080038080c42da00300b140b001611160307035401c0025610f426400c13000c1003402c48020404403405035840102d0400b4083d811010034402c00a40d401004060324081c41001c2e1241c2c8160070011180d1501c3c03180c6804040f100c0404809400c07542e40b01c600c0340d6900c040d040c0d406148640844140c810582d5210400e8899108450311145a5126801000f0340301c001d40320980d01817840d10b801e407141d802d18040d00c0c0c044001350300829585000415110102c0c146841a280181180901d0360b03031010051350000c1865401e40100d002d89485e070341c401c48042d15881c2c2600c0806c0c400070900c01b045048001782c2503462508840700c10f04c541c00d0080f05000c07881c3c0c10003100e0750350390ae5202400711551940c031900104400507019200c148030811002030b550198404800d0700b02c60b07550101421a14084000302552030291041c2da0f00d40c9071040c10400c049119407010701c00403c82d5004100c110500d20141d0041507026000214411448480c503040d901446404090f41030350340345400c80d010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 786884253 1250 786883003 786883037
    0x1b050a0909080a1206120f0b280207112106010e07050a030504020d050d0f030f06120f05122116020d140412030e040b010e03060109021b0106060e01 65
    0xc9660030140c0403207010403101e40180c0c03113108040e051003044100840d416665800300310203004c40f0441960740341001d6240c0801c02008244003030700280200440c5400100781d005642141c6007402175410255030004c0c0c15420419030310b00c1d81c404a100106281880144052507060840da00740300203640380901400865480c0040c21118040c2c0031507074074241090040c05055004003000740050341d0280074102208009030003000b0541b80d028444c3e44400f0350610703500001c0c0c1610355582d800707a445401d0a0040c00804108aa125000d0341c000301c4034048200f00382466810305c011080400c40f85040003a400c001c0c065108840030b00c1c841d5045034580c003640c41242d0300520105050305031005030460340c1b90070300e200c1c403411030070b04580c2c98888003034030b0546d4584407114110a540c00803030200d0308219410100d890305102d0140c0c01d00b000e00f0065400c05c0580e00203901d50105001d0300001070b41c00f107400512050990f01d140240040b001c000c00400b5140e640140c401d1580354829800115a01c20b40a01d1318 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 786885503 1250 786884253 786884261
    0xa0e092503020f0123090316060e030d020a050c130b0405090322121202030412050c0a08160b0d06050301020c0604020913080906030721060807080a05030405120a1b050a09 75
    0x301705c0d104080364a10381c10341e140802d030711604c180b652501c80d12541e00342107a01540400001c14458444100d201000c40916040a41102c500d4056401490410020030b40100701400600c104480342c0241c10b80030700103000144015451160894900000c0103d1440008000d080c142c04881f01c86001c0f480c2500d040520402c580207106900c442400032200043d00ea4140a0750b030003682c01581d0a00d510b80c0001c001d401029030007540d155100510320050350405890034005040c0302d40203400529074142c140c507020303102c1d8440c10303542260000700035a05801591001004d044018029075a500705840c2407681c8802c25582a0703c14405080400c4800e4488004504000e81c003030204e9041040400400c000d507000105032200344241c202d0030000b52461030b0b41c51030580040000002e440c40c00d000e0654549510307031b040020282d101c2001c03c008500c1c0081501d00f100c80c2291904240e032110116141068501035005006841655001c0300700504000c120059483c29110440180d503154032400640b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 786886753 1250 786885503 786885527
    0xe1501032d0e070305150f0a0504050a122102030103052803051c09080a020111160f0f0f0b090606030d140703093c03020a0e092503020f01 61
    0x40303010020070354020303180350300009400480201a00c2d0115a25160340f81480703803030359904070b90100e85401c01010a1141e1400354004070107280800180c5069039804d80d607580d180102926444a945840d403080344036100301002040c140c4481c10011203400c1c02100650400c0c0800c0ba9103016280c140300740103440c1c1d66140001130341c40c0421002414191000c1d82c003584070030449001c607125104010300c00c00040c0500800b542c40703107820a580d0781d15040007e084074600e0092200c0e4003c20400002c0b00d01400c4010301070750783c01c4000302000c82c03054500200c4090b80c0201c02081e680700f4600c05401d00c98004400d51090301c5c01c00544445035259000c01d6154084c0109110225250440401c0341c44447d001410b116807281c142191702640b01d100f0340012080c4065015244030300740f1609607074550780481e484002804107030b10b610b42605590001d000d40c5e4103070280c1c1810090580000f43d04603003c01417145040101c840566031381c0d82040b02c0c100311001a01040c0d0007211021000c0301254400c017118042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 786888003 1250 786886753 786886811
    0x111b1905030a0c030e0a0321090e1501030603140d09061103030106050d0b040f051006050c1504050a080a0e0a050603090c0609040b0a0801060e010506040617100e150103 74
    0x50301c54601010394410001c83c000740d040041d042c000c54030b02e4070b810286030080e60207800344d10784035580c1e240f0708180f20600d505d0380c0d03040202c8020304006085c6c000c841035400c100e504411007001c0300b088004a0040c4040e610180120000e580880e0312920b012038240d240000681da031080e020f03114a801c1d03800d181e00c8a0028070a9004100400c00f0603c10300140803200703c641404188183d000c1d0026003aa072004007050580303980c900a12030521044c0c0e035010024075140c1022820251446950780d20344001c00440486031240c02c00150802100b80b0110000c1e65110405036141d400e035000082c4400100344080d8000d08079088046420301d081c0341607078441c0403610f00801407904000b0501290750801c0d030030f0f1b81d0080c1e00d80e118a4442e81c0d0700340802000e004103200001c0c14510b032050f0701c079140a041c1e01641c020f40f400c01050210325030003402c6101c100022440d10ba5151540011030130b61000cd58003501a40791003005012001407044868610b1110036607081c810982c0609000d80760107405050054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 786889253 1250 786888003 786888007
    0xf150b030f2a060703021501080109020604031202010603080d090203101a040b011101020c0c0a0504090302030f0901050702060712020d08011d1305120316021b060904111b190503 78
    0x803525003a08400d022001c2c1d81030030000d2407869280440d00780e81104408a0141c0c001105011211406004050040180b80020b002c0d01c5405e40100c3e501e44958040508188860340c40088070038000d401c080000d590002503a40e4039a0707240e80880042c00e40440484c860b00800c201c5440c180c0315030203640c00d00803803504002d81d418581d07030800c030082c151000c03114140905041000c0c03103104e00703202406a280c041e00143c50717510441e900304256407001c5d4018611503840d2907005000700764000103a039403141442a09907582c02c48000181c031240580d880013075201d100050001d0400c06a1058403c0d003400035000c42d001c5009a1030b007910009000d0086451010071450021950100c0000c3c0d80e0700080c82901401032030842d81c41b01703801c2c0442807400301d5148000006124410030b0507080c180e04d0044620280408201c00c0c403491240c1d15002e10740c14499440810051483e594540c4030a00300381c00b003482940e83d41c0101d0400039801e200f644842d00540107040135460040102e2246824140e40040998 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 786890503 1250 786889253 786889273
    0x606030a151e050102060108030f0a08100f0b040602011406100e1507060c0906051c0207050c0904030e0f040b09060d050307050d0215160e0f0d0f150b030f 68
    0x1030040c41c4420001038254100c0d03100250000750100e280e8141d200d24424003411a05080004e803030005c0603403018609500412041c020f25540c400bc0d25040103945c034001e0a15190f5544c01c01c0d100c1c5d0660070010603030fa001c0d03c0002d0181440c00013041117800301e400920828041d0304404105000481c1c00f035030400c103586060383d5451310403000300c4203800005058481c4450789106240c92604214411a4055900c1c04500c00140d0460481c1e00149558640300e440c211444071000b544d103110000000d9807a4010a201040101c1406003102000000e046600540b4003400c004204205902010780a01d0f01c0801311035690a003801403601646014102d0b80480c2ca17103d05000b046103240d03800b5903090105100e02d10000304280301081a03146580e000b064041000d18a061150401400020484100c007001e4140d0310b40007400310004c003404039000100c6a04060105454a05000c4020102e11442408400700701c01000c41603501440804100f11240d1540149a55568460028219030f4480c110030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 786891753 1250 786890503 786890521
    0x7020610050402091c0605100b1c1d0a030216050a1a03040c080f1b1816090902040f1d090a151b030209131b050c0309060a0504180203060603 62
    0x804c0c203c440640005010348032481c07440c41c078403451201150460303120000d0140c40f02c05141d910b03015001218181d8503144411041c0c000110026044c6080c158070f8005040c0b008052070244100039000909888101459103002500c510003120f2621408185083c04a2141002c50300d03941500c4e1130104181000c00318800080003034000600403111140c8202010540c03400134801c0c203010028100042502040f615031210003a010f00d90414021451400c02108140180d01c210740c00140740d00e0080301e104080c41c0c003211003101035005002c055000180000f00c24044100d050100c0702008042c44070342905145a032034403a429074080556911034174040002c030f001c13081800e0495240000009800103000e032550240300c040302c103480100f039010903c1c00c060300303045032080221244502c0401a07101da0640071100000481000010060007045025400804108882d5010001000d46484103080e080061031035001e4069540d030f00d81c4103c440b82c2498428001d403806150018841030a42c1e54034045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 786893003 1250 786891753 786891757
    0x6011d0d0f0f351602150a02012a05070f020406080a0c1502030a05030702151501120606020303150a1a041a0412030f0c0204090309051804080703080603071703030f07020610050402 79
    0x3031350a040d000700c2082401070b9621020300c01c0801d841e001e100e40303036000d8040c0a82103c4850119801ca069081229041c1007a0301c10803100149040c140075031204001e04061200d40d0000c00025002880c002000c640d21400003591714034940708800401040b41c5402d0340400c0412070300c4240015034003e210290083e401500907651150f00c61040f2030748005295486480101e00350340c8012070440705c2e140310000f035070b000425154050f4100810b214861402c60000d6403844020004401c05080540c5900c2c1550f480140000400784c108181c0c812418011000702e40b41e0003441001c00300e8241c0c1000c2c1002042240c152403c481081c1d6442c82c80c1d500a480a485c003c002e0900341d02003100404c03d1000595540c4540341c031250090b601c13580a617003014140030340d1580360310420140c200b00c0b40c03c010015030080f080b01c480c691306250800c00d50303c52a0101c0e02d05200c0307401c4071100149088503641d1107080000034500c14030740c50003905c1e083d8807002000d81c0c030b903072054801c420104e079400428071060400e500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 786894253 1250 786893003 786893017
    0x3100b0d0b0c0d06090204151107091109030307050708011b020c0d0819120f1808090301110f09032406010c0503090409030e0a05040506011d0d0f0f35 66
    0x189640c90b10505596603000c40c0c14617000800103aa0201e4240904048441d00004529060030000394142c03850300260742e2080c29100b0340003015120b14413000c107040d9800589030f50250160840352108030303e28005403102a18001d00c00d2940ca800301d5803000b026030088584e0010040d40152607402d0500091052803218088299410f10007008140ba203080d6410b504144a40d03a5504d8243d45109540d011041d0351004044004960509810100621404204007880da510120860b40d80c0300a03004240074010100150081004c081004521803c926005040c1e4100c11015111303064003400c40b01c0091400c42814001000c01100040c0035540603080c44003030f090061080700d0810f020000018140c038130380d50040b400a0345160071a203560402d0301052001d400308a270144100d10305100000c1070360186c0c8601d20000c5508404440d100c0d1500981680400c0d008403001200b0b0903541001201161440800c03204402000348130044550505802820b4283d1964280e04442c1440c42c20105500600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 786895503 1250 786894253 786894271
    0x1051513140411030405010905070b210a0f02160c05032b0201060302040c0f02061e040f0326040b130203190309050604060f020f0d021f1e02030603100b0d0b 69
    0x1030f00a4014000c1c1e0806944a244070ba000400c07000c1488c41c050f81808169404440e14200c00d02c4203000c0503e2460020000c480082c0d241c00301a6900110f1031f014000010044100d94400100c24044191840442d04102d00070880c019040350380b0301c103055030392402d407400e4a88c40c800c00340700c07070a00c228108503180644507610010460540380e4001904035218900700c0700106000c56080388001d901800910343c001741928402c8003222401540305191103000300b0042c042c100302c840384000c150080044202c22180c18082850401600d00f03085445170058400740c1b6040d00c0c450005001d14001c0304500701e01c50307001e000384c0340e042d40c440f4170454013099010040b414040044e40100703080e11400042c000401c40356840d068024032096002c5d00700200b00e51091015048007044984081d00040d0090b2403050400e0f140d04031440c542c40c101d000388050f542600100e03060582c008042c44030394001d0341c0942011400c0d51010290840c0c20701c100e400031071955801001c00251400824909100039034070441d64 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 786896753 1250 786895503 786895511
    0x60d0204150b0c100603050606010806060409060e01141f05160b0901021201050d0503040b03191a12010603020a030f0206191112160b060415030b010515131404 70
    0x60074a68800a00c650481c1903500382c0402c1032014184104282421003444034401c1280f1811a00c03210745444000300f445042c0401c13031000c1580c1e0b80700e1100b100c004110341c0134200485c42c2c407003041c1c242d6941c003880750207400e01a8040000107440d050540070000c1690000c2c1040c0e0040a1034290383d15000703030300e903c04160a030070700000200b0421044188186040340c00103940315842d0014004040d81a080039008111442442c0002440001141c040d0380701c2c030180395125511050031a07500800001070070704023810098007540711407103101c01a20f8101300b29814005024908000340c00c844007488040d5101c1004001000800c00c0540c03140c2d00c140c00900a0f42c500362501c500000e043c00d00c03031440d00010b11844c2d06032215200c1844100d008200b5402c219183c000c0043c423900b0055030810300078010109039400708104e59290340c00100d25200100210b8036080d66030a2542c8070107400d104803405126080000c4250f1804241200c000d4a554203240c0500da0800314002040c01c11174019541050741c1e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 786898003 1250 786896753 786896771
    0xc1707030609090b010521030417101a0a0b0a05160c0f030309031412030703050a0915090506090a02010207170111030c090f03060907151e030e071d060d0204 69
    0x98002c4101d2140200a0f8131100d500d85818419445141c041000049081c80c2030303408916000300032502202c4400c047c0100a800d171402c1141400810404084101e10b000f100c0120040900306404200e0300484010f1312050381c540c0c141c403180c0305144240000035020060103101344069483c030038480d03001d001c2440500352900101c10404005801c264040b5414a404104000c0b81c18941c8000801d0040901041c420b400006003041c000a000182856100ca00041c0011030940c494207605801c60b658800c3ca040c1c4443d504000d01200c101500c60380a207000041c3c0c1c080002442035220760341a4014000d0318a0003070800b07402003900140384019500c8099680031f556044000d140202000407505545003850800c22596091138003800340a50000c4082000d07a000124866080300c8400e5144407590008460807600c0700f544101e038001c092202080d03030700c106078180e000401c0c000d40d4a040760300306070710358410a44809036022081500c240c3c000c002401d504000441070b450171f20190000c102c09003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 786899253 1250 786898003 786898019
    0x7120204080105010b1b030a0815030109020a060e031018020d08040e0c190e0a17070803030906041403030408190509031b0418020a15170703060f06030c17070306 71
    0x1000303900c85c0916141c003050680b410013000c460301d00e0204411001b0351410f0f1404070094404600206403080c1c10b194a041100e6a441c01e4029420055008100b9410182c407100d0240020741c800c0c0c4a58001c3c40703480542c01010070a0f11480110045540015800300c42b554204544060290421030340719009010019001c1c118000f0a4003400d48244010b49801c40d01d07180b440e2007858868a0410490030141a10044d111a0903060580304010b00481071042d460744928581aa56400402c8a10002040000081e80428080d001d14802c0c05440c507210100c1c0040d0b0754a00065a014103c20400c100b01d49a0034a0032a0b46114088241003680c141200c82e00001e0a01044008207800010390100d00e803003a281c03a2207080d5042502c2c1038a60008091900031509101e41c50103101c0c0d585281d0008007201c80d0045030745952811451517991000c0c544100e000300035040c94418201c01d603a401c01d002c140503019020382c420b0140c4656646201030700c1012030304200f0310060910001e1580d03440d0041f030002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 786900503 1250 786899253 786899261
    0x2535090f06160201180c0e100b030403110304050a03060501030203060603010c1706030a0f0302100506040608030d021305120d081302061213061d2506120b03011e180b071202040801 79
    0x80c0c01b0b118882c02030b905e400032003101040002c0000003401c2c10304209019100f685010b40c2d41050300f514020121000c481d483c24903621560f0400d80e40403100300c100004014003604441d068902c2034040c1c074000d8888005160a03500d0381c03030004011030940d8030802e2a00120200083d0711280050440d404400e642e19600440269003d0a80041c0c200100d103444030040f9000791500144180c40411419180000c13080e00d034098802c1c00681c06800090500300d001c041c0c01c0c514082c14004104100580e800301d041c695602400410b000451605c0f000155806100f00440780d19907000742842e80b40c030051100100c900d5200034511000004140002c0c4041461b42c801c200c0001400008040303004074404031585008841c050409100c14600503403030701c4ca40f800302c0c17a004590250a15103403060000c0c0c0501c001c0c20850030381035095840d00880701014540c0600b090101c0034108030400507000c500c4561031612112070006054068420046030049202d021a02c0c00500c00680050a0584a0204070f083d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 786901753 1250 786900503 786900551
    0x1a0a12150c1e1701180227030708031e0c03270a05030712030f1b0b040b0c07020a0501080702032710082535090f06160201 54
    0x700d21a03a8076802602d11001c62a42d824282081c032100042d4801e80300d8004014080d8032064201c5482c00400741c03150f42c05031080d10501d05015160600c4012090300030482a403070040c80f82c49010000204018044103c588030528506d400d00d4900760580c0c580308075440b96400c141130f84820032400c85602104d0361400d01ca042c1c2461842c0100c07201104001e0350100682020b4031039001070804201c4100d61311141e100d00c0c1c2c7d0500b003c5a03405180c0e81c054890a4100440c100e02e511103007485010000c0f07842c1458422845403428030515200e00503c020280140c01c03000b900403045040c00e211540c010700480b0f500c44520b00c11a40340c13610002e0705110031483c52a20034032880900b5500c1a09150810b40c41c692800c0c10315288041d481c00e039040c2041074540c034100d42d0001c0d60400c5440060b600c02d8040004002032401004e841d512555400070703031007070240b8800030302000200c003090340700c3c0020503070f000c0c0040584014131480d11511004260180110451025503513200c100c0185510300111032940 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 786903003 1250 786901753 786901757
    0x3050d0c1206090c0206180f12040602060c1918050d080c010b1c0f0215030f102403050a0f05072601050d0b06031203191a0a12150c 58
    0x100e6001ca40d00c22041d101250403030755540c3d050a41c403e00c0303290300080890b80f00441094007000762040501070303401c1500407503400005000f072854081c10409400300800848009908494a9550700c8190b14814014950405030040400b846004940e1080030151804d0440c00d22000202d40d031000002c10201d0a000c0483e13058001254505e5400020700c10034409001c15034410f030401460000e011411042103400802c00c8034015900800c0d51111074003105035038900101240d40781040e81c4104040101150440c0341030848490101d05141d15070b00302106800b08102055007042c3c04032041e000390000801855407166109281d204500f1035015840c041c40b4a900e8000d100209400c4a5001414143d182007108003114010031003070301e071100c441d1025038100905454949401c2c0000381460450046c00041c0d004c080280104000380d4001031904504456080105507081a24850204485140305a100516210810031a42420b214401041c0701e5010b00c07240f98041c010000840e9180c244280c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 786904253 1250 786903003 786903017
    0x603070e030c09060a0315140f2203090902090f0613151e030207050a12080105030d021f022109150c0717090a030605012408091903050d0c 61
    0x100d42801c0c050201504000d5480a5070340c0f510130080740c203840b02440004c010800c04070954000c0815a8483e40c2c07441c41c4003048a105041c01a408900c820f400d4a4003110780890071004020500c06440d0000000e5150726a031161a02d4040104001d410a060b0140c0141d038030078504000350b40e010014060380304612101d00c1c031641814101080f911504d041003084c455144400c0c08110401e07624220003000c3d0b0f10f40075032b9890242c5082824018840402031440c2c6804c01024181a000003600e81a00c0080d0100c0c3c2042260707400807640d401d43d012403007020014414003081c014081e0b800078071508003094598201504c120400c000f15400c1201d080b07a66400204201511986000101e6000643d8000b41410700060303444031000748840381701454100000040c056410b454406081c801141c001d0780401c05580e49900301c1b08a5400018905e48002c00301c2000801c1a000b4901c4e18011039510004103145c0c2c03111844200c5224250310300703a0910400380040d401d0903205020704c10450b0036a07581c00ba = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 786905503 1250 786904253 786904277
    0x809010e030d09031b1707022b060e0c010816021207110a0902190f140406110f15010303050a020102071e0201030606030c020a02041a0a0e0f1b0720060307 68
    0x10288400c4001e40f8403a10039190076400800d020608841241b42d20240ca55510b04031840000e03568000d1407603c0e40100800c15400071400034909000400300d0042205124903160040080c1e03d40b00c5028096010070314400108a5496540310515201002401140e40e42180c00420100a4008001c221103120b90741188041710f04002c04d014000308400d44040d0308041d40c045d0103241040e001f42c541c03801c0045a10407030f48402d1158040c06c00030140301c02d2565407203459600c01800348200440c42c4605224003882030412240000d05e040f16035000c41c0c80c03008283d003551b0f42141c05034001100344003159000e003c017501040b0701d000301010801d10302d9850202507140d0b100150942c0c00350781c01030040c107150454480c845500400c1d18080c01d58101c07000102c098000043c4940303c7c021400d01500a0204c0e4070200c0c40082d140c401c5c0c0d005408070341134642076a81d01440428408021a990310805000340410000522030070302030003150045200c00c01d100384100010403004e8000300d61030380000e40d55040310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 786906753 1250 786905503 786905507
    0xc03030e011b060c09090606050903160b0a11010f0f060e240613030b0108031308060402030a08030406141005041104050303090d0c0e1306061508070809010e030d0903 73
    0x100503942003820800388502c03424080c82c00058510501911207602c0d005042c030700c14810108040a000ea24408105140d190600206541c000d0b40b0315071300030f00c980d070200074080d40082c60942c1107403800e0304070a14180962400b01d8512840103800c40c010343d242e0314001240c11541c010380900e5642003100040c00b070715020408409079405488990140305040604442012800001c5110403099680c2a038130180d0500c071806030111503001034020b00600380007080d000e1b8048020f06070b05001031107008040b07803510200c80e207800c002da50083d41540004078803000107000740c000e964898000c0302d000440e100e007801e03179541c00c40c4201c50030707181c0003004c036400d00c0580740038440c1044203e034803007155003802d0404c0040382d640e215034410b44d0b101e440582ca54a04012500c0b0011024004150300483d81e424468000d1000d0100b850040310045c0c113200b401710b0044a10085c50f8540324165654840c4c1351078043c003d0340c524002030180d032000e541380c400a4080d0700c030030002050788480020780022071010364100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 786908003 1250 786906753 786906767
    0x2070f030f050c0a1103161e05060406020c15091002011d010b1c170d0902011704030203030f06120f0f100e210d0e0c0906030d1205130f0c0303 63
    0x9070805001c41800002d00328100000c000000b03650260126401d0307807031400000c1c0740480703203c031a039411501d44401290100e82036010041c00d61500c034100380c0154031201000000c2c0100c0c010440142e0218400c00f420380340c2500020b203040d0140c08164a8840010b000c10400310240503000c01517034641e4a4024801070100d248403813201d46100030441c10030321500141c188516480161614123072204201e05003c8554a6102c86200c1000a40c3e0396400d1403000c01c010f4000040b09a0106554202d005056080911142c1c4a070741e041d40031350300d55034841d2200404641c01402d01600580c181e020030440c03590401440c4072010b0604028032000000440302460503000c3e0131000103803400e004e8681840480006d40603420000b0703080d03584080c1c4254040e801a806640398411b0302500b84a00c01b0003084000c1a009104407040e10450b0b0103a841c0c034181583c82c03202d0800e10000400810402c120340e0060b0740210303085021503401c89034280e8143c9071104a0f000d5100c05403017070745080308100109504a80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 786909253 1250 786908003 786908027
    0x603050a12030e030d051b121005030610051212041d0105180112081e07120806090615040b030408042916030201150306060f0603020309030702060a050d02070f03 71
    0xa03007400708083e210040c0e6142c1c061403481e00c40450703c68000c610180d04241029400c80380f6052025107440c0c204100307034a1030909441003850944001c60120341c82c1008100035100311364182418103141d00e0001808922412000720314082e0050005092148040c40000e01c014020042140e242141005907212802c030b0692000b407040001146800160521080150444516202c0001e000301e00d41030582c3c1e6442031813107401c00d414001482c641401400340c003030100e80340107082101c0842d581d0703081681d030703820103481e0a43c4c1304640400045136883d08030440a402c840d6600c031282401c1d40c0d02c803507010581050301c048544260104007880807040d00203000400712840140701d0f00000759194042036a00c034094003241003100d420402414503000350405c8000502d000c0c1c1080c2015070b242030200090815000e885803c0350800c000094441c42402643d001d05070301006107182081e03e60810400f540040d50040602505020b5170032041c01920207420142d000344031078030b80c01d107091400600078600c0c01c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 786910503 1250 786909253 786909257
    0x610094a010c353c01060e150307050a110a0b16030e100e120414010309060e0312060108010f0807260a051011040e060904060e01020c0c0a0503031207120902040603050a12 75
    0x140c400010115511350441e8018240800e0381702200f8045000200c0d503284070144408000f003031110455100000b840b00229680d03070752032981110200940c8418110001a240312107402c00304280b03802e0200c181507030030b8807424005480c0380c2601855042c0309203e145038001e01e903640e680220000041c402c00d448480c1c0c4d02c0301c462406080036401001c010800039140d041542d03c0c1a01010400b5542c400c0c801c6c0925802141d880301016655000840012034189000651807030001521040e40407400040e180b201000d40107039400c09131203003070300b880104e02c440312043e061a0704500550300303004a00000b80140060198942104404c0084e904603a40301e40c80c1180421041200c85808546541c001600b25010400c50702c0740c0c240003016110005010b4102c0d4400211409078140c0000d042101a906031000401c1d15900c0c010140c0301e002d804850781103404c00100142816116111810002502c154001104801034002c178044900a4204484550020710400c2c00c0c071042c031501b00c400300054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 786911753 1250 786910503 786910591
    0xb1f17070f050d05040201021603060f143715030c060f12020901020a0501150f09060501050f0c121c0e0610094a010c35 53
    0x11400042c5107200798000c0398401592a00428111381c405d009500d0040640d0440085264427428103070b0042c00c03241c20746180c080c0303440910003d003d10904501d200d007a590b040329081c1010f402c441a501e0300c0003207400500214009090a014400f1312490020120308020301100c24110b24156901070820b070010800d01c01c441d1040300c2c06a0303200c01e200c0b00fa00b0341200050703114186d140041c0c4c600703007003000000c14039402c1840086d51500b084443c1c80444004554140889554040010445006000351030001e4400c00021040a1401009110006015007110394081d00e485504020750020b40b1000018010714448001e00c800500400c41600042c50140030142481e01003240411340c2840f90840d61078998071140300c043c910807020050b20425410400d00340e00e0004c190810109640e805000c003d004070b2301400341c08414890003480720180c1d200c4c96402c4010300140341401c0d41d58081003e4818050001040030202c0300c0317015014030b4407407a0641e10005400f216400c201c01004003000c4503a11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 786913003 1250 786911753 786911777
    0x60f09021c12050a0513060e030d03090206090409050f0f06070906030e1c092601110429040503010c0309020f011110050c0c0a1a0601030b0303030a0b1f1707 69
    0x1c2032100d18221542c41c203140740c0d40c1042c110181d41d0340c050084450703201e2140190004005070480c2440146000807000d440d2031504038030040d41101c5c150350010703400140c1441008000d051950100100364090801c079144c00300c1c1c540305c140c41e1003103116840c45290401010b005081d03401044840141c602410207000400d80c1410b0156220440c0840300064410381c09400f5005000312403820152080c940d40048451243d41c2c0104090488c030b01c5100309610b084c0c4080203c1c003059043d82c01f522000b0181440c225a41c002c1a40003d6401e400d200d003608081100007142d540034821901c20508641703021036115001c1c01003003003524011021a040c00319029803030342d10305400304241000030500da5002960f511030001c601e58500a10084032814814411043c00340700d884454140500d03d010304812840d0f641c078004606039200d40c68900d8050340b003440071030a4030039070313410480c0b4801018114a00c4e6102c000354440969265000c0a400b04060003c2d00603481c440d007180a5000301d8074100003080c885 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 786914253 1250 786913003 786913013
    0x708120d0b0f0d0b1914040c080706050d0e10020d1a04230915041a1005060a080403020a1704060801150207051c1502090102010b0409020f041107060f09021c 69
    0xaa101c8002e184811620000f00a4060f0500c05410340449407000c00c552000c0645042080300165008c0c2d5413a0141e07400040d2000e00010a5419285295501ca040c602c6c4290040c000d010605004421400b8448044801220601c060030110171101801b05e804070a82c101040702c940314150050080341000c02a96143c21401c0f8841d050200009201840b070b51100da03003500b012541c46501410009210501c014020040b0340c020078401c2c0418540c040340c8401020f003003d50038a12926400c05070612041d000f03d8020302900b80d205d8004d0050325104086980c0d04c4c0f0640c400740460072401d240225040c006150b0203040180542404440c129401400d040040d50312074691041d28850446a40341d108400d440d4103018841c1540006060345126a040420010703401c220f80c0d9500641c40c2103005902403170f290254403401a00904041c02d80c0e07001c501030101a1190307503041c42e1001000c105040025503c1d200707038070013404400400a4101034510401c115032403103030590700301541840c101002040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 786915503 1250 786914253 786914269
    0x8060a0c110c101101060e040501090506130b010b030a14070f0f020115030b1909050304060809061006050a0201020c070f0f050a1503020306011202071b0906080709090201020708120d0b0f 82
    0x43c06403c103000748400c0740c0f41150140215421566941d480c3d08103020800505400030495188a40199051903540703803808000a20310140c00340c0400300b076a0041040107500301c004c0d41c20a0040b00c0c007042c41260703500d00c504103d00030742e500f03400507c601c5002c1d4249176010b185500c07041620301c000e0048041010320041000710300e01001d4042c00303c1d000400d0140303202d010a01540ea4a86005005a40803818516140c0e0442d01c00c2c8000b00344000002030b03800c40c001c10b185101d601c6002100c40b641e400c2000448150b0040c1e100c02086d907508100c40f81e2225030800940c0007d005000d541d0703a074182451040d1400c80c1d6198052030180000442c00d0012a031044403d11004046140040e1a960317a0401200c540380c1d08a030021b070301480065280e0034403404030402d049680c0700d4a600d00c0215076034010042181d40b248516002c54011440900c0700c490107030840780c5d0003401441121180e5844600c464100f481801c0c01400c82040010800000c940c10b0141554001d0111100e4190b40740c4007002c0b4a44c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 786916753 1250 786915503 786915529
    0x3070f0f1b050604032a06020f12070503100e0103021c110d14210f0d200741070b03090d03050702070b0a08040309150207140303092808060a0c110c 65
    0x280c01241181d05920304008ae120194505211304070ba608000c403015200e03a1094424400141c8d824001140301d04580001034122540500814025070000f0205148402d4050088031645004c00318074080b640d40e01d42410005001b0104586114aa0140c061410036090494800440d0a9032000035010f001d000783c407034240000c40200d60311112401d40b200140840c0c06180d4140101500ca61000030400028000b100d1040c1642855403039403031000b0103040584409021a40d0442c4030404100b480d050420012075078050844501e592180c0c1c3c640066001110709a80d01d43c0101528181c8a505004441d08000c0d03130b0010340b02e1941401034a441ca1f1182803803090034400300d0401300b0109407103502c249005140c0719008040305100b404000f910744e4014031a403446222031016221443c90088121050544001c00c20f010603444615402c0d640c07442c034060070543e41082c4c1c800150b001c03c1800010300c51700c1c91910009840c0c5940002400d0704010305030805a5622030100c5903040e450b08070b600d040c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 786918003 1250 786916753 786916763
    0x5040f0b0405070e0103150c0c1e050a0212060601022404170c0a0803150a0503072108031f12050c040b4203070f0f1b050604032a 57
    0xc165180d081c807a10700340743d980c040351007840c03040000010f122011407005032008100e6400d00154078280c0044840c0301840201030b01d00200301942c1c0c1820700c00c5500b0b103144a41310380d0a54082c07452540018140e40300080c1800c2458100d00204030701580d05202400708020401c3c400480074411212035401100000d00003405a11003a002d500c0001d001c1e4240c4100034120011204ca110281c90041247c0d0801d45801215070b140c800750054514110810200b61880580100703602807a10501013001c00c40740c41201ca0302c014000c4000080f9003100000c43c403542c6a04e5010000c11801084031702c403a02594041c600e25503021703030004002600420b90300c2c1c40c0300080344d0101c6c4050907040000d042d01c1c2e501d210948842022101c0a00303e1410110440c0713402d841e03007500401000030f6144030f2805d1000715004400201c1c07400b02c41c0c1c8194081e00c610358508049150186200c08802d80003500c0721040c5c2c00588142d840642080704050744071041240d180102c01c019454a01e100140780300341c001d00d41000b04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 786919253 1250 786918003 786918023
    0x15030906060b030709060806010302360a0f140108070815030718050a05180703060908120708250905010c020316150912080d02030a1119110105040f 65
    0x200344003098015001900c90070008580d80d04200380c0242c841107181c81610041000384002403a40d60081c802d68240161001806032200b1100b0500c2c4889081c40300760004482c0e03101c130115055250011404084c004420802016908040302107221000c40088141004028410810f84607400351055401c4144110310b902030402201c006400c01e18940c120201650754446c1e00440003000e41c1195005090010781049240c80d41d04050800b001d0410240809a125440c1000066401c1d40035004a500550f10b07035003000030b405c1c84264031510a81e82c040009000c903062240100312403554450601f040c800e600a51101e60720080d003107400c1c92050f181404854000001991014171440c0d41e0b07140b5000148005644910030800304441074400c0e040060b0b061640401e541c6c8003090713030009443e00123412508007101c0358912070107507000038280c00409440300c86203007040802c5006440100d0800e0700060925501000051401d4940504814207038146003c1c040444c02c00d02110740e4058010300058 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 786920503 1250 786919253 786919271
    0x1d1006140a0918020a170112080307090519050f120c100e030f0703030f030c05160609240b09060a060530190c02100e0109020301021b0106050a1503 65
    0x24902c4540b039400040d40420b5000e61607801c1d002c95000b41006081d6850304180008040c86000f00c4000074010b9000b07444000c5042c3e00071860300d2020b075511100c54901560b5240c2c94102103420019800e000d28400000100d0078409807400c41900101d6041c140d031440d07030309100b17020026a1048503c0c21680500c000030300800c00c1030301c1500d409011403c0601110001103184074000e5840365644002e80000c1d410005c500420b51107401008806a4140d031903c1c14031041107010b060841442c80200c800700c1c1ea91701c80c4000682c0c520300c4050f65500c8601b050790420640e4003100c1c15220f06045041c4600307108400c120700359a9021220054ad480c0303140454481d00007107880c4105060098060b0052654045e0380d0b1304120018040e241720364400030039440a9850f40d074020094174035540000d0096085800b04034400b440503800640040201400820a0441a00802e0899000c40d01d00f1500d81b0b400c44800036030310300901441d001030900b681c800344030368604851094070346202c0312458105503c4103251 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 786921753 1250 786920503 786920507
    0x151a10210917030406240312090519050306070c1e060b060309030405040b0414150112060803090a060903020303030109090c0e0108010911010806060f071b1d1006140a 73
    0x1408403a03070b000d09801c0705030807203400000881c1c00489044132128204a0000c0900c03e6501c08001e03841601020041c03124103681c0e400e0744164a8480d46810450307141c03000525075417465912101d2000001d440301c40039041c142490b04140c00100207409104002081c8800502800c100c8180301c03803088114401c02c00c240c58003001402d895210b159104202106002e880703080400148101c50049900304010190381042c407050b50740c003d500c4c2c00405d0038100001c46210180c043d45602190500d0a41c03180d007002005030044500d07541200456520224401505042000408014102c182469081c441c03440e40001c4c1c1ea44014051440807130340740e07034008041040c0c05102c03001410b0441035602166071503020300c0b4000e0003417080a484190003026621155400380844901941c3c01405180c42e050742501500700301d40c4050001c4602c4034445580f0204400e43c1c0807480080c0c8480b41104072074400c0702c3c2c00b680b801d400140c5192440041c5880070000f20303402c850056400140351201580b40c000300303681 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 786923003 1250 786921753 786921761
    0x6070b16020601083915030906061e0f03010908041203140408060714091305072601091e0501030c0e01060e03030702041d072405030103050c0405040f151a1021 70
    0x1070640c0100d1a40442e4501c1b00c298006184070ba100e29003220855070f110b004001c09003440c1030342405403001140c81e0410a00300070044036428180540040b94680150350784c10b005500c103601c030307065250030b030303032003242010341c015050a2038680f8240e019040c50308020b00d0a07100e0101a107050180449078103882121481d00045c0c80e0007583c010400b22000034000041009031104440c510002044941e070094613482c0b21108081030300310700c042060b00b40c1c02c1102000c01440080c40508030b210f007048000c07103040d9040c05814041d510540c4440d81003842c243e2030340796100c01038011505003e00c07080c8030b0401e601c00000b0b807414160101e50106c1c40090541d031500d070940b0155014a9240640400420b03a01c0e0107409841102c001200308545080000500f254203001c01c0c000103000b600180241d42d0146401e80096030031078051b07111050120400c1c1d4580840010241041e601c031600d07080001161001006c0904810100365109003400303400703e074018107000600013610013050740011024108001640 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 786924253 1250 786923003 786923113
    0x6030e280c2402030a020a08030a0603060911010f1d210102030a05150f01090b130b041215060621200d0b01090b030103080906070b1602060108 63
    0xa03038600d0302c03540b05882810040100500000c42a81900085440001100c2051501d5806040b02070b4150361940c01e41e900251000d150f540d103400c00480860514491200a02d03c44ca90b211a004a928000b400c3d6082566050040c000541964001d844201c1c0c800801075004070b403100700e41c0c0c00b003140028045c480e1807140700d22584003008100710030205601c500d009495401c81001d80c02d085000f00110954001c1940d800295840d10070040042690040d103640304400b00c2910b00a62145003200d0b280d0007a5005905180d011981d25050000f601659031381c0c07115008003401380909100001d4001340480c0f20b42d560301c0071040d00802d401030b0b01d039024030002001d0b50f01405680d00501e0b00c07018242c006e1001c09030840c1c0f40030741010b0158090b891420480c0d0103030f444a030850b0729584414003150841c0b04c0c001d0f000002084402e00040b40c0100d441c1c8640e00d4240108100d1202410092510b0340c140c1040b00a61302c44010f80c5540001ca440840c0400001c61144200b2038031400300090300311b2004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 786925503 1250 786924253 786924263
    0x40b07050703030207060513110a0b0f03040c05041b09050a0f050f0f1509040f02120103080705011103070507060c0201060803030c090d05060108030304051902011b020303130b09030706030e28 84
    0x4424000b440c800706502c2d2540f00d004003803410800311901c0030804414030300d10501480bd101004805180c160038005198014000c507400b031201d0740e0743c402050680d890100047c0800d80758128446045401000d000b025090070340d0700001060a0801c04152040d141c05100e110302143c9004100030740d6100349112002c403000d090740e1080c46007034484445035044908200c0c810350402600031704c5040c02d031080d01d810702804031405a60381d01c1c40d00d4080341d03540690740654040d52900120034110600c0d40040d4010744c6941d8500e984c0710100d0030b0140807181a40280030031641030881c2001a02c40000640340c129400800c4a995a101200044d00071606407000800341e006000000030750242c04000340d031203580210103584210b0310403c00955981d421003402800305640b40c1c884082460089190750b00603101900b01e134600b804541c0090504005980a10809840029102d0301410203100c4500200312a04060088034051041562554040f400041d208085803104c4155240030084540606401c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 786926753 1250 786925503 786925511
    0xf071209090e0115060c170309031803030c070915081c02150f04030309080f0d09021219080307050418150506071a1f080a0605010509040b0705070303020706 69
    0x2054014018449a114a1004500d0a5201021000103004001c511040c40002d180358070305000b41940d070405044810b44030311500c0043d0003021a0140010750043c22030a005688613103110368448440c1589180301e600035041404084101d1200040100645072182c0e0003041e040442004001103120076405401c2030706c58040b4000c071f420310b242c84a803075a00155007034490300380300703050036000809042c1da4105040d1112000100070902c40c0c2d0080300c556220b01001440e103891a4603503a140e80107504038070145039464049400b1403a110815030312003100f042c050903401c2049880e5200301d085500c0b01801700400000050303102881141242d01034010f000c4c4405210081e103c07000001c00012401290302001803402003030516041060303581c441e500c00c440403260302e13000c454001c040030b0241120b00d500c0b0324107a524a11800103041c8402400e0400c2c0100350001843c2000740940e401a41310300c0c09040d1080c280b202003442842e03111b500c07031001d0410360360700c51052070200c0091007200806403c292074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 786928003 1250 786926753 786926783
    0x210e0703060504020f0609030d0e0103141602010e0f0a200918010e01060e0610140a020d0e040606051213081c05161d01050c16060807020309090109020f07 68
    0x21a800280030f28001d4074a1401540a042804424820074554944c0750780301100f0180070f2403103520680303854070061401046140358100540c40300c01c1705940340016000400190710a4035824483c5408828000703008007102c00100c5007241d221041c855002c1c1810f03141a08e0400c3d010744080c903103a000030026008100034900800b100101c1014003601890550800303d92904100c814021002910240050100181c076280704002460406001c181c0c1404070001d1051409008140030303042c04031064002c0c1a24030145034005000084114006102d075241c00c07000d1146517480000c3d503110600010207402c81c0e89850719061780709400504005d00d40c24000035209500741640481d0320f440301080005000d50303150000040d0304500c100c44a0320002d140011000700c04c20580a204845c040181000c51414100e40c85030f500b80a00a4030849048130841030402c0441d0b441007480b0b0b4003107070310b00c046c50500010800141c030160061080da101903401240307050803c2605070032604003d80c13000107241007140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 786929253 1250 786928003 786928013
    0x31d061c020a2c011d0409051f05160f0203040f060c02040c0201021804051806090a1e030c081e070f0b1b04050621070804110a06210e0703 61
    0xb010b2500400012010103149400710082e50b9207080940b40780b0340c00c1e503044490100440360112003100c804940610b00303240f00d601d52a944900e0b0a40c50103400909000c03080201d602000030400c44100c00510f18200820004030522020300c2442c0805191858540701110340891840c0100c1c0c0120613903908010001400c41e800000e4252075910944d010b004122a101c011388c200d000c1c51003000718100c07801c00c1b642c2d490f28007503003c56444843c4090700000d904407600c4292400c442140c1c50a416404a01c4840c01c0c8802c1c43d2180c81d04a261154106200d040761790000c021010300f00d0000d01030f0b00c0c0455038544281801d481924450300e80544961901840c2c00c00c0381010511120945400802501280015004200710201c400392860704c0d516103132828081c4110f0394881c0d008202c092504ae42c54a006103580309459000c3d82c9a503982e455a42400d0400141c070b640c0d00c100403441003007203150030071900340c001d036009420000319100b11202042c1a98810b010306079080214116014590001c41006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 786930503 1250 786929253 786929257
    0xa0c0c0e04030909062d1d01030b010b030c0706050406060e0f040c061e0c0c091107140c091609240306050d0308060d080412030903051603031d061c02 66
    0x80e0090b51124030895442081c0c401329412070107541e407050b00002030114111003140780d46d00340343d4401d001548400e5035070a80340801050981018501c07405640100107100881b0201c07409032500c1445c4a00d50b08041a28101500c00c010006080c140c0307400028042c0402c0d81e000c00000c26480b030325054107182001f03203520181800c5030b0480c2c050480300301c0030401d24400c0e02c000107405101002c541082d203440f41c066941c46480101184d00030a106400f085241090003600950741442c03001944a80032840c00b0b000400e8020320702e60b2660301a0300030070003c0e03480c2c101164222658200004003040800320854008206801501480c4200070502010010703241014a403c2c0055a0410150341c8442c208402d942801e10060b0000748580003223101d900d080206010200c2c0b00d404020301c0c10703075910381c1c0b12000c50003500c042d40070a14600c0100140041442810b40030110341540e0304038981540d501030002140018175040d151248800b0322000c1d2074000845054043c91903a010307030800d190140b03070069 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 786931753 1250 786930503 786930511
    0x1090501050f1611070b07050102040801022b020a090905090c090705030105010f0503040c061b0525051c1101050d14060a050a14090c0d140402150702060f0a0c0c0e 72
    0x5a0001c0d44402c0155200b6089251500c13803030070181444a16007400b04000e03411029058400355030822000031400c000b44020702209904000250903091403240384c1d42c0690000e480c9035003e03801006a03c0d000b96102c2c00301c0e1f060f00d030718a80004954541403211031805000d159083e400990620505c0358141e000b401560407200240e0303c0404c00749265800710380c10b0006580090007204d000e40d080c840c0c2d500a100f500d120003480048c00b01c1c1c46d03880d0749500d46841c55a5030741c0c00b5040c500340c02da2410440d1502100007d80300036610321079101c207030824107a0340d504070100c080c0c00c0d12000040840f0a85c41201214941120076100784510440c50341c45a4840c0ad080c1e034143e00c00d0251b000001000d09144004038202c0c0d0281c030407620300c1c482000c2440204200240030b81c0b981035040040d500000450701c41d0302e40c1e505201c0f10300c488078030b814414003d5031410b07050480550354040c045d40303005a5400381214040d03030200340b48039264032440809507490078101100a1900168813030124609142040d4035100e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 786933003 1250 786931753 786931771
    0xf170a050a060f05010203070b0403111504030306171e010b04110c060a1b0c020d02040c030f0b011e2f0a0b0a02030112030e03070f090e010b0604050904021201090501050f 75
    0xb1290745a10746024045544640c50140e0424441140410448540d035070b131040c0281004031044c0850003583d42814401c0034030b2211100b140c1f051105166141c417403900902504200b4502101d41c1005c5070313a0350701086642d0302c1c1040d034456400001c004290004002101c020b0710501480d9050300c0600520340048582c45034520031640001c014413014080c99001d0050a0b0300300c80340c1c10f45580e0441d20348203074001c140d0300005107074000c10040c2c6540c0f09000074008240d0300003130803034a041460380a17259138200c0a41000b07400f0410240400c03441c1c280354442c443c1824039445003107412403014503096045400c055100307042d56404907480c2d80440c0c907000842c42800440b40a1ba20308908500700c0c00207010316000484421041e00c0041d003d07461010b80c5410042c21180401e0307403880744104900c1c5a40062040d561503002c0c0101039202401391851007a4100c8040e410a820440459004900100042d10640f0042c22115581e1000e40c4201e00854011000784a20302d8031414800d0051000c4c1c030503402c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 786934253 1250 786933003 786933011
    0x2107020d021207030c1e02060d060302011e022a03010222121a06060c010c021b0603010e070f120e0705090c0903100203090114090f010c050a0c02010f170a050a 70
    0x2c1d01c45140c00446039180c0d07168a038107070209a0741d20b84407080c8120744100c10001800326210800350b41c44070044c00060740001000f1480e14118030004100c11040c0300e804081c00d80507602607041c2d036000300d1410000780340742d15200e010810701d048640c60f15844480302c5c0c0d01940300160741e4030f881c205032184400d80c40080031692101a40c60b40000c02d441c080d40b41c003503d110001ea1a103140c1c5c042080700b0b241c110034014256424141001d1903e0308407007109003900d025910804080d4003046c1c8003460070000100840c1d869003150b04d403074802c2302e440c580101100100400e42408541d4540580c021180d03000e1040810000c8a0112044641d41c3c503450056501c00d508000000d120351a2500c2128100000540600038051803444610017a4002405102c495501c2d4040b03209604464655584545003031030042c981254160031007400c485083c213164041200c200001551250401c89144180e542031038001110310010008a44010585104014440c2d000b4140070444000da0000c600890001000300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 786935503 1250 786934253 786934273
    0x60c1d2710061e020a0201050d06030819080112020d1b12050f1002091e041805010f05070504051804020d0602031501020c09061e12151e100504022107020d02 69
    0x3e181e1010140030340e00180d01401021006500c950041c100b541c0700d010010800751389039a203621054002040d8400c000001000440c80c40e5404401c03540104800c1d1514851300c0e4440c0c000c510781c05140c007001340140303c1c21100f03900c5050007074400740b00810b4142e885010b0491b09103806034a8a5280d51003460b240300d0a124144125540e10848411307201c010700045140442ca911001c82042014000e40e2240ea5087e06254204101442542d841d00c18800010b401c40c0e40c19105040790f50180c45030007000300038002406180c8030113010f6001843c81c0a6002203030364803480041c2e424403107941d00922030350002c4244064003840089140800e4000d03029180000c61920a1104803081251000d40c0008040e03088507000b1250100d00c04801e5000e094080810002c02c41035190206140907580c4d001c07151001c00019590743c0c0800e2001400d800c0c00c255590400030300303030030300850b80e4041c2c2403085a00189812845400220b20041224443c00361030300d80ca40700501a4844c00c4528030310000d401500c0c844 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 786936753 1250 786935503 786935537
    0x120506010303271806050a0b21040807200d060b10020607091202040b030307080909160e06090619020c01030c03050907060c1e06020304060c1d271006 66
    0x30042111140f5880701e0514201408007000041c035101d03000307940d4030b110200f215140e07c03290002030400c080040d940e0b4040240c540002074003000c500c00a8403100010f001c000384048003100c1c100c64214400040303000c090340c05c00c8402001080310b16484080e68101400b00451034210b10050701044030b180a001080340300507602c0300f40c22617450002803410041407101c42c942490320001540040e000060390840f08000c24550b6000f00403d40d08081c1c00704070140c05180c010a010340c4281c0314444204402c0b0365031000b03440040803041c528469240490321840303d0b00c0380000e6460070f140249208120743d0908402949030742e140c1ca045030010342000d0200301258020b00840c0c0c003640390000140ba40a20b030030f0003180d0300170f0b44540849004022880109000d60f800d0124808207005510062740d80c1000c1c03a10808444e00c0b00310407024000d00c040c00e082c060701c82101700407800c081511940550000046901d15140704120415201c41c2c0d21000d1211041d00b0219003000e85400b0b4451a800907400840c1d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 786938003 1250 786936753 786936797
    0x4030609150e070e070207030203060f060301110c15220b04110d030c1e1502180a03050a03080c09031b03010b01020c06071713080a0204050a0c09030b040507120506010303 75
    0xc1c81c0983d403103030710204150405286881d90041c11071041d54070325510b80d40000d090000549805030112105030520040b803800388a18080000810090b82c0f500a02000c455242c0e0400128804000240c1e00080c907580c2c405c499100c004141410f0050100320149441d40d031000d0152020307070368000c2502c516076481c00c2c45010204015010703194000c50703540d1580c880c003500013410140c20205420107265070000e80002d000041e8407000540160311240704054194020b00c100c85454407a40400d0400c0000c1807012801c4549540c051824035482c0c0e8880b20314000605c90104540d82501c161401c104e44000b0b664908581d0407800ca00a0100d44130f803400487e030752910010390701c2c2e12400802440e400100346001c2802c0d82443e0161090406017101410740c9254a40d80c8410020382028583c41c00b1860303d4824294840c01900c0104090b050b030240080c000d400c94000200341c40070354008070303082c06000c000020007004107141c00d20074480d1500d40305072180030030320080303021650b1050340d421450301d5240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 786939253 1250 786938003 786938021
    0x218060408070506070515070206090f12032a0408010c090909030801060f120501030308011d0c0a030905031c0617070302060901050703030e070e1e0402030c1909020403060915 77
    0x8020105941040f0802c0b000b07903c03604c4100e4840c4900b8540c090607644040c1d0740c0d84103012a0b0041c20391860107908650510301040100b841c40c0d042000c1d0f4121665100042d03e80011003407428244144481e20024400900c40c0c4401c1050301000c9800a4040015002000001c1c0300b5500e04180a80e80c421020a84480c104004c001c65240c400520002d4810710500ca041c0302e0500e03000080140c0e441c004404c4801c01e8006600261440300103010303190310081030b2048014544659441d5180c4060080500d020f5441010300b0561110101c600f406010800d039164200f6401c0a040e01400f00c0d00e685009081c00e200341025440c0e10550031021207000304040f021250058040c80c40c107502d08004480c194400e1504406259035020704c107000d80030420040c400380007216546e00d50303410200c61000d01401c92075030038440090020700304001600d02040b0000904429107510390030384201d4401548040313083d0082c0f0201403010800105101854115208450140d05100c000c0f040d081164403c0e110390311 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 786940503 1250 786939253 786939269
    0xc020106050603040602090a180603060516020a08030709091503140601060e01200a06052401020c090939060a0e090c040803120103060b0105040e0106050a1b0602180604 74
    0x840010701080c5950000c00441000238800c00307440791508954050102c0a10702099040e91312031040c0100400d034440d95400c4040c041c490034a000d416640251790782040200181003c8000c004149440d0181c0220b00150841780400d102044041032076030f00009041c40141d032401540183d802c0d801c000440c215050303a00c00e81d0703001d500132100d500640718500740c45c0720003806d6560f2110f02400b8000c18000f00c00407038810000442c441c01c0007122410080c18216940300e51b20000500120140c2e00007680000340d1000341c6404000c6d6a4445c5601c1c1443e5a0380c8580c2d00700d44846954020a4010f06007405002c00c02c04180071341c0c201c2140a0140c18004c03d2403c4001c00c2003850b081030b503498804001a0302c032b10b095901d01d190030f40340c0303c080f030035034000380c401860103c2000010320400a003401084400340d828a025400c007440c011040c410030a061144805205000443c404031b6840307041c04101c00c0e1880800507492000e50f01d09031000b0b40c0f09118a80c1410b030324003044095494640c04440860b0805 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 786941753 1250 786940503 786940507
    0x14071719150e030901090f05061606060e07050417030301050904020f0a030611041701270611040f0e0603060937050106050a121a190f0209040c0201060506 68
    0x568111444003030a042510725034441071400000e04210300810780d00c40c0942d0003554035410321a00250008140390041110204000b2041c80140c1700d5030300796151a4903600c0c420b41b11311168207202c00140600d801030300c41c01c02c46404000e903c0750480000d00890310201e071107144c14003181c1080e076102e000a02a542c0c0c03100000021901521702180b0741000000020030304c400440d42c0365144000c85d00304c03218850084801040800c00e0440035100d041058100d00021300c049164800c0103003541100399141e100001b04101c247c000d1010550101c12103060b440c84183c0c1e525150710703010304030314424418142c0d041d0704480041c200741008a500e50040c01c1040080c80ca08264540505030030b543c5150400000c03c2c0c0841c16960182c003980444100c83c01070000241d01030800090203a02140307a080982c01c2c8007200038980002d0600401d02000d41554a44c4480641380c1ea1094243c121140502450890078139146400002c607a500410540c841118200407202e1403040a1b0309961a600c981a030100301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 786943003 1250 786941753 786941773
    0x30a0206060904021906120b0904020a0504090804031e0b0a150303030522110922020f0a12060b0f120319030204031203020a200a030f020118140717 65
    0x484581c64015100600205500c45c02c1c2c001602e00e026280e100c0d6000850380c5400c510034403020711a800c09200d055450101910707040d00400c040d200603228450003166202c1d11941400101c1c4142d8010f954061f20580041d41c181446c01258070030380310300360390040c88040894404003042c400d070740b641c1d10840403c542282c556182900181002080c0b16481c1010f4030f8007824140c603080c400b100041c800c10301c10f0f032010419002d016407090b00411150f245603070340c51000d013807005111143d004558101e44081e1010050408905107501a6008407c00143c13808a0000c1011076000b4101140068424101e445801070411040c01c1d0507013198811a0001c0009172000104020406610661400c01515007a9290344001308107030300c8194100043d41c00b155084d1f05990252545440c0c4c62940a04410305000d8200d00c0d49032500b000d0010b0601025641400c180750003074105401081100703030040c090750301605001019104801d000f01450207000004103403036a000310796001d80c8140c9402040c001c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 786944253 1250 786943003 786943009
    0x70f050901080a0f02192705060d06020a140706290d03110c0303030103080304140703151e050907050103140730110c10060b090d1502070c030b09030a020606 69
    0x61320f6001681c02a00c1d0781c241c08601c4890552640c01000ea8803a400d841c0d015070f803029044039059840390f00710b040c00c000074480b059075440c0c88000c1e100d4100c50300503516034220406441040179074460712987c1c44082814006c3c000c0c160f00c0350901c10306018200d0b295202074018010945010501c80790302c190b140c3d00400110348580340801040840d00110782022060000086c0307150001d034011074070040700004003c20060108208590034450310000c14003c1d01715980ca8141c3c5036480c400002c107075910200c40108c9420081d85640e407404d0020100712504111000c01c0c4c075184140a2180800d04043d00c1e00c0c0c810440074800352050059559038001c2c03a00503155900c2c02020004210b00c6415641ea500012815911451203401c0f641d0342410340d141c1a0914071030425401600501c10356241c0f120410034080890111401d4420441e40e180d41c44049107464131203031001100f0603082d648081249003c11003c204040c040d240103240001d042c1e669900c00350fa072441440c6000005801c42000f01d24035007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 786945503 1250 786944253 786944273
    0x1c1a160906080720010207050d11060103031209060b040504030f030605030a113607031407170702211e070c150302070501181e030e09060303070b0702070f050901080a 73
    0x10403001d200c0c0c4c0d860b01c10f0141542641c01005056650780c000002403030701c1d29000b000300e21600b0490000742105602d10740b070140c07904030780100800c003441d15100c0c140e080200a03840f0b070828850050041010b42050708004100e80c000200e43c4020a141c903402151b40c0c0380001d0102c110702e61040042004207200030a001200320ba208100b0003140d00074101c5402110301c10603480341801c5891044050b0b00d0010001070941e108000442c4040c130070f074414442c6a0380d004014a00c104002250032030aa1500c50089281130400170b0b840400707601c2d03404012000d508040080841c480c0c402500340540b40741d078609242a2041000080410711142d1040100f05050309aa291403801405d0060502c001a2981402e48940050b500c2070036000e10b80070810440c0f0a900250b880b83c02100003000313500d00e42d40280a46400107a0148503941134000150315079000c008864907554401e800000038144440e0107959022280200800d0086202c00401d50b4100500d40c40c8c121050200140341c2280b450b02c602c0404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 786946753 1250 786945503 786945527
    0xa0915030615031a10060504030b270d170606030c0a030b150c030c01111c1503050a0503040f1211040f09080f09030c0604030b061c1a1609060807 64
    0x20489240000082010b41c1441201040da07640c1143d40c51400202c154207205c001d80110060150601060012a030342460303042d800903041c03818000001016004a4481d47d104500c0007640c403c5140caaa46c5540c04420103000b001e40341c8a4406c1900c0c0c550070440d043c003040b00c1d119000c035428420701306054482d801158140074050200e8521803100c01c0708a080354007400c1e6607161a03000250740710749801c1c2481007458404401001908040d01842c0038003250740b65001006400c0e40710202a040351003990100c03c025980401190011803145c90130580701e42140c07240040000007a440007640101200408010b642c0c00600170304882c04880070000203011030000410b505644003907100000d00303440c00400201614034400c584030303c00d69040602d40000d900006006d41801c0c0005c00000756a00300311904000704961840d0b00100d0307082121000090001d001e03002084800310050f2010034103040034050170340b0a101c14003c3c206041c060b0b541120034810340c000034405400007502240310350103058403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 786948003 1250 786946753 786946781
    0xc0c060f094827010504020706061509062003040e270609120f0f1c020304030903020f010c1101180801050906010609080601030b0412110f0c0a09150306 67
    0x10100040c60014034031242454607031a0b144060240c0d8445103002c03110110728290105000003a44a0120390700d80340c0c20180705d26030045401091030810009150480e201400c2161148002e9211905009010b00440c0c4030390320100754404065400401032004002c3e1943c001c9006600d041c1ca4a4840c06540c00d00404029100071000c907070b008a05c6403405070764880010318005085a0a01008150500350a4400003030149001c01c1000700a1884a00741c072401403080c11503d1701c07610f0b14804c03c160380c180c80c0741d0588a50310000400c410903401c2180c0b001502e000746c4800032441008001034070b001c07210542c09400c81070206408040c42d031040401480d128000c0da800e54117240d03995005070035039006030340085558020074018072943d503220f03040f000100000c80040c2019490b54560350515a005440648404840ea8443c65042d02412040e00902d08a80807980d0480348052860f4882c0c6821001e9449804140000101c07800c190159040c0c040c0c0c80b4406003403507491680c1c1c150003402200d40e5101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 786949253 1250 786948003 786948073
    0x12050c061b061f15021504170c01020d1419151203030203010918260f0f070201030b090912090a0b040b07030e011403070e0301060503060c0c060f09 65
    0x25100510440e03001d40501c101901150b02500c41c6140320403000d810504c5804000440343c0c01c0300340d001074010070b403060b400301e14411621507003001528001c0d448510440136000188400640d2015801400b001019620812001154003d40845c13010103440d0f104e400c400c0c180585a141d400c0ba400718a07900e03602034940c485c0b03982d40c1e5401c0d8180c1c00f820302c065012035030210040100b80000d00803c14244120410600302e442c3c1550303043e004800603948860074031407801018040c1d041c45012222003800b4601820744a451038030056a0365880740c10100c0c0024101400c40c6200c1c100990301c1c50040301e055001d000740300303208410f0383e5403a0002404164000a1130b9000030b1807101b10f400400240c0001c007076a5a450b042410042c01040410703207000d0420030402644081004100241c03074204c0498070300000d8800411000a0240400760000d03540b6028607014080401c2001c00108210400a41035400a9580070742d407010550048912241603000284c00c05c071024818004400300d0a500ea000e08 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 786950503 1250 786949253 786949297
    0x62d02090d02091509101a0c010f090b01062003090d0305090927060f1b1b0115050d0804090506010c0c0e190b1f110105040606030b0112050c06 63
    0x41c41c5010507584000b211301244682c034210b080000c0340d02d134011409200c4201040c501200243e03401c0001301301c15088030b000704425a490800390400b0407401d00307101062143c1c140e80e051115150400384582c4011a0544404d0201c4100d007840b10607005003840050750400d1400010300148140290045042003010801406956200b201180c01480340008071480c03003c0d00082e070400b4070f81200c41850154440300401c00e040410800f0f941d801618840d1221041e02c000c5503070b01135801169113010340300c0a11003141818480561001e05100c03481c0b40d504207425075940c00d00a40e01d8951002070b21100e001c00c020701c02080242c00041d00301c0c806140c4030010000039226114800f00030342011403500c0c0715500b0f02c07104e42c1a000800b000c6280f0700f03c08200054601c400a00840d03041000e00b040c042e0b0017051304043e81e0144101d1003410141200a00c09450680b4200c0d0050040740022200e031064070b000440d940c80101d1580c208558840018021261000c1c00c21440f07030880603400d410000e44020203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 786951753 1250 786950503 786950509
    0x5270313090203070207060c080d0b1206040312060b1224030607020a020102010f061d2502060603070e13060905010f111c0b010207060c0c05030316062d02090d02 71
    0xc0c80c020503900d240180c8904025000a090507002c0d40300c40c0c1042000c416001c0400c1451040b41c0300442c0d008000940d10b080180800d82080440700d0410480c0550000c100906400040e18581c0100080301040170640310802d8120070302840b0b003145090910b44c0b0003d61100c030310b942c00c0c1c0c0c000410009440403000c1d00c40c0000346805002c541300b40050700490032500465030240600700c48610a040107215007400d000d60b40042c02901c1c403600c8051400c00c0003182040364003a03120b0907011360a011a000c0c140c0c00441c06580c4000c2901e4640c000e1081c4200001c0c5c841034148881d0003007945104a04944081351504000f41c800c0d00801d840555865400e420403c5e198401d1405070110000e4a58940b03400c001e075807109035408080700440c9410074000d144c01e40c0c3d0219040d400d40c0c0e402e0400e00785420440c1030209601c9083e820050301840005104981e40210144d01c500340381c407421090042448075a40b0b9090b640e410300b21402040150084180d02ca2210b4020f08007041024128000c0143c4503000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 786953003 1250 786951753 786951787
    0x1d0303090d050a11010504120305031305030316180305030316020708060a0b040f060302010806040906060f0e06400f050c0d0c050c0c010302090a0f091a010201052703 73
    0x84665520460804080113040410001800400d0a0440c10280b6000d0503000c4007141c824000c003008400800145a20071511902542580190032a526032626103640c40c2c03c4660158105c0c045520307600703014061440d480740d500030b882d4804003071400c41d100c120300f0388070315011501c40d5019401441000309038840c040010920900310005d0108140d16454280710480380a21207040141c0d003020002c0c40541d070040b00054000702c0641740003c00180b01e0038078100600303980d00a00d029010302d4000140350240449214050300040f500007048041d48800800d00d465030342c1200c850408404007032242c20a080d2a2406140c0c107240020031010500e00811040b0380044903110b00e00c0e0070104446107034040501c51034072803d8507402c000307150001000c2c14540d103084070b0118034109900041c400b14107031182490300c0003d060141210034103d07107900105018080c1111403280c84540081c2842e40c562050041902078155048001048200c0c407103001c02401ca40c900071419840200705c00000e540d03c90310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 786954253 1250 786953003 786953029
    0x1020c030d200f0a090803070b0402150706090b010302040510030321090812090124050405061207031a1e0a051023090901020a080f1b280f1d030309 65
    0x3e6803a50b103541c0d40102400b01401c41d0840c0240ba4010301c244000104103052840c0c105804903035060140b00d000342c069840744901180202101d040850b200104224040e1060580e80f08072000c0c401556032400080710f122035448040d00080000241024101080c0700000d020b5484400c0810500d18948480c0d101d80d01140440c420024290100f01500b00d0a102d03070401c08075007a40c0c0d82040d0710042400c09102c3c9546c0a070610440d62800401c1d00381e0764840c074a10f0020030080544406a42c0d80c1051110b07071a582c0e181020300070b1708000080761200740c41801003a41710220180c01e882d450b030b10100300c01041c00510881104043c8003010800c00340c01d160858080c8912050318150100e0402400301c1c000010300020903981c0140050003180340c00c5441d403648600200344c100c0041d626504194240800c060240300141000146c0c2e2024403002c0c0c42150400420543e21000711440c1d0404584405900c056480024070090341c041d50804400010b28940b08001d048a0410314000006040400225 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 786955503 1250 786954253 786954277
    0x12040b06131811060c0c0f0a0314031c0b0a0e0402240a1701050f100c0206040f091a090703021b06010f060f0c020a0e09100617010b0301020c030d20 65
    0x40d080100003418200040f1500140da0141c107108600c41020b541c0d4102c00025031140282045040864980c0d030508802160401c0c00064607625000c1096126800b40c01500c0d0051101d0b6a601c415041c14012503140b41006082c405005117401842420344402030800c0368040d00c07800c1000354030407500309003c40c80c014801440d999407281e024090403500030900c9402c0541c0c0e200004129540c0d506840f1180580b003a603118030750034891401264600302d0841c0095010710003140200fa0a11068a041c054a5520a080010700e11a662004d458101c4500c0150f02c090401c1c00964600d00c00d401601c55080c081e05a40711259040c8403450030042d09810201306000e080c50200800c0340d0194540e20f00035440e0400004078105ca40126409031614058894841e40c84408a14003403801c0096450b055128401001010f844a030344800054a00c0d80d44140c135800d150150000e840e041c4200d42c400710310000218a00040000c001c00900041d1301990420030801100c400c0c20b400c210001c0030141165 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 786956753 1250 786955503 786955541
    0xa2705061905191d032407090b0a0c200907050d02131404180b010e070905060c0f0f010c0909181e050d0f2001020903010e070906060512040b0613 64
    0x50208900f418004c2541180700364018400c0d2102080590762100e4504007101480e07070706a803169015102060245e105444650300045c0c1ca01c16140e0080b8084034007441400101da0300d0400002ea0a00d44c1a5545096403001c1c040d000b007569107001d6002451036080303200f0054245155598060842000383d803001c003094540c02d540404502d018460400380300b0322020b0710201c00e14142c9a074080300005004502c07842001d000030668942c01250504000c200c010a80e03683c070718104109036241d0000080421203441030860241045c507040c003039201c88031115501d40b03000302d1415030004054403d590319030545502283c001404502100087d0740030311030000d170500002c40d03c0d10b40949001840880e84c0100030408908801041c0e1012541c48a2000300c0648003018980020090092064060ba141d241d1718104a140d2000f0000c205401201c840400c1000310a43e00c01e01500c091007014413600900d1800000203001030784042c02d068000001401003400e0809400d10501102c07003d0b504e2101072001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 786958003 1250 786956753 786956777
    0x40c14071a100b070303020705070e0c070c290d02131d0906060108060108070306050a062001090f0b0408130f140415060c11060a270506190519 63
    0x10440e625080000c12038034074040c2d86004011603460081a038000e00f0550002500d07010321030204240005041d40c00d40005150604500c441d50b00e6100003000c40d60742110b0840000e4504440c1c0300c1c0c840010900706510345500c1c102c14000c007907900c195074030030203944d090100c0300d590400344000300c0c0a800392140c0020022240c2d800c10703134550070082414250343d000c0c004010301ca9030700002c00c0f60007a07401e00f440d60050300c507481d05401904032a00602d400040180c0c00003030705030b0300c01d07003403100041c5030b104407102c0078910195907080e01d101900140240020f080c4840000300821500765105001d08505400d000d50f2000c4013100e00c14941c02a00d416046d104240880d4500b4191a103903010200c40420070050b0496201101d484244140801d01c4011369a22050080c54030880646502c0100503a43d60715030f107030000d8880503036040100c062162011040c84003100d440c11000540c0c030018a5581040034104402c1481c4003032b0f82e1000200320040c01007a0886420307907019000d09805403a0341d004052 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 786959253 1250 786958003 786958043
    0xf0c060e060108160b0d0e030c0f061f03111011030c16080105250302090411040611070308180d21023007060b03161409040809040c1407 60
    0x90340a2040110300da1030420012449800c04446118046d908041150074201030002e045015400642c0d0180c05003200080c40d00b00701041c5148950b9002c401c45070040e520712250480350b031071404014040704821440c2009071400680d5480e50b0041450300c1c0c41e80c290071a4000b03081d50040010208650711418484c256410352039400b0703000d0001e01d8020071403450090014800520030b00450501c7d80d450503150b0020038400e40442e20800c82c007030000c0c08066084c1151450940c418800c82c8001041100c1d400ea203032202007401d40490785c003c1500b03400c0c0031210681030fa041c029440c0160307105c074540d526203001802081a40c04d05084501c940300301c1c03000419019040c442d406030800540b229038150b074070b4218490000c901c1414080b010803a10703000585041c8000740501e48900354075114400914448042c049034007010394403440740012042001d44140000704009440007001400c050120500342c0c06d241d80a045a080c0d20301e0203100920442e004101d55070b009100543e020703403030255845a400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 786960503 1250 786959253 786959263
    0x12080106030f0618050a0222261c031b0809100c020303040305160c030605100e09070315020405060c1c08060603070e0d02210c03070f15030e01060b040501030f0506100f0c060e060108 80
    0x5400c030319880000001441030207440d09801c00c1c12160801400f00c40345085031007070344048040a2032002c0c0004233075684074081c01000c0b0445001c40c252065085c000502200ca02030001c682c50305400450951316259030581702c0f504a1040e950103c5618010100418190040301c001103000d15000941414101c030240003980c6070b50403500490107240e00388680c1d141d0024035070080b82d4011100c2002004081680400b034450350b40880e0b44000d0108021a25020100740d852080d0b031002c0303e5003900b078442c01040e2000da40c100e4006030300075020b100046200380508039071400600001c0111904031303400d90000d203104002c54640c51001e401544000b12120702040007007000d000480042c000b00345801080041402d941c09865400340112040000705d90280e040f51500d45081e8000340549525180d100056402500c00c1500113410094001c501c10214403401d4028400541250a50082e414003542c04458140407081000080314105005c030750304e0321410369107012020240c085549080032840c0f4003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 786961753 1250 786960503 786960539
    0x9060712020d030b090c0c0c03010f0c170402010e090403210605011403060a060e061306030c0305060405060d020111162402070602030412030c12080106030f0618050a0222 75
    0x49440c1240042d2241d6400703400306d910003254501d5a030b8031200922924208107a8045942d019803c0c041400b00351302d15a042800c8820481d46c6038903121410380300b107114811056802034013260741807900113000c0c10040004c980c80740c060700748642240b494404001d110003210380f000115540da01028003003981d200d240014840d80d81690103040d4180500020300c090384500c148014000c0c1007141d2085178a44100360b4030b0060b11103115244c801d50700c680144c050110bc40100c8002868040007c0b450314040c80303400d0040b07201401c5940000d020b41d00550f200c2d084905504080d200f403c601014503800d00120001500341c2c1c10748540400c0b00d06603c2110700c00040c10312000d6401c84001401055400007e940494a83c125420a41416400c041c2c505448a00c03000c1c0144040800c4443ca451704054614101c0ea2140d03820442c00c52804020801c8030114041d202d501c41005840000e00061608038135006850f00302c005141c00d0180d5480981102048802004201e412500308801034405440c4104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 786963003 1250 786961753 786961757
    0x60812074206080a0c0f060e030309100e0d1209050a06020d030e030d02070c05100c0506130f06020a02030307020c031204050d0614041406090312010b0a03060801020301080c0312131a09060712020d 86
    0x40a02c908c0c0003d469002e4100c10303a0080a009400d124528400c231341031401200058001200c0039030600305407142680f445410804190a0307400012a030401c004608101c503c294003078889400c4c9501c0480203085a410060620b200600003c4121001d0384020000a03100b8004820080d15080a1221202003213501c203017400303e00940c41000c0742021032410341c0020384601c4d0380fa50120f1841d0503599027402b500090203051000c10380e11001a000401107002e403130940c0850b803109207041d04041c0e445812000c1601120000c0c4420002c1d800c180003640c0342d4a1043d0400320b07489a01582d824003191003120300b95102d1102d03445280000000788161600328010b0030186d0701e4000c907003040d40e01d8402c0600c02c0e144054000a60446007501c40e074008805850004005d5580c1c1d6034030003180d96100d041c124418401c3c029014000130003030f0000c0031903103101ca40a03200c1e00600c2c9401c0d10b04175000c0e0a407200c003207504810070a007002940d4880003868614070920b06c800e01074560110003490b00320042d2031581 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 786964253 1250 786963003 786963017
    0xb030a0f1704091d16030c180e030a0804030f031401120609050a380f0c0403060f02030a061401140d060812074206080a0c0f06 56
    0x20104141180300340050303400c90a1141e0008424190414510407030b801015074501e044005502d81c1e0001c0b8003000051000b40440709116041c0105500114542c80010003013451191b041050309034220f046407240c00d1810340000c04d0840c1000190956100c10503220024500104000405421104490610642e403808200b07007544004480c1c2541818060140e04c1401d000320b0504000307603900042c801c0e581c0001a07809205461504a906100c80d41c0d500e445c0f0780c0d04110250489503054203075000d0b10082c400c07d400e95182c0720740081c074440010300001c004104c100b0010020403424000c1140c15880420300503036030b2604c03035102811205190000052100c03016084055682e00c550b03d016102c49001000e603407030403070f18800d10040c00c2a52220314203000d142080e040d01d25502d40a040c6290107841d0b03503140c0041d42241c00c610801424016030b12090342c540c20025182c80b03194481d415012202000510b652105401860100c100d034003102c2c1411701607000e06c0425000980b1034010b10007410040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 786965503 1250 786964253 786964273
    0x109050d09061d041d07080c010c05060411030703080307111b131113090b0405090312010b070302011d0a030e030303060a120510180b010602070308030f070e10050a030b03 75
    0x30903a51070308680f84865407129200c0c81c0996140d900124000c4003402e01031441d44281c00003180c40303000e00d1003800403a025090406200d0750088240800d050b901c48058006942ca5a440d58a0a48070614190b010300c103070440480000c032100029800717104280c50f550344019440c82182e20f00b034000700c20341310500c000d4403030403101d511000c500e1031402410302c0021491a4609441c070a04d4018840403010b030010038000090030010f00d6101c0b112456060b01c0c203004a903500060741d503880c1710f00c9000c0d06070121120010414034404038080c2661910920001c21600c0c0149440c0040716103d034003481c01230301315514030020560003c07680403181900380d001d1821803030098002207207000389110302c0340c1d80b00e0144407003410420140400e0360398030342000e000c001d00004001588000902c07424111a005a50000428240d00010f203d05c201c83d0301007501c4d4990740d20101c100c1320307107036000e0418028090a007101d9440c1d66a0380c005c0e2701e146542565203544a5442010007425038100b5a0000e000e030304200520 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 786966753 1250 786965503 786965507
    0x70309180f020a0f02010609020906040b070f0807030f0e150d09031115040b011202031b0d021008270a03030c12090c0e01090e1005090115080109050d0906 68
    0x222044540d03038a905680300d001411000c0141c0781801807603103028400200101d10541294202d03803042841d0303008001040d11009000124810200100d9010005100401c403142a04000b010414030405801c114000e980d51468066040680103c004c5059903c03180d00e4240c6c8000380b6803c0080444983c0030200c50782205101d6445200d01100c00c080c0c950800740249030040d4805076440c0491412a00310004901c40c50251100c290741c02c45540c1d58400000480d51188504410390300e40003005000121244040402c0c900b4102c2d600c10b4009401c6500b207001b41c0d4071401c05054401d42516034002c3e91030a1900c03085c8002040c0c3c00a00c903ea80803211030a25440002c0c800040e60f81802c0c002116800044191171002c2000c45142e81241458201d50400824800501c01c032403160000048690300e40c0c044c2c07400c0d110202c0243c80c003a0f008a004204000440e0445134000144400001d640300c07009000d49a284080e42180c0d00c41c0c4e440300f080034104041081080340101072450402403090902c040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 786968003 1250 786966753 786966767
    0xb091902040b12071523180a0b03040c092711060c34062c031515010e01020d0c0303020d05090f010606020106051815101e050703 57
    0x4041e00481d542e0040080035140e5031401d20840340c00c8001c8810303060751108028640f03288401711100150707080e00c040342c04014000510140c450880f40e0b007410b00080911031007111520301c00c160b0b448a01c1603c00502680071800560245002d103071001009420030261105494480140f03156061441502c8204403400c00c040c404080d070301a51141c404a440c1e00000e00a020f042c2420100b80243c03150004203800e8601c810381148030707200300300c3d0030414280710590501409102c0d100120303480c80c14202d162b001c0d0707148800c40c0c10b0910000c440c0340c1d894800400d142003c0c40c0c2101505081340700130310000740104801900250b0003440c10741401c022160000791900c8008441d007081c04808080c41007018001e4040d580700c0000f40f00100418a0134007620790780c0f1401106480f00d04e520b862004203850788180644425214094a40c41306480c0003268000303041d10081510581100440c2c5005a0796100b142c0d585000030295160307141c070034040780e144102080d10440d01c01071107410011240000d0708051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 786969253 1250 786968003 786968053
    0x150203060a290f0d06060207060206010501080c0412060e030a02070906091a0d030525031d0a0605070c0b13050a0f030506060d110a03080c0c0613030209060307120501090b09 76
    0xa00b070b0745510307070400d030400c0901a68500c50129401d0007008034445500082c03402c100c450a50032104c0c40d176a07074401510b6554003502d101c10105000c0000b172100380c501c03440c101c942611035071001a2040028900c40d045811901e51131006030030000082003604828007030070010303180c0d000e41040f080d42000706054100f0399114100d4002e822442c505001d041c0203005440a40c120119620440b0b44030803004950414034040403000f003a8481c540520000710100012a50b880240400e0b5007182807601c01d0300d040d04201d80444108088036804031310142d9090103065652404070913581041d0500c030400c400c03c5081d4100c0700f181318491500704041000024440e4005005840200e03403171515003004003441444c1450150449044140041040b128400508401c89040d05454110901c038041006078805c9001c103480703071156003606201620f40181a81e070401c1008084920032603450b82400c0300c4951050781a0780b265580d20080c002d115151080c594820072071340c098900051601d00c0c806070a45404c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 786970503 1250 786969253 786969329
    0xf060f291c020d0c0b03041a04030c08130801060b030a0c021203130c260f0106051518030709020910030b091503010b040e0102180a0b071509150203060a 67
    0x200107241035443e01011045040e0f00b20200080080e20b4503a2030045500c161002ca41d00424042d944641c07807108400540200d0f03156845006a50064403103200c3d98022620f40c44003950091400980d1207004d1181c8070090007150b113542e8503072408505150844000ca203544055400c520016890780c00007108503030344240c0e803000792441c600e06400e01c9000c400c2d50741c124030701400c181000c0c0d1469005030030450300a071b5520012160142c41586910303007600c3e15840f501303411400b0101c2e09c034801c800d404003808010300303420041c140c034106100000385031a43e15801281c050798005010121410518501141c0c001c541c20300340942c144280c04604100710042019805680344000c54000d80d500703402400e45060010000d02081503d00c19040c001e500600382d000940461075180030450510501d040c088070f0308500050f0504030b0949410703110300307007004071f810f401a680c1c101754000691042441005407180000161646044020310035603500c40e8000f60341c803481c01c0103903201002004046121080c2d0300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 786971753 1250 786970503 786970549
    0x3010323030f0a2f030d0203040203030706060608010305120a080601030b040b0613080c041407050a032a02060f0103050705040213120503091f02070608040f060f29 72
    0x10340c00d0390440c040c1500710303540c01c50b0000c2c402c0d151550007401c8416212801e50f030301c1081d40001d42d000741440c020064425040e0000d128141d442c000c80e5000e0b641c054000f4003900d02e00100c6a03074481c11641d143e04400042512030f4014010310404210840e41e158107460380a06d003520440000e442104003c0c0020304250b2241c405403010b0f00e0381e80045524140c003409090f20352140001d942d0107070040340181c000303e100e0460042d6491805004005015042c81c262562545034031004a849501411300c0b5418141c03a12003080480340c0c055555510380c1030442d800d00d07040c04d815000030304010000e80046801012032005201141d004610f5208031041110300694500d09104101042061079124400c880e1344007140505104000c001482070140840e41d02003e200d44015803801200c02680180060388480d10a02610380509505500f00380118222203201c80e640c1d8a130f005880310380c1100d00e6000d0712180c1d1581030340400003104034500589221103d48071040c134007040b000e000c005c8280411840b8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 786973003 1250 786971753 786971813
    0x60f180e04140f060a060617060d0305030c2812050615030907180c020d020d081303141c1803170a0b0307120b060f0f1005160f0512030103 61
    0xb003044428040c071070b140242c0360a07203016070030100100401d118840100c3d01000c8907036034211210054910a8900400011212586441c1203525810080141d42d2650080210002001c0c01441c011582010140c100b8001d241c00240207040c0510074110458040c1410184a49680d4500902c541c21000081c1180c43e035541e4042c00303150924035070255000b514081c09464400701c0541090034000181d03000c844060400700d00482e40d5100d540315101c002070940000c01e9042680c46010741c820381c040c0c07400300c0c00c50484012500d441e60000c001411001e591a0b06035000140078024800e002c81d03402d118228400f19a2006400f40c0c1045030720f41c0405103c84005440300c0c600b98459444180c014003121400e54032245421111500030802751140b03103d5500040c42441c0800e5412100c86015118500c18081441481100352448420009000b07041c09200b44c0c48015000f4501918002c400c008080764483c00c09a0801c540c1d090310329140c2c107082006001181d00d1050401c41941c0c859210001da4007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 786974253 1250 786973003 786973043
    0x90201020c15040504060b1308030a050307050a0c0606090e06010b0901020a0f020a08030f0301030501390201060e4209070203071b170c010e01200601060f180e04 71
    0x4903a41091764464175281c000300382d841d0717118040e10300d51402e10305e001508c64841c0c0005a407401000d4603000020300030030002e07001c20300c40c0026000c104458103104005d044959509419603106421441c55a507460001d50144e081c02c01c100c40c010603000040a18122411700001e4039000845805088006164407210031511003065140083c110501560348074400d004407690b10382e0080c030080c0d40b15807c265021440741e1002104c000c0280311a816250b23000e100294403004841207e40080c15550f8456000404043c10480c4a2050a1120400c940d41c100e61000c1e15140100011601d0050358100d24070f50310000807640301d00800c0c0c040700c0c1550b00da511858201c0c6103224600000380104d43e10824916072288200b00f00040d01d0071070080c040850712841d086950b1b8581245171600080c44400b108070254000e0386010500d404c852913408050040440480c5840300c02e0380150006a1420060700510340c0c0304089024440b1301c4842c144049207003401c1300c0c070038401c090310103040a1049520000902 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 786975503 1250 786974253 786974257
    0x70b0a09150c1a04052a090901051e13060c11010e07050102070e19020c100e1b01020307050a0b0a0213030c050108062409040906140106180e0f090a0b09070513090201020c15 76
    0x206c0003008000350745040b0b00d201d40a41025142420320413070b0031468a03c0c40714001c1e2040e00c16100d10b03031246204909a04c54602605020f000c02d014090100200300c4111000c5c05004103041d0410002c181083c500b800080c9405040d5000581c24070340141400540d59003541a2002510302440c0980c03a20300c0040c0450511800b00380000c4501e15002000d0156880840e1031200103101c03400303081207102168010382c0c6911400c5001001608003018500000b5486103007a50050354001c0014140501402411800c0c10b40381c00540e03080700c1400f4104501d43e031010030780381e00241c10b96240070a20800102c00c161100c880f91103120728034012540b40410f80f2550700800480307801c4031060003891684a1100126802130055400281100345005000c0d000000300f801240c2d40300340b00c500580d40e262048502103070b001d4202a8203018948060000c60354109031507015148040c082d00392540740c04200031106000304115000141003215100c0582c2c1c01180801a828040e110305141c042c100c210303a00d980c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 786976753 1250 786975503 786975583
    0x1120c05060409200301050f1e1c0b010501021f0c0203120a02190311070f1109010f08010f1a09060d051009060f0b03070b0a09150c1a0405 61
    0x411000b040003c1c00e0303850390f00524006040060900c081c20501050000070b1301c0240991a00010002c003c003290341800c100040c2e200d00601b0740f0828010110300000e0581805c00c2c1034040340c0c0302e002104130603c0704001d0101e0050000b40010000f600b20801d40d100440d459070105200f2036903a030801d900b420300034021039425802c01580001a4600b10740102c0017504040c103400440c1d510314100143c8075001c3d114034654000260840c9080001c00c0d03039010010301e1035110441d4000d4510452070324648510054038060300e40c0c800000c14441c01c4c94406401c50f80000d081c466814208032908a120003c1000210b014a0070b480307100a940c0e540c0e006c241d08000d80c400c01400c5203e42024805250b44a42c40750505520800052045600602c1c8420a4600c0d0580503039241d04055400c0220405031002010303083c54030708015510380e98520302400c3c5508100170310701c003248200d03600700104169501000c080314006102e061050a041d00ea51765030300030034152900c110781d01e507400700e1035001c3d42c2810b282c603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 786978003 1250 786976753 786976759
    0x12150b0720030d0c0813030f05060f011a09010e120d020d0203040302091501020a020307170c060918040327030312201c0e030d1118010c02040b040e16150801120c05 72
    0x706c55403458141c600b00850300003940c5500605000c2205512410b21041c100e4601544003800b02d0000812000168005013040307042c480c0304049608543c503840302c0d13808400c5030080508040c18003607001900300454600c00808540003004280f0040e83c80e41c219580214910010f1001d07511900d0050f8a0a92019406545442202c200007052040358490441449003c010b84101f4000b49040c45024011600b40c0c0d07501107184110405071104406080e50b00030300910b000246980007010104040050460284240c00e03010414010300da00701c040040c03460030b83c1c0f10070021080030500442c011269034460500f05c180000d00303441c000c0d40c400f81102c14032000c01000c01551407034000d00e66690740440c030a171401c0b500b408000400c0c00442c0047d9803840e880c0110b07511007494201e0046480c220350143c100c0c0c1c40340c0e40d29646030084c0c8451003040481030f440001884410012101a180d052103688030520400342249200b050590146a85046030505510502130304218540420204c0c0d81da001950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 786979253 1250 786978003 786978037
    0x25021906060b030f04060c111b0402160b04060b0607110d020604260d0c030813240b090a05061e180f07030b04090c0612150b0720030d0c08 61
    0x145025840e2040c060b9201b01c0003009100761000302640c95208580c1c101130a904039540c1e82d0180340705c003191034007400401000140313004c020b400056044a0004025200c0d40200020481040b00d01d00c50104559800c44059041811a580b00201c1e2200122064041e08456421400319103901c010340c0c019041e0603203510000100400b03407804800300d002e08451b03603100e01207042c89400c0c01414105a01c0e500361ba14507900369502c4109103034040320110112541c090001441c00071205815400203c3c801210700400d01e0040b000810081d20b0703010782860f542a20302001d1166541d00c40d61940d40703260141a8202041010340b0006862070f5404e038140c003401090408101c80b20420480712840f0300c0c07103500c04100785084c95044c00215003040d04020300400c403011040c001c050284640f901c60020484002c41c011642d0310210074031401c1c90b8031990611801203810790811680d03020320750b00030040d0520410248103284c0000c0d03590764890910341c1030011503102e04c010701c03060703000b1140c01c0c05500c04880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 786980503 1250 786979253 786979261
    0x6061b15090a110a0503121602210c011e0e0102010b0301020a090302090705041805130f03091a130311120f0a0c06170411010306090603060525021906060b03 69
    0xc2e2a800421011105452484403250725854003849120646070003600414030003030000310b0f101c510b5201d018158050100031480b640141c5e0f0741e0807118198828030881c4580340d43d4241c0c810b441c040b0448806414010b4525122000082441940702da43c086448c1c0241c04076600001130b030041800500711a019400000c424541c076810540d0023084030300c203507404221a65035481c115101d0003580280f10042d5105410b0303035469a8103410103a00311309c1d91aa8913418650340c0e034071030120b030500e5a070490200d00040c404010341050084440d00655111084074542950503940c007100030704c0360000401e485000d40c4480c13110f4480c1a1500b4010b42d03c0c40417200e442e204100d00700c2c0c2d5012440f078100d411004203100818454800c1ca514400c0710004506d54081e80c44603034070881010301210354a0b040582d03030310303000401c4241401a80c00444c020340d40040c00303051021074011081641c0e8048084144d4110f94004016400a006140c2018800c0d2010b01c29680e440c004e005801c0d40c3c0c0c04001110780c040140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 786981753 1250 786980503 786980521
    0x170403060509010b030705031212070926071e090203041406011415040608062110021b0f070306050606090a0303020d030636060510050a09050906061b15 67
    0x4081c441600320101c4036025035400402d5943c0f0a000098a0142010302c0134590a40c1054900be40223220390070004807640e01c88281d404c00303030040071895604980b0307004c0f02d0000700c2c802c0c0141405804030204985030340d0300d415007880c00001c240c4101001141c0c0080001c0c1840503400031145001c4021040d01d103296955070f125903000d8950121103108803002d400c0700b500164403004032021140c0d29200c5a40303503a00ea8081100c0642e0302c41d4076400c080a43e25000380c015030144040181100c070800c0050311010104004124040b1040c0400240e6200d20103c40703101d140060b0907800c503039001c0c2c00400c0301c0d40d559010403514007a00c0d103100d81207a030341c1c0000f004150700454840b2407014940e03002c01000e50707140c84030000d042c1c07000c011103161681345424058041040040040c0c0955038000410100da44401103880c4202c0c0c1028000013980108950344100d03440340c0888020102182d07100d8041c208540083e2003807041245804090b0f0b08040030341000303d02400b00100b52111102484e62030318011b000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 786983003 1250 786981753 786981761
    0x9120a05180a050d020405270106140a03111309050304030602030402040b03070509071116030515010806092a0406090506030c0319020f1f05071502070f17040306050901 74
    0x400003400014480380d5540e0300340004807000310f900090541e10b070610141c003072000600c0d01030074800c048000c200c1006000c0c410901700281c03d9400030300000b046480c00446100101852180138030580c0311400801c04600600422042c441e400c030f86035810340301040b84403002040d412000824900000c00c000060041d40c0c0c2c0510b104900070781d818030050580404050300d41c0a90301486034000c02d04400702c0e11403803041c00d501450420803022a0041e4150b203d01506402c03890348210350310350200c004507a030030580c03142203401460303e14010310300c0d8101000c805803140b103100d01071188081d448025084607185401102e0105030040c00c02c001c110b440320142c80160404440a42c06445a9241948941000030300368040c0e82c2d0072008006600e18aa00b0040c4014190f42010340c80280c0441c8100e0085420b050010003036400d0300d90683e0f8030f13400d2902c014054905400442050710600c1900007050310450401d21696100b01080109103240b500780c026402540c002422081c81d01e070820029503c1548 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 786984253 1250 786983003 786983017
    0x607030f14062b0302031c18030e04090503031009140106021b0402120f01081204050303031f0503060903070302010513050d080a020d060b090a1a040306020a02120d0b04051b0a050309120a05 83
    0xd254411b501f010540c1041d1000e25008000c0540c0e10034045020901c91038884440d0040144080b4032501c07541c450515540083c0c40040c0705108a041c00c0010000b14450030350a43e21a444000c1198504000a5124078132942002c00040100c413840c900c50341c4035412100d11140545503402141480d00f020010014240a020350920031030042094041400302590102d800042c0118595503c4803201070101200303815031103601c03599650103d603503034090022a01c01e2400600941e01c0d0103d41c2002070070b41e800902881070740700c2030381c413040c000c1140480d0060b051001410324013501e13254003500e60300a200311450450801d00e00b01d404682c04112200816110740c0c111410070520f62a800203119000030141c0710008104100010000500d03960081d00c90b825090054440f02081039a2060866100801265000f41c0d00d40e820400391601e44100d5070800c05992506900c0241c982e00214107105440e1034a00f4400c3c0800001c0d803035070701003128452001c68012519200c0d043c40740e0182a40c0c101c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 786985503 1250 786984253 786984277
    0x1e091101081014010e06131d0604050c030c180910031a06030703031d0303040603050105090f0403020d2715111902060a030f05090607030f14062b030203 67
    0x7001c202003914141c000d1060311500d401140100f80420010b5400456520304550084c0e402e000da14001e000700780e0799400400414101e50a8600101c140000d565401802d01c1d2007680f0300800c0c845481c0848041c0c0340c2c041440b071140c5582d030380c41f0034000d1121500e81c0d02030ba0b8400fa5082c20030040742c882c1840681244e102d40440845540b040c4c3c2c081c21030b264122035413905030344010002c101283c4540300030003c001400c5552a06006034a0200b8103603803182c0c0004000c6611203004010908110740c5c01c81d84020072486421280c2440c0e9002900c44054103070030410030000f41a0369007880d0289041c04151a041c1c2240309109560300d80d2102007441c1d40c050380b40814604500b1509061003c42d409c0c04038502000c011028800e43e40c00c21003160811307503544003099034074801154051001d00c40d09005807032440c01060f642c80d084070002c0035a841e01c00c0d054070f00d60804841d1001d01d10002a00c0b900807408580810303810307415040d40a80d01c140e07121002c0e06035031304c00c1c1c452013415004402404204000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 786986753 1250 786985503 786985517
    0xc1602100e12010b10230307030510080f0d0806030f0a1a011508010302040c03020c030c0f1b0a12030507021c0c1215110c010905070924091e091101 65
    0x41d0000c030f0032210048101c94000e55184102074000340304603042481003030101d08080300303552039524210b2290422140140841d0b520424440302d180d8204011004041e501c1c001c00040e1a8461000e45518484e1101014400c0310004607000d40d03420b004800c0a5000c603811540e2500e2581440000d10044204a0754140c40c903000218403c40c5c02da440031101089929400c0d11640b03141d003400005c04000c41c1c03010805034240048038a094040c001084400d405100509011244503c400c0c24055060b88400c074007008180481c003586c55118010045520400362803290311003d0500703540920a02c0c070001d5100130700005000070035640c0c04580322164020190340c00d00b180c407101c85030401c114844024100d0329040c51810403180950300440c80c081c0300015414106518034026600b5118184001c031031940200c0c400b4824100c0c244074007020181115281050b854000e826000140e080e800361000d426110906800c50034509039aa280d07925451070100002515428074203d408101d200da80d00060350317 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 786988003 1250 786986753 786986779
    0x309090b060705070608091903020a12030b220e0a08040e0c0708030408090d0210030e010b060f040302190e040605071b080301060c0212030705161d0c1602100e 70
    0xa035409a83d00c074000301035190034018107a415101c010a800c1c2d0301d101d130160a41000300c2806601e24920f10a40003007078a1a110b00e090000542c1a560f80c1081501c1e1907415041b0f640d8100b5045420800d00220400c01d19142d00300070003500301d504100901e88900b00d291410000090010021601080c174079084584851140c91501d108501003d40300c1d000070700114020030100300081009100090400c40c890070154041113181c08180800c0c008640d81d000c400706140703000e000b400c0541500321000c030701c0c2001044100d03146006074000a8000c403180342c00e0751000c03000c3c055030401030012030301400801c0c9840c0c50001c0240034212003901c0059503555004c010280b12030640d011181c1c0c040000c900310fa0a041c4101c0d00492095070580c0e0103100c00c0b0114603010b0b0144000c000f43c6000da0090f00c0c07500c00d040b07000708504055500c0300c8202c2d03e440160354400511101c0d240e401091a4007080c0c3d4650901101030807500700600c010307510500e000303071090106400c400715204285050300c4240e443c0c09 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 786989253 1250 786988003 786988009
    0x3060614130204060804030e061207110705040b090a1d010e161d0604020309070e0f040b0105060408071401030e031209070617160215070201150b03090c0f060c0a0309090b 75
    0x1e0b4491300c008a8160b101260009014600010460401602290800009541d6840c0481040e1502804034034828035403d0040d03c2480700310050507080d9403e02548640c4c402152080800030306801d1a00d644000d195041c0c0c02021403601c0d00c500c9a0002d01c00355003460041500e0300d0400010640c5203054500000d0f048005600360340d203c0124149201040c0d803480c0610004e580020b000310018000c8680201d83c140841c1081d40c007070485803581703120074500340c1303846010040c041c3c10041c46451300f40001c00c2601400240c8806903200c914103032506154503c0141c0290a52610421890002140f4032042c20485c4d8051840352001404590899540f280c050b6110744407541c9604c240c0f100c0307100098a801e801201c0901000492044404ea010b6446501c50b100c10300b1707180c40c0c0042c1d4491010f551070b40380c55820750003e00003801200d13146042c00c00c42070780d0314400143d94a02540203034980c010156541c1068408811038503040c0d0711204044d1034000c000c0f00a901030030002d01d2525601c250642 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 786990503 1250 786989253 786989257
    0x409020d080903010522032007030308011d04080304080a210e07170709052703070506010e070f0819060f061206050108010e042f1f0e010c0c030606141302 68
    0xc500684c0080e0a841c06881c11a000c403490500c000c0c04030f0f648900d0110408d07041100e03400650183d65081400d50400c0c5900040502c0c060704034404c80311100c24007011038211404c07039400c1988244000d035540e500c80310664480e0b41694820501c4c2a0021600442000641006911018010950354a80c0d26800f4040c1400042c8ac03942e40d06510461050041c90a180e0080343c000541d102079112401000704213040c00240f00394420340903080440d18900304070003000618090042600d80b2640e91610130350041080b05040194020070902201041c0d041080c03c4801c0090007440c00c00307003c00c9031144842c4032051020f00c6004005103005040b07645503502481014142e800c16501d48080740d1030090030910981c070142090b03607002a100a00d90381010920144801c00034120440100d107000c401c1082040d0343e13000d41440440c03035542e5000600c9640251210001c21003400c02c03540301b5409042c1b80740324015541005211510f4040c0100c4d01b0003401100c1403c2600441d41c0700c1c0064200c60006e000d034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 786991753 1250 786990503 786990541
    0x40c0201060b0d200313030f0c02060906071112030307020d0e03100b031e0105010f05040b090414010e070f0f05011103040e130501090b100b070c03110409020d0809030105 75
    0x290005010402d4100302c03580024400116492081103c099901310300f020503441600c0305000b14100303000ba00105078114040188101a40c10050089030703050b00400c01a2042428581c802c403400102c08040000c040911051005e024160060b008258070105a882c0d005643c00d038094400c100100300c030203208800c454181080903001c0c1c20401e100d402004003034561140f0b440e50602900740c1c0040c401d58401071841d280d00350340c40040b07203551525200300e4000410b50420f81c000d40c00c00300803e41c1515400d001031741090380048a4421300071000030b410b00414031000381c210f5a0042440006404409802403401e940080c05021106a910801580c000d003458170b4680454009001c10804064080010780c0d008004514035442040250340385821034402d15400c80d07000028030305010406001811040103004e202e00181e18041c281e480e444038081003880000e094002d40f00600c0b00544130b907000745a03440c1e800340808025080c58501241c0a0300045403980c002c0d0300e0040014100701d500c04101c102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 786993003 1250 786991753 786991769
    0x301020a0c020d020f0909060103060b04180b102c090c030a1103100c02030318010606050f071a09071e21051614040e01050603151306090b06040c020106 67
    0x300055a00b0310580f1042c50505a034000c1c120300441e1100d84440c284144103400000151100350b055250903001c40302c0080320300303001b14a048429072807000743c6000140c01075044401c40b07003c1e0766210706280d6010010f400416030781d468501b07040f0746018045503188071449035100300001c1e55a005211661101401c042c13a6040d480f013589003020900d0100c80103c1c644000d8145c80c00281c603d43d200c002c1c1c81c441880321005030b00c000704200101d0005010b040c1c041981c1130007888400d00e4160001c0941c0903c5410307100f078403400a284410010043c007074030804484030b201040c081c90221210b60b16401d141c45070100c0c400011400f54108583c0c6a242c3e400c0c1e80a50088100507000c0520b440705240d141d0608840500c92140e8466042c119140500001c0a080e8112046481ca00703050005403038402e911a41c00e0313030504c014030425603804503042c0115642c80300e04010f250b507959440340704501c4030f0b0000b502d12486d045810051220902c203252080301c0a58040c01605101c00d0102d08071002e80c450481 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 786994253 1250 786993003 786993017
    0x40804030206070305090607081216091421070e0106050c070603020f0d050f0910060b0a0f1206030803060901080d0806130f150512030a09030303110f0d09110301020a 73
    0x5140c00b00103400740c68028a07240c3e0030110302002003180ca5005d01000d1784d082c0c17404140340c10b00c281c00320100c81d803094080c2090a181c00740101e018264140034010400e00c0442c9183c0a61603840c7c80707400c0025080004125901c84a540e07540c2500d034402400384a40c91581140041000e5001d84102e404050110000705210351422001720029000f60000742e44004080080c03028600807070052500403510901e0b0107025080c201030091603d904500b20110706401d200303041000f5161001582d104a43e5410300010014156908580d00910312018218840ca0304a003c0203204055019611603001950341c4521740e606c4010440d51911070f00f8648002901c2074000882c82c3c20300ca100d064500c0b00b0b01c03c000c0b5900045000383c030f09480724003086200d80d84030742c5070030485071800f048022814003020003c0d602d40100a03800902c4940c0341c4c000030b418103458412000d48000036008491401140e0050719440301c4c090710b034407005801c0da19820b403000c540580240700c00d0b1070103100300c07540c142040d11221 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 786995503 1250 786994253 786994259
    0x7050a051207120509010b030f010b01020c0d0c1a0307020c0105040803030a1d0102070f110d051b03100e060714180111120a1e02010504120809070513090204050a05040804 75
    0x1400e81d0000a140d41e007004201c04443c514108140280c6001342980307400410035203112000d06142150013516200242e04100d100509640c02049028280c0b00c00d031b401a104040d6403c0440c5888000da0050400c0c41c503408070f0300032144083c00950f000706400e900351030f0500450001144c1300e0040d07006d00394058008002003903105907264010300c007241040d540c01e1481e000200c01c00742240c002e02ca098034200b00d50014a01005401002800d03031000844500c01d0320380150b00c40d59911543c010340d260844c003840c081322080d55410409600d0240100006121060010440546444082e21800080342e00700c44000340d0301017600151101c0541120341714003034130f0480c80111070341d203031040e1071802c18015004c41e0115070a50354020710451000f51202d0750704200764100b04510720200000e0700c085915020900001030b222010a00300c1c181c5901c6c080060f502c3e02c04185060140ca6400f0b242c1c040500340c541001480c8903004410341d18000c4408204a41c0d5107640001602c0044a00501f4443c04000c14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 786996753 1250 786995503 786995527
    0x3060b1207051303050712060506090f070503040311010614030c0108010602061b041503060614180609120a1b06090510030c0c1b03151803030c0309020604030b070807050a05 76
    0x1400100b02000900f00340f0a0381e0f62036080c10102942c2004410f8021000254280400c42c0203079908907800740c42184007032030300700141d000f00c0b40094110420003c0c0000401c05240c0f180000d503000007044002045182d540e901916003844d140c40d40d0074000d0203180b001004a601641702c2604850340f40d005050242c0e90700c102e003221102c4440c1081c0103807105010200e54001e042d00001062140740c0c0300064101c1c1440405400c0c5c0c50014902c4400c0441000b1100d810071400b19140b1500e402030324002e40311060900091840d000002c03607080c241c41940f0300c0b0313810700c031213030711000c10380100d800c04030340000d40b00c0c4030884030075500740150341e082820619045603452003075110f1f40d011200c3e403a01078140c1145960396544030001d24a901d104982c907941c00e0050208182d5440d2111119850422144c041d05203c2d03259180d8031000034040c0350340c0f480400c0382c1c50b0194011f50320059000b0586132740c8546070b1404071701040c07060300d5046c001002a40000d543c00e00941c100e074030341c0031280c03940c909140c42d013010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 786998003 1250 786996753 786996757
    0x3070206150d0516050118140904020f0316030b090708071401020115080a02011b0b070c0606050303040308030f06190b0309120406050c0c0303031005040e0a050604030c0303060b120705 81
    0x841d54001180c18002404034100303000207a0030211240190014518090004004010802c410164005000c000708400040140010741d440415520311800796143d000154600c00050a0b90307406025090140022420000810059900c5005555060303160040c04030703a2101c545c000c1407003551000034217028a80003024031185c410014400403a004058064012200b00740e80c0c4038000da540200c030104215070f00a0014151a059031000005164040d00d44074002c8201910358818461440c07689000d028041c1c00c144003500010f13044a0740d0f9030380c0c1d14003c032459004030758103c001d04503800810304d13500d498000e191080d0781080740b628a541c20000003251507072010b006e00325a8810806072010000d40c400c0a0300041c070940c0c890310780b1601e82c810090705000d501c20005100b9001001040b00c512603214448050320300580d000100b1202480c811450410259000f603e18415402000205030344000c0581d016442903906000590307480300c60802c1c03400340d2261410740b03070f00c0140041c550602c1000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 786999253 1250 786998003 786998041
    0x70e0603100c0809060c070308060f0118060c020a080f2a040c2015070f141209160303051602010e0a0b040f14030703170f0f030f070503070206 63
    0x2040e224545280302220003181c0000b107040c0c02080e031075410000195000e03c1155844284605020f00d040555940180780070001030042c3e10034502e40601c9180c40c0d01c14041c80d110042084404140340e91140d10190104003050801ca206414100c0c01194840f000f1428442d024004002092411800340001c0940c17031391340441c240f4240302e2041c00195681d0b01e000301454040300380ca07007000055120b80f0840180281d03800c4124203901031120403c0c043ca0f03801c180d40e0321050b10b150410308980300d000c0480e503000c2074103045150300e1408507841188444502c442c2c0e01030600031044070041d01c100040c503000d03070b0242e20010380428801c0c07008d0340e0040e8000200303c020510515000a02150010000710210300941046026110101e020310202c140c03100070f200078000e00d2046d4941c0c2000c100000b40c0c0c54502d0b00000780018070b50511501c0800b061070135158040d050911080c0c981d8a02c03480000c984d001106c07041c03488441d07080070495240c055003c0701d008000a9026003c250303a038442401094200035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 787000503 1250 786999253 786999259
    0xc01030b2209060b042306010507060e01060501020c010207030b15460b0d0f06050a29042306190504170601060c170d021206150c070e06 60
    0x8114501c1c090090032407941841068100140c292410704003141142e5166142c18042c034035108014210f00c0c45929001031019640c048000f031541e40c180100d0781401341001c01001346003822510306500c101900400203403072007079013240c1d400b84100004907645e140c02c0c480502450485804110ba440040c9035820350940301500c0f800408541c0c0683d80103c059200c45400203a01c10b403141031480c0480710290520007050401244014140000c0b404944140025581481e82d01c5040000c501e2003a000a00240001010801410b503540c3c1d108002c0b88421003d144000482c043d108507021144041d10141c0e010700c00c01c0c404081c1c4210315040e0008181000503031008040c850024015a00482c0540c81503c650f2080d031500d00e000d0420701d010111302011100e60b0002c00041c8a040c0e401a030346540c0e5900b10000902407440044bd00c107080c0300398424219410700019030318610607007401c0c1050080c54142c41c808944070140c03079099a203000b03105070401e070b07908507000402c44032011443e502e400602c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 787001753 1250 787000503 787000519
    0x120319090b1e01090b010e0d0507080a05100c030614060c1f140109020427060b040f14030a0804140f060301030b011a030c19051201090b040b030307050c01030b 70
    0x40d2907124484030300b200d0402e1141c210215840c0d03500014802c0b81d0040c440103100b448000c85c0440040d1845000c548068055581401c50000344001046488003c0c41840c0c10354411960604011ba06d070360300340c00b0424540e0f052442210300d05100303120b140c00310796801304814150030180c800c104042d80003a4200310321b407007a100300610301510301084295101101900051000c031a01d03006860504c140e0101554610501c400c110414070103500003410b104161071103402006100c241002041190000c03102901f02280101b400d441000681003651801004109080550b80415540c0c682c0358070001c5c42c00340244010010054550300c4030346c80d41c01c000d02e4585501481b002080e00d5800c03d92099620b0b41c07103800108501400c032500c50080804501103140f85140015060714540309900c410f6804214400c1d0040c0101d12580a4a4400306440d1600d806941d4604a21010b448100b801e14840c503d03100e10780314149400011110078079030003009400b00803000c40043d130007805a02040781e0000c00c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 787003003 1250 787001753 787001771
    0x2010c050f06060310091e050f010603080d050a0b0a2601020f0910090303090308090609030114150631080708070303030b040b06161113050414120319 66
    0x306126508242032103100030a102c2c90118100b5280c201c9032038041902d280b4040340d9101040b108001d000104e5101d54400318a40303e41d160052501c9140341c86000d080d483c22001100300403440e001416002e80900c1d0900c61910b070f902c045402c0b5418005c9071680158480c40411060f00c18202404d000560380b49250003403824400e0803405d83e403010303211001400300000d843d0840c1c41c024212482c003150500c2c11085450541d540688203c41c1e901010302250710120303034161159551021140c0c00103024009004a90410203003203090441918000c840102d036032030075512810840f06680c41c00585040b82803040c1251100e40040102c09408581d56a000034004070762208104405001489900d00500b5601e1a5040007400c84010700700c6540718a040000c0443c4c25a19401034504243c03640c4002e80eaa08081d00c0c04d05c1c078005480003840e0300541603c0b002c02c44850954070251281c0d002c2c0c840c1d0712101c854032000301c0e2582e40d909400c81e12240c00344081a140c0402000c400c4007030550450006030000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 787004253 1250 787003003 787003013
    0x30c020705150405030105090d090b0f07120e030f030f0a0e1207030f060e061003080a090905010f0608060306040c030f050a170a1206050a0603021e0a030e0613020a050d02010c 77
    0xe820311405035070071001a040113207080900c14158041206000b030000c1c0f824014004024210511440581d2040820103148150f00305084034096548980c00404020b00702c0c00140c01c402c28009014400c2c0a1401301c3c1d0300440012003107620b405c011840b030a141400f03034102a0380340002551301640080708001031080c150380411084002d0750242c40101c01c0c10314503181440070364403503c01c0249140c0110301440b6074405181c1c503840a8941c0400c4168443c403107080206c850344030a5004202d25420700d000080e2180039002800c094907641d1390307001c11695400f010300d952240265002088070042030410400304090724584035000b40b00e0020f8030703109883c64444000c0c45074941911040044000741c40001150014040b00e410302c0300a60901541d0f10380000030781910440c0c81150141600010300385200e0001703030300b00d50300ca201402c0081d85403558844010f004203808518500e46129003c08580450b03402d0840c245030b640d005120410840c00c00f014440400402c0ca070032418800d04910010000d6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 787005503 1250 787004253 787004269
    0x121104051201023001090207060b09010f15080c091903170d0b0d0c060f02030f04231801090f140a0b01080109090c09050408120f01090f0e0c01030c020705 68
    0x5081070026844d00040049402c0c6950031480d21415040c20380110415200e1440c407040c111050f9420042e00c0351300c039041c04005003403403c0007281e10450341000170130110402140b0f00c060301d001c20081c80e1003d80300c0d5015a500002a030b00804044011b102da4041490202c00d0b40c0e400081c072148005600e59030f9550b120b108036800103003000072f203404034402c03280305501d00c41c250040f9800c0b14200c445021a1722030144650090007a84200901c41840404c01070082040741c00114482d044556101da80d11130955000070351103c0007800091080d42c2501074a8040600b00d03903004c082c14010701c3c59107480d110000501c110400d00d0907064403118a00d443d510ba2010140c03161281c44404517019194800050107000e05030400001c1a113031800c400007150074030841c0e42c2a43d21507580040d5070b864038140030003d4010300142000c140c0540081107804010004028101c6a20503018080d5a01c46d80e0b82505542c880c141c0c4581d29840350340d24954a601c03035001051250801c2c0140c81e851500c4002042040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 787006753 1250 787005503 787005529
    0x80a0504081b090a060312031d0709020309070504020f16030c0c0b090a08031602120c0a240309080d05190216170307140a0201060b030f090f0d12110405 67
    0x50340c0340240306880e0420304003d40d80840c4002e8100709a50840da1880c0395496450030071020903503252404001001c0d0f80d8214107001500c242141c180c2503a41d98080d006e5071003290041928010b82c54001b850303041900945201011480480d410441518040140c0c2501c00b03801f030b400c000040d42e0000c00700d058040780c4070242c14207000145c0d4441d02d12040c402e01500540c042c030100d60003002144510385003950402ea0036a4112240c0e4488035800d101d0354074045101180582c0505004030004102c2000f80c1c4940201c042e0480901c40340000890a8044a41041c7d000e03040b50740030010981440015440150f00c03140c000d01d102c401001440d0290101e8100510080404446081c11418032007000d4000340464074840d90b240c61880e041100038484005106404101c49012401128050007074000102800400482c030741c49107004444040090001d440741c1c245402294113004810502040e5030404904607142c00740340d4803e0390b007464020a02d141d4504000002844042000d50f1500081000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 787008003 1250 787006753 787006783
    0x12060c070839010b0901180b01030609020c0c030d0813080f1308013603030506150a09060e09160513050301090b150d0c0902030a06150c1202030901050403080a050408 73
    0x10340c00811101d00312a01019058070544107a17004003d081c124401c003d0b16114a070b0404580c0c2c01030b800041c3c0282007990851840345001040003028403200007501811054101d086400e4128500307416680d2200a403403e11220110108500c00310b10644000c040c211204000f0501d0401108a8101424103580006c540343c0d44807e016072010080450303480e00f0503441d004440c7d4010444140342040b141ca204014285602c0703900040041e40c884404e9240c2c072548940050340c030329140400403c2500a170251002140c1d000c030a0421504014610b1403056140700d442c401c1c2c1d006001000d907041d8000074a0807001040040340410a91028058030b007005108115032a080e06214071500001112001241e00600c80720310901c012510312640c0c0d404980d410400107907a43c890010407000f610b03680e0002444103c2807030b841402030350f0064a00b49500d0040080c500e900907840c2040b6203900c0b80740049800a1014030013400071070709180013000790004a0a002e480c0c43da1344c41d03c4a0a220300c1d605a450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 787009253 1250 787008003 787008097
    0x40b040b01060e010e09090c060708120f0609070309051c18090c0f03052d06090601031505090c04030b07211e0e120c0c12060c0708 58
    0x10030080420000e41c090301c1d090030300c1e40d0103100850000b030801c5020b10950740703d11031000106541504c14030100b401d030352001d0700b240ea40c0d00d620305040526612101645500b008942c0c00039100d1004041181d0191b01c0051040c4401d0b25440c1c4114040d01840030140c0e210f002e4041190101c80c0407059038404000d00c0e865100c10703c03241010440d030070180d075446400c0c050305180c144200c560303006070344522100d1141800240c58a641c5140400714039500300102002e040020a000030a042d1003403144111801c440440c6513590301801101038864400c00c0850410020b54107020601d08141190b40c880c075268401401d041d669102d0010740f000030b55001004c1050080ca04c1d070307292a8811080314002003c0300034440f08254007200e10303080b142d800500344041c1c0e5031440c000001d0b4050024524404000003115201c415070140039440f1959000c00380e02c40c40b4402c0d090018aa00815002d20070100e9007992030074805140c480941c551312030704608901c48000c040585e41d083c140000703118541e501107242d503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 787010503 1250 787009253 787009261
    0xc05060d0903030e0c0105041e080111182e02010e030a031b0809060a020306010516050303180c03030711030f071409090c0901090b0109030510090606050a060f2006040b 74
    0x40c04451513041a02c680350003102007002240d8002c011203044440540040b0144d039069000000f401c10342e60090b2035654280750342a0b41900c81c01020f00b1000d800443d03080440001d481c01c100740000c0c4911081600024858600021041c20100313102c0c108640c0000700d0045100412142503130b000700e40c40400b190b40c032826070356840c1c00a5070300c900c812014100708015003000e89074640d0301e0000800140c01ca0b80c002001403003e910950a580d00c400c10002c2e42d50700b0381c59903e08a920381e00212034411003003101e04030582d00f00000060000507a20064099403810300d0b07580f2608001a4010010368142c40f03541c1c4800e500308400c10040008014090b0580c40c00702c8200d080141440703028101200f541d1100b0020196590b0b8000d15604607552840d00061100440c001a87c80011607400a4114007940d99104613031030881d0041601248100b0041141c81c1d1640b0400414864a02861000609200d103201030180100007600c2e44202c03075203e8129500e1228411403a200301103030100c80c42140c0200344 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 787011753 1250 787010503 787010507
    0x90103061406010810030b04111f02010b0d15150f03051015050f0d0312110705010605040203040c121b03030c1a15090c191d040603031b0c05060d0903 66
    0x815000542440e1004482c00c2100d8421748102181c000944031982c0795001c0740800881d400741c404107240103400203101490003501d072000c400e100c0400b000994200690180d89103408803e08101d180e00404105205813170f0340c40c60004021140d1040c08151200d040030848110042c52100210302c0b640c0201074400011662805640d42d011004000e8020608140000e42e41c440074003403025000d540c6007034211047c1c1402c83c4c0d454204401517507803615004540c480c0d201c450380144000e501a83c002e21000340d503a02880101d200449024200780005041800121512401d03030b04501d00a03442041c480d400925401c003254003540c1704801080b0f000001c4410081c20b105080614144500390401c146040170711400c500c903030101c446110f00c03000300000f1558951030f01a2a603c00403111403801403021103402802c00c1840850340d10103a00340a00d084c0103031801c2e005290607240e140da00e088154100140310810083c44c0034044500e080c411074040b4081e11070b4030184c0200100f0010100300c00c4001d041c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 787013003 1250 787011753 787011791
    0x90a0f0f1d0c1204060b09090a0b0f0403050909090102070206040e060415080c1201021e0a020609010c050a0e04020918011502150c1e07050102120f101703040509010306 74
    0x10703545203005018100102e1007000c01c01e85454500c800942c1da0319582d42e24158008215490495034000c040e1414069107682c00103c240f001d501c140e042e0b4005071a0314801d0440d20004540080006034100001e00342c909000d005560440e8040c0c001506028017540003408076000f5801207480011500c00300006440d10b03010300754000404c421a004070a0421004584841d00240094041c020314841c41d00c0c410380c2503040340d411001c420b02104000000041207071b00b40d80110801001481440d002c43e82484c010310902458040e070303441d0390b4500f0070070b10400e4607850a1100c80a41c0a94280103425080d06c4412031f07041140c01000c10388a056051115003880c03441281d8500046600c40c400d50700b201c0441300170245c2c1200110030764580300e55945000400707083d0a007001881c51180499840104401500070340854800c2204500240d074820002192010b030480b001040c42c500810104614071410303884d40c00c3c4080c080f040da4038041e04c80c00441c1c1c0c00b11083c1d0089600a6603100c1c1c0b88110f1411351a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 787014253 1250 787013003 787013039
    0x31d0a120e120a02040b150304050102030103031e0e1c05060703050402030d0c08093003271f02010b0a0b130902070c1701061d0402030c0901080a08090a0f0f 69
    0x1080d000ba4000032005540e501daa582c002405156030303039508100c5550f182d4224548454074902e0640c0c0380f4091506078080e41080c80100c011500c0c4c103840900340722201c1c040007003200581da5030345291440d0000300a5195001d1070080f41498aa81c80b1802040091050600c03940c4541c50115960400c0d01c145480e18480e01001c00c10001050b10070b02c0001c1c640e10071a80051030490300e101112440c0d1404001c5000140074024101c0e00701e003607841201b00040003034445800c10186000b220090414081250380e5040c1c2100d1348140088414591044071310310020780c0c091107100001c1c007000700802040c0c1c0305009420200d21007102040d41c5a8025504c1c3c40b1074080c2c0700c2101c0550a02016030b5400200701e501c1d01034080044080c0e01c0c004000d45095011800401d4012400c401d000e000e46c2d10801d40400c16601640039000307009111965007021f00f02941281c0140004182c44109038a660005420480302d8542c4000391882c001182c0d800c02d50721002070301d0044805140c01e45021448505005695 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 787015503 1250 787014253 787014259
    0x6041e080607050a120b0d030c0c0b0a0e1c02040c0c0c1a0f070501140112060e150c0901030b060a1106010f03030f0c0201020115091a040e0a03031d0a120e 68
    0x1002c0001240e807002c1614907007240b90030042c551503d182c481c20050120701c440035030000fa052801c203040c19032141c090203407540070b03500d2082d0044e01e036001031410307204200300c501c00316150a440c21402d050050381000c1110440e000028959680e0340001d090f00d80c01d014510005800030b040380309001000002c80c3c02441500c10340b5a0b18604021001e06074054017544141c403c41c0410080140a0b080d00000070500d02c50f1065030942d071711504c29440450205206440040c50712520030781a800c001a105a5a90303005410440c9955100d10b10420768041e00006040540360070f042d41e01c54541d01c0c040e14101c10725841c0e812690305451621440c02c54140d0010b410000159420004641c001c0500c3d00c074440c00d8a09030798446c401c0e00060380901031452a0541e41d03d00114001200d10595018100d400030b40308020260340404030411080e25600c0c2040d22072600303d10000d0f00081e001b644202494a041c10741c0c03d01028040d012681013200d1120140e071000b401d00040301f1710380e41c400300e000394040d012 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 787016753 1250 787015503 787015513
    0xf09080d150e0f1803030a0c030606020f06063a0212070b030a021e03041104050601090e15040605060d2c030d0b0f04090507030b072c0d0206041e08 65
    0x3403000840b410000c0c00c0c442180d0407a90224a094034103000d5000480d030084100d0390b036800c042d020031008000d07091055001920340300010079000c2c8041405031013100020010b108a071101010880ca80407042c0032501c0c08a050714289e0100c41c2c418081501d502450389120945540d24018410b1101d1120f4180c40300782c01001c000e000d61202c9006136500701a034240010f0f10703903102d89109001003040c2003580102c400c0100800c030810012419840c0381c20710a07102401580c440d2001035a00e042c031409101d51060456000440e0401603110001d40a40c0082c00492215982d9010881b05e620011801012a4456606c00300441d141400161000d1010b0365003241c081294000e42c0e200c1c060050100740d60364503110004120340e240c1c0c08001c00613800820811001728140b5026031758032a0b5220464800380d207900081c2c50a4017400041c1e00207001c4a05446041d010b50440c0c8010002c0049079552044240800e60f015841c0e00c40900302400b051100c030700d0300040004107002051015070100301c0c0ca5000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 787018003 1250 787016753 787016759
    0x61203030f0703020a05070b01030b2403100f0b04090b01031e02090627072106050a1224020304021c0809040e0a0209100f141f030f09080d15 62
    0x1076110072680c40003041c60010b841c0c80501100b141d035489014400b8004c00d40080001c01441030182e01180070b5070703003442c1725070340644425501510421400340096158111620107880000d00c1d42140c0140c082c2e0301c8000440c002c0c4d13580003074103c030002c29040d61ba1400400040c001c010403d0f610b8008100f107800c4041642409500240c440c90009003110f014004c010030480d01e0141926000c1c0c0c02141126207503615103800203004150284c108000f488140c26441c0804118005101e0340c0300341d44029044090140c10010640034003840c6200454480d000e1000800c81c007139179001116a0341a001101603964281801045040ca0009140000401e00c070301e0183c0000d04442c00326802d03d00242e03004140c0c2c180e044414ae003413024806002c5d400c008203804000303e0007055105041990386940851f0071040c0c60b03201c0725607070b500304403882d41d0803c489405e00516158800340b02130040103d441c0109a0401c0002d9139015500011404ca4000c000402c040025031528056601413401541656140c07600e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 787019253 1250 787018003 787018021
    0x50d0c031d1c05010b040c030c03060e0c0703030903020f0a03021b060a09050910090f0c171e061201020d0f0b120a08070503070b180c0406180f180501020306120303 72
    0x15141084802c07a40c00c02c5010300800001707403c4050700ba60014400c021000803440068050424516901c1c002450100041403401d42c11a00c1c501640c0c0c0050550305242c010780d0241e009101c0e06006409601c10300c40c110316081400c200103607520703210b50301501c04944c08000c0c160308000c2d005100ea101d0003091101d0704102c0d9101007600b04481048958583c00d07214003110042690603a0802d040c518184942c0124040b41a000011400c149030341f6078041d06015103100821000c25603240324043c80c0340e1040441c005207110856008070f0003c0c10307203081c0002242c3c20307400c80c0c0c0001090f4642d180c07102d03a140c1513601c5500c510305110101740d90212000d21450380c81511055000402090824041001800c0c404208241d134030030703035100401d4078007401c20b05208900800b40003d400c0c09440740382c01010060506001e201c044030340007464015001e0b060300842000d440d10b05500b01e103590b6140040c4940d0103d542c0b50394403a60040b4001a40c038248041404200b990b1500d2140c2c0c80d0b0300410034020011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 787020503 1250 787019253 787019269
    0xb0a081507090b03280609090b0f01060203030c090a0e010e04030f03020307020c09190603050f100218010f020a020618040e120306010f0513230f0307150c050d0c031d 73
    0x10650b00d418016170080b401000321503e1003070400007a0140b4000d404507040c08a80e00c1940c1541c0940034203d642d0b40c0b40d504034100304409005400040c1c0051011840d0704060f6000f410a4240c000c204d00915510360900303034410203003684110a2000418140310515805c45001c01914160780b07015807461400c0113020f540c0c0d41c5068002c6005040700b40028031340300e162078100b0301c0c01c4030000d50901003150350742491641c4400546050010340598152881100e05c10700c00c40b00c4a104121a128070101e42c0c82c01076a01011240702c80b0154040c02400000507543c580c01086200c0001c100000c2740d8038000b0070f22044400303124446030207500401d461200303101c41209803a407007007092800c440c052032441c03030440c0c1d54019400981d03000039025030040390309903040c503414041c580c0d000d0109a850750700802f0051020146000030b90590413001040c86000910052801515410300b8005412016551140d00e0031002c2d40850002404110107013041640c4120314500006000d032422031400c4944000400075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 787021753 1250 787020503 787020511
    0xc120f0902010509010f1b0c031b06090b030408070506090f3313060c03051b2b1d1506010f0207060c060f0213050a0b0a050313060b0a081507090b03 65
    0x106c0342200b01c6d80c5525200c0d0b1102162071118481c0c041050040380340903500954640001ca0304144c0c1d1945065201c40141000421240c07070b950340102c01231505c0102c80040e0320150094a68080c20410500400c034104030b4503015562040080c0240c000401407039090007011880302c41d80c1d900c00703490812104c4000c800f40c40c120021060002c00d607180c040858000110521000344400d090510001340710ba0503600a1740b0410b00584003409800c42007141050300d2080340d5004c11049945039240c0051700c43c80c90b401c0c0701c40300014400140c030002c0d02030340c03107504880aa0402080d0310004000c404040c4901059801c09003c0c2411511030203c0c8601035110440e501a00041000c00a050300901010390410b580d0306d001c04600710b686503041c01c4241c40304078503030040317070f0180d446094000360061903441200c07030f01120307561400d00f55122045921341e40106030304151480d07030b107450b0680026698a021603008205000080c010303455031118408102c0c800800c0c240c203000840ca41000b51003151000c880e0700c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 787023003 1250 787021753 787021757
    0x1050609010e040b010306170a1205160609020120011a040203060901091a0901090b010f110304090207020a031e06050f1015020f01021801020c1e011b060c120f090201050901 76
    0x48007130301c40700482c0144501e03401500d503001d00684250b11040040f07100354041d4001d080500038044804015035451261380e00118540540301e4181011450036805950310510500d407801d030600039140010081d29826140103001e9541d06ca840c2c400b040d00c0c400100c18144162029819481d00c500081e00401c030502c2900c0020340c5484400031000301c050764102c840c48005000d40880e58607940740b9801049802c5265021480b0000924003d47c05000600b00c1d0b108250000d42c9014102200302c1d0294104100403600b0040e5040080000341400b20045032140c0c01c0a0541c0802c89036061501c16a40c0107849800b018150001b4130044420107111135054032140000d118020602010481c80c00c1c06852011440d94030200f1004901681100340d1218074400b682100c0100c03050108101c2803200a40c5c2450f0250340031200c0e00e04550203084501c280c1800e0034400c403440c920f1501c0c0d0005640b842101d00000569807103181108246034800d030100c5088085007040040021360028003075108021960341 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 787024253 1250 787023003 787023011
    0xd08030712090605091504080406110111040305010e060a0501050d120516060501170106080c1011010903080a050f060108190612050d030c051303060c1413090501050609010e04 77
    0xa4400e000340362a201d4501110810801d048050900600900c01511020158042c80544c24071140340300802c1c030300440d04070181d94549850641c0540c1c80000340407804503595200c49000c3c50012a09011b00020f43c040d07400801e031895640c40d5113040c0346004000d00c0744030703140600601840d10740ea4803e01c0750542c013601c003c586039100007095469000d00380c495440d00b207201e800d480c00c01c680b50308420f048031000c5005001d600f00a0102130300b65002030041d00318542c001c1345015034a02c1c0020403105918602d0802400315105103009909481c15150705a000c2000181031140020051007001d070311500241070480d0508114000a0014502500800150b01c444071080740c0020107030301c4640105248090512141c59a1a005403901101002400403902d4409030810243c0603c1c00c03148801c0b40c0f07040b042c030441d0450791040010000384003040100881490b0ba000e80d44840cad4001c00d84450803c032001c5609241840001c1941c1058000d83c2c001e8200303100118950740c019044010303501017110082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 787025503 1250 787024253 787024261
    0x90a11040207020f1c060b0f0108040210090503030a050301061b1109190e010f0c0804050a030c0f1e110a0602070302040f27050c0307030f06090606050a1806090b0d0803 74
    0x34004005500d030040c5e11100c840340c100103090840340c100c0303150b900c120b00c2440000c1c648030401c240d038038056000c41d01003040d450000d0014903040409101d900c0d540d05107820403d4540001c2840e6811142c042000300d40008010312205400c00d1000b400510b180740103140112640d81d5406070030503000740b1240140381c400301048007901642816190792420901c10007108600000c4a8003030401307a02402843c0c1d00c0c0240343c03090903100c0c0000c0b510850f0000000c003034040d8140c5c0c080354011a802c0d8241d600060305420301000648030904640c040d89070307403028124144e4a0420303202c03600c00401b2140c8294204541000020b80208205d03080701e40459001807100c4104c08400c0107000f00e040b900e00410400d180d41e45d00256222500b481c407500410484a05402800600d5a90030903800080d29038400c09405400040d42031b08120764180c4a03103408103005564002140640c1115001601c80c4c3c40381000558894040b032150100402e018401481039240100c00b0810440c806070002d400c9080000000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 787026753 1250 787025503 787025509
    0x60b09060724022205040204151b080a0314060102010e12090303040308030c211003060903020312010f05120c0a03110a0f0e0a050a09051b03190503030f090a1104020702 74
    0x2c200340e00c841c11056513105050400490a0300031400c009001c260411001700f042d080900c241c5054030f00000e0100c403500d604980a8408819600540c0800d56003844600000741031036028081a0810303486c0460460340d680100c41200740700030300d01030440e85050040d60910300c00142c1c0078a040040004656a000c801001ca400c2d4822074002a0845d01c001091004001600307008003e4950b96000c103080d0505151003075100840107031903624643c6540c48060001c140154041d9041500c03d0040302d1400000e2080a030301c10031700341d1190760000d041a80800442c01e180d4059010941c40c103001d80007008028000480144c128000501140b215403c840003a0f15007440c2038001d405443c42030390040340e40e4805400071a004540803140030382040d0100c0c4180000d030003001c003110f5006010300544d00380c2c08281006051b80d0311055a25110b02034400c04031008d840c5004007040d000c0d0015650b40d01d41444032081c41a80508000055885070032500c021940071803184c403080008a90250b0344080718000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 787028003 1250 787026753 787026803
    0x90f01110a14121b010b1005040b0a050405090a05010510030b0a1809051002030a0c05040503420a0b030d0207150201060b0307110c011b0b04050703080715060b090607 73
    0x340b008080800503005a02c1e200641344460f021014100038040c00c020f101c1880741080c140803031031010610610051206a1141020703000ca544075241040c10156100000340344d8000588580c69030f1a80e80c00140080d090500d030041000c1d840341400c0c0400031490000c50103110760b038841c002c01c866007082d40c030a0115480e003140880341c0d0801c08859040c0416a4600003e52042c0c8000e45e485180a4800c55294060400c0c0c0d03045400040c040c3c01e00c21092005104003503080040501e040503019030300e00340301c003040e104010b502d5140321010050303103003d0851004035140001c00303d02c6030b0b016060403194180c1c0059810306030394a0240401684c080301c0001c4e405072600360400341c0001c8012003004941035001c3ca03400c040c070341c552089840070003608005680e810a0b211003010101c00030f1041102103070a01c401e1715000340c81740c07048500003580e03501c502445411001084034800f030441c41d0000c225039980154000740c038541510b41e151910000004007540b080000050102c1100c1342840c0e42c071418143c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 787029253 1250 787028003 787028023
    0x60f050a270603030807020601060942020114090c060412050309040c08040323030601110312040809030609010e0c04180b011502011d0a06180611090f01110a14 70
    0x100c1480500c1c3c50f464064103682003240e2000c0140309600001840a101c1c081400881d104040801c90400102400140b02002c450858205919244281600c18141c0f0012180e1207410b40c0002900e03400e2600145801030054541c3c0c036144d01801c5010240c1c1d0351002100c0854200c14051a44c0c980301d03150444c1035005511155521901c0c0881d0010000d41103130019120b0352080c0c6c0c80b2280c24150300c03001501c0e4802e00c410910020410720004842d0f5004441c1e44000c00b00580880b0b0411072411140071040b00101d07802c503422030b00401d40e481903003410030000e60000c07002402442040b100882c156a10813010626500c144d840c2c9082c4040380036100e4010030401e402156481e0a90307100c0c00c9001c007480481c950700b4019860100441d4140c1511a20b0a14810090b006003840c814641c540703030003800f81d0b030554440e0709032024a07041c0000d4062146851262100340c0041e11100044200418540320401c00e5050000090901007d0700021407510307811a8050029401d14008403400c91404854074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 787030503 1250 787029253 787029329
    0xc03060503190c0e0103081c0c0929031003060e0708060a0f1803020f0607030b090610030b0303131a03060607172a010605151e0d140a060f050a 63
    0x61300110901060f01d00410040c003480380421002c0e58021b4020044900c1d0321840030000d0700f141c4050101615a680c42e02212810360f282d5944200d101075400e543e54400d86210b840492035903420410080c2601800140c05140c2d009000c803107140441c8961508001020400c032207a9405030201707040482c3d8412220820080080450510140340207952240d04011096240c441c5100050105100e4003035141c0650380a070940456440c0c030410700c03501c80e040061000c00d042c1c403086054100d4404102625141e43e04180a5000e146040c1e011504140f4109261201d50002c004004441d100c00003166400d035842051580110641d0050034101d0080c02400030420b4031450800030380071401c000210039600480c000b040040c0d583d40800c40c40501522884110b2401484180611855000308401c80003a1000c1e007880d014050011500b11202503c2184581030f80342c007407265000c0c407403003068050220b04080240c510b00706000110090707958410116000032000342100c6443e000d14040350504d0300d407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 787031753 1250 787030503 787030529
    0x10201020f0c0c120105010807030809030f010e160b0f1603090506030a20040e0402120106030f141e03090f04061d06030d0c15050c07021504090c03060503190c 70
    0xc0900c0d692241c2c1104142840307040485136007450b46a040c85514103c41021008100340d6286969130a002d030880c2c8651740c0d150140000e0580c54103001c0c080e0700b02400f5003e0140024040c00ca03820002140b107504414102d06081c4181c0b025658404226610800c0c1e250241e0401d40c481d00d000c81c1c02844c103030020380d00080003009102c0142001d0b0407030800000c0b0001ea04090480200000929008501c1000c80b00c0c0d2000e000301d405070903d1030141004074054000480c0c41c03a0ac03a1694114440c0d41d2208035600004e440e044a048641406030300000c0040000154200000801d020340e41c0c0100000b07948541c2c4030404514450380e966004400405185111428014541500d103690600440711240a030041502d018a214803d008440c8010751100c840742d252480402840010100107080e1004648104003a03405680c03010140303c00c90700c240341c8840c3d8407424190380109481108604000f070504004081c00b0b1540c0120b04101540e504ca10b015203500c101c0d00304014001116482002604a1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 787033003 1250 787031753 787031767
    0x2060309030c1b0315040f0f080c060c07120c0b07050d15031104051b03130c0305150105040b030f0a0b090a0c030819083304021b060709081b010201020f 67
    0x2c0b20312643e10341e4404800780d82403209040c107280011603003220b004203154500c22483c0005100c04002c10005030251680c1e0342440a5501403c2c1b0b441015181c0c0082d1070804920901000401c1d500c1000381c410901d448820310940740e031490700500c005000308040c0301740452007040500c510303400560042c0d448000280500e40c0c81c24070041102992000d135000341c0c1080005500e640c0300c40f841350f4414042d0f06c18a441c60f51034030800201c44180240c100c4103102075080c0080410010015460f81110400c40440c1c02d5251000300821607102da06564040d811110758400c0088010460710f540c517400030f4901416580c0e9000c1e041c203240003508000c101030307400c02c408410301c0754030000740003030b4000c01a10b00024100080c080c0c80c0660304417426420340d801c4c620f02121803410101c09980013019040d800120350130160014050349c100c03500000e0181401034541d400c07443c00f00102c68106001307040010056044c40d40710f5858400000e403544551240d0142c1481c0380c0d02c00d504607000395040e45007064071204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 787034253 1250 787033003 787033033
    0x131a040b16150c080618061e0f040504111f05090d0c0503060c0d060902070f031d12010c020c0d23070e07111b220221090d0c0302070302060309030c 65
    0xc42aa240c9004216044a00d103406d5030041186000c0e40c0010610007502400000740341440b8510100c080d000305411103901419116405003c0c055485a0309054030000c000090088a40c0c0a15208149140d0212304806c1c0d280c215084496404040d11244101d518905142803115590b80c0900e41612580e010030070300d041c2c854042c0ca0103408000301440070617600c00d801e201381d0240741405041034a00c569480700007801550340800c18648502d264006018502c00503085004050048015944800c0100110359040c09204600003007111080c01d010080d80b50100c90540e07203140141d45444d610100040c100701000302d00010200c00003680754a280410005140e0f51301184111542e02c103209020141b041301d545228500c500182840316214062088101500c069803400038a26500b0070a02051242c022400b80000200e220304085a06080b12180d14244035007005004200c0700c1c07a201c8000135401f02d0072074210703a0111003c0e1786984659001500318815460449d00c28841d140c41d1010703442c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 787035503 1250 787034253 787034267
    0x70203031012080d0e21090307080712080a2a02090106110d0f09080a2d0f02060a11030a0f1e080c0a090308131a040b16150c 55
    0x401105001c081035542c90b40014206000390000800d81d80c0107100c80c44814100350711840c4080c040300220340b070381c04580d980f801211009440d500b048210015400002c0d0504210003001801440d0044c507491b40b8165840c20700c028280b000502412002454003911031043c004101400030840c40c84010301d15440e005280c0e5a007516040307024044c0c08000081da14080c41c070b640d03100382d0350001034030181a41d60301c00c9907004452440001481403200000c00c60180800030103031450b01c120309904010014441d96040c020200d0304002e2035912406104001401c20358a0780251a416035000b038a9120200c0103070f4003569960748081c09844003081603041c040d44680328451104194484508402c0a10b0a8001c44007892400c4008940c16901080913040c5c040001c11891200d0b00d090001c81d5180d03928400140c0c091100c10250300c011032011701401000c1810141c3d82c83d8035980c0070349010715050004030715005d105050700764481004502010322141481200c825032101b0707000c00080b421640080c2130030f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 787036753 1250 787035503 787035511
    0x1803090913021003180b0403091d040c0504020903070e06010504090513301d09010b1e0a092102030d02010e010f090c052e080a14160509061207020303 66
    0x241a03c001c512040034080d1107901007840b40300445600004441c4c503800d0408001030b101702e00f0040d42c00303c0012000300b400407050404680100c16045401c090514006180301030b0440c2c6c2c49984104280c002603900050444100e5401000f0141a50345400050340c05000702d80c0312514103070921040014121241c1580d00c0c2d05032103000c0d840320300c0d049050460303401801c80044000c1d4001410071703040c006004159030000a4902c0d909030140802c4400070903a40c020a078070a081e40308003c1554100f181d600c1c201d91552483c0c80e50315a0810409020007044004107108086c0040c43c1c00c0c08900312402c2c1d001d00f0f1400d081d00902250140d07004954024024600d8003d804003d502e0b1402c4c6507000405805101c10b8182c200c1d0110007810b08000800c14182d142d801c001c0214040070240c000d10f4204401070001203106900c403003500b0711f021140c044c1030703035900ea00f102d942440c80c03000c0244901c5810540c000b00d422514040791075598140120b0210703c0354060b0440e0481c0c2c44d5003041800d950001c000c0d885 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 787038003 1250 787036753 787036759
    0xc09050a0209181b070809040c09081e0d030216170a230901030c0c06141506280c17180901031106070c030212070303030c0203040e180309091302 64
    0x45500d5000d040380d03d07084d0b405403402ca4070035542a00700c40403180a0308000e8000d00103036207021003060005044074038284c105004125000d6041090002c14004400b804203c00200404d1048845043d5103508080800509065012484006110070a851400c0c02d90f4050002e603114165074110350219003120501c0000240190200302400c00e16218110700e04904040c001e081541c03c4e0010740282842c01302c140c040121a00211010662f540200b41c0c55410103411000741c0d0034484016120742c64008030345801140f0800008020f40480034215100381481200c08040550203c0103e500c450801c1c2e028002c03080c03a0f01c10b0504101075200800200540e1420000c42601000507c16412024030019041d40815940c0a810b4100350380180741082c403038281010102e449600203003068805406580c0241d018101c14001c054040c860b8141001442c001181081d10380b0303001424500b0002c0a40c0750680c00307259110804a010819180c2101008003202c2c2c140c80c00b02c6400f0b03034162040300141d01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 787039253 1250 787038003 787038019
    0xc03150f1a0307090e0a1a06090105060c0606190803130f060e090411040b0a090e2b0e03120a081b07022803080a02030a021c0801120c09050a0209 64
    0x80c001100703051001048002402400d42d41c1d1901880c0c0c8000e10b8003200c905603c1c000c500101c0300007415103100340034103082060202080d0510005000208905030021400b407101009400e81035070000480c01d5004000b102c1201e00c1141543e00803000c551180d100010610002c00c1a068024084104074181d440300107046800580d200000c41d001c032140c00c03440c0d40040c0c0358000306003c20b036440c29428100402800c081a0b8404040208601c40401c1c0d0045808a544070302a42c00d0070300c2480140c03a40340c0c07201d0b0300c00c01c902e00c101c0300f4581041c0140741c08e0062201190112603152001d000000d89030881c905a952660a0741c0c8019014440c00c807203215142d818440c40b2000c00d102c0300c05030307100c1c0d98000d0807604404415401400c620404d503920400890380103480000010400c1300202846900ca44c0510344071001810027034904400d41c184440700707c12003400031030a5a8000e40b07460454a04410494174541507080100780c2510340d401000e0001e013030004200350607034190021320019009603400700e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 787040503 1250 787039253 787039271
    0x13150c030b06040e04080a030b13050604050a050615180a0f0302130903020309010809010b0d1b0f0510050f0c0a1113050709151803060e060f0c030a090c03150f 70
    0xb01c0d034031460145452186118010a01007160580038003440400e60400040b4052a10005031030802103000c0d40003550b4840041102e941400d00607683c029480a005210070b0503c1c00024904c7c9410b1080c4140c04000400e02182e840030320181d40240d084060403c0400980354005d016850740e6078001603000d603003004145c03002111103102e040c031402d81641c00707141058420401190070307040c064440d134055901c8003103102c1c003582d4247c140304c407442c0305965034480ca1401d03074484440402c1952100304001c0c0a0300007042251030380700040a0b09101c0707107001d969444016680c13034110701a00000041a1050f50368500030407a19142c0d14000f42000c4a4030700802c511070301d02c1c0041d250100c8450300042d00c02c40b41081003040c00c4400310000001814140c51029044507d03045585087d030041c0c410300e17200c0c441802e250006001e21500901001460100382c60800840070030f5200241140d440b8680d0703040540140003180c01c071000690f5206212105043d0035400000291a48060b40c90949180c502c1e02 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 787041753 1250 787040503 787040509
    0x506010906140415090914060f1503060913050607020a030e33040902161b0e1504020904050112030305010f18050c09090c070b010e040c0306020313150c030b 69
    0x2d5960050038918440c0352608140008580c1603900c03031000c0a100f0080c10115140a05028076503e8901c806464441d600c0c0240400059944c910b01c030038001d22000c070f44880708000c3ea908813130740030b03078151010202c6031a02d50300e0b859411000030b000340a40c0502010310108683c042003200c40603020f079407442d0304841150204a4500c00d03095508607840c00341000d110610a042c2c1501004244401c20503091a64130b42c5d603002a640030066000c025261404100108039401403407058903500700608281c61403d24500d21901180035211012100c2201e407104041d98031134040b60300307409001c0d1061080d565500c03024800c140003880700304d01090805d000401c0c110103192200c02190802020400c6070300c03011040c00014030380605666014842008002d0381c98076401c15940c040c100c4100d03403a81d1001d840c144002c54803410b0f00b1054810301410144400301c0c881c080740d102507039000440161749807203007203c00c3c00d80e481c030140003480100800802c00703100d0546d41c00500804455141481000713055810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 787043003 1250 787041753 787041767
    0x4030b15060a08010312091401030b0127260c060705010603060c0306140d02090109020d06030c0f08061f060302161227030203030f0a110f100f090c030b0a0f09060506010906 76
    0x5a02440c00c681540c648c1a9031081d0001440c1d110181000c0700803031600000c07040884145110912060f8912008012405030103d544285400800c03041000c180d514007113a17100c540e0070714a944038160115000c020f000c0207500c410000d40c0d0145040150f05207510014001d0320700c61180348034000c41441d8800f69820600b8510400503801048680c0d980c0c20315104000941000c07494610309660b6030710100000d032600460350702820014142c100340d1441e007111246170440007010802d000640a51894070f8009401c4c03904d054030302c9420050703190481031141e0a40b014030064054102035000c105a00b80681040b0240e84085070f05941141c52007246242610311692444000c0d0943e01c00c000c6084001c00a038040d1110b42030303c0c640760024030f00c2c540301985441c841200d00f044540094180d2500c04d66180303d0044d490880755000d0120904c1900c03441160207051101402c0c128204c00014030030b01841e841075200140c2c07140100400e41c124113000b1300070201190f01c507011411054001c2905409000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 787044253 1250 787043003 787043009
    0x1051504090c08180c2209020a0f08010e030406020a1203142403030703020721080711040510050d14070b04030f0506090703020a030f0204020d0507180b040b04030b15060a0801031209 80
    0x207a00407400648210498900441b19a0a410381c2d07a42145006941c2c8044100080070341c0352400200c607040414003401c43c1e0b000601c80c880342c2d0041208005654001c5076a64540780c105103e15110b1a030000f058000d406003d07d4400140240700c200030241c0c4031244001d070a0001c4c600c10701071028221041c0359481c400c0c0d04010b000340c1d00800c3c0c02c00185100c0b009550325060103690704000121155078045d41d40d0003d80040714085031004611601d801d003403207003551100341c01d42951501c0b07180c00c01003a2803003610080070b09121006081c405110b1410864040208250700695640ea40c0d40e00b4040c1c0380e40d4104130221100c0c0100004502d00c940002248025646c004200e6040a440e680c6c0c0c2c2105021441012600030740c082c03254100e415aa485028810105500c440800180344040f08074000307071a4011842c049001c2c40244803240703040342030f134040c0ea91240e4004125141c0c0c0c2d03a004440f60031103008a0340260001802c0b514140d100301600d0490703118203124421840400016113950b10140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 787045503 1250 787044253 787044259
    0x50708041d010915050f040f0507120e0718090309051207051504061b1e15050a0905101d0f030406080903030402011209030e0909071706040b01051504090c08180c 71
    0x4c0381c1070002d40b80c5080311404809000700001685050220081d0546004a940801040c2d0703111054107448030390f0043e40e194041e0032004d80301380c030b00381380c1c41c2507012903060058000c840d51101c15008042c094030260016160080c4400710790b407500180c65903591481c4c06003500400c1ca0102d035205503d0414150780980703a0301d40b100390365441603800d1440003095003c02503600f00c0c0a00c1304418214944006a22428051901c80d80f0300c041122008080e10f0014001c03101003850900300324003107203000c2840c9030440407046022603880c0403c4088001441c0340f68201176a0b0107546600f90340c1100000080080703031800e072290041c035074030804441d03240d010494002e4040382d5502e54007141c031032256000b4101548a0f052810180c01d8400125003068812940010641d110060a00c80c03412020701aa480b03030000c0c07000b05158902603541c4bc12500381071060300d004c0c0c1c651100109903080d8076420358000d0010002e04200b120104500200507620130b03984881c2000810351000d80c92500454032a9103d8406 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 787046753 1250 787045503 787045541
    0x60d1409101a12120a0906090e070801030809061c0b01030510060c031404210b2a0f0c03070606030309060804030c2315040218040507060f050708041d0109 68
    0x1d0180110f011981c8180354083c1007000b140d0350714a00041c01250043c0e690745004542404000340400d2055005044141d215804011449500050550550354041035103a00c2c0d07110b50700828180e015840002204181c208011b058030340207548002c0a00c9405d903018427240c2c980e40c40010303941d07200b4040c3e000061401c1200c074000c6805001607604030074490b07c04601e010b640d91485e40440e0307140c20041251020b1100d0f40c10521580b07145c020f8000c000340c0300701c1220043c0200908444d914001c1d48840c440700129601500903035100a40e140d01d02c1c0d000990355200010310305a40140410700089011414201011440e244581d442da8451036040d00c8003402c1081035200c10701c0001c0b998240c2c40c1e046142c0c82e00210700344814010521076450080d03403148a82800c1c070401c50580000f4585201110501d801c100c049000001c581e0222040f03400c20445101c185d200480d418410580b02400082c000500083c28580e524450480364101c140140c29590700c0b07100c0c1c8819980c0c1014880c81e007602d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 787048003 1250 787046753 787046801
    0x20f0d20120910140402040c0503150f0301090204060303110d02010204440d1b0201140a1403010b030402010e01030b0a050f031c020607021902030d0c02060d140910 72
    0x702001d000d410088240444402000d8000c1010a0713441100d0780d40e10410410040c0802c5082501921100e000303581041c60541c030b4000224414006101c030100c0c8681d940602406007900c080d484066101e80260091080c10344a05000d0200c130800e2421902c0ca1060603000120b0f54418800d407000d69003480702d010201c03c850307001c480f600104c03540004517502c1000c949400c2003064542540c41d1074200001703400100d1032580060700c0b810a0300c2035045d0000d00c1008403001030303902160b0742124540c07001a080e20f80d2380000d4102d0f074040115a06018140b4004000300f400340036a000381d44102d200f60386044140a41300011825200750301180303500252200028013607498140b00f44002c2d1300b80a000ca8400c0c00380705048000404c282824400507800c01e40034480d5460b0b060000c4145d415141c1e032031104914856000c20b582c1d80030016407004002c440f80c42e400855030740320308517804039003e00010700000402c4180085600f0040c1d90000c098402d815000001c1c0d2020700510341050024014102d407501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 787049253 1250 787048003 787048027
    0x70b0901021e070f02060903010b09070e01170f0c1c0e0a06050c0a080f0601050c060408070303060e090709050a060305030a0e0109051215060f09090105100e1501030b13020f0d20 78
    0x7c5141c4441e8107540301c505001058440101c20351007000b07aa9a2180c201c40700e4000035007142c604a406003911408a0100301c7d401d9084004030f40c000f0115809681e0301c0c0d02811000c141c0200091010740310605000184a450400207141c182d0980100740422494a81301c15681c000d00c03d03402c1e408082020640010a105141a1b00c180d00503410304003149885003018615003020340484048650590108078801030581c10300c281d40c040c0c01c07940d20140c61814107007030326035403180507125102120f5291800181641d40d82d4022800465000c01200d0301d035048188050185030b01d6446981c0028040000000c03241340a80100c013959208c103015010424019003900502900280395603041074460b000c41070682ca80c5030209101d4107070400002440c1c1400c1d0210300309000282e01100001341c00c1c1040c01003c201100c4050354005090a00013101c281c1200401d00c4d00d441000c1140c0414408984640720b01c000d10300a0203400c00e03c0c0e034200f042c00c16517806054110b002c0003842c07180c2e0f8400d00a02c98804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 787050359 1106 787049253 787049257
    0x815010c0201111f1a0603040b040803091e0105091501060f05090a0509090d020d030b13051003120201020406030501120302030403030f14030a0b031b01020c0f0105070b0901021e070f0206 82
    0x10400d40c275840316101004c2c0014040040000214080150030080c003a4100d14810b1540040d42c02d00c2f04107402084210340b02c2c8500c0c0070b52858104002c1c2b007171801c507060315074544403540e083c048220300b03c4154112006064014008680201c0e041c1d64040a030703480740c80c1c180005e00584004400c0281048560780c083e900b45070400c5031540c0c5965680c40f0368203244c0c0d4107a00025007a6603203008040d11021950001c1c02440701c01340c0700c02d65a581034008105417035042c1c605000f1030343e0700c03040c42030030215100340500142c20501003403001a2246c00380c100c03000440c0c686101d080c0b207981450201c6500681d00401c140b80c0d1064441c030207040030702130020002c120401d45503036400031400213522411072041e0188280c80c003001c041d42580c0640705880e403154003d0007113441480c10604070ad000754820306200c25040d001d40d401401501602d030444000a90084511719081022780c240096070b = true := by decide +kernel

theorem cover : BRFrame.Cov 786870503 787050359 := by
  have h0 := BRFrame.cov_init 786870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 786870503 ≤ n) (h2 : n < 787050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
