-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1461
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:06:04.020569+00:00
-- url     : https://prove2.me/submissions/8bbe41f4-60d8-43a5-9e3b-47c10f38631b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 262589928 ≤ n < 262769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 262591178 1250 262589928 262589941
    0x7020a0614060a0b09030a080c0f0703061b050711100c0605090106170703080d05040303090b0c12060d0b18030c011505040e0c0105040b0f07060513061104050d110f09 73
    0x50301c40545105010301e02118000c110002c01c00b040b9130b2007000c00fa00400354030086480b529a00e401c609544c00b07141c0100c0b181c03924903100030003001c40654000c120001c1e011300c01e0015030403048076803160401409014003404012508070440d5074031000d81910768203507070b10040004440580302c03c480140003915210600044d018154800000e0311196840a0407469190000560321103051000900c0c84900b040844900105900059003081c82070a022900d000d1503134916040e4071045603150200d0030b02241140580c406942d10742d4100d5829200c000b40600c0a0301c60190301140104852000d15803400380c220111000c0003100c0c0701460280081215210070340d0001120903079031180520513800c1886400441002040300902c2c0703d016110549800e1a0443c01c03107454114284a404030007090001c0000306003980078140c400c00070854600b620540c00d10713200c0121008000300780c440b803000348810306c03e5460b03420203244c4c081e0700610390340c0e4104008400103c00c000e004601c541c000180e117040c04031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 262592428 1250 262591178 262591211
    0x30507140102330a0203060d110f0402210112120c11031f1a0117040f0c060f02210a03020d06080708010506130c0509010305040816080405031218040507020a06 70
    0x3e07030045241c100c0c4648503035044a080e404282d820540c050b0001c0701d15030018510201c080384111015043c1c010000d01c620006040b40c0094445d00f00f544075001c9041c40d01c21200c0c82042c0035100302400414807c001c0d44446642c4034843d03402600b070014800105083c040320030a80c03041c0c1c00c03004040300c00282200c204040b2803003841c2c4092035818101040e044411a014038402c80c440010703920031180d48541036082d42d06000103001912407491b00c071502808190031000e400064411500c4454503400400c40c020300e001c1010a041141080b84240e00d07000601210460706c020b0010715015850b08030700b0b40c40e08010005540840c8152064900000301c010040d04294890941150444601011069500150b5140741107610005c0d60400c00300507150302942c0a0303a0000d009000c907038208405c020b00c0c8120440b9101c002d440e035100124082005140800240046406084009003002c5980f4a801107045081e044180300701e848800040d00c06200f0001c1c8040150031013418402d10801030400c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 262593678 1250 262592428 262592503
    0x9130e010b09060f012d02060f0a0537150303030b0a0b16030e0d05060117190f020103110a0e0301060e06033c1510030507140102 57
    0xa000d50800809000c54600010b50500c15640a0318128200d48010011208440e15101811015000c1c100419411583d1030548000c0385150b0014603c0341001c07928400654401821000501e050108106803100b034041c1c210407012501c800200413224000c1c811100d0b89800018030262407610004040500341344024804483c0651401c21600c2100780910030700004078003400c0e01d061020401c502c40004800801d00e0014024a0200a410402d90001e450700104803404d0b64107074803510062044100d191122464400484000e10b0840070005200d1141171288101802c0240300001c4007040d64004d80200402d1841002c4d2580d84801800000e4400b01054550900a41c41c0450110b80341000ba02180d01510b00103000300307103440c02608480407444240f1081c1100b802c001003d404420041000841440f100d0006040001d41d82d500d01845a10300400c4c801d20b12440c03440800200328041400307003d4850068a140341c00306900010303450312080113011090f030003000c402040250f84629294 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 262594928 1250 262593678 262593701
    0x30f070905010b0906030103030507030e06030702010203060102010c020d0c0b09150108030703120212040206071401020301060309060b040507141b03070c0302011701180b0114070501020a081b180102030913 90
    0x8100d42d9072684030009050042c1e0a005400400402c0103002203802a400390180902c01d240c034002420364407002c1a06a04160303200d00142c1c0d008014004150380a018901c032080d82072004080010742060018010101d4680c044c2c07290340c0e51000300d00844e0b024000003511907114201d25005580d0782c03100d60307500c0e4400388040d40010f80a54001902c000c0c03500072144807441207195490503441300d400300440ca60181d001155002c008089504040700e0a0019500914664030300050380720084c185542910b0441d000300380725034a01010806e419411151186c40318034042011500c54540d00e00c0a404044144402c80c03461101103103180030004140070b488203592003070340e0f02d04845580061001e040402809000c00380e00e2400560700e000c00c46903003e210101e04c14500b00c84041e0302409008841c0d8400755007030742d039a500050401d0344ca9400480550700300c1c00031914140c000c22200c0d030044040c01080d0285880e840040c2c0004410780c400c01c151031500f400188018406e2005a400c80c0c000e2642d880d22 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 262596178 1250 262594928 262594931
    0x311030706050a080106030c170a020306131e090507230a06022a0d02040f05061906081f0b0a020f01050105040b01020a320102070213090515040c05030f0709 69
    0x1c912284a03200ba51028156a2140d00f0141d08161003a005800c031507903c001000a058404011080c00e60a894003070701b034840d00103a0b02e042c40e1040c4a80203010012100720a424a003624246c440d04601c2100074121102c3d0004400843c0c3c5421400c4c801c90b90320003507604c010040c1044840814112404410f00c04580d290a41d43c0e403140142d03142c81d400c080f00000c0e41e49002000d804040001c0034500c407068010f1040040a40d6580002e0071203481c01082c22400d980c0c1c1c1c04101560504007034802d0407192130148204c00c90b1814030000c0a5220040c080c8050749500c90060745440c1007014160701812440c0b080c1031f10b98214280003981c034208000126030715800c01000040768100b510400c0d05400d070690140140081507151000002080b8055000c040d5108840850f06000200c10100001c003c2d00050395030801401040401001080440900e0f4a80403c0d94000703000082c0440102d9241141400181e840c2e04110a104c011a484207416004002c5d03058541030001c10002c0554220307440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 262597428 1250 262596178 262596193
    0x6061401030603030816030e07240201090209150a05100e040c0809070e0c04050907050c07050a240e1c050f03070231020f09010807031b121401031103 66
    0x1107065954611001c0c0100b61981c002c2068007006114200b220500781c100407481043c02201c00d0314058081d40310b442d0031548001210540b0541c219030204040304d0344001e02c00d004450300000d0001d6006400d40305200407001080c815600e03000b03103a50003032800401711455070a0556000e05024030000015114074a050490310509020351f500031f0090003404014003502c3c0c1400c0741440c2403040a054030003901000e01000846070344501802c1d03c1860996500d9895070000c0405603d46229500400e1003055002c10900503801e078800343c0d55404994403c1d500b91082c0094003a6216444a1500c81e0404c2402281c0400500140481300b095886601291030014501c0d809070f8807401806402948072007032843c41c140d1022b1000708a05952100b40c7c0c140c103400c4a01e1003100c1280d00541c400c01019078042030748a42076821031700300c4d5440506070800b8010160205180c098110060400c00d0a010208140e40304e2210503600c2001035000801c4074451658407410900820181d4070400c0d4441e105805 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 262598678 1250 262597428 262597469
    0xb1b01051519080303060105090103020405360f041509021e0a06030608030912070e0a0c0e010e030a022404080601150512010603090f0b040c06021b22180606 69
    0xb492001100c240d00701a5083d80c03640001121b041c0d108013940e0341015000e00c008112541ca01c018480003505030741055008030406c68441415140080c074528461004000300f0003230440d0450f07260351140e2311048403c6006403103900f80c4000d14001c90041e4220b040b40c20750381c404610844110100c10b404a491720003541c1d40d20f00843c160307809c5003c0d00085400602c184021410001081080e80008400b55140c05464200e056200704080b00d04602c40e607201c48180c0c206075000a001080c5800a107400002c80c0245c03000700e1b65801d500c20009001e03101c201d00d90356504111110001005910600c079641d5142d41d500215502c900a0050403a0b00191840c0c55400324011411140c2059841c05505a07aa103002000c2d4020078280100b504c1c04d0314001907d074000b407035181d01144100c0c8074031210507a10741080c030024644004401d4200c0c00780c0038854800132560b1a00008500ca0000e0b086910302300c208000c901c00a00f07a451641807618034413040040400caa01e40040040e00e40e18462030a211107900c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 262599928 1250 262598678 262598719
    0x1103190b030109051011120c03100f050906370e09010c091202030109060e010903020705101706190303020715051204021c120c0309050d0506010b1b010515 68
    0x1900b004041e0b920000300c2480805d183d07000450038040d9001d2035802d0481350110b0302c0ea035003012203507242426000000c01c000798410007802000360120b0109210f2550515001c5551040080c0500b8410302c05c14900004c071841c0d0381c11b01d160304440c1c442d903003d2044110134a00000705890191140c081903034400074000c100d0510032541054041d680b803d182a141121080c00c0142044069030107540325010710001c19003d00910308800000f0000285083c981d0a000b802d0121941015100d02040c4c1269141298040c00c0501008444910080c0780d49403807000070101c1d1704030113000f0211148640c00105050b00416440116020b202d8000d80101a203401180e141c4541040d121550100b074001c01c015007401c4440c0710310054117454030900d5a0b481e072102c5039a42000030311440024040701100d4101640403000000908064503100c4001031141d5505443d40414001d04210150104040303182c901059020300c4481c0b0160020026400c1c170413546801101902c0090f030040502c000f201a090604 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 262601178 1250 262599928 262599941
    0x9110403050f0114130510060b030a0e071503020c0c03060c03070f0309030f080c16050609010e0f0c10050f040b09040b180a050c0f161218050906041103190b0301 71
    0x21104100107550f0704004440200e14075001b1340303c5104090110004010610032500038080c5800860b40700c1c9042d024200542e0507403410200c690b08200001c0100d40c1000d01a404080c0b03042c200941c44600041c262440c0440b050641540b41c482c0c03e0030320811404c1c24006500030f081a903180b80243c540312809409a81c0c0041004002680e101e1521440d06c0c0b080d480d07940c2180c2c1c4601c0e081e02d40040301100610740005c0341826031722900810f040c00310350307207091043c4810801e60102402c00c03621a405003d4440000c40720302d600030300da03450f01d5981451241048032007248030040420384454640d50040010b42000c0c125a000302d28106284180d86003c3c1c5000c148648682840d00042d51000a5640907100c090a00a018242804942603500d103041c0905080b0310907400043c444011424440344115540d00c1350070501512117a000d5021201034191026102d003910b010080b034483c0f9012030010010001700d0f901c084404014456a0f4054031070701040096840c20a0141c2c004e40e00c100b41c00c9919 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 262602428 1250 262601178 262601201
    0x60504060c02160305030a081e1f060e0d08030c041502010e0c1804140309120123040c060f0c06020d0c0e04050907140f030a0b0403270b1309110403050f01 68
    0x140000800d02d4070035100329072700808402c00e42a076143d4030303020034100503403c2c0d56004464142200c0031300c3c0360020148e1070300144032600c0c1c04060318496001042003076201c036501410079500080086c000d01488c400300c1c4e00400510207070351040c880b4034100174028480d20543d8640f501401401003031515200245518002000d18041440d80700c0341c0d100b0050000340d504525060005001448465541440955101e4003610003c02d2000c0c440450070759002c0c0d8130006402c4070702074000f4440426201c0b01144281c1d110703802d11503131602c89907000b070320724228080c0000d001c94000548141c4c0c40031190407d2030b0040d09a15110000d4259000b040191a81100c00715916408032100700551141c1c10160480b0117406040d0385400c2018401103404c1540800050321611000f50500c0304050f4000500c0c00c00c194244407080c03d1694642880603d85c03024440c210703007810302087c04c100c0c159503a00c42d00010880b1034030820041c0c0b148001e40c000e5400603c070584180c0103901d81c0d04010071060191203810308 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 262603678 1250 262602428 262602433
    0xc060423180f0a021c0504050f06130b010b1305010809010609060311010e0306091b1207030b0f091501050105070827030c010314010e10090c080612010c08040b0c07060504060c02160305 81
    0x6200364917000060400400c00e50300741c0315039045066820800c0c041039000d0407a1040c40107544032141819903184406030b00c4612960f03400c100009000c10f10481c0c1d41c040d10402d01c6c225943d1740f641c54000e4098081508191651072400900204108000110b00200e05003a21502e40380f0092104140d101c180403150215290016002a44010b00c075001030405448002d281c0d06c9515105d005c454504070054104484110400c02404020b140140700d0503880100c4000403c41002016416824060103216642c1440400320f10402001808070695401c46103001406042c0004001460300c00e0300041c500500074041e0a1440c2d1065220307015074601c10b16829a004002e074600381201c403828030010324051034104050f8010072100d4982c0503d0802c01c1007503403006441d0400c0c6007042800c00e103c94135518240c1c90a0b502100003034102c500c4642c065082130b41203055503a02d440c107011a00c03c81600030f081900d08410802001107541c0450100b0100354200c881c1406110450202e03401540005002139 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 262604928 1250 262603678 262603717
    0x70608040c09022a07210b0a020318060f1e0c0a18031b06030f090503030105060d0e030309060717150d03030609090803010905010f0513050a29120c060423180f0a02 72
    0x8c2c40305400650f000710a070105480030400550020b070400f201a2054001d0b2000d54051018000441d9003202d11301d9065115894203082542d0180e641e4440c0450b48810303ca40410141562030074110800f0046402001542100700c00b10490b0f0160700481c0140310100e0310740800c4d5481342c182486181c002740c7d0310100951940e420a001c0202d581c1100000480141d1101000400d200d0180007860150300c11780c00811103800c06480140c00710503440c0000200f04911010043d02d0610344c404828001c4c415260701b490410907003800c5010b1302d815004103110f81d0070320164a08010044008504a41040004000c03a1b600d6000580e10303649580300342984040e000c0030400229070154445a00304000d041300242101038000601652016204d10303220310500400980000e05106600b4036100728000d0240c201c41d192003000918500940c0555552500b81d070010840d0050b894a1460a400700201084540084000c0521250000703c8001c0c0e01c40003580c000c249024164004e0340c103200310101210090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 262606178 1250 262604928 262604941
    0xa0c09030311010b0d1a160f1b050d020d090503070501050306150c06040b0610090614090a0305010e01020a0912020f01050304060f05090c03070608040c09022a07210b 73
    0x8626036a1040b4656558a411500240d41c1d2152841583d500c540c0b600f8404400049524120200040008454100e804007061000d88e00c900c0051146000c1d00384201d4021446062444c1c405200c2070050040c07150008840d20290000703441d216074001030f5203d01d04a51500b09050b15041c02d4481d02c1d02290080c404170f90540b906014009000103800e09803420300c0f0f422041c0c03070b152450030340381580c0c3d156243e018007000e420013100140700b460150400d07510061402c0d10041a1540071a508868600046031440a136a80c40c40c0d480c0c000c5030850001d21240641c003014034000e5020a4091003ca0f0b41e9000009500c0c010124010380980c00610f030007a41f18110005441070b0380014401c0312215a10945901200e00b148240780c000d100d010000c0c84061110340034180f822840707820440070302c00b0940c10040015141c220080580d40700e07100150b1030300c1048083c06201d4000b5022608545034400850401c101c3c00142d100c1124000300340204840b50302103102c0a1500c0c42d040140c181219000043c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 262607428 1250 262606178 262606187
    0x16051902070f080f120c0a1b0501080112050c130207020a030c060e010207140108040c08061504060b120105040906140f040303140606030402010f090b070615080f060f22030203030f0a0c090303 84
    0x45124000c0e87d0301e99419507034825092004540c03074600412000e2041c019541c0c8440d42c2800352441105008900d9116100c842e03581000c4110513200d061420f12002c29008940c040d950429030182191030390710740b40d14000c1c81203490381c06a2800a00881130903001e662001076504111821203401124140000004580c0500c0041c019520420100302c005800401013001c10311441210310302e00800080c80b8100001c0e90703119403142c0005170007881805e65000e2901d92150440314103c03000590780200780350040241176241c42c05440000d804080095041c683c04819201e00d120755030810074061594074410f00c298080c0c8000e42c0109050001400550007206c0c060840550390411059503540c6205590b07441e40903ca00f207660a84485840350410001100e08028292440180080000080c0051b1f80c440b801005413840035400b00100e2082c101c400a44140c85048000b040c42c1a1168200a07541c0d500503100318400381c4070b001c00150f50013894411820300320740c01e43e511007440b807035510304a8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 262608678 1250 262607428 262607437
    0x90f11011806020c1201020406020304330f0201050c070f0f0204110301080c011202030603030a0c0f081b0d0905010203161401091b06080f16051902070f080f12 70
    0x5051258201d08001c1c501d941182250060460b54000c06180e0030000901c00e2450659900d940580c2c0103010030b00070203030048203550546507a02e0f8031041820260143c40f40980c1032038001900982070b1000b82c0b0301d140c0d01c1107412000d003d02d90003c6c03007a5122103081c0d5030b0750310401c40301400c041c000b1220200001d000420503601140014000b00d1508072003402d0230308076071080c0d002c8110b42d8041640c0c0842960040820612449030f4141181940b50540111340c03648a80701d0600100116a0450780400c40c10220542c1d1998010b00034a81380c541201c5556452440c205811216101d80300c0c100074802c0c0714607201d006403001030f4091400c1061500303034000f00021703106c4215010b0102509210032a2802d01c07401c02c40318003c92080714106c1c0011280c8030300700190781068081150440401100a14103503840d50080714080e030b44140200c40c000300f11a0790141355190307501811060b10003240154000303075110696100c000f1484d5070b19501d01c0119542d4014945000705a040b480340000a519248082c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 262609928 1250 262608678 262608713
    0x2090606070b0a051e01030b0a0509071211010908010216021207091103060910120809011101021809010609050d1202070b0d140f041a0702120409021903090f 69
    0x8074182074640d900e004400000b01c0703900a086a42c1d40c200302c2c01c0c00c00c181e0300c3c4070f0004030030b5998062541540c03601c01c92140020050000303951640049210300008100210080880d0344900110318150303d000180d40940e032101900240502d4004640d0070410320031501ca01064101010000000ea13003030041e000050f1761240b466000b890400142d01c03a9034021100c00c242110822039480c58000c04000381d010b8060925111341500c0d000034820340c9042d044400c203050300048016103c01d40306004a80c0ca50500d050f10f40c455002040260f0000010f40720400341c0b000494411250380c2e280c03038085510f4040340c401e0a0b4802421143c50010030a600f03c09001091541305995000da220030b85001640e010041c1711183c640d03601d8242d1405242c002600b504080c818110782a80d003080e494030400910103501c4a1242410740022803090740c02003045e6900046d00340301131600c480e41c40140b88000d400c2010b511170012694040303038020511a214103504541c1c809a4856003042584a041c0314106c01d8126 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 262611178 1250 262609928 262609939
    0xb090a111e190203030f0f1f0602060a06050f030c04050406060506030106080718060e090a1401090c03060506120c0d020f1209251403070302060a030c0f0813020906 72
    0x241c0740e1600031660000d0110301c03141e10403951010003504401c40ea004251072601190001d01c01e201c044802d0080450b04401c100c00c2660194a4a40eaa44540c2802c010071069090b0340c0c44001070115004102544540c0381d01c0c4040117078664a41c28800c2a0607a40c07180750341600281d400c44141d2906500454104d8011741001030416105c4000c00d0b01548282c00c440d0200701001c08010352941c1c0280148a24180100f40580d107500d085e8000c4e040c851010fa4441c816114400054003070b03881a0701c0b4003c0c0f00901d0b01202c14030350f5203082c400c2c01400c1000504002a04111012509050510480b062140802541c040b03540c2c0b40044403840d078202d01860b94580ea020455400f10101c1e00001d040c0100c0722030520402d50400c03442c2e0703038644240d034441408403c50101400c4140058440f80740c003185c0b0800340b00024034001c040080e0804210303420082d4405000b2134144141585584002d41054a03078544069415006005035030030a012101d400c18100140412001414540426030700250041c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 262612428 1250 262611178 262611187
    0x60f061b050c2403010803090a08010c0206010e07030e06040c090e0303060604050d1b0b0301050423180705131a0303190e04060b0d05090d0f120b030f06040c05030c01030b090a11 78
    0x143c8507869000303a114980315031000c1082107082c41c141840500810050000300000652600040c0d00c417041485000d03181c101e80d800003010070b40640c00c40b000307021902003520228905440e2011880ca280d010f401c00c21885c1100d0020550300000c1102e0185070010007190415250404121404460382d00403540114080406a0015001140b0002410f40000d01c25142d6041c80144812101c00241c148246141c50440d0b80c41114040052a003085a03070140f4003101c0900c59a02d0f1511320244d0025410005407100c20806401e2039000300b40d080b64440c0607080502d800800c142d0340c2d010b584114481250300c510000348181c010280103441810180012491a513260704490482d009a041071901640341e504003d0381c2c0b030060020013890806400e044100c40b0703042d180148420101903c0703a800e195a24040491640c04210003075407401c050045401d145403c2c40d203900c1c00c0869218403070203817260340455903442d8003d010341c2100b6080074203100c50640c1ca00441001400d0103e100d003109620410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 262613678 1250 262612428 262612489
    0x5090115030b160903080a0f1419111903050c0d030506130e16140108060102010c0903021903121119120e011101020f070507210f05030c01060f061b050c 67
    0x40c0c03100086a2300e804240c600c1c1c1c01405413003500d18400500c1400c81c100542140050b404d140d5850155280c60000c00d070450884800b032500000345246841d02c03150844000400d548a0002c00200d07180780305035521501c41c65000d0303040e18800e031040c640c898451016040044000d511030541c1d145840d04032402d04172039402d82d1010340c640740c01405810040c0b1400e052309503000b0111542111003031000300124100203400500c160000d000092054082038082d580c1e00d40c0d9104070748007454014080c42c41a841410700503200c07200001e41c0e484075000310550008800e0b009070b820710303030190031050380780c4280c000f2401222070304a40000541840802151312400b0300e0240701030007182d003940520655441250400340d03d00021a40580d4030840100029010180c40500e8003589980c040f1032104000c0040c80c040e81517004000c00d00b0207940c40c1c0b075170000b07420034280d500808490351501c0e021640c000c8095089110110440d018001d507110030a115401c2c1002010039000c0d11000151054404022 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 262614928 1250 262613678 262613693
    0x50a0c0501230403020f07050901060e01050706050705042303060a091e0b07030605030f03070305090604030f4e110109050f0115080c0603150306040605090115030b160903 75
    0x1002d10314201c001440c104000c00d40c04000002511040c58001c14915140c04001000d0b590140601c80c10032040351110030f01c503402034054601c00f4ad4014030501091030100c100030b040f60024412441909051001d8111250b1b002c940c0840407200900076002c40c1e61030483c0300d005003000100845032407561101044080900054a8280303922800010805040c88800101510170030f41029110340c10450060f15403184c0041100c8915a060034220f498403980000140b41c0e001d01d900c003410080a031503118003040f0200450b48000d1042183c05035014040804403c0c5040100622a84003a46200e20020980d506034003880325062030700d880c4105201c051265030a540e101102103501d540400321450a1610030b01500071039006070095070740c40c146440c0079152307101018030303e080c0600c41c0000418046e4100c0241480007c4000e0200c0b0981c0c01c29107001170040c031f0101c2e222031942d4603158500c412509000355040407250081d55054198455240c030104800c04980100b0038001e00311000800078524 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 262616178 1250 262614928 262614971
    0x6061204030305070f09060804120905030601151b0308150f1216050306040b0703051009020a0c02010e011b02040e0c042f03240310050a1515050a0c0501 67
    0x2e0b50041028100b50b034001c0e02844642d81c0d2013041c0004118107000455122410991241e00499400b89030541110195a00c0b401a0442d94250107180008682986a4100442d00c160f0070703901e0366000b0000c08007484900e0f4807640700800142441c0c0c086401504002401c0301c3d0081c1c000c0800070071a2803070001403c0e80c03500d2507404002d43c11400c00c068501609007000c0c80285003da01410761450a50342da0703009074030002c2100c018190344202040701001d0401c0c29070081e1450020865540901e41c0780503000305828001203000841c1c4000040b180d500c54541c030015004817250382d03000c2801d26820000074103d84041201c0600c242c00c00c6460983d29401122442a21813a40c1c1304030311000148a144c03480403558040c1801c004106000c80d01d0308100203c282032008005005c001001000002d040c1918000c001c0102401c00003880800303d019400000405540b0b0492680070303661751421017491241c0048000803030020311441c018a4040d10032683d0080c41100000b4060000200715601403d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 262617428 1250 262616178 262616183
    0x9031106130b0a020a0c0f140703080d0509010606020c060c0a0c0b0a1202070506010e041e060501170a0807030509130c030203270d11010618090512030906010e06061204 74
    0x109501c41d803007030101d501029500144428400d5107000404103024101d10020f0b02c006004080300c020f40402d11008003118040864004246c3c1c0d5001d5481c101070304141c0088145000c110f10341400724000500504c01c3c9030881c0d449070041c00c0c584404e4400c000d40342d007084603086805e000344441c4a0010b89490b183e5405860f0a00710552900ca00443c02882c100b03800b0b9600325114030401c142c001041001409a0440e1807015104d40c0c00d685500c1c2403800000c0b22100d001d004410320466004014a0380c12003810703100c060381500d40c190722032258596a18600d07280940b103502e003008000046071261004000c40100680181030b0101fa0600c0c11040754451007c02e40082d901000707006d891510400229074042202c4140308503900f018548079140c1240313200400c280100e507400e18460240c01e403c550001d00d03145204042000501d0810b0b0060808400f085550740a200f0500598080070300c180d9028818540040506a0170030300d038400b00c2100501f21551083c000d1020003100c001c2030780074500c102e2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 262618678 1250 262617428 262617451
    0x30201030c14040b12010e070c02100c1e1205041d070507020d05011b050309100b030c060c010603120201090b13051603060c180b0d0515090405030a090b0307080a09031106 75
    0x406400141034403030306800844c01440200140032300070354000c0b8004140d680488040ba6010034260b002d8501c01d0002c40c0040022890010348a407010b2000c2007840114059522140c500c4d041c81800c0b03c5900c228040e2082c20f40494010b0420000034a030480d07805102820700328602102c40d00002c00100c00c4010403100d5071b46440300945002d80d4101d030540d0300c40c1e030b03401d01c00e00398100020f01c65102c4180c0030b0054941552141c81854a0340c00300110911580050030359540d44102c4940b103400313815240015110b0b07142030040c45c01141e10500c5424020b54008070704c40d0789a210040d8100000f00e81c0e1200b81c80511031301c2c00c24014000f10184150081d07100f1040001e60b109148009001c045e0304203c0114004400c80d801c01c04a20180700310b45035604540c000007810f6451580d000501d0010354030740d642140700c100400c003c0190000043c10000e0468540714450b640c0d416942440d032100302c41680006043d900440c82c4140c07140c022034078041c40381c10a601109801c031030051400504076154039694 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 262619928 1250 262618678 262618687
    0x60c030c1002130b0703121e0e0d0c032d03052e0504021b060702032205180a020c010c0f09060203161e0b0901020a030509010e0601030201030c14040b 66
    0x285010400320340001e65200c010350070b022490911000c125500c3c0f0845401d100700081002c201440b8140f18911140c50907001c1140c101030040e000d1a4420909080d5191b603d400c07000c0c410080d000400c00e02003005a560081d14000d2036504407441002c4142d8143d40e0100e50180070032140c410710081c80d1412041d50009041d10748414644050f803002d00242d80da03003032a80708030702c042c40b0420f03224021f0310020759016a5038454a40444aa48004402d1404030700408040c40f00240d80407000709503803c005002550203400c01480144c0c86880c51241c10742c00140362900d000c1c46c0b2034100b2035503440408003100500340a0440141801d482c0d035103d0310000560190351560300f5a4000c03881101620483c130046080c01c182c4103410300d010302d80c114060405180351500407540034120451041c0c4960000500140f801d007003040343e0207508402c039032001103801c00c40000c1c1d180405210b03800302c41301c02000420321039103150019002000392a5503081004800c01c8603030b00000c40f00c0c00420003450303c5040030750748 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 262621178 1250 262619928 262619947
    0x80919090203070e090601050a121d0718050c1303020d1104020706060e0109090308010b090a05100804290403030f1506020313140d1b030f0809120f1f060302060c03 72
    0x5c11340b00900e1a418070034180290b008540d449903100d04010505140090803003440010401c00e136010034801d40f07442c8180c80b0301062090170740c4540c051181c81d80b2028480754441d14010207540c000d6040d03200c0d92036400102000545040100810303000e001e030040c03a13402d00d128030100b02070764003491050f00c01a8403500c0400000b21012646401007820314420840f0150744d40e0010191223040c455200c401c8008141d4a04a540d8410580010003004091004e85030070003101420840d0120b40079510740004444460200c0100d108203000340c240401440f4550340c03155070a030018200e0a1141040e1a520039841d00726291044460b000b41050340c004540b1010500044200c0794001e801c205003e466140310b428054940f40320640301107500c004d40941501d04034081c80c0151146600203032042121070768510034008040020000302000366011120010100d108540d54000f2640d000e9a0358018241c420300411480c400c0d2440d810300020100c0e0182d0f032500080c0700f50304500710102d17207078200003104041c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 262622428 1250 262621178 262621189
    0x10c03080c1c09170c07120206120711070b0f0a0f0e0405191503020a0b07060f020a1d01080c0a030906090203100506031c05040b0a1209032307080919090203070e 71
    0x410030104e8a0b03070b600e00705040454a40b5201d40c0d02c241e54a11a500303410070219580e000035152000c5416102c0c4405142201004018070400400303125207004800001c2015441c183c1103c0210900e0b9049a15180b102e001c100c070301c043d40007503140070022403294004481e41d0b5070040c07a00ac1c410004514600061b006409012503c0031628001910300c442001c00041e2989440e8104540031a1069034413159513040c44400f800c0041a08052244009075490b031954000d001840143d2241c80d0000300412820015502c0031000e40d19a43c078100c0c2441080402c901ca504640b0500b8840c1d400482e039841c179031740880c1c0380080d1840d0309150b0f99260f03010450f541c01c0401c0b06120083e2203640000b03080c419000c0150a41c452802150821000001c20722951401071412608090b060365041100c12580d007170060504003400407100a6898054041102c50151001d80d10810342194105281810500400581d08011040c50a136004041800604500b25102440c400d0381c041e107903000f801416504000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 262623678 1250 262622428 262622453
    0x10e01030b09010603050702030706060e01030c090c081b04030510020a08090a0b06090a09020d0b0f0c09060306060a030905071811030903091905150c1005010302010c03080c1c09 78
    0x24105850501201655502c8890b4641100c02505001a41c1d44503013a0072030451107120005403142e424120005080090b201882f8102c9014980c03219565450b24615001d03511040c2104c4002206100403c0060400d0004851855001d9888034035060f52996824100403000440040060703000c030710904015000f4413035640c440710010152040360078550346c01d9451440540940e00800c8071000160140b51580e02001c2456002014084040c0d010714020480920403248052885040c40c0414402020711003902d415040041241e825961003030180241e503080040140304050315840d600000c107409000303a40c00740c00c0c0e0058040156040b51112400d407405183c0220b001e900c200b0420408200201c10750340300d0a400c0b256440480d10310340c1c41d9145400c007600301da68011341035110a401f15520200800c074075a140410fa40c80c41d0104010711086560900c0040d000c03460864000000a00c0345500e03d034030181301302815050509404100c1d483c25404130b801036440d5924214402846002009078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 262624928 1250 262623678 262623707
    0x30801140f03072306030123030313121b080d030e0303060a0b0c011d030909061005070b280b01180302130b040b09100609080d0914060706140601 64
    0x25004000d1800841d654010718401c06101c0d4640072100308684c00310b1405030404a5004080341c2d200d5840b801560191602204c0b6600c00c803220b05d07611103c1c1d0401005480090154044a80b109494902400c450001c00c0c8011a5044003082d0140344440b080b1240102411041000385201060100042d04991203d04548a19030041c000c001c00340d9a100c60000980c0c0d0044c0031941c039080802d507524003604518880e002d900c54039620b007004685000024100c08502122840e05980764032041c0a5000c400c90740e5200026020051781d00414264400302d50820020502505103440000c0c02c1c5840000c0041445000ca40310080f0070855a0310200545a035410241e207400710501d9507000500e40740294484800094480c80c00016541e915800a41031040c054140d403200d150002c0741e101507560360300804003ca100c26401007202c074030000304c440c210a100d85860001c507042600002601c3e419801d6603910107420020500007a00c1d84c000c00036810400c0300b002045081c0200017400c680b02a0078174 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 262626178 1250 262624928 262624939
    0x6170613050309010e0102030c0a0b2e05011404031406010e0108030a020616020106050d0b013204020d0b030a050a1112030706050703020421150209030627010903080114 74
    0x300c002144002c001c46001c41c0d024240701c40c0c2030291000503401c5005000030140e081c041e60410400740601e03c4481407050b0b000c9003d1409500e0900c0d400760740100c480046920030808c0d11018416940500030007020683e2000c0c1c1503080030b55968a0128094604001450603002a801003041e017585210042c05060340e080658140035000f80c4c0255902d0b001000480003200078445041c401d4002e40c000c0c030103005c02401d850b6600c3c0385030410140702942880307507102101c2081500c810310080c8145110848a081d030740128129020030800001e034012844582d03030b041d82d0708404499564100310440d0f0451040c0c0150161004030b04241a646550044050042030f420004070000d081c080304465515600440010311510781c400c0031030003401281c02c0f6580d020364200001c0031441120b100009641e00c41d00841c48148282c0042005078020f101826402d684404d02050000c0c404030310022040300070170105103a200c621555142514100e0400790b002c2030160300140142440108400b000380d400307562 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 262627428 1250 262626178 262626211
    0xd020414060403240e1603020f0a080318040b090108010f060f0605090405090c0d03171e01030209150423090a2406090c0504060e040504080a0f02030d061706 69
    0x41c0c0580440746907600c0e9882c0c220b4042d0240908a04d41e000e9980c040308601200c196482140000c1d403820381c01e000580c40307003400c10907040300b0b441c0021440007903401d0341c0091800c1c400c0584030000c1c0a248403042c0381d8003580303840c40d501c0161902d000307a50081040c44c001041102c0c020745081e04445094001d002000f003805005e2100395004400c80300c24030300a0b100062503646030342c211030400c90b00400d803d070300c039002c041403d05242d842580001c201c01035003420b45054070340007600540427864042c0e00006a4a100040016117400d07030619030301c41031a00b1030300a40c105510010f012a0b00452603102d440311450024a1303502c0040644590040701c5100503d08540107444811001d90742030855403140c2c1c04903080301c05a1400e074002500400d018502440521a00c0c40d028001d5001030144900046030710b414007140b460701c1d01445000743d400403607041c641542c01c03200301c0c5e8401d82c080d118420f51000300090b49400c1d803d0721500d0000d10300c42c1894138998031249a0b840c1014406000e50000d81a44003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 262628678 1250 262627428 262627433
    0xb06040c08180304030501090b0106022b0e0f10080912070b06060a11030f03041505100603051b0d0c02061f0e15100305060f1009090f110d020414060403 67
    0x1d1165004801d0034009000700086041440c51882940c00013480b81d401c00038800c0c1009510800c0d02d050f10711130b4003a1022248085142102c410a843c48070010b2100040060b4031a809400b00c562a01000380800b100d1b40c04020103e10048000114800003917610410040344c500d0a121028040b85000c000c603241594a80303c2c1c400010b0017a03c000d100300700c00039002c40854050f0700719515011f440c4054a0300c03804003485141c49504119001d0701e402810604450030343e000c6100e058410011100b00e0328605081c00f004030001c00000340400c0c0350540110021003c02900f030054600402c1d040c3c4040744d17003001d81d600241440d8000c0d2841e110084a2110b082d00400c401880200b82d074400186e0644540e2181e0421041c2c01000f00000c2e0480e1404500021495264201512509060320b076110b1f03140d4500d0500c803410030284100000101d40d07410500420b034003500100343c0c0da0713111034022650000c50b030074030260765118030741c0400314690004040100700700e030741c202d11800302003114205d08061658 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 262629928 1250 262628678 262628687
    0x5041508060111150f130c120501060e06130c050408030f0d060b0307080c1c0e163f120c03030b0d0c180e030409060e0a02030106020d1202040b13030b06040c 69
    0x5c1e00000e407803095032001581d1403407158505801280c01c11143c6e0400c560385c2d244850415400a015039055003071100116070700b00041440c41c0a6000500015449003007801c40d50020603600782030008011080100042d2038504001400b402410b07000e03513a507140300e14a082c00c100e4605078019500781e9424010030404c4c40e040615583e1205580034513964908000c0c603034141340e4003400c2c00c0d01d82841c9400514080c4900002d0702c003c6075010304030301200c825140e0110208007841c4c2c00407000413180f501c002800034580c0407580c201c44140100c8020b580b024580d2082c0202c071b80b01408a0025080a0f0f82c4024550f15024544400d5815207101c0c074082605d440f03a00041c401c0b4040c541a42e06000480c00490341280e100400114001c41540c0d1500d4880a2040c00340406114140d06c2d581302c3c001064130740303d480c403c49049549a40040400840040003034821080102c4401103c070344c01c2c480091070040c0000146404034906902c0094503045141c051001d01002d00524083c5203080b00c110303a4103401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 262631178 1250 262629928 262629931
    0x1060b0301120807080706050a050a060b03070f0c0f081201060311070210050d06080102090f09060306060108130c0305031902030c0c01081902040b1218070b0a0504150806011115 78
    0xc102c501c60444400e410050030714407030301c4002868141300041c40c10900103a5400103001e1464004144070503240c01108100b40e40c1035000d0511130001c10004560346034026000c20300349000a0030300b40c1013003c545d19403074403051803006c0540e0f008038002a000b10700d00500302000e01600352410200002d010b1400410414024054000e00501c4807010904601d4015025100c48800d1814144440c0d0344800c0b006010390441103000d4003585144460b8002c6140202d45207224800c090700400355940c441004450102c17019201e0484044401078603404501d68019410240d03001b140115512040242c20250741c0c40310a2001c403c542003400071007031001d404940031042c054246081002501d403e0313201f42c00b213250764440c800828800600060840641400303404543c16a007a100e0103942c40f4600d10020708800c4109880c0f82c0c00c010340600041601c0f401a01c0c80c401c0e07074900182002d851700c0c10b80c0003481030001c5072000700d1480c1d41001159a0700201c0407689401f03490103014400c0c900d91103100910350 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 262632428 1250 262631178 262631189
    0x7020406050306071b1103030309070e060f06070b040201140f09310b010203130306150f05150f09130902030708070b120c09045009100e0d0201050901060b0301 70
    0x5c2185854248488802440e840800080680f43e07030303042038000155100714a100d90314000540000294032440d041c2c1c4800c0040d40060051031510030a903403800c081040051089040c009154062010841c081000e00806a15003150395640d0801000304624090070150a00d030201112040c46140407246032041d024540e660b8000c00d10301c2d08880181e0a43c0960250942c21031681500001400000c2d00702c20002d0089440c0c006215407140703085c00d8a9095800303020342004c1c2d49114075551580e4840181a80070000701041d0914052600051001d984030404038100c9460b0a8800c042d481c00b40502d40c0141051402009020300c0c0c032403801c91074040c0c05107100041c610100050610142442100c4c02c010008004001c82070090400815145190b480d102c10102684841e85000840e00b00f201c0d4003070800700c105da20b05254542280c00d01c0e003008196140c18041c3e8407034999001050700071840c0c0010188041c1102c200410760090031107c0050440b083e0341c2c10300e03030100290054401141d06440d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 262633678 1250 262632428 262632467
    0x6030d05070206030402150307230a020c06030405010917030604051311370f0605040803090402072a061205060a210b0709060905030109050d0503190f020702040605030607 75
    0x5e407603000140743c41001c20074018040c0400400c103c4516403005148171840c51800a4400f5907241110940560003610803220141e03200038154541854900b000e0750b805881103001041201007582c40420b246543c2841e604a4030012090112030318260058a0388907007003d4145142e68140d48030707001d080c0404441c0c82d004980b0400307141e00c24981408540e100b4039002841068503100e804501007001c0d140d110740c1101104051011601c94419001c440c102d4410000a40c180340c01182000000e6000e400c0486144803245881c6850304085c20001c4c03045003841d0340d19000b25242150203403500041c08000c04c01540380000300040c55844e040b0f1f04043c2c1d2074208031802e200b030312001c4003a034184000d0030280c100f00c004020401740ca0f0340301c1c030200182d52050352607105aa0b55401030500303842903640020647e407c43c140c1c1c0380c0218803c902450b400340c101c2c540c84a01180880070402100c00150541c5c034282d40020700c0000398101805050000c00b01a4001d00c040d00d05034030b0081c144200d6008200c801c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 262634928 1250 262633678 262633681
    0x504030c020910030209090706030b09090303070e0406090c030b0102060601090e160c1a06031501061b06060b040e2a0d0b010e04060e07110c01090b070606081504050606030d0507020603 81
    0x40fa41881c0c002079540588600c4a60130240c0025941e0074151183c040041d04084420007541800134035140a000b09074021410340e211100700340c0b1400f05207042c0c1604160744542c000f0320510740e8081c52203801c8a82d14001017100d0160002800c2580c000c20003810b01520500400030180790011451313100c1c4660156540f1200d001c0011200401c1a24000d840745904071600a81e000030303004d855000d0b035411000c44010840003129040d0704c2401344501808910500228145480b2594036003081c18461040011456110700001c0200d403c00d8000641c00f81d001400c118100380019089110501403007020301b4510b01d000c0055030103100c3d003020000c21a40b80e822510140c1d000c1c2221280d061002401484120b45504160500792000c0b100e040002c1d03440e414506414a02041d0303102c010b481030703595074141424852800f845500024040f102141e4840b4001008901808481407000048030007000354101418850715084015040b83d101390005039100242c0f503040421180403da05039070180c1c59 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 262636178 1250 262634928 262634941
    0x90512070b07081b041202060922141003060504021206010f0e090a081c020c0601140906010810050d0302070801020a02030403020a0f081b03010e010e03220302090109050405100204030303060906090504030c0209 92
    0x61f0b004607070025400480380d003609070b4482c000310b4941d500411a0381080103052f002c01c240b188000d9054840d820190400c600c1400802c040c1d410256006001408071401a40300c0300c59185012001d03806070492040000041c05090710f03500410340c0084401c8020185028980c40b00c08482c400c1d40040e081d6800c0078514209464459010b4a821812a038103a880a680d2007007154120409205483d205110b4500054901d600030320703601c1c5c000c02100b50b17111811402c1c0030601640c2041c1401c1a400c1d41301d02030f00083d28440900040c03071000b5082e406176031582d20750320612000411a82041c4802d01d03d0700001d110280d000030308074200406c019800d40707400d9901c4000c2030040850340f8a550555003444031f01e441e0144001b0082c00862003507010a1000640000707800507030f0216000003940445010010450051140c12030380e00304d0302038010351710100b50404160080342d02c540c1c01100826100d5904002c002c120384140d01c014035804100348041d01e02a50014081280e80d0402889001110b02241c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 262637428 1250 262636178 262636189
    0xe03040503071511150a0b04140f0703150321090303080c0a0507021008220201020c1201180b06010f0504060c0303090314040608090609030c0d03090512070b07081b041202 75
    0x6550044429140b4035417482c0170290341240111070421250381006040c0103981070038402c0300c0c7c2a10b050154001d0a40342c1c5148527085200151500c07003055218a80405004000354105000394441e40300c400080b07001c40e402c4042898011044802e0081955080010030b41000005a000444084c43c40e036500140d50241c4860050104c0a50031401c140282e0901c00d800600803070051610710f04442120b15070984d144003400d10240001d0040c4c1014413040e030075083c07404212004100400c0081410110316035180a005611001030b94008401000d005107560080003800b00a0041e24245180c01c2c140203020b04240b00e00880242015519821102418420009000300800c0340610f41e90303d956558009064035001c1d100f031041c50244001268800c000041107800301e0040102500c0e116146d408194000c2080080c165000d015501c4000c0d0011040c0b0300070032200d88182c07483c481506114000810144d0018401c184810b114558408003601e0002070354111a4140500c480b0444244040750 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 262638678 1250 262637428 262637447
    0x60e0604090c03050f06030706020307060504021f1d040603171303120c1704030507030b0a091e11010206010f05060c011b1e2607230901030e030405030715 68
    0x1500c5034507100700c19024603410340044d405800845881d1529860b1001050744606040c800d05015a100704070050004000e900061b901c10f00040c482086414407640823a00e40800460140c0080c40080840017401c4200407441c270100010358040016505540da4040313014460405a48a554045442040548100000b00103180d0000a1070750742c011700b02020b000d00d0112001216480ba00f284500c0c440b080b4102954100d0781c008000301000d5245440c0c0e4050700c20301400f000003c5440d00c0b0200042114038103581042e4031002d5021807401500d090103017088003025a0141103400074401004103800c01260360707055800c00ca89040c3e403032106028103801170807241090402c1c02010325116850b250443c615a540d100380d0404041c2c0c00b40294412504214811803046c18a04c400e6050010b14001500783c50f486052820280d850390005056003035281e104001c0714040741c50014070b100310b5507418091145030091110080d42401e0801d00003d86038440781c0540c52403000400c80700b84c0c490b07200f803c920 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 262639928 1250 262638678 262638689
    0x1e05010b09090c0d0e0d0924081e150103110a080403050a0201090209090f060c0c030307120b03010203190605060403030c0204240303051e0c0c010f2a02040b030c0604060e0604 77
    0x402880807406041901c403a80310320401b010903555000007030669901011400f0b00f40c100100804808210081510702c3d50f0b002e40a0f455480070400004c14150f04040300030b006a9007144501600b61441c40010180d1b2040740e00b03d05010028000001c02c1d075040011103410580c1418216105c0ca00c41d03008a0041140c05d02c0654040c46400500c061184003042d40b41031004c04130240c4001d90b5440900c203440303114001b0001021780c810070001c1c030180e1040c0391901c6258800000421010850f0b4006803c0e81c2007a507ca0b8008200c2a608a0b02d8076250311400c40104026075910741014a140c0380600700b00220755000c0e0142d502d440c3d1628501280161032110782e24080100d4129030340b40c0c1001405500245102c43c48074845800e800c01c41125042902e082284040c02040010b034000e00444085506400031030a110220018410301800d8101600c0002d041e03000520030f82243c0d00402080c5ca40003134085002ea08684e103850b95648441c011101038403807a0800355140b081c981d022400c1840f8681c000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 262641178 1250 262639928 262639931
    0x4031202041814011d09011112090709050112060504150203040b04050d0305010b0d1505090106050a02070e151e06030a02030106030c02060601020303160905131e05010b09090c0d 78
    0x40b803400c0525003015400c90304180100b01050802e400c1600b981c100f03002d109101905c00f000c5040c1c4816048103d03501480000010a24007010820903500703030011506241c910b140002000940314041040b030340200001c68040c0501c0d45040c49020120030381100c0907124603241c1c0005000e200b40607030210141501c20004550307c3c9058141001c4c0442d050390b08450f40d01984101640c81842801564143d070510003901d854481c0300c0704418001c02096665081c000c1851500040326034954030f1580c004c0c07005448442d5200400ba20007800d090550b000009040501c400b44503840030b0303040c403a81803114181c521104000129a14100c3c0c0310f0007296541c0c0c000000070030004c401081c0d4016504860407610141715041640c80d080e6165482200c10a006a106100080e001c030380303049030040d040e1594144400701d25115004948114410b144166882d5200c0b0000080301003141200401c42420020422695040102c003121900c030b4030046500c01c002c0140804c9295405170111681102007810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 262642428 1250 262641178 262641187
    0xd02090901051008010c08060f030a020a0b0d0e0f07060315030507060c1e02090a1808030408070c05060a0c08091302030f04030e18060d0c030f0507142704031202 71
    0x1040d001c1c01040310080d51914043e0000501e12605029a00340044507454481c0c1c2541d405041c0074410040c81d01c038580c540714107249107002d46c6803241d0500c0604a540701c0070f5039521188a581d0240c42201d2144819940529140d082d4400003042150a03540e0518021810114480b100c0c003a80041e904050844c6c0524030000611580017062030b8a0326210f01310f4212111110380c400c0030400e0b1321280117500020300c4400a8451546580108819607001400005c200041d440340c0310290022502141c0e400400035500e400d0203503ca10040040070210745061600750282c00050103403c0c4214010540840406c40e00e8065541a40c0402004001e40d8119224540343d503400c20340d0a016a0154040750024801604900309046240c06400007805911602c0d00d800e4180b0076848452401a607141c43c0b25607001c4002004074607111a528003070b05c0108102420040c0ca07a14a100c9415124400c0490028070101600701d444c404d0040c03522410207030b900356214242034403c24140402c140c01c4c54030004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 262643678 1250 262642428 262642441
    0x20c031e03041802190905210f030a0c0209150d030302070816050a0606060203040f0317070f0c031e0320010618090c0b16080c010e06150306091b010e0d0209 69
    0x1809041040450844052000703000c0c07405607242c46c500c0c003c0e03a400c0060042464200c4c00003150321108e100c0a03034220350b0703014448044e060841c0c102d4203205000400002030041035207084e28910350005469500d0200c0c20301c20f800002c061b411000c00040906070082202c906202e01c03642a11038004101e16400c980c08854030708551540403191003144c8a41c50700801050303ca10010540f010323100041d180c08400307415911405002c1c80301c3c001e18440c0403002c000c40d0000031746c2295a00e0002e841a10900009821441c04c02d0150402500c0c1800701d03000341d0342c060003082e07001c0c1602c291000361800c9d5400315008c0750121400b4242c03d07048513180801038440765114500d01d80c44001007038043d803030919409444010280c0f01c1c1c4620700444031400e00b036021050214010700e0043c05405510030002545032801d4500e50b0400c07404a8194403040c1d038035000300590303040a10046a06c80d5100000e051030342c4c100b02c0618101003401040b1341c104031120240e0302582e01c541070ba25101c25001032902e1058178054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 262644928 1250 262643678 262643681
    0x90a12030b031f0f05070f1803020a0b03101208190c050d051305040b0f15120405010603020f10092d08060105040c09030503090d06022b0c020c031e030418 68
    0x80f4004040300d840e00d01c92403d410410711a190007503c1940e80c40d00441030116003101d8071803a1625000c060340c007903040040103995940d030510041c83c5044240b0b841c1d140100281842c81e40342d50140308040b094005220000d001c1e44116580c2000007400c0903034640c180390003100d40c4e0350461401402841404c441072206900306d805003c1074150b40b5820410b807501c8005200c15604000381d034540011004400c40114588410800010824141c0c014104480ca00c032000c000b1070255000e86803079541d000140203505000c103071440c081e00d00740c8418296192a00004090500b14811902d4000c0040020f013104202102e0184c105000d81c0708440c07446131105d045a032160020310815119901c0c00004ca080c02c2c2c0108410002c4940000240d8104002082801405c40362a14110384140c2d0800c006250600801c54002c05d085e56450391008a40c2c44030b0016045a102c50b02c0c070307400d40d0300002c0216000c0d50000b40c2c058618140040324410701d1010401c651840c01250003070544158032194140322200107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 262646178 1250 262644928 262644973
    0x6020c0f060a0507020712020405070302090a030309060e10080f09010e030c070e0f010e0103080c070f121502030907230603090d0e0103020f03060405060d1e0b060306090a12030b03 79
    0x2c03141c2008161150542603070f0b100303428400c014408003680425000b61034168002da600c040300b42000751821100e5800540b04a805030000c40c0803992034a000d00003d40d1000400302c803583c042e0303009100320702d00100241c040b04004080d101c40103030100005242003029040016500030a004994540308101c5041303407501064025858041a0700001034072801c0c01d0045903040740c0b0368a0555840c2d03400c50b100d06980390710910244000d40300f13070140040d01038940c281130801041200c000d15407010003840c018070b8000700c030456184528014018080c450300c01207035580459010820300341011110003001035103e4501c0c08040e80c0200b0100402c81a9080803455501c1c581c5995200f000c90307504140113400305d0188039000160040d09000056490406502c00f54010000628590040c1110741d120324442d602d91200c09410406c2405003030800902e03260031038000c81e00310007800302c9180244007584d4604042c2c1c3d000d0190101c9402101c08503019a0002c1c030a48006000d8864100d003040c40c1c04142602c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 262647428 1250 262646178 262646191
    0xc0301020f040513200c0a020a0609060f1806120906110901171302010c050307020904081c060506071725020f0306042402120f0405011404030905090406020c0f06 71
    0x180c04c454841c07a8140d501c6000d48461382c0d4003d44900c10b114040c2c00b041ca40221700171000707510800c120310016a1b2014060300c0100350a966003ca8030303050400090070040260391920501c140d41e480e0b00070302249850b0007016100c030b034078000f80d240494481500241060300c90180c002e901e04410f614611407000002c210380c88080e21000c2c3c04d40801c01007680300280840325407202c03424003001ca800540c86420304910f1213016400312402e108150f0002480410140c6045512450001c5d1fa58a0891039440c00c00c80c2d540617480410100c0c2c5040e0203d802c510aa6100810041c1d00700c10080d0109000c1c412b030780d24200e0000140e50b0084c2007501c440040600f515007603200e20710503000036400d45400601540b00d81d90018041420b441480c1c03040e10b0003503e10b540e0190b5560244030a801070030070000aa44124203803e078036141ca041c141012030031100025005100e9024443c100404260041e0600c004c0ba4025500303c501542c44d410301c80300900070354907241060300440e1072104c422400020326501491 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 262648678 1250 262647428 262647439
    0x140a020a110607050403110a0306020a11011503080d0c0516050102040608011a07020f12010c020a02100201050c03150d0204020304080901030b031c12090f080304060608011a040209030c0301020f0405 87
    0x4801d41c4066a520411100a000594101720a1000408144003150000c0c0c014008021103a105d9490741c069030451418600095030201e814158030109005201e511001b440300c0d40000340c05d58441c0542c40c03141a62a12200391196801c9462038440c00840d4440c3d070300b0006040405a0703a1030418041d60051207141c00007000c0c0f00002c103841c6a01001241030b03e203555481c620705101c0c2c1c0d00b80003100c49102001581300040c2c9146880100c0c0070700542898095aa026140140c01c904c1080207803c0006401c80031a85407604000c01c4c0c180520860350001b49094036900102d04172400940e0300c1d9118600250401c3c008800d000230450101c0250006030800d0300c2c02e004502002d800e02d6500c040c8082d003e034003100844002d404d0706001e11540e5202440a20012480072000c0d1642d00038201600c0c5d04075443d10001080109010062058030060000c0c2c100038007244031041160322424a1104c609441030342e00003865070066400304100004400d01500030b6441e0415840c0620301504907104860040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 262649928 1250 262648678 262648697
    0x3131e1103011503020405070e040e10061403060714070503040b0a030f0b06040b07020d060903020f1219050f0705010c050d0b01050c0307060b06130b13080d0c02090703140a020a 78
    0x41c40c042c0106a10064541590101c880c6140c003000041c1802502c458103128081c000f01103592918003d0310407040b81e01c40140f20f100f041960720b5013220943c0c2c1c02001c906110000449107558003003007560304603040d403a0806a0a072503450301d4030b25206d9804002c2551000140009081501d130000d0880c89449071400c2007070403003480d001002d46001c0307121658010000c00082c4600640031024082e0b0b03e0000d4001940703440ca5540d1041101d904502c00d4016038003a0f0524245400c0401c01080400c224060712070a040003464004500c005544040080c400d0105a12845101040507036610a0f0800006d201c1e0b62154540544581c0c0305079000b403216400d10500304990350040c2c003140c0d4090100c000079480c1c43e03980c3d1103901c010028031050702c2e8070560410000641c55004030403072000d4075103204543c0d036030081c9200d0101900c01a500030700d5170b60405400f100031550041200c0709546d070140d88400e03060307440c104224010048081c80302c20580c0c2c04014002024000d80c0500740d070803465150301c01403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 262651178 1250 262649928 262649963
    0x30e010f080402012a021206040c0f030b07030c140d06170a05031209010b03030d0c0806090c030711011808040510030203101712030109090506070503130803131e 71
    0x1c542142c0c080d001c205a00f03080302201c4008a468100106035010f01001003020750300060900c030024040c0551580040c041c0300a20011185030f4000303040e1410a0760003145142e03101e0303110381e0380144100705055842204000060150440c00c10030004032840a42d648000156940281064010808007a1100c11002c0c8030050018041c2140d170380000095061140001014650303200040c403000142d52500d011084503281040580030b5640030340c001060410041c0001003c03071f0001056240700f000310100b4400f407050003200f244d41020291603c0085015041002d9000d404602040102c0350070301d0342c030340c414081810040c20641b00100c0d801c0201d090392803c11400da01007512500d446d68103e82e010400c1e91035803040c5508030840a415680041c0182030f0141d05600242c0c000b0391001d0301c900781001000024800303d60f1000d900e0400710b0841c01d00c0b00c804400d0022081000b0010740000012504000351580c0089071a03501c09866010048d40444000d104070603690121062410000034421 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 262652428 1250 262651178 262651187
    0x501092108071406180705210a141c0504030209130c090204031b031e0c0306020f09041503080301120606090f090213090f0b0a0b030601230d08031b0c0a030e010f 71
    0x442d804210007440c0c418101000c000344806a10b030010248c1002d01c00030b0800d54800c2c03000c0e0060f0b030700940c00e007101c030b03441d00d83c40c1400d0030a9402c0a00d030001062210ba4182600401910241c0340c040c0d5900c61340380e890204114080a4001d00a0038021406200107015002078000b0f200f680e01c00e04403149140845181102c00c90102c0c040100400c0c2101c50b40e0b4441100d08070b206d40194000c0841840c2e0550700c2d01c4e080107e07403224048a50700f040015400340c4070700b040d001e07844011a682c2401c04681d469505c03001014041030240f2443e5a03950440740d000c4c4503080e04954040c0c00c904a041241c20000340407040180300c58001207002d2610318200340c1c1d001c4628894110819000803e1100c088015076951103d020700030219940c05554051a40094a0820100b4044d0036000101144201c40400705a12015101d4015119810040d0040b0005039054141c0ea00001050142d40030700d000503003c1840d40c080d66524104510541c045503042c0356100c06102d0954100fa2111050000405000c0b00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 262653678 1250 262652428 262652461
    0x150d05060a091502031005150c0705040f0b130c0306051804082a10060b161103070305030d020316090311010807110d03020418060501092108071406 65
    0x18515049540000c55107909508100e240c50b00c1040340000b181c400080035000ca07001960300303c0078100c0e41001840a814508000000801880d4003582400403c0c44526500c002902600340507a0f280d80d0310034000021a0010302e4644001010704003402e50861441c0003d11800d218500080e04200d8005880d041c080c0c900741e8040c0c6500043c2405a03030700d0326202311580c0400305000c100d1400000c0c0e41e0794200e0102128030034600617000342c4507250070310401c0000e0760843e400c2030507006010400419403054000225507040d900c408660407030b200010000707041c0b84a6a04c0a0164000040d480740c06840c140d004601c248ca800d104001004c0076144215080c40c0c0c44e00000304058542080485150f0040c1c0e5040c0e4028000c0c948200c0b4099100051070074170001e4102035000c0303500810240040c0410501c1c2d000004281c0c10104800303850400024002c5003e031052400071740c0c404119181d8412800000d804040e045111195905664a009c0c0440703201110070005601440001c50601b00e02d0751f2103079 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 262654928 1250 262653678 262653683
    0x100b010e010909050408090a0e070210181b0305030c030a030f0902010507330c030b03060405031b0708030f040305060a0b060f0a0201021207020109051b01021b06071406150d 76
    0x8402c42810810b010000f00000b40040d80c5958050085207031642e0703032100f040060001d0404031481c9083c40f00005e443c2c23814000341500c940d424284600c840f500c1c50308a0301c1a00f50020306405030050303486078070340ba0340b95a80c10103070450000140300042d0080000007000201c0c826981040a024401101d6040300c054060090008804001a00c0480c0c0d221884294104222550200c0b150900031010880700015890a00d480d807100c0b544007604e071b0544209079451600307078064165031030f0694070713540c80c0c2c81540008400d8440040c01e644041c41d08020100c05403202c4811203507921944548409240c110384000c58040c030845001808103000350040800806000c7d008a00b00314405c000051a5000001c554045650070700c81e8403066490304d110103008240c0303a00006180c0d00389040880c06c0c040803000a40000740b140d028002c03280d074001030b40043c64050000340540c503410040058000d00c1000c40113071030b80550b0141c040d020400483e990340140000003d0115003c9401e090011084400c0b070b02 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 262656178 1250 262654928 262654937
    0x50d0603240c1b1a010e01050112110909070c06090c180e0601060e030f061302190b0906090f09041209080109021c050a020a0915050d0f0f2102100b010e01 68
    0x42203c64201850f90324814410b40c2c1681c4c04070800342200b007880e03109030f000b13180840308070004014558020f0111100c0740b451100500c9035841079290410607206a0701194025680d000c00600b03114410300c03050f6685580603d0038400b025140c20400e12440306805041540c00c105148803010000718415030101840c1c1e0001303011560f2812100355159000c54122a03058003404001040e001000d0114030700c40d42d410140b441d01d02449005000e828221a0301b00099000000c81c24014803603001c00380c43d94003104840250391400740f00e0104104c503100300003968000041c2010302c01048400c00301c03001160f49a5807684803480c3e0741c2003054241c1d0900352010b508141d00341214805940c541c480e4400ca24040c1707048620000c4140d0200301042d0a40e400045003d0741c490341c3c036081c404000e0b0840c000f07100c101e540185c4201661601092140000c0c802007915a24005150070804c20039031702c19034142401c0fa044910040c10b400a0f49404420504072a8646066481000b0f0342c00f40a00d01e0fa82c0d4810784d01c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 262657428 1250 262656178 262656197
    0x6110a08070807030e100e011b02030d0209030304090c0f022509021810050409050108071d1509100501031515050c210a0219051b01050d0603240c 64
    0x66030070340009064501010b80340c083c034039800c805c2040803091450146000080b188a0204424215000e04400401440078070402005640c0d00106540c44da60008100590341c1d043c41c400680380d88290360000d004e0368148001200d210b5040f048000d808140f83d002c1c0d81000b00702a142500341c0d851640b80d400c2822110400740180c07561503010b840c0d00308010036549079105102000841a01c003408010000510001e402d010281a600403140105121002003004e10306080a4035400054035284003940044440015030350440c00030b11001e205c001a00001c410300b094882d0000b481d00500540740400c1c00d10001c00c1d00b00b808250702c0303c101d611010030720791030020448085609a010349a40600d41c4a0f42c41002c1c641c956000b1000079400072031515541d545450ba00103810400c4404440d00c2440d055010b03400440c4005c10442030010007030704103100a481010050304d0314010104425107281c42c08a0100400100103100c40c07002c010462000300100d031510040003940c0b10f584041d40000c000c3d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 262658678 1250 262657428 262657441
    0x111061b09010309050f1f060510050f190509030705060304050c0906011116090e030a09050103020a200607080f04081206010e060a23040807050f0d1205040306110a08 73
    0x3000d45080001450082080070094440c2c034a41400300c020300c2c400ba04003981702002c49030b85030124110003100c014180700d000d1134140010400400c1c9119072060042c0080c0848110280c00c044031464269001d90304241090504020000d030441c8401d076010f031103068008078075881c2010903240302d640c1c41b0004105c111000d40503c0780300300d406000c442c188054030009600000d0300340420007468542c411680c2e4128949003038142502d803001c00038845a08104070003076040e9805000802504e20a0801603a20702d131400c41207682c10f10f4580d01004403106504581c0b2104030205601e40101042da541c002280c5a400004200030070503200100308210800c041660071401c400c225903c000141000b04859a500700841c031154800d01c80d031000102881c2840f0b501004500d82d10000e4140800e105040030705100d241582c0b5111401403510402c04844600340a50301c08610800300f030340c852170160340a440c807000a01580c0250000312003050a010800300d00c0c8240d00c040d40e4000126079580350045e161403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 262659928 1250 262658678 262658731
    0x30908090609060c0a060504051b090604050c04090606050705070f180509030d05040b102c0a0b0301020403050f0c09040206090d060b0928020a0512070c0b0a02030402011106 76
    0x90243e810580a001c4060105810b120040700d450240c84080781601d01072611500700f03000d109040012403260b41c0f001c0610749030030f540389503c01c405450004581d1100d841269603406194800c0c1c0308503003001c1010620320380c004040c00f1502e11480480c2d4007617845e010b080380d510801d4051281201ca2408ac032a048040c0d5400503a00500d40a0907a85043c1c260380880064802c2180c0545100030918144032134104520304107802882112010403005085205237010400d100c2c20b00714800103c0c2020900010441c0d20202030a10010021503440ea0307240380103a212843e274008210039001e211000b8099050208c1c0080c4a07d070300600701403a081800c02080303c034101e1200151480342c0e9424814440e901c414100c0e80c010b10820112000a4000305401550001d069a441c0d61850061082941054020003640c1000b20240c0c0c090f6034079510304408456803c410600030742a4401081030221441d0b6690055006034000ea84044010090b5150141c0d10902519540c00c0c80e0400907e40c3c0307603013400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 262661178 1250 262659928 262659937
    0x30f040f080c0613052e02070501060b04031428030c050a0c17100e0a0b1806040b0f0c09010815180903090108060d0b070c17130609060309080906 64
    0x80d55442d060460b90380c0c0c050300e400c82c1194140a03580d031085034001840381c01c101260103800c10070000101074080700c0910303404030b826904620036036802044040c2007010170341004000c3d000c60b03400729480b15603130708100200010000e0070b80d010b0700500c01c00c6958141e41003101000e1030401d08850300210100c5d0f4040307031118442c0030203494a020f02c680d0b89000600800c40b560081c40d10600c584210340c0f0380c4800d1420504840c030715510151902e0148442a08007082085101c6d40014040549503600e000d403141011010380024914041c2404100804c941e41030000c0c00f64084400c0e007440c56031109000185d920560a155000c12010000a2480c0420035039502e00d407030016006078621001b49182921408003030b10502c0440e000811843c1041d42d115000540c804030440c1c041101c100c0340c0d103442c00362550103044141082a00700383c050a20006025400760b46100c9400d01395503062880c40c0c0350606d05107000d01320001d80c0c426000682035100303028406a407500540943c8c42c04828004001c0303507601 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 262662428 1250 262661178 262661183
    0x14040e07061b0602180415140910050607050a050c060711060307050f0a1101060b07230f0106030c0e060609090a02030618041a010503030a1b14073803040605060102150c040905010b030f040f 83
    0x15940082f07115101c00e40a480340d5403048000300840340b03051030500e0801c21503100c0e041c081c800c24400100403441411030048420010b6456503900d866005c0e048a19104660f0310480c034140000d03410b441c480c0c1c05411101040880d90003002619100e48211000344582503000e0001d90091141010b528016290101e81d000c0003022035840192007000d66080d9442944191120a03180b030f400c00120070380001995100d41d08541080c070b024203100018441090103003a54440742d90100001e03089440c0d80c3c05a0180b4407900b20108014070f0185490002c07800000c200a43c0328050000001b5981000000d850700703241e464540c10141400180148103060110000303541c680b103188600840100240b1506003c0e0103090031110923425003043c0240d030f0042c00b20034156448003000030040481015410350f60415800349011600b502c031100100d00d801c040040798110b41c4900c1c028003000424000c001d004a54070324800b8082070382e94400d0402c01c2c1c0012605410b20150540c0050f0000300c0491100c654a407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 262663678 1250 262662428 262662451
    0x8030601081312020a05060c0a0c2901030c140316090e030d1104060809030a02100b0607050601060f0e0315010e1b040f14040e07061b06021804151409 66
    0x450a40714402c6542d00c0101c00f90144e0428a80d203001d210041c00099030140c20741c4465490210244002400c44860000160404103401443d04070584207900d03190040006074001961942c50b4140306c0d82c900809e1188460691441a10918500700070601d035604c000c00c00340015096145c9191030f0080e000017070440c040d5000402a88403183c0c05032090b0790746404019501500c407428240041c08044028010040580c418491136080f00d03800a0882c2c0310850050300070622800c000702050ba6400789040050050243d2000801c81907842101d4081d0030704c0681c1c404001c1d107140c10178562500741682d52203200c2640c00c00180f02c08210341c0022500701545064142441d041148001450340254100b6803105000d00402c1001c1c1c0c6401c1d41c441302ca610111010400350410103611640e892981c4181c206021000d611510028500001c0d0b1041d03a40106003995a00d202800c420020110031385040e00c41c525202c4d030984809090203507481a070301c01c88010f840d0703000144100107204000900760220701 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 262664928 1250 262663678 262663711
    0xc0806040506010302041205061501180312140706090203060109110d0e03090a080a15020a02030901030b030712030503011d101e051c020103051501022107020307030c0f050d0803060108 81
    0x42c80342c0001f8055150040016220a00f1301c9000c42c2c4041ca5090318141c104222901000744082c002040e00c01203031707031009142031150011441a240c0110004d4440c0004001051850030301250b60428030920348200c007070ba40c8507a2550811011500204c80540c4032807410300c10b280c0041400d621a02c0e0b545444400c99052009e641d00103071300300403643c00c105c0c00307600070394404400c10150850506107846420401c0d410010113400c02075403401000440c90415840e612943d1150f102032080d00301800c11400b41203002c868504016045030720070310460048507401803c26400d800010011380c01511030100350309295180003041e615003266040e00c070b20441d01c011030004166a800c61a8840c000e00f9020240103616140005002c80c3c400030b1010211924010448500d6179011030035004007070040e442c5030f20801124070035980a02807007200070341511401d1404018003091243d00411039005101615400347c0b58010f12444180c84070009125810070300c0402d10035030003030301d10580c85040b251000007007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 262666178 1250 262664928 262664939
    0x503221b0f080105010b0a0f180f080d0e041802090c0d0c090321020c010f050f043b0403110f013e03070c050708010501061d03010c080604050601030204 67
    0x2000d00039407100301a0801c44504100852007030054a0051405600082c181524240043c016101306003c0310208031990f20442203070090400d0400c0508000c0b00c01c0780405d500c0746640e80d0f1f502c510a89200209560f00070001861910340207c40c000c1601c02c0c1c51440c41001c542c00e00c20030b07240280494031842d5060000c2c0d003c500044c46440502005907948490040c6541000044040c44009510324080c0703406c031211000c1d4000404100da02c0080c039045120400510003150703280651000070a001400003030010701130846440000c406000100d40000c00705600c0300056151501d00004480d81c8226000140424010400e906c0d60241210030b0311030380c40d0303403194250854110800d00c40140f00700307a5198642090314000e020045850502804e642660300e00c0c901d1007800000d06030401c01210401000c01c000041c0710020042086e44002c0c40b03e96110b001c0a801500f00103207950030150308200a00441c0303014001c4c142904202d844d055076645400c0c09000150000810841c103040c1c0800c0300050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 262667428 1250 262666178 262666223
    0x20d060b131401030317040f0816060227010504060806090402060c100c030f0902030304030609060212100303080703060506030411010207080d05130504060b0307230304060e0607050322 81
    0x8001d2050207400c02da9604514002d44503500c5c03032615021703900740c1c04d0401c80014000c4100400058010a0b440e468081d006c0c100303061045e403000020301480c00420b210001d92030440d4000000304d400c211419800031030b8001121503003e18820107001440e07520210b245030400b2000560801d001070146072508a89145452400800c0000346040e00d64032404681401c0c3d0500c0344844580c04082e05006071000342e0000380d524000c4d0b0001130035036030382d45000c007081090b140d0494400d0079072881c00100520f070804000112030304031300c020350203d40120f0004518901c43e100c2e91043d514010030982c103646075501c42405040d603041b1801d0562140307410114000004000c05041131550340e88090799040c50706055552000305030b0003680110706014090098a244100381c82d4003080d40e242c409244041e8000b40c80d82c1003901c1d00101042c1d0340c000300380818484d054112509000301c0c2000c80c2c105480e9a60100c6540c8011580302c46d8465484401007010210081950290350040700307002c4165040784840003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 262668678 1250 262667428 262667441
    0x2030717032b0c05040f0608060d0204050405061902030f130501060f090c02011a031911090703091e02010f0c0804050306010b121302060409050705160305031012020d060b13 76
    0x1610b4214060004042165409141c403000b441c2e00d8643d080c1480c212105810750601c0c05860305101c0f4000c005a155203614001c52900c680040003070203d0f0905041254990509684401c1c610303440f60b0340c003040580c40b8000c49004904640540b14070750340c3d18501c01c8074450f90600440d45952500d40005003000c1e1a40910090014100d0004441c03102e8075019013100c00000c0c404a00d10035002d0009199074010401911251030080c071090310480510f850025041100c039942d80c0305040a041c070038903942c941d014014541c07003a1000d17040c1c665100e80654100e00c0c2088028002040010150340041c03040b0490304d1054413070b0320520b05150b1107400090800400b600011000c50000c682c2e46d04020300e40c3c141d40e400250700500000c1425003070300454803500c04c50040c040c0080c2c030707440480e03a00c0c1c3c440c40480d4803a9086505007440002286401491a8415141200365505c010b00125807003200042c01d000c0241e00802a036089201541c0d803c0c060182e031041e681d805040d0020202d1000c00600811 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 262669928 1250 262668678 262668727
    0x50604060305061f1e0306030b060402031308030c0d0e0c0d02060901020f07080c01031b02190201120f0614060a081603090807050304080105010b0421021306090501150c0203071703 79
    0xc2c103c1068130038240915401c00507542c0d0804d1f050420070008075540f24030300c940151041d500503075a036071140710715141e00c10040c80c010490200001001003200c0e00c43c000d0881e242d21000c041c8024031856031001d60f280180ca02d02940001e2602c000001071800d94000c0081324010b005076035803066150450745c203140c2160300c400300c644c10403425420250b0740f512036440e01d01c1018001280010100500950f54074000003c0d4090142c080205003d41e030045440080c85910030a091200540504000c00604085d109250640e9010039011040d4505682500c0070306141d540c1c1c0a4050b5a602485800103502c600000141a6036044020115458400920840d8007501c0116690381c40d040681d402c45105a10551011005020030f00c48010f112118035103050188825031900901800003500030180a600640c4292802c0000141140c2e10f801c198100c5010882d0301040c0060408c00752045044031070020341c140c010308004e0184011075400180b01301810b204490501c0801840c1814040500184 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 262671178 1250 262669928 262669937
    0xb0a090e01020c0c090106090e060613091505100f20030708120a1517070801050106020a1103011a090901020d021b0d022d0111161b050604060305061f 66
    0x814282d00c00c1102034680d150030b1740d0100301980352035001050740400307001d04400402c21130f000c04d56641d42c0105680172076020401c0c4144071036842c0c070181c0080c20035441c0d00705117100001c400180d074905074500798003505858840e40554036141104559644001842c12000c0d0100d00f0f1416100314200098a05107104049850762480b05507205609030700020441440b05050141e20032510aa0707904200403122904200c072810724101840d60b041a0690708103407e59031900c0e000285c2d1960010301d43e014580150002e01d006018102814283c4800803003010310010a03070b00c26001802e2000340aa48141e048000500345a07200404800740da11001c1e44040701101e400c2154221441803100070b412100e280000c003603068401350790800400c00c4088038138201c43c240d0401b2100c60303002c1d005a00f55410aa10441e5600804000743c4148800d203c410350300d4903c03151200d84540d60303a41011050761401800181460719080c0210b020b8100101202d802294450508a900c1c560744001c103600b52440c0c84 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 262672428 1250 262671178 262671187
    0x1a16050616090b040303092330010b030d0e0d0501050c1b0c21120c03070506010b0a050f09061204051506031b040c0e06040b0406120b01120b0a090e0102 67
    0x10300424030210b80d000000340320410401040001e07001001d203011220781d18004c0180008140324292108081030505070002c8914905c0d5552002e0030001e400f03001030b481c1c5000c40c881e440d03008503400ca031000e039181500b5034850030a1110450240e070401c181c2d01c200805030391740202c856440030f0030b450040d2800b05a90710302040c29142c3d010031101020340030b00404010101034130654001140004a520903403085524040e92948055051001c1b800c01c2c3c081004250303540d4426180d041d9240d105540c240d40380d00480300046040110170044171110001551040d007060030b40c00f00d002e015880401d406500202c10450344184007024001a442203016002811842c11480104049520002c0840d4030030b8021802000c04807040f07652046105009135400900100c202c00140c44140c40d244202d54483c8001c280021603952002c0100191141965580b100e0144400d44c10141c400c20003195000c40c5240301c0c5640301c0040c40e4080b080c186402041462802c0d03654003040100e800181100b6a41d03500000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 262673678 1250 262672428 262672471
    0x91b0815090c01030504080f070807050c0906062b0906020c0d0503010617040c080a080703030b0a0302010507060f1b1206140f010c030e06120415061a160506 69
    0x45044101040440312a0074a4070901d01ca480d072002c4080d40381455503139070125052058103400c0da19400711010046a4a4826040c00c22950f00f000c203080702c00c0d2042c100315100c1c60070601d8401740500009400d45091180c84020000301d030000300c010700142400b440616200420502911318514002c001c0160b94110398541c85040c07000044402d4107019007000104a0310386e000d902c481307245d0401400200c681d02c552030300b081206615071103500031740306014101c000e0080d000300600c04070748030f61403c0200084801c184010032100c0d1101a01003107050040d4400b28489800010724000c5840e00042d190f03034884042401030244400c0e40300041d0003048400c401002a1007188050013400700c81000d01d200c54800240030302001080c042c104481744231032800b007601807090280482d1000723000907200c01c4c407456504c2c681002103400769205d015464941e201d402c00c511800058030744a40c03010405490724480f1032000c1d885582c01d001415070008007a40881e8060083e24040d080742c207802891501080b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 262674928 1250 262673678 262673683
    0x120708060112050105010e01050d1b030203160206091e010b03060702060108010f1118030304030f050d0909050f010317070204050c030a1506020c130f0207050616031a06030901091b08 80
    0x2400d080e10349600c3c000050226070307008441c07000100000d10340165600000c3d0f110078050002c0d14021080000220158041c00b038040d00554818240c071000e54013988942c480403030b40c800c41070341c6507446a08940600700d0182e001d17504085480c003481700045003407010380021916100d0112081c0c0b005800210050114074400e0007040d1240c2c40f405800c6c02040360141c0b940d00688249500703803c103c1c4010f003030910300d52003d005560084d50881d12415009186081c01d035126804821480d000401c0000c0c0851a1082c601c5114082c10032611600b1641e801c59403085009110000b81012500381800002c00580e40c034054984241542240749889044c05079880c01510318680319559150540101408980c0d4001003200451004032010819100000c00c448010f01e5030742c011410680c0001040d00074040001a2140150b03800342040000c4440c00c00100c044911004841400380a4628058180e2030090065500980100000203121003e913071100500003107590009038085504008200800c400d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 262676178 1250 262674928 262674947
    0x17031e01050d0302060f041a0a0b15180d0204060503030c0f0c0307151d040c020a050705060315090402030c040501031a07090b040b071103240631021207080601 70
    0x81c1d5454101c241542c0e0013075111200140103495030b03192080007070240700c5506440ca0f1114403000c4c80502c2e50030481006009404009c2c15680074140000200245100f0041154010461040741c50a070329000b00c00c002c3e0b0b00908520580e40a921004003144a9400784010311000d4031003002131444000035080c0f00d00f44104080b4043c401e800c4048100305030040d010f0848180002880c0c812551040500c404040f038a010303040d035810030b26001840101c55000031717031140300c0e5020744211982d80303540b03508202d500c0c0300840e5100381e41007883d100042d05050120807541c0080c8000c1c260740390a8500e40120302201c0d000d030310960701070b5203c10158503c80f0351418400d0308513000c1c1c84c0400360281400c001c00da440c0305510581141e2140007135080d0078000482c0200170300c40d00040c01c1c4d40c01e80c0060307002038903460b0b0882940c8524a01c90740204005151652121180005440001207134203040001c0344a040340c040b03d01704a803602040f0032400b000c0c000c51040c2c0300d10120b4568040d641046000181200b05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 262677428 1250 262676178 262676189
    0x605010f091a0d0201050a020106180204060215040203481305070c020f0f03010615090602191b080106030f060c0305040302071509080f010e12030c030105010c17031e01 74
    0xd4201c1c001c01501c40f61410301800d03030207081055986406070401c034010619503100d410720440741c1050b0f0082c00c0e40c42d001402107410ba03500702d62100700640148070034a002034400940c554001800c01d0b101540c141c24040c0c81c10f624a084001d40b8801d911109400c080910315582898044c90b040300c42460301420800c91b4004005080065107000031000d0328613042440068410740b0380c00f8003550241e88200507090f8a0a014000b407004036034030840890380d4500305202038041500d43c034011850f580b00040304503a075040c7d040020b803516441d4032054240501e04e040313060b0070012400e011070201800d00540000714400c00401d41d0380884c5040190840d2000400751080504041c00c0c0004240d000401e40d080e10082c1d0050000c6003510401580d40075510741c8000300310f015080800801a8066202e072018040d22000d803100410401e039a40128401106d001042140520052026520404d4850401e520810100d0003281d403c20702000160000c86c0c0105207050400d4422244450341600c0324010b22 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 262678678 1250 262677428 262677461
    0x20a0602060c09040b0a030602160606050d05150621060403022a010e04020c0d0305090c0a150509010507021e040b04020406020706031503060603080a1701050a090e01090605010f09 79
    0x82500440e20b07540300d00d0191900c10ba80320400d102c0303182c1c0c0d4908501c0080d58401c2c8215520841d4007500c1c41c0305080440c065803054605000007450303007081c1106099407030b44907000d440b184842899100400502400351500203a046007035186807060002c1140c024242000108010314091900901e450440d612a08800c50083e80000d01e055041a6181c50190300342020041543e410001c58000d004238850b960461141d02404a000b0b41c1540c0928083c0c50440103541c0c00181d00400d008200401d4407a10f8510100000d2803a049842040070f07001101051501910307113074940d00054402000c004901c8072000c00101880c3c0185800e100d107411a06081c1d805504080c80e1440c01303501e0719060302c40d160503d9110b41b01000c0d003030060b803a80343c042c540c0a0002c000c41501c0303080c4603e4076084641c4900100300c441ca00d2100d03a0a61258660496400510703a105c460304040c8404040c107609003110450f90b4031941940c00254079030055501030302120504000040c5030084d1103068403c080c0315081c150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 262679928 1250 262678678 262678681
    0x503031803040312260c0405010e06090603160e1314090a020108010b070303020f12040302100501050d0311010e0607030f0b06130603200a0f08070806090118021c0603020a060206 78
    0x2502513129044010300743c100030080314070140c1d4140740aa00b0313507080118030503041c0030803030085c030024054416100300ba03845100c006100000c0c418548180300100380d000c0800d000291001c40c0c12400b185c1d2594040c54001a010002c0d000311300d1846801028400301c680b60614207011110841c41c0350b0f0302000c0540180a0280c8030f40000c3c19024040c05030b003164120014094040c0360081d012100b64001606070299610305c80021100202000d86003140103025045404038405c000c0d0103030302d060300c81c000c09000148109907400c2c0ea00c80000c040e071081c103540700d100e81400c0d89402e0110131710a401d07075107000c907a1307011040d4150200ea5120070182d100780780070311004120032901c2c2e0517003050312454140000c0d1164440581c0910003000b640455030198001001401c2a038072040300c030f0345500e0580b10030149443c0c60f0026038001504845c669040102c03640100000d168681c11151144c2851b50014a0485082d40c908159000c40710000b9030380703486140030030846c10128803141c010055440903025a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 262681178 1250 262679928 262679933
    0xe090c0304230111040b040602010b06040b030a0c200c122407021c0c02040b0a120b04080d0e0c0a09111903061206090510050c090d140a05030318030403 67
    0xb101e8031422800315403550500d1200c8410302580034004512107021300702c1e2507603912622a803056125010b050010750a00b0300f6040c440c02e0030419602550601c58503d800c541e074400f042801008021528020440100d0108034552400100701d00040c80c8103002d802ca1014820030b00c2002035440100314100c0d88044190a10215500d5140a124090488045c8035845100e02249043e6040f0703081d800e50024210701c80125504040b45200061003a5400e00001501c4410003904500c0780c07140c00303c6000f903111280e000400841c025940248680d0760b290401c00c5aa8141c0212074005000446540c070000d00500c1c60300c0c2180d039034402480c041d0814041c11004520251440c090542c2805010b03111000d58040140a6000000a8204440c2d16107410916003005009442d0541069803d40125980d00ea9170301094010b8038803071303180c002e8280e140402007411300031900202031007511001207c02220b00303921000e1001c1d001450040c0b00030361300d0741402084000c411200a9488505a100f00000c100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 262682428 1250 262681178 262681193
    0x121c050604062d06021c0c05070510080703050112030f08040c0b031014120c130e1f0b030601050906060d1803030e06010f050904060504060e0a150e011103060409030c0f030e090c0304 80
    0x28806d40303004101203000389841e51400321160000350740311948180c500c12030740e400380074140703c0c58266900307124903681c038081030b10046055440a0001248024504550345c00350301c081790828403500c03607400c50990341c108015554005440c0656180c10000341000984568103551092240840c0c01c10b140180800d0341aa6407038981460f1801108544412801958940d001b01c2e01a4490300642d0300b0450301c0143d45030080030720042074a81c0b515102190509050014509050300c00286c140109501c80c0010081c01f0340003001d03144000e940b5407941c00c40d44250400c01c85140c0f4030a07100800da07150265855410008160414a9042240081000a07586004c001d40d0030681007103000074141c849051100290040a032000c61511031410711608100040b42080200901c224041000c84800c291842c2a00c001605031762030000c080c400f0824034030701540a03462152090522001c4228190744000040000c0b000a8010444100382c5104506007000b801d5070110110300198590314042d600c405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 262683678 1250 262682428 262682473
    0x300e06030f1305060a0504020109120b071b060212011a0703020607080a020403320106050d021203070510060f090501060f11010605061b121c050604062d0602 69
    0x444201c155000c1064525491002e01c420780c2c00034280c40040c42d004a02401a081c155022400500031400000b960300007440d40503c1036a2007540f040594461840c12558000e0038241c20440507200e540c0d040010306075100070715500110307034000c0480750b15003601d00c0404505080401500c600405c50440040d501084103a40039401d4103114103161a00340740310000b030045130001801c20740c2521020356074401110703e203510f0520742803000d00740307100b4038540c2820780300180309041e000546001d03400018030305070035005000003166003140e08012058980d00d103003402e1510103000b81c030b554980500c40316610540748006841c0400d4203008a51400348000d010b1460b814100040112058003c000f00c0002e4100d84028000100325035100c0c141248040340702e01e1003d404014510681600c041c5445070503040e644071880d0f00d0384031202002035203c10707009010300500c8260b000d640d600340401c0600b882c8001840c0c640c0c0503030f040400d260f122a01341c500c15500b03401620035035003c200040424a02080b001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 262684928 1250 262683678 262683691
    0x71e18080a1a10030f03020606040b01111e1c0c171306030209370e0601050403240606210b0a0513090f1b0f0302030304140d300e0603 59
    0x102030581d540783c11480164a07940005002d48610200700c414150f00140321802010211030421003002800f006540080b400a4108000e4021036454031b07600522400c0c81c1400041c60080c5c861075544070040d9815100c030100c484000c00e06110a1308203000c0c4a180d85848600c141c5e405610f42043d04801c01000d43c0b49200d00000c054001076690084c1c0c40b107d11041d40f038110103072500c0c00e07100c1e4445551500c92020300c0f041503401407000d00040301d2000c4107136180100e40603151140f03003906540381d000031007040e503034207803040c200e105448089060305104030802407071699140c659076081035140d2448400d00700321351300b081403c1488500584d0303141900070b400c8541c1200e50b200c01500c5c24801c80301800c00000d01408801084210300c0500c4181c4036403114466004844402058490064070038150711808045e4041d4414041404040d000c04c0926a0b082e40c0280050361002a9540b0521b001c4800b05492200100c4030200342e14064600c0ca00040080107418280c04050982d004208280001402c1f03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 262686178 1250 262684928 262684973
    0xa32010e150a0905010f0f0b030c0a03030e12160509090309030c061804020301030f050106051e0402090a0b0c0a03030b0105040501020a122609060c0f07030305071e18080a 75
    0x4501c546002d940400d18040d80000280400102e491001000b041c08010701740e030181c00c0103907440c412325001c5000d8414460003408000e401b42940c4003190295407202400c0e0300821070301c1c00112100300401480c5039502c8212020b010550a00301400740c0c1030b101a101c071031680d2040c0225411a9004159036040c000241c80c65501d800616040e0401e503a4201c903034070b80061000002106010b111406c500c00f05014900902c03090383d881c800c1c0014040d03041c5001e5003001840c00c1c004e078285016001441441c400505402a190320303400821071641c804070700e0242a0b8012105082019018000e50006400034280765040c07518081c0007039120204d80f0302c0184542d002400e0391000f14002da0000ba0b42180652900c2d03c940591101607002e07140c140c5050b540c520902001407142880c400c12905011103014216040828540d03007500030341400351500c0180000d040381806081ea080000303c0c03188840e80da85c003007141121183ea034070100342500004e5a50300941c516001007200c1100c05e50201010648 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 262687428 1250 262686178 262686181
    0x609041101120c0e0a0b07020603010902030c04050a0b0a0f02060106020706030509212203080906130302060c010c0305010f050a03080c030d0609090506060a081009050a32010e15 78
    0x4030b500c00740c0000d01c002c40c1c9203480c1615031110740c000c01080405200359242d2071075070346034098500b0074040c0d034030020351010042005002115064018503009003224400c54105500c40000903010209900482c201040c00305010231200d601074098491007481340044c1000e541403020094507001140180341c149616003010a25000040040c0d00940c0d208400301c00f100c844500c00568603900c644042c62100343d40f81d064400300016107415204899004860034a018040c006014445d00284041134600144c84800030240e01c076800100071050164000003040006800043c0484006820002d1000321700401800b8640300c402181003a04c4c3c0000c00703261a03120900d01e0500c0c1d0310466030050a4242013900c00580c20786d650b0415410303140304000f41ca40c150388100501a09000a202d10346241d48290119180c0a2140d0b0045140d54050740594802500603210b070010801040c800c562171440510420701c9840c10307040b001d49050345540080c000e42c8000b44910741c0d1100320f8021030248801040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 262688678 1250 262687428 262687463
    0x801140a030203150f180303011202010e13061a09030a030309021504090f110a0207050f0103090c0b090901060206071d060c010f0b0f0a050312030408120a0c0f08060904 74
    0x800c04001598000d0444041020105558122410503030700790f500e1400d101c02080034142a20b00b80c0043c40c80b00300040d4110381c03038016041c0541e068500142d050040c2c42c0ca010f286030325441c0c000210030140210105095140219010081040e10400160b00c24103116100780e07603a01003500c03841e00d6014500406d11450900020b403042c00031000d20b900d2070400060000c1c01901640ac0142d220381030981c1000660341e0004400818400c40e208800160080e9070144250310303101c56441036280041c0f500107000706195840607000c20040d00311009270711002c0f42103a60741c5464240e55026000910151035a0b041414028100d4088050001794002c06250019031946404c8191607840d40704d000248602c4413607550880051800c0010b01d030041c00c4402c9100307160300f440060101210400303401041004407551b51803056400140c812607491b041001411400c6007111203580c01072070468000943c0350108040505414025404c00050115403420080503a582d007030b5580e442078001c0f072160362442004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 262689928 1250 262688678 262688689
    0x20906031504050a05060f04080a0f0908010609020c0d0e060f0a0509060d0c033c09050109080c06060f1302091206090a0302060f22063c0c080114 64
    0x110301c44400c0e000580304100c103008000031030050840c026819a280c90b1900c0c659260450310031a0040d10030305081000362149485142440310f0340c0784910305500c0d8543c0b40d40c2500e080d58469489106595004106a1040d0500b4032402401802d9402c1a103401d200b1000407800ea4082d6071a0460003a001180c0d08480502036001c6941e00000241040d0f030700c5010301654401040d01c1940f06c80002e141240400c6031040310f41c0d018200caa0307003080031201003800b200d081c2004031040340c00c1c0025644958210000030424018141903a105141c015201c0038558440c5161050080c0401d1040070b6180c550111501d07200d020a030107900918025a980317480402150120400500c0c1c42c50902c82c00c82000601040441c0e0200c841d07129a0945103a0b48401580101c3c8250560b0b841e030740d41c00000c1c211550b04011503055004a07129034004290541c01d90382c0d014a40600c031601a541c400e48003030a40c0440b00707003030300c01c20030b24140c80d010444840701c01d4004012400500401d5045158404c2c000e400d80c1d04d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 262691178 1250 262689928 262689943
    0x108070618030f03050408010c0c030206133027030b0a021e0a1103030408040608190c0513051e060a0918060e0f040b061311120118090f02090603 64
    0x310350f0b00340700d40042c41c00900a9200d48110700907035103005441924503108904100394035030103a000381125101c01d80346980880201d50200c0d00c004100e5142d49442c0701000c2c1d80140c001510848115507a001b0001524045001c1e0713a50303005801294006038420071444030360041e250800004007140e80c407407481c1e0001b4441c0025030641104841803a11001c1121402045009065901c0b800110380c01c4040b550790740000d460041400b10700b0322081c08054171542c8029403240414041032040c00071851000c040350100603481e4009140000e6156041c1c060b40f081900500043e00e034008461801680e03850010700b00b805a500ca41c000080c80c514080c807420083c4003900f8892403111030740b8418000b5100920300e038814100c80215041c0050800c01d000c0c41824869600700107484006d95440040080c41022031256a000554030640d076400595141d01600762502d1200c00c0701034950621844000500000c01441c000c1801e0105210001e00d140010000255050b1000c00b03c540b92100002d0405c1c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 262692428 1250 262691178 262691183
    0x619090903051215010e10120207170a050307020607140a08151201091a0105090f090a15050f09071a0d090b040f0b01150504141311040815010807061803 67
    0x4010280580f142d10139408088038542601c0c0e04498600d1071052200c40c0002501d42d5010860005031201c0184183c1c009140c0344d48a2203c09a5420302441c01c05403941021101c00001140841084811070301003001c681c01007c18104441c1021820000151500c517142d08042007000c2d410103c1c61510b1500d5115101750300c02084050b0381a0b111121500a05404c4001d584d02c3d112594240e08441002d09254103a440203008100c20380d440c0e003003003410458044c08000b29031045409140100381d5200821804100da50f01c00f10f04c90074404e482004004018204041e81d40100b00d080001c003000d401d00c02c00c18804050419110040d001c9818002c1048110281050405030304103c100034401c02c42205491007100448200c0c0d884141400c038500d1030000d11000f181c2d04010074410340340e08600c492a41c0c0380c0201140b240c4dd0001c000e090507200020032029a526010400b8005100e0a02070801300441010045042e9032401d162180c0c3c54941d40b043e041802040001c00340309039048400080a5074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 262693678 1250 262692428 262692457
    0xa0e130219090c0305010510050405150909040c03060f050c1602130e0309031e06010608061c0c0503011a09041205040b0a0906120e1f06090f020c06061909090305 71
    0x81d902c496600282c51203074990000a880c4c02d00209071031521029885c40d41200c3c3d541c0908260920f410300c00a074103284100d41c0c07a21000d0200c0f8805a4038440024800d501c00e0614030301c018554a000c0007a6035603000482502030800c400c02c0a01c510b4401510070380d10a0000760402c614490020490030014061a020500c0c106200c107c010100040100300d00d0500b03030101c0da10301c0440c070801c003921026015002031580103807004000884c8a00c0324141c00c044010212000100350294051040d0110402200e140700e07a54403c00140c1340030b10400100700e1524201d2641601d8a00029060384002040180448403e455100e03884c1e00c1507041e907014104200a00d42e851503240f43c05000b0381d101d0700c24000040e4034240d280b0782501c0580101110f15100000422026018442c0e03130071310000c103031041c0f80800c3d0740c4c1304001400011402405440500a500141c0d101c01001400303090140c01080180500345401042c26404030a00081003254180c0d41d0020f0007184a180c2241d161244002c03088152 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 262694928 1250 262693678 262693729
    0xb1515030901090b010611061b2719031a04110a12020306010518060d0204020d0906050415021306110109022106070f020d030b030316150b0a0e1302 65
    0x1032415031111401d04d0040860007080d0307984003011140003c0b480038052880e0007a00c0411050800303040d0100102e103041c4c0060b0300349802210444405003014200445044042d031018845040c60039503203407198040400c54101ca4119101c2410080f14014040c00b148000400102800520381441134180c1e0300900050201e0345d6581002e04000d49104103a120313004841c000503a41c9880c1110f03800038130448a8048050340e070113042161500d814001a44c10503000c1142c10590b282038031070594010320841000035642490b04003021030304071002002d2a40b034070401000041d01c0700200d200d81201c00610b031200d650341c1c1811001e8050024404020b400501003600c08881c1e6815040c85001014504101c5e022641c0b00b42d000c90b00d02d022141e0f00005a0410685504568400d41090400400c058212860b090425403a020081c04142c8140c075805201d00700000421070078040c80c01d030540110f0381d52510908020032110002d902801244143c0609569541103485490020002c400d031000c0702c5101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 262696178 1250 262694928 262694941
    0x1306050415030b060904021e0f130c020715051914070c0302040f0614150c330403080a05041506060206060316030807021908030d0603031b0b151503 65
    0x700030300380000c03a09202150000f42c1c1c241000e188045c440d40d00240001410360b288103c00c404842104500703a004410741a20b40d0350740c0c0b0307609965580301c005044000742d4600c181c0402410008580c20040e0b5089080749060902d03507106082e0349080c1200140a00303442c80140007039a111000001542044a01091280c01e102040b407554044078000d03101408689003c0642c001110309034050442c1c0700e1421110b005141c100300780114800b00840003003078502907064400710300c3d15201d9240601d209402c0060003000064100c140f202e166090410138505040c01c0c3d8000d070111100500221440c1e69078000141400110039002065146945040041c5a2104e1009454030400c50340a07019108110042c03070962200b04034002101e80003035010b420002a40d080000488070920802c0003000c03000004150400b0602c000c0c000e2155800e4000b1302c1301d00d1480c019100c0308500d00d0400c08007804040d054080707883d038561603034094400e484000c020050390000402c4005d0180382c40c00c0c042c2020081004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 262697428 1250 262696178 262696211
    0x602031606020a1b05060403123e0309070618031104050a180c0e010b1e28050c07090203060102100b011407031211090d031b020d06050f060306060f13060504 69
    0x340d8029594101c1c00510382d10f13002d00380c07110300c4900080d01c40b001c0b11060203146540180104601c1c012b10403003540541107501030840c1c0058841004640195504202954120310707950080161120410415803441d1104190055850a10b42c021615040011005145580410000392030003105a0001000f4104404040d2075805401400800c074000403c10700d0949090710030410259141301c0002c40410043c4250360042c580342c80906000f51841c0e01e401c0c000b4880c903c0c5141c0300b980d503152500ca803940e1b020301c1c00c44e19602000c0c00764810414400540d038040780c0d1140000800c40c0103d44c400b54403004072000c003611400c505113070101240c80800c241d8030194030020051380034418403201e480b43d03481d00c2ca14414401402d6014104140307100000340a5030010380c0040c10110b4800908000ea00851201410704000b250503907503074020800e040c200c0b0303c10544c002c6c40650041140b0300c2e2000214400d040e101c0081c1e48520901c1181100710341d4150818000350002070814003c48480c080070300c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 262698678 1250 262697428 262697431
    0x1504080903060601090807030f08040b03090319080112030f020a0b07030b032a011214070c02031507050d15080d0c1203020909010b07051905160602031606020a1b0506 73
    0x600c00d01402e0089041e66108401c05800d88041d5009440c195141d603680403105200114200ca01c2d1b0300c02d00001a0910841020318491302608002d1983d50502490071509807280c8220403050000c980d005102494040302d0650915505044c07441c000d03511160164a0b003ca0200c000340343e05800c0041080320344d41500100c00105094080b40d04a034032a1400302d40e031000e9400c100d02d040039010b081c8800c9621510a15030342d0940c1a4000490111340c844002c0035840c11a141d402081c07503c0508000c5040400007001c01c410340d494074000c1c03424000c8000b0080c1c850601c0d0380c1c2d0055190740ca03c44207514401e1028000700b400d641280d4554560080107410300c40c002a054548000420200710310764081d000300c0340344060050150140e40e0030421b0801c92034026210a5a03039114022441c0b01502480c44032140c6540248004d004009518421b18100360264104104541050141c5210a40c203d44481d0000391320607801350300c58080742001c030b840c1e00101c0380b150f0108410509440c2400340115025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 262699928 1250 262698678 262698697
    0x1605130504120309020105041707050901051806010f030213030b0f010b0319020a1b06060e071112030411030d050403150207031b060b1215011203050a11150408 70
    0xa124200050005400c942040707801801c1c00d0b6020b0320710000c03940b095110000441c4141045c50800f0385070070003e50b1405c0d01c1c00e1800226403001c20180101d01d4103081c528010320080b11080c0384044030780c050a00d8814050000c034180040c0107040e503030050107a016105c03812031410415604585d01d081c102050038003590841207007a5000300110301d40700d071503048a210f1000112141c0c1e4024042202d41c00a510201d1544204040c80402c00341204107400c5114070a40110b001248290505c11020303c121405010002440328002d41804202004070307130584910700602c84291695114200041040c030410200ca500d0300500d02d41018098005010b001541d00072041812500180c47c005401c9220307001010b000300c0c041103030400c3c042e0188030401440c2c610910020425041c060081140c001664190703a0054024541e2003202484000001380104804518240d100c2d0094130301032702c24450603000c0800c020041100c02e0091400304401d0086402c00f0214850350300d4141829400ca80001500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 262701178 1250 262699928 262699939
    0x60e2e0306082413020d08070303021b0a02010e01030510140d0c0b0c010506040510050904170a031a09040f0b1302090403030608010510060906051b030406020706170c04060305040809031605 83
    0x8544040c0100c0400c000c04c0c0c1d800b41c4080e803441515110050160410b107421000c00d502040381c6104020015012804c9108900041038074040610001d42503aa8185003981010724010030802011031700e040354401c4070881c100e000c03810042817011407001c0120700710103054012013550026a4102050042200310f800c100200b219490346810001600e900352a100c0b01c09454100621161030300011080c1c0040c0b051161001d07054000e440c8000b0b0742c12444000000c640d40303030b01200d41c1402aa152100c16442284c96024130320381550341041c5c64403105c801410400c6a43c000ad80c00c00c0c601003101c2005500100107034494035240c94010054040c1380509551542020b011071041e40c2c00007919001c0e02d01076107500281909000301240e40e81c101003903141000741c4164501030f102006000820181800b83c1c05000c595080410160200031200541d041d881100b8040101d1460b000701030340c003034400701e10b004a000d44030f038100700170f860242042c0e00358540140c0c1400014046000349007012100181d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 262702428 1250 262701178 262701181
    0x408030405210d031e090506010f061707050f0f0304150609020304020f0f1507060f11042111090a140105010212180a080601060306060e2e03060824 65
    0x2500d03841c24002802c900340341d440200107414141c00f0b500400300e2101841031114219049021160035240d007084291541c1d0841001880800c445811241c043d24060410208003c0c00c0c070001510940c2c001c00032801c100002c1401192404458100e1748485070882036151681458100b40c206d0f244941d003901c0e4080c0c940840010050701500a49200719001404a041100250144025150f400c103840341c1c4190722000000030302c800b0300040c081c1180151400905003201204400c2181d034143c0c0c080c0d1652000340030800852888800071040d01507031100800c4010128540f95180b89003031102554030200800412582d40a03641c00041c0c00000d5008099059981c0c60059840300d110802464030083c0821044a100204201102c007044002e883c05089590380c001041c10300c5420380200c40040e0b2103800802020750b02c90040203110300201c0d002c0084024460b0404648008602010042d003c0001180d02440c00395000000400181096560a00100407180c41d128031411450141030009030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 262703678 1250 262702428 262702459
    0x601050a1502030901080405010f181e15151203031b230c1504080403061a090103230115030201090f030b061c0c0e01030b18030301060e04020f0408030405 68
    0x814000012001c0d40140d45000c20000044070031701c1000303005039200d42d2501803a02803000c4074440e0070860358a21100380310615903890040d4240b110703000b40e260403504903412003002c5910122a041c00b8260141d00048000c110300c40b40114400301d9205410f50003112000d0014542c2507009240e1240c280e1040d40c4181d21190f205075000829054071215501d80802e00308070304060b10008142103941e03081142c02203c01c50800c4032a0301d0049030b00711804c1030041020010040b95010f015007c015000d9030350a041d15042c080b90144405120140c003560350590103800300c1403030b40444182c8110340b1000348805400441e21011200083c401280055500340000400342c0420820600b0f5903801005038006032688002c00c501420403000524043c03404080903000980102d002000503c0143c900459030340c510700f498142c2c600c5c01000b8610201c98000a001c5aaa0110869042d5038040c28403002c82c410001c0450024040d040164286120018010603440800406003080359012500c01d1300b0b02c2d9006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 262704928 1250 262703678 262703699
    0x109030c03021626010902041a03060f010509040f060b09010b0414030f10020a140301081b04090201020601030303200711091b07060b0f03030703120e0d0915020a05030c0601050a 78
    0x501c1960038507000740e44520048440021010b0501544d1000810459425000201280c44a0b910b01d07a00740c5000104109a0a00f4044c00d5804034943c403641a4a42c940300100c1c54000006100900d11004e01c505882001a01d603c4540070301800b0740014950341e190a04029103610600a420120310003001d03445851800203452016504501c001d01242c00550001d00c000c0c2d0461582e00043c02460f0100d0501c1c1c003c5000a14000c02640009049803120800c050002d0061701d850580241d080101110140c0d0f00040e480741141d42c14500098034070070f10704100c031a00510083e110f041d401e0014501d818800c0440d000c590542040303a0504154031094642c030344503040100441c2001c94207000c00d001092003940b140702c05001c05081c05805c0b401e201c00182c1140c0c40b841044011400c2d10844440b541c1e0035200d42e43c0c402826200038020305001c3e071800340102c032003440b505502180324984920350a02c00d000e16424203520808480d281c0280300c1e40e25440314402d0042d02d01401c81d0b010001101c1850 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 262706178 1250 262704928 262704973
    0x180b0111070f0302130b0913020405060604061d0616061d070f090b0a0f09020d1a03030f07020402070f030f0f020304061407030e03030d0207030905060403171b0109030c0302 76
    0x60a5401141840c581c280480b48405c485035a2420790b44200c2e0440c42e403034075800c0d42d105800c1e06d5418041c8800381e20400c405c441000d456280900c50a210030701c0b42a40182e4051401c0c20502da09100b0422440c00180136403183c4100440307083d05815031a020031442e40c0020000c00d01c0c011801450f8103100d15003075502c60b803910400c4414881031900708401105644a801229000351155800507160106051172010311391240c0411a80081c1018444103d4407481c0b2003002d01001850a0242000c0003d80e2400344142141c20504c00242c08421550390358120b071500c42d404032451b10309480600b80548039031004002ca00c00300c0d6070340c080c1c5900c2c03d102004403015500962a43c0400a0000c0c40c240041d4005c40412011f0108815546c03a075981d04201030704184182c070340b01580e00c00d80c0d4940140300c0410b07640068041d51045c40140000740d8a12070a10002503002102038454100c035601005405d580d0380b03a205154a010310010a1551164280c100c0714003d408891040c180f0142c40c2c2642c80a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 262707428 1250 262706178 262706189
    0x30609060c0a0c11060712080a05060a0b1813020702030d021f05070e0409050706030e03120c0a0c080301080106061d0a03140a141606090b180a180b011107 68
    0x10100414850540608803601001303000340303980c04130402a4004600658081c100603a00c3c03561900c0c52100b115400403030154050742280041c8200d040003004504010000c8c0036140d80580045482045030b200501044071904005080c01c41c6800244400b0000354004dd405034081c3c09201d40d48265180005044062078000260320325003400704800c9600201809050301080141590959085560ba40103003042c060194010702046440d022024088660035801d8038aa50401c0c4002c0052151038206070f81d001100c1072906644007180d035001c03203900e8070039a030041446002000102e0740810561203c81900e0300c549540d100800003050f68529048154030312913204080350b8040c40003400701086003048065440403034428403004d0341c509003403881c0708251103030300e0f81f0a00b40e111150304c13403060010060409081050406041a24645482c85417000a0065003040b414490051712022b1a01c5c008003032513040100400700b0200580050820211400d000506910840000803408138950007181d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 262708678 1250 262707428 262707451
    0x140c0105030f010302210a0c051207050102100e0a080406050a08100b070314130e040c0909030203250803011e0803090303070308061201050f0f010602031c0e1c0c0203060906 76
    0x20f20f981d080101060700055460b842580440402a03040c000700210b040ca984901c00c0120400c0c10080ac0c000000078400c030801c42035005c00b108002e02d9802203030280040034014800318001001c86041854103a41c0603000345614000540041d40c5948800a0503684d9415074506169417141c3c051445010391a00400b10202030030048030002034051041e5018100e0708002c010304008442d118664420035591154a96440c00c0003040208010040094090000540100150b94050b28000e40d40c0c052070030014600b030f4611505100082c412800b0a005551040079690b40f0360f19a9150146040c8401e004241c0c451110400315815002100707030381e00e1003030140c015401c00174281c40842c1c202001422003a0040c0c14019810b4600d0070a02807a8070402103c1010041ca00f001541c0c60307551201680080110341003403000c4100c08807007a034007807248000c00d48046444507900c880a42010403840d15a901010180b10310503400307411980d120340c818021405e581040d82c4022000c1d46558040341ea4120f2079 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 262709928 1250 262708678 262708681
    0x1b0f03150209030a0b100302090a0203130212120301090212060109031212020f0705010b1206060901030b182a040e030a080405030d2a02010b0a05100e0a03140c0105030f 74
    0x540081d03000d0410100c2c000c007142c18114103510341c08540c050030b40d050595440e00c2d030000c1c03055060030401746030410700000d411491131030320400c00c003184851858020703c01e1320000c0340c000c3c0c021002c101c00c00c04948022200d65076540e4504c1030700001d5003c0c07084502e4101403403002901c1907000b202c810041313941082103000b502c810703c141110181e808044180e0400d900f40040380c0e0300c0390040302401d04584074100008040e0ba0100802c4080000c071004650558801010060180c642c01381c0241141d0384840100308039101e00002514807240b06450740300610a01c00114000c0182a400f04000001c070380988001d0305181051000351500240ca1201a42c004c00c00c600900d480f03844040d40c881e02507000d90341828500d10081d4180c607036840c9a45481d032002c08041545203507428038102000b68031300003040800c60b0000815202d16040c0700f028466140301100804060143d0462141444010711403060583c40c0d103003d000b41c980c035201001040c440c690500f09203502640881c0d0060100d4a0301c007049 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 262711178 1250 262709928 262709963
    0x50a1409130f09060204090902040b1f0e010e1e0f0105120c0a03020c150109050a0e0d0c080405040608060405010614030a1101030f06060c0501050609070c080304020f0d1b0f03 77
    0x2810b4074400122010381c3d9602c1c0348010403864800307000030b403a04520114140c00c01e4010001170725140d07030f4202c0c030802440f1900c13580c080d070044005a04400ca403c1003c406000c1c075005031904400400c115400c80384544541598042070b4180c91a503540c1201c90b00d24600d04140119480c0c0540b14443c082c5003503200100b0844d1280c403001c0d005074840c0b4038025140c0070711072400c1030500b2500503520000d00c10b4000144880c14250066a5100d03107200010084c00d40000e0000e0359a0380b4400d6001e00703000d8004414800e0040d04005c46000d0030001e002444403941c0d0f104c44642d160300c00c490075100b42d440c100c4041003216101d5511414101d0040003805e18615a8503075240c4000c984c4010b0741851350300c001d0307150f009400f030041000400803603c0e41100c0807414180301d420f44100034485841030020780200580b540c1c000c0410801c858000c60300036101c0d0749510200c1c069100c0900380381d600c007004100035001c00c041c5024040346150413801c41410240d64030203e42d400486808014081880c4401403400d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 262712428 1250 262711178 262711181
    0x90c09030b04020a090c02060f0a09030504031203110307050703030b030309090601050a0306031a01030618120e040b04051302130606081311130c0e0108010b1b0708010c050a140913 79
    0xb003050004082d26004ca80d07403561842151641210240507800c04010070075801a0030301182d03409000380e401440701c6800c5540c0107180e4072950100070b00e80c24a15404410051103640041032180e40035030a00c2e0740f0b0800940c05800c40e0400710044000908190700c60f9480d0901000740d0303502c00c001410300c1c540c035140d0b1401900c85400c81c28055080617992280040842d422207801003031240759107130483d0554110b08024040c3c408009241142d00621001e150010703031000a034028024051400c0d204001c4140300090140c10360301c142aa106083c8000e00074200b90800340350040c54401c595440184013000344200a5903564811180420b8a0800244a55090040701030000d132013404003507000b85400c00058800c0480380c40300b907580d0380c2e1914500b090302e403c58140700900c1c03000d0030a5803141d850014220340c01d104004000c06804441e680d842641d800c03c0150101a2800030001e01c10080c18890090460704842c020300002543e01d07050301c614130f03e050201e07440d00c40058a19030519410301c8a410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 262713678 1250 262712428 262712431
    0xe010302040b0303130e0f0f04150e07030f0b1e010b04050108060a17070302030115120204150305032b0c0804140f120c0106060e13090203010f1410090c09030b 70
    0x60f00340c00200082d02c4103041c0f0342d0b02a8090030844400300b02c00e0034520758000d0782900061010222402c444280700200301c04110441120380c4005011600340b84400c0c880d820b1110552000700314800014441040044100310b482c407642c1c0340e03040d59190910905100c060b54600384101c43d1040e90402c0244411b502c01d5910580c01000a003d41da0340c5aa40e001c941e050000c8690802079a82118000784118078080c092847d0304d07280e04203410007840c00c0001c41c1846130007940d4000e102c0c0c1c0d9a030030142c92680210740300800841d0480c0036680c0b554585080c1c4a03400088481c0d201007e500c075072003046140641c1c410002c10441c02d43e15150140c0e2540c0e241d481c100c4901a820707501d0b1150880302c01c9502002c01044a5400c208030301c0740e07100d80411006900b0f49101c0d411401c203000400000104a4035040301c4d800208030120000704070f1071102e0020a00520096040c40042824280307000010904100101e024a01080001040c1070b56580d6038000c951041c80c0c60000103280d40c40410115140f0354145 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 262714928 1250 262713678 262713701
    0x507090f142d0108070203180d170406050705070501020102270a05030d0215011a1c14010b0a0e010f0504170102120906060306010609080a060c0c0c0e0603160e01030204 74
    0x70724032a40400300c404542c407003019088a910b001c0003036288443d640f10310070035005105400114103281d04d8581203600011710f404640e0181084042503028000390044c00340038124402c2e035480e9110385038040106664002a82a1190311681c240064254814030840350020400c03201d04070080408e01d5401103003022110740941c00340c8031000201d4203a9083c02080012a0103800030940e00c6880107482621020507072041c1c1d024040d2100c440c2410700d01c181140e40c80002c50038443c1c0a070302084030744130080486075000c07003203813400324000b160001d00381c0014110260940c46a0880c03101c00340c01111f0ba141910740c1d00b0001101488200020b1220080386050000340c01c00140c04c10145640f023403180b043c1140c12118990294003442a242070610145024104030714003003d000d402c4c024843c2e41c4000540d001050766a42d246c10125040c4a10303c603907621a840110503205540d11013101600810a4034414800e000340701c440c54060051801803001c07952800c00388003040c0e20395001c01005210410340d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 262716178 1250 262714928 262714939
    0x70203030a0b0325050a120b0c071523010803090a0b09040b1519090303021203040303090f0b093a0306030b0405010204150804020303070f08090307080304090507090f14 74
    0xc42940628200084c0c8440408a0100409407900b020001c4e407001d603500802c0e0360b040e00c64007200801d6a0300109607108007004107284c3d84185502c1c00240300c1c40080001c01425107001600d210061205c2820065035800d4446520166243c106080d144d1089a000c141e204036140720800c000c10085010b4640b80000501c0000d02c4122180032a8000d440b000d03000c100100c1c0011000302c840298200140d07aa440c23031a180e52030f00d09680d400b80d5280e481051304030039140c011000070201482908140306c0300341d0050003684040c00030300e004040321005403441d80723450040e010000d0381074810032441d0081c01e2000400460110011030450803d21281c509c6c08101501c4c3c0d100070001c24080d024540c0154410000166a0741c5041c4501c040400d0300b030380d580c00700a004002e00000d66070010a4074292a00007049941c50003071403a06440601c138146055406000341e03500040c2054011000e03200715406004d00b070010340d5600138115010300f0a40200300300035140840c01d0292085d056140904100003411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 262717428 1250 262716178 262716193
    0x16150809150601050f130906080106050109090e0109060903021605120c01140409150303021908120a0615020309040b030a0c0303050d0207080f0a1b02060a030209030c10090e0f070203030a0b03 84
    0x1c02c6405580b1114546c02200c4a41c8810049500f140c0f081c9401400014001c2014505000000306041490b01c50030800c16142c945050325194294043c0300d0710750340b2a0b01000464490304d4042e4851428400500250201c04000526403e08861140f1621141c501400b0002a55001501c0c08035580b881315080b42014080852507041c1807003101c070b031b00103d0360440808034a14500240340030050740300700000c2c81c3c8081032800020021000c0e11001e002c2000f03042055a00c40048900400c0503038000b181e554409a8495120386d004030041c03603a0074041d1401d100d03415000041c9662600e81607002400d20210540801c0840d21980160078903501c40d01000d4601385850702c800e0096009900924a1120000369083c2e049401503a032000d99840c0f40c0c0c0640d180500c46d00000c240d80984171010701855000a400d00301550705106900103140000c101c0008051443c0c03008008108502502c8424150744000c240c2d0b4500d40c0707908034440d0705140d000718a542e035000716903006050610f01c051340600c00c040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 262718678 1250 262717428 262717447
    0x51206161d030d020a050f1501030f060f0f0605040f06080c06030417030709060e01020f0718021308150f090304140d060c030f0b040c0c060b060c1615080915060105 72
    0x1c00d45440010a6004100d80c003010705085080824800c03541c906907100550424802d00c0d16400702741181d0f0880c131103209440741400c0942c06040c0c5950003400152400d909505004402d51004003502e070155020086c52203015081000c80304107018110281e4488459014146008001158000d00c1a41b801030b000c041142c0901080d00b080e0341c0000895400d103001c3c00410380c45110b200d1800401d200038541245402c0d40b0b540c0b07070f00d01400369a184078400c0d640741c007000c4c10540460f400244401c1c1070b40038499403035010680f11080c000c0d01607409402d100100fa01c1c50004421030740280b42e040c4c0034500d41854600f000048000502800ba0005e407148001c0c800b1580b280319101070011980c4010413442001c180003000c60b0f850020561095190005403e80c3d81c0d4030551361400f00e50300101c0000c444401e40c0000703001307004008145c41e192140854981e8000350a0790b50a044505044900c110002030030015150700e5000c40d00b10440358456602c0c240f00740d20242e4100c0c0c01c001c06040240c0f400e203022 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 262719928 1250 262718678 262718683
    0x20d0207021c05010c09030b0402100207080307111c1a06210102070303060e011d1906120309050405010b0901050315061908010503060c120901180b01051206161d03 72
    0x242e0504410320390001803036040c04400c0c001c19041d0503080c80e040b035426007981d660002e4600702800c042d000b000c070f6030303080c0e10b0f40c03402007003020054231810044a4642c1c00f6440c1034104501c1c0c00e02003e024502040c01600d103001c402000044259110044d003a20300200306900c5000100205801e43c00640400014000c03e9640d00c95141c2080704400543d0703035281810003406840d0240d100052680d02c080041200300000100303140c0d40181c1000085441e1110880d403803200c00c0c1c81042e021210b03c0d04d000000c5240803140d61000562098803621609542c0b44200f01c2141e50034424403601c80000c1000c440303c0d6110360000d40e407069001c03100c14030f100c80300c0c1c0100d0078030303040301d00020b0301d0200784a0740501460b04544841e0050004800806051401d00307000302060240300c1140e0b80e9000c464000c00c503603100030b400580d901c075403c015045c588812410604103c20083c402e250184000e2000788901410101c1c202e440b03025903c1c0707421982c3ca241003003160701e01482c1c040001c40f030088200040041d42e09 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 262721178 1250 262719928 262719949
    0x50f13050607080309010b0904150903030e1501030506090604020f1302070f060c0e09090d08180105071d0d05060103033c0e10020a121e03050411030109080706020d020702 75
    0x503c142540340d02e0401c2c0318608468010801c1071058104104000004000b5000c0f0f243c201c0c2d4007200490080c046240035009072480b80800000c50241268102268803913080043c1240d020303808446485d101c20850316102d01c0103441c040d410001032400000c2e0703414078010340741c07600520307190040c80e240ea03540320303c48012944102142c0c0c264a070b600c030307400d02640040c558156400403207103000c56042041030940d445840c120100f00740b2560310002140e02d1070040d0285400c004290003401540ba01900050800032908441e00318003c02d008580c10608202203009001d95209008180343d07400c0d901d09881c855540c0c840b4803500f1040113001628000c40e0202c2d60044400c000c0c0b4602d00d1640400c002c0e000b044a8040c80b801210f08842110100d50300081d400025600f04038900400203c841c012249001180303143c43d600c001d40c032840b030801d9602d6881548524041da184000048240c0101801e03140d4843e030181032002c040c000040414140e5008051441100c44d0061501c1d00c558040b6104440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 262722428 1250 262721178 262721183
    0x303041209271a091e1005060304020f060f1902011d060f062205090706050c0d050c0a02040204080f0f06101418040f03110c01080f042a030c08010c050f13050607 71
    0x1060038100300040c1710402194114040b82002c0201070b00344404940320b4080204083d1140404503a40840e50311018103c1e88081005d101e840e13950660703c8914080318261076101c00040d0b1030100781103240907508054040c4c110403913014240b15103480808035001240605166803041040e044541004007400c07401c0c000d9100d04101060900c0d05800443c10500180d01403028071004001d41840214086206c000003041410196140c1000300350311480c0900c1c80c0b000030342181c800100442c4002c00020070b040b46881e0340e811640b040700741d042419141c41c015581d216800361011000e100f11480a01201810100903215500000c020b8007031004007a000c0c0d4040d58522224848030013810b5200d0401c0341022500d0300185417079158980002c011050091a10f00c0141250000c04c041000749060140b0014485100d030200c50915500c4c00018a4148000c4400110002000410174818000c00148080383d07200c150508000d8401500300d50300c241e5680100380b0882c1030220b034994924018020a50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 262723678 1250 262722428 262722451
    0xa0e0609150108010606020c060f0d0908030a1a1c02060904050a051009090305040e2a0c010b010e030c090c190f0f0503040b1f080303041209271a09 65
    0x244241c840e168550010b03000084180d0400c4014000141c00041e1070b1014902500c4540e82ea4081200c0c5000b103020380031114241034205448002804032440180d40070340315100007080b40340040d18040e5000e14903020ba1940010115062001e402c08228000c0005400502170b24503000c0014001003c84400f150010010795645060040420740c500d21100500f001d514204140c00f101d4501500a00a038070a07070075031401c01c02c0085c15070b8199040003074a01c0b80d2845202141c40d81c280700703014103070094071034542203610f4401840b9040d841030b0601c400304000600a00003048204060000c1c0c0c25004201c0707050800100180341d4a404841c2c440070207801c00d0361304c1484049034880010b2500d2680d40d104010840d003407040c400443d000d1a0510f07000f01002c1071804102103002072800b0002c034107501481450101000f0841442a040c4c14600c0c186010303a51058100e0301c0c5da284514940e2120b460115904d0a034101207182c10b03090384640d80900d0400d19207120103400c84e0014020b060f0481e00b0500a4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 262724928 1250 262723678 262723693
    0x6080102220f0b221d06030d0504030b040803060607080406111002040b0a08150607030201090c0f03031407020a26060a02090d0f0f0c300f0b0a0e0609 66
    0x209045281c0500104107040301c541c2c3c40c00d04241400e0040c9083e5052044003c80048410006014200014213160344441d08985041c0c1d942e403001e00c001c076401c1d030081c0202c402189100d8810b00803a416664801d18094442c1c480d034a564040350401010a90050303c00c102e8180410303810800f03880108000d50302c0c01c50410222030003900380344905050500c02401030005100010b082c201743c1d0010182803030a56900d80e40c0548030458940144001034000d200041e680b42415419040300c0301035802403011b0340300e082c1e80b10230441c0c0c4045980310240000c1e4103203041c1c1132140301c140000c1c085940002d20401c0c00c01d0312031040400000c4000004024820b140c00c441e202d00c00244145540701000315403c5051002c8400400d004241c0d01400810710300c10550b01004100c2225500c6610507003020b81c003001140c0b2070074005601401c0800351a086000703213810038401180500c00c0c0d01c400d40c2c840c400750744804299603024034104024080c0f03c01151240b81c804901d2000b00002442040c560b0003c0024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 262726178 1250 262724928 262724977
    0x11090d0b09010c0314070806031005090c040e0a02010f0f0504031b08060601031b140f0327071214102406141b07170a060513021e010306080102 63
    0x8403a01c0e0a00074003410b040041c200318042061721826842401424040020703540d0100080c28002c800c0581502285080c050100c4a040010900ca00400c01d0b41c0810910b00603d4400c2e9480000b41d00c004c0c0014103c40c80000702a100d10782103441c85400781842800c164880e580c2070078025900d000200c1940d0144070800c01c0000400034641c208d803080c20104407181000400c007007291001e000320070500c5102900303158107110b10011a03074076028400321a80c032810701801d107224945481c0401c0c8500620300d00c0241000902090800072103005035482c00b558402c0b42d96904500c0318a0381680080e004610b820201030050b4015101003680d119810340744a80032030002902d090282d0040c00800048410008820502d00101c40c01c0440b0700701019428440020fa50749000c807a42c220840d1801d0b407014032200301d000061496650ba1048500b80101e60780c04041c0d000e0785800342d20185d032116540300c0712195101402034540303003e18180b4011801031784481d00070307081e079200002c1c08246000c4451005d05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 262727428 1250 262726178 262726181
    0x13030605070e0612060405090f0601030c03030e01080f1b0705240c0c070306090602160b0f070e0306070f02070515070b0705160b0a1d03030405070510050d11090d0b0901 74
    0x100740800c641c11070030040d02064100403031340d004054502440d614004502c01c40010041c8023034000c03800048880700d6031603262001001c83c4520048010401d002c3c05007010b903003d0078125100703800740351045400f9612061001043c1c3e403100c0c048410400c0c200950741c045032052010441104800c09040c1908030020f50211302502d006000c4080020300b03010304408a1000b1a007001160342250300441d507010141820b01c0248120525040c2030100d5040542c10881401001880360514081c06800c0d40e403421001d03600e048000003d90b91580088001a0301940128641c8249a10500c102c440d86030311100800c43d803100450b1058070300d0790301181c048100841c0600f8a944104141341080c14110700c141e4007000184003040c010a100030000004110700e109600205000d04072540400d1641024040c29403254010380f801c3c2d0b070601030043c0100e000c0c140982008205201d41c0d035601c0c5002e4040c042000200700151042c601c00c2000c1021500c5c0c1e59039240d105150350f000d10b10480c1075040c401c41550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 262728678 1250 262727428 262727447
    0x80a0c1b050d0f11070501050f0c150106020d1806050a12020d0624020c2b0303020307111c050703050c03040b04050102160b04050d03020307060e100b01021614061303060507 76
    0xf010005599000300303142034041a04000c5581c00e0234496111100a041d242160060000c01ca80500ca10108502e00d101400c0485040700c1a070b80a0f600b442500050032101e0007041c0b00c0001e6101071b52401040490b105000416178400d441c5000c0311107030740701914001030381d10858295151710307200c0d5801d0000c02030707946440e40304005660603844504180080651901401c200c4240309081d10030301030a8030603200c1101943c00c1003003800150741081a00d00a0000e40060307403c80c00049a03105226501c0100082031203803d6590400d6a0800f075031b807181140c09900c01e00044040020074040c4a40704041040640060041c3d80d04d11900c035402e0000082c038041d0040c181481c001198901000b00300c00c61001c03a01030351001d59010290803400e080591842c030070048000d0140d4601101d208501074007254103906c9840da410240102c540301801240c1d280d20070070100c1201e03c03240c0340800c4082d00921410a4550001e00440d09103400b5078151180350825074001d4600c00e458400304040d03079901035030380c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 262729928 1250 262728678 262728707
    0x180c0405010f170709090c090509010207050c0918190303150608010306200a0309060c02070e06100201140a050a051b1207050f040f03110301020a080a0c1b050d 70
    0x1040998540aa48a25450719200f24540301500000308082c800e01400800e01a007205c2c1001c2c0030800c510324201c0a41c41591040140c0d1a1034800030420002040c0211050107070001e008004143d003180400030751207405040000711207041011048454801c0c0554028521710304403001500495040240030340b0303510001310840070482a0140a076507041807038581503c0d0400000a90f0100981c0c03104000c000c2c1d100d520a480c01c010075488441c2d035140e082002601d10440e420f008110621000b60780e03030f0030580101c108d241e5025000600c181000c2010182d030382c09078070020031401d0040f18a100ca00400361000b212040d103c208200c000b850a0161540008246041130340c107074072500032a00c05000d11126800d14841503804141d00501c24410340d000c10700e8103002d1a03911540c0d02440860388006110840710100c004928031001c0c40c040c0f0079121150041d4641808903a90044140020040ca90362041841200c100780d51076001070702d000c004614403440080c216002c01580107080d451000401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 262731178 1250 262729928 262729931
    0x11704060b0109180e190308070e0301060b04090b1e010c032f0a1e08120405010e03040902041809080708030a1e020909250e0310090803041208040c03080a17180c04 72
    0xb1000022342c0081003d900514134641a551161a64006030150541e50b1119141490202c0c0101c1c41e8803040e4080c09031510210343d000900e0712040c503c901c00700f8071841510701040000ca03201e00031901614108281d100da160b1000c1160b222034031044483c00011000e01032640c0942054400c1141610f1081036203050310206a003144901d03038031140f03d48511a0f01e51790480d070a03000b29042060035004044003c48010030380341c40307603119150703600290001e00c69544d80c807110385072004904126115264856402510702c03440d114a54441880e5a4405403189000941d01d140340840354a104071000760002c824180980c0e40e8045004020040700090006c803107240555804484220ba6139682803550300050070151034402c0d807200000d007421006410314640c541088240d000700f21860700254030852040ca00016244080c0c0c004841100007150000d00d02e48800c3c505001182e603c0d40544125001842d0100804082c013130030125003030041e030328060360108119110101c40070030b011010aa03a020b890 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 262732428 1250 262731178 262731223
    0x30c060a2f1b0c030601030b19020309060a0c11070308070c0803091e0f120304030506010e01181e0e010c090b070b01050d03091d06040b011704060b0109180e 69
    0x4610070301e00ca90030307040304440b50a0752169040c910520800310305030401002c3d40d17415a03482c200594540800c541a042041c0300c4250703558107141a02c00c0d00d01070680c800043c04d17190307100e0004030300034005044404c0c18001800c6482d040c030102008940c0140d84a0031080d070700d0782040d103040b507051219600041c5050b0410b120004290b01d50b80e16000003c0c0d46400e8000c80c255504c00407504684005c0300302a0804110309030111100000001030044920400886645a17070b0b800c89107091070030a002d400c054042e08050350204400c144c00661600d104a41e082ca05414516032040840c0da9171081520180d4444800c140c0981c1c010002500501c00b06040600e0300d04a9541c0034203115050080900c2100d200e268807060502c100240c101500d02641d1126040b83c8a0329208021682203035103a100302e04000300350740309500c10cc604c0c03000c1010b6461100066103c540d00c02c5e0140c241c6151841c10803542c241c0011301d142c03d502c80900d05203104000060030035540da282a0404403542d6000003010060b18 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 262733678 1250 262732428 262732511
    0x50c010c0b0a051f03080310051002030307050708090a06020c0a080303060f060c01090203010213030b0132010221040e0a0b0916020307050a110f0109031112030c060a 73
    0xc00c0c46620030808000007940ba03955062852000d4240303124101320001c069000320410000c1001503004011695074500201e9a0360104900700c00c0f40210400180c2090002c00d61850245001d050400c0c8201030243c10250082c01144080c00f1580c0000010f80c40041c0d05101820102a084054110603001e14130714030f020b40200700d0fa01540c4200c1801280c0005e9002d00d040c00039440710305001d0380180259039817410502401c00c506010300095071203600c01800003c2c6040242d84000012100340f01c20120002d0340c000c040d00c01071989402d04e05501031f00d00b800034440220201078102c80c1348684280d0315541001c2c500118818003c280c00c00d0503241c00f10f00f215030b81e03441361810307032004245a42020356000c0c01d070100c0c10350080450040452042010250401c2403900d044d100d90081540c54070f500110407801180d80c05a40e100c06031000e01c1c4280c120515003464104000081c14800c100d03071514036043d02c05441d0503000c50300418002c1c4d648002e50795000103502d0b500b000e0f03015102000c14242da8607 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 262734928 1250 262733678 262733693
    0x501030f110a0f0507300905010f0302030916030819030603050c10090b0301090207030e04091104051b0309070504200f0702040f0e0105192003070903050d0c050c010c 73
    0xaa010105204103012443d00c0c0521440071244100e500c58030346440c40c069815001040b050f44030f40910b9611103440901c401910950480c0203c800581d20360041c140c0107901130b0003d6201800c490070038080c0308218281c0d4502031a00c3c0b4010f40c4160380042c0c3e241010421071000c1005500f12004050400a003000850030009801d0701e40013040392001010100003505980308001c60340803140c080008400001c1643e250350140407128042d880381500b01c0d451000304030031110b001034020840c84d000489025541410307844940d000008011240c0021040c8050501c1500100c407500342c5903104400030300981c146402100041012a01d401d004886141c01039038050188098900350507074041409410356075941c002e1042c500400500700301d6800c0903410b4078040c3c60b003104c0018040d1340f24007007500685030070310881c40d1030301c2182480b820301e2508a11800342070380040d01013010000096000b0010032010f1103041042c4003e0744818106910034507005080040140710a814058080803140116402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 262736178 1250 262734928 262734937
    0x20a030204020d0e06090705091b0711011b050601090e0606030a08030601030b040f05060114090a0b0304020609041803080603060f01060503190c02030711090408091e0301090c0501030f11 82
    0x112005030325941c40c400942c008241107106400948900c45c01d004500c0d4021031010b044d1002500c13042000e60f51040c1c0c04908503004c00c21203811040c100007103400f02c0c010700c509902400051501401c8640c000d10b0248184009030703c00d480540203075004000c0b5514920a00045108110281c041894503c2c0025181c0750b04110107050301d0400000203815070300c643d010302d044450040c81004085241e00781c40c0010030040354680d021607204001d01030305007021426a46501e00040450b0021030600040200541003d00103e070003060074042100d83c0d5541e401072282c1140c0200800ca454419810024181140901031b240240c10040600c44505100000181076420608040360b5a0301d54580340b1303002d1800c84403c01c90152804071b0281c085a4084001e14085010f03902d614030501080c410440020710588008050900c1080365034924100b404400c0c80c0354044c58030200750022440d02003400e4610300c0404442d000e20381c103828005983c05200700e44002c1c0042c4820041c003400410030702c0d070b07602c074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 262737428 1250 262736178 262736183
    0x803031f0f06080c0c0f0709020c0d1d0d020a0b031812070506010501110319081006030e0a020906010c050f060618100612020d180302010b031c0c110d0f030e03010603020a03 76
    0x24005685c0d01000380400150802d04c442c0350860705c41e99514a4a03000a4201c000840f40d00e0058041d01c4100501c240483d42e40c002000201c0c0c0481c8041c4820400e4442c00f440040341c00c0300542500241c0c0e010104007440c842d0541500c14200021048002810080f00071125000c0e8441803080401143c00040d001d0f046d9402800c1821041c1c075a903041c0e42c95402366410400d04003906c81500c40000e58403441160080c00c3e8641d5180043d40c8502c410b03000d688008601c041d455110007400d00140c540a02c6054105006041c007907541c10351519202e003440034884840c480c56000310103018083c28581c14140000c814070002480d941007000514295003998450071080058140240c00b007120598121100d0000114003001003203102d90f00b0600c0740880c1002070340035500c0c228540c20142000728403001001c203074169040c0d0001c111002985c803800000c50a4450441d424a202c40c140c40311b088003000c0d039004e10005a603000341490014000303242d0300516402a41130034030070801a102c41d819582038a0703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 262738678 1250 262737428 262737451
    0x15031118150f16030813050a1e0218010e180d0e040f0207050609070803040303230d020c0a140705100509060c06010f03050d0906090512070803031f0f0608 68
    0xc10741e02856014050403042e42505100040e150800c2040d00f03056204030741c802e0320340d44c800750b44100300742d212075031041c402501541003131040d1000240650028019071403130b0360301c0c4d082040c000d80200b040090340d10009000200303104014801a40c1001503168003410a41108441c07400707500c00c01c0d031a013020b55580002d000ca00401030865039100d402050301681d020608540701c050381c0c14055654181a204045e02d03006003078001c070728030f42c0100480b01030300e030182c55081c544100026190902d00e8600050548020705002c58000e8490354002010a103111a0007000090761900781100b0303014003500040510341c040c010402994840174000003c00045062850b180c40208000c59118800d90850141602031030001062948921051703006581c000c900301d80e020071986000390344445050040e5004112000410803032031401c2c8a8810b011840c010649450956605d005891034100760360380c2401401034000c02d00940a903d8520380280b040c010785002e62840c000300900101c0015180306101d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 262739928 1250 262738678 262738699
    0x306180601170a090b0a0e1c0c15020417010618021308060108010509060a05040c0b03070c121e18031412032d072001140115031118 58
    0x60b0300a2074040340d03041c084550108140f91902c551002441c005404850703c54980000c2040700c1d485102c0c40900600c004018041c030b0001d0540300b00b40c1350010024000300500581c150b0006a460070204100d00042640540c8403814880188190040c4100340c07803440e0b240420400c608508940c01c224103800349040180d6540a03640191513a401356006a2040c1c4100ca000142da1401540420310800444095031016110009140300b0f548041d00d002c1d0444105000034800d580124000b190040510300704194115070302c0da40c0c030601c100400c05d0007010401407070a2482d40080e00310300d41c602c003000f841c210000240321002d055400107a030002400000c4200c03880360300c021080050518010514207482e84914051991140400d81503200306561401820f50b02c00701c4009242d542d0180015031030b2850710403000301c181d101298450346a04815900c48000341800450380160901074191a01c0d00080c04640700809020750f0061450b40c1176000040040380d84100b070a24403080308410444040021 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 262741178 1250 262739928 262739941
    0x3020307020f12030f100f060e011e1d0a1805070302041205030a03060909021305040503130b0403061406060711010203071e061401150e0a0807080a03020111030618 72
    0xb04000720300508100d10403441000062440c1602940c4038140406045000307954141803e940e0a24038400d89070006c034108010300000740a149003120519040c0b5048188030031380c01301400031807803040703680d0701141d04400040000243c448070350140b46070550750071800c0c51a0050043c0d119203650f0005e14002e0f41c600c0131a40c0c0c240f10350101c4000b803c3c0e43e807402c041d00703660b414541c0d281c1c0d000064860119180080000b41f81602d070042d01086500245804648460340b41c6503400303400001d008417510f000800849040c20300340800000907003481102e40b5152429031401c1c8003180c0101e21002c0100780038408101c01a07481c60101c03101c031507018540c46401030f6542d005070314500031640010001030707481c03180d84c1c1d00c1625850916510f0740108018441007a40302c511081214080c0101c0180d812941d8401a0550180c0000142c40352b0141030000d51564070005c0508000c01070b000b0000303513002500b01c0700a166090142c1c802a07038482104a29500f40700c00000d0711040070315441c20451b030011000440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 262742428 1250 262741178 262741183
    0xc050309151302120d0207080a150906060b130302040b032107050a060c0809011803020309041503080a020607110d020304030b1e180d021917160605040606050f100302030702 76
    0x8983d40905460082d0307400d4071100b074a84001340d411000612888100060300000059a41c1c2d05542090318100550306001c0d07070b04051701c280340c01500d9803034680c00c000030001c4950009044100c4100c90058405003544100020707500400d4030107110350b020702903507c000c444118102c052086103420041d500c544e18600203090610303012010300346070318055450403000d0300700303081c00d11074581003008005401c840403078040c02000b08200a00143e105100b540d03d2401e19602c0105040c0da05414030303070300b250350341e482000c503600c00315403d801a0030040620400c0c43d040460108040c8030b0201031b00710510005402992801141b001400d175044080100b69814010065440c040c0001c40c0442428070300b50407404403500103002001554840c00c0300e1a201e05202198022004000040701e00100015441e1031000d480c001031145214203081080042c1180700840920350544075440c0070031149400c4c00d1203001c0350810350040b8041c4d010380e402c1c501e07240c0d10b0180313900c0b070155030781001a103d84800b80100d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 262743678 1250 262742428 262742461
    0x709020a14041a07031101020c0706080a0c020d1404051203071a040b0705090d060507090510050901051c0222030b0109090506040b07270e07020d0906030c030b060301180c05030915 79
    0x6c070554400503d000148601194a03021717104152100300c0c041d02e58081d04021500130003d110b00682001075a40b00d201e00c21804181c0f503c0c0024010b606240d114000a02d0bc12081103070000654400100c0c0c804000c403100d100302441888400d070b040f8503d0262a08400414001d0440c0100000002e4061165489120840c00340d0f41091003040710b441c1058001d011040640102c0d48600002c00031020041d114004581849034103a448504003038540c0580900300303158083c01d070b800079000d0081103000c0c036001c0201540d40806404000742c0e146035080007800c0501c180c000c41d03400350500c0400d2022440014040b40c12660046000c0700566400608942c60001c4a107280e04108042503500c261034080c2c07886109441c02010440d0769525102c0f816030742c89013210100380229011503070070003481e8000d5108c181e02a19a0a0100d000c080c0400000c1142e4001d03040201803085c00014501d66003418850410944074905180d03141d4208940a240e030380780c1c0040c803403c1d0a2415170000d8103008141e903890 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 262744928 1250 262743678 262743707
    0x4060203060a09112101060e09041416060908151807180b1e03120315060d06030311060403120905010209030a05030403051506240c0709020a14041a0703 67
    0x802a8440c1602c41241c15070021781114800c3e4038103a42d000c2c40c2006114040d04851685d180c0d420404c24000a000d2549001401920300c50750303807200179544503814041a035610902d01c98842420382800406012041140c0102040d548030140c1c0000c40c0d500d8000054101c5492403c2e8011403007521116442d012091b0002203081c83c102c0c4402e100d0044035003000006640403100a600710131b44503500440344900c02011985544540c14400f00c0d600004000c58000751444403590200304054041811076100b503199040c16a0703a01001c1080c1031b0301250035107844031100b010b4030180c20306850040103010300c2100350780310b81d03919100c03802007180c01d604454008501805842c400c070940d0030100c0d200c2e0414801542e850181c48000110781e9244030446209040081c090080f00c030031990840e0700d0020005408501c070f50b04005e83c0254190402c410401444004c0b00035945100480000f001040c001c0d40844c02108248014401e444451140600c82c0c01d8111950b5200c0b500b45c103040b52021940641d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 262746178 1250 262744928 262744931
    0x6030319030203010611060405070b07030203070501060605090a0e160509010e03070f0e06150708071103100e010c1d120a02090406020a0e010f020d110709140105090a0e0604060203060a09 82
    0xc094194064010318100e90310b5440306e030044045085142d8854500308c3d070040850300425014045502d03003c003d80381450181c03044904004866503900e00315540c1d504a40003142000c60b864110b403a161141c40050082840390402a0910188440304090841b4105051204c0400c0144290b441040e41c500c294000038215440c01e682c0356800c0c50010068080c0b09412500d83c1d0000d02c0500744004509080b0110b045042d00d4a0740c581c884441030303000304000b201c41c50b0b8410b001c401a030f9020010002c0e252414180000d010700c100c80c0d21401c480e00e01403450b0a0140365651203055166004030a5401201580c1103c8403120354a04e117410090b4400000758403410f054203120074050703140c0c0a01080c4076a42c03546c00801c0b02d91001507405070f003482c81c10340c0160321102031072064038801c9003482c1c1080140e40498026503203c9002005503142450351010300d00055004011a1510ba040c680d00480c65036010045030a4444091392100f0008101400c029000030109060351a2002b48030018000d0800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 262747428 1250 262746178 262746217
    0x21906150909110a050901090e010603060e01050906060306011409360c03010216020d02010c2001080f010605041e0302030a030c021e0604090905030f30011a03060303 73
    0x81440060060700010f4440c402903100c0740f2030906210004000b5200b00400c5045940e182600c200d02401030603440d00c1d515500c6400c004005805400b4000b00c2c00b89640011038103140c00d0412038542000200020300c260302410040242c800c00810b032081c0d140701540c100300c9a80e86c004030603500c0404503088443c00e40010120000054030f5585a0680210000c2603e0031140d02070105800d074011740340d026040c0d00c44c1340618001440c4c80100009824410b0510b03a040780d01d251100359850b40000d942003400404124140500e6034000d00030742e84803003114000407565040110080841c02640901080780411a40c034007004008681110700942d401411654002e003070f03240c0140340c0c21794070908a004018114190b000601c0d242c2c8004000300c0058540703401d20b840e00981c200500301d40e21041c3d500707010400c026615919140006c0000700c8400c6d444683c0344010101170b402601c0300000c0c4a07007080b002e200521000406158021307020640c110301d540c4949070000001d046108a00c00e2700000e031001d14 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 262748678 1250 262747428 262747439
    0xf190303020706120501050307050103090f0204050708150604030f030e1216090f09030f1d0a0b03150105030903071704080303040b0601030f0e070b03041406280c02190615 75
    0x3211001e54000e0344d9070b008050300f0201d000b8190780082c058683d2581164030700348010b5103c0c0d400400c0281c05802c02c0021002560003140445000f070714100000f95020041004100030303a1125000d0748401ea912a141c6451600c3e5a803249820362402010005600c0320380c601541c42d041c503012102d407140140d4401907030034045d0407500c14541c45509403c6041c4601e00c0192000d602c12540c880760552180d00e00204106c10032545200c1ba50481e400c40e8501103940078054035409025070240800010390f940d2401c113541d0030007180030000c07409810010300b0810459081000300036100025030207561640074110410b803205880c040e54114000ca84000300800c07041c0b000d2024814041c01e401c1e01c081128100442c0700c141640c0d44201103090652100d1000c1008501d850010b5901c203006100300c01030b490583e104d8a00345030041c1c0b071614a042c44c01c46814002c0303165070741c0c803d458003940000b0000441c10080207912994800041d101c20940b03c4015070074048280c00c8008203800288040700803603140c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 262749928 1250 262748678 262748683
    0x60e0c03040b0f070509010305071101020403151104230d0206160605090c060a18080a0c030303381809012a0905060c0a06020f030a051003110f19030302 67
    0x484003030790182400b00105610480400646008001a594140c81c0000c0c403401503000d070001609602c00c20154444211882c0f0b0b00b0720280020303511800c3c0002040d83e91070804030941e01e0461142c804003204100030444030364142e12100c0c22294505484050456080005010b43e02900000e0741081c80004c2404515007500c0041d9186071140e40704005540300e80110540c0d0b12003805605400210030840013208a005041d10200d450a194115042944820a19007070021807502160480b406043c113008060700741c0940d028112404200132040008011459540310380030700c15150101c0742001005650b09e03000b44500029506003c8801e640c249407004a00130700019070600b40039251441504c02103c42160030302c0c40b8002907552003c49d54106010069154072568810415103d0310480b1000945c083c0040c002188020101c95140d291030340740315056030402090107408401c01d510900c005030340d40701c14909030f003030039100e0b45420710514002c10414500301c6408594a810510b0010805130300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 262751178 1250 262749928 262749931
    0x2280e09070c0506330d021203040e070c0f020d11042408120904181415010b12041506030606241106130602250311030f0306090a060e0c03 61
    0x254115082a640c03202425500c110705480c4054201802d5100345d0900002442c808543d17500409440042807a0f600046014100d03401c0c45403243c102003030030003c1c003550b04d002d0f82d4020594200214a2180e95a401ea40861b4010000381b10382c0007502e100c0c040c0700d81304003003060b40c41c0c01034410480c1c000303408456408020400001c0c0d28002d0144004200c00502048540e030303100c100c249040c1009194010030000d840c0000d82d400c4031029001140000c90f2015080769a40070381c24014100000d0078061600c00f10303005070003592642c541049110046901040e400d5801604100340b017180031188554100540091340c0041e2640b4142900810181c60000c080c0a91020085030500240390300b16064074000c14402003d642070f0003090006d14245554a00c241d00107105440051419a1100a1010a440c695000c0b10381d2542010444201500011250112a000d10043d81000445100b410051000508640c000c00d040400705882c441d440d00410003411940c0d044134801d2901c220002002d400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 262752428 1250 262751178 262751183
    0x10090207061e060608150607080304030509091003030507111c03081512030703030c03090b04050d09170309060c0a050102120a110414060a09030c060e120102280e09070c 74
    0x30030b005116607400c1c080c800d4200315903080d102c205240d514001c030100403810a048140d001841000071200041c48200290710981c42900d9203510f4401120038410107400090a60b846051803040030f00120ba005000d446c44140d1004101400140d110003241d90708514210b40451071035001200420544c01041080c841e641000744451841d424000b0000380d000b69088008240d01304209407000300f40710f0f4100c800100390320f06004c100594103a58085c04030074202c40130740b89a001002680c01c4c0c250311a02400040003400c4201d42c90030307042c031201a2244150100355124040c0001d030f40c030f01d160701032104005280c1c00030300864842e08000c40403400750000716030034a61f2030315111080c2400c82c2032005070b809540c14483d03e0400b4014a9091201ca80c0c0a00751080c140400254000b0000f0071101c0321802404256542c01c072141071900a02c10958100d042d50103682c0d006003c49400707204040441007152940822a02403c0d840903019113521480c001215007284201d0104900706412910800300c00d071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 262753678 1250 262752428 262752461
    0x415170c060d500615070804050d0605091e0705011d10030b150c1c0e030f0309031014060913080c0604020a050108091203060307180c08060a060c0b1009020706 70
    0x3203c04820120343c2d40464003941e001c442065543d071080e038080c1c0500b004520640c200d515042d101c800141481c111100c0480d04180c9880c01c00690141c28801d12070460071180d030105505481c640e01c25182c24050086504100c002d91844951440c4280411000b8401400908290b80c0c5564010040c01c01c0d0b500040c025420300c81380c4210805054200e68150401c1c0014080103024403541e18045010b072030300300041010a440151041c0c0d801d210b210f02c500c2e040801140c3e5001c012050504000072911000c40551502405040f20315115901030740c03002e8101c03049038035640c0e04444c0300c84108140b0000381c40c4103004201ca0903080350000fa19130245000b1120b0400346c565640c01194441011240502070340c01c0300844000c40d8184401450300184001e060fa949a9100c0b40d00d03900d0002d0000200108030707210700320704080715002103506d50460015140501c54600b0100047c0192032220b00060407d00248001140c18201c406c0c100050031204206564405140c10b100010f4402a044462040e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 262754928 1250 262753678 262753811
    0xd020d150503060c120a0b040c090302011407050a171c1a0d12030c030608031c061403060f04050304030b07050c0d1805010c020a050415170c060d 64
    0x5180000300c5920940c4100160303444d001c020b00000e41e07005c02c007a040c259007640b41e08050b2100c0d607641c0500401040741fa5140110107196000042605012046a01c0401400c000c24800300f9400f00c1d800303080715041159000d102c04035100c0111035201e8018201700405130621840d49410301604000030b410140ca00045c0c00702040420030034020710f2840300802c980001c10705011418040d0300207015134601030400049044e610031840342941d200303c080c0300c034102e460100d0090890140c82058040c06c1c1e048607080300c103007180e00801d603a142e010b00b0040b0700c8080312000804008081041350f0117035074400300d4500103080000026005800a241101442c020f03c01e810741a1841136441c549650006654032003250f03c1c102c019180c0002c044416a0000518200480d00c5d46030f902608044030038038542c01c200c403032515a02c800110207400b585c45d0303160458069003034030b550340c5001d03251485441c0708001100c0b607401200ca50b001824060410105a0a00c16032814018a402d5416046078090307600390f25 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 262756178 1250 262754928 262754939
    0x1306030b040b06061c0915020f1b01020702010203030403121113051c170f07050f0609070f03050312270d180e16120203040602090a0504090b010e0c0d020d15 69
    0xe800360300b107001107003686051701142601180c0c01c0503155600a000d4800c80765440d11018003039900c86003407a401068002004220000c2006003c140f0b0382c0404001c40c241441940000c0d100d2001420290801028a0100c0f2030610075601861418603903543c82079844202c4000410315540a00c6210b1046030920f002e0301c04042520064041c5507030201101d031010341040c1c04203425821a40310740c00000014009480003480070040401d1000350340c0014501494030203459880c05c1c0c0c41d9000050844107200c810800182c000054644000309000350030409d56548201580680300074440c02e8801c1225003c0c0d4045074400320358046000605d0740c618500111015109040004c02e00c51026440441e50000b05c01e030030702006000d4503084d145005840082d4101161050b41c10948055034030315800a03462540e40340c6024400020442a0742c203200e1005180c42c0e211543c2014801c0900d6040036400091110007498100d43e0f403100c0002d4115141c0b00d049039200000c0c1840ca07066a045a0b008201165 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 262757428 1250 262756178 262756189
    0x30b06160f121b06020f0903100b031c080a090f0602180a050406050d110a080706020601091508100e0c0301060b09030601090209090408090103200c0706050c0304030b061306030b040b06 81
    0x141c07076240b10708040d141110341d14003000f5448500050407101042c020306145550921512781401c106000200d54180f44804040c14a060850141c614205036a0341e825000d4004801d10f92011200c103000415040301d040c141c9031801d5144004107031030310004520009075025118640c41c0001510340e01e2501d030721481400111a0140169544a0b00141c01c40b000200308400c6040282c4014040c1c0032134aa446a43c60300c3c001694200c500960040401888000794600c075407000401041000b0200c1d9141902c0540c94520039422075000703d89905044d000341c03c040000280460000d802000041d542d4403114085030442c400742c9220b0f00451000042101150003507511040d401007018207130351655521003a0399030045082605064451010208101035000581d5801c043d040080c0d07680d42ea1101c5041c00e05065030450b0050081c01d021182081d0b400000355004e036a40100381510680301d0350700040c038090b00740701d0110380030782400b002004200710384415a024034490b40d004141034484004102c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 262758678 1250 262757428 262757447
    0x6021216020a06020d02070c0806190203010e0606072f040b030714011b02040207060c230306130209060d061805010501052b0507081506040510030b06160f12 69
    0x60042c0c0c440040030001c140250b004041043c03034410300500d004865a994004110254002c6105402180801502c480f4021070501205c200e51401c600d1981014029038803210301030045c0d030103aa070200d5000208544c0d0405900e5941c80092694503121071454107500301901c0302c107142e00403801c225010450707040010702007003501c4801000c051107c40d0b0400440b01c0108070804444003504c0002d5610140c0c96074402011410301801001c01d181c8014440900000e0741c89905e0a010150803a81c01c1d545100312064039004070041740c6610281501a4825000e0301592507001d50001c0006031a40304a40e41d40e10171012030b440d18003904004c05114281d034040350001d1140a0100b40c040090443c1000400c0b030741d008451548480c2c200e1410480745040c101c410455820020500c1082800b200b038030040c01c580380000c011115075113481e06150115008001c2001810107150f02c0d130709d1010040c0d680106945020b01303500d01c3c8107120949400c1410564200d0002912545003203c00b00360030510528520 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 262759928 1250 262758678 262758721
    0x4021b061605070b1f091a01140307090501052109030304050706140307030c1205040b040c080d05090d03030b060d1512081b0304121110020102090109060c1e060212 72
    0x344c0603980c1c2042c603042800d0031080541c103540c4040c80801c015070140708290742003035100e07000d03422417a4090000d8115509031b07c2617a8070503802d00810080560100d4000e06407030081ca01280ca505542500950071103c0860f01c4480040c6030040060710307034001002d580300e54000d20442c1d682607034960054400c8080b18203c00c2c0c03415010000901201e0003600a901c5810007403501080e10082400741c8412180199022103940061030207110600ac1c3c00e10b1481d01610020000d098601c1c0d045030050102d00c1811075281c01101a803201500b81b5003e5030145220300030142c0000e239101c4503115604010301c11001c035942c000e11038040110356401104c60319240964043c0c421460814800300108108508017842c0030544400c010120340e100c00310406e140c85d00e114824120020039404100080c944091f110722045a10502122800c0d0381e0002c00300d000c842e1642811703d2842c03d81d0410380024170712100050802000046901c007040040d0f03000788026038414500302141d440b00244540320542081c2d16 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 262761178 1250 262759928 262759943
    0x2031512060c070f150b0414070f030513080313031d090f0907180c090503060709030b18010203070c03032315010e0307030309080601090506100e04021b06160507 71
    0x2d41d1940d882d0010a411401045900b40903846075881c00084402921030030440303511224444190b0416024a82404c4807003c240d01c46480e00d080f0050811000074a42420192200049180d00300c00308042c02100d508200c2c0c1c60f40d64949540c000d403181080c09412000103044400e2181d8802040041d64051407004080c80a113450360780d1480300181c4090008100c2e402810130001d5982d83c260708418802c401c024000c5a008000e0001030208003055001a011360045c07410011503d5000a03003009030b0f948400042290b84804025407908e07085032810150035032000080c8040d40d6000142404d10521076a4140f1410150342c18142814402050f44044582078501042c0740b6003901e9042030034181c061400403101880e80d80040c3c0b8110360b991003500401c19543d018401120b050021034050030300030f0418040c0d42018401f00f2146400707000c0c41360030420541650203060b916501141c2040c1501032540c0c041c1150880b00ba51680001e54040004c0304080c16500303c40e5000b1070a50364040d400030340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 262762428 1250 262761178 262761181
    0x1a010e0906010f2303060702061602120d091511071403070b0606030a1103100314070305030f0a1407050715020a0c050d020a0e0a0c0807050403051f0f0905010203151206 74
    0x3c0615814901c4c2891000d400e04115484407552401c0090f203100b0302d40c0d54014980e41c2055003800fa0801c20b0301c2d039100f086400071500c07503860110392012600f070803071070b01d60000e0146003d00300b02c1c582d44012181040784508020b20100d480035200064807007180159404a40d802c00c680206960f40704900e4014401028100001c15a16010b005075601540c1034902141040318075034100b4465200310f0348000e40c0000510140140304032619100010801c03000100360950443e250b9036071703900400d00340c03454a4030000b80c0b01656510170602200148010030980d9103c4001d403500e43d8561010b0f01640d1000f5a04403d9090300510014045101c81e4014081a100741e00f400f09100840070b4041040e07801c42c1900c40001100c0c5001d0604504c600362801000800c2548840b0013040356070050120301c1049014401440407075004a01041883ca1458074507810001441c0d58001620510800345509131400f00c20320180903040d001580f28020340d4104d5001080c00c0401c00c4112401c80c01604603980c000390 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 262763678 1250 262762428 262762439
    0x30c0102040617040b1b2b0501150206010b13050a0605070b070f140d0209091f060e0907050d11040b070516030c061b080703030603020f04060602031c06031a010e0906010f 75
    0x40402c42c41030b140c3e198003407a0017107000134a5044070000f0410807600c0610b641088241f0403a03c6403502518035540c0014004914242c0290f03115018040c20711210301c0029101030034000900c1000080c400901000031155441c880600380f60070400c41aa45d28611500041110384129155803c0508580300c0e020a8642048400981e403c03c14122407441d50803c5011019502d2030341e0544503150b10841481c00c0170340d01d1164600d81c10039a00403030034000d2144110b001c5a0f84c584449900c5402842d0480e154032074025000060290812059914a00001c000c40e2600381000104149030085040b980d880c05403414040718540c0907c0301070a07100b000c0d0024400c1c1489400d041e000120003010021000d010340e2140f540d10b0b8428081140071940d550010801c50401c0d01e40d202107100101c03010005180391003c0a07485e481442038040324040306964a4100321025800003003d96000030608580c07a08040c40351450607828042e450401000d08002185076200180ca14142e2b9a19248008d0702c51411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 262764928 1250 262763678 262763701
    0x20312280f14040b0f040f170a2a0305160e13030302090a0b0d05040209060301090f03233702030a050708040b270d0b010e040212030c0102040617040b 66
    0x1c4a200003144800c100001d000b9000030050f02403c5e003045400e84c1d44030310f41803030105840d00c15848000354a1000b9013041e000c0c40c0100c0d20b240007541100c43e960742307244104403603100c090030b4017030035194240c85200200c1401400146440120100820b0032101e686582c005a550201150422401140440c0c0d13840041d21a030080d050810000e403012540c5900c8207a94003c540141c01280d071481d580d401008294688024400e41000d03081e8004c102311502520780c2c40e80ba04a000d8041e0a000445400c10300c00d032f00250081d4404910f04440545504031142400c03070700c0c2001e04a10308444403216281d1161000440385200010440d0020741c60050700402c140c0740c0d80c008800942d6030540c144400071b0141401002024098240c0e10303a6500344400b40044402c2c02c200011042c0070710454505100026000c000503410740d201c110403524565694400184a11000025400280004a4501c0c080c09054000d00242d91668680b0031030020070207030f544800201102d010381400404800300c2c0c010310a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 262766178 1250 262764928 262764947
    0x150506041d0319023406090e150111010906090501110309031903021306020f010c030e0d210603120806010503160e030c0a081608012016020312280f 65
    0x490054030400512241d4000d950440000700700b05c240900c9041c5004490007035032407400740030320781001c5000c01e0501040400c3e5600046c180b8400029040010110740e001c0c41e0f101c9595111080280103031601860318102410003140100c0303103507007403032130f582c1c0030000c241c1c250382c4240d03403020040d810203d1400c4d145c5000307a075000310041455800c03c100040d045601c0705183c05000c0d80c2d0000c01e22100314101d12402c40c1ea80110700000c00d40b8001075401c0c007960100320903244001900e40303203107070941c56110342c449401c0f01121142c01d10700e000800410081a07041c8003e13510150380b41e00713030139940e11001585c0307601c42220101090603455074490a0140115000e03005620060b01f200c84800b0b40030040340b2040480c0d0010102e990149800e0401503030782d00c44c030001034282d150017446a1000804007592014001081d104408004950300f81900c540700c0e158450a83c00408407a2038030103d0340c1e800e8035030340204500e14842c4103820b50a422881d8100e40408060ba080e80c46d2109484100c108440c000b04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 262767428 1250 262766178 262766227
    0xc01050d090203060406510b1801080106030510060318050105070504140103020f040302010819050f040b07030c021c090b1209150405030f0306040603150506041d03 72
    0x30386005a00240c0c80030841d403440746104000c00078451100610740a140c3c051030a091221081800350142c43c0f07c4c551012048016400f0407206640c001d0700722080b118001d070b41181c568140d012603801c290314014010f980c9005400c1c0c840c07560a03601e658086050351003c41d840410b5401051040000c18031903404000344060401d200203010010b542e407503003581e100b501c110000401c00316003400365044564940030714003024241149804482460603603a40a1844083e06000d244000902c20b0252080d42d640b500300c000344100600d150070410200030040a0b80c040d110034014100203070303055000340702c5c500f1081800c1c1c000f880003410903c1c42e003482c20a110001c0c0d00708615080300045003d4000c02828100e080000d40780f5079441d164001c10702c0c01c1c2032040d810f10140d14140511003c03402c04000c450461001c601c10715601c2d0b44620104014008550000f0a010309003121168205001e03445940541002c40c1d06200c40112503883d404210b1900c280c0b0701d4950801c0010007071800760507100c00d20114 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 262768678 1250 262767428 262767431
    0xe0d020609040e0d1e0206040b0a0603050a06020304030219080d090302031b0a0215130b0a090b03010602010f0b061c05040c050d081c020307050405040b0a050301111e0c0c01050d 78
    0x46034200800e055418510b40d50660754030010309071316440e400501d070726540c20a0408071420072180344c000039a55080500003800342103000c40032070001103980d00034034007031a0800c003242d510120502d401c100941c001c40302640140286108521050742840403080110303005a1f0182c20003011700c50141c000c20206400300c0a42c40b082020b00c0d50340ca96076100b514504552005840d81c02c090780180541d648542482100c042000c20a405104174034808140949507403101c003076102c41d10394a00391212050b80d000180d950b40c02100000358140d05400c88540305081c040d003804150b02d4034062020f50f0003000050b244444034003040c2808024154007091340319020340290a0341607079032000300c0d581e2948034a0503a0781d05000513200c844094003003e4085500a4800700b1031039407500100c01071440c083c6006252046480c2c50041856580b011041009400700400030000303001960710380c1e210741c2c2c80342800418020f513080c00c03880f642c80c200c1e00362440b40c420b4a01802010350510b00440d81c1e83d01820507004d803103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 262769784 1106 262768678 262768687
    0x90c02030a11070503060a0605030d0e03060c0a0309080309010207052a0d031101050108060604060e010b0a03020313080c031206091302120102040b03161e0e0d0206 72
    0x340e0034580003102d001c1484490b41080d125a000c0ba9052040d40148010540a517000710210307a800c80031501c5543c0129010b8488410094800c1c3d0b254120200042004032094010550f10303d103403600007460201960740118940007a00c241900e41e40c04150001000410030100207440980782c2c030580b90010841c5040c580540741103c0724000d038030106101042500842d02594080c1c4098001e0040d581c6880d0800c6d074500b011501144a14185a000a900e00006d0301c41c0f4103958030501918508840443d00343d0281d80050480c140030302400c4003080201d10203001401054075400040c40e9141c450f6070328440c0b02c207005868180720350551014005c0b4841e0b02c16502c0362195050b02e20f00e402c2c400c5d00da501e03402401182d10901a4017030000400c008001c0c41103800300d55041c1600d0b042401c0303076000c0e252141009d0720000040440c000c00d564415610b40b1000d800c42d078a01c01007915140 = true := by decide +kernel

theorem cover : BRFrame.Cov 262589928 262769784 := by
  have h0 := BRFrame.cov_init 262589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 262589928 ≤ n) (h2 : n < 262769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
