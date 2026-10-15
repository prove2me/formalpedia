-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4817
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:50:04.979536+00:00
-- url     : https://prove2.me/submissions/a096fbfe-be3a-4d26-a6ad-63293ac82f05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 866187050 ≤ n < 866366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 866188300 1250 866187050 866187097
    0x1404050d1e0323030f0705030604290a050d030f05070c0f0b0a081e070f09180e1e100216050604150c141207170f01090e0c101103 57
    0x652040140c3c007141d02030740048402c2d0440110011240603941011181d04c0950b0340c01c1c0125030640c0000c01c401c0d04152a0b805007090800c04030f4a00d00c2080c01c642170400c1c42071401c42402080000d070351045108072501c410070408030340c0042011241a0252030640c3c4d40c0c3d0010308004038100c80030361015040c0d0b1820b01001505086000c01f0305160103441e40c900c00e0b2901c0700250314807042e03a035104600011101c0d0002c1000f4030b0213680c2d600020b4080d0f007404000c09540c2d200180309080322900907144191a41c4030150582001c1c415041001340e9800b15145500030304514541c3d9021500000f0b06140e400502c0910b000c01c443c40c2051a0340e40728080350640d02c1c1a16040e11928040c0270b0040e6a20304045824403100d0003205000c5000641c0c4c0c42c0181040a43c1c0c040d40303900c03030340504040d00380998212411058024102c5140c1300781384141c1001c00d194908401502150803601a02d031498100101401290b902c1c040c19021284135487d03c2200744031000062419485600910312440588501c01007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 866189550 1250 866188300 866188307
    0xb0403020d08040b030c09040f0c0e09060a0f171c0503190608010c1107140619050405120309150a17070306090f0f06050a120618140309030d1404050d1e03 68
    0x101c80c146c8c1d080c0b1000303030401c000000740e03050741c212200400ca01c207501c45030303901b880d400d403c1d800340000f1300b0080140d40e50020030303114008030f03048031400656510711600408010401c10202041c000c0305000c018041c07060007440c03400041c00124a0720b0451109403107940075608440090610321000700301d1480c4070f03200985020100e00203c0000d001d080741c0018000c808464440070713040c0180920f846d181002c000300340c011103240c4c04502401000d0001080b81e032100b00c0300820a02c1000000e581d6080c02004000131008031240018200300308000c5401c0c2c07150303c4100314410140c04a04004c041e1100b000c2580904941e0308980d160030b05c0c0405a041019283d00b00d081e418287c04401c00c14151240c041c0180d1410a0144854200d1140d404400003185580f00001640c44011080c004100c25a10240c40000c0900110300b41e500105156100e45402e10441801b424141007400c0200c0d034001c41c10041d4000d51180f10f12179180e000a0b0014840c4450300142d000120811646103450fa619002c1e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 866190800 1250 866189550 866189557
    0x603120804021311040e13120f0801080303070f0e0123090405090303060d031d03060f0403110c0f041802040612140d1704020303090904081b03040b0403020d08040b030c 74
    0xb648510090228000404540e100c0d803944400440e1410b4503080c1002404006100058003450380d103902c24034044013240c103c070340b46828180107030385d5900c400f0760340840102403a406800c001140e030020024000d110b500007500c44c40720301490410900e82c00d00e910060380d112031150300000c40b4441040c110300130020464010070b2400c1e800c490130030491301c4880006580b400103c0e06542c00201e207403811800700f8000d081e4110343c06044950400e010819001203410000241c40003440c0f0302c3d0710390600c000c02d50000d4002d410f80aa0500070128080560005040000d640107564080d550b5210185044c60180d030310120002d80207041441003e90300c1c074001c00407050074001614001d000b60010316900d840420202031230051030741c5060700c0031020052883c0355a0041d004036418842040500d950b5140c4c16480c3c0c0c45180100c04994a900704c200c3c147c800002d02508038409030300300700001c0c00b0420380c40302a10300780c0740c0586841c440d0000c1031500d044030b071149420496101802008003d10719003c18001c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 866192050 1250 866190800 866190803
    0x30606030c0206040c09110f04082d0604080d0612050c010305071805130f18120509180a1806090c050105070206090d021f0e0312130b030402040603120804 68
    0x3045079032200c040481c1c54a03800d883c0140505284002080412001e030041c041c001c00d120030032450151140c8030403481c7c2d8026407052502d42c029140380c020303410442e030a0000010766100d00001984a4420182c1c582d40000c20041c940c003004a8030741c0008025a0210000c0d280003088400130540604146030794141c4001078900290800c4000b801b840e114080410a200540e8115400030f410001003082c0540b92050131844203640d00391000901005008280c3c900e442141e58000049040c280480c079804214040e00621004106a58054581c1404001c59800c448103098480c2c40d520810005010318691b001003034a000880b0000388983c9900c60081c081c42210303c40c11940c0d80e07c0054030980180200a588010148141d070203505107003142c00207040c8000c0a035410301c81c510060340c1d94681212034140010780007001c84143e6080030018000c000000500050a1a0040300c25440440c03942c06850840c0d030000c8081411074440707400540c055544004099122010381c1402000c110040300d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 866193300 1250 866192050 866192057
    0x50415090c0512341805060a0f05130b0304051b04060f0302060901030b130b090a02070503091512040308060103050703093908030a1d03070e180706030606 68
    0x155071030103000c1c20840d10f41c421a0207541001d43d5545042c0c080000404c058580720000902180e240800e040d0400b48013a40d4580b65106010528001100701c500180c01c028000c3d007040241008035500010000d061126500d08036507102c01c511100700d03061907545d1004404800100501042060114440d5a403204811440484200340b20400c000d4549910504c01d05584844040c005818190700800130b03c8410704010a14980c03110202d01042c001812000f00300e40d5030404901ca502d032a080b141d41190429400f50300788522a1241a124810340048034460000b8440c1c0104c90341d603a01c02e803000000003500140891a040c107024001400c100c8a1a002034540b00008002500910850040340d410240f070384d14409100a03c1c468113200b0441c121070b015209502c100c5002ca414031594040c24003200550707255603500780e02500d1040741d807030703002c91641055194000c561070000f00081182d0f040d0021a0f0551220a0450690b80241c02c10b541c040c01510408190b41d60107411407003c1b519944d9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 866194550 1250 866193300 866193311
    0x40906020c030c1e0c0d0308091501060207090b01180e1e0c09090f1315060f0b04060206180a200d0b0105241207030b030f06060414090a12020705041509 67
    0x440217403580180002e0700c0c3d00480103140d40c000710303100b541010350240c1803104881c0759030040070301002442c0d0700f40d00c101c006030320004c0d0911609810340034a03100603400b804e00ca1440021108440c06c91442405502640d0b46000e00154600b40904a203c041901c1c0e60340401050510729100d0b00640d02c118015800f4503540004a002442c40c0d000b810700c601c074080d49040100845035546c0300818441e052800c0865100c0720b010a42d0a940c141d001c0041c960082160f540f1072030503001900b0b126005045410036036001c210607c0886012480c0b0440b0f80e44681c0b00c2c5083c00c525600307860b07540007400200d600315031038000c0e100c10041c2c16a04d007810784000721907000e0040f104006030f04d450b160f95610384a03580400c2c0145591241042c090a4102c201401d010410000071004245070007001c40c0927064070380c024424841d0034105403190880ea00f0030180c0c0f100a0386480700d112562a00141d500610300307501c11010110071882401003602a042c020803d1116801c800b0940f6520074a0740140c4247d145001c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 866195800 1250 866194550 866194603
    0xf0605060a231009080f031b0604120f030f021902011b0e01030e15190507050f040522060b0c0c09010e0112050f03030a05041101031109040906020c030c 67
    0x701e12103544100982660800d80060000e00c03900c0f00d0034609141c2480703041c040208120f02d01388030400d03041d248103008649a036215940c801342c1001d01003e82c215504880c0a010106454a8070200200818207285107010303c90041180108441c0d000364040e14804260701e9080030703100c140702840e4030141e8001d019108252400b0080103192400b140b002c9030000d4908081075003e60480c0041c03600d640b040e1406100da212024201d110100d40500710007400818540c2401304a101e101d0b04080c552806905280751091060003d01c80d50080130f00c10401d090b41d800c42c110009801032010400000b05000883e904c1c2c0ca144115002040940d505015120301070030b20b402c180b00c44034102c55048000c026036034070300250f4100c42c180807541580c0ca030161085414041c10104015402562000000280c1e403800e4185028074100c9004104d04150078541021199400c150944d001404100c40014039400c4c5441c216000744944884143d0701d000204200c01a1400815110004c540c0c0d03040c8524855000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 866197050 1250 866195800 866195819
    0x20a0f03050601022b0c050a032610062a0305250f03050903240105180403080a020a03060909050105060405011509140402270145030f0605060a 63
    0x308100d84007200d800461480c00950500c0c0302c3e501e00c08035418004814045a21143d0800a1108c01a0b000c01d24103a1460405400c100c040c40c00740708000c480415504021150151149061150500f00211a00030079602b042001c03d80d4186199040f103a4510001407a01900381e41120032598408984c1900c0c1d0341c8041030320845108030550011801c00310303040590f0103903041e03002146d00c80c0c0c061288507110300c1c10b40c08414003480d400d0a0004414525031420040001b802035240c00380035000c60f4031050000098000c00d920750048801c000140e11150f03c2d107807c400a024960240c42c01a09118401d01403041c19481640115810f443c18400d6a0b02d42114030380401090180c5030004102e0401013007610891143c40401c114001c0015161040f100d003035414803920107180c10036102551400c0081d40da04084070502340d80c4420b00d050340c450103004172031000c00c03038000e99000c41d20103200d03508034030002e0b11007040e01650380030208008056150800c2030007032000311000e42c002d182961b0040b503203e10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 866198300 1250 866197050 866197063
    0x20309060d050405031312151118060c07090e0706020a02030a08071b140f1906141e18030a0c050f0f030d030905010b040506010507140f01020a0f0305060102 69
    0xd000d452502a00707580100080900400c00e42d05400f00b4055007005585400440005210b04215982c401180c0c0c02c2c8000101c2d541d141b603c1c001031800410300600003501c801d403101a40120300c0700e40d459801001242040c40b42e03080888450240440c049010380855100c000b035000300000700d9000c1907c1c1c8000b40d03920011140040d5040d440740840100013201c20380108005480354040c1d40d148003080800c0b1424182540001101c2e0750a581c0014507030a040c0a000c40306002117468411508111034070074508100740c0501c2007000034100702d0b1018000043e040307801c00d000c003000580150720215000c80d844c0e0403a0301450510050700340107541c01d1030700150032918a03400001c1862030a00e4401000035682c00030000b940c010f95074640325001d40c0d40134081d40f41ca4a401d6100402d0100d0145892801c603502002703400c0c0b040d4680020b000a0b81d07404000d4a0000da40110310910203a4070074015841e10b030019002646560000829809180c0d00000151009000f91028021034903610016610f403032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 866199550 1250 866198300 866198317
    0x80321090c03033f040b1005061c02071b05100203120604050405160b1804060b070605090a05062a1206010315050621010f120204050a180302070e0105010203 69
    0x38000c3c0150000c0050700d0325104950004070a00e48554413421040340c035000d0308038030007152001030301c41080f040c060901c080d154040c20303140f84002e181d0f040100050b6580104180070100c04500000e4001410303040d070403940402d401640d0441003202120a8481c074144a001d1280107460800940e60b505000200751400c1c803100700b8240049544220034007004101c010419990ba2080e0b201c02e5010404c40003041024000000147d0f55604100300c107040c7d610030801000d0b0242d85817110170008409150700380d42015500160101d4551a02d0281610b4080f0f48203015000d402040700317100303030390703200d0884e00603000c07180c0d0081c01a500c564080d49a450017110f01c0d8030501003402000071a2584241c0c00040f81204032400000c0441d00c5c2e00c04101389800c800d4020301d20b0322902400c45108595018000d0050003101c3d03120258500301300400000f40f4030510001ccc05540c43d100420540e0700190400e508500600e032040042c44810f045c0250780d001d5500c940b04103100c842001240035440401104e2074031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 866200800 1250 866199550 866199553
    0x10b060c0328080112020d0807030e030d0c0503070b2e0305060f010320060d060605043015020f0703080601170702030703110c030102030903220e0109090c080321090c03 74
    0x40e0300e003005c01c01c020342c10381c44101d80c840300001b50f2900180d03011018041c0b0328004d0780c85160005252062510303040b181e581c14030a0284180500001075000402c40d045240d210b03402108903121140030103101c00e080b0300b030b01c002d0142d04100b41880e5403041d04400c04880c098001c07181d464a0f00542002c80040c01e00019040309186002c4450102e10500100d131380c20800b0b400c2c41d01c0c0140011390101154110b400600c00207500203010009603d882e64010700c40807a84a07070400c00305606013aa6985201907078020320b850340304000c40e0070f000501c1d415100e0b400b00910101d43e480401c1c0c1f5004207948811a40f540c00700b210201c1c0c500c4540c1c01446060b1281d0b02d20b400441c90b198654030260340980882c501b4507200d1050048a50451720700380060b43c0643c00210080da107903202d01d01203c0002d11481d1035000c050008010410100781f040742c0f40d50440d001c0c03540001d040d14850422100420140d08204180e2000052410403807900c2100b4040a08004540c18103a0300d81c00c81c4140ca030f203880344515034503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 866202050 1250 866200800 866200817
    0x408101a280b07150c170907060206010807150f020129011806080112050a0219051e01020a152c011109032d0601030507030c080d09030b09010b060c0328 67
    0x24070380240d00c28042d1170070a00304051a00f1200c0c01d0110441d000702c50310706180c0c001502c2001015010840b05001d85904030282c148a03080200d2108010b01c650f2000040103940c28500075410b00030360208002c07140d5140d8000d48800001034000454030000010340c0010412030050302c80c040c4613150f200a17034440303aa510503070783d01e0205403034000f50f07000500f50380c14002d50581c41c0041c0d840a00301c03549070444902000200b843c0c03004010400781c1d40f048444840e8000f8050041c2a1b0b404510703003a02a0780000740d501c541c01c90380081e000400000007060907a6960300d02140300300d40c1c0d041c0306608981104c0000e00c080c142c0d10f80ba400a6001d00e03105150564000340400000c90880080c51000454100c000000007172810070342454480280d1041d035054001c9107080c4240700e040f16210014014850041002144105004103103c12a00c00501500c0f64800494100807083d003014805590091103191143c010442141d00c0b54014001c2d2002c1c200c1c804582200510400c40101444806840301d001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 866203300 1250 866202050 866202083
    0xd0203041809020d06021c020408010e0d110d1209061802040b01170c0d0b0d1b0911090111010209120705030106120308040609020105090405040609110102030408101a280b07 76
    0xe034000140d1f082049146044803000c1c08140e03c041c000410580d0004902407043e05040c80c246000c085c000e0040110800100543c2a000628018441c0003071411441c0280803003241001000482c034018200390400c10710fa40d0007540b440f0310949080c000c550802c003e0509400540f0012030680b1000250062180001c1c3c00b15460406402c070301d8448400130602c44089000500100c401400071114441c200c21054600e4070881040720240c10141d50800c40414183c2c00c2990b80c1c0203140101d8104a50f10f01e80c403c200b0400c1d01960042074001c5c24003807010501403c0661144240d005d0345004e986000ba00203491401e0000a20120790035031201070300c503220750325110050103010380d0a030b040c480704000b1241181c88030300c9014403c60140c5800202c000061400000b484101204c042c11540107000038400c2d0b010108a0401c41d0100350800200741c12607104507030949090140140c0e000d00540c40b02d04185000c2c1d00e801c0340c2d00e0314501c0d04114a075140e4850a01034040c0031b001803d0800300d41844003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 866204550 1250 866203300 866203313
    0x31e111c0e0f062b0e06010b03040807020102010603050d09060201050f070e0d051f0501080115030308220b010b03040b1006021b03101b0e010c02091f03050d0203041809020d 76
    0x60161800340403d458080301e01c003030601c05880540c0d01d0240000060034249070400d184290307529003003128042d048551409210100a00000c0c2000e4401c880000f681c00c1168001d40c05400116401400d482e03034803c440384094040c411502c100800f5500f40f800003803101d0056000c461240c4640d8581640480f50b8106103c8a00c0d50038104541d01d1051b031806038004000304450014000b1800343c04100ca41c10088401e00392421090b8010100841c0d900510000360048840c0b036100b01540c0142032829500d80d060801e2082d54240641103031805000401d02040c110001c51240b13008030001040d54850300d0360007410107650b100302c038010780142030104480c48410250103101039000f000c8170401c1222040100c1203070310f5203c03420300c0b501c0040e40048032150440c0a249111800b401d101400450700d8000c40d040c5c0d0b01c002c000c80e01100010642d1441180003541603409150081c1c01c540c03503004552000307943c81c0e0003809082000c0111020015070401c050150010b0f0b107501400c081d26041450f9541d6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 866205800 1250 866204550 866204569
    0x6061e100f0c1401050717090a0209151e0307050a03080a0f090b03150301050a0612060905010e0303070c03300c030b030a0809041d1207031e111c0e 65
    0x1000c00007002e00c10008a0320050502044074001c0380001128200030201800d5022085101d59418880008001001101041d0703520601d405071640c000c5503440e20340c3e01c001c1140302982582d000c2d43c2c160012280c0b0341c0300c1c80020100b00d01a02200c203065100c00400410606070320005020510400c10006650320030486c04800315054142051070644032000030350076070030403100b420004140000519851909000f095009610560104070385402d2000340b610f140c0c0e03078540c00707055162201900400c01200754230200070315903108207494503402c042c00e0040c10500228016130002e00c4182035100e603201140b150f045003a40c0d00d641040700420150580c00500840d1203505c003031550310071003176907252170a001d00c11481e4421b94000303030f94425107000c0008440d01414400010394985102580324440051015100300c0c0d44010f0075240c3c601032408840a8840410005500c405a241001425003020a444c2030160790703010fa030b9003003480c1c0c1601408031340c2403142c600026040203038648084c1400940d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 866207050 1250 866205800 866205827
    0x3010e1b04090207030c0c0b030604051b0702120a0b0705190e010e270108031209060112170702040603060f0f0b0108181501030308070906030605090420040e06061e10 73
    0x746e0003030f1a0035202c0740c525085540c04003440d414000200500d0b0711b0180314860303104500000c5003414480714500e50b41d1a010f200c0c00203000721510f0124810303c0004004841c0c60300e038010b00b000c2a40c50801402003461f00104007441c1c03420700100b1540380480c0542c002444506042c1c1d1500c05c601d4102c0f04008114040002d0300f21a1182c1e4400080240009100a80030380075460040d41d81e0036180a00d000d01d0b4800905100c001d40003440140110f01c6009950845603810a907203841a050103040d0003402e1040ca0310003980185003800010400c00160003412f1407290001c820003045150000c0b00e41500c84a51f0b0450000342c0240c00201002e524501e01000c0802e49012120321a814043e0006180720a070010340c003190400d4100644180c1c0300011314013928262509200e501d1a22012600f50000500002c0c220001c0c0e500d03480c04000350b41d40c01509910014824400000b11800d520b450b54019144c490040e003440000304124400207448043c00240a001940100d403107a4049440c1c802c4a00c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 866208300 1250 866207050 866207057
    0x8010e1005060f030a0303020309070806100302062b0b04050a020a0c140f1006030c1d160e040903110c1801030f0f1a06010206180309041e060b03010e1b0409020703 72
    0x2c0400c99480800417803001900c6510300590781e05003009128941161944030080a901c51810892081240d41031401102c2e4140e44550311140d065004004a406036121420a482c450b821156401c48503080443c1c40c040c15182003043c0d84404800740301f60700c0b0f0900e403100071680002d8403100003540300850000079603104050b51b0845114072036850074101e02c0c07031310503090b0740d00c88205105020005500c08000c0c1030300a07440b03441c2652508a4107036058003c102d0a04402c068180c000414011901e043c2e510744014020064503403d445e000d00f04100c0940310081520039015010740500300303c134001c03400d11205201e80c8001d0380703541d0395201410500d2108441003040c4048401c0010745165207000d909101036500003245c0b1707103032000910781040104480c000070b0550f485428446004000c41d07845450640c3c1c00329048082e80e070004070541c0308030a1034945501d040400600480d64501543c10b907810360350780b81c4c1203031120034500b03651108000c6400d00380b50341000300f0480040303070b64010041e4511030304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 866209550 1250 866208300 866208319
    0x135010b030106090f0f020316050a02010b060a020607030507030e0712060f02030907060e150405040b0d0b09030c0c040204060f0f11100501150f080c0901120507050c0708010e100506 80
    0xc0800d00b92030a5521010045446010246000180d40070f00d800301d0b03011200450951514200d0002481400f010300c03c14040001900d03035845100b90000d101e843c2c00a04003c1d9609180c0c070009640300001c03140000001d1900d004a1126440307030080440500702c0308020090f03141011a4140030b510240c00403500340e6618084428155040d0024610458004c80a814102d2420b079010b40620220807010b031007241c3c8000b00b01d00b101040030a550aa400c2610700040c100c60f80d6010031220b1080b1040540300c000003c08114802c00008020030145202d9401d40380c040a0103403c5c40103a000d079018003004140d840d81911102c0780309a80301c94182c1014a841007806404040c0b075030520100c6100c41e00c2c13540d02c1c0d02c014400b00d14292808415a250352030b00b0b2040c5a0310440042903a00c0c0684ce000c0341e44000108035906030b10510a12444980c81d00c0104002d04040402829a1307001d0140b0071400d009034500052907100600c1280c0480c880c01015280491065550b90001e00707006203102e1780418441c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 866210800 1250 866209550 866209571
    0x61404020a110a0606170706050f0702040207050609010b040605010503090303010311010203070609030519110a0b070c1406040506060117011208190804020406050d03050f0c2b08013501 81
    0x104205840c040c081c00c0001009814113440b5a0411b5501c150b0756202c0c1d001820030020b0550080460310f0512080c5550307511944e4520018000c1d10a0700d6024040f44602010711024603019400301c02c000301e04540420059a440f801581e171400101ca44a803590001c0c0b0040010401d189076103120b0a02c140305407403400d4a01d5603024100c50009800b034000a4000c50062000b05030fa52842040081c0743c1040e42d004040b0415140c0e444400e400001d000b601c16002140090340126184041c0d1030348904200715080c4a4083c160b85c60504480541d01c0f4032402002c103034130354000d40880c0d0009202d07800c2050568205010030002c0f110860044074428420450751100c194181045030064500340d6480c120383c2000e00401c403c1d42c240da0415485095482d07034840020b6000400c44a488201c1030310310f40c640d911390900d542004640e014090415113030203100d8403015000144825000c1103602c1d540c0282e600c44401d445001054801d182e010218101c3d44001c04a1200c50709003002ca40308004649008503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 866212050 1250 866210800 866210803
    0xd170a200a021605030307060e071d220507031103030f030103080a020106081b01031505030304030c06080a0c0c0b0603071a0d0b0d02030303070810030b16080a061404020a11 76
    0x1514900400031001c900700050581c14420f114200f095403140701050381c140000a600c2c1e21581c0c0008280030740d12002c03a0005142400008020301e445016060010800186401d4411084491450311766171041c1e010480030110344000c01164000c001000d84c18119910440900014100d0540c1840103101c21480400d0740030003076020314410042140c854824200107825203440b03811980c00c1e40c001103811078110103188914030741d0500c00d00c1c020580c5020390710188990100d5801041e05400700190101c10f1142c0c000844c030803901c142c5d4500160350b40341c540000840d044416910000703001c1200035030115000351001070300701c0c01c0101601e01940d40c0c1e4455001e041003180e0240310083c07004c11042c0c0900d0080c8a55a82c110054904e59601c040302c1c1c0c0029164440100b68806200040c004a1200347c41601000040d5a108a421509051000b5800c8844c401071030742600041150002611002035070040c0c00403206200c070100384a04521081001035000544400704000803001a039008000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 866213300 1250 866212050 866212091
    0x31921050d02030403171602101a12160b0301050f0f0103021207021f1a040905100c05090405150904030302160506010315061a191418120d170a 63
    0x5c652a0b4481004100c091a011801c0c0144111502c0e8440310381d0046250300420002141815076000003000e0781c035522424160001c0303400ca00c2d001151001410f13071010b000108010303401c680701c65a00070a60781c4c0000703c800784024000c598000c0c941c0c85080e041420166020b0320352400505016080075203841c540d40d11000111180300040c2c1c080e4101d40e0701883d400c070200490844902090002e01c0b14409031701c00c8441c080e12141d01441d5154254000e201003801451184204140180981410080700600e15005104054031861800c0c01007001000702c4c0c86000702e1130a001d40404107030359661b1800e0b0020f4020b0300c10101d49051168072400042e0301404418080c40c030403081b13000035880006070350044807902d8100c3c038002102c58148036141c2c045001612641003101c48080b01d240100c0e0400c1303030600e08100c4541905000400e0b0005125115080c2092000c0242d0b001500140785104c11a80c07465020b12100c045065000e020b4850340072081c1160740301007141d602248041150758079510700e40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 866214550 1250 866213300 866213303
    0x30207060b040e010c140a02070302100c082212020d15020f0c0708010f051308030a150801020a030f0606050909060a030807080d06050301140f04030e0907050405031921050d020304 79
    0xd645802c0c4003006a00162045d610007581c003507180c1440c2000c200030f5132754642c902010781309010301840c49503050700c1100280c0c0215404405240c0b903c41202064414601d891070484c0044282c51012989800311003401080940003000d005480006803528589651349000c6446090340030400c0701d10841801c0c005043c0c502c00140200480b52a21049500b1908106025070016082809105049040d405190502a00701c010b559aa45550ba0000e009080450000d1100c0601c88400681e43c0d8043d8041c11829640d524148801c18a07040c2c000d00300c0d0349a001d02c00204000b407180114504201802681c07201014050100e01601c986450380f15401c1450120b4000e90001040c0e68010201c3c0601401408103030000d001e1002034183d2021304c0107008043ea915020218009000c3c1441441140751180000e80804040d041c000f0000300a64414002c4074040e1280203c44210f075a14505e51003c19600540c4903600301c120b6400b82d110b9041d070f01c0740c06410072006010b025800c84047c8011400345 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 866215800 1250 866214550 866214553
    0x316060e161202093403022502033d060f0b22050306060d2a2c37020d0f0507080c090121020a17070e01030207060b040e 53
    0xb140148100100108002c00c80048401c20358540201030300c400042a0400300400118404600ca81000300c000303003d4440d0245102c070540880000000241303c5000581d4003da068901c10f08a8010109404080031103e40240c00e03000c10144060207480d2a28094000b42c8001240b4179a032061402414100d0b83c0048001000000d001000d1000141e4001c43c0c51500c00b008460b00c40c585000603444003c0280014003e0787d9600f5071004001c0303080803405100944000119115031403005580d010695030040405000c88000b0340d882140304803103100404159448103c1c0140d440d00b035160b07a050080510320710b1180c107e0011081d1130060035240705200f0928800180c440d84142d01c40c8007510b0003c0501445580b600d007d220050b6070140c0d40540c402560540c1c55516079070180100d0312207045924030091510181d61f003805202c4103800800d4000495a11080d1207440c11a942c51428425140800440d058013184001c0d5406034003e400380e1402801e00040e8904210f0119040d81c2243c500030f101ca = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 866217050 1250 866215800 866215829
    0x7140109080609060702070f0608070503071b030807021b030a02060d110f0310060306060206130503043c06200705040c11060907051804050705030a030c030f020316060e16 75
    0x45c55040000d88001c00c5586160301d851840c165024198034030140031034041100c0040080c4e5042d0003000d0844181c0e09802403580c81034402c1c20001c1040c4426104c500050040c12412038074021801d5144100700bd0040103842010200e03420449580d0100101c0c2042d1070f150010304d0002107550001c0c04440d80c8150301156603180c1604940603590290b00702d24145450920240120b9a0004489034400308001c285081a859420726910b1405036501c9150f07448001d50744221240c84c20071341c0700030017105116426071407144841500341c882d80300d014240024501e0705001c8241502807500483c13007514041601c01c6551114040350686441d10754000200d0061003600140c080104460b03a070043c0104090b0104030b05050026400d03400013007503044007074000d0001c00c0a0041c140803a0000f41801011188406607524002c3c0c106465403500703401040030b110b00780340b8060020046418001c00c0491021094016503610001415507003039140152280070041101800c41d4091040502a884102d80c0d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 866218300 1250 866217050 866217061
    0x911090906070e040917030a0914070303090f05090403120212070806120f120d0f0c0c150905060f04030c1203020301082b08220b070f0507050714010908060906 70
    0x1d0031480f190300e805985001901008944085410605100044081541d07a10b0368100d08001d00142030016007240c100810070445020700007040c0c01260b120362900004075645130300b4960004c0303c03449041d0b0440408000100040c2c0300d60f460001040600700018184925000d4903d0030750310854410000c5020b0605001c0b191030721005400d54150484010312103101000240c1c0c0d103480b800b028a070360007040400c0607640b8840f140c200841022120710200145a03c114009044024020302528442100a805418242d003809400c03841b0303420000400994480c4641e031440700e034001b4800e500300000c0403607100005500d9401c1040c99225a0f8000d41c5a5041881c40c0b41821920000041c48000d140080842343c01e8042c0802d1025295041c04e54842ea0381c40e181000d4503000403400c20140800fa1810310801088450990007031001e903a98404070711060805440910075408007500300d034407110b400c000c444048960380940010615080c0291130703503507450720301d8041e0a860400094114404218 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 866219550 1250 866218300 866218307
    0x1090605010e0f01270e0f0103020411180f0d240e0d1b0809030616090e01050904060504140f0106140306060a140d02130b0a1a0d091109090607 63
    0xb0a1140d003182c800d14205480300000c0c4c0490580b03403142d8070740e4100780e00380151100480380b210010501c0038051406440c0600800c8000282400200c1c812490120343c03448039108042a105640c03800211b60300074282400c10000382c00500f0440b25448101d002c85200083c00c41c40102c0880740010440c19002c840c2180c10b402640c0030003000c41101c2c0d100d00c543e5145a68804001180c940c45440c591949580b07509102a03140300d0514019058070611050100401c203402078041c441c3c2d0156070303c00304c607511094841c80050080c0b040c9a0310144c107001107400b04881d03500594105210f190984040001560203604040380301026684036551030f80200062160504190302d43ea2003100034026a2500c0f50020b503203402540144000e002909000380c1090304c0f50b20240c840c65030001c041903454854a00543e0182c50b05a42c4280545062000024442c0d06030b001c01489c501200c2149041c4003d08594900510502c030081e919000d086008c881d907502d6a5180c00e0041c400e64002e40000d00e407024010303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 866220800 1250 866219550 866219567
    0x60e0a06050402090f0906130e031c020f0d1503120507051c270f030b16021605040207061103010b0c1902031b01050d1a12010e07060c0201170109060501 67
    0x140914010031000400745c0c2d511003500d544500860f00c0284a44030304000c14a00c0b50b5042d101d41d951803910f0f2701c0b00c440200c00809041c0c1100d195070241c8145041c15015401c0c0e000b101700c0c900145c038050004e205400c3e40c5401200c07082c3c85402094a2a664a4507843d20a042c041d04d003001141002525100b40001031040109480390680b2603404c0040407500240380c50000b0000c042c4110403201c200c4c14050bd0780c0c100303500808c2903c5070f8030940d50322410702d1440420143e0b0f400e05210980041280203d00205100300e40788020b180d02500c403440c0800f4000030354480c2c2c0c412290203684210035100081c4842c0610b000c4d00a10602a443d8082605424030704018080803070f24110b2605c84031401070f900015180d11060b01c00301a1a00100070b0401030f2801d004140c0c0301880c9905203040c100039110000c003850324030b00c41281c9882c8420042070000c1d00302c0e05025041099038002d80c5050020500607030a80da026441890042003100b030f5640194018502078100140154031071108000640c0c0c4001c0a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 866222050 1250 866220800 866220809
    0x807082101061107150804050a29061f2303090703030206061503011e0306020a080f010621050615130305060f01120212160306150f080d1b0204060e0a06 67
    0x1003813054284a00f0030080c4820115101c10400c110002600b0020180b209540301ca031b20110460106400c29a4520300b42e00703d2043c0025120a50f0024180d40351051502d90600c0290361051144e8000500071101e0001c0e03220541102c11410f22803801c03400c0c80314000e5100c2c241c03540240c901c8500754940241011000b6011620811a079001b08001c02c0e0400308690440d0030b001c4039102ca05c60341040d410300300d481550020b42280e1000c101030b903101d81c0020066103d019400c44140050780c8428040c1c4000c2503901c501c82c800c0c2c3c04403074101d0a07c2c4081e8003241d0860001414080324103161079141200d07034001040c1180321181040c0400411170704102840c3c00c0580c001c5410b0003503040c41e0045100c82001c0c1800707446464441000400004240b01ca11003003036918090080050700d03400d007840503210300c41e4030b402442262140050750700c0d51246e0071810307180f042c400360000315940d000807030300034601c2030300038210061088050f0700507074a43c402c0c80024205030300031100034a03100c00e0110032299550b03c0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 866223300 1250 866222050 866222053
    0x203010f02040f0b070f0206030a020d2a03090c03020307031209050108250c08040f2405160c050607150e0f0c2202030109023408070821010611 63
    0x20501103241d0f4003002100303441025008603100c580a042400a4400c25003000e50010303070010602001c14000d80003440004041c101c03e10101c0c04541c10510030700070382001c0d001011141d040c1106d20303500c00c0e0041a0114041c41c0c0c0c04c05282d0302da0300083c0c14040030f94400c03100c0311980440a0310321a00000c000004040900304649035152181440c44092800140305940d000140400d01810740910b1100030782c5a00308010f02d88a0f500c1d04500c0c0320042c4a40070b80c81d20b4880ca201c402c818400f031411040205107550740c59a040965107840d002c841489104205d94140800c98045601d0321104041c081c01409000903400c41d4000c1e10941045814005004655803c208090306030b074540080d025000703c2069906840c442d04080620340b10008030382280e01401c3c0000000184641e540e00030b085030480c1107031084620620041310400e80c480f404041c901d403c08001e09403012078a442c0240c000c00340220141031030400741c119500c010407904a00a040b0490940050180720343c441245007101e41a0750 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 866224550 1250 866223300 866223307
    0x306090a15150219150e16030206030414030720030a0b010b0a0201060902120106080c19050a0c08030406140108030f04090c030b151e0f0909040c15020a0203010f02 72
    0x30100c001c0310180c0a10b5948101100814a01034420071403018a261803140052444540e40b8101d00a08800320b01c13401150f0a02c3e41c1c5a041c000701081c038006100d41c40440307036141072445c1c3c00e005a030b0f00700400c142e038021101d41d40641d034031006000901c00c3d103100342009841450300c401d481130640102024640240e2084102e0800641d42400f1036064407044040e198654540c502e0482c098841074022a03400b500110b03101e018201d40510f01030598690707481c0c89070203a5904040c02014000d4000d01c102044650103082c42444c0a20b00a001e42003c1d0b1903d844104800d440c2d030500f5500c141c808481c40b070740c1e03a0000290084030f500040d0140c00814095890560140141002409240260580c842e901d07910b00040c00e01a52107824829805803404200c001366070404505a000405090203150b44510310518280c0a401140d03011030740c4400c16405c14241606100f141c841c001c5c011240c981010307101084144004040c2016004158010454110188107050940e00d061201061050051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 866225800 1250 866224550 866224571
    0xf13020c0304060306030203060f1302041a100c12020d2309120f060603060c250218071b031706120304090204081603121202041e05181b0d0608120306090a 68
    0x1580e00b520708cd8040341c000c01c9480300300000920b103400440301d60307074000d03484080d450800740c000445064076402180210034050640001fa0f07200d43c01c0b02c02c1c80c0b000610781d00c952005810020010007502e448050058103029510002c11000c0c0000051f03240785521220000c8a05001006000d61000082e0064a50740c00c00b114240b6003401a2501202800302d08005124540a0b8140502405400400d10401242c146240d2486800240e6800e000164080c0d030480c0c00e02d03a100700310312459900d40d0319101c00003d0307500192808074010340440d90219045a40c907505da00304202400291039401401603a461924400d07600d00321040941d28041742052208001141c10102010000307100b9041c50100039801c0070000c0000d2041e1f8006c80d030084604951a0385131140000405c0c06d0303540030b840a10020840014428660707008841801403880600d0021520000f2007000e002440c010201c00b1074070540760f018190810040c110745202d888030110410140b0b260207107840781c200c10400410840224032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 866227050 1250 866225800 866225821
    0x1050c040e06010f21020c010c08040309240305090115060518010e060414061902330117010b0d0f0204060e19050c160b01030303050903090f13020c0304060306030203060f 75
    0x8000031900a517a4010454600990b9901222050400d450003002040322540010b060f080040e1404e5000035040540810440006120380305a8900301c0ba001d405115a0b02c402c401401c070080c5031902554031600040c22030f1032804a07000181aa43d12140c1d220008802c520b02d00f9804821694100800046504e1450f00c401080b6025200301090444480071440007207406c506c9100d0b654000e45e0b000320004042c1303581c049103600401c40c501454080804180215414440d110340701c0c4207110b0317116001000b1754190501202c8156805800100340d01010200060445c50012401da41c44440704014400718a00b610500025100c1d83e460007400342820030401800c0c01708030220103076490792000402c1c010049403003511210110040c640320390207118a0007140c130080c00c0c442107004c04e0070031001c5040050048142c6404007805403a0440c04a51382d801c00c0307404480e90100d0051664200b041d1040e44200b40010f001818054401241440c90351041c14544078000b042814014100000d002c1d14009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 866228300 1250 866227050 866227067
    0xc021017070c0b0a1109040c0e060403050c0a150f2307031d04090b01090207021801080a050c0603090c0d08190c030f050702010c111201061413050601080c07110301050c040e06010f 79
    0x1e46001440c040841000c0d41c04084507200c1d654850004a2f00000300400001d2041d030048083c0d950f80400d541d10b07000c0200c294640c200000c045108080701e400f01e2403044500b1030114807a0390303070400d801840e240f0101040d407080101fa0006500c11115036082e8039245815400480155000c01c12884646c1750f1310101203040c06035402c05500024840159501c0001050740d409150102003900c0d6511859140c0c2e851900904a60500556101c1c1c23001d8607042090304c3c45462004003a0039041c01e4942048001891102e00301ca088100303000101c031000403403540d940800c5003070f00c0700403502d04981000744c03840e081483d44c0020480200162030050340e00c4550380c225140d0191000c50102a604000342810144094203a030302d41c0b03010710008494207881d02c60045110140c0f0041551501255008141c0e03104030b4000d404603408001103400e59104800501e07000d40250301007820403072600000782c01d64100380d40310707030701d8000204061110f601c080c0c0c02e040e007000007401c0001e40c658151a01800c03066 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 866229550 1250 866228300 866228317
    0x1060e0403080705180303180f0a051e030a05161e0b09061c0f0501091d1b03031608070201031a010212160605130b0f070c021017070c0b0a11 62
    0x20104105c2075242d5040607005d41100c00800740c0e61620150311254070f1411191131054442c1c45070354220032103410300700d8111058810141408200100f11201c2c3d25048070703000d000c50341500c982e41d005008244188003030050498403502d0701c045280303824003000d0142012400c03244400c00c1240104405040002162001003041e52540d0316180c46000044c41403101014440c02c9904121203501d00c00302e0317984858142d0301c2e50a020090780b22041400c40b0f03900b441c1c144180c0c559001c1003e03145592a10207455454030401070880c2d10700901030b61a084a0004040220b40c404e0700820510b04641c0c040c0a082c484501c0c41005440702080080000e688101c0342d0b83c0d080e0f0b040800904200d00c4028040c40740807044d0024000c1c03020703003010700203003910042c40e4409985192041c0046103a0300501c410703007800b48056a94802610040d60200310104a011600005218019048000300260b024109201c1c0c0307119201c40d0048102414240300b2040c0003406a0b000b940350100c000200501d85042d141c10380b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 866230800 1250 866229550 866229557
    0xb0901060f0804061505030f07080715050301210807030906030f02072012010c0917070506070305030a061511010606030e03070f08040b1b07080106030f06020307140a090801060e04030807 82
    0x61740c218900040504150704a960580508190495080400a0004110360108017154030095a4032400d00400b00b480303440200080e8200010000e1800d041d00c00d50300c140031072000f00440b0043c1c0e81c0c0c00c0c01d10362205004501007409198100103a68041c0b04010b0074892801d400d41c5400510380c5c440014024041081e10910b03040070b003407815500e801140000e004000740c000c03c98407420b03100c05080c02a05d8400d5074840058135401010880011540e08111407016041501341001e0f6030303098590ba0002001502451b51b100400074180c070318161024000300b42c1c4d8984142e02000c01a00b68291070042c0c00407000c1c90b0401981e1035620b100042206c54582d0001071022001032140341100c12445903500101565002140d00800d1960400c2c40c84520108001154070040c0d803107107070b1400d036040c501c000740529400c0c0c0400000303d000d540056501840628284010006455840549130400031410001403030060040c00550390034030605010b00b90a00c404915441c0544d8018100c420060509080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 866232050 1250 866230800 866230811
    0x515010918081608180f0a0e0c0307020c030d09060810030c120501061a031009050c310905161106160c0f05034501050702130b0901060f080406 63
    0x8603501850380c15205a10001c45643c80c2620171080e01c072070b41c0b0260002c2c441e07456005040000e2800c542c10108a0f4045030082c121030346c03012400180ba0b0001040d0b58154083c01ca15a91195014840003110511301c0c4c5039140d255051000c0101518001848104924201d10080c0003044271041040100c4000e0800c10354054082d140075400341103564802601031260b007130a407101080003800385100d1840d40d21034a102907911003000041d0352055408040d189020018900b4050251501c0000b081025100994100c007202141141586079400318242d00d07a00d030306125105c01c00b03590a94000d080380c5400d03a0b680044054071500c1d000e024085e041c2d0080a41007040495000703101200d01950043d01414040001e41450f5850380c0c4000c0e0300c0249640900086000c04210380400034950008a605445200410300003030000c0400d003000505000c014043c0d200140e46e0031225100c1035510200110f26201c070081031020000041c0c04c85402c0c0b02d031150403501d2643d44545165030054022001181c8c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 866233300 1250 866232050 866232067
    0x201051642050a0213120b0619031115030708180c013204030b150103111603110a060917310b030903130b0c07090e010216051501091808 60
    0x901c140706841005000c0398000242d140d485c40b07840e43c0f9050084a0300701e01c55448d10b040083c0c010a1591040c4440c56549041c004107400c1112010500c101078030074044244124902000c6410454104000540c198108542c2c0040d0384090810b06103150f0092020045080001e0b24000785c036054403580d80700001e841c0507a00490115042e25a410310302c456a2991207042c5200341040445000c00d229090019229141d403186c410640240b00d11144281016103c24055025040c1c4680640c01c10448500107040d0341c200340b106440a500c50900000c2100381483c0804414016200011a00c0d030103022000d8040320182c7c0f108608241d50162200302c92005a0791506001150030980c030b2420048108140c0c1c1c4000001007661658140d0190042d82d90740100d070190313105c0c1c49500402600030205c200001c4100d03400901000140d0000941006c1032075000c0e00c6a0102e00d90240c0d03c80d03005010704038070030328aa520103015000000c0144254032100c1282e485182c81c0c0782c07000744140320000d441e54 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 866234550 1250 866233300 866233321
    0x21b04060504090f1109190b040b090c07030306150e2b0602030603010b0409050c06070f1506060807020c011409190f0807062a020105164205 62
    0x20290500600030050740c040341c107044c402d00c03040c4001100c0b4203d20b000e801d00c2510b01a94142d01c45c001000c2d51000038050401f0040140c03202d141d41070f4000382c54046407500c0b075840cbe0000303510403007203064120340f50402814000d0668086502c0b001c1c010b4499108240110b40c400c40c0c1101c91241a5800700059225000c00640e134600043c0c9c0d02c42414414079000100800c5800650103900100d000780500300c2450100811240c42100060040c3c1c000c40c196580350a20201070013115006003401b07215642c01d9203586590f03141500c0501c1e00b02c0d0b500e01c014000b09421100441d0030018038402000803d998000180c00d0040441034840903400225803400310340e5400004c2c400314031b03803104900c500b1a61180103070000380644c025212203001d0681c0128002d0300c9803926800c0140070103074850300c14480306102e48803180c185500703a04101c0100407400d0f40110304c801c0720101c0c6109039408454800010b4928004007042003a05024084c2801d5980d031007400c004000d000f9020307001c00040c0ca030b2500401c14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 866235800 1250 866234550 866234561
    0x1c0b0712060e04150b0907030b0303130e0402031c0e090a020c0109051e010212130f02030a0f030206010f0b1c1803020a0224030a050901090816050f01020a021b04 71
    0x410309050860200301000c41c81d842d2406540702c1c00e0b5202c0b000e0900f03581041501c803401c60b11a0498040d80c000355400c1d1003601304400c01000603007544d161205185c00c90381410040c1d080740881e02d0150080c0011410300300500400e1a0841c215280d4903444020300800d52000c1c1a00700307102d02c3c080404560040e44550449035681104d0000b0004000d080c6400d40c6c848000d03260b94a61481c3d0715508504005043c02103508154141580001c03e9545407103401c004440d803001941d10145c400d41d4417006071410840f0b00e0129000d81e103603d1071140e040c90028a00f5905070004807a0240c0604c04100c5c04040205407107051929240e001c01d5200790035103481c001c00003000300040004820403004141600407130110b003101c0c020b4400071401e20b49007500304000d8058203400c403072220702000000d40b441596404170b90000f00403000810000160b48a02c003a580022415a41d083c1b00c3c4107681040080801c400c5215240050081d1f04002d25018046d4440c2c942028101d81042d81d2400c0e10255035a0394403c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 866237050 1250 866235800 866235827
    0x603050403051201170f0303010b040b0706230103061512061a03060a0f0f09020607080f070f080309010f0c1211040503011a3a210e030c1c0b07 63
    0x401030380d980d5409074058140501080c0c41d0086c040c481800c0043c1402000300c0341a00c122400543c503040c641750000e1019846004281e400136581c40c2c042016800107011101c6500720584128895415414100101c41c100a0208008000000c1c204589900b4280304008650003243c002501020b9807032055001c2c8451780810ba250240d4420454181c0c55903104030b0003014600801c00c500780182000000311114080003a5001105110400000308a42e00610a0720f0040c84041d00709813881c1e440d00949486040c04a404080100404c801104244a10344240241c140184020201c04401504104202112242c406d8641c0141c4906404c0c11b01207a006000c042c000b0810401d05103080d0f00b0590384201100e20038240c400c20280d100110b13241c00252840c00803c003490003961101e0521030040c00b03640031200c50041032040309048210704d210108000b003585804003d01c14280c00c00d400d001e0f41d103024500c941c0100d00b0000b0130010b800c4070070201540c40080340710341e51244501034a201218210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 866238300 1250 866237050 866237077
    0x140f0c090d030807030b03060105030604141204080d03050705160818130609150e0f06150a0801050415080715021e0703020a0510051222030e0f06070309060305040305 73
    0x100c11040651201c0c03d2841549070f69402c01c100010a420141c07104002e100395a49980310f1808980819207070a40440805100c40c00c5401c0e403030231580c0341080c50300a03900100141d042451844c0c84a074040c010b565104640e441d0103803a0581481000007401d04580014003403581c003003001e20683c0b003100350f180d184101c01041006103c8070800001c01401080c05044852070902c4801c00074861044640c80694048007500109999144070514080400806d02a40a009045038184010078030005205a0483d82c0d1500004d604181c10b10090b03c0800040715210040d50804002c02440460f008003a82e52800081c0010711742035204914000c0365180b190300611325800d0301c40442c0c000040100c05c6900c02d0350244086075940d4100030001c441e005182001c688200400b03070005540303070080f03036010b221b545003210311012a1100d4940000d01c0750080300490b889141486992500710014101140300715103031880c20500c5d640003080c0c26000d01c42c0c0c0c0d00b45501d410100c1c0406001701c0035211361401008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 866239550 1250 866238300 866238319
    0xa091506030b060a09020705031206011707020a050d14040501052227020702060a0810030c17010f09020f09040c0503030a031b080f010506090a092d140f0c09 69
    0x800c5040c0340720a0f01d04034490700c0c625100003020451030007a00c3c4899046030256040164072074400c03404000c010041d47c100012107902c0c195884d40d8494603401009190700600c0d6280c03035880c040c0e29040e409031a94080c000042e0481c0c0c0c0307600b5030300d08840c15680286001c0d9128003022600740052581c018032001454842140412004602c14500c0c03a4806a40f402c0d951101108400b0000c0f0700c03d130380b00a50044d504104851700c25010700e084035000308410a040c1140c50356074940c8806407060360080900c0401c02030031881514024010207003a030404c11300800c90a4100da00017041c0820122015000304020400103040c0882800c4800c01031601405071390391a164a04010010f01c1400030841c0f0f42151002542c8140e4480c1e01154030038418038200640590a1608100c4142c200c9241a0740c8000a100b010904109030b0240d41c0d4801090201005c6541350654490301110011801342c00e00c0c1d2038015844046240c24403040d400c410340240100362a1074250140c05940f2441c4100b940211120 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 866240800 1250 866239550 866239553
    0x7110306040f12180308180d060209042403111c0c0303090b03060a051201020702190501080f0f0105010302090621040c1706042a0f0503011b080a09150603 68
    0x4244005407a407080c82104003500003207009a508140d044c1440c840c8400030b840030305c000340010000340301481c8162800400500c0c100000340290016001c2210210307004182c0250702c2c200b900852a41000a0b4000c0c0598607240200c0010103000d844090111040c030064048952142041c0316409513816091115050190410f0805102e0341e03c402c40024085190000300c030920442682d01980b80103040313400c5903180004110000084a1400708603541c2049203030b0050307860795a407100342c0c04000c2d411032b40c1c9880e290003d42000c000030954140581900104000c079240708880e107055035024200103850b2403540011501a0003400c81c441c44591081d8000341021801001407445284221400000300d030310f800b5045144610030301080f00c15400040030800240c40a5402e4406034100014001c01c01c41840b528228605198003c055110030002c040c130540c1000c0c09060440c1e481c05c0a26070211101c0e0000407c0703900001d2100c6041541d8174030305001c2101105040b030507040d0412040c84101e441c2d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 866242050 1250 866240800 866240813
    0x61104080a150603150519180209070f020d030e070302040906020904111806091305130b0c041d0907081c1d0904240c11010e071a0711030604 62
    0xd600075191001500310150380d62203203010b41c3d4140c039407001c1401080e00d00d688010004d0080504013502c141e80c1c4c80203588240229101e13445490b051000c190382540c6090042c000d00d02070103400e5000704885022002c50a07600001e041c6a105250320b4005910b40620100604000c29900700a40c81410305a29005200d640e4002d410501e508903010404e213004010f080500303100710100306881418800c1c4d16071051826030f0190440c554042d061404200b06000c8010849108880070400140c07103a14130700a00480f025010f40c0a00c80400562400703080500d28542c40914003560b0349680d501d000007038100c174820300c5070340001e141020468180c1c08009000904001a001c060000212506940421030710020b00c540a4500042c01074052905c45480c1c401c2ca00700240b80d12011100e40e4113400540071501d2007101a1001e16aa40c80706411001311800d013541c20318003601e4410743c40071006220084a248124861440034078140340d54407028507000c07130f03001e014031b100681c540107507000c210606c0325 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 866243300 1250 866242050 866242063
    0x1e150310020c0d11060712090c0e0702070902070b01090b04090c08010b010e0301060308030708040c03080408012309070b091c0c06030c081003030f11030a0c02040c2a06110408 77
    0x25554152440b0040003c8100c4030201c1c00340100582d540b08a010541442c014500c0d041040c40c56800450251000d4451803030100c040c0c2d01119259500c0020403071019070601015000d046140c60561400c54140c80b400c507600030601a0100b000d60b59104c10400d55a50740c0b0000ea590340c041141001e072690780b1401d500800d03035101c0b0540815960381200c4a20326040c414203056a60014445045848078201102d2030040140116054200b001c8040040303010340020704010301742c0b080046003a16184201100002540c0113a03100c0b4509001480451074000c60a030080d02c41c4501043e031181700f1307600041c090186600768811010500305000301400b107514141000e444064030140b0140031524000c4800e10300444030a2000b80211740c040c00004c1c80f4800070701c4145040e241885407482910762017415640000b0f514400b01e1541031418045080074016541e42c0203440c105004200b1013503030781d50b0300310dd010700c1e589018800014004e0200685039004141c03071038002034103d881e41c2d100c40c0300310340d80d05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 866244550 1250 866243300 866243317
    0x250e0d050d030c0f051e040806090f01180803150415170c010e0a0326160203070501180b0309030f030f0a05060405010b0a0f09091b171e15031002 64
    0x9040880c50f0400f58007804950200040a41e503052800c03122511031800c6400002050b041035008000c000f80d03601003008030034041e950b0700000c0c00081000240d41c508642103401c251606040e00d0306c500e80412019002d50341e000d4800305101141c4482140000c2c010304840403400900c1a4200020a00e8858001a0303081045000100d91040a0180054800c07500681946500c81204241400007901e13940c400c1a030400354a0303000c00c010340038800c04022030300a0284406c0380e0303180c07440d22029460100060b00080c8420b00f0700c002002955001da1007240f046018032688a8000004104180300420403100640e40c104502600c90801d20200c4030304134020355000c0705403401c10020490600d002e11844ac12600b110715054034104040e103059948455594002051110100000800400a020703004a44407401c801c0032040700700e0300c0c01034241c4502c084001d4405000d04100420846100017410034030009107020852a61a4048050f08106072400c540c1c1500a10f040b0000380c200c06d402070460390 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 866245800 1250 866244550 866244557
    0x3020d0b01150e0d14070305010f0212010509041707080d1a18010806160207030c120c09050705090f030f011a10031118060403080d15060804030f0e030a082808250e0d050d 75
    0x90364ec407400c01040c6513058901610000c00e203500394903895071180043ca18148204001400c1540750703143c903412200030030001c4050a500f041101004e203044a021110304509106407040da5040200560791802c0082079201c0036680b504031104e10a00030803400c002541d100300d14001944d10340d00e42d200c3d4400401000c8942081070080030803500703032a0042e103108040b01d07903a140c1090809401c111900c408a40c40302c3d050702440d06410158842070144600d2004902c82e03070030a0019410034020400c200c0444030080600c0c2500d14105111440c2c2103965114045524140640c0a640003d032035201c0e5520003001d01c0d07000030302c10321035003004d80050020045040f202480340350307036034019103002c2422a0300400281c1203a04130f0003018020701c0300e0241e400b001b4044036008180c4d41d0700e500e2141d1180b070503803031a48a400200c01c00c1d03101960078400e0f401c1c1780e460a48294201500c107108001c401c568404c100c5484480c60301c069a2195034140c04030070004180103001881801c01c0b5894600351100a03000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 866247050 1250 866245800 866245837
    0x40906051c031722060b240f1c09030309050c030102090d020603250903020a1203080a0e01020c030406020313080109030801060804060f05010306153006020403020d0b01150e0d14070305010f02 84
    0x142e2603610301040f00c600e141c2d51f400345403101d83d1032510344a40c002104c41c090b44000e1003400402007024881c441050f8402c0c1ca000448032141e051481c9030442c0300d507160303109078010041d0140980382c03103210f00b03881603060f5021030326074841042600f60a111884148845841c09165210f296440045001102c0c020751300c4c1c0742e5403500c81602c8403251500d80e1014000c5040b610100b810b803000b03503002d00b42d11444803000501341003019010609542c03080d070202005902c04991200304041c90060031004001d010001c0201c0c0100303980281140c20140b05a03418480900b001a05000d9290005000c000b910b0b00c08011640e12440c4c07240003040d072140b01410448565802080c1c02c00100001d84580ea01503250420380030717408460004800faa80c0c3e0443d0741a0f000e010000040e11981000c00c0514421009080c81d581840c0d030b030003904c0e0703103a86440c410007031102c41005c043e8071b40c68480d07a18250001e01880c6410206580240b51200d950310080c101d40c039240303486084403200d6002e082a43c074001105c0d040e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 866248300 1250 866247050 866247079
    0xf02181e0604060e0105060903070b0c1e070503070b16021c0302101e0e070e0c031b09060906181201060f0e061320040906051c031722060b 61
    0x40f81e07482d0048811960b401c4005200c10320f082030240c08198001822510b80c15150455054190400d842e0481d16070b0002c2e411440301e030040c0e040a09401c101d0f0303004101c050302c1c0c84000f03941c50505101c1d442d1480350010706442403800841c0c3e980303d86a005042c800b2000c400c4600a4081071207400203070014041c0e04c46061400406008200c1412001443c1464001a00078040001e0102c0b940610a511401400080d10880d1440492280c0800321620781c6a1511003510b00c40098810307002040f00700304201c40e2006a813100709417920800140c50701901d03001d00307112140074041c01021207540072811b440b4500b101e443c150041d50a440130107030001c410a541d1400d01c1300c480800e44425520800d90004d10711000c161707510614030780c401003100d00f4401103240c034120320f1980181c1203031541d40e89408003401103050411061128988401000d4103050880d280101600c040d5207010036810400f00100c3d503011091800340d10034080a19100160705024501180102001f40c0110b0141d101d6400010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 866249550 1250 866248300 866248309
    0x9150507051b010e0c2701080307050c2715090a09051e301c050c122701020c1b030f10020a022b02100501050d0f02181e06 54
    0x80c44020030002c140b01400402000080c140c07000d0301d000c0000c0c2945814100c107400f0b920300360007018002301455640409003001070030028400c01e0350780a50101d4001d040040b81c4100b9403220b80e1405042a185904c40f0404400b0410b403940320300da40035038400280171100c40994000b0003a0740c440e60840b100c8101144050741ea5544984074000310303401881d1214061010005180c0d804014100003008504051b2214080c0781c01c402e002c3e10b200780002850800309945880785c59000303e03481d40d40604100300324000b00c001c0b40000b0444400d00020340800d5070f2100582c030302c0d1000345070a00000d6403100c880c00f116654403940d409070090109840c0c0030041142c203001c02e1008207100c11034054400f041218954030042d50143e10b00300118800c0010071141d036000c411080c1103081a4407400c8030803011020000740b0b04514080c0442c0300d18a040010025503807400303143c0c1d0302e003a40448a001c05210f14000a00d038a0262041c908040010208001c2c41c85070000b050131030146105003400b2a521401d0500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 866250800 1250 866249550 866249561
    0xe09152d010312121503030503220503030709080714061c0f0e12190c11060409050103032007170111040f03030207080f0c09090a0218090d11030a0309150507051b01 72
    0x3007007040105d5a007800031900c204015135000b0582a07845411000117104d540c08504081030544290b0004030a03c0300c21030348004428001d082000c020300c405c50401c01800100c4c6650403071a48142c4000a242c00d010406680038517007042200e03000c01000c0c840a6035000900168071648041c0d01900759201450142007055a4000b00c2900e002400d440c00920180c1d04d441400700c041c0c0d445c00c19a900001159104401040503040080b400b046551640c58050b014081210016150074445c0d02010290000092401d084440741d0307115081c0c400e00e02046500500740c000200841000001d4040362061440c510b403000c4134481d9007142c402507a60310b80d0a0711000100c4e80343e680750f00507400200003481d0502c02240c000049905a0708042071550015542c1080c4208182e00b00905004200311781c0c5090000d621091828100a041107800c1c0c0440c40d241d2140030f59500034036035207603043c60900541c62251510396101880410050820010182803a04080c20307050105821100e2030f0316040e818041d0303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 866252050 1250 866250800 866250821
    0xe120318031c0b06040306020a180801231e0903040e0f100b090411070f050c03160902031b0406080f070c08070201030b1306030b010e09152d01031212 66
    0x3880c45040c0360203018090240c0f02da00950001e005e0102001040b2284000d0802001c00e807140b40000303200390900c82c0e5100b17569010206d00e915082200c05603544504251000b810040b50139142652a443c4084001c1c044450614210b01d0010410030400400001001914012040c0c881e0305c2c1d540a0508401000841700841ca1680401d810400d503a26200504075081d001040031400f4402c4684010b030700e07045a03d0940e0701d401d1042c82c5005000d000d2010148505094003d003450400b0000105400304841c4030300c840041c3d0010020b80c44005400a0345802d0030841821581c8690b40d100051080400361004428540208003140416008102c0d4a480307a5008002d9410b044080d0010340007400121201c40d0024103071010401809418851032000d10300c968442e6415506044c002100c6d1b8100500c1300a080d407042002400c2e41d0240031156910104501d0040d0801080c0c0e07003c41c0321300041040405200220b030002008000840f0b80e242c0c40c1d2100c80c2c0e41c4101c4540c0201c600001c2d20580410f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 866253300 1250 866252050 866252077
    0xc02030403080a050403080a1214130305071703040f211403060d06290909060f070903023c0108191404050619020403050c0f040e12031803 61
    0x1c100203071511029060ba0720301420702c24217240d50303610780000725880444031000250440490780341801161080180103800f0700170358059850020700506540c030407000c014041c0312020030844100440e207007050302e0a001c004403d0f40c8909042c03601c40104080a1421038071201c0d0780003074600520449240c1030543c0015500d134509455140e000d400351b5440940310981020b40d0001410200300d50740640c039542c403490000c01045801c0754900c52419482841c0d200d200b240f42c40c044c0706845500281584d0400f8050841859a45032481c06540c51800f81e400250840042d150300401d01c4c1010300c03082120388400691a000c01e00c982402401807220203542404280001c01082c80480b0003d40060b840700c1243c0009030714507024800d00c0e10940101c404540950190007040001400f540021015a0103440d00303504190842d52666220313a0b0202940380183d0700381d03800712150f40d42c5400001c40300703155405a9111200c00000c000c560391040303507182124000407041015080000040340c181480d01003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 866254550 1250 866253300 866253307
    0xc011b1203022214130b0a050f031e031306020a05060711190b091e071211120a02010906111b150f03150922080409091103100c0203 58
    0x90064000f9000300100501040e245020107005015140800c405000c41e445404030a00000e0100250941161404581d15007080d44d00089a04d8420800c826070704100c4190420150001c007080c40d00e0040042401c01400459086c205004084002d11180d4100400f1901941d2070b04002d0380d40d8000c0400060140d4400800902d015100b81c42c00701c10200b850301981c00d681c0400110714055085100d003641d07812607600502c00c68400030401c20740c80314a2588404842501c20300c000307803940d41c54801c02141401140104013045184480383d40e00b8203005080805200c684a1078507511100c400c4203d000c50501000400c0e268002d0142c0403062514500600d1400807003416107980b81c008000c2c26410540800d076507801100c11304007400e29840203035100b035141e1901000005c05840d111041c107010706240307814004000d090300d00b1800d10305c0d00b101d511690044d55203080100c610441c0e0016650510301081081000700e001e0303852141400c1117080705c00c06078048210401700c0742c1801c04640980d0080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 866255800 1250 866254550 866254583
    0x504060507060905251e08071401120f02070501140c1e09032506140d1d0313050102101b1818020910020607120b040f0c020c011b 57
    0x1500901d40c8680705070140c0300500300810b004d40c00740217201c16400ca50742c0c1140d005d000d081144000c02c070413100d000884a2045c0e14005044d80c031900c0303900541180a501c5050f14a583e401003003c08840c80036880b04100303040030b03100c507003009401402c001c031515420841002e800c1c01140d00424050060109098a00301c10040103188842d0904074200c0480c03c14041c401d60350b60107002070480104603009001082078021203104281c00b440d00b0502c107100f503050380c1c40c60510341c030700c103581905400030000522250403e68032110280300781c40e103424a203c000b40d00b007600d40708080b0b01401c94000381c00310762003541d59110000c190b4000d50a2086010422100c607903115200310706401002c3e00c0c0c41c3da080c0c84941c844075142c220b82c081c0315100750003a800140e41046c9060100c0c1010445c2c119202400581c00d014000402514040d0340d8851915101c250035480f0796a80c1d400310f0030400802100704442c07498044065140c1000300301c19800b04981c0c054408030101c40c1c1b92540102c80e4810550401402c09 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 866257050 1250 866255800 866255813
    0x60105090115030b0414010e07141801020c0d1212022104021206040308040b1e0604021b150121050c0d03110d08010504051806130f05030d0506100504060507 69
    0x100d07080b40c042640b40d5640c0c1e600c03901c85100e903403032460042110351620740c10014114080c40e000742c001410401c07080700314509407080c82c0c1580c200b5402d0650800b031440390000100d291001e180c1c09154042c4071410480700300404448003401189a54440c00c0c07400800c0305030343e0120300600e00d04280aa800002c0031002c2c00348600c070755034407070300c01810581491002c4001521789001100c0480104020509000c00e0000c0610b055074805850000320507005105d130b6200113008405403100340100d0300404d84820340189500608079540d001022102403609036112009142420311a00d1080c3c0d0003d444c2c031b41d002c80500302406605070820f000300708050038030060100b169400361041d000c10100c01103055140005000c0070000381c00c02d682c1d030000d550401c0c04000840d03002414001c0000000d0a1080c0b0303001300483c0c003590280c1c4d440000c1110300c5007400d1000710a074007040000c00078040083c4103208865150700040c0149000d03500255050f0300c0003003e0300c07148107d00414001c2102404200c0c00980c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 866258300 1250 866257050 866257079
    0x1612050408120901051b03190e1207060b09011d07050a05070c06020a030e041b0806030703060c020304091410180f0614030c030120030709080d0c02030f0601050901 72
    0x3055040768901400c03031112000c1a00183c035601c0e1684d4440c0d090200400c3d101c9021400620080704140ca035003800c920305800f2203a0042e482c0c04041d02e82001d03601050041c4030141c80c000000c00541d5440800340740134001400c40621262152010720000b1884000041c0d4840c0a150b0f003052032421902d960b10145d401c5c1c0c01999202c81001410414a400100b06c500007600400701a001070007624000c0c81c0152031680d141480602403072400c01905082c211258100c6801080c60800c45496161280400d0825642da040a0003250505000c0244998004004d104503100c2e800d041042c0c0d2801c100c0107061600a0740c400007400c400200501400c1031000414034a900c02080004400e000f001012081e201d03954807160001100c2560036003541001d100c40440c0020803802000240d825090207407a40310801d90080d04c0240201c0040d204034041d4440001038a0101c04888618040748001040501740b00e400700e0190140810441c0c083c000001c0c220b041c1c500040101d112030303003844042107140c1c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 866259550 1250 866258300 866258303
    0x1111207140c120723070513020c030a09030b0a020f0901080c0d050c09040b040b2803060504050313090c0906140f0301030b011406160206092b03020616120504 70
    0x8002c0054500c6590100042d840150041000c2d0f034540c0703001c5c01c0594214200004031000c00e40c88614190300c84030007140d0f9600365803048407090301050005c5003444c0280a0030800107864440001c0700c20807075400070745410413684240110105540c490f070180c0160700441174641d95040051100c0c3c0542e41c05000c803180d0005641027014140000707180e042e0240c5805503a401c4907482e000408a200d42081e002d09407042c901a5818440c0e200b48001048200038101d4000212661042d0340b20440406c140b08100115004002030000703084c1405d045480c1d80c4942080c9804030040c800001d140c08180c040c0c51403090b0b02d900c5c4c00380f0041c0341c1a07098440c0010514544590141044681548907002020754040e5020b8a42c0c00c00941c1003080726030070350100c821071510641003800500007501c0304580f40402264144c600782c0d16842c0700700101b410301501403491092308000e540f400b8030b020041480007600f00c0c001d50840d0020384030801645091409031802c240004c1c110300c0da000040c81d441c0c10582c2c016 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 866260800 1250 866259550 866259587
    0xe0601080f0307230114090708010e0a120306030f06060e06040603030807081f0e01090c080c16060b0a0e060406172d01020406050c07091e05091005070f0201111207 72
    0x184c071140d10282182c0c5c04813403119048415105000e0701540400000e03000d4079110008000c0b022084507100d48e030302d20b01140280a2000000d007108420b100e41c100ca8025a8400036500d2404c0da1440c18401130052402075117100d400e070030300207501443c2a002e0b01e01104d4041e00d462105490355181100c00010081110311048125054803003002103180f45040148240c030b2520380c43c6e50401e10f81100356100030b9104001c205001041c48007800050045a84222000415040042040c60700300007030030001c0c029942c0650100b20004010000b554100d00c180310881c0c04000c25a15000010460b00c070990001c001580300d842c0d0401c41030201c00d010b2944c040b181e41c2013040c1002c44202c0d582607038402e801190014002040d4218400d00070000d01001d00807680c801d2010a0b80e07421844501d5003404074070460962940089024680140004915915241c60500441c40c0007500504030341101c1086400662800311074400d42031403070702a900d00d070340c01512a00c03660711114401c490000c0c00e101e07a85040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 866262050 1250 866260800 866260853
    0x40b040609050610050f06031e0702070f06080a1b0f030f09020901060509190b09061b0706091401030e0d03020a0915031e020a2705090a0e0601080f0307 67
    0x40350782089200d21130f400b44400b14000904100502c03c00104282d1624090142482803066150040025041c51002c0500340280d44c0d441d06800c03407400c04181c1c482210749405a5001c54083d80c03101050b031081d6400d401c2480076601040c900710f01c10301c00010b0f0300002003090f032800c0303c6c0500c2500300548194800102240b5503a1680000d10212400c0e0300c8500401d00000c3e8207402c40c20101d40410706105074407130b0458010310b014038a8a0b6031150f000c89900c5140001035594100034280700c10f000c0c242c050800c40340c0c0c0d252551030252441c1c101d4007034000242051f20341403000b50b01c40e0059400402d011405040b02030300200c41980079400c200c0d032a50074411039100105400e089080c28001d103003120390f004100450201c5010440c0c0480c242084003080c0100f10a540180e0402c11070302071203900100d031102d00d09221180d8a441c1d01c06070005a4003907450002c0c4038000032180c01003c20452804283c0d9420303603071030300803507502c5059100780e24150b001440300201159000620300041040450b00155 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 866263300 1250 866262050 866262053
    0x1404050312040504050906010e0f07050c010f06060905040902060d230a02031f030305031605090d050703020307050a050a0b0c0106090905100b090702071412030c0604110f0603040b040609 82
    0x4012607480780222440700400c0401461806004a81e040398174003000d0714007541480d21002c03901000a00e40908000010045541603100f0b2017120708140f0040300070410f58040c100078030040c001034428440010740c900b001061074941403090429841c0c0c0141980d02d1f20a0b0417036200041c00c40780e80c00001c42c038012000c01e107000042c01080c034400c1d00c04240050b03803868203c55100424042038626910715081c0d003020b00000c0d070400c04994100c1d4081199200c000603200b0203e900c2c1c0302c1d95800e503420000d03106401040001c00101e82d42a240708805031340149840d0350030700c10031054a1080c035900c005004010000f660001c40282550798101c00007003411078030340364030200b070b114003c108881e240d005a0400a040502c0c2c440d510260300c00b29801d074413908040d000203584140d03a004060880f05046082400c81e92440c8006048042050503a41c031068141e03402034852104840039144c40d040410341035030754509440484003544c00180300a0464407251104015090300600c103d90983d944c030318900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 866264550 1250 866263300 866263303
    0x602030403092102060405130f0606050705060a1512080c070303050301090f05091023011706070c03020d050c1e1617071421010501230108060114040503 67
    0x180300e00d019866814001d8508003200030800c4000c0707403191510030340ca9940c800503500d14044404894044400c1d03829a45c0d2030750072000400c061841010b80914211002805c1e80d0480d0207041c040f80104142c850942c0c03403011083c1038038140144420303180440c046c148400e100301000015034030b001310200e505022903130381c065103403c210350002da0224001000400208078140113407a05602c024409200740d0902c5a001c60380e440a0028000445442c0c0305003100d02c0030403000b0b00c00c600e0140a1072001c2540c0d01c41046c0090120501d8410741401034000090342d0b0b60084081c1b5044503403642c020400c0032407800e4101d5854003c03616192060140c19441190010280e090000d07190208014200c811241414521013082507480f42d00c03000b45003102c81a02610220300b0004130350711180c030064020907e400244602c6d00880b03600d2904070124402c41c0360f81340d056120358161060f42044c0c101c8486260341002040920140c00b5001a0003d170000710503510440d101003c04032281c02c4030b030429440e000003a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 866265800 1250 866264550 866264557
    0x30d0503131505060a05010f0c0b0606070606030f0308060108011d0714070606240909020f070b0f0619180f11040b0c3009210105070e06040612090c030602 68
    0x1c401991103c0502104e85401010b0500520013424103031020012400080c00d01d8840381000790800d2444000590140c4602045a160f2680160100110745c1c5038178080c4103481e0300b11800c5e40011000300000f012035000e105018160380700e0840c0d950351140c10901341d248240004102c48100210718005880d0913079003201a1075080d00c62280440c0590070600b0b40d419001a05001219141d1302d01e201900300b40d0000803650036200200c00c056520007220200714a07611a54000411580a900c01c00c00e64030300006042d40203102c2103444400280c05000040a403a080b03000341b4081e25800180360108008940c8401102d800ca0139000c00c10030b04607003a016481d001603200031005038000070541c00702e020500c81106038120014000b4404180f41404540e402d5444565520084002a4132801d5035117900c01c51060f98003201038a6019034051140c44d0180005a40207000b1440351107120700d0b10701d8280c040e201070b00c0f12943c071071064241404907400900260303a010742e0344c106103040c040046030150004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 866267050 1250 866265800 866265833
    0x20f090d080a030f060b0d0908211503070b0a0503090f03040801091104020f041a12011205010b040b030c2b05012007020303040504020703050c0d0e1e030d050313 71
    0x31540740d5a1540b0040e0907a1460343d4682d003050715000c802e00c49111400141c1e01c1102e0061400500a04d051501e24120700c50915000c00b410480780791101f5499030600c10911504d440008072140384d90300800d01d507540071a8010380c802043c0510001850a12841c003440d03000c0a8401240c1e00982d84045450569100f90450b5245944800d950b50501c801e000360b680280c002600e04620700250501e40100d00c1c05140101c00800700800c110f40e03254081442a5811030305080c0d03882c1c0165940b00b221845681c07900b03108540c1942030100b40000c519244c4594070f2000c4024004d454280384940400c4018001001c40c100106114454422404c85045507050034521440000469480b40030b00791080b4100c1440d681c140c0c0310100b0070580107841c080300765000c035841a64050f0f19a0030764942618140500e0074820340314401d20904910b100d6200c0d20822402c5010307913460040c00071034010b065024050351112074041e0700001c1495481d910a10096a115100d4204840d1400e1181e4400c085140190031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 866268300 1250 866267050 866267063
    0x20c01030c0e060706020c03272d2110020403030e03060123150a020c090c0c1902031504060b01391104060b0d110306010210020f090d 59
    0x5001006503010310501210074010b04000a016108600050359841480c000810054002c42d00501c4c82e03108005840c0400507442c3d904580c034801200700b000c44030030940c825206d84000f0a0410310324019a640320b400303d83c400c0d14800290402e805219040c40c0740d14010144012421014003400d0091049503103415039401c01680c3d0358031b5410300518141d0f005400c0be200c0d40111740104195011082055104501d07040144940c051000c006500c2c2c4001c940b0480080c100001d45006450b4082038020091500716120050303600c420300740300150f024042c0c1c100b146501c20142c6403480030403401d207007014a02c01012110000c161040c0120ba481043d2030441c1c0064890903101103568014030003004074400422000c0041c800101c540d2108da0b180004024071130000c0d510075050001d4a4946841034502400a0101968510140c802d035440310071a641c81c0e5182c0b904180140111030203d1b03025140c1680100040031005a41c54000d510014510490306410080300005403241d40408102e140a000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 866269550 1250 866268300 866268313
    0x60603060b061908040606050904290702100b0f0418120807050712020c0301110a090b090312031801050a0906150e010b0a030617010b0315070c0b1e040302 68
    0x50680150384042000c1c40c072896061007104070000d0104144601164145403080c66911281807031002000c03550400d0750007412401c204000d200704022908801c14800248002401c440b400117405050182c030700800603008034900155a40c3c2136006248400801800d10082145a900140460700c4900d82d450b011881910b040051104140c030034405103805090543c0c81c3c0c0f50411000300f20388078016006040d02112604810072038820440e1192400c03001e4020010001940d40303042d199009002041c000070440800400c20044050a507251503401800826126081c03e4a601450700001c1c90a090701c95034004401d16540d09014550003000300a200141c200300f141001029620303032644060039404521002c0100c0728040680e60304490081d0440fa80f5543d00d000201c01500055104003800190000d1a101d804819440080c410000718100c03034401d01d034180071845d00e080850f0070101013a4107a1880000c01c1e80f0800c1c01303030300c144055010f50005075046103650400310155420b600503030200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 866270800 1250 866269550 866269553
    0x18051c120203090f0409150e0303060f22020c0f01021612110d030f020f0309011406030a24020403051906110f0904410109060b1b0c0607060603 63
    0xa031510380c000c400d48061032801c4035980c08100c0084100c1049806103644003000014002002182d10415041d40d4041c8181703d1184c0c0201c0d660340050740c9040c032820382030360582e40f1850309038050700d045041a109a40c26260319040032000b508860346581440c051079044150b10002032004250f005084090001c20305450708002031002042150003040c40031115081c06580c0700000e4888150100d460041440a2281804006130051002840084c9000b1090003241001900000c2070200d1b044a255031035906c1390101035503002e2580000d01000d001010b4401d042040c04888001041200c101624165413540d4a42c5008000c0009060341d420103005042042110b00604506030310345c080150818010702c5840c0fa0038130030080b00b548039aa840301555500340e60740f180c0300401001161440a406140300d95607080040300115101d2254246c40003140303c11980c031920f400c2c3c8625405250500240343c260f0075244084410324282031190124003651079980000030a01a84207040c0803407941c1c910b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 866272050 1250 866270800 866270813
    0xd1407050105040303120b031014011703131a1c0b0a080c010e042408060726130f12020a021e060a0c061118120d0f18051c 54
    0x494000c00d0402c1020041040400d0b44806252070240f01900000380100300c84002034901142e0303c9200c1005803d08402e200c0b071074082d001c606c0c100c0300910300c405207400700c0720100d586030321403844455401c518140050210031402110042d44186900c0010301c0c081c2003510551088000346120081992110350285041c00e16864402c01024100000c00395a500000007800041e0303a120f42a0080340e55031881c00c500003440e007900c011b411450781a030385039644905103251141021540000030800001100e0b0100c4409480b410300040100541c01c0c080e03c0c2c0400324a20b2005002080d115101031005035008034203110010880301100e0740041070440300c6441070050b198440c00f8142e0f1490130300564180e41e41c84070f03021529404010b1030711070b440d201c40d03141980c0240800b90350702c1650701001c40d15036042100b0b01044000d10600b00c0700c99041c802030902043e81cae8400c84954000140c000b03200140c6103401100040304461400c50681d841d2a10303100071a1103400038404c0840c2c41a0392140e00000d0200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 866273300 1250 866272050 866272063
    0x30b1903021804080d0b030307080c070e0c0309060412210615020f030d02031b030a0603140d0e010809191104110c070b0d1b120506030109030e1e0d14 66
    0x141c580b5804424605a240c1c09060701490030352500003501c50b840c00040d60b8091040300c84c03903030348141e03225150303280900501d617030b55240c0c0101452020b08101107a4603400e80c3e000c0ea44510655402004983c0d115a01c28aa51000580040c2805080c0404082d034004403032060401c421403080000e40b0394508000c8081c50503d0150714000c0d5000019a4902c1c49000f0040343c103130088542000da90b90301c2d481c125071941c44a1521003c4201402b00c10700142582540014040301c0c040c00135030000200c402010383d120340c1c41c0282c004c04101034420307250055000b9028180d0000c0481e090320b0352140e0690756a1070200024a040382c960103d008910740502e064410031807504c2142d40341c0c90404a1040010f6a65100d034010a54218000301c1d82001c288066044401c4405000304048010700d050303030bc05480701c0407400484c0d50305170031729001901c1c0d800c05208850144e40c0543d200101c6181d14020b02920541c6003080c1d88412040c4003443c011510380c00480d190042c4030b24101c4280c0030540c4a680e09181 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 866274550 1250 866273300 866273329
    0x9011407020d14100b0904020d051903030e0c0a0501020604151806050a0e030a080c160c0b030402010e01030209030d0809010b0301050c0d0e0c0112020c0114070504060305010504230403030b190302 86
    0x901e0007040840036254106d0403544143d042d65061080c00755411b16603c8c104519000c002d00c07011001000d0105541900845c40040001046507071512082c0c080004039415406440d00603800800090080b42c000e00031100044415000003a0b002d450440200c06451183c000303440e829110014040e1412207440380301c0e034059105010394109215040000e14800c0041e0020f030f015200446c44040c251b08000d6802c4599900003850b6803259590f000700d0407960003c4074264003003580092559403a5009008482c00c1c0400103001d48440c41400d002a40c6120014120084941d0f80e80300e150401e8509124050007020300c003036216114451001c03c20140d50240a035610035070003802030750410f66000000b05a40d04082040540c803061070100450040040603031114075a141e50341800160384e0404002e02c255000b071303a002c1c0520381c0c07180c0511056030000001084003180709640800041c0c500c8882a801c903100c1e00d4085640c05100f00014130402c1c1c2141c0b40c95000890010410840c601f60700403c007400c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 866275800 1250 866274550 866274583
    0x2040f0f05060301170c03160503160821090307080a0b160813150c0e0a1a0304062d14010602010923150c0706061a09011407020d14 58
    0x290070709010928601041c41801302c08912180d84140c0400103011491000e00d01a04603a500c1f5030010b903001da0b1001c0d0740b02d454007074003454400152446502c0d80710425650648000c141019020f00300070301d120306087c040580c80400388064000741d80e050110300c008009600c01000c0e9076070b081c205034201c9480074000d041c00040003285040790a40082417240d11461100104078801141e00380b241444800c0c61050710003d181c01c015040c600c0e08010002071294041c1e41d02c00c0310580b96040014219030041c440d6460314010700014000500c503400846a0441c0d03a003803240681c0c0f6a01486180c4141e500e403030210746407100b11200c9604d804500381760051401c1d20080c455468030351140e07030a0b28080030303010407060100412400259001c1011807140c8540c0302090388189403801c42141e1503000720b18112505400c091300050300780420800c0820000b03d40c503000c1d18140b0745600659000035041e810416140c400c1c006c590260b551b464000c030040f4044c458065004100102081c00c0c8404580c403403892 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 866277050 1250 866275800 866275829
    0x4090501170d08070c110303030405070614072604081608010c05120a0b0a050d0f062d091506030305070219060e130e010908041401090509040618060f02040f 69
    0x5041d40500031136000711050405031010282400e00c01403894002e9103990700742c070000042c0720030840009103540888119a507600b80924044140c01507500c13414101170a06103050446042c40082440b41450014180f04503030700e01940d41004600f0f0102c40320703a000071a41255005c01003010280214050701e0340c0d619140d8600048104030100c0c2050207413200700300c90741c0c076402003200f600c03000b40c48005003e0040044403034a03110301d0481000940c12404070342c00e034244082000c1442d940310800f02c4c1f85048203000007100c1c12480135080203003010325080e1070348d241d00382920703c4080c480c2c0f1485010f18000e58a50365102580d0042c0441c0700c0d45070b00d03408114141c003901000810751042204181030b5040303445081c01c6500c40c005101400d1080407054032540703003200b0281001080300040c000c445000b0200c031451013250300151a1940715116a0741c100c2e103140001400920302d544109907841c82c4140c003000070382a03920340f2806c4440c038000310b40745582c1c00102407007440c901d130840d0740080c044400300014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 866278300 1250 866277050 866277073
    0x303090f050103021c180b01080d11030a050a2a03050a030e070f050d020a0503070915080d05030c0706090c031b05040e0c01050703090b0d050a05060405150f060d020409050117 77
    0x341c0344171403a20103030b81d503104151942c016803804803005080e04821039000958585007800d8442035011002d00204032120340a41c500c14000c419542c4900b4241c031200d042042402040d1000b0503403081c50644140d9100b000581083c80e008803440041c066910181c88600b5144081d084803c005d0090010754444142000781104403408007040c0c035020380312134004d5201440032a2030f03154250880e641c9409001c0e00483c1c034242d154011031422000d441c020034559a40c4190640301d4420724800c3c0d0002d1010030002c2c039001899001850035500c10320002400d08200d07156402c0c02400c41e00101c503c1144d51100c000e40d079620700341a0002d040112009c01c141100071030410356540c80d5860183c18410040350300740034503000d000d020009080000c00543d50b00b144005040c001d00c0101d81d890b86130b514220203e40c003030415104961048503000134180f00c07100000200700c080c000001c03070b8a61241d0704100c0484000c0490001c1e0005040404000c503495040096500d0707100200114680d2540c0030340201031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 866279550 1250 866278300 866278327
    0x8070305060a14160e011202030109050403030b06070b010614070f03020c1f0207090c02150a0209130902011d0a09090506060306060102031603120f06080a1208310b010303090f05010302 81
    0x4190402c141081007800382030301c0050310328850610210180510120000bd0042c0c00e42c1c1100d41306e144a940d04200c244210801c104540c0a0000c010340212140300c0103001043c010314220716410802e413111810500e41d65241e00481102543c124010b821101c183ca4443c101a80d807240c00c00aa213550002c82c00100d00008c3da00c21030341c400c40c0c0b001602d507041020818001e2242c00040000d10345008045d01d001d400c004060340c444c200250107010001c0404a1410441c800c1381c01d0306505030340742503205407035448400928040244071540700642c05000a00c0e000c81d4810070401500c05c00141c5101d107801010141403038001000c0d50b040d90030803c503201c1b24007403039161b8540c1035501d030811a001c11100d15400001300a140a00b0001c80c3c58001d0110700c0b82c1e0005a03410301c807446108a610501000300c0102d905910940b11348501509205c40307004003407104014040240c1c402d10f004c460800361038440c00048803081c0c0c010b501249029005005151042c01c040c009410b0a0034250304d04045507031103a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 866280800 1250 866279550 866279581
    0xc140f071e061503051209010518012703020f0a030203060f0403030603290703062102030321010f0909020a12140a03030e07061e050f0408070305060a14 67
    0x2406070003000308038524107411000d0a94519082402000903c0f00f03080c980300c540643d80030a070f070103100e03d010409143c01600102d44610b0410f81d60142002016611a61803e8800d6019410307c05140081c50480078070b00482036400c607255410502143c907500500640710f140004090245200c00c40610158800240981e003188000410804c41d981d2802d04030001c202c10340000b800f00b80503482417003102002070802c0c0142c410040140c1c1064640c0203040e001c80d4030ba44030301130716202c2c072585039410011001840c000250003d4191ba00e80482c991031001d0aa1a4005400c4101076141c01440907800085009018141d1850104034406113030700056030201c410711401c0300c240c82d402d100c801003144800012001e5040103003100d400c020b0300c1c5409000f5244403010300000b40308003240021564031402c0000a490500300221b20884a40da0085940c0e1f800905007007a0748904000005e0b109034100084002580941c0203040726092541101e018ac550381e44e0254a8104620f086c0522031050700c010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 866282050 1250 866280800 866280803
    0x7140409050d1b0b04050a0b150d060c0509030105100602061b070b06011704120201050c04030309140f03030406030501080c090412030e011113080d080903030c03040204140108010c140f07 82
    0x80780c00e00d075000c414030f200705542401030a04002c0b0042c030003042000a0301004203442041a6400c50b030b11a1061032011a01c9009181d001c8102808113010542562000e0000d10803403500d14074100c2d51038080390944506031240d40724071a003400108807007a070520580740c120405003c8080170201e041040840c3e8011110060310751412180400e0071a130190090b4891510694195151351609040100f1409411145180503500300000079079680102d0045a0949038552250b800d45030501c0a4240022184005560003d000b0150f040195808001803c010601c40d075000c01d643d81005100c0b07083c041c030001c0d064028420081404000341040b0700540e80071700306160001d984a00303010020b000d000141d84418a291001030401110075424414130140c40300102150071000d02850100c401c1c0d9030444950405400500c04100403002600007560014002000859994442040441c80020a0b4800d4106079500d032002e1031541e401ca41d8861400c80c1c1d80c81c119081c070940601410182c440c0b00c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 866283300 1250 866282050 866282057
    0xd03020a03140705031807120b090a08070b0709140105041206060306060b0706050912040519051f080a1407050d09080a030902011b02030d14071407140409050d 70
    0x41044a041c80390340003540d10041c641180310315003450b0902a0085d4421b85004075444d0f50042500e001800004024048411f0055143d4800c0b0b8680c0710b0200b1500e000c0d2088001340600c03140c0b0008114000054031204d4042c4005510b58200007501a001108950013641c01e244c031201401d40c0340e80c03c14180c0341102e400b03503140200b24290b031070904018007580d040140241e15102010680800b03100190001d24443c840401c002d0f12080c030742c2540c0341e010407024110301d1010803052140e403c11461f94a516520340c1031801940351200c0016142c51000d6103002800c0c140c801508100caa8032513041174000c9a40c2e48104901c0b000c0010010240740e0040000080c0280043c4e0f00c4003284040c1c1c0301039101a00042d5090310b503000c540d4001e010704903035a0281d000a0080814580d50140000810b00e07061703000300182140da140f410180d44140f000c81010740302113014065800400c83c81000e10886d01100c0d0040c201c020304104202c040c00020780180d0703008a190181c200000388002801c040f52121505 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 866284550 1250 866283300 866283307
    0x905150d0c050319060b0a0f0320210408091903060e15010b0a020a060507090b07060c02070f080733110d03020c060a05090a0f03020c0126130501180c05090906090d0302 74
    0x8000da000c0c01c601030302c04000420510ad500c02070002840a004e14208011000c545030030500601021444151405007040000304041c9000346001c9500201c04030303d15002c003410980d20b0701ca00040340e400e44002c0110350440441032691101d408002405090f2281c100d90901c408014002d640790720074a00100380e01c0ea00d402242d4030a005074019002480c4250459545142c00d06d04600940488827001c03015210303400303010a203031000310764480541ea2001c00415456190003014110503903030b5020650a0844070b211303a400c1809205c00765008103d20b848840640100c100c4039440c0402d80818030040610510070f01455400c0460307070b5900549500c90100c1c0d1070719400c14503424048a070300024148021303492a00101500410b42062000090b2140e01c81c21012192030b0410080706164210341140d0036000400d40b50f84c000c14039994a009100001d1151844330980440404181041e01d28517642038040000c1d10382150f11560015141002d4949824491245c41e590000f51620805060700070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 866285800 1250 866284550 866284577
    0x3050d080604060f080f19051002090a0902040e06090a1503030804021c1505090102041401051e03070c170909160c050106090e0d0903030905150d0c050319060b0a 71
    0xc0e0084409043ea9244035580d45994420844c0e5a0300e1520684000d0b000b50a841fa0040d450140c0000303800d500080035011481d142a0300c0300c000d5000b8540c0e0f6038400e8071036401061201007440540080c00d1501e8800e90749003011010004040c1004208007043d030b0600e44400401c0c10013540303d004032541030500e9513042d1110300c0000e25031140515800829010100941c05201c00f0150240280a030400c2c2009a03807030310142d0900303034456400340b000608503280d05d28030700d54031480c010311017420200f16000016540d400310421580c001d07960400018016036801040c00f41c030450120850140c1e4041da454140e02c06c011440000000705120704000e12007070180b180c0e500a803140003030b031355028000704070064a07802c80000034078030750b030311304906216400c6601360660107040d19400342d82e00354440515040c134100c204200c3d041413120303000342e444081c0318005000711540a4a022500c90351515600e9240070920812400100540c00c030700e280c00e150f005c10081e002c030012144d80102c035103440c05980708038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 866287050 1250 866285800 866285809
    0x50306150f1e0613050114070203070b03060f03011109030d080103020a030303021b01141803030709171207060911060708040509041a15090714030105060d14071d010903050d0806 78
    0x400311243d042030300081c141c84582d0507450540241e8901f42c8440e04010070042e6001c00c0e40c0203108000f501580080c200b40140130030399021f076a10180042090500d0201c0c00003007800c0d68a070342e0405103a684081a40764061500344403c0b00046a1440d0002140d07245400003401001a0300c00907041c1340c3c0c00900b0714070310803040c6a007030b860a401c0b2000340241290220203c40002d0112503050048100c2d0329440c07800040030085038010902e5940c0d56480301d04016a1114001050540100901c10001d6030346031010740b18080c008a41c020880051010384074280310241484c8000300e60301c50700040059800043c82c00040c1c40a40380c4c00c0e1800e20711641d5920300000c11101414134061440f070940b04026444015040c186040303642515580950344031104c050700c04807414011100c94203400d0005108a08120001c0c0642000810002c03421055100f1203195940041e280100022412040d00140342d00080c11481111000c1c40c02404144c0b840d1034443c0c541c2c0000c00b00c101002101030104000d0303900c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 866288300 1250 866287050 866287099
    0x5150a140c0301051c02180709170102030114040c2a06020d020a020c0f030a0b060a09110a18030b42030c03010b092d0a06050306150f 59
    0x3a440418850a007445035008541013441034910501000a003080c03110a10800099020340c090902c85c242c141c20071189450b40c0b0014144402c000c50018005003118218060318a05610f007000140e40354141252001d0040010a8440c001c5007007812600e1566032003000041d000304008400c481c013003040842c9120717101208502510702d5001091b221007030841a030040c64592441e07000c9459032550f4406000b0b900075400d00141e07058200401c00c001090ac0742c2c2c4c00c80d5000100401d003d0b8080d44030a060070880b881076603209038482c4007080d800b5400d50480e01220010040c0c07441c0100407881d542c0c41c0490464000e14201c1c02954450480400b81451070744100444510200c1301d02c4800e1013000819060b0344204070b0b901c01e01c10100c041032a03007018403035455401c10107042041c6c141d40f40300544440c040e488800303081020f6001003282c0140f5072104010b00911070b040d008200a031401d0b04152401d04050900c20400200c91a0128150f0718203c2e002c041d00c600703403074a8224403240c8291504060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 866289550 1250 866288300 866288321
    0x6190204091409101a060901030906050405070f0602061009110c2a180406150e16080705190f030f0501291204020d0c1d0703060501030905150a 63
    0x1030400344060b001101e00d5151521074000036040310054090115124107450400051302d106040d50010560682003203002000d5407201810081614480c84d6511011110111001d942d04e8000740e005110800d54022444d005105a2000340703e00c1c00c0c0810011b504080342e00c2001c600640e50900c0500b20420401564144021201560342d01d640440a0401442c2091041d60000394a480e0307a05045c54106440000c0219170040768109940d165110700040480441c9a80c802000d42d8000800d80030800d4402d20407a5a418101400c40c168140644082d4010b0801c006001050000d0110300040c15407040c403c040c3c51400c4202008440005e4008000c05100c0ca880d4034207100001c00d10000a81b661200c003004040810005080211b02c0966401502c1034000007100c4000400c0140c40d090f5030b84c05105004800800340d41d561510455808036403e401019101c039420100300304c15400d032007070170010300b0282010302c20101a80c0c0c4e1152a41c0704062600440814074001ca585c6803d558818020308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 866290800 1250 866289550 866289569
    0x9170303010e07200c012c0405040807051c080f0115080a0608030c1e0c09011a19030b040e0105011a070c1a12090a080d0507020a12050405030c0a060206190204 70
    0x21407003000c013541c44180520202e8042034005410300100c0d6110346581b03003d40c400c0074000311140c020008201c05000e02810956030402c05021007008180184440c0b044111900075010324821302d054050708504005000002c8240c104004019500c50307030080c82180959844c5c607040c0750b0740d401419401000b00d50090105440007140040480000003051501910a641000381c102c3d49542c203282d03901a03002c4201d40003e50310004100b02c0781e01c44040c0050f2300d607200560303040c00340e406901c501001c9480c1180740080d8850744800120b040c28424400e0310910302000303021543c14056902d901d60328171741446110120000d00b003420300c10100915000381904905103a9001c14105102409800420448100c548240e02040ca440000548c8002c1e199000341041c3c10f240085100ca4028035008081078154001d03d00208000b40c62200b00c100c450003140c03035485e103441c1000c05051811007030f114864002c022165052107401c0d000542c1c560b001d0302d1116a00c03402d8194520980c080e004903401130303ca0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 866292050 1250 866290800 866290847
    0x501060f1d0108281b031e0503190e19051207061e0e0a0603051008013b030304120f0507150b210a0309170303010e07 52
    0x4a4850403520340880c1c45505942020444881e10300148081c28403d000321039000071401140030150a20032418100084002000c0400540354000006500f00c05414007003a6104144108038681071390a07041d4540c0c26041080166a03030b1203c0d540c1c4151a403c0c4d051a5600d40007010340c51041c41000c11804000d001196604008400c181240842e40078040c400c0c4600000d960b1181000141c031411280d49540d40d402c4000302e80090303003020f201c8854135002c01009440c5140c040e02c545003007400400030703641c000a251401d030124082d405d100b900302442c00e0341031060190040031204e4100042d100c1019115001415042c102c04d201004654544d05500002c070030002800101c0c070540d00c00d600240c4403d0f400c140000d01c100c507540b048a400510b0341c03009010500f044a02503200c091140e50150074610400100020181d620240c80082030080d401000b1640400d5403000b02c1400420505102d02d4807130b054000c000352240814055100303030031500c000292074240b00364100d852500c1c442411001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 866293300 1250 866292050 866292059
    0x80705070b0619051e120607020a081c0c0c030f020309060315030102130603050f2805090c0a03060e0d090f03110d020907020c0406170d1101110a0518010503062209050106 75
    0x80d1704030140d0701035201310003406a04901c044c1c0030409a1103042194081c10300f51201c1e81e078240440c0c00c01100804804920b2201c100c0d01600380c412000c18200d581c8600880d41e4041c82d00070040240001c50800b150414031200089407600c4043c1d0380c12040400e5108409201040030900a0088555421141e154410005000340d019400b06000c1e0301900c0045020b903860b00c14841c2d0103074807071144078040b032081c002d0300c034299071035900c041d0704500400260b802c40b041000001d0442d849a402c159101662a4440c0e14000f20401007040a02503608200e406a480c06a0701a01581c2510010b000000c0c002000300c05583c400f00c101401c3c9500038100c44103824600c2009584e03e15480310240224500140410040e040d00340e15420f000c010740044c1084642502c0448107010441d15412080d900c80e01c401d420341c449400135000100065840985544c5d0302a052100c0c8211031003040c0c14014108140101622624400306483d03031462403c1c92040c150064440040c4031586000d0025440c0c12404074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 866294550 1250 866293300 866293339
    0x20f04141302130608010e070f0302070f0c0807060306090c0503060112090203030325031b050a1b03030e06070806030a0807110a080304142b02030a1b06080705070b061905 75
    0x2010303130794030340e5850541e0b030f80ba0849611011400d880300c3c3d0100f000080e5200302588603800500c1c0052103009070014103201943d030001c6070011038100071032513006140c0274484241e0603c6501c0040040220a10400e003490b20054030502c0701418044c104502c41e64401000e4680d5003151818a07406000c0360b03a6840e15030310441e401501450851984424000d030110054802c3c006d4180750045103a0540900103244016034250340306141e0700d020720002c000360310700400480180c0f81559000351408281075400040300b0f801c00c3e900820041c1030010140601c0481d031000075142c0740da964002c200e20755a440a0600d4462501c3c003c0078103034403000303104004c141c1030004009002203c03420307001301204c480c1410800c02070101136100461b00d180120300041800440c9290ba000e43c500150a075641c02c462034852a99a11103c40c80c1d4901030403201d01040556848440c55038172580c2c0386061030400344c240ea1140903420001d495240702e140e0155120640092a003918001440e00801030050500d8180b041c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 866295800 1250 866294550 866294587
    0x140f030f15152d0a320307140433030302010c171506041e03020a12230102040504020c0a0b0a060b0307030c0e1002010e070504020f04141302 62
    0x2c0c4a502c030910340d60041400c2000c0d0700310301608401248035810320b50000c15540789090010050380444086400200d05045030b8480c0c60b4100282e030b2000a14441c070051001c43c10340f440085000f82d11400c0c00300000400150305640d0003200700e90104800380301600c140100b801c00c000050640100001c03c0302501540b051144c112031280d00203001d41d0a14510030b07504010a102e03008440848800052202c144101c044120b500e001002c04d410030743c440714100740e010000d4074100c1809440000600940c60041741c0c00005040e01d040314800c0d02c00503600e020102805444400302c000001203044401032003074050300c0207000041e00c1191190078a9402a5960300c141605131546001c0801042d8441c03c6070141f101901c01e0000e005166407642c00e0100c0003800382e119500201301130324003000c00c290348202c0001c01c2555035500103d04c500c03072140101d042c14540c4e4440392013070740304200c00202120203406942c111420311151403079120011002c0350455100c0c00034038103014070000381411a58600d0011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 866297050 1250 866295800 866295811
    0x109060e1c1103070305070c120c033507050106030b091b1507030503071704060e061609120f0b0103050f071203081b090a0e090115140f030f15 63
    0x10140e401c07410a2042d02d0400300b604004646400400c02180072a000b10014034200703205002c030006061351001c184070407602400f81200c61745e08003030b020001d00c0180080100c0a00526041d10140401d441307155558420140c4a000e000d100460f841090000030761101d030045800c020b91410524061641c07940341d0400c030780304c408840701e00030b031842060603d0505604c114401c030115a1515015440981c1c998000038400420082003c00d148010407d03d808680603901c9880701050901c0d2150700f0340d0801400410003140d03c55030003480168503502010030360844100b002d070b1031251042c40c101385048152030300c005090200000d0000007041300002d0b0841d5450490805e85500356241c03001a142d141140d44080c00080c2c203000440c110081e01600b101e141002083d07422b280c4913381000c141078840d264014000600424104100e80301d0a005a442c0c40620030010501181000c07103c01c841070b40d040c3d0707140c0135204000e0300c500700d620f081080842080910741200c40c03c542c078a805a001034400c558 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 866298300 1250 866297050 866297083
    0x618033108300c010e0313050102010c09090c030209090423030313030813050114010f0f0308121e010e22110904030e040c0206100f03080403080a020109060e 69
    0x14001640d06000c0b5400110780c000c02010501c85409a04068041c0c00325001031411450410031008012005d1151031031140c180740c060340e140d03140361000001001d01540130b281507905000700d030310015134401c400c0416181d240b0000642604000d40450090040d0051030341c0110002d030605c000e2010110031124140f03030039140c00c0729420748241115100e01040e60b600111055950b484400603000707072242584105485445404045c81e520b40c603003542e1f0181100c0c04204031100051041002070700b000d0011707000050410280e2850b55964050074800c4040405141e84e440c0c01040c07411150381d601c0c481c6c01c0c0716400c200b400da5840c0d410006a00703130140c5d203c0d030f03050001240d44e000059064100305c1c12a074000000000c040405003e0120400004004908200102d00100031560f03070f41c490074140d100307564002d000c02c0c641500310703c41004058014545850740e00b1420000550300c1c000b00c80c00d884d848a102e94858101000a80c00b4000c0280020000c0e400d00700451207400b8009401901c1207007184 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 866299550 1250 866298300 866298397
    0xf1204080610060c030e0301110f0307080109020f0403020415120b01180c080f071215170c030c061c0908091017070f0512011205070603020a02061803 66
    0x107141d808a104600c5a003000c24818050030700424002d500c0c6d0782d024003000d0300104030024071320b801000c1030f4442d0f00c1d65541d03500044103200480e90301004860140507907040862503c0e0128058540a00032440000d10a81d11100c07180b6500c4981c0650390002c005e5800b40e400f95511510f842d81c0120000d02030000c00e40c10540300107041601c03c0c000c010500c2000c1d1244942c981740c0040b001e1680e440200140e051101d00d80c018040560300b48202c11003418030040400c0031030308044000d401c10000f10090300741a4046003400b9025070f00414078410782c0c503089501d2551031003c0006150388515102a21448a14181401051280c0701d4001c000712401140d41003030074800e030300c420744014114040e5003040505e08400548075600410041e42842c171542402420701d8403030300c00c0007841c0209804c50307854009404c05035010840d04100110142070541019800c000720200025902e000c0203100b01160740c2b000819a004c441d0610803981d507082d941016140c0400e00c54400d61001d007409003002081706031107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 866300800 1250 866299550 866299561
    0x20f0f191106060d230f0d03060b1e0a020f15151206061c060510060e06040e1b0d0f05071209050604121106010f05100e0607060903020f12040806 64
    0x1c10283e2203503070000e00c800e041302c0341170719080401d914124603200314005078621080031000c1001038a024074083c40c01011021108100242581c03060f84c4061039048041c007105002011040b054907100c54001c0549443ea0280d150485c54049902c1030000e2a000c0c03148601445014041c03004d00c14910030000184100000081c003c1104d11802c104a0f1600040040703040e524001c8401030441c0704c0c12a0f48501001a601c410301103950640d82945900496070042103000e0300071505c48526142200d90605141c94424440072224004201030b81109281003412000035030101558003108424078200103152074561411f000381015a14880170403444407560031010f4070b501070009410740c0440500b44030340360756444000044000400c81c05011603101d044011010130002940200302c042c819004d00c92a03c010b1181c0c2100c600e01680400841124508884d1215011034400c5523010f180040c41d0042030070100e0500085800ba00030a00598072001460380444002e0025540b510068511f540c4a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 866302050 1250 866300800 866300803
    0xb0f040b0609041a040314120906010e06061602010216060e0f030106050310110f0a021507030504031b05071e14040615120e01021207030b0d02010909020f0f1911 71
    0x40f00d00400480102200502c00043c101809800911a0404003804503014941300c82e1600b00c48280801c0c000501c040090111040206a00500700c0b007105030801e05007040410b020307110784214604100605414070003164420010114640b20310484141407d4490000a10300112412000c1c0300f1901d9503d0b01480e8034040c0318410407241e0060040065140704460200078044c0352402441d005414000481c02c510444014105041c5650181c00705025810124000410140459003058034000420001036003203203240209000048400548507d83d2134010f103007040341d400c031800340c910a0814881450070784130b400003510b81d984035058015040c80184001c80307c0d40d00c01e5903140b100c03990844d001640204a6602a02071210700410585078940a540c2607030310021521014010001c00c10820551510608505840c101c554800c5d90300302e500020110840c0b801000c04195000602e460b040740c00d601194128a0304040c140c1d120301a0115984018170100c8004000c11424040785580440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 866303300 1250 866302050 866302069
    0x503011410020601061808100507020d08040506070518040603060c0e0d0507121b030803060f03010b130e010608070b070b010f150507060603050a420b0d0b0f040b06 72
    0x41d40e0b008020316031800c2400c4501c01c80064141910f88910040454401418080800c841c81000c030081081d0030100c4000349130101c1161500304001005090100042c0302007045c0750009240e26000381c44411000c0d244411143c01103219a0291a00b0342c004100200b940007881c000116850700a0400e55110a012807031919031401401500003d505024000f891202d43c0c5083d80200c0105c012408030700007a004604198106565a510103c1009810f16007801200c488240903002440000742400200c1d2400d1124088105000c1d1184890ba124440940c0404010043c01007115203d40d6114400d440c40e601409083d0307103c81c841700002c24803100d882034000c111081c1401c0760f003950311011411103032038001c1750701220001d841c0c00d000000704400700221602e040c010951407a0403465005240c0c00202d003070b28010712404050200002d4020005c07011801030142e4a808140b09114200054030340d1000a0014034502d41e41c0c3c24041c40070b245500c82481548940151022a01c46008000b003552 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 866304550 1250 866303300 866303329
    0x90405040f022b0609141f111606050c160317161403060a090e060604141506030a020d05010605071119031202120406030b1306031112070b0a05030114 66
    0x20783c103500c1800064a281e00151145008207285030b1290b803031a0045042202410f0189a1384141c0d80019075114402d00c00d4515000000c00c40d0b82c0341086840300c1105482110310003400d21540c8800007815400ca24044031000d240143c00304140050320b01d009440ba144000240391418644800249078880c440c1d00c2200c00c800c1c507100c804001034543c2e8001207551001b8181500900380e03090008129055011306028000a80060003181c500a400d03c000c9491350300d140035000b0b40400a014074215500404015a0030070750300701d030396584c0394010a4044c1c490709072141010740c03070a4000550581d110000d4241e8611940e60b0304000000d940400c41280070010884804070000300f810000182c16905403c8030260170b00644400b000300740003607003253304103900410110789c9490304d140729403804407481c04409120708070070031103242541c9070414030258448a41e40034412040c501200c000f02002903c0040c2a4104016900c81000100810702e030801e100e43c0c01803114003014110340c0e02d0710248102588 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 866305800 1250 866304550 866304619
    0x32018060c03091e0405010603140f04081b070b072306090304060e011b050c0a0603150b0a020f100603021003050415051e04140f0a030c0602030606090405040f02 71
    0x2c6120070030600116002d80013004a078400d0b0004220f072514044c0c0e50003014135442c0000e90003091400500c84c6c85c0000c00000309480c64204220000340c00d00140c410043d01507240c140b1a02c12440310302d01d8000107402081407001d0200c2c0c400e00f007140c8442541c51810b241c449070040140d60072003244d40c1c0c5a0541d0880410307081800306100040c03154858071203d0f00145459180403402d40341c24040340302c040600b520290000c01800196041c03900c143c00003413001d0f29082000035002501e003e0380010354000c0e00d0000d00b000034008542d03442006031280c824401000d960a03031f24501141001007015110881c01804001c144140d01402807007840d1046402c0310300615111001c08042c80140f0f401007803e0032100381d00001e025403084130769090b403049100e01d20b0036200c1010140200c0ca00000015582c0f2141e101c042c112000035403004442c801241d00150158903515214001034503400340e50050b80e000743c6440c080100b40300c940e4100305100e5009079800111070740f0040d8042902015140300c58280d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 866307050 1250 866305800 866305807
    0x16020f030d05060105070609060e01050705180f01170928030c0312110c030c070906061205041a04080d060609060504180f1103010303030b010c02100807032018060c03 73
    0x251581038000c55030202c3c052400350320b8043c869660004035075034044141d81150b5650091074000a0034030595800035164108039040c8240c0181d00c112405480103014050012403021500d140d000d4880c8030100800c1e02002103443c41c04000540d5602114100b4042c031781c1d0806803085014103200c07644000641c00d036039007650711101c40c1c401b41e90741070240c035280a845a449104964201a182c040e00c540c04407a4099603403a20010340c00c0b441c10341c40d81c010300089840c0010801c24540c000c50061040980c6e461b020510f07646034201030a2840d00d03036103070460036040142000304001d003a000030480c0840002d820022651141411100c92000380602070214a0030003040c080110204800c070600e5540100103d00c5c40650100034003622140c02a03129000c0c070120042c4201600360080640000707003032900143d500030503000030340c8e0404084101801d200240002ca6142482a00301e1459040c10304200200300240404003c1c59910129040000140104001445140c0034080356190390058006604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 866308300 1250 866307050 866307067
    0x61f061e05071515091409190f0c03120815280801020d0504050f010203130605070c05070303020706110601050d0303240306020405040b0f0d0b0c0c0303010b0316020f03 74
    0x5007603002140640742c180c0c0b401e1200103070f58564050300c1c0304030312114941640701d840c0c040ea920564160700b520410f07040f0f86800704035a046001076411950942c80f02c0905070314010342050142c100d91001d0252680c80c0340070010003030040700c18012f1100812680c1e0041c40b80d40315009800071124402d038055001480c03110101900304405845d81c003103803021086c2c00082e0f0b582e500b05400c90740401e00e0002540e46038400c1200340001448400410f2040f03100940c514078150082c207c80c402c103902c000340050b584602180b00e2910542c05900060b130302100321080307551241006980c8500341d2050500240794627081b02000f450100d449412690050640800e0214580e0285c0c00303044050390904049811007108a42940124003003001580100310041e0b465050806000650301c1010381140113048402100600e501e40f9000c420b45150030440b2440681c50341c10144201e41710356040070f540d91001200218030b4011000040d03009002c50280d500001d8844c0c04141d85400c01e070f0a0a04243e0802e204446 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 866309550 1250 866308300 866308307
    0x105011d01080f070210140a0c181a0c06070c051e0a1217040606030308070507020609210a030504080105010f0815060312070303050a0f201605061f061e 67
    0x42e002904c500540d01c0c2e0400c500f007100d0450350110621b030307240300a031410f02500904c02d03c602a21208285000d240905040000b61821a12407091103178440004001111803003541040d030320301c0d94000080e161541401c503001481c4112049050315540504a01240494140d12041e0910604200501681903080e203c03070b441214550f00f0700090000d150458500100c00c4800f241c8124071520707000074500c0c103600b03000300b17010300050201081c000200205000b588e07406082c0d0b03d082d10b0459070f07840500e451011304419209000d140300e80e0b600ca8100244c04240e0000060025101500020019a07a0750051205490f1175032280d446940c2103031211048810010288691299019089424400030b040080b116688100000d90000c0e40d1403091003140b2071523000c0c06002c800b6018092001000b03219170302c0040801010361100c10300b00081c842c080c00600300509041d56400074283c501c0c0d883c21610307086480250040c100741c42c45003024042912400340080e20301c10074804810038884d5403030301c0054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 866310800 1250 866309550 866309581
    0xa0b100905062a1e06010e0a0c02010e060c210705030c070501090503031e090a0c1205010b1e130207030207090c05090d0804140f24040b040e0105011d0108 68
    0x100402c8280003092120255401440b0240300310140145080e103040030381c00114180d1340781c0050a40c0c0150004018407900d107882960042d1115200049511011409900400508242c0116400f91404000440030450003030b1149408071103032010511500807411114100c212168401709005001180007074003010b02616039148034000024040710303280c4803503207540c200f10717400e0b219642c0c8145149071a0242016a580008030316000b804040c1c90341d503c4140300c2d200d0340168451044013051a80500109411181e1494005051181003120003481c5190307901491034494000c500c0d00d0f185400160940c0b0895000f07503011307405410030742c0c00c1140c01400b80042c18a80407c004050204010507940c0003c140f500c03511801600e0356071403034100028075219101c00c1c100d01c183c0d441c0710450400e03103420f0703410b03288151100010086444a00ca8020b003038000d41d04005d110301c07030205000c1002e100324404541611403d80303845100310031240d04009142c840d0305095001605e07031804159200180d0101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 866312050 1250 866310800 866310817
    0x70203031602120a1b06030b01020a020108090c1309021005030f0c1803100b0a0b0f0403260f07051002073c240e03121504090503030a0b10090506 64
    0x2c643c15904403a18881c54800c00c2507042d16501040410040009006043c2170010082c1c5d040c103200e900c90090010392100248900a4140107010f800118918070a00910303221140042c803042c0d0510841807060018010114102e0003031080300d21040794540207a05407886000c19040c10401036032080e4518499400034800319884080203001004195800d04c10f80e00d4070540900000381c408a68410414031440c2944a14071003a0300b041040007000041d000c8800713581d080382c0020004500c0b10400da850007251280c04000c84004148410b04c06044002005100e0050040742d2181c0740031180c101c01c034410000c0050501c3c01c20b80c4030021445502c407150001034494208610791f080c080c0140341c001e01401c5006c8403001540c1e820800911480e0111605844101e0010000d0075403040202d99603100742c0c1124204d00440d6800a81c441880d2451341ea80c9003405072007845880c001e45805641c83d0000c2d204046134605184001e07a031800d1003000c2041c105100d9a80d449200e00e0001030110a6100014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 866313300 1250 866312050 866312059
    0xf0a050f070b13020301060509070212092824050702041e0513051509190c03021905040b010e0f0d1106210a02120c0c030c0f0d09050105070203031602 66
    0xe4001c02c0000202c1c1d0300caa0402064803d0b01816841058215407d46c0c20443c817600641062041803940000c060300f02140c144610b90790f40d000d0000140c248503011035030301c590000c1051004d400c0c0240d41500c030112a03541d414000c0c0d000461003000c400c44158644200012804d0254802510f080d40001d25060688104040300b050161900e9007560001c03900c0360084c201c0c08100d0010003108100070100e12651252403c502e0808031925038076145010a00d5003802d583e420200c042c000740515031402968024800d07a4440448180b010a440c2c8501c41d00c2d100d289803e0000450354098408040808001048081c12060a1040121485084109546000700069140d40584450b001021100441501340401d134bc00b60348600c5030348400800c2a07000c1c0303006100c0b0760841c81b4000495504107040105030740c1c03200505408a40345019491242451384103c0443e4203400c040422920001902ea90324a19050b442e0801528180701b035a200941542c01000b40d05800c51200c24a002028170052 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 866314550 1250 866313300 866313307
    0x80312070e0f01030515090108010c020d091815081c081602150919051006050105041d0c0708030a060503060a06140607030306030b0114190303081f0f0303020309150f0a050f 76
    0x100407c0f1122000d2700003030503d81d91404000142e5030100000020010f4515066130b0a6082405c0100b025041070416a045515019040c034807150301540d10f0b000e4044c56040b1440c06081440c2c00040d0820078040f0303408036070b1003400b0401140c2040842160450740da001401071021590303800302003000c000c240150600480c0c102c0802e040d050b403088101c550158005001c102c2100502008842701076100c0c0d418400200b104100881100c0d440c00105404048c044143d82e5604992802074861722200801c90340c0700004100c41c1c100c01d80c0c40302040d0707403042c3e08031801c1da6204880c0c00f0480f00c040c0680405c001e6aa42d09902c149484401002d0301c91080c0703030104965949646d010800c40d001c0e0081060061540300201ca14100305a403c249a0441c0313a410b980b03d80f8546024103a00009070043c1c1c4801c4180c49441101c80420010031f008058400d481161203a5a0600039101c0c4c11030411140708100540018003910440b0080d10200319a90810610b49814000b0035100340d88130a580d02510345e02403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 866315800 1250 866314550 866314591
    0x70c060e0703060f141b0906090d0807050f0d09051504081f0c050a17042a09050a090c15030f0f0e0f120a0c0813080312070e0f010305 59
    0x780041c0004511980c03010410134045010320381900c00c145082036512040d0070401100c14003000c50062465031202045944902040100b40148a055034464208820307421041c10020100c00802d10309000b80c0c00e03603210010000c2051386414803500760000242455009120514258182509890884040e140750a5844039142c0c20714107d0100240990007511109281c1246805040d8980304145030041c903103080c1c2003014184601c4010348889500001c000a41048080055101031103400740115540220000340080800c81030300445d9019414074001c10100d900d2809821802940501807403600f40c10064040500c9160700d094030101502e604c8010706900c1d4511070003c21022030280403803503103901000146011280d423080ca2203030b4040c034a8501e00600217000d541585400b45406610001c2c1030030250018001d80c6000042410103580000d840c0300300000808804041c510b120005640c3c846040d503041c1800d01c4801c5c0c000319007500040bc150301c60750202d58420100300c2c8076030344030400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 866317050 1250 866315800 866315803
    0x60d1a0d0302060711030c070b0a03020706151d0115080c0f0d0b0f09160e0102010905033c0a0f0309050a030e040528020d0623090609010e070c060e 65
    0x1000d20640141c0c102c0c406109045912803141d0b806945010000e601d0f01d02004170755030340c0b403425110724641c0050106002c041d0390b200381c04881070b854108109001e07a94040ca201c01d101c1002d031141c2005900114203400c1c0003088241e107035049030030f02074a10100c40c07501d0303000303a680600080007a00044410095189043c0030b020142030f0383ca1140400249a403000d0342800720781c94074515440c1c0b06d104450104075040306852010001114545000401c540068005034050003003840c0040140c0400b03d111050712680314580042070191640c40402054030310083c2c1c4442c06c0e400140001910100f28440e0364038096601b03410341c582c6a190002d8542240c0d2251810100c500404a00240160a80c4016807a00380101500500c024014420980800114900f80503403c0c003244046900425000c1e111400d0360700801c002c00c401041006100486055000714001d904441c0e403049541c040459603608100100605849906540032643e8850840a555011804d1021650145c49521120b101c40d030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 866318300 1250 866317050 866317069
    0x9050603071a0c010b0d0803070c05241f15180b030c070203100510060c080c030f03010305100612020d05011b030e210a0818011e05070c02060d1a 64
    0x149842c030356203d40490001d5401e48208212891168042c265400085007481c022290000594240302d065240607246c540e08181803140b4409491302c40014002211180100f40d078810f00c0700c061400501e03822440b0451480449004124281c030b01340795007240c060300030742452110031200c41e4068040c0f995a4a4054994000c8810341c1240c10702041003001c41c00e04020591030060344070400c2c0315510f8235041d00c0d1440c0c500352051500700701108880300144000002240c50140b501426a5503415a0300703081900c950080c0700440d518445c10810071ba059442c0e225900c1a6070441110b000344032001c0c0c080268084003414280c0d01d80d50b0304c94061904942141c8030a012007410b8902003084524003004078140a151210851411900d0100d60710b001d44200072286000000c2c00c04006540311100e480a2031426060000040d62030481c460ba500c01c0d00a000c4100c00f030043c1014403442d6110402260526864400250440380c1407101c0c00740c0c655247c008010a04020418403c0d801c0005c000841002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 866319550 1250 866318300 866318339
    0x40506040b09090a0506060a03021b0a0606150525020f0409060605130b370803040e091b1c0203062a070b06010c11060a17060d0c0905060307 62
    0x200002d10301000b0f0511440720b81d8002c1014500f08221303d01400428402d1140c880c5450806500043d440809180c694840000c00f03400e4080720541d165a2400d20024645805080310155101c6040340c40c040c8603d003101c0c0080740e0151100004102c480724600d036420300c5203040740d0181015a000409403207a12886480071300a6101141da145080c0a2100c140e200800426015090a01c0190360380c5070740740300c50742c2141c0c0380d020f4150f104021440000c0300300005806180c0b101d09503800244000001000d407040c4c652000403107405440784030314140d0306e485d8884d00c03484580c0719005e140103c2c134110700808241c10400703d03201c2d014031315540001d0500e442110750359000780c408c0b03140c3c40f2001d24034181e43d08201c8142c00c1d068a0710307201e902c90a00100e002800c450401c030203529440100210039001c17440240c00501026224181000d02811910070100e00000c9055040001000f80c54440389410400f500449001146c604003001000074280052500713415110b14100056910440401c1c002c209 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 866320800 1250 866319550 866319569
    0x1c09060e1f03150f050a031704080609010606021c08130512120406140705030c031009020403150b0339030f030d051f090c090305030d060602070806090d110304050604 73
    0x41c43e460030b0440c40c0b040320340203240f20962150f000e01142e00c030450783c00c098a401201c00e8034103410716082041c0ca8415034010307a4007800341102384102010150804004d84155400350361a00403050001c105070000e058940e0001500c490200e003d07140c0d01d2039149252030051003580c414048081640d2105d41c41099020310007101c08040009003d860301c6101d4a440500d281c601241c1003035480248140405032680000344800008a96542081e825100040c120010203640340c0c0e981c0e0600005070f088242880c0c4410381000b0420381540350200c1c903018401c40802c002c0741588802410400201c101519031300e1110500b401400955074200700c50895000414021640c1303158941c600030a8980103407810351101040640d0140d005240c051800507031f00c0710140041c00c0c140094048038082181d0b4005031003400002000c0c80444581e4100354180c1d4040c3d02240c0100d5910075180340d450408450b8641140c001c4005460901d00c12a404640c0c100d00a040f00d0800340c681c4c0018450b5402948003000e038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 866322050 1250 866320800 866320811
    0x14040906020406020a0c080f2a1003020406030f060b0d090f0b0f04031115040336050f030a0506040b04030915020114071b0201050c010204090515031c09060e1f03 71
    0x4000800d01100e0161401d47c014200300001c03001c00903607480b80044c41102c1891b10f080301d80741d141510f00707440790000c0f070042c20005109100b96024000758014080c02c3c0000342000b500800c2840306004407030403205500e110b54030b03210b071911105004210304841140c110f584550080003042d10602d0b02401402456034000290410b4a030241014100000c0c174903c94004200d05821104500400307503105401d801c0c55030f02e010014a80340c1d0445074020080100c9000c8441120205000481940c183d44042d6030080c4015100400c05a40b07a00c40240185a940f0540009000481100706182c10a110781008002c0548840715040031082c440d1400005079507e14180c001082d0248040307400090904003179039101580d00341001107603010310010b03060040c0003c020881650940c100d400500150b4010045414104005000c114103100d440c6d20074410700140c500b200c0318020780281d513030307100f6107669038520f02e401015142c0f68000c0e800150311104030326250055a03200c44108840e241690380c0002d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 866323300 1250 866322050 866322053
    0x21e0618040e15160903060e0703030906110a08070203010204080304090b03010506010309080915091e030d08100e0910050901020702100f14030c19050c1b0a14040906020406020a 78
    0x100c45003030000c94055445003c103080e0005161460782d8204e040d04180022200214001717591010031540011b010354a80641514100404180c0200b0359200e03554440809690310821902440a8188504150095441c00002900140c01400254800360015050917510303240d990564200381e10034039002c0c0d10b540d43c3c491249001e11405500210900b82044518a10f444406650207621050b80c0165989441641880d44403c140e0b40040e00007410f0140700a141003070940d6200419001d5402845202c0103c48981d0049006030301c118045006a2200c6142c00320710b42101d00e02a006800c0c0e0301030b48000b4406240c96000d6988203815040c0050b0b5141028814088890510403480f004c01407419440c0300c645502c4624280c07040310340d407a180c0d201d4803401419000b501c07c50301400000303070180f030700b080080d07410101074124101c2c0c3c0c10aa5001c0300d08166400030032040303400304a9105850140074040070010304810160310101500c00a081842652401d040342c0c05a040351000d40e0000c0003c20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 866324550 1250 866323300 866323309
    0x406030b041404050607170f0106050d0623091b03130602070807030804021906050d0c180e1006030204060c030f0507021e040f11031810150e0919021e0618 68
    0x80401810a202921450b10082d230142451040c019802003081c005020403181840d904150b002d8920a001c05400340c001c0c80501c8440309100000d9801000301314005481054488100c1d20329031140384281d4556521950a20a03602889200700c070082e81c2808100045800100030b05840c2d031207901d50360003d04080c010001e0181044510541c0b5480c0d03080c0074020a81c1c0401036550389608018003050000c00100144e84d2071841510342d5000c42c014400008800242e595400d016031174803c0212481611444210164402c502900c004180f01c0340344400003a202d407203d0208a00030340f5150f0b04294a5900060011040e294420183d10041c06000c00628091080764910943c1e020304111001c02d44c16520201d002c001c0c48a0070000400e00c203040e4130f070400e01450281c0782d01d6080402c031984a00c03031640403050712402a07420841620001030300c0c00c8000195003554001d40c04404800503059420004d1000780001c014003144400501d14441e40c8500003d000704c1407003200442c40000c850001d21 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 866325800 1250 866324550 866324567
    0x9030406090801051b0903071d0403110607020631050109050f010c0801170705060d020309060601052712070306051f05090a09110d1a010510050406030b041404050607 73
    0x42c00e0340d074945014010001c59004141c80b0001808000716110485580003904050080d0300c80c0800d04101100b0701a40e440c0400720510030352280c0c440d0048107031403140096507404200e80c0000075a00642c042a08450001030315805204917040612a040c204072850410410b801e104580c0f5a44604c91001004401d0100449030103202000300f00c0094846402418a02c040c49010340712110380002884c01d220510030b142c0613100c00b4080e56a10716102042c82d000350b02c203c0310f01410303028010100d150740d807007141103031116068003020326803580c801c84021607a144400b03d8a640041100302c2aa420003003401402d00070f5004800008139850143c00c0081c4034861004a20384071700c5450400c2c0856a80c4150b0980c002c089004000703049041450311540313180702021650741c0b01081665540412003404848482007844420003145c0e81d90b41c000b442180c62000d8071b103201103007041c0300c113108451207036001c44d00c0b0100040010074003901a250600701028150f03400e84d4a90800801c01540d036821210a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 866327050 1250 866325800 866325809
    0xf12051902010203070504050f0a03050303131b1a0306012a0606050a120314040308131502010c0e0d05120706150f050d0f022421040f0b0403170903040609 68
    0x39880c618008400600921988c01a24440c110340c000c070340490345640c182d10f009103501c08216540d03824031003001a0020400001120b640c100648000724a044c0c1405000c11151510340c4204a008d0034102140650401450305040050400d000c04405440c1c3c0441031045801440070042c411490410605076901c5400c080c0c0502030000040205004030340d0034081058051603d60010010b2501103429441240d0020b4034803980440d032200300c180c0701c0408808464440034194034005d8500d005a00b80c44490007940e0200d4a40f000104c090b04100c50714030321061182d0142d8240940c4000742d000a40c000c18002d45410f5921064211080300c03900100b4003030300307181442509580c03500c40002c100b86000e001c0103000c0d00320307007030326808640300c01c150006400002204250705040745544600d0980140501c080140001c015000701036a03407591042c016500f02c003140c501980ca80d22060100400540214101310040500302100354842c44a280070b08503220186a546152410007042e00f50950007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 866328300 1250 866327050 866327053
    0x90e2a1c1103010e19060816080c090426070b071704050a1709031c0315050a1217120f0a050702030313081b0606120102030c0d090f12051902 62
    0x1d092038650003035000c0d01d044903c401641c01040d070340d20065405e80010700300d2031002c039802c103000803030040c1c008504e440960301e070307140c5a02020b41d94444050f82c9861401d0241d8100b860200404c011502d120544c503d421807404030079112903600504800c03644e101140031303502c1004d1b51081c02001ca03408240b110300e07142e100c40c090103d403c0030f03150a500c511191b40010084000304965203500e02215050750302451005040d656130544151000114110807080b0000181c81d0500d11301030140404041415200c0103040038410f1800c141d401c42103d81921350554403881581094000c1c1c040210080c5050a180c0071400410709003810318200540d000703840c44060606140400003490360000c1503030703441500140712090580050030315207034a1280d1079400011844114040200c420001810f501400050329078600300c101040400b800c03800260b80c40d03d0061782c10000b01ca40c91035640c03c000c030124068900071314803007241e07690142000c00f0140588013041c0d0202e4180000d101c004160110f03102c0600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 866329550 1250 866328300 866328311
    0x905031507020d030b01020111040b28050702010c0609290702030f0a0305070e120c0f0d0305040506031f0617090705030d11010e0f0717010b01090e2a1c 67
    0xd400b075221a00610707490209541e07002c040e41e03168802d40164261b050040c0701243d440c0e03100c0340842d9072079008000041004a03024000805034210035201c0801c01c900303507912401c1400c1c9030f00441d11442c10003821744245459440d95000308007000d41c40800080d0b404045004150801c0702c580c2c8800f0014070200c1550818444030030070b414001e080b5410050301d440c0001e01940c070100c05403a507003e1204000d4020030001c50701e02100320f001680e5240c13000115814a400440e01c001c0041c00848c003000100012400c0c04100700c1410706101854228091785550741d0180d0381541d0400012070f081d071007000000c1d0074011044007860608401500079a80380040c001c0241028003280e9180d02140c16007041200c1050500c1c070a0400b0750040c2d040c25030200507160041940b40c0122f55078101402010100030002d002d428410b0014810010329001c103031184400a4a4039038240b640034001402d110000540f42c400040442c00c804106a010074028400e64681c12b4004a90a14600300045005100d1508 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 866330800 1250 866329550 866329561
    0x915051309081602060c0607081519060f1b05010204061706030c2110061d0f0a1805030a0f1b1106070c03210f05030105100c02010302091009050315 65
    0x980c00c40309001024840043d00414a00c0030581034030405409031414080d60b803d2080556110015174068440710700707044000070003101046108480b140040444200c444020010381380a18507000785412542803c1c1d00561121310800705c5c0051805088406035400601809200d0300588000880400000400d55603d40300c00800d513500d030b96000c4c10b403145000c25140a092440d01003030a04051941d41914005031180089601030000c502a840001e03d42400c55441c020120703502034403c82d02d0b06210f403026250301886038010500028160702c40c00c0703540c030744001041c0108010512103c00750707100e05506006250040403407505000b04044c0022280000740459400103a0300c0e0201011612a0741d10403440c03510135039491840d0700050403103880d8404044041e5021400708821051a1034003000e0002c0301030102d41c0b5100034029280d01c668240380321400d030740c0b2503420710f0a03080c4181001460b00030514006900c6401c40c004640014200380418081c0d4102807003640004124221607400e2070821 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 866332050 1250 866330800 866330813
    0xc0f0c0303180b1209011509020306040507030c08130c15080609070302040501271508180a031b0201090e011401031a10050f0d112101060e04090503040915051309 71
    0x40344032050000201c103000c0b40d4048020752184c7ca44c00404d00e02d503034800c0c0e5507c80d00340294004480683c4254505800107201600900a203030b201d0f000c0b90341c1e0381d20700e50f503c850a030842e2441d100182c3da14080101c2c04a0448800e4200e410f4040c0300d6201d5008a01e0403600f01f191020000b4045c84c10180180010006030360044014035611f5001e06a82d2500c00051480320301542e107980c4901c80d000c4481528819142e0401801c07406910100c44005600c021440060b035560203102e4014002030000862580c19950107040c4c404d054414580581e0243e51460f10201c4a402038118031404217040043c013005680500c122028104442e002d585105446e8000407811101c1c0c000d01c9081c07090001704020211280c00480302c0145141004012468040390180302036040168942400c8100d0406900c2c680a0050000d04030340c140e5403590b103260801005d000180880751340c205d45603c0b042c0804509070000b400b84002554040150005a078070341000c0203040a40060142c4036079240910b582d0101c6c58 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 866333300 1250 866332050 866332057
    0x8070c031103073606030609120903050c0103020a030e060a0b01020c03150105040513080f030f060916030b060d1d0d09060c0f020a0b0310150504061e0c0f0c0303180b 73
    0x2c0070b20b183c004c225043c100186800ca0451000e440c124501940403041100f030f54850081f00d801001420850700a450003a030f01e084807400043c2c40da50001e01001030380c2d0300c0b80e0001c1990140c10301c0c0106001c2102503c151034030006642408070f0940f55400c00c44156810000b800700e0030000c0b03000300201d00b4429021300b41400f041c01944d008940f6036000882003c08840e840c005144d01110540d40d5940d40580355205410a444000b1a1004a03001c44e0341483c00c200d040380a1070412010400c0c80c0304098054000740007540c3e40d590042d5051203100c0780410b4030720840b110500080a01981066000e01c40b505040c20000a1000d003c803a90307080c0041980318007441c5103907620080d55409070138903000007140c0480ac1d61224254450000070486031284046042c412104201c0403da240b4221480c1902c0794042c501030000025154241281011600d41410380602c03442e041040c000301c1e03151201030100000c12419a042003d44804000b01603011003500440130900048000240c2024100f004511 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 866334550 1250 866333300 866333339
    0x507081206060903060c27132c071403010501030c140301020708031906050405011a1324021513060e01060e0702010f060909020609060307020a08070c03110307 70
    0x205400c000403456201c0104a03083c1a00040c02c6400d2868106c561112641c40300500c804441c00203850560807050b511072000740381c0c1c030007440c4901081418415000130207141d03010080c0f80b0060400c2c40140490700d0207000c04d54031802c0150120740d007080c00c07881d85500c00d0103005001c4d85c980001000400c3e04002d03c541070301c019600122100f400d100004e406805184009080c4110000c180041e0701c40c0400806003001d4000c4041c00816a038208202c110b0302c0901c0340080e841c203070040031307031800d5040401083c2000c1090359012801d9281d40501c0500c0041245854411904110030922141c041046940400c101c0c05420420b1400e8102001c00c420302050082370681c42e2441000791060a422480142060703118445140c07812a10083c00380c5040800d0042c2a450312002040154007401601010741c0c0180999103407408600c28400780b68001000070085015039102c500025905500901401d4003440e1041c45880c25807c102101005042d2014460b030f001c05d204100c001300341c0c3d44800605 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 866335800 1250 866334550 866334577
    0x5010315030203072903070816080403050a0315080f03070c0b03090316060e06091e0615190b03070305040b010b0703022805060c04080f1605060a1b0f030f050708 71
    0x445e0f0b001403610383c08220b4001d00b000781c0d001000300f00b00c3c9680a04914890100c241c0c3e1104002e151040a8a00c1907055501600240d020082004224000d402030403004510134102028a075803001e1ba64102144e144400280c3d4100051107400e10441c0241340000e00410000329241d401e200d81060b83d684500c11070006407140c00c12881081c0119075001000303030300300a4240c407068034005034044d84510302c0c20521442c11032000f103510000c4800003416442000c03030310303118034440310484100310720030107541601b201c450483c04e800300301031030064003550040240c0d403030102c0c0c40d081505d07080d2002d58058001002c040e00c10f0040d140860380c0002c0103400d03c0d26039032200750340800c41d4400a800d02e905580142091040d103060000f0301201714010021118000d00780c41301c4008240500c0d444404281c0c0c00e18800241640500a518190000303100808290a00341000d41409102504541c0712240640b00070f07040c145002c042c180c0100c00015203103860324146281c080e00383c0c2c03504118040c0e20103400b9078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 866337050 1250 866335800 866335829
    0x506130303031802180f0a15290c0a0507060e1806040e0318040e1207120318110f0a12060e070e1003050c0109181817040501031503020307 61
    0x300f040100b00349a48a402070312035059460903010038003501d4030a482d880c840410703540c005110900680702d2101d02c40880368070984404e2411b07244503801d540640942640f140c55401042400380054001c06140c5601000713041c6921060a01604210065000c5000e000ba90107400b00d142e80c82c010300400d010a0320441011684070b0074049002044d07000301c000514440001d60f80b2900c9503030300780300e0789a4030102e030240028070b0404012600c0d0180d002c8241d4031110305000c3c450008003140c0f00c3c94980c200900d00040d40300803014103400340107411281603905100001494001e400c0030400810a6141501c034000204d181c2480b007418003403d0500601074682c0c440c0042031044040c00204000d0903854080300b12807c060152100c02c0c070003440300b02e030207124200720f0625550244068500302d4490500d140c2c0070307408172070b110070140800540301c601d0103070b00c13405110004550680c1c000c4855204034a564903a0300f06800034045403044d681c818504c1b04108803c2004be41d001800e181660000b1515880 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 866338300 1250 866337050 866337071
    0x20724090501200102030112170c0c120c0301060b1b01150501050d0207050706200109110f031e070807060206011a25110a05011701060e0a0b0c0610050613030303 71
    0x443c3c400300e120000c0380d40000000201c90710207030740000e4090b001d00c454019000c90804024080c3c401e90400240d1078019441c1c4030310501d0800c0078040c100108005403042088281d0009085a0382c0340c0102c8480c80000c6a104130020300c155414011105c21802000290b000380c40e00b08441145104180c100000081d4008462006805482c681640201112101525404090280ca8120203c12101000d01038030150100c414094541d203a82c1192681c0986031409007401016002c1d10780e425058841c6400381c00000405552400d000030340d11004e42005800c0c440041e0501e46c81e94001000c40d0b100f8801808001854854078903611031444a0035540c1e40c809071109584c6101683c54605c400040030304c2000d00100410b00074100b041100c00308003407910351006540c0000e00e0350551030b5a1804800620a840c00750200410100004014843c001c0c4d55944145070766100f48a40c102c550000e90601c54660241040c54010302412110343d81404040c00000c0c01c6610341c0c0c800a010036807184c10440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 866339550 1250 866338300 866338337
    0x60c12090314030c0f0c0d0e06040b07060213180506010905100806042a030b1014030f060307050d0c090e0d020322090c050a09060e0a180f0606020724090501 69
    0x143c1007224801c9081c2c603041d00100944d00d643c0c0c011501d501191823640da200c0b86103480b204581c1920240303405541448407985982c4000d4108400c1502c546a694401198840042d402403911a86404000c10741c0d00e8070380001003464039540c0c4403e0050b450401c45000481c0c00c108038a40c001015280010078100d641c070ae10714441034401c101e81c6a500c001000d40f00481d03164110f6032400f4419902c00c1142d0380c00c04800c0b11249010701503045890703000c1c004a400030703210061180e08140000c00311042c0607101c2c4001814081020000c88405c140f40c8401c104440c024080d00c00c3c010381010242c0401048418080e403248146034105030032452148000c000e000c00522a04081c00e0030b07880404c02c501e940e80c005800f5612005501c000315081c00c5000501c1482403040c140f04003c050b045900061411164001403110100b201b1040c1b5201c2d09041c038031600178414203000b0f1070542c2c01451035624204800840e0361040025540b01d4000401045140c0e4100700c07102c04581b002c1c61700e00c00209e121201070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 866340800 1250 866339550 866339557
    0xb0306060604061413030c030b0f0705030402041a0a0603020d110309030f070303200a08160f0e01020123061309080313080c010f020307030b03150103020d02011209060c12090314030c 80
    0x10310303581c5c0584012046c81101c1804c5c50a480c802c1202908a44441603c01504072046460f440001c000300300207001828a9004a00c11441d02070f40340391050070341d000055817002c1c0c82d000680042e03404960103490966500588410040000d82c0d94910706009429640340cac8a060a0081c40c1000001d0000826200340c3c80000001e03881105141c0318403120900400550081c11150000384100303000c922010382244810403030000320b446004160346002c006a4000d500d01c001c042c1555a1400e5000d154805840e1440e400407600306400c1041c50310030300308055500030410f0b4800d0300e45003c17a1840024800300880b6080b8190303400c000e05a070706500c0e028070944034071003000250394203003e2482c000140c1a0040c60040d11030b80c4007813100030200710515a0358120020604040100d0000400160400150a64002c0d00600d0000100c0c102c4c0480101640d4041c60100c981980c1c03400840100390344104202d45a501c2a6000e011400b001e032030040660085501c40d640e00300000001c100c588820b40103d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 866342050 1250 866340800 866340817
    0x50a0f05041d030301090b01110f150c041a09030624060711040f05040b011508041203090804080304030b0c0309060f060102030c010f0504050f030403200301020403060216060b03060606040614 84
    0x40f01c2d036179030b11030508401078a580c1c100240810719000070a4180d00d80890a00324a050000c024078100d00100400c8c600c480c409800d2a800c00720030080802c41100075000008140800124903965412203c00d0500d4990020900f00903484001280c40d48028815048414501e040722150340315440c03400c2c848210034044c024a42c0c464075290406100f19102e42103544590f00032070076109180e03078420801804141c21030100340050b0082c400200000c0c4042c10320321011280f8a00064051a1580d85410340d0748a5040082c19038408a010410006468203481e84103c0c0e2941084c194104110029500d45001c0c0010071001c01e41c1001900c280d20030400c0d20345445d0314000a106c641c44125402c4002c02e400d480c2502c2e94021102c0c00c09102e000081124102c07a0712071a24200a01c41400001040ac0300d124076591554080000202141060000d46601003041c80e43c2003540c40300e4a403401c01c80d03941300e0015020750810001c010701d0359204415141100c400c0d041061030044480b100d40c00500c1401b90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 866343300 1250 866342050 866342053
    0xa03020a02031c0b030105090f0a1506050904030c0501060605090a05130f06090204230a0e09070509042f011d04090c06020c100c111c12020c0a050a0f05041d 69
    0x42c0301e0071003d0283c01c40701c440002a0002c10803500d0f041c104a80b00d80ca4000c0001c2c0c15072004000a002030005001002c04218030500005c0d5103803031310300140b1100d0060310190000382c0c0103642c580074040b087c414036004106504010349000346583c08204035031210700c10280300d01c211201d000f89500b1a50050381511005541c10021151200d480744003e4119014a03c0821041c80701e0743e2125500c5d500003404a40002d00c811440c620707008848500010080c4240d9480c018a840010b0035211b090348540a640321300000a00c8008a103000481e00d88161100f68040e00220b0100e80d40e80d8121004420115168031307002010044d80c004100504084140105466107900d000070340c0a0380400c41100826040322950055000c0c00744c2125001c01010f400b40040110031002542890b00c1681e103004115022583c0c8040d8182c0d454002c11030905c0781400015802c8144125024980103880d100a05800c94040482605090040940003428014540126925080c4540e202202c0904403001580d840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 866344550 1250 866343300 866343337
    0x5031e060d2a1707050402030c0d0203091c030906180314091903080a091205030d05072618030a080f04020d02030a080405011403061c08040504060e0415110a03020a0203 74
    0x800d0100b107050f400c1d5108280d00490001041a1800b030003102c1c02a110310600600b8109074698000c000d51001d0300c20319580c0703c2e4030b030640c80a9904820b1081442900c0c0c900251a5401e03042a0080d5031600c0421709696032035440100000381c1080d0300303481420031002ea142e00c0c0d081c03000100320240c028007940200003444003000401c000002d4002c0803101c1a90b40e0b07920b6190b03920300030340302101e1040170010000e070810301402030034000f82e82c03000340d000301c251405c440d4122184183d1304e411345445443c40b100304000c0b8100603e010600542ea1240c500110055141500441380100361142c068101100c940301d003004034040d503460024030110351380c0040a03101c00711014604034400d50700501c56540484c101c400c100c10016100c0e03003503e1103008040d0034107005003000510003184501c2c600080751154020307c0045041e444a21840015000065002c002820702d401c02d0340e002064007400000c1d46082c01b80e80c4404550321000c2c0c1c2c600d40400e04016803071395200d1000b81d00b540100d071110b517010120700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 866345800 1250 866344550 866344559
    0x160c080a051006080105060a0e0601030b0a0e06010917151312020d0806030307030503071b080c0c0405100f03020112020408010f1a09090706140c03070305031e060d2a 73
    0x8155801c00d442c000c1c108000d0550b03100a03030f03402c2c2c074001c641d0207a222210a0040019003040802140c4c0314005160003d1809140300029580e40e6290300005c2d0110103420030401d05580260200c4054045c0a080d000c8030407107290b0700c50b61980030544180001086c0c10100e5142c0c1c1c0741c901201601c0e5408400d8500c1d0f00c04594009507201c4040f0a074900140c0300c4008111a800c01108039400c00f9090390b101459680c03200d800f43c80d004003581c2c81800002c44040d5507401f04104e00d002d840c48204d1440a44421204001000103450001c0c10803d0f01951030b550130441185408071090480f98282403034038044a11141501c001c0c003032a0710120055080007044002640346a0000d42d03d022944456460460038200f030062001045030250030700e40c0105810300505014071800020700c214288847e1a106d61003200e1401c0d5001790703904038082000070003030069030303407816108102c1400b00c0080c22000e450400001107011488400140000e00c2007250070707514842c10000c4c2c01001d00c00411000300150354 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 866347050 1250 866345800 866345803
    0x50f0c03160504150c0b010b070b0103141e0709230a0b0d0b0103030305100915090222030515011217090f0409050f010c0306081f1b0302030118020906160c080a05 71
    0x3010845d40e001606c800400c0d91a42c00003503516445d048200003405a0940ea240c0a507000e5815900d45d40e849542c0d55140b00d01a2044980b50041c000c10282050701c1c03401004000341c954454841d01c04440c1c18804466216402918a84c01004180080341c41c800c02800708001e000341e00406082544040004400c0c036130160003c034082c00000744159405981c80c8034040c21500419500145400511000c100342101e540180c1010801050486a102400509180740c14a41d46c01118503401003030101c201c900d595101640144034078001c0d004d00c04899516030000d5284040c4590707650300c001c220b402071030720342403000328081002400800c5010450301f003080e6100b0000318403178403d40c2014040690144070307009075000c480c181c00c0108401d00720300482140850035410468480380c0c0d951003140350184a07211001c20004941ca00580c0c1c1d50410650035139a41ca030403002031640d80108480e920302e440d00411a40c00080e040c000640701002850103100140d03a950021409205010849003032000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 866348300 1250 866347050 866347067
    0x30f05070602060f06090a0506030f07080f0f0120070c12050114070e01020d050702060c03040b0403030e0306191a0a1d01080613031d03071701050f0c0316050415 71
    0x4090b003c407901503075440981580e101e02203400303076046914070f808a002e0201e607070001504a07800400740ca21100071010880c0c07400940c2e038401a0b40390b00440c0d00d408103200c1409202035051071074001b44486a000030008030a40003801400341d014000150303820901190300c40800242c8410441200b140702c080c2002806005404442d08140b9840d9011803234540c010300000c0801794044c0c000d8001c01030382650a69060300312850a81e0404404c00400d4180041072000b0f001034000100540e40702e2342941030080c0404001551280294059020f110303c039851042000f8694148c42ea02003600f01424410004113494050602d41200b50a8004240300c50310003c2e8040344c0c40941010300e0f41e1707a668409150758040507a00c400c0f403003846204110100784908022001080070b40d50740d0b408024204040392406d140369019440a07060000e01d034204540a006003034209184000740c1c031b050305142440001b9440054020321185020511014007075010b1003d0320f0040681c071000100c21800800e0180c00c001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 866349550 1250 866348300 866348309
    0xe0d030f0f0b030613050c060705010903141809040f02030a0b15041e2a020601090c021c110f060406050f010807180f0b0613080f0f1005040606030f0507 67
    0xd00300341e40301585803818401d22000c10001001404182c07181c0c160401307103420220042c0c8580c0900e080341140760f1250002000c07603e10980c0009408895800d0080c910b840d20b18055068803400c101005442602f003e12980f60142298061416152490401e80103c04550b0003505402040c00f00b4060102c610031240c0309004140908100542400822081380c139070170041c45080d00001d0110b95107149541c00701d000320a503c2840ca021480d21001081c145612030507403001070b4400c0d001072182040c0303802601b00c4401e50340002d007060a9003900703402c3d9054107924440104140120704e00c000e4441001002250b210070810f542c0305c0d061a0401002400e0129020740203000004000110240c0001c1d810040b10741001028070010300710400c076800b0304041465888021b0302c0714402202640c548009001c41c0d0340c40c82848021030b1070f0242007030070503e003080d01c201d80d50044032468900300b0003c2207003100c07003420070400602c581e164500b0200901a0f60400343c640d2083c10421010814000b61010584 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 866350800 1250 866349550 866349581
    0x606030e030909160302070515151e0d021311030402030f0d0207031b030606120201020601060906122013030b06030d0504030224030a060302092a0a030e0d03 69
    0x89000c0c0d025964440d0500381600700d4040000140740b0002d000d4108000c24080c80d0142c9041c80300d0301d4061502000030301340503031200d54405004440440003d0f82c0681d1909a51540d1104245200f00b080c02184448071800f400c030805040c0e08654500c1c05659a02c040c11504025041d40140b6460154104032000ca00034882ca005095500b403000880b00c00c0c41043c8da008080c0c46003543c0d1206415494110344007680c142c00b82001c80041d02c94000c00c0040d10800b02207000054050000a03c0e1910690086043c091100c8007407000703a5000010052034185248049000200c040a414540c804031042c1983c00c6004511503100c064400c07610f13401c80303014804070340d4540c40300c20805450740c0b540b90408020072000c010400043c00e000c6003035600891024804004200103041089076940f0440755030742e540d0365440c81803013140340101c0c80a40162150007039000150419607400a00401c3e01c4000c40e8090020800c04030303051080c2c01030010100800c09a81c014000700c1005000b414603407413908041d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 866352050 1250 866350800 866350811
    0xf0201031e052406030f16020a0515070e09040b011203050d0507090e07050405100f020f070905100803070f020427210f0c020f0103022b240302041815060603 69
    0x51340780c181c0603240501a241200c0d500c40d01c41c1130111154541842038203003036004101c15080031030418826040441c0750300178541071600d40100003c0ca44041507074000c0c49000d03c5401c4c0400f0806000c0610b0550300304903601000c1d21010309050714140101c0880345006401d080411044a80c420007800486a14652076041900e42a80556960255000e800d410484851240c415144202003450050030ac1e801521002c00700700440b2070070b282068221001030760303d410502c0485c2030640741e42c3c13000340380c10005581040c080780d0328801c581801480113131107940c80b03400b648402841091822001c426044000042e130b80b0134541001103401d90032620718022095820101007a000303c8025110000d00d5031a08620f200c1a804c00c00424802200319041650070310021a810705402c40c903c14107011019400b011854070780700041510801f481500311020f08602c0c3c5401ca0090200d01c2c015241d044170003103102ca030082841d03500c0520703000002e840112002001683e0740700940c000010f85156903818042c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 866353300 1250 866352050 866352121
    0x8030a091e17161209180b1521010305010c020d08060f0409030e040c05041e03031e0c020916112e0b1203030a0b0d0f0201031e05 57
    0x4800741c80c0d80010304110582c0b29251640d900801c000c1c0140e400c8640c42e0700d0a44480d40380d081c0450480590303000401d0100406001d010522030740c1e80019030410000b801317a02c24a002140000110080140c04080c012a444a101503e000224030102200c903603000d0540e075904220b03000e0310340e1102072000b5000b07200340751007005d1045440911610024142c8441540c0f8042884000d0242450039030410010b400074011076902da0180d041c003040c1070b5540c561503a08211001803d50210040c2d9040e0b01d88401e41000004c1d00400c2c11030000000d401c190740c07003400408083c0d5038041e01090095118503200c08101106080c02d00d001d5070110550b0314542d1111810807001c1d502e00c641190407903180d114042c1e0400d0a14a4103242c186a561303a01c01180c80110031022418440506d002d50225030008820846e08100d54401c800745441c045903403103210b0b03540380c0320907001c07082d0000c000e0b04141d11501900100310002c646e10121143c1e8903401c20081c80e125000e07100851a1000d81e28801803000303046030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 866354550 1250 866353300 866353343
    0xf03140702090f0a0e1606021605010e120f0304090221090c041a0306010306230103030906120b120606030d03020f030604051b04060509010f17060405060d08030a09 72
    0x8034040d90142003401c05468001607224a110028031184402d81c0310030b15a00c0c02141402400043c8816510600c4107504040000c1c2c01d01580c0c2d400d40c91429079600042010f40c3c1c0c441c01c40d10030804265030350000040f041070810f040111062603a0001c1c4000500042c4108140e801044209a20114292035003150b03103080b202864144d0781541d6684c0002c40541d0180303032543c440c1d00910951060042400d403600d001ca410318009078001c1d05c101790341d080c0d46040341a008403072010721034201d2000721300340d07048d40da01500d0000c49000701340c200718083c540004c1d440e8a69100b030f0080305004080040260711506802d81e11002200c05500a00038200301041140c006d000b45d5203c002c0c451044e50556407014180002030200a181d600001941000000b6101c40030005002802d21a81c9660b44c9400400015280e403001d2030019041241c2c03c030b403181110649209060704a1000c6801180c2a02c0300383c002424000350402c0586200000024441e10303c010b90f100c4035029118081e204d042c0025a410340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 866355800 1250 866354550 866354557
    0x10218010905060306010e01050d0603021f11061909031407110f06070b060411090d110103111606051f08071d09030315010c0804090e0c0301021801050705010f090f0314 74
    0x1140884c400e0039400c070448d800359014100d1001c04540018155540e50001403041074140c0202242c40a010032018007035501c40580703100071007071000038000360801c034250311580d05050138403c403803a94030f552500c1014450000202034050001e2407940368521810640b944c040024890391113044000148040360601009950681c3c0d00411223850980c0e4580603c13000d4400005a84070202040000e850035a0f1418000780705240203142c4000c030f04203901c0016048403040030110404640501c03240c40d40c0080d102c1d040f0f450940c02440480c00f42c8584442070340d051414030002c040d01c1c2070042d001c1210107000990030115000d21046c410601032056030701d40010b000b541c00d8015500100300050f5414462441c200c900c01040c5440b4003d01403c0d00c4041c000d40013a0840a41c071a01e521601c4a6176008000c4104500c00c128001c502e41410f8400780a4078401d90f01e14141400008244581404000e61050494540305102170009102520342004c5100d40141e0450208007000804459408080140c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 866357050 1250 866355800 866355811
    0x2070e010618090b0d080f070c171915021b03030c130b0c07060c0314040e061008060a051e0d0b0105032407030f090c0e0601030e0a020906120a050102180109050603 72
    0x1140300e00c20841c2c0316207405031f01240042841d4003040003841d00003544c080800c0300500340c548100000026503084241410700b0050b84e00d500440c3c0c400001b0114100c61b03554001c980802900580d80c101422840c6989590f040ca40440c07400f001c401c114100c442c07400200720503888680d000040715141c64140159018103868080c0c5644480002c2c461a4059140102c50b0f40c02400c00071074001c2c050b21100c04c150701076004440c417410500c1c01e0110702e09250484035030400240c204001c070b41c0341040c04145051014402d40d0320598866090015911302041160b80c2032501610442038401c180c288059102401e100700d038028891498011400c1c1065514848110710800b981252502c1d4850104d01a107134290f418018956110342d1540020920b4020400801c5010900076252130044005003c4800b00b054002040d00541c411000599602c500c0c00c3d0b100e1300456041002c82c400c220400e00d892070808000f405580b001038220400c02600041140b01c01090380d65103441d580b11400d100c050700060f41c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 866358300 1250 866357050 866357059
    0x13080703110105070510020f04050a050d030c0210050903010203090c011e090b25030c03020c12030f031f060e0913080a080910090f11060c150702070e010618090b 71
    0x1040c03541c4680c00900c4c1d568007036401c0380c5101130903100c80c2c0201e07400b9410700085c48000080401840c10483d00310001000f08942a903110a6180c0300a04040225400244521100701900003014040c800341d80000070007500864807440c0c01c00c40743d96100384101015002c034681e98000d007800480318111418081032aa81c22060a02d07100c9807010a8010000c603040704500b1803003007020540851300b1064803900130b81d0307161000200ca007070280c20004180300d001d005080ca00400c40d484400001100da02d4849034100716541c3d90740c2c03020300804036420391f102d030140380308010f000580d203900201c0521514002c803111041600c0348040360400003580440281151001d000400c8414042e400301c40d8841011015105003010740b0322920215030344613030304880e0401010b003000144420000441001c14050300e0030f87c60008820410342e0764109100340041039a01010006800704d100303101d580004d00190301024003658603090007420581d241d841e0703c0c1ca058200000000d4107600c80c003e1405a900182 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 866359550 1250 866358300 866358323
    0x130c12110a0b04051c0c03140109062403031206050a120302010c020615100c080d0e0708010b0f06030709350c10050f070b010e2203050a11012013080703 67
    0x40036480300f0612517415511501244c00000c082040c0d4403a20441800d50b100005201c001d902d8105c084802000550122801c103202c10b4007102102200042502c0e054284003842c80c4030030389000d02408584d009180c10000c00c000004500003015602101d5510a8009200c0e0700005a0100c0e51200d0440b002000780c01454044001c504000320300c560f80c052149840302c5901c4458680b000c0d143c1c000b490203841c49a492044070608001480701d0710141602100034001041150005015003804c010384500c20100003000c01d1009004074000381c01040061001019120001842c2602035104151070080b02d60f40381c10302d100e04402280b129480100148040c4d8046450b0408446580281904c4440308000b040420085100035240c13900910312071100740e104d07207800940c842e41c10350403034070980c0c11a28a040441c00079810401b6100c4403ca94905040a4031a81e13080318050720f0761203a469a1100300c04441544581c400c4014900d01d0356404811030314030fa03104501541daa6540c80090541c03100d51 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 866360800 1250 866359550 866359579
    0x1507140d0c020328090501020a0507090509070830130605160204051006020706050c03030c030402130e0a11060a05040317190203040503160608130c12110a0b0405 71
    0xa9001d194180794520441e0305200301651142d039402100c80010040c54203890461a1081e80030f03084074094202032000d13160540c4265150f5581d000103014044040c0d48480c0080e6659804120f1074005080c004204c850900e414900c04500c6803420800c103244022000c900801c1406201c2200c600f610b01e44000b8021900d0150100d0300c941024800045a00c5a21900300240e507550003610b001c1c1104991100d4998641100130789050f0f0310340e109905000d02400114145007021060b2a80850071295040e0b40b541d42c3e2000480824120320400c82c00d500d800301180da0000f000500d0b4220b01d01c644544061643d06d58104207880c0100032034103001580070002400040d5506400020b1402c0f12040b540c100380c0e44803194980780e403012114400581c00490200001d1a00300f202c12444880f10640c5c00c04141000300050403501c0c020140f44d600c0705058626010841f00c03501d0080105040c034401c00545415150a4491003030700801a446074650030700218289080008490484000400b0010402c084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 866362050 1250 866360800 866360827
    0x30319141c0b060d020d02030609070807350f151f031107080f0a0e0d12050703021c0207030219060c1e0c1d1302012c040e150714 57
    0x101e000b915004102400340c00c0b80d900090000d03040084020304056100c0c84e01e0742c180030500500800c80003c1000380404d010f5040d1300a46140070791105004d450b2002400141211140d081d0940c2e00c10340107600c1c008012207410039130900f5010f042d415008070904070700001008042c80114882001401c1144007001e502e82c020340c4285040400e404500e806d20105840e561100d4014241c1e20740c1c0d034900000c440d0019544410002c0402d80200e6201c81400b8583d1984102000c147c5a41c1061082c001654011705001300308900c00551900c520003500b28018000070f40701c0c0c0303845c40308a0091f0800901c034030036200181041019580aa600d424804142d611a50a030001c0b108000d441c410345c004500010510000b40c02018000791404825225240c520300c2c14902c80c020f04040001c20300c22541030050381c1c0500710003e070345400d42500b001822078180094028520002e020352051a0400f80c1b010307103001180320041c90703d1b070a25081403075880034015503075181090f902c2019014100b0141a03040031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 866363300 1250 866362050 866362061
    0x82205090106200a05030a1709030717221a0403050c240310030c0b120114030c120f01110f0403080a03020c03160b1005060d0b0f030319141c 62
    0x8850600310800300d20941411300071300310382c00c5d10960000181d09040340e1b08840c1d1492140f00052880c84146082441e00707442e400f5403074000308601540c10640040f2460201a1500c145021001042d02841241359175410406445021450303201c0d003840701c101c8500b0078192012203400c000138203900c03414441000036140b2113081c2100b090001c01050810205410041c5104850b0142d14102c01d900b582001328010545500c0401e074401c040080c0500844081e100b0b0f41150400186014001c0c10380001a0528420a1000d5048031540411003800e900c001580002d950004000b04003030b00c014058008280b00d404041e1200301070810040000810120007803440072109d00d001418400c1001980d81141c0c004200781920700c49031001101801812080c3c0c542003088561154211464100802c11034082d062440072003a6560109081c15181c07017001040052004041c0e030340ea0710f8035944015408240c21511030000d440b08426548281d6400211240450030f0b07088001d0308034034440202c1c054003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 866364550 1250 866363300 866363327
    0x903070201020312220302011e0c020d2109080304150b1005130f0e0a1d0a020904021306031a07020a0f0209070e04020406032028140304082205090106 66
    0x114003002c116400900c1c1c40c010700c010311950001c03030003071540d400700072712840042c040d080140c7c81c0084a024031500041d0420a600040c10402c400c074803401d03000340100c0e4441c541001041c1c24200c8802c00c0120080040d80f1540c8030b03503a050210007030b254a41d8100c0720b611110341e03004840c2ca801c141556002d440a000da011f164080c8981132b60311144415038683c0b5030361140706001d4030841480311003011801103c28480031001e4858000c2103140144c0d40d20490403101901510105011a0940d142c5000d412170342c991000d07082c8921b50b920729082c0b150040d090015a141c0d0004008030300d4040c40404e8001c24503400006840d80c9201d03940800840e00e070003170400c405200f070400d4251001d1b01e031030010740014001a03c0024000c01001d0408072070080074984203010f032004001d61070003440b030100d00b00d80e01e141d0318000b4248403550400a4542260540c1007400403a008410001044440c00042c5818070340c42c50021003440b558650203158200c03d01515030f10245010041c8003ea02c242c0c58002c0c2075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 866365800 1250 866364550 866364571
    0x60803030c031f0905070e0d11040b01020a020a2607080a24050c030603070b0c070b07031206140a050301020307120203270d030b0a080c06070804031a0109050903070201020312 77
    0x452000c049a109039105901c054130b1940c6a80c100035803590401200241c0c280103544c48a000705040d80ea100c0e482c41101c05c00ea20a642c0d840c000c20842e44200055400c0740d03405040d900100e91520381c001c03403030059400c030650a514800b083c40c45c07200000c610842200e0080340200030010103031340c03480e81a004d0350720014240140c0514203001e42044d8000e8a004507070070307103484e40e076801c004040c9401d100e400d030014101580100b00e20305400300700260710012034082e86e00460300e800403071801312481405040580006418000040361080900303545841081c000c503403043d41c45a84005042c00e17030201300c980802240c0804040722403009190000c5134010102c2030242450810748980c1c0400e482044a001c001d540410507143c4d50710780501c100b49000c0405c54075031028030b113056181c56aa81500080368040c0c0c0c4081000d80c2007155078429030b0065940800e00307641810122031880c0740501b0900c00e95211a0410011038600d420120848280f19010380c055480c022040020306c00c000405014420748 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 866366906 1106 866365800 866365831
    0x1e09060d0e1e0c100203071a33010806030304051c020906091009090c050423070f051602060906030702030a08061f0e03120a020705010909060803030c03 67
    0x3440350498021040070790b162412801c5004001f0003c00075490580201d5031450b0002c0103521038040b070040030618131a058007800e81001d0b0384504405888408401c900c60794468031502d50300c41400b0342100d1410b950f40c00480d080d000384020040d07071b40300000031960852405c15903c54005800b1034180c529030a041040e1060012244a42c0c3c103120b80c0e6001c204100300b184a40c000050038014000c100043d14480c0c3c0c2d5210380301d06480a001000300350f000419441c06141600c128074502e903a09401c1001008880020a0b500c4c04140e0340700d4410700a80889036100e01c000c521800e0154091a1070f0302c5206030181100038081c0006103c4c848a0000d0041c0e070188540c0741585404501d40b407081c92035081d01003805c00704455010901c110f40011420141500010900c023140c4084e601d50300f090303650303450600c01c880d580d0040c154203401c03c00104411101400103950020b03d5144511030 = true := by decide +kernel

theorem cover : BRFrame.Cov 866187050 866366906 := by
  have h0 := BRFrame.cov_init 866187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 866187050 ≤ n) (h2 : n < 866366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
