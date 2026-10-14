-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3501
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:50:47.399709+00:00
-- url     : https://prove2.me/submissions/163e169e-69a0-4f4e-944b-d8395b9b1055

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 629496402 ≤ n < 629676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 629497652 1250 629496402 629496409
    0xc0f121b0327060f040305031809040b0c030c0705010c08040b311b0f051c02010e040b061e030a050f07050706090c09021c05010905060d02330c010605 66
    0x909078042e41e4000c0300307007500b65041c9148078800031009005005036040c541c6000c414203c507445a08141d409030310106d890340046000c0d10b05294081c005a4250700c071403c1941d5042d510f41c001a01d0070021440100c00150b06400c2501621a4240c01c00001d100c1c0a004980181800d101642c0c1507548185c6400024603920318008103909000002002036171059100268a02100f5081002c844054100140381c029009000c42000a00b0720100000002440d000c1000400744248054000d041c0d210040240540c0e0090024825a0f9013501e002c10b0f9118070701c001508910801b01c0d03a04800c2140011103500890150181d4410304a141e010010b0752902d00d1000c2a00703008681c500300091041200100003021500004a1103201e07003808620395071503c03141c000740e070402c09860b001031009181d1046c80038118041d0b6401030200c124104810304000c4086101154900c00190041020150850303a94010b09550b00280320382c1000007042d003040c9240e4078a5035000071882c030700e41e6080840208051030b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 629498902 1250 629497652 629497657
    0x4090209010305183f0c0d09030809011b0602040f14030307050a150f1b021e072709030c2604092304050708150103170c0f121b03 57
    0x40b01030020490b1132010117001c403100b41e100c65400b0050001c0140315452031400440035a02003c040c00490f11400d400c3d11844c0f800c3e01c00d010b2502086122031007040440c00c0349040341d11060b000c4c600f0030b046c140505d4074641c103040c501c400204510f01c00100002c0890700302e08500c0a45045203107100c2c0c1c1102030410541c0e280121803000e040303500480309240010700090b03031400103003012600104000d26217084a8040300c0c54190301811041d6a055400f080c6907051028410305d0311002841140c00b02400000e650b2603516008180c5407404015411444000141c908003000500c407805004405061500400c61107206100710786140102c00d00101c48544505e01c64090104000440d090a2600650070060100315046039003c594841d4049415a600b865272032155000d00003c004441c58100840d161241208440c006035010400520000301c0310510408ca001708070440e80c1d1100340c0505180e0410288410024403441080c141101c000c440304098001601d4003c850401655481483da8491 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 629500152 1250 629498902 629498941
    0x1b06020a0201061a0301062d02010b010e060a0207090e03070b15010e03060c0703033204030f0212190e090a0e07050a03050613170406110c0f130504051204090209010305 74
    0x413001c0c1300500a0a205104140d11489071603940720040d41c01000382400700340019101d10040c0d44030340ca81e0341076580041100702034103c240e41407482c01138030840080d1104600d006018440707031104225140703540c00f0000e0350b108179005107075480c05050112150b03400c5500395051901207401289865410314010800a21880c03c40b0001458107030344e80d608500030142d10090000b0b0582001c1040d080140e4040050203c0e00621164000e80c142424050404100c40410200311341c0540802d013003200c0140c09480136800f0041a44070981501c101c01c1da20782d40000019038100541404100c2420050b41001e20303000308010599884079181c80c1401644c1000f40006402540054003003071408542100d8a155a40100030440c4011090424101540e205a0000d00015448550a2102e003400c0c4179000d04120202c612001c1e00410b44c003c00e64480300318140400700c40d9280006400d11409101d0001c03000451500d2917511519500081c009401c80d0380c00340d00103481d24002030131020070656400300c3c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 629501402 1250 629500152 629500199
    0x5030d02010b090f07090b030c0d0e030a0912150212040c08011a060d060902030c0a03060801091109040305090d0f141b150c12040e1506191b06020a020106 68
    0x441d135842c900d4280d00b0402815070410090765960008520340c0c1c40000d14016111000030540d90502991341380c0c1076519284040c0f038190010050038044a170000340c2d05c0b04494103042d942d00604c46504090900c900e060f804900042d000250000400c505e880245220307501c52803035100d5490b101c0021600302c40b41044801a41110031480c140c03545030110141c0340c1e6414103100030a203161981001c00a0f81c100340c5011400305400f1558007641a09070060f47d014154a0000b04036402d41a142e0301c07840191880c040703000f60081808101814030420840e0314284015114050108091604048685400600382d9080c0413a1303003003d03544900400c0e000d0341000094070705554540c00d6000c000c030003c80401201c0c40501c04100c075200204043c08051011030644c06025220340c80c00300c811410f19002004403480000ba00c1489040340d84090944003000c140c5000c000080043da41e041d138601400031610940b4200d4071241400b040030300e4000786641e8519500a11800c0d0361078805869003d01000481e80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 629502652 1250 629501402 629501419
    0x6052805150f0310062c041101080601090e070206040308090318130b130506030d140304080915070606080d0c0201050d0c091703040306060b03060306040f02030f030f030105030d02010b 81
    0x1458944544001402c05004040c1e07001185921005001c0700c4042c1d0004a01c04c0e903a540308000c0002444c0510440640498481c0403460710359902c01c030801844454606021341140400e016900c503078403031005400170442d5403e003410310150203541c0d0307282140c0850005101d040010800000030061f11990340c1960ba0420b66210b00c4c00802c40b412028800f880b100c2a618045d80c84940d54440d481000c50075401c800080310300300740703040c1400c20000c1c45641007070080130b102c00340c6038880802c21203610a401003006a212041000003d00000000d02a0b000000b00407a112050081c2e40e030094048031a40c1c1d00700c40e642c1104402c1591800c8000201a010031810300200e10451250381090120103031a180030b00d4455102c0b172030304c4405600c0d40d0703034507800da400420f0600810240d031040e40c02415800e500030341945860800640c3d6400f009100614240003d03605004640301040b681e5955021603058a854121115110086801c2445a50321130300c90308440c0340040c2e00620818048050181448a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 629503902 1250 629502652 629502691
    0x108060d02041b120c0306051c02061204110a05030111040603051e0403021f052503090510020c0c1f390b070801081b030a06052805 58
    0x2504400048040c0d80054039005069446000c1c40c00306401d40c003c0ea283c00083e45420410700d821070b400d020350038003454a07200080c440ca645d901031459440a00a440f28201c0d602880418110b010b00a00070000c40c03a464103100070443c07010b903588912201075a58000c0c295549040500740c80a081c480b005d4034070304000074000c84e07110b42c0203903038001042600b451000100c40784110080004813810781c0140c10180c441c4085c01001c03030b02c0c90340b042039014007030003681003501c036264800c00d45020f040341800c000c02039004000d009401540c04c2981000c00e5907000e032420620240031351f0007010b0407607440c0110b020000c4289080c0891000f0381580402503010140b0b64101030b540c4030070560780d80b10400c00c258000720340700e0760300042c6142d40720409140400401007441c5c80c00e84100c0152401091100180c014811b50000080d02d201c2394440c0856070b4481b490310750220f8144401c0b12000f070101410305d41000704209490100c801c1060400030103040d6848620019821603070700752032221000d124050744c1c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 629505152 1250 629503902 629503909
    0x90a1a091021020d05150a0b030601050f0f1e0310090b04020d170301060c0c082e020706020c0604020a151b02010908010e0114060402040506070609030302091504081b010806 76
    0x1400394000c030b50414000b51045800080303000b5090b0380100d501d5401740b4a0070b0303c4450804450703504864082028080c0007201d60000b80c035902d05000b001e0141041c0d002c0300800e6034940c045c019503920064580700e24a4510f201805581d92100d030228041d11501c00e0f03d9100e0f160038840c80f185203030804c1d4070025030b40301d540c03c110882c05002c2c800d03a89072a402c00e0342051082c10000450007031003291200e010a03c103900d004060303070015510001c1340390400b6640c3c0700e014040300000521480746080c0e9101c68951040d501c00280542d800140426101250400c46c900c0c1c00261035008500885440780510313034a444940101c81900a0440014480b52103600c010205420059185205040141c03500c0d8442d885079003180c007816024021607440c0d800c48241300075200d1249400c03000550703083d0300d0681880b011074000d00c1000802440c05940ea20440300b8140320ba4142da16042e402814003001c12040c1150715019000340c00ba045560003600744022410601c00c92030700c180441071f1151a110b96601040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 629506402 1250 629505152 629505179
    0x20a08091503010902070501060e06011e021002040605090a080d12020304020d060f02070201030b0a2904030804080709050a0b090408090d06020a020706021e070e070905090a1a0910 79
    0x249412000a001c0071000703008180155010713008141005854020a04061b425240698007a00d944440d0b0018454181d03442401031000e107094a01900001002c40c801300c5c80d04680300421007625101050102d00f04e94000d0080c00c40a404444041405403105c1076240c403444d002c0e000c540070035206403a00382d10401301d0b005164003900003070607030031003580301d4076480c0990b440d2010360411a0b500051502c210768062048200180e000d0b40c602100d03604140323800c481401c03420401e40d52004980c60601c0c40da2120400c4030051036111030f05984469541e01304c25502c070320501170440c2c45400c0000103840305140d07121754090321300010b0008410780c65903103d0729925404100490740280d1025002d001080260004104100c040d6000b4164289014002030034954107000c000461a2a055043c0d0fa010001031308006850f8100c1800e4020f442e081d0701510f200e00242d00c610b410440200c10000c404060340e000642211401e0b41264201d494a410007401140c21503203814510348100040c000312052114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 629507652 1250 629506402 629506417
    0x601061202071b2402190f120c0c0602060402060403060b0d063b03070b0c1306080f0105060712050f070501050c07110303041d060a24020d0c03020a08 66
    0x2401803401c031140e220000e001500d90301c06400d00243c544100302080824840102d21200740f00c44e1045642c09070b41c001d4841b504400b10a03030f10f0070032100c85024095034a14003149030790b01c0034401000c81072020000e085200c007007030b05441c402010040096030318004258584213590040c01c441c940f504660702d00000341080e0b0f184507005401d1312000000a0340911401c0c5020f0742c1003109040041040001c01600540842d2030030088030550100a24042c00100b40c48045500c910740610560358926040c1541c0540c00b414940310007007900007c1c1e4560028121030096019603c1c011a40e070703c60b000d101c0b03548200b86008100c503404900d9211402c0c0700c0c2000c4c002d2080440c2c4801c1c944011901c802e07094520171707a8082c138440d030001201c0c410802d4290859a513144280d007e503040c00d142045081c48017151840510703401d05000300040845d034980e0172403800342a4140b9040b004440310390b1a4480c0c102500c500601500c200c052220b81180141e07100b040580e4158010b19400d811591000480e030070491 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 629508902 1250 629507652 629507687
    0x12042d03080d1a060d090c05013207050a06020910080105010f0f0e0d060b0306010501090f0918020901090e07051e0103020c0c0d080a1706090705090a0e090a0204050108010e060106 79
    0x42408496a507134004010303140c280030300424903040b030741442c911500e41c3e41d000c6818401d0744181c408004100780c925803104d01011000c0403c0700c2c14400303d460984501e2100070210b01414500c0c00400c9440e5001e401d2014040c0c5403070640385d040d1401036580305028011980440c89a04101c40154896203007034210110a1402d00c0f08010306034046004010407040450758543c5880442485060400200340144002d2800029091070304000e8030800d45940140c054450301c44440e178a0000480c4904417580768044c0a0804a41c1c0d100904001054481a94040c40c0200303e800a000e18102541c05000a2051044003802c1351800c01500250f100e0380848180c0d000f04210100280d64034906110034074051a4290303940d01401000401c0c0d080880030581c14400003409200594403000030660780584142000c81d0750300c03206d10014444030b00701e50000c114001c02c1d03410001c140c400882c40c0343c078641c826a42130003681d80b600c111038242c0b00c40390300076106a844a4010040036100f42ca24109a08655 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 629510152 1250 629508902 629508941
    0x80703080f220602031e0112060b030601051f1b0b0f0f0c0a21060617100f09050c0d0608010204061704050a081309020406090609140102060408090312042d03080d 71
    0x4a1b0f4041c07450b009a20034190b035890845940140a9540580030f0020340440c0a45000d41c105400508003036003448080720485080354803a00c609002c0c003902001c1d03030710b403294102c0e9034030445c60a21001c01007100d0403682e41c4544408a610440c181d0082c80c004d100f4040e289003007511980040ba11081f800d161504c80b003002503505400418248640805000e0035520111681800d410b80e40c413409020380020041000020308004a2100c9005607060740c0001c140030945d502c40031001b45d000d000d2a164540d400c0d280143c0041c00c0c81055000300121001a2524001240501400c015848081701e0150103034001d507043c00700003420301c1e00401081c0c10b201e100142247d126540b0b0400c0f600103800c42400f044140e80148165600550b05e40b0003401c0d940c594a80104004000030340f1218060030040c40008041807140c1a03586c00d204040c006480801d00d5501c65130340e040f141c0c0c040741c80e0407400e0300b98070f0506596016103024041e1080c00d49410904440c0303490320781103102000f050700032289800c0c180340c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 629511402 1250 629510152 629510191
    0x30405060313060e0307050d030f0204091d070501300912020f0c0d080a110f120403020a0905070c1502070b0108101409120f0403080703080f22060203 66
    0x2100d02031401102010210001c42259241a01c00c840b014180209681e0050180fa4000f6100144c007108034150740c9030204079141c0602000000c2e01071138000003881e030f090600e801100000b84007403242d201c804004403144595141c0065031483d19100240300751780d65000c4041c40c076004000704010129045007000410001980f00c1c0644110013801d140d00581010707042d140d4144040012120108044078148080b0a03982d40720306040c810405c81c68203025000c44111a200010b000082030701c074200094903a200c200d000480565442800101e12400303009101043e42c02880c410544540015120700706101ca254807406800700c907039075580055980810114000618403140b40d402044010f008004001c0100090000d90b06014000340e00d480d644030800903508000078a00050360084501942d490380402c10540040c4a05c3c1c0006c0c1214030001802410140d01c0510a403068209410b07d00c856111801d500100e14008403440c507200d02900500070104409034019038002c81a1540c40100110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 629512652 1250 629511402 629511409
    0x7050a2a0b0c030f07030b01050703030b0d0506012d060f08040c0f0e06030d0305070905011107150c02190803030417121810090503030f04032304090c022d030405 71
    0x854084038030700c40100a1204d03011040c00b030a600a02141014052260400300007412400fa031400601096241d415501d99034403583e03e0412243c0e000000c1d01c040d580c4908030501c1c6540c0d026000c009246603012103c80f820307100b0040030f05884950362041501c1c00301c2c60080f25000c80113802581c041d01c00c440001211505c0c42840402041c89032800c1c1c0d110b2034018205401d044d00406010140b60600040040340384c4e00c441d1590603201300342803a509100503603d0080c45e1802541007a40314111545500513640d800c0442110704a10807690381480e801e103460038052100e0301e449001142da00500105001400f512030800003504518040d40c00e21070401040c12940300180c459942240303415500b07800502040c00200a51401c0640902c40240369640701c9030385e40720007082c201c0101d580f40003140c105481041804041000302d000c0000d00e5440343c005400c1079105200742e80340185001c240d20f692a0000c58240c54011203040b0701e00114036201c9121020a00013000c0c0720a902041201107003540c1c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 629513902 1250 629512652 629512673
    0x1403270f030a0903061802030d030c02011104030c030c0803070c12030e04090605070e0a03020a032a03030509180f0a09020a091a04140402060a0c05120a051207050a2a 73
    0x814a81d00c2c80704403459405c119003102c103542420000c0c0d03c404009130016071800542d41c5030a250700d02e000500075030440d404074018820a10406043c00e800a800414050241c2d1001c3c143c90154a00041d00d50b51240a16581c0c07180c00b100030b280301c440d2802040207494150440180601904050900b8030320040081c5c11a200d4040888913035680713009000340940d2200c43ea051085040da008c402903810754000a80300c400603c00241540036803041c103d08102418009190048404900822aa16407401a1844c1c114050450285580e9401b500218034040c950b28000d600c6005081616142d010340d146c045e10303240350f00b6600001c0c2040d000544440d01c3c8940c00582505501c44d01c80a001d0104100c02d5a01ca1003985c0031b410038180c00d010159a4000c2110302d200071905107240f6654040c27030014240300402906003929140407480880c141c0d0040020500d034031a070040da0b1751035950300200fa00c150042520a000017803603c004050420351071003841e211814190b01d507408200c416554200d00303e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 629515152 1250 629513902 629513917
    0xb01060c031e020d0e010e0d0b13023303010e061201150909060e060411120f0d0f020d02011505011101180807050706020c011e0302090915011403270f03 67
    0x44c2d02900351002d80a45c090a59150700c1402d184c0101980304d4034000440783e21007400090030321207540c00441e94800b522995404c2c5c0c0750b4050448400d41040c070032000c2e00d0020010034510074000c81c5441890305c541620481e410b8406460104220380c413414180415080401072031383c215980c8400368418280d641d08008010403024002140a440c0d0303282030300a5031060354092400c1ea1015050200261070007203e10032090054444038500b1140d040c5c4e00707103442c043c00c41c140711a0207000043e00c100e940c4000c1c02c104020b116003c4035aa02070081d4128200d03006902481100381c0380c114280f00340e40c46035005241c202883c00003c00c0c0b40d00303001c03509a940801c16204855170100001d04d601044014084a0010322070707030028006d071100c03040004c0c2c980c0294a201c00420303050705120310201c0340245d0568200c1e80c0040c10300802c41c5021856502190107118500703010507807580801124100401c1200e02c00c0c0110f00320311001c4503241d038803456100080c3e44000414007400c03a4400c02000c0800190440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 629516402 1250 629515152 629515157
    0x14010b10080c0f090409230d091805090304090606200a0c090e030c0f0a2a030303021b061018020903150402010201110a050d050c09010e300109050106060c0b01060c031e 74
    0x220000640c40078a0002d08d410035805100d20941c0c10001911140b0200504455011010a199540348005800c520443d0400321019145c840d0100740f060340600c0c4183c032030341000445220184541c00d62507581c84113207402024100305072400c1c403c195280d08200020709007a000ca07824142c00c41111030400403c01b880548941c0840b600209208504140d9000c0a00701c0c000131564003e00c2078401c1100d80c83e800f000e0245900041d2901503a400524034143c22070700380b8103648007400e0426102a1813a9944100003d1900c41c003119000f20490303100f201c101d42c0d00203000380f00b0911028041028600005c10583c159540c41010300c00103134501c2d004251034080f40c0d840540d51098400620125030026002c0711403141c00380700f156800d0340c1040c0e106541700c200301c803114190041e0100c80383e60510115003000104100c1a103895101105400459074a41306200038040035860712000c42d80b40b010500098401c00d00071004000b030502814180c004203010b850b148000321041c010f40000d050090202c00c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 629517652 1250 629516402 629516453
    0x19080405060f100e0907030606150e0906030d08040203100203010303080a050124300b0111030901270518071b0c0b0f0714010b10080c0f090409 63
    0x400c103040c094076500c00b4001c0380c00c1d0401d00303040c8a807915411140c011009401c110b200480c2104d402040680021584031100740f1a03691200070b075940c4810166040004035802c131072800c03500d262030311001c0e02c0340c20042d0041500c0700701c5080c112802c41000e84260380602070008901c07111a45400118041c40c000c0c0c50300c00641c10030020f0301f421035005078803101c0008491149000c00c45d02c080c0070024038042510b4004641018250244c014882d40e4209040401407410362012800fa150400c1d00d42c55001d88400da600c241400c0b00640742d20901c280c150025250b030340c1280c81510325044407144142580840701c1c0198880000ca11500c5440c1c04d01040c01c49010b00b04003005038000051190106082252414000d0030b039240606402d490081107903013400415401d900c0000081502c0400740c0004040301a41d0099044e9070080040b8122903001d036001c000c2102649000300251801000c44405103882c0c0540064000c05c650003a03411154003540b5000034001064143d01d2800c00602d60510424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 629518902 1250 629517652 629517661
    0x1e0304030903170c0607110114010303110708031903383c030c0603010b180a080304060f0c061b0e0f0904060c0e091807060302090d171908 61
    0x201003481c0300c1c0607083d400070300700122000e0410100b684c0d90880400e05054100251002c2c0403400b41c910810b9480142e02206c00020500d0f62212a200c07001040c1360548000c1c0d62522819074692040320600c9200c43d080d41a8501914030950040d19021840350b031180c280003418030030408496510740c101e01c03400300c16100340c0300c80d01c4c3c003185005542001110000110080f6500200b13620003a08a910015064000b080890b071010702c201002c0c00802481c20b5920740e11120f00c00f00340c0d00100e9410303402101d0480841c8143c1070002000c01a214503000542c242442c0000031540b03503036160040d200b000b00c00310014001030101d01581820700b03114040d0022091011100030080746404241c45e1048510800301006500e814495603080358000c640420701a038903174000d40d5408150b0301e43e00c0e04400900200640d0300c3c078001c085400301e0202c0c4c0039101c4541d40e4000403400d07401200710341c650000101d221a40064422856042c01030301d03013090542040d0500e0407410060440d4036501001c03c01000810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 629520152 1250 629518902 629518913
    0xa0b0c0c0111040e0a0902130603061a03010903080f0a020d06060507020f01020c010507021e03030c16060f05040b1305061b060a05040804030201270909051e060c1e0304030903 77
    0x1a01c408240320006080504d03008550f4000503018151341d40ca960703509203000941d1100a580000301180b404140401a0f0340c0c903080d80140b81c551440c100310302c424040c60007645018014283c141d86c0641d20340703040380c948042c1086410800380842c03010310b6017081180041c0107240aa071005000d0f6840e80c03a1034200386e0061000e45114040e03201c0c1107401c02c0c0c0320405a682c03c2010f654810b43c055800304d82d11290380302d140340180d0030210503950520001c10481d061b25400104801c00c800340c0004003500664400c0d0540740115601001c4000c241c0c103100c00e02591040c60041d1150800300c0449814280c1e99802144c1268460b504400040c0c1c00702000394045501040584c3c3c01c011152000c001d94a0251240d545a004600009040225150000d18003141720394511004805110001050329525616800106040c2c4030882e541d01458000041c40d00740ca929020140b200d0074040e0140c0d030381e099041865075002d500009120965081007100c0040d0240103180f16a11175155080c00d00d0550404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 629521402 1250 629520152 629520161
    0x30203070620070e160306080a0b16140f03070c020a0b03011e2607091515110c090c0f0c010209010305011a0405010e040b0409120f050711120a0b0c0c01 67
    0x908682c0e82c0510b074100a40310210707903c00da000c5054401e80081200e2510100c002d0581c99110320014400d2030a004240002e002e5050f00909107005105410403a400c01640d0007054038a01c0803d8410900c44680351160010003945e100b1200c3c5031a00305a00e0f25400100d40200c942c02100c007101000c07005104402d4014038028144514030350f1411401e00e031500705186d440320b0413809903024000d2a440c4145032000c103c0322024010f00380080c00460306450070903c150f2f0f03079481075025088100d8440d0b15034901840803071103015071000c0074044000000b810311440f0ba6024000199440d000c101c041304114841c0b0107058041c800c0e00016a840384104001401d499041c0c000400c0d00240c0050b0b4802c501d240405c23076040b0b40c001e0a18290290034000010003c0008202264001d81089626001c1004815001810550644072000c01c44001a401c07210345c040c02000520703883c80720030458087d280c00c20300300c1c00030040001120080301d9a0369800038101d2040d1501c0d054010042032510605000713004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 629522652 1250 629521402 629521457
    0x5010605010e0a09020a0525060c050a051905040b0a020f0609060f0f06010c0f050a02040617100b040b100801060905010c03120903020a2001031109150f040302030706 73
    0x20032142e900c1c00ba9000502c1166a440303120b030a180d0004400704d00d03900403819548219444580450395100d01007205895840c0303440103c0300d4604d08541768a40d0b90080064070400003480d6281c6040442c0d007621400da005200d00c0c02c0c0d00f40301050100051001c02d100c010b04061410b41c0c00741441c61520f06460745070a102400758040e80e04204104641c403041c01c3e21450344540b41c4082041192502c86c010396600c0900c14014210402095002048c0700b00080c01c0c254080c030956040080c15a01c0c1002c0c1030441038503e16030303115000981d048904003d01c0d000392100820080c030024040007448005907134003204840340c0d00030401ca0401040100d0f0488840c4004040a00b09609a51002e0b40c00a00d43c540d00d04c0c003441510740c0d4042c440e0a140c0308102000c121580800c504a1080904039244043c041d050b1281d40021705103200080c44940c045d0603108060740c0940f072082c503042e001c3e10101280d007000e2819066010184400405603508000550041c001d5880705a14500ca010744808a0f1010a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 629523902 1250 629522652 629522657
    0xf0212011d06101202010c300f02060105060d0e10020706060509010b07020109092c030c0f01060302060405040b01121112060f0108041704090203010f090e0a050a2d0b040501060501 79
    0xc00c1004122076130340310025250760901c4c0040d48038a06180883d0f40035018603031440902c201c1c1d8510300d91380c15401000203807030a8680300d60010385036400c800c90b03590030b0901842c5d030071402c00d0019000200c9030b6048041c00c18949020340c2c0c00b4030070702480f00040740c10084045d2126500c40a081001c0d003481e440d018050711122810602d001c0090300041c05c00320a603c1666151a900c582e120b80c00b00ca1600d9468409a04030020b01d00b1840740b4031803d0340ca412100110079180030307405c0e141d404100148240d02c1113035405001c1d682442d240c03408101c020204074070035505000119141207040b902c184035804a00c0f85211940381ca905601c01207080c2c40b080100318078000d454054078180603a0700540c074241e206a1120503c054000f11894007140ca00851b03200584003030002c0000704851449030180d000790394035807004100c0c40310380c0c01210b0b50ba900701440c00343c0982c004d0a2154042824101d244102c584468285840e041c5221923010403c501c2d00b0040e500d25003400c0a00081040a000e8400146807d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 629525152 1250 629523902 629523931
    0x20d1e060e010f0e0403141903050606090d120e130504031715040902040b0d030806130504030504090903050f071208060a080705060d181401060f0e01030f0212011d06 73
    0x1883c1c61a84411a000f01e8a89074503010004042501c6981040d0040c01032181581d1500313801010901c510720602044008a030401c0c0c009140c5040807800e03594a450010000b214099840e1117000f403080c841140c030804c000904000b0051900c074001440f0104a0942c000545481c0c1401c0080101d00840c40f495150315a020900c06584481142c00840200c11680011802070520028008000302c0e24442e030410801d214103414560804181c901c101001c0d5882d812001320340c0d040344226803003100c00402058043c0014000107103250701141015119081207403030413003901158103054001241c01c441c2814100c00e00540c56600094164100009480d0588c4070782c20a44d40607121a2103001d82401220045041100e82400d600700059110ba59182c0d01700ca41441d0070846016a40084018061340c01d280c400510320484a81800c21624924022912642941c0c2c0340c0710f0080083c1e90903644002082511b01180c0800e11400c0507903802444029049c07a030303800c400c5082c24001001c2540c0396044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 629526402 1250 629525152 629525159
    0x171b0a050a062c060f03060a0f120b09060405060f0705041d0115030c02060109091e1118060d0803091005091014090a020d05241027050a020d1e060e01 66
    0x40e1826103040c0702d0050040780e22980c0347c41c049030308460305502000300c5d40092040050714482c1c030101c1108042c00303215105405d030380e4290301c5642d9113400d880003460750384601c0004003244050313400148c001c11f8600d412072070550385d0061100b0001d5502044c0c42154400001000b1b20492451110900042400d05104060000c3c10283d19607805115444070162112881c00c1001035452070002d51a4505d819030700d10348480d0804020140f144854a4081c801c81482062050300c0d02d801a485075200801101c910502c07070741c13205015040a06001050301c60030300740d4003800196004003032160703a82c00014030150420340f8641d000d4074440e1045120460200051000006c0040703404008240c058401c0480b603207031031070442d141c00a4240714065000001c80021200381e80140d0050199030031225500c00580c40e001114030004030300080c60344a508107a00c01c105145503400040e0b00405020b070060400200d0010304d0240ca008101c5812a0085071821b88000c8402e4840c1d00301422030910f0028082d0305 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 629527652 1250 629526402 629526409
    0x60c031a0a090f021612080c030f0a0908091c0312410702060f18100b03100e03030f07020f030a050c0109060603140601171b0a050a062c 60
    0x886000c2c8580468592034268101d580c250103c4010b081501d0900200a480d401e01d868030125880ca0500018180808520346030a01401d50b070240804141c2c070001502c4e220707103000090040e4541207484e40400c0c01518151b80e51400c000d0782094165001c0d41074040300c3d18004180c1c00600544142c81d030f00d04085000740111078120010400c540300442c2c074064105405800707205501d20455080f2402402c1005151580030035040d000e001e40c01d10311602920b48408440c40c0404082c98642c5950000d04019151882600708000684010f01901c84030741044054106a0b1409040265103500c00000d001c044603c080d6516031105141c4040c04052501458241d120300ca481c204104100c00840d071200c48442c00c1d03010560350ba1380300300100003250f45c80c940440ca442d20640180f01c0b40c0506000000c07890800d01e00b80a40000d02c5000d08181c6003005e030380c006510460b801883d04404018004640354858501040280440b512450f54040b543c0704150003160b81449210740c03c071604c08c100400e944 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 629528902 1250 629527652 629527669
    0x12010b0c030409150905090717120f090a0305010507020102041703031303080702240121080306010302180d03050702090a0902061e0c120903070b04180e0a06020304060c031a 76
    0x340035880124501300c40000390103460065070031480b025850079040c0030b5500400600c4500b2111841400454242d1070860103843d0150704030400440d120802c0309414080742c0a006110242004002c0c0308407d03100d4442c1d50848000300c9041c0003607940010f003440901120044051501201d0300214a0361910011100c400091a400103060005410100b14824020300c96241e0300651fa03800b0003c40c0c20074200d0603200369002e100d40150800c002c0942c0d080102100e82000c1301c180c001c10035610b144c850500460013580041c401009415801c2d840591594030344030300100550291b9906030f206c0c0d07610300400046000242044025900d07012140c0016114941070315040da02032050a0103044401d1380e1018144288011f1803200c7c0178170300c100c0401c80c000902170000c0d40410307030845112644480d88000e00703200700d002d00342c0c688190060b1501c4108041d006800c40c0c00d241403d5802400321640c0e00810790b0010b5804442c1d0540320556001246c2d454855440c03041303041c068002c120f0071010041381c0c841 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 629530152 1250 629528902 629528909
    0x50a2a0c050a0803040309060f03020a020d110c09090a0b0c04120602130e0907080106140105031603020408070b19051602040506040605220c02030418090f080f12010b0c0304 76
    0x509186850140942844640303880c9400541413503036440c1a160040c25200c084c0985404280c1e25503100c00351900c0791081c0c07200c00803150020b0014812514040c0d80d05103407000203090900c100c807d084520348030222080c1c001d8414200409003028035103004c001c0300000800744055450203010420081e000031080040c443d130000001640c0b078600c40c8100c1102840d0703801101140007444144034040e40000340540485207804000c10149031261223200d140c10900141d20300152040c00802c040606440c14112450501d042c0140740664401d42e09040009981c0125041035000c207081110303155010b58900041294036000780303440c50300c0c1005050041c031044068011580d036000280d180d141c1d039100300080d000040460f502110022504a045004988213000340c85c106209151064000020791b002c0d205018240c0d5000e11124962100030820002c0075944501e5849039040880e15800040040392030500241d07943d142c000d10901c9032014103a2214641c03034000c10411940144c080151401c0c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 629531402 1250 629530152 629530157
    0xa0509160e07030902060f0306330c0f010c0507050c030d050d0905150a02072a18141e090d050f1c02030906071704170c0f10050a2a 58
    0x76841d500d00440003040c0d0910001e4002e0400a01c1c200714801c5940554032440782100e0003148130042100c1000035120f042d1254800c90401c2c59130b4413040001c2c2003c3c14211244104a4501710a0101d61070700707550036141d8020110700001240703c1401418405500418019001400203040700344000706103204002411400079980d41d8004100003052090903014403042640480b1420b18000c120025481500115505032381c05e04d440c40c40f07100078106110300a80c0144069401c501c0c001c41129580b1000c885100220303035954445610030303180300e007003401400d01070040d1481d0641851208403500c1d001e06107400981c092002070351920341c400e044400c00c002c01c01419446007045090740140c40074100d07404031464004010084101c10014040c0d1103181140e6031515510b40ca200081c0e07802d48213950182099004c00d44200d001d0000e6401094045010710481d8400685040102e0070f100303035451038030342007500d500a105030000c1d103000e400c1d841441c0a80100301554070004031036550800409170b405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 629532652 1250 629531402 629531429
    0x1151704050d0c0f0525090908040e07020a05010e070e01080312070e010207050301050103150c0906080703270605011829150d020405030714010f1409030a0b0a050916 73
    0x20842900301c04c00030513500404a0701900717085080c40d44001c0180310283d00c45480c000d000118010940540010300d40c2000406182600700914000340c00b030000d10f039030258442e00302208005003007449018026007040c000360a50701c6c00c0044c01303190020180d2180307820340e100380584420610480c100a8000c1000e080c4102e0800000340144c1c10000254081503041d4a840e00000504c41511034400384107a44180800803081601c0342600e0300d441d94003504001505203400680701034040d91003800b40882c406007590080488885000040780b081d80107e600d5900c3d20010032407004002d0014107129040703103061050000610a5220301c0345003410040951030302ca01d041c811070301c4441c03040c40f083d203281c00810780e03d80d0b00301c4a0002030751042c41820b00a12415200040c4101045180d818500d01692400300800b030f4400b08135a803007081c4000500d142070400606015590401500400c144104854040d030b181100c52001101e500405c0c0a007aa00300290208002c00310a40d014162500c113200c40c503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 629533902 1250 629532652 629532677
    0x10302031005090606095b06120213080d031401053001020a0216060c020a090c0e210c090f0f1503070e010503160515070204110301151704050d 63
    0x5c240340684410720a07490b13150541c90170039540ca0381040782564160700c940b00e4100700c070240319947c40103440980558441900240b0600d803040f1030ba01c0c0001d951000241c14a81095100d005116840e4826070055000c07400e41500f107601400b4441c3e40311401e0084c00059232400340401c010145004001c040c418504200020b101c9841c0c00e00750300580480002c5403200310f025070181da034000c501e41c008d507402002c60001400a01c01d1010030002507000e00400c0c1d1481c40c01d031401c80a089415122002d0248a819612894561503104286500318000018403680d0341d119103070809110b003001d6401070889404101d9104144030449402c0340601d20a080031360b480b80158400c0f4a059041a641801031200c0080c12064480740316060701c0d8100d007070f107005e505a035908000030001c0d132246c2034100c00d1402c80d120b10030001c40090f240c0640003030004618446060705000f01c40c0d000360040708000311100c0030b501d010303035010401068020f0086030307050302c81c185074460995441c503005580c0e003000203961954 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 629535152 1250 629533902 629533921
    0x90c060f220b0703110c01020a06020901021504061a0612181f0f0c05070f0204020a0909090b0f0f090c2b0515071704020415150801030203100509060609 67
    0x24812070300045841c844140c8030407011110350b00c803000941c0050803020b6001c10220002c1000d8040c81c605800410f0005201d60701d01e80a034014018190640c041c44e680b06604002c41040c0da4400c070320580c800100e018003058a007480c00d41da00e007240d0040c00e0034041102c1c25401659a1504100b03505805400104a40000c51030030020784103405846d01940e8a241045d4166000141d00980c070b0381040c00042040348044a65009902e4090030000c0302c00400f4000d070825500902207442103140c04000d81c0d40703403400c0600b0398015810460b58030a0450421824444140103540c0004074160844100d050140c074565031000021481442a148180d002c0d52001030803101c4003641d00d403a480740e5565001c6082282d11050682c226090020000000a00e100e128110f40e900f0445c1c110782c17040340c9881e030b40c081c00001c0c501c81a035076810803403402c004909407800c040d5071400164141da508645605602c189800e000c41002440f5400d810320003409800c07480400c5251744218203840e0981d00b999000c094 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 629536402 1250 629535152 629535187
    0x52104080f07060f0c2d020f07080f01060914152b0c2c0901110712030b04020430020604140a0506120c0a170f01030308090c060f 57
    0x41441c8100040c80420081560440d28408040790f00c10001e400180f5000c0d038030700c0202e800301103028100a414682c04540c0c40000c00c2d451300c0c2841101c0f46411141c1d507081c6071285503046511503500040003031003551800d000380030150a4640701031094800600c801d41c0e41c081c0280c1104101006c42d1402002521030206030140101d5481d11000040131303118040b0303941c040451040c4d40b01c0c2c02000003c10320010a0880c5c0405001e400b07258007450b07070300b24540c05660ba03025121506c95505c9006a039566820030340500440e500400e95402c6120b125007014044910402c0403500680c018070041002140341e2141c0110303860b04522a0a9090a0811000000703030410002903010501050102e640700025800b070310406002e0345c51007201501e44040045500801d1001140c44c29554002904800402c018000c84410780c02c0090741c141801c100240c00800c212010f60652450b80010030500d580300d420190080c28044c080d00c2c2091084010882a210740340c1c0f081c0d4a003000090b080204180880d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 629537652 1250 629536402 629536417
    0x1703071410060609080f0a0305030c0901030902060a020f0d110706030203060103140a020408010c020f030301140d0c03060c0909091106131a071118010e0a020d1b030c05210408 77
    0x1002103d8440c0800341c44880103000d503280030302c0b44404020081c000007482c014016019107410341580c1c1c0b50400381c45a82c0c03003040700e2810191207401e4100180c490802418035420190090300200d101892807601d0041401c0303580080001c20340102641501c0440d542050300c085140140c1d41e582d80500584c09031003d9480c055901c03120340304106080002d54081c10a840315003000748680710302e01804a075500d0284c014a40036070001c20040140201c50f110010710300101030401004040c80d81c507405030544099000f035880d1911085c3c1241241d9029050300301030301c1500020800c40b00c0c0c3c1c1c1ca0b0300e118149100d07826030260900068042c03001c5d00c0317440b20000900e5a1062040752000707840d038008854124510444000c400b8404100756440d081c0140ca0782240400704c13400d0560303c1c105801d0b28040740546a45a0107508010500e08115035018541d0411a600300b440b80d80e101c040e40c024100d5041a0101040190901805c0d440c00602d00d000003010650488507043c913110350a00354000c0c1b04550 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 629538902 1250 629537652 629537683
    0x708040314071407050a0609170f0d08041208010303171909050708011401150309110a030506040507080601180504021903030c11030102040509040201030f1d0a0c17030714 75
    0x307080c0c0b04003c5020b0515901045540603107112030740d40c0d424002110300c2806440003040d000c200074041c9004100042c002060200110340c100d082c5140c40d2400c241c83c0c040c10000090851007080103100c200000300e40b40c10064074002020790314588000703041c480c40b4450040c043c50380d5004a004110783c14501c8000c081100d8041003000000e2404980d1950710f845010055420041c2d03002e01c0c503900c0d030300030b6040301c504560a03001d901d410314080b0020054558115061a000d0b03414940030f480d00403021011b18800e900421b824180b6003440c925217031481c0c1c0110a260700c0040140010345081c903103007400c198855408580c903240d92001070708000504084000304d405281d000030500d503015208003499070140c0c22001c13000484805140c2070340700d40d02030140c0088150300801c0055100b5405041482c02c40c03c000181d0032030301c45031080c0c1880088400c6200742c2c890b0b60980705000b104000c583c0244291005502007e0640001645900a00304041c050741a00d680700484101c041c48154417402007030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 629540152 1250 629538902 629538907
    0xc0310030b01120c150509010c0312090b010e15030c120a0233090307030b04030c14060601140306100c0f0c1203090e090709050a0b0618030f0a03080708040314 70
    0x1814018180c2d14000030039510b400c4c0c4003400041308034490741c03402c400c60301c165903091418006100640390541c650400b1800c00c4008550304c455074410703110701e044071340c803800202e0015403400003101860314010b0004040a03465291002c801c2e03400007007402e81c4007000e0714498541c10781c990641e8100502504065040000c00c401540e0441041c402c80001d520300d1940510300c22025101c07030f061409001e00c100e400d903000313a10510205d4916030095a0251092406e100002c0303190390365035503060341044402000d910600601400d580c100d410300200104030124a801c602d00000001e007000c3e1101403003400d01241c0c40c9040c047c840d6a0001ca19101d0f0056001600e140e82c0740b90394000d02102c113100b0f03000a51003400101d030040108480e2070041420f5001807602d42e080c2003049006043c09060345524590300c0c21003078401e4403064054120503e81600001090224000381403c0592848011050342c105500100000f81c000c9071f0070f03070001140c0c584982140d4a80c40e080d41c0c0e2005840c803c0704039a80c003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 629541402 1250 629540152 629540159
    0xa081609030b060a0914071413030605100b070f02101403010e0c07050304030b060307050402040b0a031d070f1a07030504060f03390201051302060d060e0f04060b030a08030c0310030b01 81
    0x25080447c020880d9a40d4015044407194810303115006008090740c44400402c020404599a900616080780440c0c50711104d056030ba0049101d144d11002c011103105102100540541c5030110240134112070904100304034001954508040d0301c0140501104803c0c580c0106015401c2641520320782940f180c100d07503032140c0340e003050780307030108221401c07842846030210201e81400c081c001d9600300c804000e8524280b80b24001c0503005420700c0008940c00c0007003140c02c26081e5108021540041001c00d81310002142003200240e81b91441d00d440c603036102020822000001c0c5e20504542c00c0351618506079046204080c0700b180a8004114120482d42c101c0e0305544503880e00344c0000c044000820901c2062000081c020303400e86030119051040000c0d0000c0c0e00c005414000c0048c0001c3c0d0f1041d80000717042d0345803a280c401701c5005580d004090115031040004101c0c3c144150f480760a822801840700503010380e6030210382c0c0320091031b250300460b0210206840c41d20400c0c42c0c0c00035584c0720201180d80d684 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 629542652 1250 629541402 629541431
    0x717030a0c0602040b0739150c05031b010f060308091009051003060e0702060907060e15040603020a1202030118022503020606010909060803040302040509071502030a081609030b060a09 81
    0x401d00800d07d4040c030100c0200141205001c5640403040040240d121403625200002414220341d1501000348400540400b00081050004100042e8082c0104940c140060300c50340c04c66403000031401c0e445140c040148040f48401050b60019403040b40c2c410198210b82c603084034003500560040d600a803c117034000c200c4da41c2540140007540c030b41701c014050a0750f51101c101c3c1da44100381c0b888a45504204410311800c2d101c1e402e48500d40310050f00c0380c0c004400345091401e850307002e98400b0300040d5000c80c0e00058254003c4113503410940f440b00540c1036505001d03003103c4104542403009501e0b54001000700c50034440c0341801c68805440442c92001c4681810301030f441d0303401181e185000a00dc01c0b40403174140c0b250b205417030542e07009030001c40c109400c40d800e0100906002c0c108140c50310440000150690903c1c841042040080c5d024584071170704040b01414030314007d0240d171602c41044880c0b0243d203910015501c205c0e900240c1c0e00c11292a0b030303008915500180d402c21272000741060000d008080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 629543902 1250 629542652 629542673
    0x1e010c0813140f090c0d0b061b0d0f020d0c1103010f0519020a08061005130b07030f0806031b04020d0c050c060f0f0403030506040b0607140717030a0c0602040b07 71
    0x58070a440800042c042c9010481402a0b020742d82d50700c0901c100101da50400c492010b0900421403d20002d003140b078020000b200c0c1c0d006070041101c2d00307140702c00f2907035070803411301c015031100070356082c040ca02444200b0301a4440050382e90300310812051281c5c0b5418441d11440d80314500c41c01400800c510500c68100701c01400e1b0072035504007100000d08034500c0b4085940308991448050b562071040d280c540c6000c2201440c000d43c5142c0c100001405003c2200320410502401015003c000c44c1d40d60030b1910b4013400010460003070105000e41c0604128513510040f0b0903199000301c1005140d01c103c500000203000340070f01020f1226542c900202c110680b80c10038010001070081c0c10480c1c902d07aa80c00d90f400a0b140d030403940c0d074400881a03c040340000b4003d810903138108500401c0402c00d4038002d03010400c0e6420169055502110144030207810081c140304503005846140d40c50401b0382d00c10451259240b1420361000c0070080c1d200302c10300a00c5000c0e0b06442c06001e5405049035204c500e42000c18048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 629545152 1250 629543902 629543909
    0x1050910030c020d090510080c07020910062d230a0504050a080c15070c09230a0b0f1e04091202060c1312050c030109050607020705010203091e010c0813 67
    0x144103056003007030301034001c400030381c1112001008405000d51441c1d04442040300a089d10a0000e001d001d443c00595480c1c0c4120b00c507180034400e502c405450000f0040024941c180040b104401440300c1c0300e01c1460f040740d042001803150602980d03101c0540325403100d05584422561652a02151104045910200801c1111421105980480d4a035255541c40d01c45c51075030f50750f104405050141d01c040810010349030782e0380140c83c04510140d80311005000e88200c0002d200f040242c2040d440034020b048401142c010680220410078903c07260301040100c00050041449405205003842070b50b1608031078498107810290003440a010755251243d22508682c0303c090150150300000b44241007000261003c070b203401d075212400e00d0301e00350f00917546e00d00041c42aa03035801054100d918944003401590462446080105035518201c4002410407460b50803460443d0070400c0f02481d10b41d14000e40c21000001c03090036004c84484800103079410f810008004040d020007107144900710394401d1090049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 629546402 1250 629545152 629545157
    0x100810170c0a091b030e0d030902060c0d0801030b010e0f07030b0402041a091005030c04030305071104050403170105060403050a020616140303071d06070605060307050d0b0a0b010c2001050910030c 86
    0xf2044490304c245c05441040c520b100d229440403103080389040c42900040e8440340081d19051507d071402c0e905a091003102e40b11280401c2d911401001007007424000e4a004001d02034610074641031080c0c0c14048900082e11041c10940c0728410813034541c1d00d0384e046130003e100341324949480b02c00c90a00d1300c1c1507411051544c0e105000100c0145085801881242c1c13080314040300140c03504d815030340c080d10b0340e03044140300f07031601480149849815290361249034000d6001c2e45070446c5040c03c00d4900340111b88142c0140340150313000d00080000610001d0500046681100d4580d1940070307900c1c925003c490380c0280540b245000386080b03210558040010341c05040380c0e0780c031030030302c04010000c2c85c0b441d01078078860a4201030300700000b80100d038490380f01da074200340b0007802d0b0303260540c0e100c000030414625854155400c1c010036042c083c1900b9240b281a04045080c200b003a01c0c4640d40e1504c1c110340c4055a0741c0e240d116400c0d207003500c02c0c0e840b503022035400160007003a039000c01c8500c40d0020010500030000d90007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 629547652 1250 629546402 629546441
    0x1061202120c3f011a0105040b120408070b010b1c0506090c031807081e010c0e060f040e07030608211803070305010905010b100810170c0a09 62
    0x141080c021a02036850301c0b000c0c10352688000302d0307503050b541e1900c11481d40c001042e04001a2284030000b44000e0794841c081c40001ca01148130390301c0b025417030440008031418040108020040496048280c2c1d400079a440681d030f505036180d08207911180303d4920014504c02d03802c0700220341c5d00d54100103010300301995042c050325040b0300d045220444d8816903034030758071115410014030901d800c0d400855021986030104016941e04017901d80c07501800781c11120003074000100c80070700410302d07100f004041254100213105818141c0c802606449110607054002c50001641c521aa030000040b00c00405900200201c0740c60b00d44002002064140900205030055203003c6001030462101c4818401641542601d40b0320444420044001407100e8540c15004030000003001c90001e10603805036078025000810a40724a10401c2910714038002a401030060880034011912110400002501c0350300001c0f014503c01401640d1500f402c801c072960b80101c052602040200407904400d8007650701001905 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 629548902 1250 629547652 629547679
    0x4080d020a0b1f170309030714030d0513210b04060207060e03090108071218060504031112091917100c0e0f040518030a080105010801090c0c110f0301061202 69
    0x6507066003200c0c06000d040c1c40440a04c100315500d07007200400c80845080303a1824030741038046402c002c40c0b0303405004001501a0000308a040a200741d05a001c41c501c2c01c2c6184c18081001c9090741035081c018a000444a041c000b2030f0703c1586030410342c003590001440340231444d1600d040b030040c0d41300d00400c41e0800d00f0a500c035183d41900006990b1480c070141c480e29015034900c0c0084414181208040700010b1315149010300b010f50850103026640d0040001185030301c1c1c2410060701d559150361040c1c003164001c0c1c506003034070803212003502c0c1124400c03104a01d544407880f007492000c01c11b136045440d6000303c401c180c048004c8000b80f4400c3c0e44029800c2803002520542c2c041d520b581c101158560400040d151100552401c0c0e8045a48040741a955800f00d4203400545480c60b0400001000030581c02c0b80140712545e0040242801010411403e1040c41c0b081d00300104101d072810380040c51b22030324002d00c11081d500e284440101c1480600200032041c1e844c0d1040100d40d45d090410380c0a51420208013 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 629550152 1250 629548902 629548921
    0x9010c08010b09012d020109020a1d010b03090c06031e160c02040207020a030b1003031d0d0b0a110d020918100e07020a050d1106100608011a04080d020a0b 68
    0x103040324200c4031107504200c80d50b80191107000206071050070300d42c0e26010b02645c65141401e401c0c50202e0300e500000c0c1c00441c40c81403002e200351542001e00740f4611712821454030f4043c1e4070020306490840192580303e03102d50150710721b4401e021401a43c401c50100c200144d1822480c2e60f0b185101c51911107a1f001e0303c4490038a01152054000b01c0f00041002c0700d92409801c240d00203050305031025004070300c1141e03681c55207909103c0a80ba0f100a43c0614003081082c19801030b00c0041404c0d1190071103a10055000008600182c030380c0005000f10b0138080028851601980181003540c0040409940c580c0c0c001c008100940c08255071034800c00c04603072591480d40040f1501803241c01090079091300e10341846c1030040c5141000b40742004501c5584101c0000941c01e000c00000c2280700d4403201100f0300c0218086084c0000200311602d055041d0340c0800c007007544003003c541140c1243c0d000015039482da03850360480388126044190721b885504110340d4a241e0020302801d013940943c1880000b5124100c01c4c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 629551402 1250 629550152 629550167
    0x9040312140103210f02121803060103032001020c1f090b0a0e070905041109091009110a0503010207321209190b0a03021b011b0e0d03081b0c030d020309010c 69
    0x10000143d000104040039108084000d11618241c0380c0d10b00c0101d2307080d400003450440c00b60021000661550540402c010032525545001480480258104032800c0721706030741d41d6002c682800c0c51a228800c0c040c4c10580700c0d44003090745900301540003035515000180c44058440d511150300300c2d1180300400541c03c00940b0075a0700440d400501141c1416940c1c040003044000a00a911341d8083c1d20190104802d880c41201c09541c81258900d01949200e0200b00c0546920b5000500a0740100010000210a00c585122500c84440701421848014650f114141d01d000e4684020b48214440300340c446250307202030200c824003103455a03c110800042d031281c40c800742c4906c0345804424170088002d14001c0d0041c000000c004d18000c103c0000c0240048d0940f4042080c1c0301150400049c9142450b502400520440c5c0c410b44900460001986d8018a041401480380304104a91291100301c140001c040321460311003078044070384402c44c5242c1000254000d0340c0d030010365886d00031003003070b4240182d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 629552652 1250 629551402 629551427
    0x150507030e0723090a06080f0106060906050f0306120f0f01021e0c030d1e0c0f1419050f0705010507270e0105120a05010c020a060b0f0904031214010321 67
    0x1082c40b20442c0c0d828132043c010007030002d50f41c0549072200461607000801442c0c06c0840d203a80045603662401b0b501408a03003903900b01804016040084041c200e1b00141202e411480a444948040070900c4030581090582c00c0704442c140900c8080c81e0302c2c01815005841544854240c2000904a040909100f44030302c40305451160002d00240100340d000781c0c008206149400c54450004c100c01040108441c002807914001c15450711441d80143c1c2d1100042c4250718007410603034501038800310b40e4030b02c192000c40381104021002410501d44101c4034151800740e5480402440301e424640000344c8020200280c8821129010b00d5000d2107007041001d41084903400780300076003130ba4201030621400c00c000074039801d110300c66040b0250004034244a0f104070080e1590203000106054070b4958103030342826070b80d18443e1181e141c509007036903690821190050b43c54200541c4402c0c500d04024040c0c000c20120741006010302000106002c04079030840c40041400d5804400061030781d40c250740020342c008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 629553902 1250 629552652 629552699
    0xf030a091403010c1b060e0a0b37150f0b0c0d0203120109090318030c09060603090c0506070c09090f141c05030615042c041e150507030e07 61
    0x124081c19441840310901c2103024140102c0c4008080180c1f80c9002d1420404a6000e28075000704541e091541c1c1200d420404050000001c2061000c00c0c2148160401035048505544650703080f66040c03440540030090402c0105a50806d03030311541150250410003040c40640103400050540030f1020085030354410207442c05039216401c1c030f040c850040600440c100c091194110ac01c2406da941c0402203c0110f1160500302d420b10f08048804054400da54003090605081040c01000101142c0340701042d502d02351111500c8089a080030451541d00d903000c2000780d4a405021400d1251418104140300d0240300358110181c401a02156a080b15211480503035000d00108030400b48610021034000b0740003041e50b21010002c01008002c0d40c495401488009040b403440c03114402c00074100003514406005607110342c9026250300a42544c41403c0389041d001617014882000101c1c202012906500c2e502004240307410100600200801c2c0802074552050110000f1202c0b108519020340c140c009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 629555152 1250 629553902 629553917
    0x301060e011a0f07060e010f06120f081813020a03110f1215040c1808010c02030f0a020118030c021905030a0f05101407031103060d030c03020f030a091403010c 70
    0x1161100e00c039000010228250841082010040b17825401448a030a004000024045030b010030070508a48890340000c107040c24030031011021400400181c40740380e401c50021a519520341c2012000140180302d0705912003009040003441000035409400a092561810800e030841003200310f04a019241c03152001000405c4003120f250303000064290000303000e2606400004416000505543d03100c9040d01c0051081c04409442c3c0c2c9e0140b102c0780003004c4a8000304540412020000d459104000d4010b040c09000220510194030035030000340c020240550740c0000d42940d01e4001c00d600710298060b8030400c84070781d404164481415030070781224402001050202c003a640c401e40003c0d0500030035030380b41c001c010070103400710414000c404001e16580b58610b0180381000d13000d000c032803910303035081c049110a0081000c11b8a07a0400030940e02c7c0c040c2055031908180c1c0c50101e10f04a11011404080d01001c00c4950072150001e0000080d078001d1103d0101c0100c13510103040c22110007440100020344031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 629556402 1250 629555152 629555189
    0xc071a0415050a031e0e0c0f0a0509070c052a01020d0e190f030302030c121e36030f030c0a03210603110f010309030c03110c030601030503090301060e01 67
    0x55802844582c80304d007000b1076200081c03803080442181180c1203080c401c1d1212400000b8220070b0000c019024412140c4043e980c41c2c200c0450096041e500038240101d00e100c0124814a0187d030010a0b460340c04001c841c0c0041600c02d22100b9a0080c00700114081c80420141245600114400e60311407040c0c2d4038204d60701c1c54101000320028031248400c9076003a081c3e5021600382054960000514066001941e5036100004c09030302d4030070b13070300e51495160401740942d859044400602e88416a50400e2958071488e041903161098224055501e45404109003c1c5c3e40440850420140040088040d900d640341c803245442e81301d02c80d9000c0b401541c6c00100e181e000103400f650907203031040c2d4440502100404c0071049142112043d40040c6c0c0c090408078480c814614000228011003102841c00f0701c8800f0099038060803803481c901005040c88101d24440c122030408100c043c210044c002c0c121000d07541d40341041500c0794080d04695000b54280030010421900a40c9410b04030707032000c504203c03030104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 629557652 1250 629556402 629556407
    0xa08180607051b160e060d080304021003110c01050115032003070c0b0411040b18160e100c0c08010510030303091104050109051006140a120605060c071a0415 69
    0x4088041d62146080c8140031044003c02c100e40c020358050007544015180c240020411281c100810b0345108400300301c40d02c00020f580700c00b035903040381d81a0b8040c50152042103042d0081d013480705500d028150082400454542d0541006040310007604851600b0b08107007004409646e1401022030854002c0502d50302c0142c42140110790208003881c00340c91040065403142c407000741c151016245554890b1600500340360071711402021080c11a540300243c0915003d003030076014010180c418084481d903039804054000c8007904002d0a0092001205030003800001d8180a03103104251800c001010300419280014440e650182c00c038401c0142806117942e0301280500041c20080350710040032911981d19032258042c640c040c100c11000030606292000c45c04400b6101c0390f204000300100c0405400844000030110307203850000d40f80162140d280d0011500240c1800da20264100d00b0000e8102c44011000c16424151541003048920050b1481c404030b5040c01307580a002000880021500011030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 629558902 1250 629557652 629557657
    0x110a0c02030703120203180a03120507020a0b04081e07082d0d080601030c09050a09090c0315230405070504020a030e01050c0a02010c080f27010e030a0818060705 71
    0x51005040b103a10b1500e9954203000f51111100c450007592002c51800e040c030701c0d0392903081c8003240e05490900b4080d1039501c441010031800d42403030f41400b0002492100350340300e001072540907100b1811503643d51340d82d55544a58034000e0301c0403501038070885a0044401c0101107074107030445464400914070201c40c80801c000c001c03032416840071482c0307800d80512a207013810b00c410541c004054940b456980381100c00507050f1b030b84403134070036041180c0100103000f103954104142c1e081e100003c0d000100700105181800660807107404c090f0480700b0740f00102d9480801a0030100c410304203e000421003002c028060540c42800380c40c01013481d08000c00500050405074081d0032006e01700c0c540483c0d544000210b0b10308541341940c5602c91034100184114110b502401000001d03695403030714115030b02d0300420010581c20058094810a072907100c0c0c40801c0100f8401c0d00c6031505885008205c4980458401c0307542c1e40c484a803050128a1100018036410242200914094035440140c9600e0fa507525045480c0d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 629560152 1250 629558902 629558927
    0x150c011a10110f0d02011a010503072102090904050105100f1508040206220305010c02030c06011202031609090b060f13051b0f031b040503070b090307030b0c180301110a 74
    0x501c42d0076003100d031074041084040b513101c81a400004907035a4501c41d440040001c1904541800020401c2c42140383c3d200020000201070021001001a5811403003c06445501c02c0e1542c0480d008080c407042c0903040d48040d0245042012a000c19075555103030030f050140a00c00d642200030610052004c15002d25a40e581c0304e13100a115912346444039807644185420036060407240d03242e41c0340910401400340f05000911480e03000550501c1d042001c4195190301c14040c03c41c484000701000011510704001d98800440c01203040140340341c031200c05100525800d001903480b0214035021074041c3c10030250010198002810004600c1d00c8151118084c3c038015040b03a640c81a83c1e0816032035020722002402071441408901d44c0c0c3c17401c008c0e82c150510388d10342d03442d41040d20081004003e40d9800040e404229200250303616112005000001d040c540700d0ba00282c03115660404129214100000400820495000085c05e81c2d442c1c40600d030803103081c0e80301040107110400c02548014056280107030b00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 629561402 1250 629560152 629560187
    0x330506040903050715021605240907030807060f052a0307091202031c02100e06090303061009080319020f06070918110a0306060801120201050406050a0e150c011a10 72
    0x10001e181402003503001c829003044e01d480e04031100c00c200440441c0c0c00c27080e2030890580d0215203804c0c0000000c2d1546c2c02d81c4401420640001449001c014407a004100310030980720040086180c0f10110b060810400c030a18803800c400110448424020302054a001c1e0750140d46136440c0608208941c0c44040b0074500aa1749882a030701c00b0454003400c0300d00240255005d03400b504401e01200e00c6034059814250000446e5003042081000302c1e100002075942c01081100c2c036903d08900890113071660b02c102d4000303101c0c50000060342c15410076103981c0e0079484140d55080b906103809503a00540c43c4d4809950701400181c819000300164401050340500500d110640010001103250804e50a6813104c1c00000100391941d03810000c1a401101c020300410070460001640d40c0a90f000901031b100318010b010502c1408a641d800d0307144a455144d11a81016054040d4004417402d608031729000040701002640c2407404c2c50101e080b020a214a4240c0060940d41c0074030714410007507500c080e5018840c0803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 629562652 1250 629561402 629561407
    0x1206040e06070302090f0d20130603030e10030b10122309011503050c010c030c0203031216020d02100906090819020709020306010f03050433050604090305071502 71
    0x1003680d010310034103029080382d0720010b90b5032004100703204d10b00d481184214071480d182189040440c2180741150800c80b280394603040111405400582c80314098010021080d02e000404410181c0080c01c0c0751100300300301c50f40b0060700040501203095030511681c071600a03e2504400110a002d003d8014070325129030000700d04540d51480020303100d090003010900b003008070024489148428483c00d40f282101020500c0c8990464942c07554585c3d107103144c0c2d81040300365500315060520440c3c00c00c15040e401000d8981e1251001e0b1505420030040d0350800c071010307400c0d41514805000103103a01d42c03c64140c019000d86124604408018012180c0070703200c050701d07201c4100001c1c8210300100300f60402c8050424000030040c8000340307440907035040005000e10420a0100e01d03038000d40c4038142041c0514000c030b000e60f5035280855101d80825a1079031088035400e406581c8884581600c900e00030140400c000543d2001c00300020b8400200010b80071400c20044100401c0c028080304c0c4581689103405407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 629563902 1250 629562652 629562671
    0xb0f090910240906080d11010b0607030c0c050a12060e0c10090303080907060e040507020c15071a0c04030b09160f150804080a1d090103060504021014120604 69
    0x95401242585240205481082d100c10182c240724101811004000b00708039070400c06200d81c0c40036503503a01000d0202141110101d08000d40088400c1e40c80540b545403141c04034078014004040d2558212000348450401090600701508100221912030607079071382032095a15541d00804807110285070500464880c86501c4d1a119501d107a240070a94130042300a140d400c00420f08280a04904081d4004520820569030310400c504080f603070448001809469009082c3d03e45010f180615401c151030510307024003814070310060094140100a0b040c00c1c030002038140f55408100b11802c800c1202c040c0014404900006440359000c1505012240d2079515030107000030013002c5078080040b502c0103a0080c0040584150b080700881d140f03061402503400e065035400341d81d01405030f5001c104045852201e03010f4110203040f44043da0051b10030001942c503420114080c0404640c160302500e0380302c030058409841104440b084c1d808000a1908000d07491050303045821000d8002944a526248503a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 629565152 1250 629563902 629563933
    0x105070e210114010518061302091305191406060304030302090a08150a0f0c0c021309020d0b0711030304050312060a0504050a0c03060501030e030f0a03020c07060305190b0f0909 78
    0x1650490201044103c01d50700d000c01300711200364128511210a42e0013400d0113410303203896410707240f000f1800202503107d02c42800422090344c040036100720f1035030401c0140014028a0156280341300a140740600c0444154211281d0402041c0d072119003100c4104000340100b44a903004e0405000001d02d1920881e036215202850324020180301901c200800d024442d00d842c161180b0403219401038800d104240e001213018040c900c00000c007038010014601540081543d40e88220005580244505c000c46450b0610b940c16003c00c0700d00c0d9010803a6644030b0198800e000003900d200fa6030000045151502d0310600400814014141325001829840042425651405114405c80d24024000344000e44501d000301a1007560380414189480d001c040741c8000d6021040b95600c009250140d5903880c40c00400710004d104480e483c00c428080d07480d0200d100c2b94160400d83c000c20195002410001d80700503440101c901e070000c00380d440104201548500d09080450f42c0e8000c01141c00c0d00c07078401c0d030700454 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 629566402 1250 629565152 629565161
    0x307140f0901080d08070c02060d051b0a1709070f0b070f0b070309060b061e09032509060e0609040308090f07060c03020f0109031407170f0a110105070e2101 69
    0x7011280c000c2c01d6035140841c1c3c17162060b0f83c020014a00342c441d24400c0d070003160041c841e8500c00409103840d00005141d0074221940a000420440c549a5849044010041a0850b001c008000d0500618081040d1480001703410040c0e82c001c0e880d001c00d052800508240c20340c0450011524a0800d100d440017242c003032030030709208040540340404e01400030314040088800000c40d09120741028032040105074010300d2102540010b00c51041e5980070700c840000e2030202203102c299600001d407120a5581a400104202160000041403000540398241d45410000480d01c850f004080240080d02080c1300b480c0880c0c02c80c04440c00c1e1005c20911298003030920f403250b00700b1808200c1075a181801c26070b04008a0300c2122027039000700b01c05a00ca650040103128180184186030b00082000e00510000740710080284141941c815541c07a1507101c140c005401103100440400c4050041d01c0d002c1c1c00c180915442040556070340e210f08862403040116102c801310b0b4980026680c0d440c40061050248107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 629567652 1250 629566402 629566409
    0x70b0a0209061b0a02190302090603010c1b020414010303170708010311060d02160507061d030a030c170408071404090201120216060207060506040b03240c070b101e050307140f0901 79
    0xd06c51b8118118018489142c0001d07102074060380c9000188600d19a00c0382c5014806000078050115502c420700003c0c014001400310044901e0803940000200758001403001907210103090070a42e995600401501c24001c24400501a881d4140d9a03440724035101000f0f0030b007010700d07250040c1007510211305d10800d2a402c8074104d4460f4004001480465000840d00f0507401d1284004040a480c2c0700100f134860300c0e2110000c0901030080c0c1c80004002014000989a40c680f61510b038035039036140300b010341c0c0b4078040c8500c9110074079004070003166081a0064405454040e161240d2035200f1100c150000c0d4801100480401000100000051a02d00052981c18000c14000c501810084104005c940000001a03c02c0c0d00c0004070a07a0743c848408803800300c0740204004181a600c14500101510455000501d41040c010800c100741d00181c41c3c260546850039540540c15070504100b8a03c80030354040c07242c0c585d101903010030200300584007030480181d01a0284000c4002c0c81c0c04141d6840007a00b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 629568902 1250 629567652 629567689
    0x8130905040609051009031b061b05030406060b0c060411040e0111030103020a06180909030c06020d050403020f030c0c0906130507021f150308030907030512070b0a0209061b0a02 78
    0x1c201e8410700804204c610301141404001b0400840250340207000d80c801030000d6900301c7d02002d441024091103a000d500310380e0300d41c12448c907138101540d8024000d500842c1c04507415450003001084104041054608407507544005203034540765030302d0f50b452201d00000c03519032058507202444807443e42070142800540140d520756460354154810481c010b132403a00004208101903c17007010140084a022003100c581c00c1c1c001902401a080c100d0b456121407401800c034500021b80b004044e08182d220502c1203000350300740d44e1002040c48000c0e80301d101c1e01807070290a6001c0c400c2190a40b826180c125048003009102d9172042011107007141c191401125100f0142c0c01000f40c81e50b000903028041d0301922000301c3c00700030700e0b0381113840005140c11390b01003d82103c1c0013000145140d07a040103130401a40d00101100c0100b91000802c40035a400800b044236266035410100b12034001d503009a5424a030014001420210320700241d44210700000e0718011540301d002c0c107400168940b03044a002601201 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 629570152 1250 629568902 629568911
    0x20f0d0e0705120a1703071b11090f0114040b01021b0102070e07020607081b0301030b0604020c010e030306041104120f020a031502130b030907140d020301020d2a080103081309050406 80
    0x601781044100b844904038101c40004000304140590722241c0b407a4984d038402003400d480c6043e428240c42c90071260074444e4220040f04180800300c00b000104904890300c5c07280702d84a000c10402840b054035003810042c2d000d6405096040305c40e00e80b11010040e180c43c188100e50b041c5a49845100c0400340c00d5a500c400758010000780041994007440c443e42c0305da01810480b40c50300107198280700c07600c01440080c00110342007004c40c003259250b0701150300c00c101c50340081c13001c0107031704401c4c03604c1750f00548020780f040d80740040f80305d00c400c800800c0c0c038101c40e5081c40801c00007529440744103001001444c200c0c1e11641010000c0002402d0801140c0d10341c11410340141c807410b80300a110701000c0f460304840d5080a0038010004c6c5914000740040c01e4403c03100c0788155041f80380d00440d20b60721468000a61550010600790949880d681c402c1c04401a44400101d8600c416481e59000265442c41030340058551070051020410308401082204940f02d130545c816581c40425200300c910036501281c015884 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 629571402 1250 629570152 629570173
    0x7050708030a1d2b09120c090c03090c050f060903100902030d030911040f0b1201020d0b060c071a070210170a060605090111010908040e040b0a020f0d0e070512 70
    0x80320081098440c800300500100899003079030807403603d03501c004280040c0b2900034030300e189220b500b02000a051031007003402c11b0842450191507a00347ca00851040c149040424146680309004640d400d9410050b1030b0b4080b4200001c3c04141c503080c210707a6400c1a03040050021640b02040a00741b100c84403a00040c1e6440349104240c01d11090001ca8410181031114100c0403542c2207024603100401103074001032280e000d42c1e00d03102074001108011350040407818103a2940308190028401c4000c0030034204280c80b040401c010090007058408140b550154006101002e1903800001c0c5c4220b502c60b4280c2855944c1c0d000460050811303015500144c040320b0b85000385010100c040b50003ca1340d650520089003410030080142c0a4600b24604011200b0824400d02000b9802000140d412610607584c46446001101661005440c21074008443d14009a80711425200361110312184000319490305400c1180346001d8120030f0100e49444c00780020015665981a105d05089030b1500040c160103c072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 629572652 1250 629571402 629571431
    0x6040e040506090111160f060608030a021e2107020618011e02060714040f090507090b040f0b0f09040501060216050901030b270d03090b06030a02090a0507050708030a 73
    0x10040c0103121160304100100e160740500c5c0090300c514100c50310403840303d48528248400d281030386000143c010351030003030701003000c03c004001007104990030f07021034980c640800091501c6c101c0a182c000c0c061380150401d407040091000701c1e202c240c15950038081c1003202c1070f000941164400e95003440a801c50300440d040c9942c2240541145810109a0041c6616a5000039488200040890042140d0340c20080003110030320050b01c0c007a00817501c0d204040b0740c490240c0070050805548003800b10751070f11000110a05240c08032010f585561240449032840c1c004000e1854111420344000580f0502210003075880d54440c07a4003d00b0240d0007012441e80f444040401c0c041366030403050003007040700014004108105141c50700564004207540b00d40000680304510300148500b880c196004050041030610340c27640084540c94040c42aa201c0380c4c0301c4400f0036642d030041c450002c3d0042c0c520000660035100700c1c0d00943d0b000c802c034180306103020752569031801c0f1503104a50001d02070f9501e0b0800c0d0348450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 629573902 1250 629572652 629572663
    0x3120a05072007061202271c12080c0403080414060417160f0e061011150f0a0b030d0e24040f060306081e070e0a0e100c0e0d020f06040e0405 62
    0x104010841c030302002c0d10780d448904408509600d8080541f2100d0760f0f50b50f00c8105404c240400c1d5040da03082c00311f1551500c0782e11135800441c078000003a00400441c1812414000f100c1c1166032100c0300d149001d18141c2801030030300000d00c41980c000c401b071000007220f0200000c0b403040c9045880181000d00460001070350203006940040001f990110700902100404100c06034210f101211080c3e00096010000c640d03c0740e1219002c0d40710700501100050210000d0034007070080e8940a0012116030311681d051046134200080107506a002c072070044007842c09290100b01d4000040c006608028206100f8400c440b00040344201d1500c0000302004003164220342e290140410f480c061042c3d03407500c804170740d4035411501640103240340c940124460b032900b041b200006000c5800f00d09424608a480b100c020080003020010720b015000b00c0034042d218a205440b440c0840f9250101c0403140d14040c005580340301c142c1240c0200203901396400643e141c1d0003800060889040c4c0100514080c034045003000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 629575152 1250 629573902 629573927
    0x1b07030503181b011d0a120303230f0703110a020c2e11030d0c120c030905030406051b0106030606170a020d0b0429011703120a0507200706 61
    0x150002401c000f001490642441a000001d180482004401c4880540030700c00b02180b1680c00800d1050000e003503107404280c108064000e4038100103030862444c00d8010310719400e013800d0041700d18200103142c40c145501c1868011800707107000682c0c000c020420480c03540c400c1e0004d6000d6801802c1f0700e0072500e0008003041d40700d940e42800d0740135520005d500300309209000c40c209042c020140304480742d03200100203070b5095045810301800008123403840134200d20b040c5c0d070183d02858140032003400203e0081c000d50100c4c561220045150601d01941100c05812551002c1c4c886d44150307884a040704424040c0e00041d6014240010308580b40c40ca180144500b460b01101842c2c21000d50000075a541c0e07003400300c1544e00240c01d8456a40c0c0d500d008200f000f200060321000004550310101328440d01092981070f02c0360800140c0070b10503c101141d50740d008021340301400d000f0301000a5095040c940081350001c4031410594400586452040c050443c210b01380354441d071141804000041c0d0055141554 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 629576402 1250 629575152 629575201
    0x61d03070804121a0c030f01080d020606090604090501060308030915071e030608190b01050604050306060f0a0b160c06050313170f041206050c03070f03051b07030503 73
    0x20810580d840201602482c8202101c003003408180501340042051380e602e8144113900300340d41d039140ca4040003a4030b400580c0d80a044600c0d040010030041c00019022070b15604580080109554907010420540402881740b0382044d120201c1100040f400d0041c00c0155100d680c14039240c0c5000c0910034a8009040174040b448103006080c0b1605580150300c6c600407440344003040045103140407084d0050855580002d60f60300c20303600c82e504108080101d00321268860789581c1c0269907070300d04010700b5020303d01800364950840004213010b031414040c5c40c1c40c51080500a0075842d075031180d4442140e0800c1802a052041c00c4000340d08201c0340e002850003804079030505c41e007541000c0c0c0f401d96004032500c000424070310944030a441000400e0702540c0305040050045542c650315040d2200b62908641c4045546505050104030600259010789100388034541e01d9803407a40c2003503011006088054464640c3c3d0381000702c1c0c4a0020003040050882074003e03254540d6900b841e0380b452018070303c0455900394 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 629577652 1250 629576402 629576407
    0x4260f0301030b13020901120204151401120533040606020f061f030204230106030c090918080313080708031e0103240e030703030b030d0302030402030c0103020f09030a061d03 77
    0x40e52200c2d0701da03040d51207035421482c0230340d91480450010000b280e00a110030390f104900080b5103e804070000750315402031760707019810310b003100414065440c2901c8884410759000846031161140c6001c1102c040c01541c0080312850b02100031400302c0c0e20a811403c0182c001c540d103003003050420402c05400200704900050801801002c029007030311640002440f07652a0101c04d0002ca4550303190031010910010f51061559403583c3c040c000300060049000031030669200081c90804a1044482c1010740c01c01c4403032450342617910349425601c014611202100e0700040c0318082054800a4481c1d184116203180e924101075034000d040a52461107004100e048400610008403481c030320300341c00000d1034042d1010010500c240009848268001d041c9880049001c006142c0d140d0401031403508260f050300c0c50100d40f4035084059100c102e4019403d0307030141d01c10003c3c5500c80d500414603461119038941c01c0144c218006401c0104150044d02d18580b07a41c9c45402090b034907a2000c00160340c0500844c0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 629578902 1250 629577652 629577691
    0x6041a0606090d0503072111060c030411030313060504030204111603051b0f0d030b0312070206180603180c330c070303020f1b0904260f0301030b 64
    0xc1d4103104000d6101c0c090f42c8154525010800e04006031030801d640a0381101c010a01081035410703105403840382c000041d0840300011100040820003c2c00b80000380003503851580c441e01d400e1143c0c1100c010880d05032104001c0109000d0f605480403028011669a81e9500d92542c0100016100c0048001003211010081c1c00ca0140c1c4480e400d503901581420b22540702e0100e8002c5c68400c100060300440c40f400341d200e003283c004001003011007100f05991010008800e03541e040c560b55140000e0380d10180c00c0c0400854001d494618040e1450750004500d402040a226000c115142c2050f510319005440d181e01e90700c0000010300490b01c0c244015500100c01c4e1040d41c4080c51040c20003440c0c0e00d58440c04014039039060000d0b004441a4440a604403011159207140080d501c0080340c032845101d0041c0084409036005882800d0821030005241c040315460715142c040900750301144402011100d0b0304e802c1e440e040c020380a042080701e0002d2090322907146080c103070140c040042c0522510b180343c02c43c1c00b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 629580152 1250 629578902 629578909
    0x8010b0a1401030f0b03150a05010608160503150604150e19140d020319050f240a0902040c020703170c0613030e0603040606180603080405060f120906041a06 69
    0x741c0940400d1802041122090442000800c2e40c0d54220303415025000d140c20040210f5003001d4003034441d80801300f10607071b40d40b00103c850580913500394810b0303004200e8140d01148110003650b00300c98072128030844900f85200280e01a407060b0b01c105000c01d100010503080580041400c82c8030f500584c4d00c400e0b80c580b1185200d40310503d45c0550207a445500c00c1c2c1407400c0d10b802154511150340a8200c50021180010003800040d02c008125114414500e02d624800700102d40c840c0c40c903803402c08031864441191041111948001c00d20f0030045e580b0146080541e8a50081e20680c030540c2e0050210141503091140d040c400d01c080c030150541080241c01c420120015600381e01500b8100681100c0405d49421aa143d01450076603911060100500051154561054085618003210203403085d10001c0b40c2020ba079040c0c800640029400d00c0104042e040c101c0080c00c13403090107a4a10f281041d2030b081d40f1148807059a0109099105008010410080380000e050004c180d003d10002c0e841c0c4103000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 629581402 1250 629580152 629580179
    0x160c0c121118220311010f02090909010b0d030c060902150406020709050c07060506130608100e0a0309141c08040e091b06250f050613050616140f030108010b0a 70
    0x3c1d443d03125a00c0714a4040c5845804d07200c16484c10701d0020b101307401998641601030740019142500c100303445404a40031010500c00d10422581c003810a150b03800203514140c81d40301510343c05603030752903c4924000060f580c44944a4005d01c02034181d549544c103148009141c40425040100700d1890941441211b00300c6a080c0c42c007060744200c0200341c030354420012880182440c132210101a003050404610070702c0c0494041442c41200c14200005090f00740b17000d030ba5460030280903000c0342c0c40341d500b07001e001e804010440800c42c016004404402032a40d403103185091100080c1c07017103000031800f403145040c1000c403550001205c02c0100052540c0c20f01c441e0b00301c00c4441d469403041d0380c0050308a5141d4184200c5a502000d9107480031049940c41c18901c0c1c1481034160111501c0c0916400900ea040c0ca6070341e9026a56007100082c021a650340c0071b00800e00398032030030080511a10b22a0f03400b40420080c001c0440581241c2e80f95103070b51421700d465080d103002180c210702c12030700d000050000b120102507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 629582652 1250 629581402 629581441
    0x70801090608190501140106020304150c2012030a0207080613170c07051c030324180b090108070303121406240a09030c050603160c0c121118 62
    0x7007820100e03045181c01c17801010f00c0189403d680b08840000201d558011018108848070720125440d841401c00007210219104000100101c1c3c0c2688100c0319060940c51120029102400c68420000b015044d0345c40c680181d9000001a44101d8040c4002d04091000c01d40001a41c058840340d0f980c29500c000f103600301d91550403800e800104c1d070310701c18a01c2000300303030024030010380070007049840b03020395444400100b0b10550201e82041c1045002140700018042071300b001620602d0410b0601800c0102050401d10050a580d251098400d04d9615580f64500074050310340140300087c17031860050052044004903401c11440c0c03050341c5000074410f000080d407101c0200d901032030108580844000030303840201c0305a0300000111b9217084081d0400c06400a42e0700441c40e40039003a90340c50400c540f501c804ca030012501000600007401c044d0140303100b91002403141e0f96411a55894400c0700701c0c00b020008042c1c51040010309001500d0500d64500d11024000500030802480c0042c0c003655000c12205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 629583902 1250 629582652 629582683
    0xc020d030905090408121b0d020f07150e070803180108281a0f030307060914030309010506041d0c060a0507140706030605010c03020606130b060d05070801090608 71
    0x28840082600c01c00148015100c000c11004460401d4205a00070f07810071925440c0d600c40a00c045184d00c1d408108404120740c61107091890300404400c841c010b504044e0407081e1404061210800041c603429980040510083c800941044000d4002e0300c0e15089030721892164204018508641602090350600c0c0f010a0074280c100ea00c51100802c034110100c50300b042021001c04c1030320b07152551500040d901d42890084404003c812800b005660103c0e0b040e10380c4c2c541d001b000582c00044143c0c01140ac150301642941000c450110826411030307004440c0b07501d041e507544040108915252090100181c0c5403922450f0f840500c5021a6641c1c0c800341d01c0380c2c0705d0800443e410410910590480d0021030f07116101031586810031500c55503d5515018000109090010105d81c65104d03203402c0c10b03010f4041c1d0080400d41c40300000d22910b9034980010880490b110a5000308a445d410014032402c080043c00250a181015000304045010b03002a09414201001000f1079103000840c10190342120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 629585152 1250 629583902 629583919
    0xa050603042609030a0f120504081b0607120c0204050123150906180f010503041e030c060509030d0e0601051003150302090405060a150b03070e04060807171c0c02 71
    0x1a0b00300b0340300b4001c0c104055810703c103444840741009011503d11012500c40c500705076141107070700b006540324010b0313006010060707101c022010341442c0c10b8050300c260210f024041c1494000da60b00c488040204441400c400302c1e40001e071540c02c504003489154010a1984054034040703603500480324070340010448140c4034a07500403c0c80b0b6a20009002c5550990000380020354400c00b03040c000b02c4580d20700f2129445400c8481312029694003074070071240308540c00400e040404172903c190406407440004181c041003840c0082d01d000a94030b128450080a84000850f00d584180c4032036025183c0d544095000c5800c0b034001040951204800307641e00141a0034082000c400307610140c5030031035084d031003e03500c510918140000e0150201d03100c1d000c0d00003000c0c01d001c401c10985030520340c0c0c0140e11880082d0542000010451489441d041840940081021a1803a1380d81c038824034000f0603400004011200c0c1440e4a0001802c100c0e02800700c01301940500e0b01501d40f040549401d40302207010340035410700c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 629586402 1250 629585152 629585213
    0x50d12030c170a0605090a0c05032202090c0d0b010207030b0105011202070501090602040312230705011b090501090504050f0c0f0f03090d0909052a0c070902090a05060304 75
    0x5900740c04000e0050ba04903407182c5402c04860020300744e40c3c40f4090144480034045004040c00380110034501d403164452502d1519411442d154003140f00214800d59440000c108005035a800c1c0b005002c2c40c1e04d04541d5031540d04a181100403078003030000050541d4807522040000802501d8903d04640f02428960320b032040c80d4a03104041d00c05e08a000f0b184d5440c003e905810007250b40e016109980c05007100349141440080140c68440c40c84c0066511010703000800d2107607011321001050618401c1c0c0012400d45141e040d403803400709801041c0070220b0001c83d800c0c4a6540c4c0180d415000b0a0201c40c20301042c18841e070400c452001c0500321202480002032002070300d4400208441d0440c1d0307191200f959900d40f03002d40580740c010f540303580341c00101507a07000600038060b809040c3c003940c5003105064242540400381c140510315a080341168050501c8441d503010002d00c00f41c0001c0c00310410140ea2020782004011064907a500171912810b418024480850002c02d0021120000041450108a80c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 629587652 1250 629586402 629586407
    0x30403030f0c03021519150e100e010302040c200a15060303120f14040524010803030601120b0406121406090a060b0a090c0c05010e071a160209090303010f050d12030c 73
    0x1c401e8521b010301d8141a114030b1301141503411b06088918403618402c04d41c03074542e40443c62a90510944408507000c0c40140050310f0594007414210600e0301b00800c4025580c0d4182038400304000c1c0e0052181c1042842c941070291064400342100f20840040040604645e80a00440e50000b20240d51035030704d00384140c0007100e9070f110350142c05000e0300c03080b0340cae28083c0b50142e96040c40c220f20343c090701886c40c0c1ca070900d200d000d400f060688003084040c0d1305542e21403004481159181170019011522010300210305e403610321811001d8100c684440b00d094925040c99901600050308440306540117501300440d010340401c60542c040c0d8080d8010454401250004800091f69045000440e10b8680004100c0c1d0300720012080407880340c00240f1107100488045906d66095219200e112080001c4500e5241c00d80700081100d5041c014049011100d1500810000c0d2405c541083e881c2e8070010042c0b244100c40b8013008010b00044031202c42d01070040e5030305030a214902c0d15071310a05455120a00c003150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 629588902 1250 629587652 629587681
    0x60f0a0c08040302030610170a0213090c0504150501030e0d091514030a0c1b110607050709021b0613152c0318030304030206070b0c070b0405030403030f0c030215 71
    0x6030010110703200c0e410301c605e010031f103140c5503c113526100303c0802200c0d1603000049103458510350020441e1448452800c00d04024107480d201c201c0364030300787c3c404c04a100e40c1d03544102d070042c0d001c0800c0c200450b41408005011541104c01e003107180d51008110f114200d52082c501c0054400e08070f48101d0005500e00c00303869070841590000e140b41c1000c010044250b0301c661240002410b031781c1d95070a0b601a0501100b01400098402400106958101c000b003418404010100a841581110030b02d03951030850408070303003080a05181e0740229455440ca0341c58108200c81c0c0000c881000c1c10050003c50361150b40300c102c03550442c41d00d1911030000c445102c00800c030303401040c104211880e014140400207a500ca901554403501d1112680454217007500380082070320141c81c0c0c0901031900c0d00156480f500b05c040380090030790210560070003491001401c80000c440c01644640011038595046141c050034401d0325016100400c48010101004258006060740700081203814100c4180c9a6074844035184 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 629590152 1250 629588902 629588909
    0x10620060906040b01150f030b0a03080310140604081f061d010312050c071e080a030e0306070e0607060b01090b0a0207080c010306060207060311131202010806060f0a0c0804 76
    0x140541001c0100c840e00c08102148228070030b152201040ea01c500503040c032101480c000c0c9002952101c101014140243c1c056842c00100509407a80184d913a9a05a00c40d4401c403a500c2400c0c101407000c1107a101400300389007084d0000c560761402d003420704240c80e6465002c00360f1102d611006551054401940c0d0b40040050000451903103154050800c00c1c2043c050300303100859205000c2d41c1140c040620950580301c0e0440441d000e8070059141152034003ca00d600030300700d020071080c1500001c10036010880c040396a8443e440e004035001c074000c20103040c0400102100306110051014403480d60f140e200722054281d01513400a15160325000480e54a20107402030404c4c813500041e0060420f4000498504903221034044800028840d0011810384085225030409030384080010300c0803178083d400c41034202d00700181c1941401103c0342e410b10120413551010f02c20081030222101956030001d69641e2080082e5240d5250110342ca01c01642d91050220b68001c11811200c45030811989808442c000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 629591402 1250 629590152 629590217
    0x30c170705010c0807020c0a18140702070305070801050609040b040501110301061107120b0606030405120d0b0112140c07060608060f060a120f0809010e0a030b0601020c010908060106 80
    0x31040903141a070b00800300040114080384801c800103034014030021700c110318110301610f280034a502d0047d6084641400002c407052031501e90302107524031040800a07500c110201e6004080d520316504010382000d220703801c42031069060004100c0552541e078005500300c1c0c0e110905101c0d40e5100d00301680100380007800290b407445d001000182d00c1c4c1e40600070501100007501920381e042e50315a0f03a160f500314012001010030124000261480c0b814501965202d400b50050300e58400c07450744841d000764404a2940d41107561141c4c0324115517401603408c00010420750080000f41036201c1000a10340c8010b2564519010028a2004000d034940080700101560070454846080041c41c941c98030004445480c02200c0d40000080c2201b00030240bc20a40c1e0131031100c00d003041c540d44a1f0207443d0b0003254010305203d10754150000984a0001d400019070280d0014140d5080c00f40009003003061140b00c150400400310828070003108049801411900d441c10401e8442044070a03000b1081448070f041c105 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 629592652 1250 629591402 629591407
    0xc19030e0a0b240d030302030c07050d1e021906110c24060109321003090b0108031806072409110105030c030402010e06361507030c17 59
    0x70410408081d03401a03082d0001c0c0d85070300e20240f410400c4140c0303079000e05902500010624001c20b010364000c5401c00c1107038212525101281c5c5603540ba010728481c441000811150700352015000c11074582a07070300d10354406400030301402c10304607150f205445c9001e0110344d540d02954075500e0340c04084555482040c0181c0303968601e1290a5400d40c201400140c81008442c40001c61961050380300c502580d0200102513296540341e640340303809004041a94442844860309010203507540d1401c42003112203954045007910440c81c003074140301810b83c4050302c941e01c00d000c074032102c265049100c41e00901c1651540d80b0381a95003041c502030000403a540ca42c244100d820503060510f160000c01406005407500c988280100d00110b890f44400c881840158000b400494015807255003401c0d03c00400404643c14400310b44081c400c2c901c0104400c440c000e1041802d9529103000c201030200b41181110b46c100c01d08400010900b0303900c20b140004080150052000f001c0110003d26916140032414000340c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 629593902 1250 629592652 629592673
    0x1b0604081006051f120905100504110f0f01020a0b0a0f090c030b0709031502090103060305010e070e0c0403120f030219030506030606150f0c030927010b030c19030e 72
    0x800500701c40c003c9500640ca850350300c2d5801d02a200c0700f092143c400c0d6442920200f12080b10f480100398040d800c841e14007403140d20103031400701030241a004078080e05c0013404001c40c007010448100c2e0141003031400346d0429070f200900340e0380100300050b80b01c2d0410448006039460b0080c13100180307451a8020002454503940d0001d10080d0304a01d01076070f20403c1d00b5800e0b610f03481402d4500d48450b200040c403004e2a010100402c0c8582d4000d020b5800c0c041c1404902c4544076a01d590079500b161062411981c820042040649900000d0a400100700140d0500c0c01e41103807100d100412005e0196010321564100c480c8104c0c2c4a641210304012500786241054014900002c001d0401a40e07214032030b101ea0804104140b401a00240800d06585985441c0c02489159036000782c0103110080e5490200340654036007a22139841c0d05541c0c041000300701d40258a05121540400c80680001c90044003d208001c0c48026071412a404416030000e0742450310101c00781200030703140788039003d2014000c010180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 629595152 1250 629593902 629593933
    0x14030406110f030904090f0b0c03100909020f010e030a080427151406090406030f050106060f0c02040b0d050109030e03011a15030a0923010b0109030201021b060408 72
    0x810603a80c00766202092207101410255a400441d003003000c40341c00030820070546182079030080390403a01c1180701c450204c10a880303511004204803221002c40b03000000700f052050441703000002420444c00c003000b14082c95004520307415144090f1505200700160030300c48d5580d04120a000685d80048240d9540d07403100b810814040c00305846200c83ca1008842da000b044440c0030b400e20494850f410003001510f8485140100c1550007445030f0031180c00c1200c10a035499501580b0301650191281e4528044d071450800d084410304da0024081000c020700c104641c43c0d001c0382c10143c66404031408a000c00c0214001030005e90f402c40000c100c0d42c41e140b5031038105500828a140c2c0700808a008101d0280001e05202282d21110b4039145d000c1944001125000c5484c4041e6401407020a4009100180c6980c1c4681300050f003001c5110803d136200c00c54591000c24065500f80c02c40c20f00e88901d0b51440d590020350b4910036060b41050321410f40c100002c0e16144c9500340c40003008244201c4400c84d205c90713105e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 629596402 1250 629595152 629595157
    0xc050646030e0706110d180f080703050d0507150b0f0d030804030e0102060106300c0503010e060a0f0302040905101a090a02182418191503181403 64
    0x2a20b00e14015000c00048180c05000c44074030552220020b4454955006412a05e8081310302526511254909012401d40954105c040180020714018207405083d410203d00d013118444541c81049820001c200c000303140b010404400e00ba0003100881d0303000081c4005041860744910309604810009004c0f814940e120308981d010b20700a4490704805180c41c0c004a0303c46400f40201707000301e62541a1030b400800e0000000b946210302d1000f240a00c29442045403d4400581c0c0c0742c80080c0c000310062241400d1041c040ea00400129000034000d0701c5d01e040400141e2140c030010380300741e070fa480401082c000240441464101580310410490160784070000b900c0700c00b010500c1c0100051800034400c52028070071940c2d01c010000c0c43c0c6500500000801c1f40369591410070302c03120400c1c8070b204200c201400001e401072011401200c2150b115140a0000039140196400304008002c00300301b050f400c1816079004c034980140b8000c00c0130162851010704888100000610355183c1e010400d0700050007002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 629597652 1250 629596402 629596421
    0x21216120e060a0c1e2114041e1202130203150d0c150c020d0618150b040e01022805070c080a03020111130620030c06040c05064603 58
    0x4010310421091888050740215417000b015520051030340000b4002824030000c84e10020f240c191911022269019030360303041540105548003c0c251801c0c40f0f0100100204007801c0b14400e907105440c0640c002074014007d4020302107810383d000000c01c058150016032100c00d0300c00a408800c00145a01d0140b45061061145d45007c19184142d12446d911400c0d08801890700100000c8540045485a00040032001440103201038a0044c000000d10114a030103c9448554400a030401e058428003054034400036104150740d00c100704685020420051100607618261283d150b2481072140c144e8061107500c001820500001e800010406400202c080c1b0040c800d9009000c1c02c00b034013003046210300408005544513014200d080c06803030f100d080040d00d1555103442d03541c1c2d0840720040c2c042c2158031001003850182c01c00c00420090045802451004090070b031440c0d0b19111107480500460311a90407100c0344011034a41c00c0b040809403c207080c0925145100c03481000d01d0407030019004004014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 629598902 1250 629597652 629597663
    0x703050705030106031a07270503011121060f1c050d090b120702150106080403020606010801080d05090402120c040306150303080621120901021216120e060a0c 70
    0x4030042014101809624110795211220b003041320f07180000707190428030060001c0100709000c03c03c0010140d2601480c11130303060041c0400718860401d0141402d450303001030104081b1404100401c4010013109008103482c00b2400d01c400380e52500b00006101590320083c01c0e60000f2441c2214208103d074104100d0014890380840340f4119030824152004c0c01548181c1ca6800c20038460244040c1d518000d259012141c0e1069a0074140312802e104080303502a0400c20000d07018000300001c05804204241d0060340c2401c1020701c542c5065174481e40e4402d0510b210081040200309856182c445405982040d8011035522010345020310700c0120716080b62000755191800d00c01300d04034052040b609802580e4240d518203800e81c0d1303084180202c2c0b00124010311400c00340c5603a60040080d06100d400f21070b5010480c002d40c0d594081c40021300c2e00c048620780506080c030401c40190b02403169040020001d41c8540d00e10b40d00380d00c00406545c542c42c0000c10a400280014904021f0b99000001b1503040c1d1107107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 629600152 1250 629598902 629598913
    0xa0e12030a06321203040905011401081e220f0501140a020705060a050408070210110f071202010c050f0105011203030c05030403090303031a030f0d02010b090f061003020912070305 79
    0x1001a088816900742c4000d808030354420404055003130686180b12025104002c0b07038036055842a8050032036200342c1c06126050f401c2d0722400c00c15a444450590000c442c000510000780c59032004003118040904404100e03189107900001e03165800c0c698030181d98102d040c509000e4443e04040c0c1c00390100c101300c0c18105001c0d40c0010855600c40c82602c001c15080001409165160100c4038014500030b00103503a0000144074000060362660340100958a5954481000c00303004030100d4540204030310181e50319013001006001081c1d002113159400e82c0c0929001010700c0150500604181024481c4140c550a20002042c52945000000080d500c42d550420034018400d000300d40d1404241d800400241204501b0030100307109400c42c207108a4801c4035101c1044003000005c0c5030081c01c9603129000c3d000b90240b000d8040d021701ca0b100a981c030903500c0807030901c0d020300030440c92000240360911031a0394041140405201e0340c1507a60400340a4032540c160b03000150001d41e40c8015110840380f03031168 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 629601402 1250 629600152 629600189
    0xd080c0c0a080f032203050f0c0a0b0405033004030f020109120b070807301d120c010f05151318081e04060c051908030a0e12030a06 58
    0xc03031480c814003c602a50603d020000030f4043d5001403081a010501c1801d07020010070806d03c88940c07246401402440004111814080c146a4560000d038204074248410800303a103012030011a03040700c17500354214010308040310500c0c140100e0880c018030b400108010080042440d05100007500076202e41c5a542e0352010790700d0113950b6000780100926011000300300e00901800350560026503505250460110380c10b030166a91b5444207034003024540c020300c642c408401c144250741c60280c214103035a1503075007a0101c01d60b075000400104903040704009034401c1071880a52261000340c120000500032814405254401c2501c0d541c0094456001000024020f40c614440d0034403101c04c5034442041983c5645801d400d80d084860b181c5441d12441540103c100c4054005001800860315502e9203000582800c13494165403000d41f8000d1800d00a505010503021710589a0043d007041010402c0c1c422102c0035401c0c4524a102190301c50004028481003140540201c0b0a481c41190303400c0c40d0024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 629602652 1250 629601402 629601419
    0xf1103010306113604020f091513050910050a030b0f07021b15040e070c0519051b063a0b150a021c02030706051303090b090d080c0c0a 59
    0x34040c503c0307550305480303011312154852030410b9116030410400000b1114140c10200307090303031b014003074200d100c10001400800e00e18240340c5641d200701501c0451824800c034011075103c291a1030050910500c40e4000003035401040c0380038280a1720024001e14aa25601c1c81d088003682000d0b90681590007180000a4003103200164140b410021450040040c007204420300800140e141c402842c444070812000c50b042c5001800c041c0600141d40c0c07a460300b81d0650900d035007445050b080c0d900424803007a4000700032500009110900c00c025070740110040e00d600b00003410900c190b403a5850440c5408040c0520490480701e681d007918403802e040f002403800c0e024208200c3d40c0f288929036111480c84c01c1c0d10030003154203000d0140c0c19200d004807021040c914003010000006031006c480180e100051034400c0005034003c884c0c00002d40c1c11001131700300d85a640030303055128074003c054800c07102050351892503403450f002003000c43e040300400d641c6032420820517403101018524903000300d2180c0c100086500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 629603902 1250 629602652 629602657
    0x4050f0114010c08030907060e0909030a0806060403051c030f0c0503040b0703020c0f1c050306030a02010c050c060406183003031104080105240d0609060f110301030611 74
    0x110444181a5a0380c200500340780e400201c40642410001c00c04030040000381010f0003140940c5900009081c5203140a0004001021011020707001e01d842a051041186c1c0001c2a50b06400c003504000c00c0c2580e0301d00c0400e038a4002d03940064814803408600c2d107056802400000181c2500f90342c140b040031840600c01d800d903864032140c440040c90810000e0040b5442a030741c00d4012041e0b1038003605c0c001c00c002501c0d00d42000307100d201806420030060300c00f51407001c07880c84035881c92904103141180b4107000002e458420100c00a814400441a10000c000c01400300c3c0c4030154000b4502a191911180d00510082101c0c01c041450110301c140458040560400041c1200c00204042550322404029000082d40501c0450505441e00030048100b280300000e04090820701000095602d08400c101002e80300340f00900e50b24480381c02115007252941204402c4103034000c1404079962165140603001012650504568545407840d08030903002c203400154100d03801600144800705000380c0380c04807071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 629605152 1250 629603902 629603911
    0x60509030c01030515031203011d040b01060e150f07030e0306010b03060d060e0703062309070915090501080f0610050603150103091506050a060c02060d0e07031401021201050405 78
    0x41c0d0180c125044a50b110b908081e038408210b2002d8a45143c0405c04a45444190701100103c40004030040c40740490111704244030700203002600302c0d14201515103d01d542c0d41802004200719000b450207106845201e140b0b00115034010b2625030b03a83c0407403060b00998004003412000140618451101464002001e80c1038695110585145464540c1001004040f0b080c040702c16580307c10b03c00071240418030075a40254083d0380c0c01314412501c40d01107822005207029807155143d008007400700120300015420f082e240c0401e40011442d100c107007010b16004850380a044928109400805c1c40f06021074241170804000d411030307045440d03000082d50140a03900803941c00038400c0c030010f01351420a0315041080c0b207043c10001085501921a50340404a41d0300f4003c803141c0340c040800007800c0c404000c000601c81880c008101561641c00280e1510078910252036a64131548041074214081c401c4000640e44041e415044c000f981c09142e0113500321019001000000b1000051031742824024503215 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 629606402 1250 629605152 629605159
    0x1505071a0420121b01020f030c07030b090a0c0509060f040615090f0b07030318050a0b01031101020102090306040609061409061b1c0c1206080a0b01060f17061f03020c0601060509 78
    0x703641203030303480304c404c140c403042e050341184601914144105c006100510010a04030068507869007541400540c1c554050145405507020740100070103e0070118102d401c1d160300b01c803c4206600d400b000200c00180c40155140d0203071400b0030001e4036030081c1d076513803840f00442d40361802d507650b03100d11444104190744120040d8030b804000070300000380300c0d50001038411006c200d040090615034a03024902b00c1240340c21141d0035880c100500500140d050440c3c1c85003004d20003580303418580004242c42c0c120180c8010501d40d190040e4208000303958000700001941d2010055281c580324489032307900c000541d0aa41a00b1501c683c1c2c40300c9081180444880c2c080c40c11068504000800700d40d0000d103200554a020004625202d0380c105141d400381d400241f03c3c080003480000c034107090601c40004180e12680070300081c00e40b00071040303801c148940b07000103036414010700030342c5c0c1c5102050f12580e900304070040480714002c0003d0815015809058070302c0a132001c8130496a00d8070810384a0380b090f420002c0c2e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 629607652 1250 629606402 629606413
    0x2090a060305250e0112230307060b03011409030a0e010207140108040614070306090b06091521180105181b01051309020703080703061505071a042012 66
    0xc803010300601104015104154841e20f49507118440344015400ba0440001d0000f002d40440074003041004c600010000c0c200c501010300310540c120b03541e9208000c40101030940b6100d10002a507001c4d8000720000b2001d9140c0c20703a81c03601c0b0342ca140e2690322080090b80801c0c0d81800d02c11041d44001000350648401411596102d1f045030010344041030010411610252100c003e92101941d4610140c0a000d0310b0724041025400c280c0c2090989140d011000c0c00744c6010701040016507107048541ca4481c00d0040d00030303564061440217621061484205100e40070542c014828070000f0701e0b414070803614440000700f01f103858466020081000803e040e0034540e00010701195070340c44044405d041c1d0703074050600c0d616209000508942894a03940281c1c5202c1c0c0c00b142d8803041c036400c1080c2e82d51090a500c1c080016900f0700c2d00120000e48110020000c026021070403404000141422881c4100c40c1d03d4100b40c2e61030030349400c118101e43d010b13040c480102402c0300d501283c205035480d0411100300c00003030720 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 629608902 1250 629607652 629607673
    0x30f090a1a190606050d060e0f04020d170a0e09070e0904080924070605070810090519180201020c03011103010e0916080c030c0109060e0d14031602090a060305 70
    0x44454090900e8a90102c414992903548100d807203180b004010703685445446480008900301141c030710781e001c01400c44030071041140a003d40c1000550140e070484080141c10310a05058821030b03d010940c085a241c00244401c0184d000588040c0c00501100d40f21103da0b2084012949a619140034540204171500840d00040c0c542018207203041001c0d00b4109000302c07407820001e0010601c44c0708070402000081c16000c3c8405401a69408115401c200c100e5003088940d0510488443c482d80e090180e0b14404a448a104a80410a1845014800c0c0f100440c41c0c0d0b8802c001c200840b8040740940b2803d40200907904040c061131040c01d040606042c116031805680c0080ea150080c03280d022070244250059110100314070b20405410003000500c1c02e80c05640515141001000c46507042c02614081000100c1c0d002c035400f08422010b5680b0212000149000e00441200111010305800701141d04a0b992041c44451880e15008441e1140c42d9210311b40d9170822034010b400301512540100d183c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 629610152 1250 629608902 629608943
    0x30d1a040908180613030305031e06030d030c12060b09010915201212150604030b010303051c0c0507050c090609010b1804141602012c120d02030f090a 66
    0x28203000000f034244c500e0318144001900901a080c0c00407004a0030110602c8180c0e000b42404090340c000c08041c0c40001d00700302d4002075594002c1c2240200b019141c0004215003445002c54080c49085102d00780700e80c94485400342000d8105034402400074034905070003d600c00d20300c040004c9080061301d6110844522000c80c48c003031511807070503000c03d00c10405540c481c00310480c014040a0212145031105003072144c080426800d40f400101d00c9140d0070710041c40406e00e98036001e03045940c14200203a54200005405004610858000e5407407442d10032900b5405405c400207144891003002900c414150744800c00401d8142a10300315000390300000103002401060005065120034603241340f0f8045001c00c0013405582d0200b000015100203c0c0030720807403c1d1031803002c0401041ca0300080c850b00d03001c5030a42002e80c0a54040c80340d000f007280383c0410144024444500783d5849014010303641e80d503009441021350300a80340300c01160918000181c08510205100c082c40d0362240f42c1450524480401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 629611402 1250 629610152 629610187
    0xf010c02010302090310050402120c01051c0b0a08060a0b04060305150402150c1c2607050702091e10060903030c06020903061e0702010c0c02150c030d1a040908 70
    0x40741850b50801c11076a856500300414941c0a03400c00f008a0f442c942441800011840c404001c141d540c4482241859a038100e01540c240c4000581c14800d024115002c034805403086100075030704060304481c086034964010400d140b1a540b0650b0501c203000340d4006100449000e40310240050b00800e4403005549120f04d882d540240c00180f0004400100f5510141607602c040f903401c3c2158001006403e140700c030410800185821400e20010803180c01c201d018805100b51004003070b2406140c002504540100140c41203260094011800c034030700b140800d002c049005051035519841038001580050400c0360030380035180d4640d51005001d00d10342c1d0948421444540803200c0326000c4c07200c256641c03002c0005902c10030030714030701000050750060f40d41088100901030380216410725180a00d501c0e000f0941c01e80f0280d041d200c0d00300c4480340c51715000f01d60050011854081c08001800340d1519a41e03040f1807042c040d01580e01c0003050700c8904010031112061801040c121040c4808014180107044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 629612652 1250 629611402 629611427
    0x6041b0e0c0c0102040803180f040b0616031209060212010e0403140a05070f26090f010806030c040624020304180902010306150504060e0d030503010b07050106030c1815050f01 77
    0x1d410552620f06032407c540110f081c14003801c4e100021a449840e14041d0040c80c6541980c003002400b480002251482c421340700500c601e400122441401c240c0f09404401000741c0702070080240b40083d02d046000384d80725016a0b02188060313000800d1405080c120f8a000340e6254907000c00030341ca1f070351442040342c2003400e6800a202041c4a800003060364801a4050b0743e2240a00c951444d4904500301c116072000322040484200500500d0006d89520b04200070000003401c00c8117527562200002071616418120301d9400a0130700c8800241280004d00b40c04a09030307001c081070900c0b04a1a822a80c1c1d010ba8072807442d404d40a580b000c0d0000d1016032001031018010314001c16a581c0315283c160310102901c841e0310010307000040810a6503030110741d5408503076003165601d20102c0d03d82c43c01000c0d1300040c0910301c040c14001451800f08002540110b000f1035002210745100c40c0d440e41101402454200034099040c2418641c0e1000c1a21404060903104001c01c2500c1c030412a50044230408040a03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 629613902 1250 629612652 629612677
    0xc03030c0d0804052e0c0905150c120708030609130f0308090a0b010806010906321210050601030c02030309061501050c0601090e010c0f0906051303120206041b0e0c 72
    0x588040040320f00000d9101e9442104118000b103c030740c0040c200890b40058182c1c6c0c2001142807050080d55105500b03140c2070701901403a43e0700d440c5580d5140e401c1900c4c0c0103c046454070001442002c000340782010790322030714084400f004143e951000000e204428143d0040c070300741180c1810070000340a42d44080d00080400304641d20480f007a90780c4100f065084c1c00c03035503080c1d01180041086400d1030103194041c04002d4540c000c010200c2d208909081d2402628020201c2740740d03040c01480c2c44001040368440d03080700484665512040580f0000d2405464a45c00a420308005080d0385000208490150715450300400455842c030101d40010415220300c00e0410500304110402082c6c100300180c041e000b0b08400080401c443e5101900f10760718202c2020902c4034481c00c01c88403680107043c500071910700d42080355036862446c198000c00c110981000342800d0002c88884401980040e10920540c4260348040304a0710815041c00361a40d83d1050780072214007080000c40403000a40034201e48603091 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 629615152 1250 629613902 629613913
    0x3030e06183a060c0903020303120c0705070e010f2102010309061d1606020f0d0c110d050114090f030904020c0a0618050d17011214031b0c03030c0d080405 68
    0x4200c101d942241000d1034200c1203030840005403e02819105040044240303040074400c051842d030101ea2070b40242c514241c40041010001480400c0c90001c07510303029801020b80b66200e4464030f032000001003c0c00b800310740d84045003000c51044824603248200c482d0240310302208401c80c1e0300460107046008001c42e8110f4444808500f0040004183c400c010306e140090840b00101b00f40c05180320500340c5c03046086620000d528842050041610724071206035246c0000c1640d000c0c1001c210496a141c85590404c050344060030901030194440ba001d89000e1038965001d07191020f0725951034640070302282642e00200041040c9180607070003000401c5204083d14600007880d05c0d41400c03141d82c029400c074184034540004007000070a00c81002468402d05046000080c0013542c1200000140540d0070030b85200e060010901c40304481356000e20856100b1070b0f640d03488549030341d4218441150b886050f031064400e0448039180210a43d04e00307a0000c80240394100d41c9590450761688040d10079521400780 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 629616402 1250 629615152 629615209
    0x314190b04141006080c0a090302010f02190b010e060d050601180b10081b04030308130609350405090c1315031a0d020109030215090307030c03030e0618 67
    0x1468180c511818110032540c3e00c0e03a25060000c0d0151030014460f13545404200a03001c1010341041d600b03410740e6020310b0800c411902c10501a2702d0540407282a42c40245240c04500c100080c0120725416500c0f0840c000e00f554442c41c0038401650000e00c4001c0c0b441e080400148400c0c1c01c201d9501c000a40030501c00f0440800d5400403580c0b00c0c00d0804c0b048000350401041140c021054a10000c40407060a0498a40f0340f85071002000000d0160000c200300c010000315005002d032541180045e240c0050450a038440705a41c005100000d1043c104080340d0028002c12850303122505942c101d5402500244545d036407048241c6081e8080410460402c5150300040340840c000c400001040095803030001d5003000d600b2802e0114011114014800d16441c001d03400103036805000c01c000c4a41c15200300c200d00b5032914081c044c0780501800103805120b0507800009100c4d0795aa9501124041e854810048480b5402e1014134030408014200000103020030350220b0400c400074291720034462920401c403141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 629617652 1250 629616402 629616431
    0xa06210203060f120105060a060c0f0201080601110618060702070303050f070c0b1207030b0901060c0605220b040204061e03080715020a0e040f0e121b0d02030a0314190b04 75
    0x140d0300300444c0f01d613544504002084c00c0610b40c0c01c000d8003450401c2e002c0345090341d688041256000390001c1c1001040c401003040759000b6022509a1003140b800e035040c40c5000c0c071b10f08440803519420024036202d16008655814004070711901601e8140e51000d00e8400300d21040516907014040880b0034101d0780d1400505103140d40007070401d440f1400501d080c00e09103401e00500b0707144407050302e600c00c48245004010168101e416072058030340c003850200790b49c1d89609408101081c03002115904015808015080041070010301e4421882120200442130702c84c06002c0080340f1030a040c2e025540b0901003030011806400207040164400e20040c000307080294000c105070b80011801c03502003920808a014135113040e00854400301c607101c00401c4007040490055685440d00ea040c64000d020001c1d5000320b455600c0061400c007101c68003240e5082e031400c10000d69940c000d62b4035000091074091000d100ea04c00300c41d00790048180380280541d150030805810f006025060b500d540c01a611403d80c180c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 629618902 1250 629617652 629617669
    0x11040302040e070f050301140f13081305041b41040323030d020f0903010615080901050402060a11100c02010e0106050d0c090b01051e090a06210203060f 67
    0x24010107842e616207424001c403010213640e00040c3c4264189058030580c0395200c0c01c2d05e03510001c0d4240488a98403a402c08660381d40c030922002d030040d100042d28440f01840080c1d80c40407540b00b41e0302044049501450420500c031040b5801000580fa01c6284600e0920820482d00011200c0a5030003840c030009210140e824442c0408100020041020018400042d001d44080c00902018134041d20745640c030355440c0c2c0f2408500c142820390115007000c1c002c82450640b0786500e0060000c1025548650828204c90008d0941308001404200000d8890307106001d104d0040e0350140165080c0003901d101600c3c9441c0680000d07101d445802c00c2d89075000d40078042d1441c008003070b400020b0100d008004082c2554800d40016000b0b00046494000140c1d9003210b0f401141d0f1000e4000500d840030b000101e40620641c00d0840c103114110429001e04942000280b1201404543d000c4807a950380c3c01c1514081c4010840d00c6403400092910000306149800a541c01a070060450a200d03241d600014100c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 629620152 1250 629618902 629618921
    0x90102101a130e06061c0c090906050c0423120a0b01050108010602070501050403020d0203030712030b0f0d02010c2013020d05150616110a0e060a090e07091104030204 73
    0x22103404035140d41d9042c0516411041d2000b200244402c0c008410304584e90302e8040c01c402c1c01500440160008440350f443c850840a500c1001c10011035603410820000e0061030800740c071407615200c003084c2000808812681110500840c9881281848124001020b44080401c1c1c20241c0c03440e5034501a40c00f484005c5100703206502200403541440001844100143c0161055501820381884140c6c2c000050b80e01703c0c4c3d41215040c100065070301c0401e00307600032030078010f01e8482d182b41c0410715580c05400103d00c3c0f10381520b0382c1070f11459210401030740140302900a030105005041c0342000c6115440b0b0446d10340f81241007140715401c2807020400b400d900c540143d818a80c0450764120303442c51802200d812003101c0548042040b41c000000b01c152140035048150030680d1900c0d0401c01c090003003440d1500e440100541d040664071614181c21880031526548241e03640800031500c190a44186e514010360800104155800d21500344004d0080701c04461020313806000010069440c2c4c01010030302c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 629621402 1250 629620152 629620181
    0x140c0f040306051305010c050c12090d0c081b010203071112070807090c020c040c021504140a06020702030105100e0c0901030b0603040f0c141f050c15190515040209010210 75
    0x241340d2030300b04582119001d06005003081010003440280c4e500c002014004400c01d0811159a0030f040d10005180d080180700042240400780c0c030003c1c1c2107002144031428040d16404a03102c880d0160012a100c0c800c440c8020300210f210f012191503420002101340c481c400302000c403040c2944403501c0614201b5154811580291100400703000640d050101001c00501900c0500041d4071624006c0d465909c0d50b080702c0d85034003042d80000c052100e23041c0c0f158482148239007130b00c02c0c02c000e038107210b0080c0d4400f141c140c1c081d608007004a101040301659a0040b10070b09900c240e06916200c14400305a88540d048504154460090044990300c0400440c010703440b41b08840303c0c6c00305506e058094602547e00844030441500840666900d4149400c0300304482000b0951864501c540c06907828000d81d40f24401c603105041d80345084282ca052681e0141c000300e51407d01084550303d143c01501c0086072a82105000d510090006080c03640280100d0780050040d11280034907011031724111070310216031041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 629622652 1250 629621402 629621431
    0x7080402031f0c1103070804140d060e0a17090a3b01031202030f250503120403080c07021c060b061c0f1406010c0510020c0606040f140c0f04030605 65
    0x303d40c0080d030b02a4290003840207141850404d4031600c400d0b0003680302e0300700c140600900c0d00141d81d070360000719001c1e182e000c6402c0000100b01c4050559540a10f407044500c1c400780e8044180c4805008241e5200120081c103090b840750a04007602c08030216010000c4420b0100030008070030f8100255002c02d010400e40c07052541798992705010701d600c0d1903048004250f400170050021030000c00d40458416039441084450011a00d046e50101046010b02c040c00310300003c216420f04034031181000707014900135640c0005503114140465800d2044400007503009441046005900020001c0107010070f0152000054022464011803090b50140c9040349004030940c0404540c0307a113a100301c1e5103234411104201300f0480e000c0400e1302e405501038280360511800007031540c1000380c03c100300b015a13180c0e218155111040000d040d41d1f00c1c0801d40301c66209904207201c2911036043c0d1700c514845e180c81100502d03003d49440b1000c4e02c150307100c1c6042c0406c0000402011020440d640a0940165844c0304140e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 629623902 1250 629622652 629622671
    0x210c050c07050607030f08040f0c090209030609070f0608191104080f01090309050405060d1403040608060f060f0309190308010504140606090f040f051e010f080607080402031f 77
    0x1400c041c400d41140344640402d02c01c07400800d038410500c2038410b40f141400d407459206c9003080a80400d140900a081032047c84001c12031505940103005403400c00d404540040e100c00010a484203c28060750105081c0e1800410140380f04030401d03a004901c00d5120000e444003c1d0848040d078007880500d01049000140130050650104030903403035014a80c00030425a9815a00141507224601c1060701c078648a10108a483ea119405654001e0307010458800314401286401d880c0d80052003000003065850000461a04141c1c080400c00c0b0340060456107041c1c0c02010280480c0c20241c0911940d02c03c107000400d036640c041d4000310302d00e806038440004030341c5098108400e03200c1d0b140c070f80c0c40b180c501c11040c488035413907020580e81c00c040103d40400210b00840c02203002003880c01700c03543c1824208400d0214060a0480040fa001c01c2004001c510fa0780741c1603100c910355011722034011300b5802140005d2101e84221802500a8070040a0b1181c403419640740c440c2d66143c1c510303600c81480d40c0e1032040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 629625152 1250 629623902 629623927
    0x4051513060302030609060d080c07031b080309130c1407030206040c1203120b13060905040606080f100b010504050d03030b030607021506040b04090b0108030406020105060a031101210c05 82
    0x240c0246400d1030150f140d4503106010540440d0041c0c50580200b0701c0c2d0400101f00071160090300c0e0002c1e410007c0b03404195403802c002d99403808500d08a82451402e00c0041940100401103505400000d0b00b9011034243d01c1403500020b0102400c000f013003005007000c45400880c41c90080c800720b4081e40c014005410300d070400000c0c8400a52061850407240150310001a801004150f66070483c01e600140111151000c9000d1714245035060b55207524240d03011584407080d0f801180194000c850030030170f03240c0361503045030f03502c807030051440c800e41c41402110052542c0ea044004d1400040c54004d0401c1e54030008600d0a8100031f5085011036290f03407180c007043c10700300036042e40001c0032b10040ca100f002c0302da8226404a40a81114000d94440425105030b403141c2e00441052940180e034200030b03681d079655143d103c1d0000e00a403001035080901080c142d29120300344800b0740c1e4000c44206007a0041d440151881100c25600e246000d001800c002140802072040081c02403803038940983d210700b80d1010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 629626402 1250 629625152 629625187
    0xc080117070824072d14042301030216080d02090d03020a03140a1413030206040605030702010b0103060b0d02030618090115090501030503041701020403051606080a0e1b0105040515 79
    0x210410805c2404120400c3c02d9442504062249807000b02c01c842e411040c4101c0300002ca005110404005c00600015078949445412602c010003141440d040c0c003004004409034031070040350f044500888003602e0301241010000345254010300030011302d04200a40412940b03100c6540503000b5030001050703001495041264025131402c50325480f486d1007031121018003419403d00c040c448030320f404203c0700460011701f04407801864008180d182c8403641c4150090055200300d843ca4015401c2000c00d10442d4040d008030f0003582c4081107440d08008a9203d0795000390001407062340d00c08410304060055a16003180d241c0500441000420700380d4140110a190b00e03142d5228040452500f401040454008019241602ca07020401549542d520030020b02a0285400c0909a8000ca0414018410002016004813162038071044c80c0c60307071102400d400701c40603405183c0f402c0d0403024400f00d240c2c0c3c1c0c0007406944081d05051490803d900e90300400d8600b4085c0d030a44608600018070700501d00d046040c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 629627652 1250 629626402 629626411
    0xb10051f120f0605030a14120315010e060d11032a04030219030b090705010809010b0901031502130e064002070803070c02040b040c080117070824 64
    0x10501210221088000c20040c00c040c80380a00550700c0820b114500100c1d008500104401400c40d021a445070401c5078940e42058640c3c20780d8851003080c4042c0c403800000303a900c0f54042c08641a44111140015134444600480c01e0f8bc0c8680f04008800e1803100f43d206807a154019408029224900410f002099140040a8804402c035914200c4a82642c000c111380981b40d0580b4120b00c0c49000b0b0132a9240b4250a80005025008071400c02075007400c0001c0b9071040320300c00d81e100510794454415603401c0f2240d002c90950040510401400400c110325085d00c0183c200600041c0752090100400ca80042d03d504505a9820f000c0d09000031480c201c02040103a0110044041d910100303030007150400348203086900e0003105400601759102140381d05603040075402c01c400e41d41c0c07450010002081c840c01240101c0c07055180020f0105c040c1001d20808011029a172101021a4204000b01c210403da5401020300e80c402c801000c07640d640280580302c444486101040d030400740342031110a150000a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 629628902 1250 629627652 629627689
    0x20307090e070516140f1e0c0d02031c110a030c05010501090e060727120209090319051b0316030806103509030903011b080c0d090b1005 60
    0x5012807a0384690700113040560100c0c0201e03025a0a500301e50825500c840e02e43c08a000d10340b81d41c0091401225005182a0840300b80c940d111603c400300400c00c0394940019406074044481c0701d08025544c0600c5204500500b020b128142204460a00c0d000421000718002030100507004101300007402118050300764a00700340241440281070030f40c0d0f164000c00041c01c0280b50a080c800107045e0002e1114111541d007000882181c8070b4010b129520b4806030102d01031540703080044c00b144004403e40344441402c0400d03901e2240110301c102e45a821011404034003030395003d1a41d5142100700004c00c00d1a5560000d000c92880609000c2e00d51800182424012440721028001d0568010300c01c106454800c02541844082e410480e82102c42c4244904140f400703110512501c54000009021890000c900034010b0b01c80c22144c4548584c10800110041110b0401203415425040d01406840d0041c410000c0d9540c02070f181c01c10004015110030a4078400f0304020301880c245a5a907240e40703140c0c1c0c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 629630152 1250 629628902 629628907
    0x6040506030d12140412110c0109050f121b011d01021519050903041509030203060c03042a051806030c06030907080106090507180303080403050d020d020307090e0705 73
    0x1000442d0b142c40e00c650580c0c00700090303801029042032003a4442c000e4520102d9103400e01d440c0514040c40c82c41c1900000340b001c201440550311500e400082c0c00c0110400680d40c0310081c40c9050240451150264070190344a40c1d00c0020080d0102e04102003a80140040c8070595508403110016100542d80f2020145940401c100d0030800c0c1d800040c43d00c040131081402c03208a69542c4009000442d034000c00520b054280390500980a000002810989a5416042c03907401040c0310107071030425840c40000c0d01134101a0014001c10520006964002d000d112503a401c20b9107800c3d02e400b4000360f69240030710706410300e00600040c18590302801d4413a507901a821034a050100020b039842401d0041e0b86d10038800080007618a8401344814801800c80c0c10080c01583c0d103d440d0310300039110031075140f0000740246221841c1340048082600880c0d401d07071225591500c1e1030701c046401c1e0b88060a180c05017a0204901c49440c5400e200031880780031980d0340c44558a0500c0c0c6981c0c6d108001402200030010107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 629631402 1250 629630152 629630161
    0xf0114010807060807120b0402120103021302090f0409050102191706010306030b27120403021f17040c170a0512040f05010e03010e06040b180a030c110307030b010914060405 76
    0x2d03642c0c20117030034107046100001191300740001d0141007100c25003183c00402c0681406071000c2c07010341039038400c40f21028074440c50722003a0101c1c09610304081d886808086008010f0030030754000002d21b130180c0300140c80c0064a54511000701080e40e04000014412984d0380c0c0c0015880c0710072504440c007442c007805814550380b9164410040a0241c400150b015036807040c0c0d0b0b00403811a968641010400e41d14020015030314108107801921040c1d00030282103112458000040340b81191145690b03c030030030150104c00e10b80327401e040010422207030200d03002c0b0041500100d101c502c07110002c0450081001440ba450b1203401c0c409004103001100409101c140060300380d070411007054403c28a004d02d41d8558600002e0301420107600281413038001c880620043c4004000d030035101e10403e046840e420010000c00304e83e201444078020b030004d62191496400035600c02e45400e5051401002c84035025220740314850460700030303800046a1603540c034600300811481208180d00400484080156140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 629632652 1250 629631402 629631407
    0xb04060b1e01030e161707050609031504080409091101020d0926071e06020d020f0304060804050c130e07050117011203090b0a051206060319020d0b030f011401080706 73
    0x5201c0d20941455160300784209058020491082c00840f580d14000103642d0300d0f00d44a2441d06088222901801250b10100381c0f410a40300301da026600c098020a480c04900061407440e200150003124041d80c200800290180f40b0300030500a14050400341c0c0c000004400068a000107000c102030600040c0e91003001010252181d03450b01081c0c19185d18164805d07004014203001c070340d410801c01200b411042e400c450440a0024060f03892030b030201d072000d000c10903050365034005c1800722105030351040200f8000a8482c01405402501c120112001080700c540090020410140b0100c039403540c40070715900880c001c0203208010082820812b55106513080070030703141c2c4414060f40c4040324524144d80100f52040080f440203003c2c07036100035115000840000d100b0340c00303000758907500d41a01001c103880d8a03020084074000c03201d0040c0701c103843d60088204406900400c107510b000c03c5e52241c8181031610117012540d4820956800016407500403010b052003024180c1059500b0381c0411410301600340c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 629633902 1250 629632652 629632699
    0xf1b060720100e0138060325030e062e0303020304030b0402010912050f060c0f070f140d03021b070302012a081620012003160b04060b 59
    0x310b03100c00415101c12081109014014052500c4c20088800f00d40550a0b002e00d03d900305582d10401108248540b07140820146001c15a0140710402c0004c8100324401c4001d482003426100904001c60400301640c070041c2800b038101d91400850010041200c10f090122043d1207490120030051f40c0d1003421a1002942c034003a80c04018800084800840c05583c010202c1100070702800504500003680740c44c24940340d41101c03041640e5031061f200450724114089040c0d800c580c580d48503042c01d04065848d10b5955011680043c0c401180000d1244500078060044501c0c281ca213450141c0d4400640c400411001070903055488a90001c003003d10060380d1124200c1c42c0340d040b544460828650a850b02070700c0340e441400080c03031090000b80b43d000a182100c04224002d00644140c1e1607404040540410035801c009070764001200c83c250300041c002120050394080c000071007117074200001d503401c6a044060a0b00240e400b608003d04010411032180034160401d28141c0c0d000c02c4241307400300700410a8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 629635152 1250 629633902 629633923
    0x51206060412020d1109071112041a09040f02030a02041404061505030c090d12180b09120f0714030f0304030213180209070e03010b0f030303010b0f1b060720 69
    0x40f030000f020101400301c5441c15081720b0000034a0000c60b800d16200140c0940500751300600c2e40d0160384c0241d001e2102c500151011280e201d1400c92034420b0003883c0481070390102855070741c0140d0714062900490060f1015500c100c0c030520740143e0f1036003030104900036100900c4501c0e100b1810044280178440200d5031450781d0040740d080107a141d0300c6108001d40240030710180f041d00a12454030ac0002d114150b2282c50100d04940c0301c109128110402c3c441514410340a00c49103901c00f0000c20300142000400b400c1103070a00015240481c1c28159041c1c06e03d03107958402a40b1055051030f41c4400e00e000d201030020400b001c0000c61034185554041102d800e8050142170440750f0300c8541c4807403001500c01070049258001d0240e8814646140050f26824141080a0080d80780c81646055401c1c1541c3c5c048584000030021802e5030310b84503860300c0780d5001407040e00172705c6002e00c82008581c404403a809242d11030600545850300d03100c44000c201e441c107581101c07800d00b042c2400b0785d48010007140d0340020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 629636402 1250 629635152 629635159
    0x2a0f0e1f0e01090b0304080d182105042103092301030c05071a04201309031b05070e0f070c0b040813032019060f0e06030705120606041202 61
    0x200784004006854410701039112601a081c00000c000401040000406092180050401c20b071408440329402c07109042000412940050520b1050f0000c5240031601d1901c03586401480c141c1c50b040e6034060f0100b824028075010540700d50780400c154010030800e01411071a03118105940000c00d0000350f154030711910074103040c1c1c0c900c004000b02d8805d10455801642010301844540c00862280c503588104403070580301e86904102030300b50505543e940308040318000344810341c0c200141d1110401080d03840c2c3c0480c00c2c4148200340e60b104c1d10481a8000d446070086d00a04002890034070759054000c0014180b585089d140030400070820b41001460407950303082011000d1503500c1c0d10b0542c141c0c0c840e2540d2104e44005046000040020f40f0b2180c0704102107210134503056200c0380050002d00c030441707009541c2c400d143d01414070071142700e8400e2042e41c401d0762414400d512001c5010645582c01030716441c000450020303081510505519065810503805d403280c2e8a054074200d402080c048180100a12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 629637652 1250 629636402 629636417
    0x1b080d47100906111c020a0c060816050d18031701140a0b1b070f050a0e1b070501060b030c071b06052a010e030403031403090706032a0f0e1f 62
    0xf01c1072020081d0500e1003130b00b40006143c1035000b00020356187c001c2d09040311032644a041c040341991040c14118000e402c0c072040c0903c9200c4c1d04034144c40a0700640e9900b07031313031a682d40ba40c40244103c0f44d00442c005400f945a0580303101d0386c8401740e515607505810042e540da0040350445c1c0c45841d004040c400301c80d40c1c400000d0312410740201d00702252f003000200402a00c60755002150441c00300340a0f0003100e1040b2035020705c1035502e42c80c4c3c3c558568100c400443c000d941c0220003119250010007455210f01c2040001540c070745403c2049419002903400c000d2034240802e91404000300c3c489482400e02600c140300c4c16040c90b1050080851060807800c008120200c8130224503000101149035120b50306800078086010480f0010341c0d01e8121303100c1035001603001040c0d1464824058100c078040c003900c0c4080c00c09a400d2620681c0581800310407141540d03d18040001e401031002c808034400d013000c0c1d82c0e45228000010000b40614031500c5114420251008491044081d8038580e0b100b1b24050b00700201d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 629638902 1250 629637652 629637677
    0x41502090603151215010501020127020d030207180203390a02011503080c060f070504060807050412060614040c0903140f0604060c1b080d47100906 65
    0x1001e0a01c03040c1300140a01c1031012032841038003e041600e058540a90007007003030203c0b040d201c05110030100c04c06101c101503903c1400150a0507080d1001050080c011650520380d17409944580010216181048560200c24025651449112042c0010300c03182c2110050b5507031362111402d182d40440d11214000001100343c0f0440c000c0d00100142500c140d401181260347c0e003030100203644102c00c8040180103a0780003403000f101603a0210701401065580f20f007054205642500d814401500700d9080c0a410300c030001d0380076144541e1000240c4901c0011905070b150458208040502c41c41079803040b4202120007813402d9106040c1000c890300400c3c0017034003020388400c050030316004214403001d5000d000200b105011081d08901c245114071b958054144c86541c40340d00c1201e00602004108110421041e1440e10b40c1350070521820102c102c040c00d001d0350284403120080343d004001004800080d00c00e00030b1501600001c6c02c0420300340e40c00c204a01c207071310b001440020b1070301a030400c1c0441c0d8000d10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 629640152 1250 629638902 629638909
    0x1151a16110411030f0702150a0903020705040e0a0201090e0c070204090602071e050607020703030f121d0706091d04020d0f0204022b060e16050f0a0804150209060315 73
    0x20004007402a00c02c212240b498410703440258011035030b880061000748003103501c3c4c43c800102c00081910805400707a050300ca0780c4100c07010b81f140345010303021032003008408103a03039949100d412482d030700840c01032502060074030000d405080709030712410302c0f24519003c0101e50f06010040740d1205504940000340e4490034078103d0024026141c000d0690071503c142480006080c40618500c0c41c056021a4402d585040e000c0360f07150b03014000140014031051039401d801d40584944202e03d11241d10100e00403140c03141c03840040c94030380c40544140c0e1041d40d04021094110203100050420540c039420303180c3c0d0118000c0c299540c0540024022840d0700e240c1401e01070f20020000700d203030b0f00410555452070314403200c00d200416900710001201c00340c0e2550b1101e80040c0b140e40b0403542d02d203202408950711040443e0004a03008010b0060100800001c45000301e0b40e0700900b803c01e0940c64900c140e0500b17090070344075200c0044102e0644c51040051514654990055950120030111000b41c01030301580071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 629641402 1250 629640152 629640173
    0x1d1b03070e010e01050a0f0b1c0e0d27030c03020d05120d09020418050a03030b120106080d2003032403010504030305160e09010e1e0901151a16 63
    0x207044550880004204090f50f4a1143e040b03070030841e0680344054541d400301080444034030901c02c25135410403540c01c4201d00d8211000c0a844080c0c00090403441040d000340c10080f100c0351010009940484421105c200405003200c0d00d0050902c0c40d502900b07641c1d5031203803e10329000c068440d900c0040d0705001c0100810050208003620304000761524046600e24000d4107250100f00e128034180400b0390003035085186005135098000c80140300321040f6440540007405410b280682001201c6101441a402401008018214a001051162920140200000020000d0241c003078000402c1c10b100140000c1603a801988c859204d4043e01107208181710161056480a5015420281044103054160b030000c2e21908404030141038500364031008440e410030307c61303019922003040001032154800c1c0c0c108082c0d002c8000390b07041e0000c9181d04039440d0004402c40d44a0703000c0c1c4d1260901d002c855036406404001341030640f10891540d034800e6591140380141304407080030500103c0450188103003c0c16 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 629642652 1250 629641402 629641409
    0x230d051f0602070311090c0315010201060b0f13051017190614010e060310030b0a020909092401180507090902130611070e04021905040c0903061d1b0307 67
    0x884012a59803907102079158143c0d44801c0d80c82c010090700140f55400c1000015200b101c1507401035180d640c4e4401020480000b42a44d941190359800d00400c6d03600e1003400038841002c00311851521085d40c101e58551162aa40010b40030301d02c500d040c0c41c403071038101e954100c0c00c4008103036140c025560f5100255551150a811801d02800c108001400ca40400011104900c0aa841103d0459002c082c05014842654202040d02d2086020400314240c14192900f001c0030708400f5141484540005112240c20b4031140003a400050745400940341da01a0a404000319403013882966141c68503c0500f04001c8202c1c0c1000380c0c9603000210554840c240034405804004411900c0d0084000d200b5101c80260040e48041003841b031604920081c0080c00d01300f119420200b1076015619942480a1405544000710001c9a0f4500104007035a0368001c502030984181d03902054240f4500300742082d01d0722900344d40321045130a078070f070340b20401e004c0744527010b804012086038a121030a20100c0e00d88034041e0b2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 629643902 1250 629642652 629642701
    0x812160b070309030315030822171c02010908090f030a0c080c1e03070603110c03040801141609030308181f0c05190c1112010903230d05 60
    0x301008152a0554031030700c035641c041d680c10005030001da00e112210f400240005003014000b801141c200992030240c60400d204181100d442203591080d280c40d0200544804203100d030013125100310445e010140c070384901c490902c004d1204452946840c4551300c60b0b11f403918003c540f00c2901500945042010b000182e910030300d140140f0307548540c5d25031905c80c194001c1e4402e101c0500d100c00f07840005a00f4080128009000d8041c0c01d20f4008103800402c2c0312400c50b5260041407250081207001400a48005c0001500114200d02154800c00580100030140010b5107580d04110013a168005110020780b80d06040900701a250f04200b20321200e09500c40c1c803d50b00c90228650100302c448400400980b210b5181404003100b02901514680584500e00075207030b10150102840c0c910400425003094012880b00050550791000301e0902602846034103001d0391240301240402d40d01500d020701c400740300792162010001107038084015100e00d2032400c008588032400721740f60015a1454440101464 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 629645152 1250 629643902 629643923
    0x30503130809102a020114130b040e06010305060111100c140d090209060d051213090501080309090109020a21020c010c111501060e060d060504061e050406081216 71
    0x5003c01401820318400803a5401c0c3c0b1480310784141c09003800580f50050f8140c6602c0080c0c5480c0c4850741264008003032103048500c1c2c0c0f0740f0001d900505400208081d282558256803680351520001d82903031070181400f81000060b0707140c1124014045120304d90000705140100d4540400402101e81c06003604803101c1410b000201c480c040c08140e40a0803090f0700c2608e50322182c3c1d0f205001c01103c0e941d100e00240c510380009041070140044140184602c4451000000c600c0d511541040d0444009030441ca05913031001038041c0461802015081c014001100c1c15481c00203d0760000b81000a1110540c0e40e6a13a0256403044000d502d0b0141d47e15056110000c200d80c51903140e0040c003003181518240064003d03001900380b4018202c0c41c550503a0069194842c020f87c1d0a0180400e6034010a5030070711459940c0d60108440d919806140010402d6420b82105000b40480000d00c0040b0baa122510541c03500e18100070221022510f254003144511a5603110060b50014000e0501401e2004203100c850 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 629646402 1250 629645152 629645179
    0x10c0212030c0615010f1b0b0a062111040b0103090609080a110f0c062109010f0606020319111002120a050a0506090621010218010318030503130809 65
    0xc0909048002c0c6003c440164440560100035083c49500c000c0c00101c1c4003c0c0300b10218054040b400078a180c100003081d02c0f602e00d8035901d401000503980f03402c0140d1a0745082001040c6680c00c600c1900041d100b4102c102c00d16513030380007118090040da0380a07503101c29400b8103030381c0139500019400d81c002505008909451801c0649035200e040a20702040e248840e594170a0000980010311070002001880f543c00e155080002d2600b001c0460300041e888242403c488030090500140508144000480d03a4004446210103540c401d40000c0d0844d0700c24401e410540304030300c2c18080040150305207803008000d900c80c0389080001008403c025140000741d445a4510011241849480d4141c4104000e84994062a05951095801e01c1d400520751000c41c0c43d5180010120210b844d2003454080c40e0790444074120700f039030001e0b59545080404140912125609800780c0c208a00b2444122a58056135540c0030701140009030119103040340e000124030030170202000700c920a40c802804800166030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 629647652 1250 629646402 629646439
    0x11d042003191205030903040320060a110c123406020a020f12060a2c03070c061b03050c0307170c011406060706230f0106020114010320010c02 63
    0x82c952402c461400850342c40328820381c85401a680030302c810070095890b1a207103865a4000001d0b80c180c200c00d05c584103503a55103d5469500510003007026440d901104204110032500700200ca41226000f07464062414000c000082040e194403c010003520025110b801a0b010f540e84070001d91007a46503c0c90000310b0110780002c1c03000d584500c01c84110314400001810f12640710000d00102e007a40d0300c1100850060707203d075000700c038901607803c0e184001ca800c6e049070205505101666082c031900001412424802070003982405018107040030180183c0c40542d80c40c0c03500040b10040e08000b0003087c11303001071b11b0500494801c00d4100403a0f00c402d00c1c0f2260081d080740d1007040d0840096181c403c42e00000c0e0341a002c1584690001040203091030702c9500e071180030300b41c030401140000031000082503031421964513050281d034080016910039030400c43d010782100c51042d55550b04228032001040080d6010511502c0020b258540705400012000160348024610f50029441a94141e04120f00d10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 629648902 1250 629647652 629647693
    0x604030305030115051908070c050601120203060a0b030607050d2301060e010f0f0e0a03051507182103170a021e040f050607021201050915011d042003 66
    0xc10b404c0001164210214040e5114032a402100701c1d003001809600d4451405411900d600c148141440305000d20260340722170030f03e0003d800a40e900c0204041e4882541410040e9030b0388451001c0c01003205c0d9a02100080c2d0b602001450303a4100700c4c00140122402100e60081e48506038948403d00804451a05042c04018240150380004403c00826120396101d802e00c9164a0400d03256001601c8903407004803100701d45c401c1c0e0709030000710300310001000400411403100c0f141403442100d580790801040041c001a1600c0180402a5a800d42802180c402c101d04c0c0551790b40c10f00d90710804010a00c0d00340e9165410700da080d030520140c0c2080000e44013298000b014034103084000f42c01007041d04504004640910b015250711107024000a111506080c0000c040c41d9000400041c0c2c8801125000c609440003240c41032100e03000042c0c000302c01d00045003003501502440d038a8010042e5042c2140d00c50b000f00401c0907006086401b1003491001d20500b1640d1501005810351b03111010019084c000030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 629650152 1250 629648902 629648909
    0x181c06050601171504020c070302030f010f05161202160b070207080d0302120a09050f060a020403050606010305070c022b0f0c06020d0212030406020d292704050c06040303050301 78
    0x750001c0030809001956890140c412031980c1c1000c1c0c408440001170000a4002060881161066010100140c0d4040003000800c400000011854011102c0c80e5020349038042c0480f843c070000184400070b1650080030440c0100984200140c9901101c4e43c000074010a0000191140c14100b0a1282e0341e64042003920070b49000d00201d07a0107a209140407002c903c2200001c507031607400d5801090241e0420b03045410300c030340a02e046492148050300c03a80e01f1b1090a88003d110f6640c0020204100141440702950144c803d081c00c02c901c3c9002d11020300344030b21421009200b41102c21001c0034101144002d9484035884400303452040c000c3c0d02c0c3c0315078403400e4200305072140c0358a004001070b2584002107102160390180d0140c04115407200c80412260405001190f58580910510b11483c016103c0e000c81e110b100c0554000040ca041d07100b482e10b4020841d9240900c04a10308240380c4402500ca10021100300c58211205a856080260400c0f84003450a07900c00e80c0041c000040c154000c0107035068 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 629651402 1250 629650152 629650157
    0x9052205030d0c0203180d02040905070e04060b0f0a030204050a29040b04060302151e0f09040f05010506180d0609050321010e191b0320040b181c06050601 68
    0x910280440070b985e03a000e0a40b8100d0900e030101c12851a170306100811030307592407001c0c7c40403c00d2238480e5a201d08120264006c18001c4404100b00001d001250041040c8180300b80c525000e852400300100c1c000083d28003029001d00e03114408a1b540f508141e00542211218081c5910078210382c16003001c103550f40d8405144034506001b045c0c1d80901d061b101c0d80e0100c3e60700402101120030f511130808a160847c10f200d032208440010310100700492400100203a14105503683c1e921074081d000c20085403050341020141500d01001404a5180c140444140c042031181e542c0c5114220740018245001c000001401d5034100825042000000800b800d459800c2c00350030380d09150a0740d07055101030b000f482400c401000c90303004515800103a00f0016400540e0280100314805400380c803035192000c89103a034001940c0c85c851081030f01c0c480980d03070080d03000345840645030071715020065091f0b000f0b0082c4410b05d016180500003150355600300c25031800e40050200312050400b0300304600203110858000f0301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 629652652 1250 629651402 629651411
    0x19050414090606070201030c180f03060e030a23070c0f0e07020a030e09040f02120625020c0411041d0402010f140304330204050a09020705030409052205030d 69
    0x1401d1900d14082441031802411560501407039400441c041d100178012041803009141c2d00441c03980c80c1105a00140c03003040d842d686982d01d1442c0c401c080b503083c24a003101940043c445110b50f640d00030641103070049083c40d2903100300c1d03950b8141402c910802600a005109003170001030f001801c4a4a40e00700e0b155002d02e000503030341d01d0030141e0b250381c0030110040002d011140114581c2c6004005140c006001d8150700103086040c1d03010032900d22070760703401300b4944d0310103000c009100c820400c0304440320b40600c030520010300018101960350713014507503658400c03900c4500003080314041d1003c0d01c1c02007201c0000c15010103501c1007103601c141e9007074800b6030004140c2d44010240e80d0207480a10903502c403d0103207030701c0c56683d5181c03400d44080b54120180d502ca01410480904010048800796003201880c005076034901d09000c22500c5032055011601607401444036402203403000c003d0f01c046070301d4180b0228407544c41d0703604810307441585082c0800c0d9061000d02081030000010145c148003008d10303010003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 629653902 1250 629652652 629652689
    0x102040e041103070308031801022b0606110c01210c0f090f0b1b010608031c0e0a080316090801060f05010807030510090c0201180303090507121a0705190504 69
    0x544404841c000035003c030208002003071814110222315840040621300041c106086d110450088402c48919a00350408103c50080a181076219020080c00c1c5401c0187c603c401342c030304484e04c410850710303024148070640c1c0072041407000c070103144149058084810840b1410600010309090f11181070382c4001548075030007245e40c21807004880709544050b4070315401c1401c405414100104030703408031400355403603910000b0194001c102170308241c64500100401c7e0b118290040003280c3c0b0700110007159605c049510303408201d0007400c03243c10200000e000c0c1125051080140c0e090b4245600180302980b0308500040c89401c0c42005c542590000da80340c16060321501c10490683c1c009451905001301840000c00004c1c555501020020300309000105601c54004124089c49100c40400d5001ca40c5414261003000300a10144000c2c014180041c2c000c402185c4075520243c0ca02503042418190700340111703001c6801b0741c082d9130040309030441c1005c80606814004040390840e100d102c01d81700c08942602c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 629655152 1250 629653902 629653909
    0x10030c090c02190503120c1b07050f240a0201050403030c020d1e09090e01050405010b0619140f0a1e0302181e1f120504110d050f0102040e0411 63
    0x45201d9035640c01032842c2184810100c060f4550810102e030944810001014034080c00d0103014820300d4100100b50310b500a4049810404d0343c81d508907129074010100c107000703941c0e800315030b001d000c4000d82d08400c264000b917000100c0799410403d0245003000120304002c038140c0c1500301d01d100c0d5200b40d43c18041d240380102c050343e44008205642000c40c40260014110384000c0008501280c043c4c0f40030001187c0d104500e008503007052800a2090b5107070300070841800030902405082c00b2041d9240751500c5c4800e40c264801c42041030250b400c01a20960000c210101481915802412124a0303691100c2107100170b40442c00c1035082c104405080c0100d405142d009201303907164021268201540c40104030100018159050720550b001c0060340c011046a40f40c9211162000411500b003192001b01080c1c00b4090440d038802c020b2069040604000001e41c1032a0700c120700c1c1c034003a911000300001d5840d005051201001c00c5850740c0d880807400042e4203d0044595001b07900402ca45400c143d00c40051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 629656402 1250 629655152 629655161
    0xc070923041101080a11040810051f0e0601050f0c030a030c0504061d06130608070806090103020f060913020a020703150e061f0b030703061805151c050610030c09 71
    0x203420301c0002c56060301e840d400364815550248950703500240e81c05040101010356001500003100c80e0b404500841041c0c040c510442e80c010f07018001800b1011804146a00103422138056206200900e0b0003081d5540d0007071080da6440040c50705016154408210581d65070b4010841403000241403d0304180101d008404450943d0b1301130342c0e002c01000044920b1300c103c0c03008040c0150401410000025845002005107020300b50710b42e94001141014000200900000740085209184c0381c001040140e40c1c0006103004242c081d110355403901010700015103001041c0410f017480340d000180c815000b40d4045990019031780714912030310021059252030300895418400d8200d10303501210104600001c4034003202807014818005084503600c560b4400180c1d00140c9070000840c0c1c41d102d06100982d44069440140882110100482d14080301d28007a00c8044030400e5004502c10b2102600c4000e610003280d00e41071f04142110b0f4a81460648004081c400341b006a600f007200e10b60100c2c090986008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 629657652 1250 629656402 629656411
    0x70b03152e0309050f0d03092a15170412030c0c05030301141216090c031404060203131a010501140a0207030b0705040815070909060b1804020c070923 66
    0x444201c0c9000300391040e402805450020341d01849081024003148804012090a00a00da980031421403420b180400300c0304c4040308407c2280e00b034000c0341c240c000c54070082c020448178459501001c0102840044d1600d0300d43c04041c0c010078040b50204400d0284104105030100110350b41003224810345c841c01c0f1030240712040c0c000d00c96042080100329002e4030910740800038400034820f0a015072540c0d541450b1102a8031480142c901250703080007030001d1846000c84500306801d0900c0030f0b5132429090001484020b0009141d582d011002c6080750302402080c7e90542e5000e6a030b6140b060a000b00202d8030202480b60314005140481030b6040c4500400685814410580003003200e117055985601c14040001e2100c420018240b10000d07070b210b030400c01e9600d04081800c40c41d2050400010062080095801001c5524100181013081406907000c413001000502c01e0b8140c0040300100180c080e1040c5040700b54507116050011139011011752100b00940014165520703540200c0501d00c0302c010040300d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 629658902 1250 629657652 629657719
    0xa0f4a09040206070c170610050108070c0b070e0406060201060503102003190c1d03010203100b0d0b04021201140301051012030c060e07060824060c070b0315 69
    0x4001c80c0c0107040c004003400f4007910a8100515450b02e802c503200da03140400c9003104865000c1c1082c80020130006d5000e00c050602843d01c841c0502c2c050101600754980312200610002141d80054101440b4841d401176401c0010810b0043c0c66a0340c5009010785440d0049500c24045da00990302180c48d6803040b04201c1c01203107085060141f00c4590320b0407540000b050400510040c04003010603501500c030740492420144c5804e07240700c014001720300038501001074890082e03204005100ba1240045d0a490031542c0d807410f040c0d40d0b0001010240042c180500b15aa000343c0041001c001942d13209085a0503560003078085840000c001080501382c807000c1d1420314a880030160140034440100d00c1c501c0d412806401d04000418866807004200c4000c3c041c041003603000b0000601100d41e00c0030384c0e01d401c8610b00000c1c035603c00c2401040080c84640100d1a4420440051043c0060f403051200c1002400c1d00c181803500c80c5041007a0102c40d9400d220414461a2000f80100e400038150380c0d102d02d01014070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 629660152 1250 629658902 629658919
    0x6090b16031202160807140f060105151c0b0306150a0501030b01030b0d051b0a140d050a0c12023f0109060509010b010f090b0a0f4a 58
    0x5031000c0c1e0b000301c0c1e51480194100e808010b1160a4981d41c40e450759924810000103030380e490541462001c1c090b1140c0740781202e410811a0100c101c3d00081c4d21815030304222010f040e561000d043e0824107200c4c3d24880d480503415031644440010403580705151500040c1e0545409e6034402c82c40a0101000c43c1d05aa0710080a05050200354825807000b006c02106040010b40c0058140000d00c1c1c82e103010b00122802d40c00702e802c8501c07440c0050160390700c0d05d03010b44040308058181282006020700018003035006585070b40350481489001c002500150790040a4030340c0b100e484020240b481d1102200c1071b0300a1401340f9400300c0303074892000842c07442c2079110841c240a0107c00d0025540c00d01c50340c14200590340300c54090020580345c4c880c0c1030091464400010301c039034031100050586603c0f81542014443c0e003000822070a01c00000310345064070382e89460019000421000d0700c0340c8044200e80ca489000405440a01c0c0010041e02024842e811440601d00721202d01844e4416242041090304180c80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 629661402 1250 629660152 629660197
    0x50607030506121b0a06030e100921020f060f040b0a0b03010b03030a0302030105151c020f04090603050307230717070506032d04110d1403040f06090b 66
    0x2584469007004000304440c0083d42505102132400648455490789004029031036419464491032000040881d818240036a859420945403144070b042c881c000e40c541c950b01010200039038403260385e040240c00c0040e6004000e00d4400290350b0350000d01501071910401c2d000c9100c80e20503402c20340c4611350004013040c5079030b2030142400203400134880302c82c0c2541d00c031100780c1c11039035041c0098a40b0240070b40c1c005840c0d600d044104032a0040005900319075080400035401400e4001120b00d800d0f004005000d65900c0d0a4044281244a298821056246003101c01300c1003040100c010f2003410b000ea040502080c0a120b02c80350b000d65041c52540066201c003204004140c0d034541d8184040c062201641c2c3c400380d413000890f402c0d03402101c0140541c000c100301c41c0d001e03480d1401c0348041d0740034480501d51140707460b6440001080c076000c102440b0b00709242d50241008209400c8a46580824050340d841d039a445c0300e02c0501607a140165008582d152502064900e40d15003a1100410003640b16030343d01d00c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 629662652 1250 629661402 629661407
    0x21203070e0117160e040c050a050a0c02150408010b0406061e0c1a01150f050702211023091207031202030103050d031415040221130c05010c050607 65
    0x201c850140c1440201000700e61400035000c203003441059142845180003a07190b10081c1031800c400e1019220b1841c111404c11000e60040540781c040b420380c01c080e6955282d00c0d1050361090717204100203511003401c440003101469800003078400c82d050740c4024032010300f40c40204420713629075010706030003d01c035501d5030f9841034682d49016080304102d081030b07800120380b91203008004400c104000e111241600041014207421512181d0021062420f00600050260020a548a2400f019220710700603090186402d490801100070705003950216003154940f2144100640614a0084c00d400d4214284014003001015882e01c43c644040280c0300c1c2e0303410b00d50182c041c0d801082c030940130071492103c4d4003498211840150301a50098005000240c006e00d0000d050300c0618500c01c403c83c00001c10300035607080540403a001904111800f6803140c0603000c16070b1180d0711000080341140052000d1040c01501c4c2e940100c41d25000745080c0d07440c01d44500056031882407140c8010099401100000d41075031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 629663902 1250 629662652 629662667
    0x6010518040617060f010b0d021c05090607080c09131805061302150429090a03151104080a0308070216060f02010c020105220c0f0b03041202120307 65
    0x1a4044881419100010301280448010380c008441e00714484007041070314041008030340e134080c00d0102c42d105a5070510300c642d5024011007074003082260700800c0c0c510060740069000301e0003558041d020007403071800301c071b071180c2d200ba0607119000841d91540124001a030044202c0b1260107018042030000d060301403440c0e004000076444131501f198011101000035900744085400f031420b40242c110b010449004210504481404148201900708070070400e040f040320940d030345104400005500c40100310b01701c0e0564071910051a5005907100b4000c0304009401d148080d1159030502c0030414110445541c5403d4402d50164410551001100754002072040324000d60011072841034411f03003c2c49840860f40100d20340c01820200300c0440c004043c1c0d580c248903008041171644002d201504110480c02c900308803409200d0316000c0c69111080c248002c500581d8020118001031017049a80d9003d8210b01d6042074908868001200d0034000e003061001620390480015207204c2c51031030b25400429250035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 629665152 1250 629663902 629663917
    0x804171e071d1f03030207090e071a09240711040203041e0f0c06120b041103011203051204110a0803090a0905060d020d0302010608250b0906070524011409060105 71
    0x140d481101a581814040304400700545c4250010040d15041c000c14109482c11880d0f000e07900d5001e0300381009600342c0740c1401c9011505070085169143d0410000c201c40200520400d014004401289501c074036030b150080162a0164188564120006003000280d200644018150303140f000d0740c103030407083c04040fa00c1c1e280d8800c24502c02039240c196503501c1c5000e499400040801c0e401c14802c02180039601404c007003900116002c0200c0b401405c20b01d229400706000302309822800b2406a41014060011603401101da030403030304464034052a02c06958034000055038000c2c82105400194a1000019120820340060070810614148405040240b81c01000c5580c4000d800d500742d00581c58001c0160411030281d40041805030801191604d00b40c2d00109000c03010000c15148648090f06a11020070b64650a001c2030f50740400c00d0000d42c3d00e0080d4000078016000e4038806480102e04000110a040d8084a003041d290317076258031125004501c60b04207500038045500090940d0710400050001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 629666402 1250 629665152 629665171
    0xf050621010810061509060f170103050a21050a0e130f0f11090f280b0408072c0603100e060603190c0e040804171e071d 53
    0x1000034060925145950a030701c81d1100c0e411420f01e01c2d9046195011301406000e00811222403410a240300401c90105e61140b01c04014200c4202807101f0b1041d462070544580906401c800795031681010394503240101800ca920030b014001b84014000b501070030201ea0040d689035141000b0b03200505607048160740c101590b022081d45c203802980d215502c07647c200841c000200003140c00300c09100d2000c4403141201d1046016090094500b04d503243c11190ba1074080c01c0d659082c141e41303c808800301011009810075482e40520700046252000c1402820458039900c040700c0510780c0ea020700c910907402461032a103201d05100407200191280c0b0300d400d034010302d008d000c4460b042007241c1c549080f245100800701d225040102804010301d0b08103c2c00c0300c0c08400c040461a01039242d0340b90a242d801c14810303d103201040800207414403000f401503400419a0700b42e01072000084421ba075460b11068100c0030b03910b48100790321341d02035900060840182e4a00c04272420815005508100702c4e03031401840c8041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 629667652 1250 629666402 629666437
    0x2c0303040312031e0e0a06020d020f16050d030903172802040306050c0909180a02060304060b120a08270a12020a060804080a03091118011401020303010f0506 69
    0x500d501400b02c0301d04400d0b903000a05940c4000d1000d8046800003a0f0341d80072814505800280341000c034800340c3c03113035101e980117a50307030030004028000e4000d00d120b114110401007043e5800c0d4003e221003c0f0303260312540c00d54201210380c90041d01100d8a40d5409000101056115a405000f8140007500403014014406034001c00c0b003000428041d546c8a2290441c3c1c012804101b0428035014050300800aa00407500703200c0d8260107c1c1c10440002c1c00d1072420501d80c1d14180715440140003800b180754010f070403960b81e450141080700203003210640d42e9001e50907840040c0d99800c03020800d50030443d03201030144d261450354590601c3d1002000d000862078000101100400d43d03c0e00c0915005182d9001c0100340710b000c41c0100001c0b003203103500030014029a0800c20001401d02800c440d41000e05003000114000c01c1e04241541c0e0080c1d990140e0004034a80c0009500245004603a048812040d1103116042844004a89130b000078415404904a518014009454201c000c0c010300c2c0f40f420713030300c09 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 629668902 1250 629667652 629667659
    0x110a1221051306050a020d0801080d03240f14040902030c3109060c1806140913051009090506040f0503160c050102060c090f01030902041808192c030304 67
    0x2603445550f445500450740000383c10480300e4040c8801100b07142d19003005d036400d41c54104e2194480903408900000c16a44820000b010030341c0b991030000660f12418060a09516510310100142690082034010031101c2c1c000074980c40d2078003030011080e034003130045c218801d140b4041c083d404a001c020050b16001504003203144011402490840e400640ca012903d000c00b8104030b800c64072008559030800c19517080c800386c810100803019080383c0c80742c9454800c0d003400304e004000b01d006039499950300103000d041854041d4000e40045028480c00510700304031903030b14411007086079204840100940c2003980090b000c11300403101c4070843c90040068900d8a10b43d00c0184241c200c0c0000d0840304420041009c0c000c030b590401a0f01d40c40301a0354811481c1c43c3c850400600f42c0703250418082c1c1015280c0c024403085407256041904040000d0020710348050140ca070500c074541040c02c0c4184031400c06414600c0151084440b1101e04094142b0b09501d84258411034482c030000380d0386160544010400003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 629670152 1250 629668902 629668927
    0x1505091908010905150702060c030414070f091a01210513055109070801020a0c290c030403270510031512030c02040603110a122105 58
    0x340586481035000c0d10341c010360241700d80b82403000540681d04562100c000c1003241e00d550400c40350015084600034040b20035140c03c0c5460708409070440e40203403103202c500254070552600900c01c0c0f080420081041c0c0081e400044520f410615040e50003004203130810f001c0000190b21058108000082c0c0214000b09920307510b107001c0a10701601200510100c3c201900c00046194010004100c10303c2161a100b903200450a044c0c942400307104009103c001c65009482081084e0003003500b00e000b552990008540545883c04040c015544201d0100e03140c890300c0042c0c001aa40000021428030190700e50980b541003c0c1c2005104506010b07031500c6000c407030a050010404041c102c05c6040718014140403e00401c06441c0011009050a20720503214944551036400166603144883c000c3c00030b00ba041c210751400340504082d400500d041000b00500007400c41c194114201655019400c03980c1d80c110b003c54008441010300320045030302e040c1250800840311400345604901e04281481b0b49803000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 629671402 1250 629670152 629670161
    0x12080c0f09151303050d02030c0d0e0118080d0f020a02063a02030105010905030a02030a060b0a0b030109060609050a080a061802090f010806130b0103020f04110a08060a150509190801 80
    0x103c00740003000201c10810004100f01e280c461060303510196040440f07440701a40e0322016543e0100a2060354803c2d01c1040c1d1184903000d020072901120f1304c050581c0e0b01c2200ba11800380f0401003001032141d90200541a0000440c040c1c130640c00340159140c80780d0b48400b0344501401002c50040d07030340804031500e03003038030b40c0054034009298244e03005131340b075261100145c2102c00c0e47d4802d5001c0d800441460006d0303070303011802c5c0c01c6842d0040b002080785aa841c0010340c654255401844a584001c00082824161988070350107686103038132415441501e900c100903400903130344111041071348800200400164150028803020748075500c0710000c000d642d400604024011540c00310f58101d504010840c40304108140c2c2c1d084007420074004d156181c20b0310342c4c0c0d07907625050101a000fa07400d4090740c02d0a417119404214900c25101c8410703211552030034001c0107540b0a03070b012841a002154049a42d1507520182180d0f905141c80c1c19203801e21160500c01d008041c60308800900c001180d00041c401000e004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 629672652 1250 629671402 629671417
    0x50904050d090f030b0a09143c10110f0f0309060117101d0106030c030c15051b010605040c020d090f0e010e150d0f12080c0f0915 57
    0x25140385101400d0040c0854200d80c40501d0f0044071102c20008a1290f803d03040d00285540c101080401c0542041206403840004c42011071280c0c0a4225605516030881c0030300605110704400c4002305100d0304182c10b0b48007501ca18507504490455240b0941e03640c0704841d101c4940e13a1590a0007503007820001c507a00241c8403206201130000410140d00c4040c000b40780503105005160703080c00c840358a0070ba80c40815500c0c0b001d40c0c40d550341907010074914028101c140c0706400c03002448501d40703a2a0402e08601144000c84010300801400314441c1c60440401e4068003440c3e035141c1c05c1607031100c601c5440c0012078050301400c4d5692140071443c1e0b211800780075203080542d0020548840482d900820840081d80040d01c030039230962003403042c071002c1c0060070304440700311851030b0280d1540d0b507a41060018510f0b080781c1c0301141040c04803c10103848201441c840c024010300114010001082e50409421202280c01210401594600c1c05070308014042c3d03060090301c0c0c500c0c1c0c2d8441c0d4941400c182d0190f03c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 629673902 1250 629672652 629672663
    0x2102010512152106090a0503090609030304090501080a0201020d0314131509031d060f040312110607020a11030c09040803070504080106090e0106062c040e010f15121e0c050904 77
    0x920000c00d02003000800d40210701c5d1300040400510580300d00b41c69005d081d52140c40f4560004600e0341ca940c00b04183c40142505000412003543c4d00c04189940741c04a6030101d000d401f0340b401360140e0358040d200341d100501c0304009c83c40b25a43d61000c1c1c40f000d031240d40b81c120b96500e801070308104454014441c0a107001c0c465103913880e50100d10703140f20210000c91130543e44212020462503804a28104c1645d0480f5070150400151181800c1c3c152070200c0000f0303c0400e203105050400507038644c005011500603008030451940741004000345900c52491003c8160007600c00b602050008454000443d400041303460031509184c1c4960543d802c0d251150721001615881c2c5c011480c52050038440c0c10b0007031805040c01000ca07000241c500c0b05045207401304100d00c0c0841d0b4580d0543d44c44a4000c11142105003000f0040a090f0032510f1004bc003074080392418583c080700002c60328604440c1c04403e017641011114041004480d540551940204130803100d15012200c001001e444200c00c0307d00843c440d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 629675152 1250 629673902 629673949
    0x40c050d1e0312060f03081b0106080a060903080f01210201050c16050f0d050d210501030602031503060108070b0723060a0c0e0d0201030b0f0910210201051215 70
    0x240f075520b042d10300316000501c100c0301d550020000100d0705e2013120081c4004000720120b44500c681118010009a1700058550290340a06801c101c0d1607030143c40441e00c0303510342418603281c61030020b81d0000240a14004018050302c4071540e0a40c040c04284210702c1490024a45408405030900306950003107005414001c00c48144010b283c140c014807040301c0265801014041d03c3d4135032554034900406a00f0030b00005140c0002d54030950b800416010450702018800c55a480c80d20800030b52007107800c030781903000d4030f5070345507c0d0714011503841e048442c8007008144050501c580c03500c89074401d0100b1070700c0035142e0404000f401c801c03603a424a4072450901608062611131b5162064a034a4100d800420041840140196986d01c03500001580c0a180000d40700207030b403002c80c00031429040c00643c09007021341000303004401c601c0c000c0700380d80c0c445803003840e0000501504041d00154050003400b1490a0081d0780040c00104140c0e98440440708600028281c060042085034081c40000e904001d00c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 629676258 1106 629675152 629675177
    0x1403060a060c1b03030819060506030619050a09091502040321020a060615020c01050702060d270f0308070f0f032d02040f0509040c050d1e03 62
    0x48401011030f40c3e140d060161401c2012203002030650307008283c100f6580c0781c0303000f0002101c102500c0c0301d0958507002c0c04c00070000c91a5000740308022002000080702e0355400075040040010303241c001100c1416023400200c3d8042c0828080e60b4030f004000400014560303402540070401e241102c070300300070000d640480c20002d0800024003202d0500c10041043c52201c2109021030046400320350300354015038015241401034020107580b211007488480c2c148034880d0405001e160b40030792410100c042030610fa9000c01e80c4413005480c17007201c402d0070701c0c20940c011421a411111605002c00105406040140010100c80040e400c01d5250000c410089004d90780620304a886030902c5502a56603124030002504180f144151401d845c000010f418103101c00b405003c4c540120310380511500300b505101700044c00c88011a42c4480080d580c921003400c03c2101c4a045120b955240c410004 = true := by decide +kernel

theorem cover : BRFrame.Cov 629496402 629676258 := by
  have h0 := BRFrame.cov_init 629496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 629496402 ≤ n) (h2 : n < 629676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
