-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0122
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:56:55.18249+00:00
-- url     : https://prove2.me/submissions/46d034d5-e507-43ef-92af-b883fe39449a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 21762596 ≤ n < 21942452 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 21763846 1250 21762596 21762599
    0x40207060b0d0302060106090e16030902010207051c06050a09030801090203040203030403020d05060415020405010507030e0301090c03030c120903020d02040b030f030406050403030206010e040203031e12010b04030b150901050118 100
    0x3110380c000c499515011340e01a02003035040c0720b4001c2450006501110ba4600f6110a00000ca070590500107562100c070b081c001000c8900740300503030a124a0b81c1c0080d900c4035401503001e04410f1080b11040040d44180810007160b5a806851000c40c0c12905001e8009985240103101000c40d9900542c1c00900040480b03007401e580741d002403056220401c08031640c2c1c00c803100340000c00440401c42c181812903450190300b0a1708240000b040c50044907000f801b00280749600022a880a51090074001d412a01d020039864807810042c290b00c62145048481e0040320402408151246120405407503009011044664264003044042c10024405961601542c003803a030341c0030380c108005c200802d4980c80c0d550f101c0c1c2c590b08010341041c00582c001c1c2c02a01c118020131006039004030880b01c02c04241e250300c101c2201c03001803054084c0144660011095500c2c00041483d80303032900a00101c0780300b82481d00561ba80c074070225a000900603120798200701041c00500a541c02000740c070406042c42c040d1030f0340d0203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 21765096 1250 21763846 21763849
    0x60b0f130305010f0c08061e0d0212030a050306130504051906150305010c020c0102060f04030c08040b0403030309020909011415060706020f03010e010512030d0b01030b03010c030b03010c0c11040207060b 89
    0x1952681c4180313407065a21111070b103100382c0044880750b01540c2242c51382e100e0155484009030043c00144003901ca140c03d0217107c401c5541e80d00c0091010711200007141c1d1187d80d070301c0000d845940251a4240b2a4420000107c41247c04e0300605118a0740700018042581d102009855800401401202e11541302c250f24270120219445202c0114020000818030b01619070000c0d0030003100b14151411908610100300f4004000c503e034541042d450304c0e0280d192841404d14084038000e903009840094000140003050540c5a0807054917680200c0700b1120b2070300c50f480c005003229015900c4c100c174a0482000a00c4429240030346e0081c03110090086450865150307942c00890341b24000c0c85841220200041c4506150300c2c4640b0f016000c140c8150710026402406140d59004541c01d080398943c071854144401c1e4840d03004014040320140003400355881d00c402c0034016008054046000b50302c2c195001c00518402c441071108582c002900c07074424460790080c48042e5024000c20358071942c980301e40c0c4c4e415 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 21766346 1250 21765096 21765101
    0xf2518090203060f040605010f080303061201090b01140109060504080d0c03030e0a03080411030102042304090c03050a120203130e0a090206030f010807060503040201050316090b0414040e01060b0f13030501 90
    0xc0c0d5413201a441e262401c1d2809070704030381068119040c000101d180c02c0c803107000f0010403641c1050080300c0781021207040148850150032100300040407007001e0f400014000858138030200c0b00b80402d80710100419140c45007140c0600903846a5491917000038a180001402901d50815036800780c03038007040840c820100213207443c1d10417000f10006000c2030108170070301414407600414a9001c500a500c0d292501d104100c4840b000f1a0008001c449140ba00b881541c455000c080b0300d90b0711049001d09a40c0d01d040444e2510041e10301a20082455408502c8442c80441281e44280000d214010018100038450151080c0100040398030390740c40c4400005030f0340f0080918400c0d90001d0b01054150304080c0004d007002401c1c1d100000b800400c0c401e000060780c203d81034030340c821001c0724800348800112000702e425030b00b59440b00e4994000020081680d0080c3c52081011000c260340500c00100301e110f40900301d50140c480c1c0260b510b001d00c82441d121070882d00503c640000c40b10316000e01d07500c031707180c203401c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 21767596 1250 21766346 21766351
    0xe0a080304080a03032a080901020c010f020a0806040507050a0c030302040503100b01180609050f180a0209040b0a080a0b250203040905011d010e09030c0a050f251809020306 76
    0x103540d408036500808065140c086e82c10340e15481c03440071000e4000f4100015011000501003020310001c00b0024020078401d605540c1d842e2403070b80080c0492080c1220740d200031b6100998000000b046140000d1440c10b180c09118002c0c04a60342c0d442c907000f050301007203036200000001101059000c010000d2265410000c07016161103082d0700203170034130a40c0005000c6040310000c0c0700400310f110034100421a007000d0f40078116030b03090f80c02e41c440302d40c0000014810100034441400082441c0d0a029040f0340d158041e0800b01c074142c60404ca801144010400303005a00d00c1403580c2d590040d10150b00084816805941200003000042c81c913000c04c04142c1c6e024050745940d0801a071010501b000100002d029090040c003400c2181070f0700c01c0701095480b2500105000e410030640e05840441c60802c001c0084425020305003050350380d52a46d5243c0141c940321405200f06d0984260310341e019600740207071f08075040c0e8070b8000d180100c0b9500e442c01011100340481c2400c0340c200c1d51118284050f803020b000c00c91 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 21768846 1250 21767596 21767609
    0x405070309050f03120f010b0405040b0f060d0f050702070302030a0f03140d0c080f06030307110a090e0109020a170307061505060301151409030a020f0f0607030816020303070c02010e0a080304 84
    0x50326000107100c01c0c404442e008010701401b1404d02d0041200505200898040d990f080d01c1c0403805000b41408101000d88882280e41c2004000500d0030407030f90a540155010310b0030080c14081601c8070f413000c0360348002a020103540b40d0801e41101c1d001802c2d05c0740042020340710341402031084690340c0b221b9005801550410f0b000d252074004030403210b0750103580c090b4048221940304c3d00302e040810110340da9025000004111040610114481d6500c2c946400c008001ca040b0038001401c4643c2c0603400790241c1c16040740603503800d00c0d0100f04508100810103075028001d000f0f504090301e5031500d4028205900400041e107600507000705240c1c0740e00380210b000e00740e4000c0c0b41e2412480320600820040c410b10030a21104030600c2030410540e00811010990b640448007080d500718200c0000c0c04000003018190362001c40000e6003004c164025011034460200042500304a00c010760040e42c50744012222080003503514650000190302030312984029170406000c440a0382c1d102c90406255070312580001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 21770096 1250 21768846 21768853
    0x61d130612030e0d0803190b03010c02150606030103031e0302070812060306180d110106080106061112030910110706050a05060307090e10020a020a051209151204020405070309050f 79
    0x681415000314002c0c14404051303c0c0010a008191204e18240c000036003004039030a0f035921100b440d9003281d00007081d040c1000380200850242e0200180d65484542001489c4000d02c03000100349140c41003e0707030b0490f50180c40d50f8840040040100519440c815214070a00d40d0900610000c980c406002e01050b0900403800f9019003890420940780c500c004041c02000c664030b2451801c0c034000030507111114440da00f030200824a164030710034058801d0381c101c0d400359840c00000050440c0d1205101c00c94006c4102510130321f4000000252413444100c617419482d030310454100a6520190303010a421549805000b81011502c1d900c11090314019210a52856100c000344202440c0501c0000f00070100c1d4002008403010300e070796040e161148086c0440d80d242d4042881074816009014000180e0350101c1541c25030281d500104c0e540b03070054402e26001d003100b494507024580c51001150943c080f581c100380026070703455080102030680140b8660406441d80c180070009241000750300103118210010303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 21771346 1250 21770096 21770129
    0x60503040c0801021c020d110d02030f0c04060c0209060d020409050706110a0f060e0319080f07030c0206040209040c1206051504090b01030305161401020a020c0307061d1306 76
    0x400e06101280c1041e00c880c4d03c100189500150400f442e800715580703a0102585510001d82040014a0541180303100c0700000a19070720014803c0e8006d500c40c84c044081107502d510f903980c000e442802240a1100031a18030950b0002515140903690b52029000302803000c150400d40c04101030b1640003808540f5940728290a0000d66040300c2d4007a91034407002c0c02880804000d031643d03800f8084481c4c000c1d16a80d40d0b0f2504e80400d510a00840b0b01c4c07408200c06442440c00800c1d0020098102111444403910407500480c02c6c040c03007400341d10007131081c44e070041069440e136400300310203100040c000b1030708039000c3c141c0000c41000c0804100c1c2c129004440014280c600307034000b0400f07000c488080501c5035182c10a0100055610f07070a00b81540c2e0540740030354550800e170006c81c8064844020107400c1e02d4090044080d0740405400170001ca40455003500c1c1d0482924017410740c1c44486001d01c1001c03a031100720f10b203030603c504d000c0091070000060207440b0724403c2c16203800450341c00350048242c04145121 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 21772596 1250 21771346 21771353
    0x192a0306050603060f060d14041a0105010903020d1b0f09021c0509060103030f02030c1009032003180d0b0108010213080304060804061a1f0909110d09020105120106050304 75
    0x5403100801c029101c0e10324525040000440781044403132030f1072080300c0219900c1c0c0f0503012540012002806c003d00b07601e8038101030900311803d4900d000007a55145512001140342e51082d900e020899501405142030710402d680c41880048403120b4520b929000e6020014492044001c0c0030001c02c9444001030750381945500d41800c1140020714811007c0c00c10043c0441c4c1c3e080080d0309811a505490050f12402c0700c408100c0c00d41c800c00030340d1a4184178030320750340c102d2815641c0729010f030510030346445d082d140a4102c0b0075050078a540c0521700070781003442695176504041c5403e80500f407005018100d17034451030750352014840c02a080a021a9408107900e5006000c40500101400701c3d80e00850426190010007040100000d1005104907100d441d69502e04100025141d91f072000145140c501343c141c240541d8515916036004030010310f400b1030000d80c00c9200e204014484141040b1146401c2128006402801c03c064049040041c1040291000a03000740c0701c502816165960036603d04050a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 21773846 1250 21772596 21772601
    0x42c070501050705070603150e0907061101090c03060b0303131805070908060103020d020103060e0f06010f030c08040206210c0306010311090102030319021605030c010c090509192a03 80
    0x2003090341400720421807600810000a5aa81145c54a18000c2030781c2440440c00c0c00322001c0e40e4440741c0c44922050030311990190100c0d682059600c0c5a450305c1d40075600c3c1c55414241d03000c064000d8a0b08070700c098284007040c4a80c00c420211440502203c1c03600da0143e500718089000f80e4800d01ca480100707405e800a04240d4020581c01480c1858a4403005043c19841a298001840003c0c49020780032206011a4000e80018004080400307580c3c980740303008490a0880c1c2030071a01c60b030020b081c1d10b01c034034011802446503080111440e0398001003640e40c2d50900c2400c0e402030340c8607003000050b201700b695601c5842c180188a54480d014468603814644005002c1e540d408601090b000c80c20701601c0d5450741c4c0002a41c0d840503004451552018403001c10300024890200404a03c03225191050f00707104000001b4841c1c001c5550081150310400d660840c0e040300c050040716406001000454a54822002008407882d0305840004190990803880d11284d00c60380010591001c0072220550440d4051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 21775096 1250 21773846 21773849
    0x16080c030c030304060318021003140705030c0a08090309030304080a0311030a080609072003130e01030209010e10080106060e040e011b050c0a060c0801050306070f0f050702042c07 79
    0x580c024040c908809000945034040c03401460201561190302904008004000c0c1d000c182d00900390b18850256440024094800240c1d410181200713180421a0b580c811022240f05030f00404286042c441a64400c9a84031000350208074144401c0c00080f032a96030900c0200020401c500090002080c0c914024145901e13665084070140c00c24007460f0152278101c0800e940c00300e400c680c801403030382d9480340135905007802c0c034460705e9840308803007420f46034080c0000201480001e04121a18a6a449840e101015001d000c0250000d086100400c000c0c40b45012094000d40302081514501c2d0b2114541403c590182c3c0c0120002071569015030820b080c18800e95840e0b9075880000e01ca0002c002000c907a1001000c1800e800300500000c2c1d103001d2100611084c1d042c1588250706212000d003182000b49036100c20b0050912900600001c1030b0f409000300c1c061301c0032201944500040303201c4104103480f56004070fa0309a80098503171250620b9491440000401d4034800c2e03280d6104144102071091420f54503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 21776346 1250 21775096 21775099
    0x906181309030512090a0506010320030109150b0a08060a02040510020607090614070602040803070519120828141302090a050705040503070b09090604060b031506040816080c 76
    0x1400c1e20a40407a60040c03c90304064000c00c10b15410380c45808840d0701e0102c0805003d8154003442002004200300382c055401200310045954001c001d060007003500300d031400742009000c0c13005003050041e81902a042200c4c10b00000f484400425901d085181c1030403422120b6010040d0300040610052030400c4070307660380b0b04c1c40344002d007014a001000641601c505009400a0048028074650300700101c00c111226103900c004155116660b0391070311503603608407480403100b80c0540354080001e00000e100f0301030196000100a0403401110800361035069000d441e19a109210044030a0b1004068044299041d111440060015802400c0702018040a0b00740d0310740c6801c0c004404056500d440351513070804444007001484d6154454241d03214462a07001036010702400f000024446429030203495410026550a407481d65843e04001c02c0b00d1031170252031b0b0104820b001042110230100d0300e000200601600151400d51030380040c5107041740400c0240b419201f114800d0080c08024445508034040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 21777596 1250 21776346 21776351
    0xb0c07020a0e040203010515060901030b03030d020a03060f1a0409180f050604020a05030f030405040e01060302030f030304050d05040b0a030209030111030c040801060806010305060609100506120a1503031202090609061813 97
    0x8c241e4009200d41c071900504074100750701d4070701030b04032954103108542440c84800403c40d583c0223030440240192495114111583c070409100189040303440d00c218100030300f001100d52600c1d003030454410041070340e05912440400742d000040b0014081804071001c1c00d0140008000500e40b80c4100000741d20035810040c007940007009004940b040010594060310021600801c03540314401c41140141220703800654148110220604440d0001c0000d50050380282c090b0346103007810a50540d001d02c1144220280981d080100f203004610941c00382c210b00c00f0040011030840c0425940c040e2540098510305030b0710200046c00c00c09504d01748511381c01042c148014041c0307985103031102500c0d240010410b41c02400c80d1030000d6a01001206c158014220044c21251a6500001e8102e04158100d07107210040f454041e0070700d80b5482641c01d00c4110383e8159034458686400311402c40182d000a409650000400e00115505560f00700140501030650505110146084000c04c03030340e98201c5001d45003030751 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 21778846 1250 21777596 21777631
    0x1020708030a03090807120309031101020702030604020907020f150105040c0801030c0b090a0f090209040501120209040201030c140301140307050a0303050304020d03050c03070f0c0609060c0b0c07020a0e0402030105 94
    0x80d004419070300442000d050001d02c060050801e441d642c0702d0013000500721200031700415101d0f50544e103e0030b50340c1c0c000e60301e03210400d2200f41c03110b00701c2c41180d4020350316034805400a0014500b0742c20312940158144180c406c8100425410b91802e0a4845186505800b0800501450030940308101203c02c852410305165403454854a04206285c00f6001c0f900800241e6004151900200b40300207250b03102c0e038000b2096513450060025000036800720300c146d04100c000101865103200c09582680c000300304051607220381e13005400520390403c24905001d0000a140086821140514001c0180d042440c21021400301010300300501c41d000307544100d881c4401440401e500c1019281d0040c0d050f0f8a004d403100c0ba5040582d8140520469400140300014501041010000c0901c1803e44a2424a040d1548a00f0203075001103080c060000011541c860040210b1300c0303442c00b248c1008a4003602840c0101c0d030380114102c00140e81207440c025140034140021401c0c244100340d071040c2d01c00d030b8040c20075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 21780096 1250 21778846 21778859
    0x6071a09030f09060a050f030703051b070b0a05070e03070806010e090304060507030f030b040501030602130b0c0d0c020d0515040b070e0d0204091502030a06030c0e040f0b0405030403020a09020d0b010207 89
    0x3e004070980c0502800c0c0209040ca501401802184d00481c102002d43c1d4036403400400080c003400d4115150381c202185207401118103060320041d540ea07180c2c000004291695020b510704000c1100400a1081010545200603da1800d005000217850458040d200560622846d050b0b8960003a10648144e40100410400640c0c0441902c4140782e02d8509903820041c0c1601c04c80250680b590707031030340c0940b4010000013041031036402401c40354135510000c480b20341d48029020007405110140c0255030003d058420748540b046801c0d11076a4070041c01c180d041e0030561641031800700103111104843c421041031105024010308101d902c04034911b031510a1100c000d01160001c001564002c0c02070341c44034901401c11000d21082c0c403c2e91000d42d0700b12b4480c64900e1454019003840d00c01070340d00d40c2c00803d01140d2a142807510303078030554003c1c2d011f89202035960b5810500c0c400c01001030301c15010500003c801a070301e0003004002006000005a1180d080000c08030840e005400581c2c1958003032041049403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 21781346 1250 21780096 21780127
    0xb030706020d1107080601060c03030c030507090512240f010f05010c03050a20070f08010902060702060c07120515060d05060a0203060102070503011b080c04240e06071a0903 76
    0x41d0b1400d864000085041203000a01c3c002040d0070a141c01d0140c0800401c181e50b08c8008590100d009907410322044501090550031514180c81250009400d41c90034003c600b0160850075030341c42144210b401c5c0460342e001040007a0380404010350050050014400704241f5900c1041c05042c0c0c400d4404201854100044d140c2644038800905020006caa100c440b03e006a680c034142e41e03c800d500c001031809202003241c40c0c1c41d1074014041001c8a028010079100014070841e103090b503011b01800e00e88940c40d020404540c01000c2410420f1050002c08607030b881510020403e020b110310018901c4c00030f8101880b164550080c4040d0285030003007041000b040b400114203403c2040410f00503900e8440100407420320401d41c100a8040d0b091804100c0400c9030701d401d80005001d9030703582900c0c035260410b00e03c1a91080748104841c1888484110780d10703607070f50200c4800003a100d04000550000d1f0780003141c40c0350840344e0103407450200400005201442054519400049a0301444c40c00990f4100c2012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 21782596 1250 21781346 21781363
    0x7030e03480d0206070e06030112060204050303130906060f0807030902011412010801060b0a090626090f070b13090e0a0803040c090b0301020a0e01080601030f0204060c0302010b03070602 82
    0x12000814840d00080388240d21082460540c210a500c0451a40e07601940e03201051001440140304d0800000c8119100701c3d059032000320f00500003442e59207007510101404a450070709032001030b42040001026641000144094242502000e0b9158500500181103a40c2c5611427814442408003401009602807001075100d9820708001031200840d00040340c2421006101000e8104c002540303108210010340201d048905410003031002d10b884882c038081038010b501c000750120f00080001c0c40880d000d03145806a0b400038402c0980b891a902d085002003240035583c40c038050304941d5600f200c490091044002034012694000d14004060305031109050300c52094650180d03541c41d04200301d80013400a00001508000380c0b0b6105d0502c0d00380104042021b02c640c910f42840c01810810703504040c02038403940101e948414010b41c5c0c040006407400c0000410140c10540d4680181112156610141003e070003e50303510340d500066440d0290869a000d40a580300340d005c1d440030406507078000b6a840c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 21783846 1250 21782596 21782647
    0x1151e05030c0d0f0c0c02030601080a020604030b071701030809100f080a11070b070509010f08070c030807030213030507150302040b040504180605090a110405040308010e090f03030405030307030e03 87
    0x5a03118030040044000304000e413071000c0050300708550340e20343da98409403810b0094001c8040d61100e03640c3d20001c9556100c115070003074201900f1f12040000c51200200c09511200608010700401c003030507603481c1844000d810403170b150307400031422002c1420019050610312015040514100e80c007036034050f103000402081031141030703181c1410030040f0455505884180e0f5014620702c000d800c21a40113080390b04951152030000e0311014200c44080e2040b44003500504068881324100d140c291400c83d440da60083c808001e05400308480609010100c0e0000010b60040c4003820030395040005c005091141102e400080500511082c072424072454119021108100c800060400d5442c41000009030304841c0034081900d81401c1081401e400300340c0c0c0744910700c102542c0040803501800c11045900644018000403041c400502c022036440040ca900546800700300c0317500e0700c10304403900d00d190700c01c9500310390703e4101000384503100c0d4040c0a10342d01d030300c01035000d1070404e12040400540306040c5154032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 21785096 1250 21783846 21783871
    0x18140901031506050415140a030f0b040f0b1003050c0109060e06030439120515100b0403060b0a050f030307030813060204030818060405030a02010c060f0501151e0503 73
    0x7448500e2182d2140004103005003040c021b01c1000c09440c5030045640c8501000303054040c02e1200c2c50b140038460700050700d600c2503011041c0401034440e143d5400c00280b00300c404100345048940440c042010040c807414860a00c403070701505501e001410720100040131411300c0504042844109e402c03410507182500d06440d160307100d50300d40c102240a0841c0d0138021000d5030104030003011010aa03030190790300b4140d600d10003480d581d541041c003040040e0440c2c040d041e5040b420201c0200320300544040e40240864100ca0644c540700c0d98100c24a500581c03040310129541d44108105080c031400c03803402404101e5220340d2403140030010035103e00c02c5100c001d04000d07060000a07280070300000c114001c15000102152581c2d16490031284590203526050118020b0340c646000314503140d8102c0c1d080d9107019000c0d045280140e401905d0701c1c1c0b03004508035003d42d214007484d038800c031700341c802e660003081e208071501829030400c000a01400084281c640c9501000e014003400030f0740210803242c1100d45001034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 21786346 1250 21785096 21785123
    0x611070e04060f05090a0308090712140a02130902090105030d020303010b0f07120801031e02060901030e0c040504030e090c040f060f050d050a021e130306050c0c0703031814090103 79
    0x88004020250f0303a080c0c200c0c0b9080c14000c01d4900065142e541d44d100343c90380045500d550443c0d81d074485031407040100c10396902c15100d00041034010031140d40c81282084a907003212a500054820240c60760b0a118160303944c980d981985003002d00140108000d901a2003081c4003200025141c1c0f00500503113241c0c000004401191040c000e00300c43d8059007000e8102c075261103c01c0c0c000c1c1136034000e1205851054202d00d444540142c0204204815a80244203910300380000c00190040c0a89104007501c1d402030a003031204689440c0a040d110740d200f66210408070004004110f80001c000d0002540004280400d228100b214040d180030745106081c1101e074055408400c546500c03507980d11210050404040c412004115000b62182c140045c8180030000041c40f08151a409100b400940c00c464a450800c00301d001d590100790800340345030300e4601c0c01100604942c40c00c140381d0f00480008032001a1000f01c11143c0b441c2c140540604003107450803080c011300107082c8080602000c0c12a03c2100ba2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 21787596 1250 21786346 21786353
    0x5040b1602120c0610140315070207031e0303200403020409020604030807060b010f0201020f09060706020708030903040518090c090c1c050103020a05010203040602030d0e030915030703060611070e04 87
    0x21101400320b41e4941070703620300e4440c01c00c90f00c1d00e0082c0e924101e400b40310a80801c0140300031407261070603078002d001081d007614400a07031554401d003e00840d084d40900040400131030050982200c6605101e2200c00c0c2d811a64500241190081d60311140301c5d500d0a018049514410b1086400720781c2c04071000b160f00c215600008110340f0642d407000781030740d2001590780d0421620790890003501c1000d8803100c5130681510f400360300743c0c451100498881101006804124075010001d0101c2d280241c100600340308241c0e6640140c0d07801a10420b001e44c0c40032404001a18140039510040f4244005021140c1403240c5801d640b00b8824503003e110380c000b00300240c1c86101c00400d448034107070b00c01c40704a0507880c03264154008250030f020a074016282c001010802e54000800c0f54120b6490354001d524144040c0807030030003816003541210b030a000c10032a100c030304c1e52100307400e901d0a000c00280c41e680782030842010b0b04680107a4404400e01444030b00e4181e9124010a00d0411141c0d0840b030b0074007a41c1c4524 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 21788846 1250 21787596 21787603
    0x9030b04080f070302100b03070513020c030714030309070506070b0604050712060f030b16021e1009030302040501110703051b040212010f05100e0303071101030212040605091005040b1602 82
    0xc070b02000b40b940104420702403590000d154200507503003050400000b0f6070a41410b07152030751802031a421410071203a60410b400c03e64024051021042c017664104112550b414114079030118080007103520200a101211000b400580010103049800b03524046866550031070600000300300a04c142d650b60005000e240c007902e0214200c3d00c000008004e015165000001e40121601040d500c605d00c000001c0c07541d080e08004803a40c5202a00144182182c40d0102c003584090b091803580315003c0c0784040100e12541d801641542880fa440240e180e50400d00010f0801c41041c40301c07030240d4002001000404e1000c039548141d040c0754050b030b845c400c0481d00420f01900c101c03000d910301080804000101079968480315016104c0459082d2002d0b582c00008039150011950041da154008211020000d00315946918a803041818003504041030040c4002c2088021202075940302d44540c20011400014808900058039203030042100742819100d445026a0041c09240510b62618840801d64000c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 21790096 1250 21788846 21788857
    0x10f020c04060e1603020f180102070801020d06150203090f06090a050904060b01020c06030717060d0515070906050c06010e04020414040f0302010b01080c09040504060e0307080c0c0d0309030b0408 86
    0x7610901c003042d500e10000e41e08100480790300e080461001084059513100f80221808072071000c44150a01c13103d41680000349094000f40d41c1544149840020401000c0c000f078003011f22244070000d14240f40c010704190003034440e02c4140440d0000c008410342c0c0e540711010028104015100745440e04000c0020079a0a2455001541d000051804200410481d6000444c5490003a425a14003d42c560300b03201c12404141d840401142c0b041c0e22540301c80310701d951010750040c3e00625242000f800c0c2c0d15421706041500c16810304400e0032004102c865900f0003542001009503140c540c0c54036116909290b15801c041c01420741e07400780300011405650700c94000e513840a0b012880014941040e1a26032040c00800340201c0c050b5003403038032054440d80105440b40c8500f900c41c05c1c2614081050701000020b110081040754180da55514260080c00200080c110081c8907800d59030752007204c4c420b4949000c61183d03501d44078044442c0b10400290307100440e141113a5028084007107503207071858500038a0003503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 21791346 1250 21790096 21790099
    0x40501080105013e0a0b0901060b0f040b0306030c060a0f0f11030f070c030602032701142d07090314060105060f0d020702060a08060405060301090803061e090c0a1106090a02010f020c 80
    0x1c80d5844414068805851070007409144020020b09c7d5403071910b151640a07501c03195080c1e01041c00100030104400008641c072482c005c0c01c0c0d59281503888000381c00d9810001c0c0c0b00c0c00043d002d2100406254221780c64050008407400c090310651424250b0706c2da64460a500300c2800f44003c01d12034100400760913404081e41d48024299200d00d0800500ba5440c44100c180d902ca6244288403030504407070612034100381c1407440c501c10b80e00ba510804d400504051200b02c0e035101500141000e80140140b42c60107004280d00e07980c90740303514694240380c5803070244281e96103696007084c00100010307134656040714851049180c0c10f5885448000984009010b180e0000e5082040000e03203017041c6510070900c510580080303404000c143c039084285400c8540303000006007840703000c10110b010ba2800780d40c6c4030880012241e05101003042c1d07a011034241c20b42030b2540c8022110102d10f003010340c0d4020b035041c1c1003120701500074401d6150003645640e652401d60303c080e05200420540318400340c824010840030000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 21792596 1250 21791346 21791353
    0xe1b0f01020f070b030708010b07050c0f011101050408040602010e0303060d0b040f05011404020a080604050601051509030718050708040f0201080c120403020a05070603020a050306060c03070512040501080105013e 93
    0x907149809001c41e8000c442e064005411f1400210380a6240000d50742e0306600f090003451011b02400610a85101008506040c450480d103070008400c030900450388528814640562a546401006400d49030003c2030805aa0414010802c0c6038540102d1001519001182c0c2d00194566080203184405d5404015202c0d500705080f817629210049070450103544281d4030140c429642c0d5007219141d01c8141d8000b0b01541080b001007059242000f00d811301e6402d2131041b10300d03208810000a250069540c440240f00b812070071340444c0000d8a2042c03651086903410714540c41c7c6020f42d42d0130b600310041c076402810f22510720007080341000140c0a036110703015640401a0a401e141c28040c1d40c4258559080b00d240c0704901005c51218030038001d841400002e41c503a542580c17034030020400c1c283c1040200d48040c0c4410f02c8107d010030300c200714030104065540040c40d40e80741490001051400144c02c20f42c14003600c800300009a80c1c500c05d042904480f107040e0030440030080c05d09121680500d51058a0380e20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 21793846 1250 21792596 21792599
    0x60f09010801060f09060303050d0b130204090603061d030706050702070302042c070f0306090f0605041407050405010501050a030b0f03061008010f05040201090b070303180b06040e1b0f01020f07 85
    0x101c158400b6090f2580070b194910b107169503080300c00544005000c0100028010f028507085a522904181d10540c5c0080008850348149000d020481e0041c2d03102400e020307160042001070150510a60115003140000101d11050407280c2a540c0c0c46180c20013828140c2d0f6000092882e4400c1c003043c0040c680c014030a004401c10707103401003070324001c0c5141720301503409a4070b00e002c10020014610f421290383c0c0440d00070080c5580c03503a1009220360901030f21040482c0c90f01a0000f040c40c80783c0e1740f01d00c3c4548041c01d0010b05400c4d50768580480f0780c1156000c0d5142400501580e078026060f01e542d083d1510340860682591008120200703c4001002e80511407102030003052402400d000c410386182900800459803260444c03001d8a00507035000c0d01042c4562802d001e443c00140090009500070f0030046481c10303030784002c0400840c121405403455840c50f000e06c40c03d80341034007803901e016100900415005403d0402d00e0259000016941d00c41c0205c4800d50307443ea4000e120182094001d40300b030740c0045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 21795096 1250 21793846 21793859
    0x1050405130905070311120c01080601050f04031b15050c070509090102090d0501051608011a0304051608010207030824040218060d0902030d020609120f22060f05071703060f0901 78
    0x390001200034410700c487c03260026070780701c0024003490302d440581d03801416458102c01500c1507403090b045100042c00400022010462200e00002424920aa00e00c211032600d0302c00d806e01400310328036400704081048810303403051000038401c00f41e840488030360f8142c1c2c42d008515802030cc901c8807a0f41e005030203c80003400344003041d40100c0c804d003004500400c0716261881d044407040c42c24080c00307506035461541da1101c00c181c240903503845131040703040b80d00c8410070351104076003041d007503003c2c0d08681c2d000100d000030140c3c02040b15400000c040010b840a2000ca102003c1c0d9181800600c2c1c0155404203480040101c0c01e14400d113900001350000b81d507542840c01d044040c4c00c816200303a00910130309510505051000030300b1446544203001600b8024080300f5002150791052041c08081f8001340709092041d00056200311702c040306420551402c0e45865400740c94001d5004a4000380302051084601003903c410f11400b4540101644503625581e0b80005a0000501039640c1c0e00010802c0000c00d81d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 21796346 1250 21795096 21795113
    0x609210c15040b0112020d080703050408060103111f120902190608060a15050f1e0a0c0308070206070203040306020304020d0b0903070b060301020f0d0902030a060f02090f04020702010504051309050703 88
    0x203074051801c041d95a1307280c000401d603003071417903800039044072201820a0124000002902456100c0c0c034206103450350300c0515500d009001e81080e9800e0040141f48859840c2c1f0310802c0c1102150f107280e1810348002030401824103901015181071154030703001040110340c2e4058071380c1c1c101242185001030721611b650000b8003040b400c60745540034107840b10021900f600781607d038295104599840503d8262400d002c0b4000f90407180d031900120a01d0700c505000b0501000181c840300e000c5583c0c2c0406600e20f810004c044001c041c0c8030b0801d541001c0300f801640c40d80442101c0a882d08100b0140e641e03141c0e4408101020111a0040c004aa2003c107004607407502000a0a0040c01030301c154036940c944004140c00c074881d40d00580d50940040142400c1e040080e04100c400c035000405031550f032616500da460982d0030001008100da07a0000e0441d0540c545100c92040c2c5d024169001c6040c000281e0004e4810701c92409154891032819013650b0645000d5000740725500d07482025509059901e1610303401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 21797596 1250 21796346 21796351
    0xc01030b040e0a03140906070b04031e0f0c030207080d020102040f0e01050d0f050f0a0b01091103090607050c12070c0e010b031014010309020d1a010501020609210c15 73
    0x1906044146845140030b0003100240c90610001c0d1242c0e04280da000d844001c50640e4001c900e55003803100454a60b5410007a01843e40150700c120450b00e014500240700d0801030341c0540044424420241c0082d5000c00102c4002c0d40f41d0825110700b1800d414168a4500340e070788888814800c0c0d0b402981b100fa410740250080f2100c44880c84c1805450f0308890010800174028190021200466000494803c01000c4c21080c0500c00780c2d020003402d005e9540c10802104400da840c4c078140d00041050180f07074410070f07821840c04181c0038110304041c400e00307459490180102003000008a14880c149005000d0a003581e41e000100d9030b43c94180e4a4803d4100b07206202320201202e801c800041d2012011041b01e10854414565607c0a4149800f102514080164550400da69030030301e031340147c5410310f007812103502480318011100e5902400c0d80c8400320580040f41150081c0092081c15031000980c48820b200800405103005003c00c4640d410303004140468469100f00b52001c2900d002003003a850 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 21798846 1250 21797596 21797599
    0x2031905130605071409150c03070f0b0603070e0606030a06051008010e01050a05060d05040503040b0d050a0c11030a0c031403070f0807020d02070e04060b0607050f0c0409020a0e090a060c020c 84
    0x5981d4410409503400031781100703000c2c1034100400c00c01c4143d14041c0c014140c0080403d007407a042000009109140d608030000071216890303940c0d808000e1203241d400296010303800310024403d040c20030106030302283d0003812142c05890088049180800b103030f0002e10203402c018001c140b154464000c02040e0003000c3c8030b000c000c42a060000305a90600d0202c0d1803e80f000544494585045101080000c1c0001803041d035031130006100115190060b41c00070117014610020215032400c001e041c200440e140040104140681a0640008500044162480d40c0b20604000120449500b415110016015646140314034004200220903400c00f60040000c00161395072242c5503982e903000d030307030f03a244e000808405a4000601000002084240a03900c40e208820200d42000c641c40403c00a400405003102d8541140040703000003002000201d55140c03045400303001000359900070586603007103409684900c1c0c4400d00020300481c4100200840d440e40075000300000e80324038100135101c40264080b40d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 21800096 1250 21798846 21798851
    0xe010516050f041d0f06040b06040b070c15120605040b0a0513020904021201080115030203120f070c030503030106140415030507021f0b120115050609030f06010306060e09150a020319051306 83
    0x2d041b03030503d1701c561841c1c010f000d0300c0545858101159688141c2005104640c9801681008100040c4a001404403804039440311075500c905009284c0a66000790041c60085151800100340750f44d43c2c10303a0501301c4e04240c1d074040180c003250301204040c0c41140840e40d0414000141c240341008100d10b95812580988000c1240240da103c1581001c0030f507200c080d51582c402d81210b101c0204e5100101003521261041e640350540d9643c030600014504d5105a1b55604040010402e16410401c03010000c003030f0102052400342005584115035608507500003c041c0c1e01d0f400521118001c05c00121024564020a03c48400140b4290040c1109070a207034000c01c21004503031a03e4105008088042d0301409d0444002d509141c2480907940000e603e559052182d9046042083c0d801c1c80b503640030310b01400f40440c140f0b040038406500b0140183c1100301c9035004021492209652040c21a08003000201c05a41c0e6205d00280c41c84200c20380001902c1ca0b864542440080c0c0d401210400841c0c0c800c440c203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 21801346 1250 21800096 21800101
    0x60c060c0c0201171e0c0309010e060c0d051302091315020a0c14070b0a09060f0509031005060a0504020c03030f060303070f12021606030b040e010516050f041d0f 71
    0x22035030754064480c024042520840341403850644070b500f40313501918240c42c140b02c0c1055145070a85c81001a00c40003980b010000512440c2102030161441e19510507000300700500f01561100c205208406942c8005a07540020491010b001428040000d80042c4280a2410042c01140c0c14003452582100c650300000712803221100780d402500c0f08002507448817001c0404503201d00340d00c01a034aa00c8251b03400307501d001080b82142400a4a121400d66484500071814850090104070340707594032805000051048100d60b980c0020400c010650904000c40c41c0c0d01c1d0741c400700ea40080d00e5003000380d1041c00440d1014032004000040d502c0f41a110301030a03000e85488081c10307100c2c49107010203481c0d0403400e04664041039000164080c600c0a238811220100ca0502610002d44140c0c2c1040c0002030b2070380010800c52500c0c0c09024907a80c8660000c000d2030801d0000b1002126040002c001403100114641c0c4c1c0759082041501c00030604400c0c50000c0401c06815100c42800441e003141c0305207a903001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 21802596 1250 21801346 21801371
    0xe0a09140703061202040509190302070e0106051306200106081b0f0906060a17152106011203050409050f22030504170a060c0806040e1203060f0d050601060c06 70
    0x107000304440c3c14204240100d44c241d0284009001d00801c11513081c40340000c81c24031022034415a1405a001e9805001c14600707007415000761007410b1b40075804018041c41005440740104200108550b0036081007064001c0000d075a107600031844841c14825464140001781404001c81c1014041e030f03850710050b00a0142104001d612040c100610342c02c051000002401c03800c01e503000b03041c241054140445140c05055124206c0380c000c0703841400030f401c0d0040b00f0009003400081d81c1c0c242040c2c904000c6030480301e403120964900c4144500c01480c100c4000010034140110115405450300d45801d00141ca4030410910440005407804401101c4210400d2140300401d0041941343c0c0c0c0c541d40c1c8501d404d280c0150041d0000306003680c03d10500551a205000071708500c20042c1100c010340351041140707400070800089450704603a40400350001061200103404010890340c2c03100080311a412001030b5003000c100c0c0c0e5181c402c40100359200700c20000c05d246401544803c0114820082440031540e48030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 21803846 1250 21802596 21802601
    0x9010312030609020f0d051f1d0108010212060405060a0b0315030c03030403080a0503190509060f0606040302090103020607061d0109020a1202060d0f020903010207061a030109080a08070e0a09140703 87
    0x10501517210781030040c0d4032074103c184c22894011030740c0700c40220344108800039a0094841d6510003c40d1a41a11040e1100041c3ca402d40340101703070b0b500013182054040b005016103010010311591003180d43d05d00260560380d4407074200002e0004103141c10303101d00e4646699202d0703040c20342400707102c2d104a501c1d40c482c0d49000000c480c19a41e000e003a45040c07111501003900c0301d410103040c01320b40d008401c000603042e000d50700c00c0390b00c5216400000d00003401e01500d284280e040c060400d9004480800003400941c96113103445044030790564075296034002c00d00740040144002100201e00500c808140342140b0b50541141b19024021140580c045540b100090400044190300035042401032190051a00d4540c2c84901d18a00c01c500c050310302010b41e4006422070307108101c2160031316a00c105450002e0b010003800340c1c625400b54020814880030380c581c100540100203001007000414000550300a02c60440300000b484050300d00c414140c0c903054280d000d0800c0803590a1516245800030329580d21a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 21805096 1250 21803846 21803857
    0x100b0a0b13031209050409060504060b0108160c05030c07150909091502072a140303030106092c0c03011701060b0301060f0504180504020901080f030f0c0c0901031203060902 76
    0x40d140702414515036a00041c56002c0551405000300c000000880342c8980c02121603081c41031200040626046c94050115041d0f50101c904200c040c804108100d1000500f9040041a5013072611440b41d80d0300d80130f8074500c03450000c0c842502900c0400954155480308002d94890030361208090f080e122141c20048443e6400c001c0e1610741c000d0344002489010798000c00c04030780281c0724040100505030380102052054810800031088400e41005000e0388211104218003048020354595494000010542600d60060fa40c03921101115102d0f0300c02a900c01c18031402c5d590021540700d143c841034401d11034001f4802d440044244505024807600d040c4115401d450309002031504690a1440481b0039442450040b01800010400402c04155900f04d00d00201c40030003001c590703840c191062006a00301a40030320400e034401062102c0a101c0130003901c400b22510304105071aa01ca5503a1246045801c0044681258035a00040b05104188002c041031004036202809041c1d903503c42a41288210f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 21806346 1250 21805096 21805117
    0x602040503100e0a02040c020c03120a0f0e030a060b06070b09060403030507020a050d0f0311030109020c070f140906040605060a0e040506010903080909040611030a0c02070b0f071b08100b0a0b 84
    0x54084e6001460a41c0c0b06680a64070343c4100c0b201c8400304000302c0d14140c1040c50641c2503c4020074410246584560004451402403034000007004510340441d0382c0e14207845e40102015110044a4125151a41501c40e0b0030b4004001c402c0301d041c21010262580c0c41603600f07400103818900050b4000e03000055080e1100c2c4d10400030302c0f820b0300c10003045030b445040c0082d040030151108490034100d8424005103002c0c040d01500180d850103292007162801d002907028400300c40c14048104141c0060032080e400c0e1140584100049a450342c00080060546400003036000d0008688004596400b10440013616001c0d901088070b038070781b80b00540d0640010311004140c3d60b02004454058200510815042403240f80041a09100020b000c40c01c3e0700300b11007230b20f01286d5a103903c1d40c40f50307410030010006004151000c1d2078007000c0580119076201d00c1d00050000d8040f00d0401c07046030046103186000b03020702400d4449140213001d108005d0800444894441c00c01c4c0500400e01912180484102c03181 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 21807596 1250 21806346 21806353
    0x109061b02010e01020322081006151101090b0702060601030509060c0706020c030403020a0308070c0b09010c110a0b03010f030606081b0d1e0305030a0e0a0c05060c070308070602040503100e 83
    0x105030307004540c210415681d040c1180002d02c01c0080645104080710700f2020721540c20f040203401c10003081c3c0380000c13200e0f40f6910365080c210100400307484200311000c2c411052410b01c009600310380b41d050140070391f05002003400c2c00a1081104c02580480d04074021380090740c0c28080c9803191030803143d5035a400d644a0310b1044e010090540020b40950041c10050b028200b036a09059a940020b14031850540c0140c8030708a000032294100701c0ea10420ba0090200280c180d070414460b400000c0403010040002800c0b400001c8091490b42d64480b5488010045010069030740c0d82c5491080c004034a0922007102c001d03003001c001186414001c5015000c00003140300040e1a00c018070100145401d0f4510207851a0b00482e01590041c03140000c0c80c1c005038065245c10b035507030920741101002c07505030020a8031560040b03115400040d0030840d130003048032b02c04c680c1681c441002e40302141c100b0035190f0005003100350000b4800d04100040d00908200c56044090304c0e0b0082004181c00c066a50281030403a441c0c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 21808846 1250 21807596 21807647
    0x3020603010b1e0307020c01080c031e041b06020106050f030f060c031906060807080a0c020607140c070801060306050f070c1b05030607080405070803070201020703060b010c05030a0806010906 84
    0x142c2d008040c0c0701d140450b40c54414807041c4030074111455803040e02d040f0016000440340c0585540c0202c4490340201201c26603518601c1c0001301c01c2140031800500d0090a440c1c600400c003804410415002100e10506070b070000160303541c034003038000c1a482c49068081c0ea9480c030202c0280c036000c02c4295194841c0d0018003115642c000078441075a00003040c0405a50494640240c60417062140c8070150080da101c04140f4148410081c200b844001c241800050030b1105007203080d6404242150050350300c1c1403c041017248103200c2c040354068920703c00420f103d806400100d028054000d07608503402108108483c0e02c50f912000c1e0513040c222150408201e0800f10709000403d01420310036540c02c401c154503e05130316080020b040c1501507515400203a20fa10901c070501c0310a1195100402541004500c1d080303240d40040d40f10b05492002402290740c480380310320300b640210704000160741d1000c196030303540c0141c0b44040e100410a80e8083d0000e02c94190104250740521814088460031825858580 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 21810096 1250 21808846 21808859
    0x905031203060f0103090804080102120a0e0a020f0102250510020102090d080d0906020a0c02040e010b030d1107080604080a020d0c080f030a060b031003050c0405070801061803050d0e0306100302060301 88
    0x1007282e8601d0030f0406642c0d001b00c50110b40913001030400781501000142c2c0c0d4400c030b542072003200380000d81070f50714003450f000610007607510000e13040e04007a5041d206172000000b85c0340141d0804a0a00c909900750004c14108004401c0b480301c2d51065400880d0009061014074000720300b00d0040081080e0820000d0f00840d0110700c00102400c7c81c82c02400010035030301440d40e12902a60444410721001c94880c0306103000318905030050700c040c041d0390b00c020004800d800000994860300105242c080c041c40c2501d500b075403481032100d00e0207401c81500315425410a8074000c4144d6200400550040c050445040551842003030349904983e00502880e080941d2070003110160ba00240035009581c1d42c6d141300142070ba4000c0003840c0b01c1d0802a014106407803440c00e110f814020795a00d01c0d4800d91401040000542d0428482415615180751412654940c440042000002e68001030f0803031181b40d050280c000e510074a620115401a4141c65140e111100d03a480250600d010080d44144140014000f8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 21811346 1250 21810096 21810109
    0x10605010f082d1914071202040b030114030d0201051603020c0c130609060503060c030109090f050604120f0804050703060509120c0609070e090d030903030e1005040201090503120306 80
    0x8048900f0035001c1a446850044101d4601e808041148810004008022808464865906000b1041442502250b110280c291071006041000384248410307525200c55203036046e100a4201c1020141d60303542c45840030000c2c4811009514401d01c06c605800392094418021140110b003007865480c4007003c40c0c0003c1e00650000c0185030b5180c4203012526601e60707921580010650001d2100144190900403820199903003500100e0080c1c1c4001c05000d24074482604684c11101da88400041c0c1c032515140600c51942c0a0502401c01d100e07080a2206000e24800e80c1805000c003901d070308075116070310340c001d66060704110340182507500304c03280820216450360845980b01c003c040030380d0000e425064100e00300fa00400302d030340c0555203c4170800885030010810800580400881441d40c1d00e0140401542c44000649044c1050349520030380b4101030090308510242100c120075107090341d2103010004000d06d803c48003a40041c1181c140040c40c0c0c200810f00d09550881940d04910356a104e2003802517 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 21812596 1250 21811346 21811351
    0x5060d0b01090c031b0e01030f0204050109050f03010e2505010905010804060b0f030f01020c01060803040305030f0f090402070b090606060c150c04030203010213090c0e01080402040c0c060f1d010605010f08 90
    0x241038032100d140f0f041d14620885c4181e62040d82d11100c0440f0151000102110444550907000c184100805c0c05140e8214aa031000c540c81200c090407144500004240135215002c010003080c8200d16002950320345020b9450017100100711620750701c40c0d9a100440344034007a88180c6000c1092480440d003c40c2650b00b150314840380152488004482c0c0d072002c60b1401d003681c03071042c416950105581c4610312003030043e0002051100b0041d41040c1c21610780c00c2c1c417441180410080350600140300b891080c1d612060300c0110f03c0051046450301c0c440c0c280b1a50000045400c405a0f000b45c40018210f40f400c14182c440710f06603100107020058403c152036000260241407008030300300500c00000140c0d03090000b80321f941214443c02a46030320381103151049c0c40000c4411000e10005c1d110b4004581da008401d2940160100c1c1c004c0307258a05910192080d02ca80a405008541011103c2490541d03030380014404030301071306a150440c072030700c000b4508850140c02903c1c0003032010001004000d100303541c1d0340d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 21813846 1250 21812596 21812621
    0x111031b16080418050a0605060405060c0c19031208040305091207080a03030e060f010302130222081f02040503070501030209030f030c01060f05040504050d050310030c0b03040605060d0b0109 84
    0x1c0e500c1c01d55460348149504298018444441c0f410144000c001c1d0501805402401000c001d10000d03080000040050040b030003402e000e81c1010401d07002c090000c000d1aa030142c00507100a1042458416900503010302c5e01003698164100054075801a101310511441940c00d5941c0f1420318104400b00329a00d01e030544820f5140c070840340041444c1d9400d01041004521076140042c40f00008850305042c0800202031044860310782004001607103d4110080440c8004180107030307640c103d4071454004285c6126441c02c0712100c1a40482d151074001540700283d140440d03040d00310000300100341c040c1d10940c012030350990401d9400300100e5010703030090460401c2c0142580c0d00310003c1034800b451908036030000a850381d11a00b0030406484070310990006004243c03420f0200d032a29450b03440d90380010811000c10071000000180b8240100c0c41c007030029641c4042d150947c0c9e541d031120302d9065001510142e610b02e2900000c10780a24200d480c00080c1a48400800e5080c0e20304501180100314824194 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 21815096 1250 21813846 21813877
    0x10302040e0a0603050607050a0813061d010c031113030b042307030c15021903140711090105010203070b01030b070e04020301150809010509120702180c0c0111031b 72
    0x200e4440910030066100d01c210b035100140807441d60401da8502034001e8407400602c0b40070000301040c56403060586074001c441801e80b1054002500c0c040c0014640c0d000d09100c01c0c0d040d040815210501900400080002a90b080c05900d40d59000003045209000b0b0280000c64400000c00006407145e0046a106000d50181c007001403400316034154100d40c44100f40c0b450b8120100c14030400c440f00400313201421214000c010800b03440480a035542019084408000000004904c02c00d4480c2d003442d40d800f9032881c503260301c9000ca0b2502d444807088819a991103407031900b00210742c5510001c142d5100c60307004030b000c0302280d28640b0340d0710f10980003510303100400c0f80400132881c2d0741d200c43c0003c500070b0044049418200c4162030004020410252071241280d06003802e20510020019140e0078070301081c40c80a980345807038030000740800d1200e26100341d00c08841017040048a140000f404543c1d03c074600900c00c003a031100d202c4c0464402240d9120b0201003200c42c00c511181160060710383c403440c440c840e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 21816346 1250 21815096 21815099
    0x708061611070e0705070b0c04030305040905091c020705181006181505030a05071403010b0f1b060603070b030108070e0c1608090a0506040e0606070201050706050c030412050a0905040b01030204 85
    0x51040b90f4404851403001300d00001007407002c1100c04090349a002003080b01c080e00f001d040d50b5004151380f10b9807282c88205030311140454400801800507428a4100202c01104100b200c2406912440e80b1f124140c420103051710201d8513415007510052140464450b40302c00c0c2d07801d00b03c00b0746204120310010408a407411902103821103e030028102020029190700b9241c1ca0b0280107001902d00007084402084840581000d40b5030700380c0203407810750f0f1409030a03640760301e4800340000710b6004412090341c21034440c1c0d404c00c1c1151800302d8500e004d1101a0282c3d815a9140d44200c0c0f62031100b84140402d95200003010001d407200ca125080d004040c40e44418030b030a541800c1301c101203107220404d4550000000d0b40303e0441c07906582e0b0100a041c01d031134090426280c030168404100300205268001d000010b8083d0440e8843c5003151a19a8031150400580c01c0000b4194800d800884045500003803003c00399103518083c00648250040b41c0e5030b5032038900d05220502029003c01e116681c10f160f006d000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 21817596 1250 21816346 21816359
    0x1112010905250806010602281505060102030d060906082404060b120a030206090c040c080a052802040302010e0406030b131704080609010615090314030f041403070806161107 76
    0x119009002d280c2c002c1c00000300c1c410b5009a0414240701880c04445141c2403900003503201c0d1110a01000704480001c0c4d41e0342d0b10001030f820b61040fc0c0ca001c1c040340c0b074204046400312295102d04250341c0308904503070000101d10f003c0d0319802c8020141d055401e52140c0001c00254050700b0060041c00041c0c0800118040c000c0c6062901e050407608502581002040202d00b850400c160301c000c140446052041c84081d14016050507000381120102c0c40c0c59100041c0e00902888005075a14509446503001c941c20315561070080d0081d0104074001000e84600c18560300d00f41c020701c0241d03600028407038015180c0d160300140e080388024080342c002c100424110080b008140c0504020080303180900643d00c0d000000381c3c02c5806c1350708600791540c1c09080c0079502c154131104c4c8105a0354840a861045107071903100074076601440b00e40755030003500010040340842081d0151103c04009608540301c1c1030b218441d240e10744404a980000050822513100003080c800c0e0340c5618403522030f40070365107819101c54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 21818846 1250 21817596 21817603
    0x30a020405090c040b1009091d030a02070303030501050402090907080a0b09070903110a0e010b0a140307030f0b0a05011409040b0d0b04020306070f02030306010507020117010311120109052508 84
    0x42e56918a07400258074401c1c942401d01500e606003004440a02036104141c1010300101a54003ea0f4516555020500400469454841c0e072003038503041144d0b29011242002552114140030403800641401c4c00040e031400d040c002d40d92804d030000c1444600d551008811507001c24000c0c016420991129081e2a0541314412080d0240030f159485400c07040c01d41c1000030525900369882805100c00301001c1000360705001005054030707001d04c2d84569a4100302c07801c0328208003901d0804a440c00c00028407508a8045d030102d0031482c2e48140c00d01400a4030001c000b41c43c0043c3c0315075804151090701d100300340a0107000a202c1041c00410020301d03041028042648840c00e940d04444d62003410045c003082d458108540ca5105109107413807680e4258400d8001d40fa800041c24080c14000f011031000304585c0102c01218569903000e103101e0703096070340e4104607207020182c1c11603a024044410305900e140700107004280c0d10035040002810000001c12220407400b00d00c2c1c1032a241ca0010800106030510f050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 21820096 1250 21818846 21818851
    0x5070c0b04080901110a0b060f03070b030f010e0a0b0901050105160f05070602150106090e07031d010c09080a170304061409060709060c0210080a020c071d090a0b0a0b030a020405 78
    0x111400b60311092990009040c0b1409010f000101c1d0b07004c44103038800150300031500c2d940801d05440c084078210507071020130310b450083e4006a0020074040100890100f1000d00389040700c1000071110b04545550310280304450200e240181c22001e0306d00188059405040144010003c0b1540e5030310104207500e500c05001d40d418070440745500601000c01415030704200c0160310242011004005500d408005001d0500a100702074030052504005102140242e11006100c03a400b010440d224605030002070080100921071000301e8090000441c6030f03074000580f40f22440e444038071518100e11507011404076401c01070040354401d8642100c140c8222103d8611805080d090000348690304010b0000b6003000000d803c241c0c2045400841d03e4050f9440c1111a00b5030005400c101d1030903110352100e80d0191045032558105486440300c0064034aa030b100020809e02c1000c075900e02181c60f0007410680341d11181c40081e1050350440080b4400c0241644030b08042c110040403a40d2502d40c0e6030105040d43c2c001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 21821346 1250 21820096 21820103
    0x7080a060906061703040303080a020d09030309021810060c0204110a02060f0105040207080d090606091503020103050a0e0a080c030705010603030e040b01090503060a15050a090207050f0f03070605070c0b04 90
    0x700d11020302040402d000d008041d10b0900d40d03100c01c80800840382660303401188005070030030510002240e60001903034103d81340d0034800f07942800402400c2c01c001d400f9040340c000483c0690400b42d81c1c401c071200003103490350040d00d8200d0390007111807800d13000325100c1d40e000034240c0e48940d0300c450034040401601d00030002d0f44055005002070385001c11071082e01c010140c0c006400759004000b0344001641420803122040300c41030001555600e00c0c101070340200055009080c656213480700090b0801d42c812615000c4a04c00da0b030510081c2d13214103000c0c05842c0040003200c000e41c44a19060300040081e4003900252624008407400c02049171030759821344089610945c0030030040c4070382c4407840c10b06006802c2c1d900700c00e0030030b1700400e460240441d5640c81c000340342d15603060342d944200da80c44101e403e0300001444001e040c0503800d5100c001d250001d602c80c85044820b80300308540c0d61030321100807a258003030341000f41c003440c1040c41a8803840701030031000b04068100030284940c00001140c2a8601c1c0c0107901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 21822596 1250 21821346 21821351
    0x10c03110f0606090108010c050a030207060b0909031803190320030a0c0c05030105090a1401020706050a020c0c01080912070c0b13030c0b1303060209030106030b0403030b030d0e090a0b0307080a06 86
    0xc0c04001d0107428001031b04084c0345039041090002000790014101c9610202c40d10300140d5a564504188008042d28008640c2c001c5001c41442020798000010300703180401d404841e01c0c0d11400504060751440b40520843c80c61720f4076420780c80401e000c0e01340407258104c1590b00c10a00040d44060905660204106a010442e100c2090091004404422000d4041034000300441d00f080e42c54980da0345510354006104045940000d60310316002c0d0140d40b0000d500c040240824245840c05101a422a1160f10454441c04200c0c90042d88603041c0507000701c40d0710001d004c130080e0010303803d04580e10880068030310882c0d0500004800410100402403100c4020a00d00702034103501c0c01004040c0c2c260301929010750b0a0103880c0403024120704610032250f101000584c1c4840640100740505056480940281d0341c240810060540541000e203c4950440c15070702d01c210305503019900c9603505c221040d005454000018801c02c9540d00050480d0002011240e02554071a00c45144c005400e004942498 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 21823846 1250 21822596 21822601
    0x10612060e2a03010303020d120915050c0c0106080c09100506030106030507030204170a02100504140d060f0507120507090b0f070606080f03120c030105030a0803100e100501020f060903030105010c03110f06 90
    0xf03a101c0408601e1350a1038206000c170781c2d51a1943d607060344058104cbe003c070070756030340129010020a404541607007a5200092048a66071480e0a8032282d080e00607a0103001314000041c9180440c17244242a80c800419045c2186d090000440051800404450a148d800c0201081034421080b240f0400341f105802401e60241c0d9105000801d41084102018064280001e00c10110343c014100185232041c0c1d080340006404d0f040075405040c4501c00000c0f050301c1c04003800074403036005040d0003c4003200f050502c00342e203520074121815243e9100d084194101403114000300c0e1030000040591901884002c154540c684542d10b0800045031078208495000040e4100c0d0b0928400f081c80c0c3c041445100b0500b150300d00b00220b41c88649110f40144400ca000000410140301c00782c1100182c40c00c140d0342c955500d42051040c4842e0f80c903005040c007512a001d02001d140d82e0000310f0354170403519030000c7c50450b460030b801507914900c0e10400701c0074494980c4c14640c041200304984038a00c000320004148a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 21825096 1250 21823846 21823873
    0x1090218030708121605060114130e06070f09030b0a020408070e04020a05040f29040b010e0901050904050f010c020c041a0112050601020c060d0f060b030903040b030601050405100305010612060e2a0301030302 91
    0x20340180c190034512814000b0740380d0750000c0841c02c203071310a0441c01c03c12403b1028250454444103d50030090162a000040c4044540b49034090803d071800c04040710320007a19107408054417401101e0081d4448040d10b800e02860a25400545e44110001c0b000304507113421000350520620104860520403c00e400c0185142c607050160760302011080c24140d4801c40c2e14070114034615814044c040c007824180380400c041000c1080b03001d13810141c1800070041038113880e030000e490300b1618040078810b074101603020382c1100d04030b00184540c000c140c48040106074520b0350755001d003500924150640c0181c4803540010740355400180184031030008002080050301d02e082d8229002c46d001001841400c1c410000c10803000011201075403405042207440c0d594040c0100c500e4480d903000325401440e00040b00402c550541c01c1141a1083c6403104d00c4000c804529602c1103808610407d00050070440202e05001c0c0084040d012401000d10f40c0d404500e00030388075214550080e401200160b110701030003040c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 21826346 1250 21825096 21825109
    0x3060b0a02060601032f0c0307050d08010302030105070905010503040f030203040b0409060509090105074103040506060103020a050a08060a050616060b0405060f121501090218030708121605060114 86
    0x241d8000140a1400c1c2d1300880c03440510942046d1861020100080f91b102042c3c1c1042a250701720f1740b00c000c80301c2d40701e88580300401812081c8006c90096003000d0120308018080c2e0010820707551b041c0d592904655981d1600c01c828584040180c0940c00b042001194001c02100140f0150100301e90200b00750b0b1070f003021b000b00090010031a0031140d140006000e51643d1048847c20102841e4500c09036411550702440555500d070144410301451082c45d00c40f101202501451046010300c09449590f0b4a0b0f80040d001d91080b150110001407082104451040c022500c0b41d030818005003038000115110341c04180c2550000103082e1008440c05070500401009000350319114109990612890516402207103031656000190303807180e00c090f850000d0288080003401807518403890003604070b5130358098540003940b0081104d034007007000d050001424200020041c045419180041910f03050701c041c09211904007801450a80c0340021050012400070480c7d10301801c90310300040074049000c41013280 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 21827596 1250 21826346 21826361
    0xc1006060203040303050708040504092001030606020c15040801060305150702011107020607050a060507030b0307050d15020f040f060905090a140609060103090b1608060105040b0d090303060b0a0206060103 90
    0x115541000400e0080c20740c0801030f00d00320f99042c10020385440540c9002d9003223002c2c681040b03030410b15020b46031041c03112014030850258130884040450501c100300440030345246000d00d00241e8442d00c1e40c0103582c04d1640c80c4c14081d203403d076001801d090b201c0302c0031420743e60b0592041e41c40351f20010308148050511018a508001607000070040c900d000d6080e04070314010303002c000c2d100d42130205050301442400c3c800c46074072030f5000030100f046103001000500240003200c51280a807094040106041c1040351a0240b5580c10981c07050002d440306681801942c0140a100b0b910701042c0400a24505068052406000d468598020307603820030301404500d4500902c51034600342030840178008105000390868000348241c841088650310000141c02503c1207040007001d0302e111100b004002880c0d10b940345101c5240317a45803401c944a0707a00440d41c1d03008074040c18055050401c001801d038580c80d4407260105110f8140480e629665a100c50250b800400c403480c09600725104000256a02d84078450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 21828846 1250 21827596 21827623
    0x90709060b0301080a060c110d090305010612030206040602030603010b060a030606020d0c0f0f020415090b0a06020309010f0819090303020d061a0d11090a0b0a0806040c0c0f031110020c 81
    0x20306544c0750000c0d4940e90080e400014004960341c142c202c031800d2195140e2001e5406020403a840800c002ca0000c0c01a0754620003035a05500e400310200c1e282c0c4644001341d2003117405130b009107400d803239640302c5400951000d0800f503855965960000d072280c48040243c0401d104076240020740034981000070b4100081d002ca00420800b04a48041c0050304440300c0c14500c0c0d40180006080b42000e2000c200106414256051800c45544d00051003e2080e04014101c2c58240d0384030404582c0c8050a0b40d4078001d10400d00c1c04600014422212184100e00182c1e0010300384285d9440e0341c01c100c1300300d4100c442854003507000940005a28098041310b005001c014003030300420322005040e80194101c1c5002c0da110002003540c45502c280c00610600e0140c80c4502002801000c810ba40d6800081c0c45030f002449000100310f19030002502450a441002880c0301796445000840700310350740350492040017100450502107031004034a03461404200e0500c25200f08500146e40d1207280e000d0724a000904c04c0c010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 21830096 1250 21828846 21828869
    0x3060a030b0108030c0c0a0608040605071701090e1212160c080711030c0f060f0a05070206130e0c070c090c1206080106060e030703120309020112020a030f3b0c0909070906 75
    0x400048d6402400c242e07010703420120010b10381c1c640000c100d40030440b200c0c0a00051141d00d0020901e00065070061130034030446004c441605008603411720481c000c00350148030b101403510010740702d102003d1030440b00180078a48200059810303170315100f01e07400c903c0c0c0a0301d04d84441100b0100c581002c00240c03040341411109100384d85138801c00103003240b040401070140c141c40810314125090250313050f9030000d40c1c010903007921b85650203c825200d8045200f83c1e0076010468000c2038140110380121401a9008a0b55141407428074807100c020f07000e10074404c810450080150308160791240b10315000740078241c0000c200c03940f174140000c01c0c6401550a6900c80c0e0061802003000920a03042c40740d5942d100c3c10040380700c100781d0005032901544c043c3c10f0017940780002034012080b5030591002001c01e948034000c2001101e00c0503009203003841c3c1000c4071040e0324841e0011030010f5007010752004c0c521004e4102e402900313200001c10056103003a00d000e03400d40c0c0b08080c180400030b80c0d4003c00000d071180b144032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 21831346 1250 21830096 21830099
    0x903021609061701092d0203121228050c0403060906050601090501030b01080a181401020c0601140f010305061311091509011b21050c070b030c0405010503060a030b0108030c0c0a 78
    0x100c1400390f900c009040c604d0303012001d40b070010000c00c03600102807e8009081c0c48940c000c140620040c0c2d40b00040130003400e0041800191121099901542e0080103d0030a40f9120034400c5000010700c1c01514a600841062000000080580c0204c0300ca05200e6100410705042c10700014082c1c1c0e801c1d40043d814581000840411030340c1c00b41d01c042c0d02990340c241c08100401840d640840c03060000700003600d03145141521448480c41500180200402c9004642148c0e9840403810645001c1000f00e0350300440090302e540c0551304c29003119421080050601d4a24001f0b00d404d030045a8042403e80442030021499030780a180201290710b03801200c10516103445004400204100060036000c14031134940154001400050084200840c144c1c0d41c400f0b6080140c00d402410682051244c00e50314030a000c8041400caa003c02900d0150413298106801d00d402c000c01551144c20003806c02d40c01c2124034800202168007105014002e100e49009175948401d01a259400c004005028900890302d1340c50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 21832596 1250 21831346 21831353
    0x1180f030810050f09060a08120c060c04050a06080711030409090201030b060304080304080a02030708040e150a06120e010f02040306050403080c0922021207050307020f0c09010603090302160906170109 88
    0x104404c0384013040320b403200940d58040c001030280711140c011000d10f10544a90500001d1401c2c003c0401d580030f101200e0a070b65070b00b0f11944e600d120ba0300889410502e101d00801c421030250200f2a080705440c00d0a10900310024042031940d0001c0e48002c100544038a018010740d605031240c09132220040d0340c854550714168640786803070b10000e080107104100c00103d070709101d2302c00d00030b0700c003041e901580d03850b0303110b0ba20b440f0282413990590340902c80c001d100d485100286405127440c0200e402548980c003560803981400380043c4443c800c08200f55403114000b8450a50320310050018500c075010000701814203040051008a0050000840306070400848405581b003c8003000c1e21019010450542c0c03040c618684040d006513441c0d00080c00050044c8400c0341d07040300185105107100c0e4200d440004944440a9035809641045a00015490014802140300303070045000b481c040d00444030910003900c2c8601060000354448080c80e99140002c4c02501d05403402e00001c1108000203004480d02610b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 21833846 1250 21832596 21832609
    0xc031204031403090c0405010b09180711030d0e010b1005030a0f0608030309060a0c02030a0e1002160801020d1103010b0d09050f0d02100609050405060a05070201180f03081005 77
    0x402012854008400080800d4072594400c0003400804500b1500e0303003064070b100d9948880c0c01c16802d1096003403800202d101141c03036065407040b04c001820091415014000c0360008030000e0651401c0004912000103540400c0008209616405a000580c40030392400503003101d5405120b41d00c100c88000c1d2192038981c0c45016241c021101010004020442c24240d000a18071a4089080d80c08013004200d082d0201145140c4603c030800410700200540b14001c0780c4030302c14400040041984a00300c6541740c101054500f484401c81e00441d03030146101c01da0000c5801055010b40300980d0005150090b06856000e00400d03503608640d0389045504200c94001c5502400700403200342640c0d240d04005101c41008404820000c103010f232120703040f00c680001e494280600303440c5086424018005a1b528051290358403841c0c011018000c0c81d00c0d4400c03008090240604203400319034a400c0c1510809010b03540015850b8030941299498074040c0c68068401c1d28001c1698410200344442003155071601d8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 21835096 1250 21833846 21833857
    0xf03040b030106050c0109020a06051207180e04020d050109051c090303080601030f09020402030c0a0e060909040803070201090b1302091b0301120f060c17010e04031202030604180309090609020c03 86
    0x313092039500c0b0644948554010441e9031070281d030058105000041c440e0704480200242c00140310040b01c1d03070340c03001c0090710004604610500e81e00d020020030803100070040c41440e0080c2c070003440c40f103079840e10b070f00c0303c9023520700079030701668960402c5500003500d0301041d0300da68507a0141e0400030f200901e5030b100030f0007082000f8236003030515868a000ca24103400582c4031240840e801042191a42482d0803541e0040d01b1486448000c503400e6070070345034245000d40c1607035550303100140f03001c41a0341c4030381e103005076a08003410070010341d03480302800c80000314403400c4c49100794400c8281030f130300c41d080b030040001c10781000c0d1450010380c41c0710820416140240b0216070644184515059114031149041c01f1005864403005d000b0625007840e10664540c0701c030041088152540c00c81060f41d0f203078260b002120b28107945c02404030781c00034001800c0f29420f401650384000000c1c00052002080200d40000845d481400c81c00113504110502c04560303244a2100a88840f90085060803446410340e5a00e2245c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 21836346 1250 21835096 21835109
    0x2030709082d190b0106090501020102040b03070c0305070507030305120f0906011401140c060403090503060c09010305040212190201030c03060612020c010209061b1902090615160b06030f03040b0301 87
    0x107001c0d120000d180800c450404080c20341900303c0000e00d10b040180b22200203000f030800103092002c00003240e42c4140291001d0b168080c000b24603644980e4802d9602d0020142c0807410300070240031320310100b1011301240300158000d0700c4080d601c02624045d60241c100c0100034030210a0700105020300340720000f074040d0540b505801242d2170500c0c00d4005035407546141500e11004807000a50f65242000420194000e41c0302e51203c1045075112000c05031520011a0301c0101c400040c0184201c640c8603401040d000360015008034403180350805514100581c1c8105400395000d99000d560855030b1500c0b0381b540e421601c1c5801c000312070800c000180b40c11180040b2640301e54002c68288a0307040c1c294100c480d2000001c004940c1ca0640380c809041111218072482003c3c040c000030f000c02c10f5034980a00c140168001c082000c01e9564208002003218420f50074a45400d003407100348014104401c6003610640031340c946071040d2501c1d204042c40c1500c92114031400d41c000344002c00103032a5440549065420 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 21837596 1250 21836346 21836413
    0x8151005190306150c05030a050310050405042f01020c090a02040f08060108070801020306130c02070902130503011802010e010521010e01090b0915060a02010b04020c010203070908 79
    0x20141000c86441c0074a015850a00301e10880a400260700b55010104480303500204462820712500700351900416200b020b0242d070420400c05010360300c12802140d0010301c166980400540315000b140c101c1d04125401c403020041c2c124404085371fa016281410840480c840450082078500001d4499002801545c000c40f0a8400314910341d11980640d809400407010481110f42e440c900c407a6078a8081c03041746c0440c020001e02080440c4c06008407846070030040c100408c0d489080e03006100500440d489101140540d080100d411400d50000305a528111860080991f0070402054218bd01611814200941c2d10300300c2d20050742c205012030540c49090814640303803a80111600e980ca50705180070b00140190380004036110310a0307900039041e1a0554810400c18a0010a000155106031900300d81740b03000c08422181d5182001c01450800c103d423002050381d18007035001c1800c5c1d820000f9044280c2c2d4001c8200284541e01120807801000c03548014007100b819614201128050302c01d54003203240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 21838846 1250 21837596 21837619
    0x6090b070807050105131416050904020103020c120315010201020310060305041a0406050412020109050c0402031e0907030203010b150f03060402071203050114121506030109051902100815 82
    0x341c1d401602c400d160041c00070301091030240c520f440d106058141c00c03903038400420704d1401007944c0001c01c01880c000b648446001d00e814070042050200000300704904064080242440c500c0051019025281c1599181c648034103000384600d062582800e125411a0310500c10044001e000c929524200c0f05075003000500c9446605007400e041c1955010083c200d004041070008000c1c1552103284594007030f500003480510a4a4102c1c01c2c2c8400c43d030042d280e540305120010f02894264011504104c20105074000303081c0800c0c00c060450403c507000b0340203400188041082d82002c0c040c540100e03408489440b0301041841c03e010b410b01034280e05201c0c2860100001f0226213959048071017041d0494085210f0709403c8070010054042406803100b64070580c00c101c0e140303082030314035a400100c0210190510359a9540800003030030008000f42d60541d00c4410a2010500c10b114684a030b00fa40b0203101040e807018018400c02405505001007008501c01c02c00256203507074140075128050880b079160300803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 21840096 1250 21838846 21838853
    0x4090b0d02090709031104090807140f0d050d050702030f0711040209040911040e01021905030603070b030f090601060e060405010c060609060b0a020f0a08040e07020f0601031202061006090b07 84
    0x103148000094001003050300f4080f00541051007070088a208101400c040702034101071009449085d02c1c0145080401c0c001c40300061121244401001d4180d400c59021f84400754103d490509810503500c086140025a00b040e0300f583d0040d598085201c0c00114504480709041308680d1056460141c40e00c5169410303c03030769559980488030940c20090050002c551141003070b040041e420001e2921403840c0176201c400c0c140060090701c141c65031405a8200c41e405c3d4500030740340c0d035100800207541402003040119402c00d580ac0914018410382001e00e00034605060902d14044060b0060f205001c51900c04025035511031044805075842880c10410b004254900000034013229040f070107110342001d00202c1d1007640100035001c03001c202d034200e490005803404002d0f201c004420b00030740904c50802003417002ca03088000c3c0c039030803151510444041c04403850750541421401c1e0404c850a6416503c20050b00f0790401070144c001c00404081810a440c1910203820798116116400000901003503000c2070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 21841346 1250 21840096 21840109
    0x903020d080409020409020c1c050f090a0306020403080a0906080c03071d100201020d0b06040b070803041a09030d0e030c10050a0b0301060b0c060708010e15120114100501021204090b 80
    0x40074843e40a41d22142c03104421006500860341120f00c604c10f205d1040d40c80d10900e1410443c0c142c0685506140c00302182e00850140e2096400d160060b029450010000b28240300400046010b1f038940c6403584107802c0010300002245e07000d10200f110207030901400541c6c1c40b0842f60170140c00d0403c1c079041181018441c8a0407081c00d49290f1119150050340091501074005040c0542428010000601031404002d507138001d40c00703894031251301840048006030100004641250040140380e540e44500740303524001c0744003107035115041d82000c41d016640600b5401000312200d120f001660500c4080050b2035a1102c41e9107a04218585880100300b00099562200040e500c002d002400540c0d00c59192070888c4d405290301c0c803502d114240000b00c41d54482c00d01507060b54044c206281d80c584620320000ba006000304202e070b920070704201015012500910481249482403c03003000c0314034024265404503200740d404141903401c50b901c3c017500550703000100d5042e11001c5800040c1c1c0040040407940c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 21842596 1250 21841346 21841349
    0x80304091d01090b0f0c0a1218080d02070c0b0403020d0209070e100503040b06031c03360209060910062106030506090106090606090501080a0e03181801060903020d0804 74
    0x807075481c00300000c06001c01811400d00c00c1400b07901240058a070207801c0c00311446012500300010305030490591101c0400e800110b040748880030b00344420202030729040481c0e8070406441d009070342c0c0051b6040400c10605c6902004004641d0704034205450b507000f0841d40058040d00a00c1001c00c4400100c44900030424080c040c42c018040e6003c0d0950180701070955481950140c80c0031481c0d41c002a224900000d00c00c0c2001036010fa941c0d44100c007458180c1c090a00c40180d2080c1c0360081e444514000d58000503001045103181c4150190485401404010280503008a014401c1c190401665055100c0311034100c42c824031304406800300003110751490404c0007044014440c24000000280b14000501500803040e1800070414a41d54528620403241144581e00103c2e047c2141040950300917210b84d540300300d01102c0480c070000d40683e01801d6511809514030044218030050803241040090001440320358600b00d000f5505041d40a404000340748002442203081044c00410001507800381c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 21843846 1250 21842596 21842651
    0x120106080109020f030604020a0b0a03020405030303070c140727060b0c03070302060702160e06010507051c1205220516030605010302010e06070b070813080f090f0a08030409 76
    0x20140e19048164060090b401c0c0c01e81c49134a544000148501d800324016009990091880c0c4026241040c0c0ca4056041f9004040606909200001d030544007400254801d401e01d64603808007880903c1c000550b200c9020211100b903003e92410310240e511844500302503c0214003402014948000103005030101d82c0044040010200303050004407800809080d03864031940135500c87da070320b258017241c1e220702844c0c080c011448141401c100340807c1c88410380d08000185040c030b00d4810310b0703110383e4540030301d0f0811000c501800c0002801925880010401c025110080601081c03c1c04840762000d24080e5000e00e6031603046000c8001040342c1009915040d03001840f0141d92503549007072200060400b48416408910240d40b000141e01e070040071210320035070109420084e504c5900701107401600c020901d40c1601003524000307004c251001d02070030a821300650020b03602e12980007481003004130940c44601441c00204244000440441030f84c0c1a51001d4600060f010560710040000402094120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 21845096 1250 21843846 21843851
    0x30d0606020f0c211614120c010e010903080a02150604020702060d0b010c0b010e0702010507030203061815030a0b100501090e1302010504090504030309030f05090a0b0309070801050903040303030b0d080702040b1201 94
    0xd2074108440e180b181d0071600490a0886c01c10190360a0148a4a00c44041e0321290490310703082d1020341c05895144a04103061401018041e12070750f443c001540b0800220002d80e20400c1f103010034001c001c180c16441071042c0d50640c01e110803a0b000c1032070760103080c408440350764032011121010b0344203a10402a1a41080c01454256500e00740000f1194040c2d4400006500784400110790501a000301e0b4020900a002c1c600c3c00c415900258442100181010300300e001d94110302d40007039404000c90020341e030052034090740e98201007600505000c40c5900040c10311a0311a030401c0300070b241041c481d601a03c00591030200004600c0100c8243c407035070300f2a1054130310b058240001d15034164031641415100b5180c402100c0f007211011382e41c41c0a00b4024a510141d01d52041c020310080740d01030f58100000504690310343d0788451419081d43c2003110340512680c40400c0400605034180a444072048054550610b04400c3d500c4212003840f603103034086d010341e80383c0c0113244031601c4649400100d462001e008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 21846346 1250 21845096 21845113
    0x70b0c120112060501080105101e0801050702010f0510060206180102070219050102060a090809010e03120703030504021f0f1103070501050103030306090e060f0711150108030d0606020f0c21 83
    0x192640e2001d50002d54809113400004150018140314203402031280008aa00c00d5140c801760306803940f001061003141098030b000009400f0401d01905024503170315000402c0f0211080741c0042140d800500c26112011000380801c900303138002c69042c0d045411041e40a400300f4070032540d01c0c068401d1307800081d042880450030040c1e02e00c0116000083d02d00c26400d03500c036a180e070048007003035071440c5002410903941003120080301e42c014480d0040c0c4400150968140c600368010301d04281d0050b403000d03008a500c520401c801c46c68600c030355a6040c18050b107034040c0b2a500b42c42c002e20b4114212114003d120b031142e00d9040c0e1010803c1a228030943c4030300248410343c2c42e858000d0161416100c0c1c000c52905011203070101000104102e8816000002900d0340d95507400300c02ca408038000014022503011b0380d1072806500420051182c041e260781d40c01569102c80c8960660201c0b84182d00150440d0031005001040d00008151011020400c407001210715814060b42c54071410104c016040131300c00c1404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 21847596 1250 21846346 21846359
    0x5071520040b0409060801020306010e060307140c060604050117030a030c0c0b0a140702030412060b0105070b0f06090a050103050604030c05010e01020c070305010f0c021f0207020604080a11010e010203070b0c1201 93
    0x3c00503100c02502c240100d80d910540035081c0e00056480c035000c100080c0610486041400145070301c0010b62812a1644501c03024591540d446080c5541840c1c0140003040581c0c2400d0141a004290545100300c0115070918281e4590089184407010991507081790b9402c079200d460100240c0c0e030000c090700d40c9401c103024028028440e80c1541c0d0319083c6440e0003d100780c2d00100545003140c0404035804203e040582d580d10007010802851414040140900c00c0854001180300703200c0c040c08851610a420040d0401a44020042a0070603d81c2003400500000b80c02060b4290016890304141d20020010b24219000d4001031401c40c2984d8404201c030700000c4000203404045a005030000c1000b80840c203950300c156140516100f01507400030701004001c00789441000c2441039801d03030050400e01541d0000707480c1e501692060700617134060707103003801800b00e0b0400c0e00d04000002d0800c03400310006da40020351a07005080020b001c24445400203441d5a0342c1c072007241d5000c069040c52440541c0c4520 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 21848846 1250 21847596 21847619
    0x302040203070203181c06020904110a020303010f0e011a090409020310141003050d0c03020f0105010e061f0207060e030a0506090f100b06090f06120414010c0507152004 74
    0x100e600300500d022900c0c084181041c0401402c0b040c906011b8031a1518540c49900183d80004c1c04150443e554140c4000e44080003805820f10b194194007031580c0b035151413040545c07940e45400071408403550304010021541d0480741c2e2585800c030b500e5225141c02c140f400250003400c131a5800794050140d40001c840203170743c075030100300d160150800b00d05154541c0c61071402c001200d4003004001ea400700540240242c080e04201c01d0f5584688100c8070300c946065885800e44c1d90a0380201c070003612800070702625152061040d50840704100c0c0c0040401600200295030341001e00c284824050300c0e0340145440d850074415168036941250481c1d5403424004212569240516060702c094060729140c0c040031501405034001000004050754200960f510810840d216200c00301c980c420001c1041382041d6240c204400d12441c081da528450480b140706e0342c1c070b0039218400020780400c1707000c0062600181d003240802041c075640347d90026450002c01d01000030581c50200020b41c0000200e0009030401c1e580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 21850096 1250 21848846 21848857
    0x210201020102270310050402061813020706020d0c1803020114040503120d0e0601030c060e040e01050a09051204031a0405070b0c0d0f1707030c050d060303050405120304050a0b0c01060302040203070203 88
    0xe40c05c982c0c0c0803028140041c115101034a0096001c0b000f0811900750715000508240d08081c001c000540b2803a8003440712040382e110403022556650041780c40d0b1055a101c1c4140f9004c01e40a003004a035000381ca000c4414040f4050200038140308115110300a4000c0c050281d4010303040107000c840c595070341070501c206e6540000445000707003400d01081440e10200400c0c41d0f4122688030019420403030801a040d2034007014031240c290003a039130f514030884040e42409204c0c00b0300a543c100185003d40c03801c00505019803d81542040001007000b000020410f900420000304045240c01d4952503519020f03080841a50050ba2006000b0500079010040481c440101c43c02c280c80c0c4620946c0540c109813001c0c1c4002400244101e8114005002540039030846012448030389410b40c60301132032031565011100b81d604182d00042d80410f050101d42003c0c1040d42e40a01510025402d051418000031407d000074010310700c0009010404070b81c0d002094110401860b4010025901d07490905002543e94005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 21851346 1250 21850096 21850099
    0x150a0b04020408030d0b12060c0309031303030c1101020d050a03050402030109080c031309090807020f040608060112060e0304150f020307050d1d120c1212070302030a0f020721020102010227 83
    0x1b010301aa10f02e203480301550b00356102c0c00001c0d20300b40e920710301c5198694000070100b420500042001c0c20100240b0003080d00558072a807240200c59900d410000c1c03101c0010703a000c40c19944098080103c540d00541590320001481c540843d5680d40c0740b010038013404046500070814030000c640c0b01035841010018002008c6c1400e4280d68080c4d40d12455802c3c1d4007003003009440380c0401c115a501504012400b41c0d40c1100150000c10215525050b00340382c00826404600d42000c01054001000000e001d0302400e00a1040114280f0f4182400c1c9246080d0081000d014000000c50b07211042d4002c0c015180090f070000309880f50009114000390480d400011007080c44103203010710070300e54602a00800740107034242d07005110310301c1c44506004076480c0e00400100a032060000303042c0c03501d28450007008424860b501443d00c441c09041c0207044510092400310954211010501c0a01c000c080e01058900b540c024100400e001400182c1c028810381d0700e00408440459220b000c1a034100c0c00e81c4101800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 21852596 1250 21851346 21851351
    0x115080714040504020313020a030501050603010b0d050d050a140412030e09040308041103030f0408010b040b1002030a030218030a0c051c080909070e030d030906060b0301030203150a0b04020408030d 87
    0x85461086900c0180041c000e00020010300040c400e0f414513501540e4030040015000c0c0345016036400051030f00c0c500340d004032500c2e9100c03001c12209090a004401c2001c1c4162191140940c01d41e540ca51241e10300842c000030458003042c040b804a1003080000350400c1e0b100316560344c4584507040d50000a5080c1c0040e00844d002c0301510f10305051083c1914071868160703451484a1701d8941d618020300801c0844c1903458030043c007a021032158070388000c0005140413800000d1120f0b1480c01d00041d12141c030382c4070b8401d020954601c00b40a80120442d0080c00d42840c0041e66402c0c0e81d0903494402c3c42080c1802d816114030450202040b20703a00e1b000c4181c42084510303d00403032880100c455142c03e1070200410200b420320a904540c18550f40407604a041400d000c0d0b400050b0780d011a241503000f595032710000340c69150034401e01503a031207850054499556140d01e19030460300400c0e5a00340c0300314611250341c07080e40050b10100507a4400408550010002d40d0b480d40e4880e81c182d030700e0f004903074100364151 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 21853846 1250 21852596 21852601
    0x60d11070c1d0c1204030302130f0911030601021005070912032c030304030f1127010503210306040905070b0403060b04020412020111010605040f0c0f0c030801210b011508 75
    0x251400074894a070210350720f071a11a500303104c0445403002600403000c0c5074091000241000d400706403600500030344100007010522b40000841613510550320245010010003d000c104d907070100c2d480150440c29000843c00d500c90a074200d40c181c915511543c004d0070000c0a000402d40e010403030414210354800b140010804580111404041c49160541d05a008010400000755801c500a86a0340200020102c00030342102043c400700d09003144411148103525088081018040d540740503040940003007a810201c41d414100c2e40381c107081f62080c81003011000480a541e181c229031101c1d40d000e002e46045594880150b079150f006808112585402c0800522240c00c081c42640e049600002281d88800010340064a416120601c41c03890342d52990f00c041420744490013a08601c200301c03180003403000d5070b0b114003c1c1700c4841e0010380390401c090070b68840d004c00c0c2d22450050654020340389074140384020841032100c42800c0d03e0300900d8602d000000148404c2c01e2041003c1e4041c0361303110201241d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 21855096 1250 21853846 21853889
    0xf02070204051005091603110f030907090209010f11010f0e100605011704020909030c010905030a030506010302030f0402190e0c0304050c0306090303010612020403150b0f01031406060d11070c 84
    0x8080f54001d490704254441d0005a0808100c43d0000501020b0f04001031f0400d1400c1c1c0d00c00d42c650140d5003040c1c1c1030030f0000501c41c01c60340800400b001840310030021400d100300035000804c9240d0703541900e02004811140304c0d0501c0829400782d645c04105c060104100035a403800191115641d180c4541c009242c6980050a54001c404070f291440c0064580c4000d030fa202c0d420861003220103804814148014042981da00c1c409200740c0c64000e004800554030344145070802000e80e0401080d881c1014014000c0c0440c00e14180403503608a0740c119610f02d010030300b80e090b0364030401c0e05612082640ca100030620401c500e6550085000d14091020f89036050a01d105059403030200381d820070b0207a40308100401400e44101500700090445ca0409442d295581e120b0207944000c00c003e1a80d01079540310580c2891a10403562038900200303003014410040c552820312881c40f002040d090184030002540d046400b5240e1140b070414031503100701500c80081d8100401c82e09039500484030309100072020004407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 21856346 1250 21855096 21855121
    0x1909090e070504060b04061e050705070605091306051e03030904180c0906030203030a0302130b070b160e060702040b0d02061209060a05040818010e0405010b090306130503090d0309090f0207020405 86
    0x60351f54135103c5441d28003020403048074550b0b408058400b0440c0a01ca03003000100c080c8810b500420b441ea54060704d4140c00d03410850010340689030110210318140c2d040010340c87c0c034005041c4035141000c0803103003188030b2004213081d031141410140d0b006140004c0c021420703130100602c0d403d5901030707440704102d20385446008085a409001c0694982c0c800e2000012a601c0b83c0c00401101802e21400160117035903241c0c10009801a5070100e03010a00301d010440301004940fa5004d090307a80380b800710600c680a1010521038461160040c0c0140c1c2c9903030b01003400b610b4005203030080590182c03929076100300846c0c1758207084409031010400c0d03001d0100864002c4007107014181c0a030b500724051603d06000e0341004c4140c1c0c40110381103810300c0805030800445a82c3c9200b502c2c0200089181e084e80c1c1c1110718209420118018440110003034060b000402140000041d5109000e064880042e22191402d00380c81c60b10307540d4000710829060000c0480303070b0f21580d000f81801c50300c01e480911040d2681030a201e01c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 21857596 1250 21856346 21856349
    0x305010f02040f05060c070f15080a0b060a200a140609030306090f040203010b03060406200415110708030a050a0305130209041211031201030b0105151909090e070504060b04 76
    0x50004822400c1c4203902e010001060309140d81da01f21034415035075500b0807000031502d40c020070080d15240c45c400b001c035410044280e849155164200303c0c0300740307040008113240101c0c01458204101c44103400c88400003000301c2d045065410040b1051403c4a00d00040305a10400008145015100100700d40000000aa9009000007082d080c4a81e07076000c80030140c5040200245c0c0e01d9902e60314401e88949050100c103001e1409038901140c60001968000da504045d413650540c2c02400f000100090807039000c0707803040600c0514004c0518914a000245080220342003507100c1e010005000540b039411100030040d14841e80c505225658400d8102c1a10011404029401c8041c100000b400078402d100740303641c03640301802c1030744044a08640031842c3d900704506448108145c03d0050003070107610180c040c010f00045464211088039000002d215005030900b003900036070070351040e406860148600402801c0c00e0307081005080912013402c1d40d070700000d01c10703103028519101d404291098100d08840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 21858846 1250 21857596 21857609
    0x18010807151b020d020d0614090a0201020a1509020306010803130902090612042904050705150a11123105010c11040912020307050c0103020403030e0d02010c060c0201060305010f0204 80
    0x190b0361a50484800022000c89012070340030503e034040d1070050755807080390741c5103900601000500454800d0303540940c64018003103c10990241034442c00503a400039070710141070350100b5030f076140700f46900080000d0a508880294140100d80000c9076040000000d480200c080355440da0310f00760707280b40d4102240700d034040daa0380042c001c01c40319203000410762503950058451500754103803038040d090100b50041003400c106064440d1400f40024488100840800303004100c0d649101102e000c00801554802c40d0900e4040c41a00d010043d02140c0074013007040e10089a0301400e540f541c0110354504081d450900002100b40c0c1c410040c948014480c040c581512810385500420360155255000d4040c0c040a19691158807020b600000810013030007111029500d030001c6440301201d00e0a2801d010208181904261048c4010400701e9800f603178000b00910150b902c0c941030b110030700040780e1100e035001d40500050308003101c2000041e41584000c0880f03010f0710003041004250280e920070ba01c918840c14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 21860096 1250 21858846 21858857
    0xe0421090b07032304030c0b0307051b030c19050105090c060409180c0803030601020706050c03030103020103020901030905010e0706022406090c040905040302030304060506040903090303030b030304051801080715 93
    0x14807204545400405036240241004080c6150070380350b07024160000c41c00c0044001e0007080c20001c01004804c0c0c880613000c04020386007140f4000d00000e00c1c50043c50080c1060034100c2e200841c950405000300c4105d2044802030b03c005018140d0469040c1042c1007003280c07158039010004a508070086204401080011300039450149071003040c401802e21403840b20b001c1140542c4101c0090340e600c03402401011008061030701d9181035000642052903d502c2403041c030004001010b2003080200841e815254242170050b202d100081c0101e00400d00e03024010a10b62a00300e0142308014000345000883d441903084802401608400101100025582c503d0311107205020800c2840e055100c0d51b072126000d81c0710350500d96034600c1941510000c2e41c065016810000502c020b01c583c9014076035101c8016141071040210320b41d0028041905d610010741059560800381c10f1a98050040310000c110090821042c400c209619104508081c0700d12010ba200d1280c0000707052100903042100b01c0c041d82c684 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 21861346 1250 21860096 21860099
    0x103050702100e010e0a0c0306060501020304030f0201050f070206030411031212010312110a0c0e0604140a0506130213090f09050a08070201020106090606050306040e03090319050a08040e042109 85
    0x340e0b0060070f5001e0304074006540b22071108001c45400c0100813802801140c512902030301d9401c2c1a81252a150456411504100400d2001c140200d410502031982882e00303d507030348800c090384030b1203000e40700000b54452800010700c0280007a034030049006c88011007d54001101c070300f11000562003080c85895052001c0d200410100341e03e2000701443c40c0450a146a40c40f0504c0c5969040900345c40c01103600f00f400900500038201b080703007220b6018000740da0400044580f000d540c90390950040c502c481c010b850b98005061394440070301208050f0002d500c255100c20b00c000d482075151f503541c001c510019261003004801c402c81ca0080c80041d41e000f4002d8083c1400315201c02050f980101016030556480d000c000400501e81c1c42034000900042d552503844e420540c4c1000150350880b40070300c500c4c0e030040c402c0407199a000301d141402c0000d0381003d6001c9603982c2c41d1040c18840d0640e005840352002080010b06100d00100d52441948190001440c002c00761128004900000c00d1990008281b4070b030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 21862596 1250 21861346 21861373
    0x204050603010f0203070207090e060606030c0c0f0f031c020f0403231b031014070327030207050a0b04060c0201050d09061104051806150f120a0504110103050702 71
    0x500d81080d0058000718028024000f80030076a441511554011391000008020345901b03440f035040c80e5010400907045c2c23410207000182c00c41c0800f0f03101c3d407505080003407110300e6000100982c80d01604c84c0300c25030345c0d40032011140740e499800c516689030a02801c0781e042c201142d094800c4900f031581090720242801c1c25500c4241c0d80402d080300100c0c0620840340c0700c00e00c01070108102917aa0280e010301000c00018001803605011001a001b51590304010078803c0360360109118541c0710070b040c5000035500310707100500e0049110000c0c4a0048201d004504000c2c50b03408107951003910810384010080981c0c1c0d0b498425144118822200091070001da00d900561007000104001020b03271a0104c0d251041d61280402c9aa11880740d5140d948000340c10007480c18200b601c010b214003811200c1d40c08c1d10740710010071040711142c1c1d0101c01110000518001e425003007010b907410204034294010141c5014a41003000302000d440640e008039411420340c4440d03200b03020b080d00c101c940354003074508980300c000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 21863846 1250 21862596 21862601
    0x603090302030d020d060303090815070e0609120102030a050903071e080c01050a05070806010203070201140d090b01090b13060605070b06150c0a02120610030b04051002041404060608070c0204 84
    0x10118110b00040001c40074079901030000e86890b038184e5600181c29440e62802400c0003170141e20121441e009003410012018140007440c0c1d1022180c100700d5085280280003030040e110724050541c0c44440c208100180500543c040c0d489920300000802c5583c54140e2866580d00400358010004480c500480c0301501403100314428007481004041e00b010345040e101c41c29500115103070381c01c20381d0342d50800c880c1503400303040960011000e0000d94038081d62074000038504100e00c08009445c00000850101d40b2003154069400c03d60020086417441d40c442080002812240c2c1c1440e104a580c0941c1c00d8220a13980324a60444196450b85890607030640d45007020307140300030a0b60341e0007200702000c140041c000314000c100400c1560041c007410305036881005203580c00300001403019409102006a0380001d00d0400f001d81e600001e420049581c0c600d052454480b40945414000340003040c00030fa84c00c0c05514281d18001d04503401d0003500d855110031141c00798101c8400d80019443c0c07001501604095 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 21865096 1250 21863846 21863861
    0xe060c0304060b04110a0f0201060f120f050c031c1202310312020d08010803090a1a07120906080a0c080703090c0506040b210403020312060f030a12030e0303040203070603 75
    0x50130218103d44405e40348284c5030130620300900482c0050011580d4554284075000c0600140d00c0307084c8100c0e04241070420000c03d60074004244026550b00041801400c2104040c036030b90003070031261151a41c1d041c5c460f0703241041456101090592108580d4841903000f03840c0c003044c0c02c10b1901d1400038031300002e6071541d81c0070100702a000f64032b40020012582c181e404000034515a00103040201f45002d000b001f0707010507440b5201070f4000303000240d460b907101c500c01c0702200c043c0001d483c1c3c7c1030f540b00c0004c151840384500040c540d0580000820320030390420008401c4940580341d526140c0c0d94451288150752038107081c9400603007903d00007020107010f41e1050205501541030704082a884201081481c1e119401500840c040450808503082044040c4c04014104040a510509080e500a03680c2c1c0199001405101d400000085182d251030140c800000d03002400c80d10f00744130a00b4003543c680715410385440021b05003004440e000d2800004c0728003407640500105611403500304228000c0019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 21866346 1250 21865096 21865099
    0x60305070c031b0209041b050a03020a1a0c010f0606080703050405060601050a12051801060b0c0309090a110d0b0a0f03020303040b031f0f0603050601080106050306041505120304090e060c0304060b 86
    0x2c3c00c6091000d41c480c1c2c01d21520940c440c00c540f201c1c098407400403000914080d441507220703440c81c81c001d20060315107200c5035003100c501c0c000001c84d0000241c0801440e002e01c1040030000d61911503111401c140d0bd4001900315845070712100040d03120048105c2c01d0750011500a05540d0003a00440c40c5544100c008040d00451440c00e80c0c0c0c4030030103e0440d0150741084d02c454040510344407041d102400280f1a170801031100460240c03620b00709480d0940c903405051901d41c802c040707000010380341110603001b0300885802c00c40b13080c2d81c440c445802980101240802c3c1402003d0802011512803020b40d40002940d03002002181818070300152140558001854a120311803009040444544046682c1c40a04102c011600540742810350041c21034900a003140d0410440ea401046955003140c2200d4008109442c04280701075042071250364072407580d20040c0c0180c0b0040540390345880200c00b40090f203030103c030144400014405400d036198000e075142e001001c000c0001ca0002940c41c0e1111059820 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 21867596 1250 21866346 21866387
    0x904050c0d150e01050103050d050a08010b0c01090f080307090b1c0e0c0d050a0302010f020a0c020f1807030204030510050103020906120a08040f030b250f05070602160309060305070c03 81
    0x100b824003000796840242da0107810381d1140c0050040160501c95545040687d1904909068400d08010300510061081c018100c40001d206100ca00c1c083d08565071140e00450003030009146440c00ca141036008032000c41c0001c3d265203000ca0403500840032582d070103842000b0301c0c03c01c0742c0d05030b12407009080640000c0700314442c03c850320029840d070200340b880960191000e00214050307401c02a00f91184851031040c024070412010803200d81080c007030116142c043d140000c10151110100c0c0340080f415800e0151540034104016801d5819001802582c2c460f100765074504118101c5001079820a000095200c851180000c81a050200144200c00141c000729124004251282100380e84180c1002442019a520520500400743c0d1050740142d07881444a40380920b180d01c0c0b2824103c402000001c229448000760b540a101c0c5081e5051503800c12030840d41c0714486481012031504c060802c40108690400c006162070091040a2041200303803201c10b07903240340f56800c803540007031103200c407030002c0c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 21868846 1250 21867596 21867623
    0x6061e0405130201120e07140103020c01060803040801150509040b060607060207050d0f020609071503060513060e0106080106050313020d0f03020c04050916170118080304020f0904050c0d 82
    0x40ea9402824050240d2a040d03115000003800010220b102c0c68100072a4242080c4440d205803000190003001c9a8080c010084480c500c000120080d119030400a8082d60034494041012034000c0000d00484219070002c002042d0b41007689200c040c49413181503440000c0d40d0000c0c009c1240601043d5210030f000f00164035103909552140120b800403501a655680048001d00c0032540005650419901c175000901c1545003200006030ba03580d01340203842c01881001000200300780641c0004000c0c000c0103040359122a2000c01040051541d88280b2681405090000628501804009042c3e13951940e4051840e5540036030f50311a6070f5040310880e00001003411240215a0f40f0100e010080d210f039001e0300c0b181c0300c40c07020072054550213400c100c55a040a00901140c4400d141003004640d1501a102c400c00d403640200da00520b108451001140c0d06004001d007000070300310046215520860b054645a000310003400040e1008490040441e40400d0001446190030320590180902c520650304004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 21870096 1250 21868846 21868849
    0xc040f020c06130309090605030a02042414090c03070f0e0307030206040e1006020c03031213050303130b090102040f090203060a0f081018020604050904030203090402030103030815100206061e 84
    0x1012a0000c030359485031290f070030801d80d00c030503d04000d1010b0002071155506082c006506c3c1e4048581c0280f24a0740c9513115407070480b0b89540314004a800704041440c86540765800c0d58248100d031541c620a40d0b81500007120182c40206036805154207075105012507000440070303034144840d0841c8680c90700c14039000200691780d0000030000f6001c1c40c0750031280341c1041590508005029000002990040a00820542c41c0001604d0318841d04080300940c80d1200c3c04010142c15841c0005400c134040003080010200c4048000c44180e0710030710b40c07900c40381c0d00d981801e0308078001e500428881c250300300e5041114104540195400c01e600802c50804a952004900c0f54040c80d6031005407540c200054107110800e1504c03d034034444d911004d450640c80600d500240d4035114034081c4a100781c1807240418203041c401c000740c3e00c10f10b00241c411580d030351f10b900300580039007000c0380ca07508115080c0c1000c8502d801c204c0c84103800403040e41c008001584459080007503401408032101c000d9440394150240c04e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 21871346 1250 21870096 21870103
    0x601050c071806080f01060305030f130503060c09010f090302150703020102121807050303090a0306020c0f0a110a060216060e062506050c0301030507120807081209060105010207080c040f020c 84
    0xb80310410b00c000803114a020b00072414002c40c40000b07602c0ba450560204046040030003240e820701e080724041c0390f8840041104850075841608456010302c60300302000341000aa00080c22421001d03200c00300e501e81114000c41d20007465010003034120014800f441c02052610020b003540034460300000d81008040300b00b0411441c0e013114a074043d0501d141e583c41900e0001d0040f90013400c4c05801031440e011141020070324008152000500b07140c0e0000e890b80c40080c0c103000c4c000c88a15403c040e2290b00869003440f115159140040c00d05c141080d55000520034000180203d00080001480413414542003007981e1400305104215003101003044000018003a42c550b091046030520500800d5140341d00b040b104851005203581c540b581e0810050000c144000358040858005a80d511110320700c91502c01d103d4000c00e41e009102150201e1888403e01401001c01d20941c0804210b648d96a81c4600490303031350781148200c4101d900003030103820407800c1a0308038030461039130508058908080b60044a26 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 21872596 1250 21871346 21871379
    0x40302060601030606050406020a1101020106050303040b03010e0c040e040210030b03100617030a1d01120f050702010e1b0411040803040803040602011b120b0a0b0c01060521060601050c07 82
    0x140c0288040149668242c4681070140078036150003800d050501c00003075910001c5100182440030031010569040c1e10035080500900800381c1900c0d01d440e035904204040d1340081c00751310419103030900054511909007043d582212b07000d2800880700c3d111a000d10402e0900e01200e03104040d151243c014151320100240c0d08038086003200020300619049150920066455202c40d00f90410040b0196882e4400070b0702b594142c6041109640000c80720060710103180c4014003c1085080c02906001d9514643c402803103024a5002448400300401d90381d5103460b540b00c0d0448424900044410701030516910000307580e006209058549506d8902c81842e40c0c102e039010207050791001500380312007982030023500f540018056001c1d0125440f40c4000e40007059001c82e4191060303403801d56281035940c9000c0300340200308511a06d65154203081c44035010f03000d0b9000b054092049207901d80802182c11405010700c00042014065540350407004650940c00512026041d205d1814042070302d030891b409082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 21873846 1250 21872596 21872603
    0x605060a020a020301060f031106030711100204080c19090209011709010501051809060a110d09080d0c090b030c0a0c050304060c030e04020c10050703110d02040302010e0607110d081204 81
    0xa000c2c8100e20402d03080d40e90b240c105c00609441010100005604402d054101c074008844c003645954500d44110343c8002101705244451142ca001e82900229030750081c401d0340e00c0d00d000d851014038550203001401c01e0210000c559003140315410043c40b4000d6003e0b121400d4145070100844401c4000c100c2444016905000d041e552032b0010009460641a29409164410000c1c0c42900d0b05007111511000001e280703c2c1d82645400d42c2d00440d0a1583c1110942c1d000207000b0810f000860074034052039004180b958852a242c460001640c90242030030000716a0f41c4aa55840e5580d01440013000b40c102203c0711040c000d8081c40e5400081c0280060005060160341c0c82c16403103000d0030028079884000c4c400780c3c002c40c4100f01d40c0c030034010702103400c2403070141d00301010070252a41642180140b180a050011030000442c60000c5104a80c00800450b0300036600c01003030800075010480d9030722440c1802400310f03034003031590011400c0505d032040040b4001d0070340c1030421000c88040710400408032800c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 21875096 1250 21873846 21873853
    0x7030506010314060f04110103180209040b1803090f1314010909170306090a0902060c1002030a0f06060f140f0d02030a1508070303050c16080703030e10050702060304060605060a02 79
    0x81d50078031010450950310048980c014210703810b154813441f001641400449041544800600b030a8003a0401c0701301300554003800e8414180b52a0502c2200c02c04161003018102405201c1c0c0381403d20000180c40c01d449000b030142e030b0301243c007200304082c0c1d00602c0e80000655491f45d0070503880b5004c01c1140c50007090f20324008188550103103450342c0241400094500ca0410610901c5500d8585011269003e165078200081c100194000580140107061106040d8480e110b044a00030820760095070040d0f00c800010720800015181c1c03401503c590b0300600000500d101030442250384101040040d11200480301d0380707001410701000402c1e5008050000345550008184140090140f241c600601c0840305c4a84040341000da04948944071403201130308000c004900c400ca41c403820700a8128003001c000161403c15030f907c840742c0d100c4419100c258089000000282c03130381c0c100360708040a000069554907140ca800ca40c208040d03504003510645640b03944d2007000c00d054407824002d00d1281d0054004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 21876346 1250 21875096 21875123
    0x2040602100b010819050406060509070c110a1203050a09030204020706050105010813080405060f0f0a11071a0909040807060905031e07050307020f010203070c030f060615020d11070305060103 84
    0x504242c4604180d030b2810400d1240400c141085980c0070219448811100403e10380c54a0178164080e00181c0c2000b035015100c41d041c00710054200541030311180c402d0061a01c09102c1404000c5515680e02c99100031488914800340040e01c908014040c002e59418031181c42d90316a00030404a81045000700c034119544d00c018080c81d0b0300003455036402903400450800d044400e40d1607207000c0c0503621405025860200c0c00c035070098121000d413040c2c000c21302e1506440d01c003080d8004084000908448050b405400004181c81c110043e5001141c5a04082c0e40d141c14441340503c20f00043c0100296010182032100000152031030041416a034011002542c485011000032560b101c100b01409030361035003c020b00000520044252184070b50110785042c00da884a0005030f085100f0b4590040ca091b427010f00100c00c100d00116a00040d501401040201e50345440030101010f001311240c5001da4081500002810300c500b03145d2240c0d164a800317031400b25070750303a5910745090f00a801c1211403003040c40c013 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 21877596 1250 21876346 21876373
    0x507060201051b0310030201030209031905010603020f0315010e060d06150f060c0c0504020711030708030403050d030209090f101503050105030d080601050a080604090f0311070504051b0310080102040602 89
    0x200f241c0300c4084000c503155003444441c40100020b140f0009050503004183c4181079501400110840c1c43e0200c040060441c403450098001c050781c0c00204c0c8078141d80c03044903090782000501654184032070040064641d080c4003e080c004400281007581c89001200c0641c001035490055510000c0034039600305001e0b003004180070704510b6a41110007005404070105002c1801a01c04404603241564016030b03500c0d460402c04038640e03141040311740500c02c2103000145000700000520071207004000b82d0307040c8540f5080c214180d106042085a002184001003a0111280c940480e0003480c5401c00e058401c2d82e6030204101c0c41c1c1c0b080b50b6580480d50303840c01044581000d00040c640c010703d524000300346d40350000004c5e200303005000c92a0108401c80001030000d440301c0d03014084040c1c0040c151143d041103880c1c000d140455014514016006001d400105401c080c01b0316030042e1002c0b1004c400d06d5190070031401550300001c0c200c4001d042802d5000481c040d007840200040c001c140d0103440340d4030070140b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 21878846 1250 21877596 21877621
    0x280510020309010908030f0f0306040b220b04180201121410050a0503010203100e070908070b03042f0d060b04050c300402040e0307020a0b030109060503010513020f0a03050706020105 80
    0x10b001740a150010020280220585401ca440c003441c49400303c0d440b92901c1000c41c0051080b0900c2942101407a1280f5805141200c103402076555400d109014420860f418001a29481c00e01c02103107a08500b58200150b001e480c60012011f00044002a0101d81c06040c0c9405003050314001d4540142d840f0501050800350070307080162000740d0003503295041180e011002c1c802d2504c80c000000b02c41c0c2c40841c0e052441042d00030028682001200c42d20f40e00c4559800380d60b03009640c1110207186444202d44203808040740c003402c0f072000b000000f40408000c8103001940380640401c40d0301d10b54035030300303000d0f180d0305c078405d207401642c180140a4559104034141ca00712010403812049060a800400d444c9514100c032007039200b581650003103802803451103210700d1800b030500020340c062300070000842c0b2210b001014604803243e81070700344505a41c2d9014107003252010303141080120b03904600c0402500f0540c281481344c02010b040342c00f9144d03403034580a05240b00d0303030000701c0143d44880a0200320344404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 21880096 1250 21878846 21878849
    0x1e010b0a030b090402030318180106020706090801140703022511030114090613080705010e0c0103060b0720060c030301080312010f05100f020c120102071202010b2805100203090109 79
    0x183c40e601803034103064001955078011500c01c1c0031790b5a01994000c08035150031403a64205519098001c1107940c45400107034680405000d024001028520002443c00050007000000607041155000e161100030044000e03501c684004180300180d480340c40c8148020a4840d0310303407130103020101030050783e4008050941d9440c0203014041d8502406100c0124000300e1496000096500c6554402d0f10515210806020b281000307006540303030030582d0400060105140300f00c04000d07a0300300689500c5602a84036800b4140b4060715071030800469420280009d4212100c10304000c243c0f50809503000c20346883c40d802600120850b401c0441c0303110f214900b680c08140074200c2c03200c2100c0316605020229100b08010902c0342c0800503940c42d82000c01d0b00a00044603072120141c5006214144403411a000c0c0d4000c0200700c07940e40b0000c0020000d02d1041c03107000b107048401404480c540e0228002c40003041d800f141880410f0081020000b520303a00e51515030801e00f05600507540301e82c3e60800261680003503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 21881346 1250 21880096 21880099
    0x9260c041b05090d0b010801050711030315010c0203030405040213030318140f0109150c02031c0c020105071a01030c05040513050c0613030c03031701060e010906081e010b0a030b 78
    0x40002081040742900c1e4103045900003403900036101c000040000711011160080034040c018410000f1681d0b81040d00814400d02d155181c685116141b030701015542e2000301d5804e506500951851001136200350900c40245000408603400c060701e96000030100e038030417507989605030906c403410810540c000f043e00c0c1250f00540741c007548440c84c003811050300f00300c0c180c0098032900b41d200d03031358505a000f103110f400602040100410702440000000e00007280703a140581c0300b407040c849841c00c29072030030300b192001c02c009076030b00144503e8550065400da00800c00031900382791480a4a01d44101092115000790b00031200d080c14a46450280401c83c1c0740502901c50405400100d10b010038000148034040d144141d41850741d800406071003400c40021382d080280141c0070f580c400014103070700402c140c418190740200c09240703985c0d6a500f96425100c80c54902d0100e5107942040003468011b80c00582d102c58501515403030340400f14000b000d003d07000d03040080c500c01c020441da20700960511420b840e2040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 21882596 1250 21881346 21881351
    0xc1b01020712030507050c01090602091206100e10080d020c0406050103051005011209050102030f040201030b030a030f05070611030a0609050108031608030a0905030a0305040b0c07030c0b0709260c04 87
    0x89075202c0d405181c907045001d000f45901e80c4081000d00c0d1245040780c4000246038001c20001d440303460020040c1d400100d600d84130b000c0384858140c0c0100003040c4c0602403191841c11880c150719119100000800051070b5000d8081803401c001004082801a50805c642c25400381c0700c01641601040115401a003186040618180400c031000d0b841030801c809a403002d0800c4120b008075841c240000d0500c0440080c142d500110510214014044105024503c00d89044c071414840d0b20601da0384406144021700010000c5902c40d6029024030001c0010784d01841d4045442c042c0301d4007400050b403007661807060f59170382c9081c1040501054800d2034050010306001e0b514046c80100f4035035040c500980e01408001c1e000012a11001065200010040d40308082d00d464464180d0041c0c0280012a42903d0b40c04031500000c45080c4001c045581155158442440240c0340b902c800c081b03108010302ca00240140d1000226256080b802e4040c40f4410900c0402200c108a40d400c9043c0b8600c3c1005900030350 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 21883846 1250 21882596 21882607
    0x1f050712090809010c230c0a080303040209010905040c3302010204080c0111030408010518010506150d0f0902091303090504060303050703050d0f061d0f0702061512060c1b0102 77
    0x1410303441141d1441e1001d00e04240003142e241040c0c21007000c10031000000900011602150110100f1071f0740705442c0890b1401001652007500a489100c2120000d500103e4100180011900c0e030307201c0c60700580194a1040403036220002100d03e407103a4043d1041d140007421402d00e0403155100324442e50f82141c0300a508007441d04042c5079132460030012007414030100c241e4003e0343d070300d040042d20000c200790701c000e02407810181e5001200c01980e40c0700308072030750804001030f0203800d00c141d024083c2005480700614024132282c0c0c81c001032200c1480d002d030302901e80e2045070160f660704020601514202d17140c070581c0b0100745805480f038261070340158000c5051210030804207410505840c02c0a4060070b100f50f0f180c501e51401401008103902406081c0d142c104049482d110014500300d00460341003042d13810741c84084802d460b49504503042d000503800580043c502c08204a01030b0520240507091003414003500c203495003020300131a52440500804110410000d00790344000c0c0546400070021403601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 21885096 1250 21883846 21883853
    0x706180308010b0d09050d030c140a0c030305060f0d050606010315050603040605040804090911010806010203070c0504020a0207081002090306070c051209060c0a06060306060504140f07021f05071209 87
    0x1680511604030745000c08544c110030700500345c001c1e0305242c0e030140585040c0e0715030b803202030f0003401180c1c10a4002055850008400e5800200715040c000e103645030303404542c04507541117018040003062180c1100c41c9242c3c03070f0014bc03117000c40340300064851009400e881c980800010111560f880380b004100100c808200010b803a07800450b5002600500042829511414515a03522880c1e2080480c41d203403000381411302010221410100350300f41d072400c9403621800700490b03a0b40207804e00586074258001c0100040d2805034001c081c0070819005071190b06a481c400030b81440c801400c0c076114242c00152960796403070b051040541c0842d6a060000281c3c0e10354031840c2c3c1d90b403001e162200d00b802c0000390601b0303282c0d036650039628a0f0001004564030143c4504d4035101030050b9100840751142020004501441d060042080c00c1c0000b61070364180796103882e448032140c03034003030310700801e42c007402607000d01c4007040d120142185540420003086900f820f50300200184c7c0c0c400c0c4040e99151502c031901001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 21886346 1250 21885096 21885107
    0x4060b070b040f0f0503070c0914070c14011121010b0a0c050106150c0308010b0a0f050d090209040f0c05040504030f031a060a11010515010207050607030e0303070807061803 76
    0x210350808030012441e40c661800c3c00120004020113843c241001a64204104000000b00340c6103209580160a0681d01d0305402d066442400b43d60301c1c1e803051040050141803240803100030850044600d5030702501142815070850345201900441c52900040080907180ca8600d004144040d24600c1b801c20340c0750541800c4d5500074200030300c0c2080018a058000d0010941011024002202070000701207440e0001138031108800300201d0108407601d0001441c44041ca0944600481c66100c41c0e00308000d001d011115079001d40c10401106a4854030b000150b20f5058603144980c0c41145405ea40c0c0d61181030080d2598100d5029910440c10300c010040040d40c803030b01c1d80102100314140440c940100414a40d144410724442507004800400d0008a20342d01413401034100d400d450081004d40c03206c401030080503c0429482d805a0f010541c10000c6040c04030081c40024000e01d810800e10a10600090031603020b500d0940c0c10401c0420b508062003800e10411401c1100c081124060b0601a41c003c1d00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 21887596 1250 21886346 21886357
    0x30405030f0f0403050d080610090302010806060c01061703070c08010606090506090f132906041a04120309060818060403030203060d0501020301080703030e01020607050405040c030207050102030a060303080604060b 94
    0x15182400b094102d4600301080a6901071540714003602d800240c0340000500c1000d0071144148156440d5884140460040c68040e050703940680d200704072952036a0602c600c4d9804030807285855035940c0000140606250122003021903d0701c00307155510083c0c00e00c40a0102d0f950000152640b41c19410059a0781041040c0d0817144103032203281d100e100441c0003514001c84c800850383c00078140b99401c121550554480e0034104c1c40c1c1d1a088446941e07100340c0441d4012500c80b0303150403100421051150400d2220805250505218854503240e20340c404c41c2c44001031000b0031000b00b44081d01c107006144d000f41d00c49070300c200c207107450700340c0440d03442a520398849000c0c00240c14140d000020441603200d2a1840812a411038003d5540303581d5092560340d00d41030b62200341d0001b41800880c8806601c040313002c0380581c60725910f0f24200f5003401c1c00c100091040480c1c52040c56804c2102d500040c1c800e001451040d04038a1000844615600340605802001812030b84103524200e810320444c1000c600356403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 21888846 1250 21887596 21887617
    0x3040e0105040c141206040510030206070f0c030f0302060a14070203070b07090518090d030203061e030a0b0a05060102060109180305130f0b030106021501050907050c010f0204080102090a0b03040503 87
    0x2034802040b10250313000c084a54035410396880001d2002c00000e65401000d0089405440030000d9944020320203510a82c2c9000081d8011000c1080c1c00103d0400400d4440d441d004615986516076a44c2d0780584100c006042100540c0100741040318105180c45010280d601c0d540d041d5115141500c802512445503040c0200301d0792481000c2620351b4441c840302c2c400f821024021515078608003204050f444d41c1242c0c0e40d040c2d40b00301501e0028542c40b90003a6802080090902e1110140d80d09607001d21000100c0c2058040c46120505400f04080540d4507010f039040307010004075030074002c00083c248003050700440507150400b00b441100311481d070962a0140e416150554a68000a0480440f25426408060680a00d01000c9401c82000c001903040b0f5030303503070226210904001d807100700002d024070071640d2014000000840080c06800180784009141000240321840c001400f4220703041608401ca6aa501060060b01401e001c01c00001610300c0b01e1200382189415500e546d9248521103200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 21890096 1250 21888846 21888851
    0x504020705121b0105090703080910030f090602040602010c080c0f09060715060f0603060f03031103091206090f030304080406050a0c080a0f08060f030706031508010608060402030d0203040e010504 86
    0x44003803200a20100301d01e0319140030655518040e4504100c4600c00c031503004443ca501e0240890078522001403040c00301c0760b00541c810304010b0f9180c208031600078154400c406268550b0740c1501c040d6903502c9045481c03032146400607220390a10030000d003110b03019084039080c0090001406142140901a1445008038400c803542c0c1c3c14000b00407400300d02032100001c10414015100f0081c011090b0041c100b610280210a40110358503d130840c203503810340c407030003010060244003800803d02c01c4100145030800002120310744030b811404140504500d120361890b5412400a1100444041c0402e55000501c84020b50a504158540d034040348100d20420092110005c4c8000c5034034001c0310402103064021144540701c80c1480000f410720120b07542054001900000060700f07500e0400c1d035200901002500403c201410003006800411801c0741e91f520590352404009114402400f440019225181c098282401e0900c141741c5080480c00c0c0c03c80030b5400c184028041c14891034220f030704440046a02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 21891346 1250 21890096 21890107
    0x40b0f060406050d0606150903080405060f04031401050703050112030e100c05071410030603030219020f060d0209030c0d1e080f03130311030414061e070b040615050a050402 76
    0x140040182d40c1c00590481040010401132150030b60149003110351040c1031840030000283e04869094036808020320040080c04144803e042081c094820b15400d03051003032500b07444c2d40350100c0010209a071400c840c0c3d100c0d070801030761507498058280108050141ca43d54030110782c0d4060106140410b00314050140b1001d42c0044034460b00100c407055401a0a540781a6280c10f00007070344055103940300380580c00d14614801964428420703c400c40381c056001e40728000321121000103010a9a100f6070340000d40d00c458a445550f104010464240e0074072005a443d03100da8241401c0c1001d41032100d2160003100e0502010031501828640740102400907a24540800e01c0c1081482c003980c0c1c16450045000703c200b01b88482180e0303902c00c1641c041e0715000030341d0030000e4030b45030390b8411402080c14400c0c28104640050034500041c04078105603401c102980c1c01190812503060300510703402c0c0c0d021207440c403d01052090303a1042c0c807120508406044151030504000c140380e0031080c85090301a6600003503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 21892596 1250 21891346 21891349
    0xc0c0d03060f18240602070f0e0f060d080c10050606070215031803040f05011e020d0f02030405090a020909090f03030c0d02130e010614130b0a090e0f01030c060305040b0f06 76
    0x40194450020784d8804401852041c880658901e43c1c000c04000d4800c0c000c0c003113070329030340b21003a41c1c1220322414130210345a80f040d02c46010400080e00c4250440140f00100000904003009019101c07604030050281c2e554041d00401940c0c030181c03035140165010402d000c0513072500605070f1102c0c01c50000b010f58070707118610042022000c21115400d1400702241c0814212495001c01040300d4003680e4a1b13040142e02c020285c2c1c01609021a0000b40c0d01442d110b807101c034003c0d140c00c1d50140c5940141c03403c06548001040c3e0042c0c0403641901007580c00036141499242c010500d0f500312a0742e00c02408100c0844841c1c2d5a2488060001c4401c900003046181c105015501210f41504e03200c110540c0365030ba110f4071280104002e0240c00b01240a4424020140c070b60903013074502289205540b400784518219903486103911a02d00b500821800d100080b655807050113449000741ca0a0380104240e61560804084020180e04444109401e10062201081003a04000d81007002c1804d00340043d2101320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 21893846 1250 21892596 21892601
    0x7020d180315021c020712030501050118060e0604030204061701050705070f0201080a090f03111212010b0306010504080d05070302011109060d150f080c1002010c02030a05070302070b030c0c0d03060f18 88
    0x904c4000207800042c01900300020007801041201103a2000d100a907214801521918070051880d0b907598900980ac00a441c49240314144c0e43c0c40290070503282545980105007603c6264108002440004181e10301c15582481440d900070054079009040c213020350340e44e130400c1c145d00030080c1c1000502004950345040962003c02032035441002650001003600d00a094503034544011308003801201c0140400042182c01c844101e000c2110b21503c1340e01700030690b86250806013105040150a0001194642d8204800744601d03219494250310f60f0b20516009080d5200039008442240c414000c03081141c48280641e403030724807000303004541e0704001201001c80005076070003940d01d15204000001e40c1c1d0705c04280145080c1c810f4603140821000c3d004181d0a83e8442600c42006900412025800750303c03640142001600c05d1040d0b64001d0f0341d5002403210342d0815031b5008152007000031000340c269402c000c99500074aaa040a1141c00c3c604054000c8442940c4100001c0030070440002c0c02c0c412103035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 21895096 1250 21893846 21893887
    0x40b0c01180303090201170c070204090807020603102c07110109080a030c0908010501031a0702190b0612010c080112060b03060a051605041406070303090b07020d18031502 75
    0x1110341100000c5039082c000c01824000b4401d074081840da00c400031003140c0914060b4410303203680160a182003595030034080207058041041e00d04d28030034020500140d41e443c00070350142d8090044403c4107402e0003401003210580070725000b2440f07580c500d00c85100d4040b08540b54040d2841c2040c40001094030040742c00f40c0072035a0002c000b8000024004412609a48040c90000c030b642d0f248a1030340d45541d40d0078200c0d0403c6c08086e2241c0c9503042002042c0c00c0202d07095074013805501c15194103c943e001d048a801c2c180c2902241d00b00401400c0140302e040c070060301c09041c05a00000d03c00101204000ba000203010b000d12258481000c10079014000d84e07400c4200f1920000e411500286001d01888c00108815035a603001c55404482c0c00200742d115900b99001d46001c64906030001d4221030400400d41e000e440220140764480c8200408a01d441d240c40303105155540240c00c4101c6401d9006181c0c00a0880c00380700d103500020280085011705c4944200030401490040e0740304c880780c10410f080d0bc0d03035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 21896346 1250 21895096 21895121
    0x310050402011803150b0307050d020405060105220504050f04031d1206130203070f0b04060e12011a030105060d030c08070c0e01090606030f05010605030a050411060705031306090605040b0c01 84
    0xc00400801c10140f140c5c0407a030380b800c02104101e01c6030341c242055114a0035106095101c41c0302480300700540b8043c0c0c05242c0200c0c050508500d01000300b41c52a8212801d22130314202c8450b40d150400032030030300e800360a0303000403001d0f0b0290251519035000780c20030074080e500348202400c1503480c1509440b500c0c10f0300c04200d0311408482241c0790a07850441c6000788600304902a0080446c00a12415200e0f004030035500d040c1e64035801e180c2405021a030b18140549000d5000f040b14081500f46242072156507004034111030b11000300071058041c0342c00c0d5440640503600407903501c4c40c1100802d501000580c2c84580c05030f0060385c1c40f40303107003004447c20349980c03c20f01b1400c513800000034002c40755900450496000d51410310043c25a03035820001c562003407003010080f60302000011090070150340f00320360062061802d525014044008520f5540102004660ba50b10010740c80c01d492a2264071100103029034075004283c1410005c00800e13b00a0b1311445048440c0401d00840d404001e4028207200f915 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 21897596 1250 21896346 21896387
    0x601021e1507050d1505030705010305010303021e0111030405011d0c0102120c0f070e01081204060c12030618061707080307140c03031912060f060507031b1208070c02031005040201 79
    0x84d0004840045c140500c01c0030b229201c0c00f0000921075000e0700406040f81d406030050040c07202c90341d03000b601d0620400000541e6550b0b8411180140c011a00518003131401a000020070140107080e542100000e0000020301d0390040e400200c80d6a0300060101d0400e014448050711002c0b1009254581400084403154600507841c011614594015091703040340c2c001e00443d820240c0ca40b289940501c590f0003a6400100e103c04000003081c000e4101200008851034001080759840410b12480801d07180302c40e090742d0b02c03201c081208038418403801c2c00742003210029104041c5080802980d911070a4402006603981e074401601c902000d10032031110500c090f050f40c1c1d40f2400303e02006200c00500c0c691001107090003504060518032071081c48160b0b012001404206824114151031540101e2022400c11078000c40b040c98084000112260f05840f03044071006510349860060b000d140020010400c20406108220250390001501d0901100240001a10351114001200c2d808440d00c075180e945d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 21898846 1250 21897596 21897611
    0x4060e070203120a09050a02090903070c0f06020d090b040509180303040807020406060807020703060f020903031801030e031e0a030f0c1d1203030a0c180303080601021e1507050d 78
    0x20740120061503c3c0c100c079200c4006664031818030f03008440034000094501da208029000050404490841e004540403080b80d00340900c503603c1c241165495000001c2c000340f071150400846030104591009040c003414208010fa007441080d20b0180218400c091240c07551101194003410580c0781da040c401c03040d07400d0b83d503070345428203201d83d5070740c48004200d004500d8820002400d074420792296001d00b50683c09881c0c076a1441c1c07600c0001d410100e000c12609907003003021301c1e1507940070401042d160107400d003489000d01c42807002500702da07580108000990010440d0702500d041000c401702c811120707000401c4e1100c201c00001c0340100708003080f07200e10b6460204210a070036000f03031040c00841420640e1902c880c3d88903060100080c0b501f4802c2440d41c1c000c0c004a1202021a0010803400c0000c0c94010341c203007550b146184052040e60b20640100311035409000255078148442a560281990303110650482c808405a9641002c104c3c00860613403000401d8207075200f1070032500d007141000340c24860074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 21900096 1250 21898846 21898861
    0x301060810050906030d18050307270e0a03110c060f0d0501062a170304030f080903070305070f0309030c09060f091103011509030b04080c0f15070c0204060e 69
    0xda400340c80d25041258180340015541c039241843c0c2c0d10450700540a8020031504120a9607080c142d0300a5138200c020115020499840c1000100c008100c0115a041007203102c3c0c600b2941030707418566891659041612800700d00d100059400c4401d07502d07183c05200104491203150500300d40301182c0e07a1059001134003aa4442c202005080900b0a4040401c85a603941c4026640040c400382c15949608012000480c102400b040800740c1902521700c003003000c0b001ca001003116500440342240401ca05484580b0f210b607100c00e100364800301e40f600861901c28152009051401110401400a640f1940050030103202d07121000065034070840c20002152100c2441002e445503000e101d4005454102c00135885001e4003a2104c0c1e64035885241d480c503420250441c20442800c0c1400c0306100001c00000b0001e401140c0c10303072007140606600c940b61200180d080e81007401030085900c0952003540620303003543c000038055810490358100903100341814404500504411b901028100f000501000b000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 21901346 1250 21900096 21900107
    0x120c06052d10061202070506040506040b010f0b030f07030216081b19060e0a0b071706010503062119050705030705120303010b03060103020903010e0708060603030a1704080906030106 80
    0x812840d216034841c03040c8002650040c003101290950000a0640d004100300d07800390020401052a030440589000c0e01e68848502d440700c182d0f800c48203a4003034000c1100b4401c0140c410b5002d014403c520030000f91070104a49907500001d00710707004450070b8101150001d802941101c584904055489000b80b00c1c2703042c5012140c10500d18201521109245030a56200100b0107400d42c40c0c0b1202903c1c102e044584402c402450340c0500100c180c86621603103008506d40d800101d203d1061640c1d0320b0100802c40d105040d00c48409410141032080510600c085a52030448140c80d01e25a203884071002d80a03403442c0b41c40c3c182d01d40c1d544c9082e004c00344000300a003d4042007840550b00c0690803101100e03561000d111030b000080d501030301c940d0014030040c84404040300055800580525025041a111a000030708584030700c3e142041d00d6110100400c40304030203000c4264000c60032800f450a084400380091f0440d140c400403011100d411304c0c0050104070b984426503112545c0a01896129078480c00c1c081c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 21902596 1250 21901346 21901381
    0x30f0d02060702010b0306011404140109021e040308090103200a02010501080f0606060a0c020409021206061e01051602030304030606030302070801060f0320010306030501050a1a0f0d120c0605 84
    0x103000745400900700c0ba00500601c81025409002031003668a80043c0700c00b080d015524107584191148034000c0c0d002c44414009010b0030b080000180c0d1000c4028100110513035040c1001c107141002d1004201080c01c40059500c099020309010039440c0c0e0701009103a4905030403254070702c58400441d2100c400b030781c15804070f81624042000c603203907132000658807951100b048034016840b850421410f0400da01c14100c4d01e000601c003030008100c0c400c1075400200f180c0d012405100b5140d10880070880d5504e00b43c2c4007611128008880c40c138a0b07800d9040000c1c481d00c520703042c2a00e4a10030311803201c1191810401c0b11300a5400c841d0411440341c6918000351691417034442c0b00020f609085020540318201510704003241e0b440f8214061544049120103000e5038402d40c22814582d80e0038000000c07407000c2c000c00f07102e81e40140000401c1c1030025041c1701e060b1802c0410b54000d022444121046494200c0d0302644243c100d038002c480d00000b81c01c11100403001d40c130010400c0b82000180020310b62070005000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 21903846 1250 21902596 21902623
    0x5030303160e0405090601150207050d030c03021c091203090504021303030206070203090a06030b03010b13020306100509130504020d050706030507090e040b060418020303040b030402090f04080403060b0d02030f 92
    0xb00003000039420081618001d8444940c5d540210740100840c811160446034500b070b050054540d91551900040d00b10000d0750426004202c40d62850001c0580c144101c85003003004001005a80061102c010050011400b44c1e040108000f1750800c185805039030382c0c20042000610941d5542c0346140c11034203005480c030003140944504008100042d00102c01e45040c0da1014040e480007500d0b0000840c01781c040030515940655950f262036200703481e4580a0380415100d0000940ea0b410191705102c1c10120042045040240c02d2201036081d5031050781da0005000300c0d50b0042203540b594000103881d940d03083c200078043d120f200030008002d50075400c400d01c610746a4456610a82c1e5450510040c11000c4900070518800200001d007a454140c1c410603030542e41d450060782c0c0845e1039010903c0d60384150001209a1004020403046160000c0c041380d002410811201032811302d07a075080c0c0d1034092400000c06150f1074030b08190142d00c90150035040f0781d03001011910340216181c05140c0b201c000702c5810 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 21905096 1250 21903846 21903857
    0x3040b070c05030303091518060421020708030f0a03110c1018110103090c121109010501030903080a0b0409020402040b0a020105070302040503071404090512030a0f140414070503030316 81
    0x141460f0203c10390307101c1d040e0b0001611022208004002c4250402009000044610078590745080d600b00401803145208403102d5014140f854000d40f410307520380026030110341c840b0106100e8408003000ba90392602c08010210340b5065140000d031301030002d40303410094460f004517000c808608002100e60010045220411180c1013078103045002015082c006080a0012220060342c2d52085e800010f40a02411000c4c81160b210898000c02c0b008040b000d0f1000c20800840c001e00c5d1420074819030041109007010080c484043e50090041240140950b800c40e580382441d900c00d84458120803011940100308643d143d80390902c41c041c1740c00003020500198030748000142424064403c50b820396800600a2400f9850014518480c901c0441d45640098851008500044c030411041100a01003036503d6100c0c0740c1030b04020100c84140c2c2c44040d85908040c658201d00d024603410301d030000d03040900f04030006040420b2034034001c6d40c1c0e400150503101c00000c0104000220596520403520795072107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 21906346 1250 21905096 21905099
    0x906090b04030308060d0f1b03030305130b040b0901020906040b0a020c010e13020f0f070b040213060614030601050c0604150609020301081015081606030c03020a020c0609030f03040b070c 82
    0x5a060341d0103603000040100c0e0f007000204803a881c00c58010403089218081415a009803540d07175070012525050880f90f005981c65080c001c068060088550000c0a03170b1217101c020722107443c1d2401c0c03100c0150000d0b040341c521b80003207600d510003074041742c05820000d03010701d65071680c030104200d160b41f21421000040c000c202002645600c18419140d000c2030003010007c42c50310890030035000f54004902d84400d40000c1101e00c4054051902400a40307001c1c441c0c01d2a42e24060042c02041c03079003040c0900150340792010920946030407031612031004007800c54894483e503a1100503078051141049081b1903101c0d00c01000208400c072400d1100c4d98040c3d0406121080c0d4441c208000da000030301610100344c00c04000801020101e6015520760089560351541c540e82c1c4d14800c50030107505152070500e000042c0710510a075500341c0101414440035107000c40c5000003600c4000d4645c080014080d10403080019088010ba60400c41c00c681c0c03000039025680d9072540c40341c103901960301101c82100c0c102d02c0d4000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 21907596 1250 21906346 21906359
    0x6081902010c0212190b1503070504020a0c0b010b0702100512160905191401050a02120a051e030403170402100e0102120409061502031306050c01021207020307020406090510050904061803090609 85
    0x110450221f01078010540c803420502080040d40090303400e0300422600f0304800022038104801d990003024055407090359100c050050010302202141e044003800010010b0060a24406003020780c0206100b040400005c0781100858101d0a81d07440b19921454000d9285400742250070000e00703d509040002d203032020448010f46031401120a40c1016804c403101a95402606400030080d94603203141180c0303009901d24002d0050325010040c0181c0c01004401c1000b0141c200f52641d14542202d207064000c0d00e002da0014500f09200c800507403c10580c0b02040348503034000c20240e2500d20744405810307100c64035030f04040010012480307004070740d84400300c46c0740b08240003008a85205003c4190302c2c000604101e0291000ea1000e01c10042d41d40d4200f121559500c84110044d002c2c20955000e1030340c881041c010001526803d401007960030349000f0a200d01212480c0e5004101c0350240ca154240381d40d1800c042c00100540d604200360429200d002d4400c06911030308010a840454446e002815110038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 21908846 1250 21907596 21907621
    0xf0918010501050f030a09050f060a0507031401030f02041401080a11060708030c07170703050405040e0601050906010f030b04090803010f2709080702040c03020d06081902010c0212190b 81
    0x700e9140842c3c402c0184800007420310008507803003110280c010441019030390b03c1e40d10b000c0ea1091a00002d400000600c4042d00796405041c4c0c00c0102032800340851003110804115802c4107100045c04c0c0040d20000500315211508520b0342040c41c1074040039290307590b9600c1500c1c3d500850b421281c40e0484030840b030352807412034161541160000340250850741c480d00540c0780e07540200c90690b401680c2c00c11446c1c0001c0300d0002802e81c24880d6031007584452900042c40295540ba9030b01d800c01d50810f50050299403505480c0e5036000d0005d1a050240c00d103407a109600a040c1c4422880d0001d0400b0800010301900c180210b04888961034031003c02583c0d0a000d41e240014414610103180a100301c1c01c140314000c0e04814400e0f03001d03845940c500042a0b0000f4105c45502e0080400b0075004103222046d28440d00c5180014041e01010307120036148076032601d4107411207407002414000c482003208155203455503040b0303008490004490424000340001c1e10662194002140d000841c48001402000c888 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 21910096 1250 21908846 21908849
    0x10501110102030f0406090f0c06120c030c0c020114091c050d08090c0603190c080a0b01030608071806080a0303050405060709030201020309011d03010f0e010605011814010e060f091801 81
    0xd08100c13415205c1e03940c3e178400f030004441c3c1a075034030856400050105c0e0302602d05100810041e102d00030700f54044a41e40e0709544242e007142080c14900000e6007485a00542d040090a60910b00b80c0701d886290240b06802d40900301005800c4440002050b482e022120640d0150740d01a1046410010143c2421600e6071411241c040254015019841e21030910a0140d40c02218408aa098240e0074012031130445150059000005940005011394140c1610a00070341510070700c3c0c00e21095082400e11640c0b100305112390480c40401c41004210f0b00c540740d0003600a403107044180c800311002ca09004001d000160ba0a4409000700c00c00724500070b000744c3c4002c003160b5041c1c014504180d02c0d80010758682500042c1e1075031130307860079448400c269400e203c0d00c0401410507000049a40780c10319810300b1a40e0b0360700401d06004c580143d00980c40c06c00c01c401c208840c08580c41d0b5004203109401240c0c0818081c040907002103001c60445a0100f144000c4e11030004191801d600403414403100444a0000703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 21911346 1250 21910096 21910111
    0x6060b0f0403060c0309080d050417040803090618100c06110a170a0608070f1706070507020d050c030304030809090f06010e01030e16090903080f0601090513090209040b01050111010203 81
    0x108001c10010300c55400c44d42c2009250304002400d80501d403034801441d4081002501115559001c10013040b00781030144001e06a015211030a0905119240c0d41d00d00c00d09a119100d8a80814518120313507120115091220000e0150713a4040101107018010905c48001110214100380c1061001d50612094510000c5280d65103c10140c03070803204607400101914145080c0d40720320303001c03403041020818080201081640c860000f45807a25a42c5041a84407000142c0d4000e401801500750f84603041c1c460043d0110b503014140c1c07185180031890b054040d10000d41500004ca0b0000c28026807501600a01b02d00740d074000c0203075072105002c0e101c0035002c4614034049119000b4200c4103511aa0000e032843e00820200c86101d0344044050f0b0b0606440e6002e02c503c191130b49691020558071208003030308045c03d10843c449034148100003810300c0c0c0540c002c07540224058905002600420740240c0c14040d0064070902e102c2c10941400b1031082e03401d000340d501003096049e00385d0300480e0520849108100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 21912596 1250 21911346 21911377
    0x190201020703020607150501030302100f02040e0103080a120c030203060f04020309060103081c02190f020d0801061809021801090503030406050d0e0c031005040b060904202205010306060b 82
    0x941c0d013000640e0300001e100352080d005038080b1038001d070141c0c464240a18040d030000c00909800c00f00c5002603602c603c901100c418014841004064411810349055070303405684180c8450264070101e80610704041d0000c1081c0c182196a9120358040c2d000f035004440c1500d000414080b20701c10301050f88400d403000f1455502803401040402c01200113850141c01d400b803000d95441d910b601050581c0c11046100440e20a0f0300c0118090641000030444400120b0018055515207000083c00b00e0b8414840d01c010300840c135074043c050a1098084a000d80508081151500100700c5040c482c400b12900d21800700340b140001040514000080c1e8048880030ba4500d46414000941030f8050b00791041701a00c07902c9a0001c012a0303a4060001e14403c41e22000c00040d20300e402d0230051030400c0040d1602e070003583d98005210108100034224000e4908025440440175240d6010880c01c1c824481d61084601c05400b4900c03800e070b5607802250480340604822300025031a4114800d0500c0f688003406030181 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 21913846 1250 21912596 21912599
    0xe092406090601180e0105090109061203050d020d0e0a0203060108010e07060e06040807030b0f071412060a050909010204060e060405011e05120c0405030f0606030c040914030f09031902010207 84
    0x40d060760341550228061404c95401c00101c80d403d83c8854030350304002d1110354400c0042c030460400740c4001c2c2c014056040b00740451032501d401800c1c8403119090103000c01c500051100504446a0101c844001d001003042042c41c05103050980ca46459590481c841c0c06003000003c0d251005001d600c08244040c40600819840d1100660307207070040b48040c5401c41c806000009000105106e010f008600640b02400740e4508150546424400140507809203d20a812102c90502d180140c42002990345124091a00c40c00c0c0080c0c5180c049510941d80120b07500200101ca80f4190003500444800f600c0d84121030210404001080c0520300540e03000640300030103c0c6039400c03100304030100c4140c1800c0007413510b082c9040c00c4d2081039040f5406442c074400010204024101000341014010302c4030003800d028200000040c3d00c50b0040600c20744100d8032603040310140030210280b50303105158582202c1d0b4580e90300f82003003221740002c01034038800d010700f01c0d450203068550000c03925503da059000e88480c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 21915096 1250 21913846 21913849
    0xa020307150909050106020d02070b07030c06110702030a060b0a080105040503090103090c0902040306020405010e030c0904140c031605040605061e031b0706050406060b070812060303130e092406 85
    0x103180c1d0a800800200e100005001c1955225090180050360b0146c918461076a01c0030380f07012416804000301c80020442d031400300e1307031109130034007082e81c00307580400d5003ca503421409090107484400b9500d4000e52000404004181d440f800116900f5207170007100c196a0610f036801c841c421a03000d007032a002004030074100e601c20b07440361480e00d10801941040540f42c1460700304036006608221030380c56002030248515031b081080d01e00202400ca000b850b12002150129030a0680900000c00c650800300b5200030901051015080c4240b0180449001203103950410300b50141034130409010b90702d400350110f081c3c1058403c5440c1a181112050046030441002d000d2a0b0f20007400044141c0b022003c04000c5d140760802002a103020f1580801e483c00c06003401d0040b04c0300d5500c005018003040041c44001000c44042d54403a50301450540041da4500340800d045105d08000b508921820250116040e10010801c5014545280896460750130715050f07103e03d03503140c01100030f11000c200d0008103075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 21916346 1250 21915096 21915119
    0x20303010b0703020106031709030601090203070f030c050408030708030f09010b09040b04030c0c03030c0302010506090105030c13020919060314070503010e0711030307050a080a14070c08070203100603060506030a020307 96
    0x405201c3d1000180c1c10b5526248c1242e075001c0282c9860b00000c002654000030b1404000c894054202c202d011461414a004003514640d0003540310414952207081c680003481c0a0420340d002404a002580c3c0e94451514044085610450f0082842c005010124070340d071340e05103d0742900e441c02401e031340b034140c540e03840c0e60742c549500500490401003100c500000007001c0e004030343c009511903120707800c80180d2407030b019003502c0340103021a000c4c00080004200a540001e540780b5800030580d4404903030038040040130040e10900165542044e210403220740d401003c8425802110510b2340d0402404411004075540110700b44c5080c0d0000300284014800d080c008208507402400c80e003060030580c0805801e16066803c11185170020a130081111981c1c030f50040030301a4400c01103d01007142c102104206080040c3c060505420440a00c45807400c00c100001180c0f100340d0000c1c11680101c1000a0311009041c85000032902c0900b03210200d407160030b0004100820541c0140074120403418024801c29 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 21917596 1250 21916346 21916357
    0x4030c0303050f09030d0804050607110705220204031a1b030a0c02010902122d0a060507210606030c1b11032a09160f0806060408010e0c0a15020303010b 67
    0x1880a4104558134403540c040051090080750354480300b60502c3d244c100141420b00c020078180a001d4884610240e5160115104054510440c1c0380f8044015056580410321400c9000030501c500c009808001e01040500e4030004091610501c900c41e540d12244044418074500c20380201c040900104403d1810364110151189082c030000031034101c2900018028400701e007568145401152a20720002c12401e140384100b80780341d196040000c03280d000301d5540d602280c0c1c0904007954a80c04200941d01c14040c4155104444410f401c0d030090f449900d20062980344941d00229103482040e180c52070249803440c00796402e040c417a404425841e02d50755511001c10034819494000c400800103024501400b20440c42070040190b00302001c0c440a101d440d03c2c1c00b801d8a44100c2422002818617603101090703c442880d180340c0801551a02070200700d82e030255802402c405d50800240c002040b400040c00346076050100c400884060f501c82010b5a641222010400140c00410050007100c221000404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 21918846 1250 21917596 21917617
    0x103053d020901050c010f150b0f0904020915031008010b0901120f03050f0f0301030c0b0304020a03030309170304060b040b01030b0d080906040503031902010f0c0c0f020307030803070513080304030c030305 90
    0x524110582e460a82100c40194003070200e65035030003d0310b41e04007012342c03040b01806a150b09e5519103c0403038110b42182c043c5448041c0b14270b80008a6085607181c0b01d000c580d25448803890740d500c0b03041c001e05000040c005400341000940c038080d0708603890300d00210414100c400d4503601d02c020080c5502d41014030740325800140c0c01c2c02820040c41303a9102c00c110003040321028155105403203504607e4800f80c104415440180e9414003031041c0310160390f850b1401070031664107080001e12941c1c680360851044015030030500c0b84010100c104814000150042540070f0790841e0200104030f01800103500710382c03002a04036000b603004201880043d10003c028100000b00900250030955201d00007491580103c00914280004000180103070740c0900501d0580e1501020074404641c010030b0040c4403900501f8064543c07040c6036400703415920184030510247d43c01c800201e660740350144014000f54401030700714032040d02c4d4181c0001c1c03204000c8261400d9a03402060003020b6440c60f2411510707504541c1144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 21920096 1250 21918846 21918857
    0x180c01120e1c05040503060604060b030c0c1c08040614040302062404020408010c14090d03050307030b09010303080601020f0102040e01050d03090b07050c0406050f010206010608090a0203060103053d020901 90
    0x2211450700342d0080d82e00d420907aa510360b6542c01c0034141401c1100141200b401903060040500c1420905429a80d01891a03407550351121240083d081c90180e01041100c1d20300700c40311811041d998030425840c4101e000d58400d0040b6040d111560881c07000840e80900141c03c00030204004e120111840c0142880d0303449400c40180316000018220703072140d03000c113590760b42d41ca01c0b404031a90005618004800a5000700742050000c02c041010030516950003010050000002040c01d402507000540150000d0900207066840b4607004d082454141c80310f9003d03108040c401c20303185d88140222026503204d0100711140d41d180500b07014020507010411000d000803c80302140081c403660103006018020001007202c3d105400500040721120341150b0300403048000d40300c040c2d980000b0041e04413400ba1404226680e40d4164140c00d10304d40a00096050240d07030300010901170005000d1030419081400c0c1c19010805992840d559040a48008154081e54408c80e99807542540030700084c50040c10305 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 21921346 1250 21920096 21920113
    0xc03050a02070b120106030b03060106120b0117040f0c150e0d110603040602091302040b0315040f09060509010f180b07120e030c0c030601050f130b04060806180c01120e 74
    0x1c03484d4000c46010b06400c100000100a51a40750007608200710055029050701e504004004101c2c0300480e040c808207540341d10075108664454400f40310040801d2103e15031b41d0603d86050030215a0200c03041c0c0c1e485540c21004180070306000e012400c440900e03103c841506a061040c40b800701603486043e40c05402241780d070314031601c239600210300c03e901c90032006175079841c02c0080242c810064822915018414042404019090030460390480c810880d0200600c41c2c0768005030141c100610320b018240e041480c0c42080141e00d0300000d0003034203048000d0100f80712924034282180d050421800c5100d0700c422000c0701080100403c0c6403c4651841c19221544c1d8005041040c0d4503100540715060b4000211800c21540512902c1c1240a04a0240825501d0b03c03001801100b94a00c40c2481030212040b400b0b10321805a00c0103003d404042e10520005585a0b081030700c0301b000303c500c0d41c1c0c4451081c80c902d44e44040840e0f44041d0100584a00301c442c0780441c684c800820806824503000d21610700b9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 21922596 1250 21921346 21921359
    0x50105090405100b0705070e0106020624031609060e011409040305070f050601060c05060a05040506070e012c0108010f0b0f03040f020901080f070b040b07080f07080301031a0609070c03050a0207 85
    0x7170107114050310082040a01d004916100200140c3c0005c086400810a204102445031510480b640000041c1c0b8130080d81507000a050488401ca085079581400d1800610748a850b00040101d4101d00344581e65603136202d00e58400c4060705481d0951103200b400000300024000c41c090200a4018860f80581d802140c3d50580b42c80310070f0308036901050f924000c4004208040218a40c04020b0481c18016428555110350f603608029040740144444c4461020341030b480707044144a0000e24444e1581701c45100c010241d0301a2004c0b00e2079000403032580021030703490440d80010b4100c42510401c580f90010340c0710f01101580001c4d104880d40b28614a28001507038401100501070440c42022f85100000303402d045240c030f46194440e1000c02d0050000700306030940641550a9190031a20041c0c0d5164040f00460782e1740300e000d00c02064000040b0012051004000d102088042d0244400010f600d400040114003d022502c05000030070840c29100001d1160010300441e01e0180100c031042e580741c02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 21923846 1250 21922596 21922619
    0x190b03030f0304230a02040b0f010804030e0316090506010e01021501051c080304060501050423060d0201050f18030d0e0f0f12010e0c04050105010309080412030513060201090c0801050105010509040510 88
    0x4262a1170344101d0300301c0103515051044024503181100c49404001e400000038040c0d00d4001c001406100a006050141c1e44082c040140010803150303504202c1502c43c49140c005180680e52280055246410001254000110306074000f403100402d0b00c8036031030501086036a030003c0c1c2072002000214944000080c5003e4003960140d881010041081d604000c14071084a40c075414940c078098600003245020030440360041c1c1c1200080e1840e10072135501f400180c82d184941c8003440040c207000140046401c04070114114000c4044080d02d00514414074100d03569081c011229602191251100c80240740c01d04030cc0c0b00080001d0441091407280c400210700b124246406035a05401c80e41016105240a110b0036000d003d0908082201e01c100f0703142e100c524002c900441c2c0e404013800b041c80050500400c01d9031070201c102041080351588403040240a00410103003180d02e070310710741d40c049000403044c0541030503204180d6130141441144000c000150901600910f01c0000d16000801c9400459 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 21925096 1250 21923846 21923903
    0x1e010306050607032606060d05040501020702030303100807050301020f090108040302011116020109120b010605030903070605040c03050609010605150711060d050f07090303140703110601060305190b03030f0304 92
    0x1d4845554032003172103120b5080910100b14510600301681c0402c2005d40e10201592286c0c840e18100081980d114908140241310f8008065414071006c010072100c1c410b0313000140d05807103000741580e440b260386005150903030041c2123115010303010500c03018540d9480b030f0070301d01d510500038400840c40030b840d903000d41c0342c86e403200200c4060281c0c500d84c40d0381556003025403503009015440e0020b00020301901c4814005d08103000f07181c2001030020101e075046c08104107441440e074100400300903900f424504440e01521074402101c603801100e00180c40840107102c3c22040326070103040d442d50010100c466107901d0b407045a0845408070b980c01070500980b03581c4043c142545d800680091075080400f41100b5402006055008101c0d102c4400d10020f0307404200d0700045400c10030761680780e0580e46030070346100b10102000c00d100e104000000a1081c1d06070840350042c10042c0e210082d050000141ca801e84010710305660301070341300f00094000c0080440007141d002c1e001d0284500c488440050548410001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 21926346 1250 21925096 21925103
    0x30402040b1306030303050a0e420f0417030f040b07050403061109010e0d080f090d02040203160905030d05070b070203160609060513021e12030a02070801050f01051e010306050607 79
    0x240d07c1004095400c622a54038250582070041c0100d41c0585801d503249008040d600c89501c1d03041c18a9a21a001450b0340b02c588040980004950b280c103240051440d001210281c91488074000c00c02d00e080c00010441e4000c280006046540340c1c0c41e82c46240880c10b0147c4682c3c1080303020000000031400c50704c0340380c0141c5100c68146513110050340c001459542d082c40074502c038007005881200054040e8007101d99140c1820039440e1140c2e14270000610000b8883c20180d0081d00000c10072a0195a2011188103140581c80c0d4016840d26503090607514a00e961900c4003050003080580081030402c545030341d00104910481e49040ca81c0c0c28082c0341c4070000107048420b01d80302c155042c1080500d000e020b1384004800881081e0344d00f43d80011707500407144013480e080c0305101d0104015a46400f8006d48411505108407a52541d0780480207580c0d81c01440303202081d510384404501d00080c2141514100c44005180030f80b10087d180c01402c840d410481c1c0715040c59075802d000289130300c0e100d0140000500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 21927596 1250 21926346 21926351
    0x141006080708120c03030f0604020403060903080402040f0204080703060b0d060e060f0a1b0507020a091a09010b0a050703080a0b030a060c08100f0b1c0e01150602060402010203030402040b1306030303 87
    0x41c01d00c40c10316000c1c280c440400d4010050040359130151001050b260b001404601c2d21040761101404903000b03114540000d403046080c0b694460906400c082d8090040d8400c0d107040000c00c03d904c082d00c003240668001c149694100980c20001f00e18941c0080030703104401072100400051039620001102e44d003040c03201003600700b0000c022780150445c0c9903070342c840841a0140009042d000c03010407103014004443c800d0100125084040d900ca030b009450286c00110010407400c84403000c81450008814000c03845a00800008100da04d0610103841030300e205521a40c1c00d06107165010f94040034010004d2210559405201c0d84541d0b0402100c0390890003004001404075651400400a0030000c28001202065074410000030014800000c120307004e0031107054071036030710704503440f010b000c0c40c8051214681000718a800d4288194000200c50b20700681041c0c1c0256600401e98442804071070184c0980c01c184002409410540c00030700b40210300401103280780c2c590804680440300680c10036000241d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 21928846 1250 21927596 21927599
    0x609120a03200303070903030c05011d0c0a05040b0f0402070f0c0b07021813080c010f0e010c020c0901120609021c151802060301090b0105090607050303070905040e03071410060807 79
    0x40703042c214045501815024616501d45074401a29000742d920000301044018003c100621400f0b5005491400d0f200000d81c0b015100b0f85080c603610120030420f1407041c2101240003070145030620400310040700140401c41020146020040250481801a95441d506e9036401c0c002520407603002c0083c1102d0a00030f0784844083c010310078225405031800c3d00050842080c0941c0043d001d00b01c28295510106039640c8002981180d4007428004030007901070743c200b40710091b0448064004000480c001d40c01c44807031f05602c4080180c0300d00b080c0b14002d22007080021450118103035411074404a4005001c00300ba980030921f03404400d01850f40c042d9240070010400b00d20f01885402080350700c0c840120108a0109140c000840310b11040c4038000b0241e0399412030060a034001c80c00d56640c02030050882e51075004600300700341c03070f5841211600c00007101e2050220313051401d445801d0890801c00d00445c1415a940d445084102410041950714032405502c0801d803e018003500d07018103083d002802009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 21930096 1250 21928846 21928877
    0x380703030c0336030509180103051005010e070309080403020d0305030a06050a080c0603100f080303010e0702031602060a09090e0d020f010b010f0c03090b03070503090607020a08090609120a03 84
    0x200d0144401101d903010303050780d46403070124001c0303525440c109049440f4140c0380c95150a403113a22600303610720742000c0d902071041d03601216a4500f5048a016400390390110111442e11811540c0900070900e4540d28440881d55041c426400003094030f114030726032881c081e12900084d114542c2c0c0d0104400040f800020009250424040c40c4014042640e0854009d4281020291101d00340300c0c2603030140c02c0102c00513401451401040d070003420325000c0c40318560f455074069034907680300f40a038003d80a0018041000f80780f00100304d600d201c81d0741c046044d50b078a0690800025078009441541005400329020030182c01ca846029400143c841c01020816101800a07090504240c401001030345015510301c1d00ea41c0144001e20302c91601d1500c00440300340c0e8038041d038081ca0340e5080908400f00203c204620560000b00441c001c89010b0100c0d640790342e644600301d84c0c1d214040e00043c0360301d10a02c00c0c5001c030f0416001511414000901c40355141d5110810340703190180c44907080d00018090503031140d60 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 21931346 1250 21930096 21930101
    0x2090118020408120903010f050408040909050307020405011508100506030109020c01020d0525020a08040915030618020108060d02030d0e040605060c15071103070b040f02040c09170106380703030c03 87
    0xb000c2382410184807514168480404074003440c8590540c05032105000303010080d003442287c002d154004c0080003956112000051110303551000d0f43d01141e0004040381c004040f4070340d05d9003110030090201d440d6a02349900703500650454001c0c407090b03640900070b802c1e08038889d018240c0301c0c51140f0144490b012800300090703038151014003d1001d40d08140000310202d0540c01c1141e00303a4000e050049208880c01c0660741046030550f1028206529109007805000204c440200440b070003641c40e0310003604c0742c6081148080f0040350003980b550051403000d01c1140500503108a4000c01040000e0f49550f440100c3c1c0b45d07a11140305505a5000044081c1302080c840704251b410800c51300c0c0c540040c080070f0a84e03640e82c0c49103030005401680310200050401c92414001e8107103c2e809001417107128000100503040c0151802540844403101da0500704104052180c03500319a101913604c0d005452164a920701c0c995400400042c0003000000c4004080481c0018200248a5900010990701c1c0701030007001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 21932596 1250 21931346 21931361
    0xe010306090209060403121107060c02090609010e2403030a020708010e060403022107060615090501020f03070b0c0d09032703030801030201031d010501060c0303050a090209011802040812090301 85
    0x4071910520403007140f074458a054400b5203900c403e04011480200905413000141400568024854043d020980756400203182210a10907a0291065107441d820840d0042c1c3c05d004000300340c0d514000080d4051240a000d5601001c504c102d10341c110780ca100400e0840d40401e9458015070300002040240d104248100140000304e1000f1f403d0301d0a0694000303454090340c250402c030710f08610340c40700c101c10020001c8421450344000f042041c40e5403a002c83d41c010030272920748804601c0300030001410794008184000413003c000050b510348401d41d5101d004080340178220f00034214003881100e000d00311030310462046502a4071070925815844100d07014403010300e1a5910680c139001c00c2040042c1c0c1014803203055079424200440c4504c0801e507800650141906510030960a02c000000c8442d0086030600100740240c0d8240040d9441002c49820780320003190083d00001d0610040168040d1584040a00d0200c800090f01d000c1c5d0f22a000741c600a50f04207241d14041e0001903100039847c00344110030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 21933846 1250 21932596 21932609
    0x20a020709061a0a0e04020403030c0302010b0301060308030c0a0306050402070602070c0f080d0f1b030806030c09011203050708120f0709080a0507050103020a030209060d05100506040f06120b100e010306 89
    0x1550b0030035421a80290141242e41407003640800d03140b81c003602507007096501780405402107445a50301c2c100205110f104807070903070140d4600b088284041c241070192000740c0b0f8011904920399241c1085982c1c00d5070003200554109a503403080428a69602e00003003540070300451000d0303181d40050818006001e5140c0c80328000c00410002000000e50100748100406180e060a50480401403410360b050240c0c40b443c0700724803019040324420940c200d1100c502458096003280c0c07604072420180401d6107420b00944030841030224020300028854001000d02034071401407541032403031101080294440503900c81c26009a14030402c80c0031607000c0b2001c001402c00340000c080b000482d0311029201e40a600415040540000314440b819000380c044904020303010b80010340e1440c0034030f0382c00d00802080d95600d0200405143c00120707850b0035030a0f64103a070081c498880c0c00038641441922071500803600b4144140e1515518100c503601c654040f002c90505484094210048000040454400386c0050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 21935096 1250 21933846 21933851
    0x3070f0602030411181906030f050a030f05041406030402030c120105060306060405071b020a0b04030305120108120a0e0d080301091406011b020603040507151107060801050d150b040609020a020709 86
    0x111702c0c000b80004290f0401038140400902c3c948480301100540410340014151524409000042201c0010002400f80c002d582d11064045a004101d400d4801e0380b041354000300400320701002e646003910003035402604c000d0441b6882856900450685050700304003030075030f940d5081045098141402a982c0c0b151044501304440d00c3d00280141504008c03411601284101544281c01c5403199401c5001a0aaa418103501c6035900d1070020f00960060041a0142000380300004056000040d41d00c2003044030b0746003e003480003640086483c5148100c480750302001d10909800840d4084004502030f080300340002c04c0001c1d010400080707100000e0710a5041105507011840c0c81c004004003103800980c1121020394076122400c09600c0c1603060303002900d01c11440320140c100240c0004501c05000f0010081c0c54a40c0e0756010255203a80c000d02c2095000511854084005407a07400030176410300b4503800005d41c0200741004581101c07080d0700a02c3c10594000386400d18160100034120042000c0c40c1d05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 21936346 1250 21935096 21935119
    0xc140105070f14030f0d0e0313030b0705040b0a0908160b0414030c03150f010806040302031902030c0106060305100902090f04021309090308071706010207030305090303070f0602030411 81
    0x8203184125040500800850300c6400204607640000c044031140318000c6130b072204040240c0da000790f403010090051036840d0000c6102c40c004044180c41c3c4541c42e03c00c214942601c0c640342c1e103c0a840040020307007044800c11011078078016000160000480d80c1d907401c0e04842c101410039260025400f007001c03e40b0031031001042011489000c07a0b050321644140d41c0b80140c442804a460100c941d0303074659060049620038006100c8030380c41c3da40716100852000c0c0c1c480c2d988080c6a51500000e540c0900140c00030400c280c0070300711400b882c07072245819204892818030082c4d101070845280da00401d0000c0d445a0500610144601000e03001d0840c0030411481c0071900300010390b400300d03600c2100b401260041902c007442807030100f640307000341407185041c400749810f0702e4001c1c5500c4c8110340c0310010400e022a103141c0c0801d00100c441c411030381038006240746801c58406a40c00d40100407080c0d0300d80b0080102034009844034101010145c866000503842c0e00b00391401c0900c00c1c98000d106801003041e07035503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 21937596 1250 21936346 21936349
    0x160f14010302190e010306050a0308030f0c0c0304031b0302090f0a0c020d080604050403050f03070201060915050102060f0901020c070602070302040c030203070507080d0902060319140105030307020103110c16030c14 94
    0x10b80c0c3c541525604280c00e20841060040c1c02400c030750b5116542c0729000040000a01100b500254400e110881d1082c01da5035030000e070002c580c020b200c002041c2d94420306c4103100103000e01c400288500b0358003c0d550201541c2e80e0005028140c11941402a190b074a000e0003445c0409000795200329109002600780b60555460080284400400c414807554803100481c0c1418050342c105c8a24180810410b5960b00d459040a0b003e00303164414020042d01d07000740c05103443c062182c1c0d0420703200c1c140d01800c00c1d41c403104401d41c44c0140280030310020755800c102d16a41540200110400ac000e43d030003401d441c62031070040104032111260540c1c02c2c140100108980b02c4c1d8001e0840c2c4c01c0300c0d401040c1503143e405042c030003c001c2210390310094002200109010541e090448074100080e4010b400740100d0100d02216200180284140303501688184100302c0158020780110780030883e50040a0b080022142c0024038254006500c2e94000c50100300500034416130807a00c0e0081d2245818034600d141d010300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 21938846 1250 21937596 21937627
    0x20c0c09070c061a03010603030c030207120b04020103090203010b0307081506030703080a0807050c07061d0a031203020708090a0f030201020d090807090b0d06050a0209030708010b06120405160f14010302 89
    0x2c80042126503941d1090325055214610802c010601800801419440b4500a0204134400b0780c20340140c030598030000340300c40d078a603402c59582c1c0c0c9c03000d8080b413940c45039401035014201c403d034200d9146d5260161844142c5082003008000c09400c1d000b0120400507000f4410700d61406080e443c000d422202050010444103000c8400c100003c0c0b03000e5032170780d41e11841180c181c01144144008ea0041d90400110280d0100c00c501030000c40702c600007444203810040082080d42440b00808008450301540c60706030007640a030034001c0c0215041d41c0303420840c4001030622940e94200e507950303101c0100e00b8803d650341004000540007290030041150b904010f0300d15501c101c14441c3c60042c3d03450b400400e07060303241c804000014550083c0b0500043c14150007440c00b94005810041c064418031a000a5080d014040c1d1000184041d105624090010420600028004005580030b01c500151041c2c2c03510421107520003407143c600900c0303004c0e0400040003461008130a00604150050104107011340940 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 21940096 1250 21938846 21938867
    0x41404020d0302120f0a1409130b0a05030102030a0c020c0303070506040206070204110d0b0f010302120a0b0a0e040b2a12041b0909020301050703020f1905120a020c0c0907 75
    0x100d8a0164507a000d2400b02e113040b00d40c0d4105028084049030b010441c9a0404c0541503054990301c8820401d651030345d4406a501a00c03e02591001c0c00d110001c0d42c024031a031003148044e1001d0008204261110301103800c1e40d00c10b0319069000d40d910303100366000350703030502965140c2e842c21030245140540f242c0320b05940d480c0180000c5c0c8207840009216045643d20342c803615440c01c206440507100c02004a14a00030301c58000b0079405549000c0d0190360540c400c0c1f08640a100c0c0c0f1070040a41d945501188a004161011005400100755103011892402031030840b4461882546040b54501d4a80700000c200900041c021043320307100c522103058181030324155042c00410710680c924a83d220b05000701c0045038140c0c90014181d90140109100c1040e400064469000358000e110f5904e46c50000c80c124802c00e2182100c1d06400e010543d1001241d81c0040c42c0c1e1981880d0440c00c0c001c0082c070b80c034011031003a20440c030304e180d00280c8500321840c04c0c0400071a003401201c80b00038030318280402900320340703d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 21941346 1250 21940096 21940099
    0x10302130b011206080109050d090f0603050402031e03030a1406090103080702210307030207080705010e0d0c0b030711010c0806060d0c021507090303082202090c0d140601090504140402 81
    0x3902068802a40319900c12511203c1c1490244030441c3d13a01c900724004c0c05040010f4907503025025580c00070034083d0b50014101d40000c811415400d18282c0e080b0000e26001e1701c1243c0c540501c0d100046221203003044083c0f62440701d006180d403428419000e6044072240300c0702c105034003907584c20070545503100742e08241180e80201a0666501152001489050140d80d020340460b41c810500ca80300000040540802842031f0202c1d030f006501c40c00c225a41c0c0c0c120b84a4070780018050801710781907050000b07280f10f9140c072a10340d0280082d2640001c64168004464510024040c08001f510300c2d070090090105002d80d0342411442c80c10000003040c035510034100b40003085921450070900341032080003d9007203103001900c08051400c1c03941d4010400b10140c4401da0004000c40040b415003150b101c4100345409020f0003000c0303072a045a080c4108140700400020307110f5428000d6412100c418050280c1611402e603151880d4900f013000501402100d0700880d014a2030850411380221344626a180c02c03540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 21942452 1106 21941346 21941351
    0x2130306060501030b0627011e020c010306050415050418020a0312090503070b0702041e150501020d020a03080c0c031c0203010923040b1801060e0603060a0501030213 73
    0x188520003608050924950180e900b03c207c076001c011074181418240d0f0741c03074a83ea0740041d14509201101603008110410050341c3c0c180319500207450215020840711404080c0040c4074255405201c2c0030b640d4800d40c01d0b09011000346011809135004010b41411a10f0346042102580220ba603000401d50024001c2600d260115280e07090f102c00409282c01c0022a400b0000501480141e414442000031056030704406540111502d0000303440e0071102c6c3c40d10b0040028070303212000b0007500031908003e0140c0c00003a880f228680d044005996aa0348400b4185c3d00c190070b40c428034103101080800d210140c03100401035006181201c070208000c100b00c3c20400e554520a03554040c03000c81c101030800010740065401c40425402100e249096211b094185003040e0840f580c58002c014210444420407410303113000c000c502c0d03000808080500c059403656002c2030355002c0d041c585040e4240c = true := by decide +kernel

theorem cover : BRFrame.Cov 21762596 21942452 := by
  have h0 := BRFrame.cov_init 21762596
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21762596 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 21762596 ≤ n) (h2 : n < 21942452) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
